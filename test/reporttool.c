/* Exercise the CLI report on proof bodies produced by the checker. */
#define main langc_cli_main
#include "../src/main.c"
#undef main

static int report(const char *body, const char *want) {
  static const char prelude[] =
    "def Val : Type 0 := Nat\n"
    "keyspace Bal : Nat -> Key\n"
    "def Digest : Type 0 := Nat\n"
    "def storeLeaf : Key -> Val -> Digest := fun k v => 1\n"
    "def nodeDigest : Digest -> Digest -> Digest := fun a b => 1\n"
    "def emptyDigest : Digest := 0\n";
  Arena arena;
  Diag diag;
  DeclList decls = {0};
  Machine machine;
  char text[4096];
  char got[256] = {0};
  FILE *out = tmpfile();
  int ok;
  arena_init(&arena, ARENA_LIMIT_BYTES);
  diag_init(&diag);
  snprintf(text, sizeof text, "%s%s", prelude, body);
  ok = out != NULL
    && front_load(&arena, "report-test", text, strlen(text), &decls, &diag)
    && check_program(&arena, &decls, &machine, &diag, CHECK_KIT)
    && axioms_print(&machine, out) == 0;
  if (ok) {
    rewind(out);
    ok = fgets(got, sizeof got, out) != NULL && strcmp(got, want) == 0
      && fgetc(out) == EOF;
  }
  if (!ok)
    fprintf(stderr, "FAIL report: wanted %s, got %s (%s)\n", want, got,
            diag.code == NULL ? "no diagnostic" : diag.code);
  if (out != NULL)
    fclose(out);
  arena_release(&arena);
  return ok;
}

int main(void) {
  int ok = 1;
  /* This type mentions an assumption, but the body does not use it. */
  ok &= report(
    "def unused : (p : Path Digest 1 1) -> Path Digest (first (nodeDigestInj 0 0 0 0 p) @ i0) 0 := fun p => refl\n",
    "{\"ok\":true,\"axioms\":[]}\n");
  /* refl reads its endpoint back into the body as an opaque OP_AXIOM. */
  ok &= report(
    "def reflected : (p : Path Digest 1 1) -> Path (Path Digest 0 0) (first (nodeDigestInj 0 0 0 0 p)) (first (nodeDigestInj 0 0 0 0 p)) := fun p => refl\n",
    "{\"ok\":true,\"axioms\":[\"nodeDigestInj\"]}\n");
  if (ok)
    puts("report regressions: passed");
  return ok ? 0 : 1;
}
