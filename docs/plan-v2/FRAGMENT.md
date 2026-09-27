# Matcher language (Phase 2)

Placeholder written in Phase 1 to record decisions carried into Phase 2.

- The matcher is written in a separate memory-free language in this
  repository, not in AMCC's `CSubset` (Decision 2, `INVENTORY.md`).
- **Phase 6 obligation:** show that running the matcher program in this
  language, with the store instantiated by the AMCC-generated data layer,
  equals running the whole generated C program under `CSubset` semantics.
  Until then the claim is about this language's semantics.
- Both printers must emit the same C dialect (integer typedefs, headers) so
  the matcher and the data layer link through `c/gen/engine_db.h`.
