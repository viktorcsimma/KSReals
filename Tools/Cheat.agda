-- The postulate cheat; used to skip proofs
-- while pushing for computation.
-- Importing this module makes the whole thing
-- unsafe until the import is removed.
-- But it cannot affect computational results;
-- since it is erased.

module Tools.Cheat where

postulate @0 cheat : ∀ {i} {a : Set i} -> a
