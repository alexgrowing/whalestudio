import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.IsolateSpec

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Gal.TranscendenceTraces

theorem UpperTheory.Gal.TranscendenceTraces.opEq_of :
    FL → RpBasic → RpOp → OpEq := by
  intro hFL hB hOp Q Z S p _ F G t τ τ' hτ hτ' n
  ext x
  obtain ⟨a, ha⟩ := (hB (ZMod Q) (res (ZMod Q) F) Z n).1 x
  have hd := (hB (ZMod Q) (res (ZMod Q) F) Z n).2.1 x a ha
  have h1 := hOp _ _ τ n x a ha
  have h2 := hOp _ _ τ' n x a ha
  obtain ⟨y, hy⟩ := (hFL Q p F G t).2 τ τ' hτ hτ' (Sq.self p) (n - 1) n (n + 1)
    (sub_add_cancel n 1) rfl a hd
  exact ((hB (ZMod Q) (res (ZMod Q) G) S n).2.2.1 _ _ _ _ h1 h2).1.mpr ⟨y, hy⟩
