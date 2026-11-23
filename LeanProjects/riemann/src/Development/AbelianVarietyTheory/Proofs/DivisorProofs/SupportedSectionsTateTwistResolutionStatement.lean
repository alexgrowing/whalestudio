import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SupportedSectionsTateTwistResolution
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition
import Development.AbelianVarietyTheory.Definitions.Divisors.SecClass
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.supportedSections_tateTwist_resolution : ∀ (q : ℕ) [NeZero q] (i : ℤ) (D : Cx (ZMod q)) (ι : D ⟶ res _ (tw q i)), (∀ n U, Function.Injective (Sec.map (ι.f n) (U := U))) → (∀ n U (a : Sec ((res _ (tw q i)).X n) U), (∃ b, Sec.map (ι.f n) b = a) ↔ Loc U fun V g => IsUnit (q : Γ(V, ⊤)) ∨ Sec.res g a = 0) → ∃ e : ∀ U : Scheme.{0}, Prim q Γ(U, ⊤) → Sec (D.X 0) U, IsTwRes q i D e ∧ ∀ U ζ, Sec.map (ι.f 0) (e U ζ) = resGen i ζ := by
  first
  | exact @GlobalTheory.EtC.SuppRes.supp_res
  | exact GlobalTheory.EtC.SuppRes.supp_res
  | (intros; apply GlobalTheory.EtC.SuppRes.supp_res <;> assumption)
