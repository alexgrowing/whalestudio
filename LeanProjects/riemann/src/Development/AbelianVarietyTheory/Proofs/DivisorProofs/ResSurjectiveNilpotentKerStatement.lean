import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ResSurjectiveNilpotentKer
import Mathlib
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsSchemeOfThickenings
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PreimageUpOpen
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ferrandPush_res_surjective_and_isNilpotent_ker : ∀ {Y₀ Y₁ : Scheme.{0}} (i : Y₀ ⟶ Y₁) [IsClosedImmersion i] [Surjective i], (∀ U : Y₁.Opens, IsAffineOpen U → IsNilpotent (RingHom.ker (i.app U).hom)) → ∀ U : Y₀.Opens, IsAffineOpen (GlobalTheory.FerrandPush.upOpen i U) → Function.Surjective (GlobalTheory.FerrandPush.res i U).hom ∧ IsNilpotent (RingHom.ker (GlobalTheory.FerrandPush.res i U).hom) := by
  first | exact @GlobalTheory.FerrandPush.res_surjective_nilpotent_ker | exact GlobalTheory.FerrandPush.res_surjective_nilpotent_ker | (intros; apply GlobalTheory.FerrandPush.res_surjective_nilpotent_ker <;> assumption)
