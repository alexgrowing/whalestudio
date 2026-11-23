import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClosedImmersionBaseChangeKerMemMapAffine
import Development.AbelianVarietyTheory.Definitions.Divisors.SameIdIff
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsCrystalPairing
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitsPatch
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.closedImmersion_baseChange_ker_mem_map_affine : ∀ (X X' Z Z' : Scheme.{0}) (p : X' ⟶ X) (i : Z ⟶ X) (i' : Z' ⟶ X') (p' : Z' ⟶ Z), IsPullback i' p' p i → IsAffineHom p → IsClosedImmersion i → ∀ W : X.Opens, IsAffineOpen W → ∀ s : Γ(X', p ⁻¹ᵁ W), (i'.app (p ⁻¹ᵁ W)).hom s = 0 → s ∈ Ideal.map (p.app W).hom (RingHom.ker (i.app W).hom) := by
  first | exact @GlobalTheory.closedImmersion_baseChange_ker_mem_map | exact GlobalTheory.closedImmersion_baseChange_ker_mem_map | (intros; apply GlobalTheory.closedImmersion_baseChange_ker_mem_map <;> assumption)
