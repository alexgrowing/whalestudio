import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechH1ClassEqOfCocycleAffineCover
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CmpOfIsCocycle
open CategoryTheory AlgebraicGeometry Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cech_h1_class_eq_of_cocycle_affine_cover : ∀ (R : Type) [CommRing R] (Z : Scheme.{0}) (s : Z ⟶ Sp R) (J : Type) (W : J → Z.Opens) (hW : ⨆ i, W i = ⊤), (∀ i, IsAffineOpen (W i)) → (∀ i i', IsAffineOpen (W i ⊓ W i')) → (∀ i i' i'', IsAffineOpen (W i ⊓ W i' ⊓ W i'')) → ∀ x : GlobalTheory.CechDR.HO1 s, ∃ c : ∀ i i' : J, Γ(Z, W i ⊓ W i'), GlobalTheory.CechCmp.IsCocycle W c ∧ GlobalTheory.CechCmp.cmp s W hW c = x := by
  first | exact @GlobalTheory.CechCmp.exists_isCocycle_cmp_eq | exact GlobalTheory.CechCmp.exists_isCocycle_cmp_eq | (intros; apply GlobalTheory.CechCmp.exists_isCocycle_cmp_eq <;> assumption)
