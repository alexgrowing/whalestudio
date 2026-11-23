import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechCocycleIsCoboundaryOfClassEqZero
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CmpOfIsCocycle
open CategoryTheory AlgebraicGeometry Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cechCocycle_isCoboundary_of_class_eq_zero : ∀ (R : Type) [CommRing R] (Z : Scheme.{0}) (s : Z ⟶ Sp R) (J : Type) (W : J → Z.Opens) (hW : ⨆ i, W i = ⊤), (∀ i, IsAffineOpen (W i)) → (∀ i i', IsAffineOpen (W i ⊓ W i')) → ∀ (c : ∀ i i' : J, Γ(Z, W i ⊓ W i')), GlobalTheory.CechCmp.IsCocycle W c → GlobalTheory.CechCmp.cmp s W hW c = 0 → ∃ h : ∀ i : J, Γ(Z, W i), ∀ i i', c i i' = resG Z inf_le_left (h i) - resG Z inf_le_right (h i') := by
  first | exact @GlobalTheory.CechCmp.exists_coboundary_of_cmp_eq_zero | exact GlobalTheory.CechCmp.exists_coboundary_of_cmp_eq_zero | (intros; apply GlobalTheory.CechCmp.exists_coboundary_of_cmp_eq_zero <;> assumption)
