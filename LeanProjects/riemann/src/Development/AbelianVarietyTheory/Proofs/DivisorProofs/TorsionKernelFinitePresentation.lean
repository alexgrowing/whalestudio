import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsMulVal
set_option autoImplicit false
noncomputable section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField WithConv
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.PerfdLat GlobalTheory.GroupBplus GlobalTheory.GroupBplus.Aff
open Coalgebra Bialgebra
open GlobalTheory.DeRham (spOver spOver_comp)
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.GroupBplus.Aff

theorem tors_ext_of_local : ∀ (R : Type) [CommRing R] (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (N : ℕ) (B : Type) [CommRing B] [Algebra R B], ∀ z z' : Tors G N B, (∀ P : PrimeSpectrum B, ∃ f : B, f ∉ P.asIdeal ∧ torsMap (IsScalarTower.toAlgHom R B (Localization.Away f)) z = torsMap (IsScalarTower.toAlgHom R B (Localization.Away f)) z') → z = z' := by
  intro R _ G _ _ N B _ _ z z' h
  choose f hf hz using h
  have hs : Ideal.span (Set.range f) = ⊤ := by
    by_contra hne
    obtain ⟨m, hm, hle⟩ := Ideal.exists_le_maximal _ hne
    exact hf ⟨m, hm.isPrime⟩ (hle (Ideal.subset_span ⟨_, rfl⟩))
  apply Subtype.ext
  apply Over.OverMorphism.ext
  refine Scheme.Cover.hom_ext (Scheme.affineOpenCoverOfSpanRangeEqTop (R := CommRingCat.of B) f hs).openCover _ _ fun P => ?_
  exact congrArg (fun w => w.1.left) (hz P)

end GlobalTheory.GroupBplus.Aff
