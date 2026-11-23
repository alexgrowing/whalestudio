import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsSepClosedResidueFieldPowerSeriesComplex

noncomputable section

open CategoryTheory Limits AlgebraicGeometry IsLocalRing

namespace GlobalTheory.Published

open GlobalTheory.NCyc in

def SmoothNearbyCycles : Prop :=
  ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [HenselianLocalRing O]
    [IsSepClosed (ResidueField O)]
    (Ω : Type) [Field Ω] [Algebra O Ω] [IsAlgClosed Ω] [FaithfulSMul O Ω] [Algebra.IsAlgebraic O Ω]
    (l : ℕ) [Fact l.Prime], IsUnit (l : O) →
  ∀ (Λ : Type) [CommRing Λ] [TopologicalSpace Λ] [IsTopologicalRing Λ], Finite Λ → DiscreteTopology Λ →
    (∃ k : ℕ, ((l ^ k : ℕ) : Λ) = 0) →
  ∀ (X Y : Scheme.{0}) (p : X ⟶ Spec (CommRingCat.of O)) [LocallyOfFiniteType p] (q : Y ⟶ Spec (CommRingCat.of O))
    (f : Y ⟶ X) [Smooth f] (hf : f ≫ p = q) (y : SpecialPoint q) (x : SpecialPoint p), f y.1 = x.1 →
  ∀ (L : StrictLoc Y y.1) (M : StrictLoc X x.1) (h : L.scheme ⟶ M.scheme) (hh : h ≫ M.toX = L.toX ≫ f) (n : ℕ),
    Function.Bijective (stalkPull Λ Ω f hf L M h hh n)

open GlobalTheory.NCyc in

example (H : SmoothNearbyCycles) (n : ℕ) : True := by
  letI := henselian_powerSeries_complex
  letI := isSepClosed_residueField_powerSeries_complex
  letI := faithfulSMul_powerSeries_complex
  letI := isAlgebraic_powerSeries_complex
  letI : TopologicalSpace (ZMod 3) := ⊥
  haveI : DiscreteTopology (ZMod 3) := ⟨rfl⟩
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  have hu : IsUnit ((3 : ℕ) : PowerSeries ℂ) := by
    rw [← map_natCast (algebraMap ℂ (PowerSeries ℂ))]
    exact (IsUnit.mk0 _ (by norm_num)).map _
  have := H (PowerSeries ℂ) (AlgebraicClosure (FractionRing (PowerSeries ℂ))) 3 hu (ZMod 3) inferInstance
    inferInstance ⟨1, by decide⟩ _ _ (𝟙 _) (𝟙 _) (𝟙 _) (Category.id_comp _) (SpecialPoint.closed _)
    (SpecialPoint.closed _) rfl (StrictLoc.ofStrictlyHenselian _) (StrictLoc.ofStrictlyHenselian _) (𝟙 _)
    (by rw [Category.id_comp, Category.comp_id]) n
  trivial

end GlobalTheory.Published
