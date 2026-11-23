import Mathlib
import Development.AutomorphicArithmetic.AutomorphicVarieties.AdditiveValuationNorms.CokLenLeOfRangeLe
import Development.AutomorphicArithmetic.AutomorphicVarieties.AdditiveValuationNorms.ABoundOfDescends
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.ExistsGen
import Development.AutomorphicArithmetic.AutomorphicVarieties.NumberFieldTowers.CycRange
import Development.AutomorphicArithmetic.AutomorphicVarieties.NumberFieldTowers.PrincGen
import Development.AutomorphicArithmetic.AutomorphicVarieties.NumberFieldTowers.CycMemPrincIff

open UpperTheory.V UpperTheory.V.PropA NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Base UpperTheory.V.Kum UpperTheory.V.Tower

theorem UpperTheory.V.PropA.genLevel :
    ∀ (l : ℕ) [Fact l.Prime] (L₀ : Type) [Field L₀] [NumberField L₀], HasMuQ l L₀ →
      ∃ γ : G L₀ (AlgebraicClosure L₀), IsGen l ⊤ γ ∧ IsLevel l (cycZ L₀ _ l γ : ℤ_[l]) (cZero l L₀) ∧
        ∃ ζ : L₀, IsPrimitiveRoot ζ (l ^ cZero l L₀) := by
  intro l _ L₀ _ _ hmu
  have hM := muQ L₀ (AlgebraicClosure L₀) l
  have hq : qExp l ≤ cZero l L₀ := hM.2.2.1.mp hmu
  have hP := princGen l (cZero l L₀) hq
  obtain ⟨u, hu, hu'⟩ : ∃ u ∈ KStar.TotallyRealRoots.princ l (cZero l L₀), u ∉ KStar.TotallyRealRoots.princ l (cZero l L₀ + 1) := by
    by_contra hne
    push_neg at hne
    have h1 := hP.2.2 1
    rw [Subgroup.relIndex_eq_one.mpr hne, pow_one] at h1
    exact (Fact.out : l.Prime).one_lt.ne h1
  have hr := cycRange L₀ (AlgebraicClosure L₀) l hmu
  obtain ⟨γ, hγ⟩ : u ∈ (cycZ L₀ (AlgebraicClosure L₀) l).range := hr ▸ hu
  refine ⟨γ, ⟨Subgroup.mem_top _, ?_⟩, ?_, (hM.1 _).mpr le_rfl⟩
  · rw [← MonoidHom.range_eq_map, hr, hγ]
    exact (hP.1 u hu).mpr hu'
  · rw [hγ]
    exact (hP.2.1 u hu hu').1
