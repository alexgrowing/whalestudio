import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CmTypeSeparatesEmbeddings
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PeriodComparison
import Development.AbelianVarietyTheory.Definitions.Divisors.JetAnalytic
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrysToDRBijective
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsCrystalPairing
open GlobalTheory.LatVal GlobalTheory.LatJet
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.CMVal
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CMSep

theorem exists_int_sep_all : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (I : Type) [Fintype I] (φ : I → E →+* ℂ), IsCMType φ →
    ∀ i : I, ∃ b₀ : 𝓞 (FR E), ∀ j : I, φ j ((b₀ : FR E) : E) = φ i ((b₀ : FR E) : E) → j = i := by
  intro E _ _ _ I _ φ hφ i

  let L : I → FR E →ₗ[ℚ] ℂ := fun j => ((φ j).comp (algebraMap (FR E) E)).toRatAlgHom.toLinearMap
  have hL : ∀ j (x : FR E), L j x = φ j (x : E) := fun j x => rfl
  let p : {j : I // j ≠ i} → Subspace ℚ (FR E) := fun j => LinearMap.ker (L j.1 - L i)
  have hp : ∀ j, p j ≠ ⊤ := by
    intro j htop
    obtain ⟨a, ha⟩ := exists_int_ne E I φ hφ j.1 i j.2
    have : ((a : FR E)) ∈ p j := htop ▸ Submodule.mem_top
    simp only [p, LinearMap.mem_ker, LinearMap.sub_apply, hL, sub_eq_zero] at this
    exact ha this
  have hcov : ⋃ j, (p j : Set (FR E)) ≠ Set.univ := by
    intro h
    obtain ⟨j, hj⟩ := Subspace.exists_eq_top_of_iUnion_eq_univ h
    exact hp j hj
  obtain ⟨x, hx⟩ : ∃ x : FR E, ∀ j : {j : I // j ≠ i}, x ∉ p j := by
    by_contra hno
    push_neg at hno
    exact hcov (Set.eq_univ_of_forall fun x => by
      obtain ⟨j, hj⟩ := hno x
      exact Set.mem_iUnion.mpr ⟨j, hj⟩)
  obtain ⟨y, hy0, hyint'⟩ := exists_integral_multiples ℤ ℚ ({x} : Finset (FR E))
  have hyint := hyint' x (Finset.mem_singleton_self x)
  refine ⟨⟨y • x, hyint⟩, fun j hj => ?_⟩
  by_contra hji
  apply hx ⟨j, hji⟩
  simp only [p, LinearMap.mem_ker, LinearMap.sub_apply, hL, sub_eq_zero]
  have e : ((y • x : FR E) : E) = (y : E) * (x : E) := by simp [zsmul_eq_mul]
  change φ j ((y • x : FR E) : E) = φ i ((y • x : FR E) : E) at hj
  rw [e, map_mul, map_mul, map_intCast, map_intCast] at hj
  exact mul_left_cancel₀ (by exact_mod_cast hy0) hj

end GlobalTheory.CMSep
