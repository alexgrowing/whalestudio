import Mathlib
import Development.AutomorphicSpectrum.Statements.GeometryStatements.ThmFlatA
import Development.AutomorphicSpectrum.Statements.GeometryStatements.FlatLineGenerator
import Development.AutomorphicSpectrum.Statements.GeometryStatements.CardComapMulFinsumEqFinsumFibres
import Development.AutomorphicSpectrum.Statements.GeometryStatements.FinConstFor
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat

namespace GlobalTheory.CompanionTheory.Ar.Flat

theorem exists_valuationSubring_of_padicEmbedding :
    ∀ (F : IntermediateField ℚ ℂ) (p : Nat.Primes) (κ : F →+* ℂ_[p]),
      ∃ W : ValuationSubring ℂ, ((p : ℕ) : ℂ) ∈ W.nonunits ∧
        ∀ x : F, ‖κ x‖ ≤ 1 ↔ (x : ℂ) ∈ W := by
  intro F p κ
  have hna : ∀ a b : ℂ_[p], ‖a + b‖ ≤ max ‖a‖ ‖b‖ := fun a b =>
    IsUltrametricDist.norm_add_le_max a b
  have hone : ‖κ 1‖ = 1 := by simp
  let A : Subring ℂ :=
    { carrier := {a | ∃ x : F, (x : ℂ) = a ∧ ‖κ x‖ ≤ 1}
      mul_mem' := by
        rintro _ _ ⟨x, rfl, hx⟩ ⟨y, rfl, hy⟩
        refine ⟨x * y, by simp, ?_⟩
        rw [map_mul, norm_mul]
        exact mul_le_one₀ hx (norm_nonneg _) hy
      one_mem' := ⟨1, by simp, by simp⟩
      add_mem' := by
        rintro _ _ ⟨x, rfl, hx⟩ ⟨y, rfl, hy⟩
        refine ⟨x + y, by simp, ?_⟩
        rw [map_add]
        exact (hna _ _).trans (max_le hx hy)
      zero_mem' := ⟨0, by simp, by simp⟩
      neg_mem' := by
        rintro _ ⟨x, rfl, hx⟩
        exact ⟨-x, by simp, by simpa using hx⟩ }
  let I : Ideal A :=
    { carrier := {a | ∃ x : F, (x : ℂ) = (a : ℂ) ∧ ‖κ x‖ < 1}
      add_mem' := by
        rintro a b ⟨x, hxa, hx⟩ ⟨y, hyb, hy⟩
        refine ⟨x + y, by simp [hxa, hyb], ?_⟩
        rw [map_add]
        exact (hna _ _).trans_lt (max_lt hx hy)
      zero_mem' := ⟨0, by simp, by simp⟩
      smul_mem' := by
        rintro ⟨c, z, hzc, hz⟩ a ⟨x, hxa, hx⟩
        refine ⟨z * x, by simp [hzc, hxa], ?_⟩
        rw [map_mul, norm_mul]
        calc ‖κ z‖ * ‖κ x‖ ≤ 1 * ‖κ x‖ := by gcongr
          _ < 1 := by simpa using hx }
  have hI : I ≠ ⊤ := by
    intro htop
    have h1 : (1 : A) ∈ I := by rw [htop]; trivial
    obtain ⟨x, hx1, hx⟩ := h1
    have hx1' : x = 1 := by
      apply Subtype.ext
      simpa using hx1
    rw [hx1', hone] at hx
    exact lt_irrefl _ hx
  obtain ⟨W, hAW, hIW⟩ := Ideal.image_subset_nonunits_valuationSubring I hI
  have key : ∀ x : F, ‖κ x‖ < 1 → (x : ℂ) ∈ W.nonunits := by
    intro x hx
    have hxA : (x : ℂ) ∈ A := ⟨x, rfl, hx.le⟩
    exact hIW ⟨⟨(x : ℂ), hxA⟩, ⟨x, rfl, hx⟩, rfl⟩
  refine ⟨W, ?_, fun x => ⟨fun hx => hAW ⟨x, rfl, hx⟩, fun hxW => ?_⟩⟩
  · have hnorm : ‖((p : ℕ) : ℂ_[p])‖ < 1 := by
      rw [← PadicComplex.coe_natCast, PadicComplex.norm_extends,
        ← map_natCast (algebraMap ℚ_[p] (PadicAlgCl p)), PadicAlgCl.norm_extends,
        Padic.norm_p]
      exact inv_lt_one_of_one_lt₀ (by exact_mod_cast p.2.one_lt)
    have := key ((p : ℕ) : F) (by simpa using hnorm)
    simpa using this
  · by_contra hlt
    have hlt' : 1 < ‖κ x‖ := not_le.mp hlt
    have hx0 : x ≠ 0 := by
      rintro rfl
      simp at hlt'
      linarith
    have hinv : ‖κ x⁻¹‖ < 1 := by
      rw [map_inv₀, norm_inv]
      exact inv_lt_one_of_one_lt₀ hlt'
    have hnu := key x⁻¹ hinv
    rw [ValuationSubring.mem_nonunits_iff] at hnu
    have hle : W.valuation (x : ℂ) ≤ 1 := (W.valuation_le_one_iff _).2 hxW
    have hprod : W.valuation (x : ℂ) * W.valuation ((x⁻¹ : F) : ℂ) = 1 := by
      rw [← map_mul]
      have : (x : ℂ) * ((x⁻¹ : F) : ℂ) = 1 := by
        have h0 : (x : ℂ) ≠ 0 := by simpa using hx0
        simp [h0]
      rw [this, map_one]
    have : W.valuation (x : ℂ) * W.valuation ((x⁻¹ : F) : ℂ) < 1 :=
      lt_of_le_of_lt (mul_le_of_le_one_left' hle) hnu
    exact absurd hprod this.ne

end GlobalTheory.CompanionTheory.Ar.Flat
