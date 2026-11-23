import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.TorusExt
import ReciprocityTheory.GeometryOfNumbers.LatticeCovolumes.ArakelovDegreeEqDegreeOfFamily
open NumberField ReciprocityTheory.GeometryOfNumbersTheory GlobalTheory.LieHt
open scoped ComplexOrder

noncomputable section
namespace GlobalTheory

theorem finrank_mul_deg_lineLat_add_sum_log_nrm (K : Type) [Field K] [NumberField K] (m : ℕ)
    (h : HermFam K (Fin m → K)) (L : Submodule (𝓞 K) (Fin m → K)) (x : Fin m → K) (a : K) :
    L.FG → x ≠ 0 → a ≠ 0 → a • x ∈ L →
    (Module.finrank ℚ K : ℝ) * deg h (lineLat L x) + ∑ σ : K →+* ℂ, Real.log (h.nrm σ x) =
      Real.log ((Submodule.span (𝓞 K) {a}).toAddSubgroup.relIndex
        (L.comap ((LinearMap.toSpanSingleton K (Fin m → K) x).restrictScalars (𝓞 K))).toAddSubgroup : ℝ) -
      ∑ σ : K →+* ℂ, Real.log ‖σ a‖ := by
  intro hL hx ha haL
  set f : K →ₗ[𝓞 K] (Fin m → K) := (LinearMap.toSpanSingleton K (Fin m → K) x).restrictScalars (𝓞 K) with hf
  have hfapp : ∀ b : K, f b = b • x := fun b => rfl
  have hfinj : Function.Injective f := by
    intro b c hbc
    rw [hfapp, hfapp] at hbc
    exact smul_left_injective K hx hbc

  have hmapJ : (L.comap f).map f = lineLat L x := by
    ext y
    simp only [Submodule.mem_map, Submodule.mem_comap, lineLat, Submodule.mem_inf,
      Submodule.restrictScalars_mem, Submodule.mem_span_singleton]
    constructor
    · rintro ⟨b, hb, rfl⟩
      exact ⟨hb, b, (hfapp b).symm⟩
    · rintro ⟨hy, b, rfl⟩
      exact ⟨b, by rwa [hfapp], hfapp b⟩
  have hmapA : (Submodule.span (𝓞 K) {a}).map f = Submodule.span (𝓞 K) {a • x} := by
    rw [Submodule.map_span, Set.image_singleton, hfapp]
  have hidx : (Submodule.span (𝓞 K) (Set.range ![a • x])).toAddSubgroup.relIndex (lineLat L x).toAddSubgroup =
      (Submodule.span (𝓞 K) {a}).toAddSubgroup.relIndex (L.comap f).toAddSubgroup := by
    have hr : Set.range ![a • x] = {a • x} := by simp
    rw [hr, ← hmapA, ← hmapJ, Submodule.map_toAddSubgroup, Submodule.map_toAddSubgroup]
    exact AddSubgroup.relIndex_map_map_of_injective _ _ hfinj

  have hax : a • x ≠ 0 := smul_ne_zero ha hx
  have hframe : IsFrame K (lineLat L x) ![a • x] := by
    refine ⟨?_, ?_, ?_⟩
    · intro i
      fin_cases i
      exact ⟨haL, Submodule.smul_mem _ a (Submodule.subset_span rfl)⟩
    · rw [linearIndependent_unique_iff]
      simpa using hax
    · intro y hy
      obtain ⟨-, hy2⟩ := hy
      rw [SetLike.mem_coe, Submodule.restrictScalars_mem, Submodule.mem_span_singleton] at hy2
      obtain ⟨c, rfl⟩ := hy2
      have : c • x = (c / a) • (a • x) := by rw [smul_smul, div_mul_cancel₀ c ha]
      rw [this, SetLike.mem_coe]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨0, rfl⟩)
  have hFG : (lineLat L x).FG := Submodule.FG.of_le hL inf_le_left
  rw [arakelovDegree_eq_degreeOfFamily h hFG hframe]
  unfold degreeOfFamily
  rw [hidx]

  have hleft : ∀ (σ : K →+* ℂ) (c : K) (u w : Fin m → K), h.form σ (c • u) w = starRingEnd ℂ (σ c) * h.form σ u w := by
    intro σ c u w
    rw [← h.conj_symm, h.smul_right, map_mul, h.conj_symm]
  have hpos : ∀ σ : K →+* ℂ, 0 < (h.form σ x x).re := by
    intro σ
    have hli : LinearIndependent K ![x] := by
      rw [linearIndependent_unique_iff]; simpa using hx
    have hd := (h.posDef σ 1 ![x] hli).diag_pos (i := 0)
    simp only [Matrix.of_apply, Matrix.cons_val_fin_one] at hd
    exact (Complex.pos_iff.mp hd).1
  have hdet : ∀ σ : K →+* ℂ, (h.gram σ ![a • x]).det.re = ‖σ a‖ ^ 2 * (h.form σ x x).re := by
    intro σ
    rw [Matrix.det_fin_one, HermFam.gram, Matrix.of_apply, Matrix.cons_val_fin_one, hleft, h.smul_right,
      ← mul_assoc, Complex.conj_mul']
    rw [← Complex.ofReal_pow, Complex.re_ofReal_mul]
  have hσa : ∀ σ : K →+* ℂ, ‖σ a‖ ≠ 0 := fun σ => by simpa using ha
  have hlog : ∀ σ : K →+* ℂ, Real.log (h.gram σ ![a • x]).det.re =
      2 * Real.log ‖σ a‖ + 2 * Real.log (h.nrm σ x) := by
    intro σ
    rw [hdet, Real.log_mul (pow_ne_zero 2 (hσa σ)) (hpos σ).ne', Real.log_pow, HermFam.nrm,
      Real.log_sqrt (hpos σ).le]
    push_cast; ring
  simp_rw [hlog]
  have hK : (Module.finrank ℚ K : ℝ) ≠ 0 := by
    have := Module.finrank_pos (R := ℚ) (M := K)
    exact_mod_cast this.ne'
  rw [mul_div_cancel₀ _ hK, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
  ring

end GlobalTheory
