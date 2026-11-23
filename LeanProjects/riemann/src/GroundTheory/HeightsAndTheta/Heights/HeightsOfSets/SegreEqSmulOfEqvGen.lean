import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HeightsOfSets.FiniteSupportHeight
import GroundTheory.HeightsAndTheta.Heights.HeightsOfSets.IsSaturatedFirstCoordinateLine
import GroundTheory.HeightsAndTheta.Heights.HeightsOfSets.CurveComplexPoint
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterRedA
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.HeightsSet

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo MeasureTheory

section Fibres

variable {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)]

omit [∀ k, Fintype (ι k)] in

theorem segre_smul (c : K → ℂ) (z : (Σ k, ι k) → ℂ) :
    segre (fun p ↦ c p.1 * z p) = (∏ k, c k) • segre z := by
  funext i
  simp [segre, Finset.prod_mul_distrib]

omit [∀ k, Fintype (ι k)] in

theorem segre_eq_smul_of_eqvGen {P : Ideal (MRing ι)} {z z' : mcPts P}
    (h : Relation.EqvGen (fun z z' : mcPts P ↦ ∃ c : K → ℂ, (∀ k, c k ≠ 0) ∧
      (z' : (Σ k, ι k) → ℂ) = fun p ↦ c p.1 * (z : (Σ k, ι k) → ℂ) p) z z') :
    ∃ t : ℂ, t ≠ 0 ∧ segre (z' : (Σ k, ι k) → ℂ) = t • segre (z : (Σ k, ι k) → ℂ) := by
  induction h with
  | rel a b hab =>
    obtain ⟨c, hc, hb⟩ := hab
    exact ⟨∏ k, c k, Finset.prod_ne_zero_iff.mpr fun k _ ↦ hc k, by rw [hb, segre_smul]⟩
  | refl a => exact ⟨1, one_ne_zero, (one_smul _ _).symm⟩
  | symm a b _ ih =>
    obtain ⟨t, ht, hab⟩ := ih
    exact ⟨t⁻¹, inv_ne_zero ht, by rw [hab, smul_smul, inv_mul_cancel₀ ht, one_smul]⟩
  | trans a b d _ _ ih₁ ih₂ =>
    obtain ⟨t, ht, hab⟩ := ih₁
    obtain ⟨u, hu, hbd⟩ := ih₂
    exact ⟨u * t, mul_ne_zero hu ht, by rw [hbd, hab, smul_smul]⟩

variable {e : ℕ}

omit [∀ k, Fintype (ι k)] in

theorem fibre_finite_card (P : Ideal (MRing ι))
    (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)) (y : Fin e → ℂ) (hP : 0 < degC P) :
    (fibre P Ψ y).Finite ∧ Nat.card (fibre P Ψ y) ≤ degC P := by
  classical
  set r := fun z z' : mcPts P ↦ ∃ c : K → ℂ, (∀ k, c k ≠ 0) ∧
    (z' : (Σ k, ι k) → ℂ) = fun p ↦ c p.1 * (z : (Σ k, ι k) → ℂ) p with hr
  have hQ : Finite (Quot r) := (Nat.card_pos_iff.mp hP).2
  let F : fibre P Ψ y → Quot r := fun w ↦ Quot.mk r ⟨w.2.choose, w.2.choose_spec.1⟩
  have hF : Function.Injective F := by
    intro w w' hww
    obtain ⟨t, ht, hseg⟩ := segre_eq_smul_of_eqvGen (Quot.eqvGen_exact hww)
    have h1 := w.2.choose_spec.2
    have h2 := w'.2.choose_spec.2
    simp only at hseg
    rw [h1.1, h2.1] at hseg
    have hΨ : Ψ (w' : ((k : K) → ι k) → ℂ) = t • Ψ (w : ((k : K) → ι k) → ℂ) := by
      rw [hseg, map_smul]
    rw [h1.2, h2.2] at hΨ
    have h0 := congrFun hΨ 0
    simp only [Fin.cons_zero, Pi.smul_apply, smul_eq_mul, mul_one] at h0
    rw [← h0, one_smul] at hseg
    exact Subtype.ext hseg.symm
  exact ⟨Set.finite_coe_iff.mp (Finite.of_injective F hF),
    Nat.card_le_card_of_injective F hF⟩

theorem maDensity_zero (φ : Fin 0 → (Fin 0 → ℂ) → ℝ) (y : Fin 0 → ℂ) : maDensity φ y = 1 := by
  simp [maDensity, mixedDisc]

omit [∀ k, Fintype (ι k)] in

theorem abs_fibreSum_sub_le (P : Ideal (MRing ι))
    (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (0 + 1) → ℂ)) (φ : Fin 0 → ((Σ k, ι k) → ℂ) → ℝ)
    (g g' : ((Σ k, ι k) → ℂ) → ℝ) {c : ℝ} (hc0 : 0 ≤ c) (hP : 0 < degC P)
    (hg : ∀ z ∈ mcPts P, |g z - g' z| ≤ c) (y : Fin 0 → ℂ) :
    |(∑ᶠ w ∈ fibre P Ψ y, sheetDensity P Ψ φ g y w) - ∑ᶠ w ∈ fibre P Ψ y, sheetDensity P Ψ φ g' y w|
      ≤ c * degC P := by
  classical
  obtain ⟨hfin, hcard⟩ := fibre_finite_card P Ψ y hP
  rw [finsum_mem_eq_finite_toFinset_sum _ hfin, finsum_mem_eq_finite_toFinset_sum _ hfin,
    ← Finset.sum_sub_distrib]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  have hterm : ∀ w ∈ hfin.toFinset, |sheetDensity P Ψ φ g y w - sheetDensity P Ψ φ g' y w| ≤ c := by
    intro w _
    unfold sheetDensity
    split_ifs with hγ
    · rw [maDensity_zero, mul_one, mul_one]
      exact hg _ (hγ.choose_spec.2.self_of_nhds).2.1
    · simpa using hc0
  refine (Finset.sum_le_card_nsmul _ _ c hterm).trans ?_
  rw [nsmul_eq_mul, mul_comm]
  refine mul_le_mul_of_nonneg_left ?_ hc0
  have : hfin.toFinset.card = Nat.card (fibre P Ψ y) := by
    rw [← Set.ncard_eq_toFinset_card _ hfin, Nat.card_coe_set_eq]
  rw [this]
  exact_mod_cast hcard

omit [∀ k, Fintype (ι k)] in

theorem abs_ptsIntegral_sub_le (P : Ideal (MRing ι)) (φ : Fin 0 → ((Σ k, ι k) → ℂ) → ℝ)
    (g g' : ((Σ k, ι k) → ℂ) → ℝ) {c : ℝ} (hc0 : 0 ≤ c) (hP : 0 < degC P)
    (hg : ∀ z ∈ mcPts P, |g z - g' z| ≤ c) :
    |ptsIntegral P φ g - ptsIntegral P φ g'| ≤ c * degC P := by
  classical
  unfold ptsIntegral
  split_ifs with hΨ
  swap
  · simp only [sub_self, abs_zero]
    positivity
  unfold ptsIntegralAt
  rw [integral_unique, integral_unique]
  have hvol : (volume : Measure (Fin 0 → ℂ)).real Set.univ = 1 := by
    rw [Measure.real, MeasureTheory.volume_pi, Measure.pi_univ]
    simp
  rw [hvol, one_smul, one_smul]
  exact abs_fibreSum_sub_le P _ φ g g' hc0 hP hg _

end Fibres

theorem HeightMetricChange.proof (hpt : CurveComplexPoint.Statement) :
    HeightMetricChange.Statement := by
  intro K _ ι _ I P A A' c hI hA hA' ha hc W hW hPW
  obtain ⟨z₀, hz₀⟩ := hpt K ι W hW
  have hmc : ∀ z ∈ mcPts W, z ∈ mcPts P := fun z hz ↦ ⟨hz.1, fun f hf ↦ hz.2 f (hPW hf)⟩
  have hc0 : 0 ≤ c := (abs_nonneg _).trans (hc z₀ (hmc z₀ hz₀))
  obtain ⟨-, hAdd, hR⟩ := hI
  have hW' : IsArithVar W (0 + 1) := hW
  have hL : ∀ j : Fin 0, IsSmoothHerm ((Fin.elim0 : Fin 0 → ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) j) :=
    fun j ↦ j.elim0
  have hsnoc : ∀ C : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι,
      (Fin.snoc (Fin.elim0 : Fin 0 → ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) C : Fin 1 → _) = ![C] := by
    intro C
    funext i
    fin_cases i
    rfl
  have hAi : IsSmoothHerm A'.inv := isSmoothHerm_inv hA'
  have hadd := hAdd W 0 Fin.elim0 A A'.inv hW' hL hA hAi
  have hadd' := hAdd W 0 Fin.elim0 A' A'.inv hW' hL hA' hAi
  have hone : IsMultiHomog (1 : MRing ι) (0 : K → ℕ) := by
    intro m hm k
    classical
    rw [support_one] at hm
    simp [Finset.mem_singleton.mp hm]
  have h1W : (1 : MRing ι) ∉ W := fun h ↦ hW.2.1.1.ne_top ((Ideal.eq_top_iff_one _).mpr h)
  have hRD := hR W 0 Fin.elim0 (A.tensor A'.inv) 1 0 hW' hL (hA.mul hAi)
    (fun k ↦ by simp [HermLine.tensor, HermLine.inv, ha]) hone h1W
  have hRD' := hR W 0 Fin.elim0 (A'.tensor A'.inv) 1 0 hW' hL (hA'.mul hAi)
    (fun k ↦ by simp [HermLine.tensor, HermLine.inv]) hone h1W
  rw [hsnoc, hsnoc, hsnoc] at hadd hadd'
  rw [hsnoc] at hRD hRD'
  have key : I W 1 ![A] - I W 1 ![A'] =
      arInt W 1 (A'.tensor A'.inv) Fin.elim0 - arInt W 1 (A.tensor A'.inv) Fin.elim0 := by
    unfold recR at hRD hRD'
    linarith
  have hlog : ∀ z ∈ mcPts W, |logNorm (A'.tensor A'.inv) 1 z - logNorm (A.tensor A'.inv) 1 z| ≤ c := by
    intro z hz
    have hpA := A.pos z hz.1
    have hpA' := A'.pos z hz.1
    have e1 : logNorm (A'.tensor A'.inv) 1 z = 0 := by
      simp [logNorm, HermLine.tensor, HermLine.inv, hpA'.ne']
    have e2 : logNorm (A.tensor A'.inv) 1 z = - Real.log (A.h z / A'.h z) := by
      simp only [logNorm, HermLine.tensor, HermLine.inv, map_one, norm_one]
      rw [← Real.log_inv]
      congr 1
      field_simp
    rw [e1, e2, zero_sub, neg_neg]
    exact hc z (hmc z hz)
  unfold height
  rcases Nat.eq_zero_or_pos (degC W) with h0 | hpos
  · simp [h0, hc0]
  · have hd : (0 : ℝ) < degC W := by exact_mod_cast hpos
    rw [← sub_div, abs_div, abs_of_pos hd, div_le_iff₀ hd, key]
    exact abs_ptsIntegral_sub_le W _ _ _ hc0 hpos hlog

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.HeightsSet
