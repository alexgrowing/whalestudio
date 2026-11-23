import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsRatioOfWeight
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GeometricallyConnectedOfIsIsoRestrict
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GramIsHermitianL2EqDoubleSum
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RealPartPosDefLogDetBoundOfConjugateComparableStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogLatticePointsQuadraticBallEstimateStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAdditiveSectionValueUnitFrameStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SectionValueUnitFrameConjPointEqPhaseConjStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GramPosDefL2LeSupOfLinIndepStatement

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSAmp

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.BallGram

def comb {K : Type} [AddCommGroup K] {r : ℕ} (f : Fin r → K) : (Fin r → ℤ) →+ K :=
  AddMonoidHom.mk' (fun z => ∑ i, z i • f i) fun z w => by
    simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib]

theorem comb_apply {K : Type} [AddCommGroup K] {r : ℕ} (f : Fin r → K) (z : Fin r → ℤ) :
    comb f z = ∑ i, z i • f i := rfl

theorem mem_closure_iff {K : Type} [AddCommGroup K] {r : ℕ} (f : Fin r → K) (g : K) :
    g ∈ AddSubgroup.closure (Set.range f) ↔ ∃ z, comb f z = g := by
  constructor
  · intro hg
    have hle : AddSubgroup.closure (Set.range f) ≤ (comb f).range := by
      rw [AddSubgroup.closure_le]
      rintro _ ⟨i, rfl⟩
      refine ⟨Pi.single i 1, ?_⟩
      simp [comb_apply, Pi.single_apply]
    exact hle hg
  · rintro ⟨z, rfl⟩
    rw [comb_apply]
    exact AddSubgroup.sum_mem _ fun i _ => AddSubgroup.zsmul_mem _ (AddSubgroup.subset_closure (Set.mem_range_self i)) _

theorem comb_injective {K : Type} [AddCommGroup K] {r : ℕ} (f : Fin r → K) (hf : LinearIndependent ℤ f) :
    Function.Injective (comb f) :=
  (injective_iff_map_eq_zero (comb f)).2 fun z hz => funext (Fintype.linearIndependent_iff.1 hf z hz)

end GlobalTheory.BallGram

namespace GlobalTheory.BallGram

variable {k : Type} [CommRing k] {X : Scheme.{0}} [IsIntegral X] {p : X ⟶ Sp k}

theorem val_comb (P : Pair p) (a b : ℤ) {r : ℕ} (f : Fin r → X.functionField) (hf : ∀ i, f i ∈ P.H a b)
    (σ : k →+* ℂ) (y : CxPts p σ) (z : Fin r → ℤ) :
    val P a b σ y (comb f z) = ∑ i, (z i : ℂ) * val P a b σ y (f i) := by
  obtain ⟨ℓ, hℓ⟩ := GlobalTheory.T.exists_additive_sectionValueUnitFrame k X p P a b σ y
  have hmem : comb f z ∈ P.H a b := by
    rw [comb_apply]
    exact AddSubgroup.sum_mem _ fun i _ => AddSubgroup.zsmul_mem _ (hf i) _
  have heq : (⟨comb f z, hmem⟩ : P.H a b) = ∑ i, z i • (⟨f i, hf i⟩ : P.H a b) := by
    apply Subtype.ext
    simp [comb_apply]
  rw [← hℓ ⟨comb f z, hmem⟩, heq, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_zsmul, hℓ, zsmul_eq_mul]

theorem nu_comb_sq (P : Pair p) (a b : ℤ) {r : ℕ} (f : Fin r → X.functionField) (hf : ∀ i, f i ∈ P.H a b)
    (σ : k →+* ℂ) (y : CxPts p σ) (z : Fin r → ℤ) :
    P.nu a b σ y (comb f z) ^ 2 = cmb (vals P a b f) (fun i => (z i : ℂ)) σ y := by
  rw [← norm_val, val_comb P a b f hf, cmb]
  rfl

theorem jacobi_field_square_integrable {S : Type} {Y : S → Type} [∀ σ, MeasurableSpace (Y σ)] {r : ℕ} (μ : ∀ σ, Measure (Y σ))
    (v : ∀ σ, Y σ → Fin r → ℂ) (h : IsFam μ v) (z : Fin r → ℤ) :
    l2 μ v (fun i => (z i : ℂ)) = ∑ i, ∑ j, (gram μ v).map Complex.re i j * (z i : ℝ) * (z j : ℝ) := by
  have h1 := congrArg Complex.re ((gram_isHermitian_and_l2_eq_quadratic_form S Y (Fin r) μ v h).2 (fun i => (z i : ℂ))).2.2
  rw [Complex.ofReal_re] at h1
  rw [h1, Complex.re_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Complex.re_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [map_intCast, Matrix.map_apply]
  simp [Complex.mul_re]
  ring

end GlobalTheory.BallGram

namespace GlobalTheory.BallGram

variable {k : Type} [CommRing k] {X : Scheme.{0}} [IsIntegral X] {p : X ⟶ Sp k}

theorem cmb_conj_le (P : Pair p) (a b : ℤ) {r : ℕ} (f : Fin r → X.functionField) (hf : ∀ i, f i ∈ P.H a b)
    (c : Fin r → ℂ) (B : ℝ) (hB : ∀ σ y, cmb (vals P a b f) c σ y ≤ B) (σ : k →+* ℂ) (y : CxPts p σ) :
    cmb (vals P a b f) (fun i => starRingEnd ℂ (c i)) σ y ≤ B := by
  obtain ⟨σ', y', θ, hθ, hval⟩ := GlobalTheory.T.sectionValueUnitFrame_conj_point_eq_phase_conj k X p P a b σ y
  refine le_trans (le_of_eq ?_) (hB σ' y')
  simp only [cmb, vals]
  have h : ∑ i, c i * val P a b σ' y' (f i) =
      θ * starRingEnd ℂ (∑ i, starRingEnd ℂ (c i) * val P a b σ y (f i)) := by
    rw [map_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hval _ (hf i), map_mul, Complex.conj_conj]
    ring
  rw [h, norm_mul, hθ, one_mul, Complex.norm_conj]

end GlobalTheory.BallGram

namespace GlobalTheory.BallGram

theorem count_ball_gram : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → GenSmooth p D → ∀ (P : Pair p) (ω : ∀ σ, VolDens p σ D) (a b : ℤ) (r : ℕ) (f : Fin r → X.functionField), (∀ i, f i ∈ P.H a b) → LinearIndependent ℤ f → ∀ (M Vv ρ R : ℝ), 1 ≤ M → 1 ≤ Vv → (∑ᶠ σ, ((ω σ).meas Set.univ).toReal) ≤ Vv → 0 ≤ ρ → 0 < R → (∀ (c : Fin r → ℂ) σ y, cmb (vals P a b f) c σ y ≤ M * l2 (fun σ => (ω σ).meas) (vals P a b f) c) → AddSubgroup.closure (Set.range f) ≤ AddSubgroup.closure (ballIn P (AddSubgroup.closure (Set.range f)) a b ρ) → 2 * r * ρ * (M * Vv) ≤ R → |Real.log ((ballIn P (AddSubgroup.closure (Set.range f)) a b R).ncard : ℝ) - (r * Real.log R - Real.log (gram (fun σ => (ω σ).meas) (vals P a b f)).det.re / 2 + Real.log (volume {x : Fin r → ℝ | ∑ i, x i ^ 2 ≤ 1}).toReal)| ≤ 2 * r * Real.log (2 * (M * Vv)) := by
  intro k _ X _ p D hX hS P ω a b r f hf hli M Vv ρ R hM hV hvol hρ hR hsup hgen hRρ
  obtain ⟨hfam, hpd, hbd⟩ := GlobalTheory.T.gram_posDef_l2_le_sup_of_lin_indep k X p D hX hS P ω a b (Fin r) f hf hli
  have hl2 := (gram_isHermitian_and_l2_eq_quadratic_form _ _ (Fin r) _ _ hfam).2
  set μ : ∀ σ, Measure (CxPts p σ) := fun σ => (ω σ).meas with hμ
  set v := vals P a b f with hv
  set G := gram μ v with hG
  set A := G.map Complex.re with hA
  set Λ := AddSubgroup.closure (Set.range f) with hΛ
  set φ := comb f with hφ
  have hinj : Function.Injective φ := comb_injective f hli
  set Q : (Fin r → ℤ) → ℝ := fun z => ∑ i, ∑ j, A i j * (z i : ℝ) * (z j : ℝ) with hQ
  have hQl2 : ∀ z, l2 μ v (fun i => (z i : ℂ)) = Q z := fun z => jacobi_field_square_integrable μ v hfam z
  have hnu0 : ∀ σ y g, 0 ≤ P.nu a b σ y g := fun σ y g => by rw [← norm_val]; exact norm_nonneg _
  have hM0 : 0 < M := by linarith
  have hV0 : 0 < Vv := by linarith
  have hin : ∀ z (R' : ℝ), 0 ≤ R' → Q z ≤ R' ^ 2 / M → φ z ∈ ballIn P Λ a b R' := by
    intro z R' hR' hz
    refine ⟨(mem_closure_iff f _).2 ⟨z, rfl⟩, fun σ y => ?_⟩
    have h1 : P.nu a b σ y (φ z) ^ 2 ≤ R' ^ 2 := by
      rw [nu_comb_sq P a b f hf]
      calc cmb v (fun i => (z i : ℂ)) σ y ≤ M * l2 μ v (fun i => (z i : ℂ)) := hsup _ σ y
        _ = M * Q z := by rw [hQl2]
        _ ≤ M * (R' ^ 2 / M) := mul_le_mul_of_nonneg_left hz hM0.le
        _ = R' ^ 2 := by field_simp
    exact (pow_le_pow_iff_left₀ (hnu0 σ y _) hR' two_ne_zero).1 h1
  have hout : ∀ z (R' : ℝ), φ z ∈ ballIn P Λ a b R' → Q z ≤ Vv * R' ^ 2 := by
    intro z R' hz
    have h1 : ∀ σ y, cmb v (fun i => (z i : ℂ)) σ y ≤ R' ^ 2 := fun σ y => by
      rw [← nu_comb_sq P a b f hf]
      exact pow_le_pow_left₀ (hnu0 σ y _) (hz.2 σ y) 2
    rw [← hQl2]
    calc l2 μ v (fun i => (z i : ℂ)) ≤ (∑ᶠ σ, ((ω σ).meas Set.univ).toReal) * R' ^ 2 := hbd _ _ h1
      _ ≤ Vv * R' ^ 2 := mul_le_mul_of_nonneg_right hvol (sq_nonneg _)
  have himg : ∀ R', ballIn P Λ a b R' = φ '' {z | φ z ∈ ballIn P Λ a b R'} := by
    intro R'
    ext g
    constructor
    · intro hg
      obtain ⟨z, rfl⟩ := (mem_closure_iff f g).1 hg.1
      exact ⟨z, hg, rfl⟩
    · rintro ⟨z, hz, rfl⟩
      exact hz
  have hcard : ∀ R', (ballIn P Λ a b R').ncard = {z | φ z ∈ ballIn P Λ a b R'}.ncard := fun R' =>
    (congrArg Set.ncard (himg R')).trans (Set.ncard_image_of_injective _ hinj)
  set T := {z | φ z ∈ ballIn P Λ a b ρ} with hT
  have hTtop : AddSubgroup.closure T = ⊤ := by
    rw [eq_top_iff]
    intro z _
    have h1 : φ z ∈ Λ := (mem_closure_iff f _).2 ⟨z, rfl⟩
    have h2 := hgen h1
    rw [himg ρ, ← AddMonoidHom.map_closure] at h2
    obtain ⟨w, hw, hwz⟩ := h2
    rwa [hinj hwz] at hw
  have hTQ : ∀ z ∈ T, ∑ i, ∑ j, A i j * (z i : ℝ) * (z j : ℝ) ≤ (ρ * √Vv) ^ 2 := fun z hz => by
    rw [mul_pow, Real.sq_sqrt hV0.le]
    have := hout z ρ hz
    simp only [hQ] at this
    linarith
  have hκ : 1 ≤ M * Vv := one_le_mul_of_one_le_of_one_le hM hV
  have hcomp : ∀ c : Fin r → ℂ, (∑ i, ∑ j, starRingEnd ℂ (c i) * c j * G i j).re ≤
      (M * Vv) * (∑ i, ∑ j, c i * starRingEnd ℂ (c j) * G i j).re := by
    intro c
    have e1 := (hl2 (fun i => starRingEnd ℂ (c i))).2.2
    simp only [Complex.conj_conj] at e1
    rw [← e1, ← (hl2 c).2.2, Complex.ofReal_re, Complex.ofReal_re]
    have h0 := (hl2 c).2.1
    calc l2 μ v (fun i => starRingEnd ℂ (c i)) ≤ (∑ᶠ σ, ((ω σ).meas Set.univ).toReal) * (M * l2 μ v c) :=
          hbd _ _ (cmb_conj_le P a b f hf c _ (hsup c))
      _ ≤ Vv * (M * l2 μ v c) := mul_le_mul_of_nonneg_right hvol (mul_nonneg hM0.le h0)
      _ = M * Vv * l2 μ v c := by ring
  obtain ⟨hApd, hdet⟩ := GlobalTheory.T.realPart_posDef_logDet_bound_of_conjugate_comparable (Fin r) G (M * Vv) hpd hκ hcomp
  have hsM : 0 < √M := Real.sqrt_pos.2 hM0
  have hsV : 0 < √Vv := Real.sqrt_pos.2 hV0
  set R1 := R / √M with hR1d
  set R2 := R * √Vv with hR2d
  have hR1 : 0 < R1 := div_pos hR hsM
  have hR2 : 0 < R2 := mul_pos hR hsV
  have hρ' : 0 ≤ ρ * √Vv := mul_nonneg hρ hsV.le
  have hcardr : (Fintype.card (Fin r) : ℝ) = r := by simp
  have hsq : √M * √Vv ≤ M * Vv := by
    rw [← Real.sqrt_mul hM0.le]
    calc √(M * Vv) ≤ √(M * Vv) * √(M * Vv) :=
          le_mul_of_one_le_right (Real.sqrt_nonneg _) (Real.one_le_sqrt.mpr hκ)
      _ = M * Vv := Real.mul_self_sqrt (by positivity)
  have h2rρ : 0 ≤ 2 * (r : ℝ) * ρ := by positivity
  have hb1 : 2 * (Fintype.card (Fin r) : ℝ) * (ρ * √Vv) ≤ R1 := by
    rw [hcardr, hR1d, le_div_iff₀ hsM]
    calc 2 * (r : ℝ) * (ρ * √Vv) * √M = 2 * r * ρ * (√M * √Vv) := by ring
      _ ≤ 2 * r * ρ * (M * Vv) := mul_le_mul_of_nonneg_left hsq h2rρ
      _ ≤ R := hRρ
  have hb2 : 2 * (Fintype.card (Fin r) : ℝ) * (ρ * √Vv) ≤ R2 := by
    rw [hcardr, hR2d]
    calc 2 * (r : ℝ) * (ρ * √Vv) = (2 * r * ρ) * √Vv := by ring
      _ ≤ R * √Vv := mul_le_mul_of_nonneg_right (le_trans (le_mul_of_one_le_right h2rρ hκ) hRρ) hsV.le
  have c1 := GlobalTheory.T.log_lattice_points_quadratic_ball_estimate (Fin r) A hApd T (ρ * √Vv) R1 hρ' hR1 hTtop hTQ hb1
  have c2 := GlobalTheory.T.log_lattice_points_quadratic_ball_estimate (Fin r) A hApd T (ρ * √Vv) R2 hρ' hR2 hTtop hTQ hb2
  set B := {z | φ z ∈ ballIn P Λ a b R} with hB
  have hsub1 : {z : Fin r → ℤ | ∑ i, ∑ j, A i j * (z i : ℝ) * (z j : ℝ) ≤ R1 ^ 2} ⊆ B := fun z hz => by
    refine hin z R hR.le ?_
    have hz' : ∑ i, ∑ j, A i j * (z i : ℝ) * (z j : ℝ) ≤ R1 ^ 2 := hz
    rw [hR1d, div_pow, Real.sq_sqrt hM0.le] at hz'
    exact hz'
  have hsub2 : B ⊆ {z : Fin r → ℤ | ∑ i, ∑ j, A i j * (z i : ℝ) * (z j : ℝ) ≤ R2 ^ 2} := fun z hz => by
    show ∑ i, ∑ j, A i j * (z i : ℝ) * (z j : ℝ) ≤ R2 ^ 2
    rw [hR2d, mul_pow, Real.sq_sqrt hV0.le]
    have := hout z R hz
    simp only [hQ] at this
    linarith
  have hfin : B.Finite := c2.1.subset hsub2
  have hn1 : ellCount A R1 ≤ B.ncard := Set.ncard_le_ncard hsub1 hfin
  have hn2 : B.ncard ≤ ellCount A R2 := Set.ncard_le_ncard hsub2 c2.1
  have hpos : 0 < ellCount A R1 := (Set.ncard_pos c1.1).2 ⟨0, by simp; positivity⟩
  rw [hcard R]
  have l1 : Real.log (ellCount A R1) ≤ Real.log B.ncard :=
    Real.log_le_log (by exact_mod_cast hpos) (by exact_mod_cast hn1)
  have l2' : Real.log B.ncard ≤ Real.log (ellCount A R2) :=
    Real.log_le_log (by exact_mod_cast (lt_of_lt_of_le hpos hn1)) (by exact_mod_cast hn2)
  have lr1 : Real.log R1 = Real.log R - Real.log M / 2 := by
    rw [hR1d, Real.log_div hR.ne' hsM.ne', Real.log_sqrt hM0.le]
  have lr2 : Real.log R2 = Real.log R + Real.log Vv / 2 := by
    rw [hR2d, Real.log_mul hR.ne' hsV.ne', Real.log_sqrt hV0.le]
  have c1b := c1.2
  have c2b := c2.2
  rw [hcardr, lr1] at c1b
  rw [hcardr, lr2] at c2b
  rw [hcardr] at hdet
  have hx : M * Vv ≤ 2 * (M * Vv) := le_mul_of_one_le_left (by positivity) (by norm_num)
  have hlM : Real.log M ≤ Real.log (2 * (M * Vv)) :=
    Real.log_le_log hM0 ((le_mul_of_one_le_right hM0.le hV).trans hx)
  have hlV : Real.log Vv ≤ Real.log (2 * (M * Vv)) :=
    Real.log_le_log hV0 ((le_mul_of_one_le_left hV0.le hM).trans hx)
  have hlt : Real.log 2 ≤ Real.log (2 * (M * Vv)) :=
    Real.log_le_log (by norm_num) (le_mul_of_one_le_right (by norm_num) hκ)
  have hr0 : (0 : ℝ) ≤ r := Nat.cast_nonneg r
  have m1 := mul_le_mul_of_nonneg_left hlM hr0
  have m2 := mul_le_mul_of_nonneg_left hlV hr0
  have m3 := mul_le_mul_of_nonneg_left hlt hr0
  obtain ⟨c1x, c1y⟩ := abs_le.1 c1b
  obtain ⟨c2x, c2y⟩ := abs_le.1 c2b
  obtain ⟨dx, dy⟩ := abs_le.1 hdet
  rw [abs_le]
  constructor <;> linarith

end GlobalTheory.BallGram
