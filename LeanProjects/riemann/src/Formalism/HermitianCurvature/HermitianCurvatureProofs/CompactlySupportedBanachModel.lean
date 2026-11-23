import Formalism.HermitianCurvature.HermitianCurvatureProofs.DilationUnipotentWeylMeasure
import Formalism.HermitianCurvature.HermitianCurvatureProofs.BetaSesquilinearity
import Formalism.HermitianCurvature.StatementU
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.CayleyForm

open Matrix Filter Topology

noncomputable section

namespace Formalism.FourierDecayAlt.P.Ux1

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.B4

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {k r : ℕ}

section abstract

variable {𝔤 E : Type*} [NormedAddCommGroup 𝔤] [NormedSpace ℝ 𝔤] [NormedAddCommGroup E] [NormedSpace ℝ E]
  {ι : Type*} [Fintype ι]

lemma tuo_smulRight_sum {Ω : Set 𝔤} (a : ι → 𝔤 → (𝔤 →L[ℝ] ℝ)) (B : ℝ) (hB : ∀ i, ∀ Y ∈ Ω, ‖a i Y‖ ≤ B)
    (Ψ : ι → ℕ → 𝔤 → E) (L : ι → 𝔤 → E) (h : ∀ i, TendstoUniformlyOn (Ψ i) (L i) atTop Ω) :
    TendstoUniformlyOn (fun n Y => ∑ i, (a i Y).smulRight (Ψ i n Y))
      (fun Y => ∑ i, (a i Y).smulRight (L i Y)) atTop Ω := by
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  set B' := max B 1 with hB'def
  have hB' : 0 < B' := lt_of_lt_of_le one_pos (le_max_right _ _)
  set N : ℝ := (Fintype.card ι : ℝ) + 1 with hNdef
  have hN : 0 < N := by positivity
  have hη : 0 < ε / (B' * N) := by positivity
  have hev : ∀ᶠ n in atTop, ∀ i, ∀ Y ∈ Ω, dist (L i Y) (Ψ i n Y) < ε / (B' * N) := by
    rw [Filter.eventually_all]
    intro i
    exact (Metric.tendstoUniformlyOn_iff.1 (h i)) _ hη
  filter_upwards [hev] with n hn Y hY
  rw [dist_eq_norm, ← Finset.sum_sub_distrib]
  calc ‖∑ i, ((a i Y).smulRight (L i Y) - (a i Y).smulRight (Ψ i n Y))‖
      ≤ ∑ i, ‖(a i Y).smulRight (L i Y) - (a i Y).smulRight (Ψ i n Y)‖ := norm_sum_le _ _
    _ ≤ ∑ _i : ι, B' * (ε / (B' * N)) := by
        apply Finset.sum_le_sum
        intro i _
        have e : (a i Y).smulRight (L i Y) - (a i Y).smulRight (Ψ i n Y) =
            (a i Y).smulRight (L i Y - Ψ i n Y) := by
          ext v; simp [smul_sub]
        rw [e, ContinuousLinearMap.norm_smulRight_apply]
        have h1 := hn i Y hY
        rw [dist_eq_norm] at h1
        exact mul_le_mul (le_trans (hB i Y hY) (le_max_left _ _)) h1.le (norm_nonneg _) hB'.le
    _ = (Fintype.card ι : ℝ) * (ε / N) := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; field_simp
    _ < ε := by
        rw [mul_div_assoc', div_lt_iff₀ hN, hNdef]; nlinarith

theorem AL {Ω : Set 𝔤} (hΩ : IsOpen Ω) (a : ι → 𝔤 → (𝔤 →L[ℝ] ℝ))
    (ha : ∀ i, ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (a i) Ω) (B : ℝ) (hB : ∀ i, ∀ Y ∈ Ω, ‖a i Y‖ ≤ B) :
    ∀ (m : ℕ) (Ψ : List ι → ℕ → 𝔤 → E) (L : List ι → 𝔤 → E),
      (∀ w : List ι, w.length ≤ m → ∀ n, ContinuousOn (Ψ w n) Ω) →
      (∀ w : List ι, w.length < m → ∀ n, ∀ Y ∈ Ω,
        HasFDerivAt (Ψ w n) (∑ i, (a i Y).smulRight (Ψ (i :: w) n Y)) Y) →
      (∀ w : List ι, w.length ≤ m → TendstoUniformlyOn (Ψ w) (L w) atTop Ω) →
      ContDiffOn ℝ (m : WithTop ℕ∞) (L []) Ω := by
  intro m
  induction m with
  | zero =>
    intro Ψ L hc _ hu
    rw [Nat.cast_zero, contDiffOn_zero]
    exact (hu [] le_rfl).continuousOn (Filter.Frequently.of_forall fun n => hc [] le_rfl n)
  | succ m ih =>
    intro Ψ L hc hd hu
    have hL : ∀ j : ι, ContDiffOn ℝ (m : WithTop ℕ∞) (L [j]) Ω := by
      intro j
      have := ih (fun w => Ψ (w ++ [j])) (fun w => L (w ++ [j]))
        (fun w hw n => hc _ (by simp; omega) n)
        (fun w hw n Y hY => by simpa using hd (w ++ [j]) (by simp; omega) n Y hY)
        (fun w hw => hu _ (by simp; omega))
      simpa using this
    have hder : ∀ Y ∈ Ω, HasFDerivAt (L []) (∑ i, (a i Y).smulRight (L [i] Y)) Y := by
      intro Y hY
      exact hasFDerivAt_of_tendstoUniformlyOn hΩ
        (tuo_smulRight_sum a B hB (fun i => Ψ [i]) (fun i => L [i]) (fun i => hu [i] (by simp)))
        (fun n Y hY => hd [] (by simp) n Y hY) (fun Y hY => (hu [] (by simp)).tendsto_at hY) hY
    rw [show ((m + 1 : ℕ) : WithTop ℕ∞) = (m : WithTop ℕ∞) + 1 by push_cast; rfl,
      contDiffOn_succ_iff_fderiv_of_isOpen hΩ]
    refine ⟨fun Y hY => (hder Y hY).differentiableAt.differentiableWithinAt, fun h => ?_, ?_⟩
    · exact absurd h (by simp)
    · have hcd : ContDiffOn ℝ (m : WithTop ℕ∞) (fun Y => ∑ i, (a i Y).smulRight (L [i] Y)) Ω :=
        ContDiffOn.sum fun i _ => ((ha i).of_le (by exact_mod_cast le_top)).smulRight (hL i)
      exact hcd.congr fun Y hY => (hder Y hY).fderiv

end abstract

section smooth

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] {n : WithTop ℕ∞} {s : Set X}

lemma cdm_iff {F : X → Mat k r} :
    ContDiffOn ℝ n F s ↔ ∀ i j, ContDiffOn ℝ n (fun x => F x i j) s := by
  have := @contDiffOn_pi ℝ _ X _ _ s n (Fin (2 * r + k + 1)) _ (fun _ => Fin (2 * r + k + 1) → ℂ) _ _ F
  exact this.trans (forall_congr' fun i => contDiffOn_pi)

lemma cdm_mul {F G : X → Mat k r} (hF : ContDiffOn ℝ n F s) (hG : ContDiffOn ℝ n G s) :
    ContDiffOn ℝ n (fun x => F x * G x) s := by
  rw [cdm_iff] at hF hG ⊢
  intro i j
  simp only [Matrix.mul_apply]
  exact ContDiffOn.sum fun l _ => (hF i l).mul (hG l j)

lemma cd_det {F : X → Mat k r} (hF : ContDiffOn ℝ n F s) : ContDiffOn ℝ n (fun x => (F x).det) s := by
  rw [cdm_iff] at hF
  simp only [Matrix.det_apply']
  exact ContDiffOn.sum fun σ _ => contDiffOn_const.mul (contDiffOn_prod fun i _ => hF _ _)

lemma cdm_updateRow {F : X → Mat k r} (hF : ContDiffOn ℝ n F s) (j : Fin (2 * r + k + 1))
    (b : Fin (2 * r + k + 1) → ℂ) : ContDiffOn ℝ n (fun x => (F x).updateRow j b) s := by
  rw [cdm_iff] at hF ⊢
  intro a l
  by_cases ha : a = j
  · subst ha; simp only [updateRow_self]; exact contDiffOn_const
  · simp only [updateRow_ne ha]; exact hF a l

lemma cdm_inv {F : X → Mat k r} (hF : ContDiffOn ℝ n F s) (hu : ∀ x ∈ s, IsUnit (F x).det) :
    ContDiffOn ℝ n (fun x => (F x)⁻¹) s := by
  rw [cdm_iff]
  intro i j
  have e : (fun x => (F x)⁻¹ i j)
      = fun x => ((F x).det)⁻¹ * ((F x).updateRow j (Pi.single i 1)).det := by
    funext x
    rw [Matrix.inv_def, Matrix.smul_apply, adjugate_apply, Ring.inverse_eq_inv', smul_eq_mul]
  rw [e]
  exact ((cd_det hF).inv fun x hx => (hu x hx).ne_zero).mul (cd_det (cdm_updateRow hF j _))

end smooth

lemma hpk_herm : (Hpk k r)ᴴ = Hpk k r := (hpkFacts k r).1

lemma hpk_sq' : Hpk k r * Hpk k r = 1 := (hpkFacts k r).2.1

def prj (Z : Mat k r) : Mat k r := (1 / 2 : ℂ) • (Z - Hpk k r * Zᴴ * Hpk k r)

lemma prj_lie (Z : Mat k r) : inLie k r (prj Z) := by
  unfold inLie prj
  have hH := (hpk_herm (k := k) (r := r))
  have hHH := (hpk_sq' (k := k) (r := r))
  rw [conjTranspose_smul, conjTranspose_sub, conjTranspose_mul, conjTranspose_mul, hH,
    conjTranspose_conjTranspose]
  have h1 : Hpk k r * (Z * Hpk k r) * Hpk k r = Hpk k r * Z := by
    rw [Matrix.mul_assoc, Matrix.mul_assoc, hHH, Matrix.mul_one]
  have h2 : Hpk k r * (Hpk k r * Zᴴ * Hpk k r) = Zᴴ * Hpk k r := by
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hHH, Matrix.one_mul]
  have hs : star (1 / 2 : ℂ) = 1 / 2 := by simp
  rw [hs, Matrix.smul_mul, Matrix.mul_smul, Matrix.sub_mul, Matrix.mul_sub, h1, h2, ← smul_add]
  simp

lemma prj_of_lie {Z : Mat k r} (hZ : inLie k r Z) : prj Z = Z := by
  unfold prj
  have h0 : Zᴴ * Hpk k r = -(Hpk k r * Z) := eq_neg_of_add_eq_zero_left hZ
  have h1 : Hpk k r * Zᴴ * Hpk k r = -Z := by
    rw [Matrix.mul_assoc, h0, Matrix.mul_neg, ← Matrix.mul_assoc, hpk_sq', Matrix.one_mul]
  rw [h1, sub_neg_eq_add, ← two_smul ℂ Z, smul_smul]
  norm_num

lemma prj_add (Z Z' : Mat k r) : prj (Z + Z') = prj Z + prj Z' := by
  unfold prj
  rw [conjTranspose_add, Matrix.mul_add, Matrix.add_mul, ← smul_add]
  congr 1; abel

lemma prj_rsmul (c : ℝ) (Z : Mat k r) : prj (c • Z) = c • prj Z := by
  unfold prj
  rw [RCLike.real_smul_eq_coe_smul (K := ℂ) c Z, RCLike.real_smul_eq_coe_smul (K := ℂ) c,
    conjTranspose_smul]
  simp only [RCLike.star_def, RCLike.conj_ofReal]
  rw [Matrix.mul_smul, Matrix.smul_mul, ← smul_sub, smul_smul, smul_smul]
  congr 1; ring

lemma prj_zero : prj (0 : Mat k r) = 0 := by simp [prj]

lemma prj_sum {ι : Type*} (s : Finset ι) (c : ι → ℝ) (Z : ι → Mat k r) :
    prj (∑ i ∈ s, c i • Z i) = ∑ i ∈ s, c i • prj (Z i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [prj_zero]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, prj_add, prj_rsmul, ih]

def kap (Y : Mat k r) : Mat k r := (1 + Y) * (1 - Y)⁻¹

def iot (Z : Mat k r) : Mat k r := (Z - 1) * (Z + 1)⁻¹

lemma kap_mem {Y : Mat k r} (hY : inLie k r Y) (hu : IsUnit (1 - Y).det) : kap Y ∈ GV k r := by
  first | exact UpperTheory.Reformulated.B.Qj14.kap_mem .. | (apply UpperTheory.Reformulated.B.Qj14.kap_mem <;> assumption) | (intros; apply UpperTheory.Reformulated.B.Qj14.kap_mem <;> assumption) | (apply @UpperTheory.Reformulated.B.Qj14.kap_mem <;> assumption) | (intros; apply @UpperTheory.Reformulated.B.Qj14.kap_mem <;> assumption) | (apply @UpperTheory.Reformulated.B.Qj14.kap_mem <;> first | assumption | infer_instance) | exact @UpperTheory.Reformulated.B.Qj14.kap_mem k r Y hY hu | exact @UpperTheory.Reformulated.B.Qj14.kap_mem k r Y hY | exact @UpperTheory.Reformulated.B.Qj14.kap_mem k r Y | exact @UpperTheory.Reformulated.B.Qj14.kap_mem k r | exact @UpperTheory.Reformulated.B.Qj14.kap_mem k

lemma iot_facts {h : Mat k r} (hh : h ∈ GV k r) (hu : IsUnit (h + 1).det) :
    inLie k r (iot h) ∧ IsUnit (1 - iot h).det ∧ kap (iot h) = h := by
  have hh' : hᴴ * Hpk k r * h = Hpk k r := hh
  set D := h + 1 with hD
  set C := h - 1 with hC
  have hDD : D⁻¹ * D = 1 := Matrix.nonsing_inv_mul _ hu
  have hDD' : D * D⁻¹ = 1 := Matrix.mul_nonsing_inv _ hu
  have hZD : iot h * D = C := by
    unfold iot; rw [Matrix.mul_assoc, hDD, Matrix.mul_one]

  have h1Z : 1 - iot h = (2 : ℂ) • D⁻¹ := by
    have : (1 - iot h) * D = (2 : ℂ) • (1 : Mat k r) := by
      rw [Matrix.sub_mul, Matrix.one_mul, hZD, hD, hC]
      rw [two_smul]; abel
    calc 1 - iot h = (1 - iot h) * D * D⁻¹ := by rw [Matrix.mul_assoc, hDD', Matrix.mul_one]
      _ = (2 : ℂ) • D⁻¹ := by rw [this, Matrix.smul_mul, Matrix.one_mul]
  have hu1 : IsUnit (1 - iot h).det := by
    rw [h1Z, Matrix.det_smul]
    exact (IsUnit.pow _ (isUnit_iff_ne_zero.2 two_ne_zero)).mul (Matrix.isUnit_nonsing_inv_det _ hu)
  refine ⟨?_, hu1, ?_⟩
  ·
    have hDu : IsUnit (Dᴴ).det := by rw [det_conjTranspose]; exact hu.star
    have e1 : Cᴴ * Hpk k r * D = hᴴ * Hpk k r - Hpk k r * h := by
      rw [hC, hD, conjTranspose_sub, conjTranspose_one]
      calc (hᴴ - 1) * Hpk k r * (h + 1) = hᴴ * Hpk k r * h + hᴴ * Hpk k r - Hpk k r * h - Hpk k r := by
            noncomm_ring
        _ = hᴴ * Hpk k r - Hpk k r * h := by rw [hh']; abel
    have e2 : Dᴴ * Hpk k r * C = -(hᴴ * Hpk k r - Hpk k r * h) := by
      rw [hC, hD, conjTranspose_add, conjTranspose_one]
      calc (hᴴ + 1) * Hpk k r * (h - 1) = hᴴ * Hpk k r * h - hᴴ * Hpk k r + Hpk k r * h - Hpk k r := by
            noncomm_ring
        _ = -(hᴴ * Hpk k r - Hpk k r * h) := by rw [hh']; abel
    have e3 : Dᴴ * ((iot h)ᴴ * Hpk k r + Hpk k r * iot h) * D = 0 := by
      have : Dᴴ * ((iot h)ᴴ * Hpk k r + Hpk k r * iot h) * D
          = (iot h * D)ᴴ * Hpk k r * D + Dᴴ * Hpk k r * (iot h * D) := by
        rw [conjTranspose_mul]; simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc]
      rw [this, hZD, e1, e2, add_neg_cancel]
    have hDH : (Dᴴ)⁻¹ * Dᴴ = 1 := Matrix.nonsing_inv_mul _ hDu
    show (iot h)ᴴ * Hpk k r + Hpk k r * iot h = 0
    calc (iot h)ᴴ * Hpk k r + Hpk k r * iot h
        = (Dᴴ)⁻¹ * (Dᴴ * ((iot h)ᴴ * Hpk k r + Hpk k r * iot h) * D) * D⁻¹ := by
          simp only [← Matrix.mul_assoc, hDH, Matrix.one_mul]
          rw [Matrix.mul_assoc, hDD', Matrix.mul_one]
      _ = 0 := by rw [e3, Matrix.mul_zero, Matrix.zero_mul]
  ·
    have hp : (1 + iot h) * D = h * ((1 - iot h) * D) := by
      rw [Matrix.add_mul, Matrix.sub_mul, Matrix.one_mul, hZD, hD, hC]; noncomm_ring
    have hq : 1 + iot h = h * (1 - iot h) := by
      calc 1 + iot h = (1 + iot h) * D * D⁻¹ := by rw [Matrix.mul_assoc, hDD', Matrix.mul_one]
        _ = h * (1 - iot h) := by rw [hp, ← Matrix.mul_assoc, Matrix.mul_assoc _ D, hDD', Matrix.mul_one]
    unfold kap
    rw [hq, Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hu1, Matrix.mul_one]

section smooth2

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] {n : WithTop ℕ∞} {s : Set X}

lemma cdm_conjT {F : X → Mat k r} (hF : ContDiffOn ℝ n F s) : ContDiffOn ℝ n (fun x => (F x)ᴴ) s := by
  rw [cdm_iff] at hF ⊢
  intro i j
  simp only [Matrix.conjTranspose_apply]
  exact ((Complex.conjCLE : ℂ ≃L[ℝ] ℂ) : ℂ →L[ℝ] ℂ).contDiff.comp_contDiffOn (hF j i)

lemma cdm_prj {F : X → Mat k r} (hF : ContDiffOn ℝ n F s) : ContDiffOn ℝ n (fun x => prj (F x)) s := by
  unfold prj
  exact (hF.sub (cdm_mul (cdm_mul contDiffOn_const (cdm_conjT hF)) contDiffOn_const)).const_smul _

end smooth2

abbrev J (k r : ℕ) : Type := Fin (2 * r + k + 1) × Fin (2 * r + k + 1) × Bool

def Eb (i : J k r) : Mat k r :=
  Matrix.of fun p q => if p = i.1 ∧ q = i.2.1 then (if i.2.2 then Complex.I else 1) else 0

def Mv (Y : J k r → ℝ) : Mat k r :=
  Matrix.of fun p q => ((Y (p, q, false) : ℝ) : ℂ) + ((Y (p, q, true) : ℝ) : ℂ) * Complex.I

def co (Z : Mat k r) : J k r → ℝ := fun i => if i.2.2 then (Z i.1 i.2.1).im else (Z i.1 i.2.1).re

lemma Mv_co (Z : Mat k r) : Mv (co Z) = Z := by
  ext p q
  simp [Mv, co, Complex.re_add_im]

lemma Mv_sum (Y : J k r → ℝ) : Mv Y = ∑ i, Y i • Eb i := by
  ext p q
  rw [Matrix.sum_apply]
  simp only [Matrix.smul_apply, Eb, Matrix.of_apply, Mv, smul_ite, smul_zero, ite_and]
  rw [Fintype.sum_prod_type]
  simp only [Fintype.sum_prod_type, Fintype.sum_bool]
  simp only [Complex.real_smul, mul_one, if_true, if_false, Bool.false_eq_true]
  simp only [Finset.sum_add_distrib]
  rw [Finset.sum_eq_single p, Finset.sum_eq_single q, Finset.sum_eq_single p, Finset.sum_eq_single q]
  · simp [add_comm]
  all_goals first | (intro b _ hb; simp [Ne.symm hb]) | simp

lemma co_add (Z Z' : Mat k r) (i : J k r) : co (Z + Z') i = co Z i + co Z' i := by
  unfold co; split_ifs <;> simp

lemma co_smul (c : ℝ) (Z : Mat k r) (i : J k r) : co (c • Z) i = c * co Z i := by
  unfold co; split_ifs <;> simp [Complex.real_smul]

lemma co_zero (i : J k r) : co (0 : Mat k r) i = 0 := by
  unfold co; split_ifs <;> simp

lemma co_sum {ι : Type*} (s : Finset ι) (c : ι → ℝ) (Z : ι → Mat k r) (i : J k r) :
    co (∑ b ∈ s, c b • Z b) i = ∑ b ∈ s, c b * co (Z b) i := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [co_zero]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, co_add, co_smul, ih]

lemma cd_co {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] {n : WithTop ℕ∞} {s : Set X}
    {F : X → Mat k r} (hF : ContDiffOn ℝ n F s) (i : J k r) : ContDiffOn ℝ n (fun x => co (F x) i) s := by
  rw [cdm_iff] at hF
  unfold co
  by_cases h : i.2.2 = true
  · simp only [h, if_true]; exact Complex.imCLM.contDiff.comp_contDiffOn (hF _ _)
  · simp only [h]; exact Complex.reCLM.contDiff.comp_contDiffOn (hF _ _)

lemma cd_Mv : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Mv : (J k r → ℝ) → Mat k r) := by
  rw [← contDiffOn_univ, cdm_iff]
  intro p q
  simp only [Mv, Matrix.of_apply]
  exact ((Complex.ofRealCLM.contDiff.comp (contDiff_apply ℝ ℝ (p, q, false))).add
    ((Complex.ofRealCLM.contDiff.comp (contDiff_apply ℝ ℝ (p, q, true))).mul contDiff_const)).contDiffOn

def Lt (i : J k r) : Mat k r := (nrm (true, prj (Eb i))).2

lemma Lt_unit (i : J k r) : unitLie k r (Lt i) := nrm_unit (prj_lie _)

lemma prj_Eb (i : J k r) : prj (Eb i) = ‖prj (Eb i)‖ • Lt i := by
  rw [RCLike.real_smul_eq_coe_smul (K := ℂ)]
  exact nrm_smul _

def kc (i : J k r) (Z : Mat k r) : ℝ := co Z i * ‖prj (Eb i)‖

lemma expandL {Z : Mat k r} (hZ : inLie k r Z) : Z = ∑ i, kc i Z • Lt i := by
  conv_lhs => rw [← prj_of_lie hZ, ← Mv_co Z, Mv_sum, prj_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [prj_Eb, smul_smul]
  rfl

lemma kc_sum {ι : Type*} (s : Finset ι) (c : ι → ℝ) (Z : ι → Mat k r) (i : J k r) :
    kc i (∑ b ∈ s, c b • Z b) = ∑ b ∈ s, c b * kc i (Z b) := by
  unfold kc; rw [co_sum, Finset.sum_mul]
  exact Finset.sum_congr rfl fun b _ => by ring

def chart (g0 : Mat k r) (Y : J k r → ℝ) : Mat k r := kap (prj (Mv Y)) * g0

def Dom (k r : ℕ) : Set (J k r → ℝ) := {Y | IsUnit (1 - prj (Mv Y)).det}

lemma cd_prjMv : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun Y : J k r → ℝ => prj (Mv Y)) Set.univ :=
  cdm_prj cd_Mv.contDiffOn

lemma dom_open : IsOpen (Dom k r) := by
  have hc : Continuous (fun Y : J k r → ℝ => (1 - prj (Mv Y)).det) := by
    rw [← continuousOn_univ]
    exact (cd_det (contDiffOn_const.sub cd_prjMv)).continuousOn
  have : Dom k r = {Y : J k r → ℝ | (1 - prj (Mv Y)).det ≠ (fun _ => (0 : ℂ)) Y} := by
    ext Y; simp [Dom, isUnit_iff_ne_zero]
  rw [this]
  exact isOpen_ne_fun hc continuous_const

lemma zero_mem_dom : (0 : J k r → ℝ) ∈ Dom k r := by
  have h0 : Mv (0 : J k r → ℝ) = 0 := by ext p q; simp [Mv]
  simp [Dom, h0, prj_zero]

lemma chart_cd (g0 : Mat k r) : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (chart g0) (Dom k r) := by
  have hP := cd_prjMv (k := k) (r := r)
  unfold chart kap
  exact cdm_mul (cdm_mul (contDiffOn_const.add (hP.mono (Set.subset_univ _)))
    (cdm_inv (contDiffOn_const.sub (hP.mono (Set.subset_univ _))) fun Y hY => hY)) contDiffOn_const

lemma chart_mem {g0 : Mat k r} (hg0 : g0 ∈ GV k r) {Y : J k r → ℝ} (hY : Y ∈ Dom k r) :
    chart g0 Y ∈ GV k r :=
  Formalism.FourierDecayAlt.P.BetaSesquilinearity.gv_mul (kap_mem (prj_lie _) hY) hg0

lemma chart_diff (g0 : Mat k r) {Y : J k r → ℝ} (hY : Y ∈ Dom k r) : DifferentiableAt ℝ (chart g0) Y :=
  ((chart_cd g0).differentiableOn (by simp)).differentiableAt (dom_open.mem_nhds hY)

def mulB (k r : ℕ) : Mat k r →L[ℝ] Mat k r →L[ℝ] Mat k r :=
  LinearMap.toContinuousLinearMap
    { toFun := fun A => mulL A
      map_add' := fun A B => by ext g : 1; simp [mulL_apply, Matrix.add_mul]
      map_smul' := fun c A => by ext g : 1; simp [mulL_apply] }

lemma mulB_apply (A B : Mat k r) : mulB k r A B = A * B := rfl

def cT (k r : ℕ) : Mat k r →L[ℝ] Mat k r :=
  LinearMap.toContinuousLinearMap
    { toFun := fun A => Aᴴ
      map_add' := fun A B => conjTranspose_add A B
      map_smul' := fun c A => by
        simp only [RingHom.id_apply]
        rw [RCLike.real_smul_eq_coe_smul (K := ℂ), RCLike.real_smul_eq_coe_smul (K := ℂ),
          conjTranspose_smul]
        simp only [RCLike.star_def, RCLike.conj_ofReal] }

lemma cT_apply (A : Mat k r) : cT k r A = Aᴴ := rfl

lemma tangent {g0 : Mat k r} (hg0 : g0 ∈ GV k r) {Y : J k r → ℝ} (hY : Y ∈ Dom k r) (W : J k r → ℝ) :
    inLie k r (-(fderiv ℝ (chart g0) Y W) * (chart g0 Y)⁻¹) := by
  set c := chart g0 Y with hc
  set T := fderiv ℝ (chart g0) Y W with hT
  have hcG : c ∈ GV k r := chart_mem hg0 hY
  have hcu : IsUnit c.det := Formalism.QuantumDeterminants.WeylGroupFacts.isUnit_of_uh hcG
  set γ : ℝ → Mat k r := fun t => chart g0 (Y + t • W) with hγ
  have hline : HasDerivAt (fun t : ℝ => Y + t • W) W 0 := by
    have h := ((hasDerivAt_id (0:ℝ)).smul_const W).const_add Y
    rw [one_smul] at h
    exact h
  have hγd : HasDerivAt γ T 0 :=
    (chart_diff g0 hY).hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) hline (by simp)
  have hγ0 : γ 0 = c := by simp [hγ, hc]
  have h1 : HasDerivAt (fun t => cT k r (γ t)) (cT k r T) 0 :=
    (cT k r).hasFDerivAt.comp_hasDerivAt 0 hγd
  have h2 : HasDerivAt (fun t => mulB k r (cT k r (γ t)) (Hpk k r))
      (mulB k r (cT k r (γ 0)) 0 + mulB k r (cT k r T) (Hpk k r)) 0 :=
    ContinuousLinearMap.hasDerivAt_of_bilinear (fun _ => h1) (fun _ => hasDerivAt_const _ _)
  have h3 : HasDerivAt (fun t => mulB k r (mulB k r (cT k r (γ t)) (Hpk k r)) (γ t))
      (mulB k r (mulB k r (cT k r (γ 0)) (Hpk k r)) T +
        mulB k r (mulB k r (cT k r (γ 0)) 0 + mulB k r (cT k r T) (Hpk k r)) (γ 0)) 0 :=
    ContinuousLinearMap.hasDerivAt_of_bilinear (fun _ => h2) (fun _ => hγd)
  have hev : ∀ᶠ t in 𝓝 (0:ℝ), Y + t • W ∈ Dom k r :=
    ((continuous_const.add (continuous_id.smul continuous_const)).continuousAt (x := (0:ℝ))).preimage_mem_nhds
      (dom_open.mem_nhds (by simpa using hY))
  have h4 : HasDerivAt (fun t => mulB k r (mulB k r (cT k r (γ t)) (Hpk k r)) (γ t)) 0 0 := by
    refine (hasDerivAt_const (0:ℝ) (Hpk k r)).congr_of_eventuallyEq ?_
    filter_upwards [hev] with t ht
    have hm : γ t ∈ GV k r := chart_mem hg0 ht
    exact hm
  have hz := h3.unique h4
  simp only [mulB_apply, cT_apply, hγ0, Matrix.mul_zero, zero_add] at hz

  have hci : c * c⁻¹ = 1 := Matrix.mul_nonsing_inv _ hcu
  have hci' : (c⁻¹)ᴴ * cᴴ = 1 := by rw [← conjTranspose_mul, hci, conjTranspose_one]
  show (-T * c⁻¹)ᴴ * Hpk k r + Hpk k r * (-T * c⁻¹) = 0
  have : (-T * c⁻¹)ᴴ * Hpk k r + Hpk k r * (-T * c⁻¹)
      = -((c⁻¹)ᴴ * (cᴴ * Hpk k r * T + Tᴴ * Hpk k r * c) * c⁻¹) := by
    rw [conjTranspose_mul, conjTranspose_neg]
    simp only [Matrix.mul_add, Matrix.add_mul, Matrix.neg_mul, Matrix.mul_neg, ← Matrix.mul_assoc, hci']
    simp only [Matrix.mul_assoc, hci, Matrix.mul_one, Matrix.one_mul]
    abel
  rw [this, hz, Matrix.mul_zero, Matrix.zero_mul, neg_zero]

def ebv (b : J k r) : J k r → ℝ := fun j => if b = j then 1 else 0

def sC (g0 : Mat k r) (i b : J k r) (Y : J k r → ℝ) : ℝ :=
  kc i (-(fderiv ℝ (chart g0) Y (ebv b)) * (chart g0 Y)⁻¹)

def aC (g0 : Mat k r) (i : J k r) (Y : J k r → ℝ) : (J k r → ℝ) →L[ℝ] ℝ :=
  ∑ b, sC g0 i b Y • ContinuousLinearMap.proj b

lemma aC_apply (g0 : Mat k r) (i : J k r) (Y W : J k r → ℝ) :
    aC g0 i Y W = kc i (-(fderiv ℝ (chart g0) Y W) * (chart g0 Y)⁻¹) := by
  have hW : W = ∑ b, W b • ebv b := pi_eq_sum_univ W
  have e1 : -(fderiv ℝ (chart g0) Y W) * (chart g0 Y)⁻¹ =
      ∑ b, W b • (-(fderiv ℝ (chart g0) Y (ebv b)) * (chart g0 Y)⁻¹) := by
    conv_lhs => rw [hW]
    rw [map_sum, ← Finset.sum_neg_distrib, Finset.sum_mul]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [map_smul, ← smul_neg, Matrix.smul_mul]
  rw [e1, kc_sum]
  simp only [aC, FunLike.coe_sum, Finset.sum_apply, FunLike.coe_smul,
    Pi.smul_apply, ContinuousLinearMap.proj_apply, smul_eq_mul, sC]
  exact Finset.sum_congr rfl fun b _ => mul_comm _ _

lemma aC_cd {g0 : Mat k r} (hg0 : g0 ∈ GV k r) (i : J k r) :
    ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (aC g0 i) (Dom k r) := by
  have h1 : ∀ b, ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun Y => fderiv ℝ (chart g0) Y (ebv b)) (Dom k r) :=
    fun b => ((chart_cd g0).fderiv_of_isOpen dom_open (by simp)).clm_apply contDiffOn_const
  have h2 : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun Y => (chart g0 Y)⁻¹) (Dom k r) :=
    cdm_inv (chart_cd g0) fun Y hY => Formalism.QuantumDeterminants.WeylGroupFacts.isUnit_of_uh (chart_mem hg0 hY)
  have h3 : ∀ b, ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (sC g0 i b) (Dom k r) := by
    intro b
    unfold sC kc
    exact (cd_co (cdm_mul (h1 b).neg h2) i).mul contDiffOn_const
  unfold aC
  exact ContDiffOn.sum fun b _ => (h3 b).smul contDiffOn_const

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

lemma hasFDeriv_chart {g0 : Mat k r} (hg0 : g0 ∈ GV k r) {H : Mat k r → E}
    (hH : CkOn ((1 : ℕ) : ℕ∞) (GV k r) H) {Y : J k r → ℝ} (hY : Y ∈ Dom k r) :
    HasFDerivAt (fun Y' => H (chart g0 Y'))
      (∑ i, (aC g0 i Y).smulRight (op true (Lt i) H (chart g0 Y))) Y := by
  set c := chart g0 Y with hc
  have hcG : c ∈ GV k r := chart_mem hg0 hY
  have hcu : IsUnit c.det := Formalism.QuantumDeterminants.WeylGroupFacts.isUnit_of_uh hcG
  obtain ⟨U, h', hU, hcU, hcd, hff⟩ := hH c hcG
  have hdiff : DifferentiableAt ℝ h' c :=
    (hcd.differentiableOn (cast_ne_zero 0)).differentiableAt (hU.mem_nhds hcU)
  have hchd := chart_diff g0 hY
  have hcomp : HasFDerivAt (fun Y' => h' (chart g0 Y'))
      ((fderiv ℝ h' c).comp (fderiv ℝ (chart g0) Y)) Y :=
    hdiff.hasFDerivAt.comp Y hchd.hasFDerivAt
  have heq : (fun Y' => H (chart g0 Y')) =ᶠ[𝓝 Y] (fun Y' => h' (chart g0 Y')) := by
    filter_upwards [hchd.continuousAt.preimage_mem_nhds (hU.mem_nhds hcU), dom_open.mem_nhds hY]
      with Y' h1 h2
    exact hff _ h1 (chart_mem hg0 h2)
  refine (hcomp.congr_of_eventuallyEq heq).congr_fderiv ?_
  ext1 W
  rw [ContinuousLinearMap.comp_apply, _root_.sum_apply]
  simp only [ContinuousLinearMap.smulRight_apply]
  have hop : ∀ i, op true (Lt i) H c = fderiv ℝ h' c (-(Lt i * c)) := fun i =>
    op_eq_op' 0 true hU hcd hff (Lt_unit i).1 c hcU hcG
  simp_rw [hop, ← map_smul, ← map_sum]
  congr 1
  set Xv := -(fderiv ℝ (chart g0) Y W) * c⁻¹ with hXv
  have hXl : inLie k r Xv := tangent hg0 hY W
  have hA : ∀ i, aC g0 i Y W = kc i Xv := fun i => aC_apply g0 i Y W
  have hXc : Xv * c = -(fderiv ℝ (chart g0) Y W) := by
    rw [hXv, Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hcu, Matrix.mul_one]
  calc fderiv ℝ (chart g0) Y W = -(Xv * c) := by rw [hXc, neg_neg]
    _ = -((∑ i, kc i Xv • Lt i) * c) := by rw [← expandL hXl]
    _ = ∑ i, aC g0 i Y W • -(Lt i * c) := by
        simp only [hA, Finset.sum_mul, Matrix.smul_mul, smul_neg, Finset.sum_neg_distrib]

lemma tuo_of_bound {α F : Type*} [NormedAddCommGroup F] {G : ℕ → α → F} {f : α → F} {s : Set α} {B : ℝ}
    {ε : ℕ → ℝ} (hε : Tendsto ε atTop (𝓝 0)) (h : ∀ n, ∀ x ∈ s, ‖G n x - f x‖ ≤ B * ε n) :
    TendstoUniformlyOn G f atTop s := by
  rw [Metric.tendstoUniformlyOn_iff]
  intro δ hδ
  have hB : 0 < |B| + 1 := by positivity
  have hev := Metric.tendsto_nhds.1 hε (δ / (|B| + 1)) (by positivity)
  filter_upwards [hev] with n hn x hx
  rw [Real.dist_eq, sub_zero] at hn
  rw [dist_eq_norm, norm_sub_rev]
  calc ‖G n x - f x‖ ≤ B * ε n := h n x hx
    _ ≤ |B * ε n| := le_abs_self _
    _ = |B| * |ε n| := abs_mul _ _
    _ ≤ |B| * (δ / (|B| + 1)) := mul_le_mul_of_nonneg_left hn.le (abs_nonneg _)
    _ < δ := by
        rw [mul_div_assoc', div_lt_iff₀ hB]; nlinarith [abs_nonneg B]

lemma continuous_gN : Continuous (gN : Mat k r → ℝ) := by
  unfold gN
  exact Real.continuous_sqrt.comp (continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ =>
    Complex.continuous_normSq.comp ((continuous_apply j).comp (continuous_apply i)))

lemma gN_pos {g : Mat k r} (hg : g ∈ GV k r) : 0 < gN g := by
  have hu : IsUnit g.det := Formalism.QuantumDeterminants.WeylGroupFacts.isUnit_of_uh hg
  have hne : g ≠ 0 := by
    rintro rfl
    have : Nonempty (Fin (2 * r + k + 1)) := ⟨⟨0, by omega⟩⟩
    rw [Matrix.det_zero] at hu
    exact not_isUnit_zero hu
  obtain ⟨i, j, hij⟩ : ∃ i j, g i j ≠ 0 := by
    by_contra h; push Not at h; exact hne (Matrix.ext h)
  unfold gN
  apply Real.sqrt_pos.2
  calc (0:ℝ) < Complex.normSq (g i j) := Complex.normSq_pos.2 hij
    _ ≤ ∑ j', Complex.normSq (g i j') :=
        Finset.single_le_sum (f := fun j' => Complex.normSq (g i j'))
          (fun _ _ => Complex.normSq_nonneg _) (Finset.mem_univ j)
    _ ≤ ∑ i', ∑ j', Complex.normSq (g i' j') :=
        Finset.single_le_sum (f := fun i' => ∑ j', Complex.normSq (g i' j'))
          (fun _ _ => Finset.sum_nonneg fun _ _ => Complex.normSq_nonneg _) (Finset.mem_univ i)

lemma cv_continuous (b : Bool) (X g : Mat k r) : Continuous (fun t : ℝ => cv b X t g) := by
  rw [continuous_iff_continuousAt]
  intro t0
  have h := (cv_hasDerivAt b X (cv b X t0 g)).continuousAt
  have e : (fun t : ℝ => cv b X t g) = fun t => cv b X (t - t0) (cv b X t0 g) := by
    funext t; rw [← cv_add]; congr 1; ring
  rw [e]
  exact ContinuousAt.comp_of_eq (g := fun s => cv b X s (cv b X t0 g)) (f := fun t : ℝ => t - t0) h
    ((continuous_sub_right t0).continuousAt) (by ring)

lemma stepD {b : Bool} {X g : Mat k r} (hX : inLie k r X) (hg : g ∈ GV k r) (a : ℝ)
    (Hn : ℕ → Mat k r → E) (H0 H1 : Mat k r → E) (ε : ℕ → ℝ) (hε : Tendsto ε atTop (𝓝 0))
    (hC : ∀ n, CkOn ((1 : ℕ) : ℕ∞) (GV k r) (Hn n))
    (h0 : ∀ n, ∀ h ∈ GV k r, ‖Hn n h - H0 h‖ ≤ gN h ^ (-a) * ε n)
    (h1 : ∀ n, ∀ h ∈ GV k r, ‖op b X (Hn n) h - H1 h‖ ≤ gN h ^ (-a) * ε n) :
    op b X H0 g = H1 g := by
  set γ : ℝ → Mat k r := fun t => cv b X t g with hγ
  have hγc : Continuous γ := cv_continuous b X g
  have hγG : ∀ t, γ t ∈ GV k r := fun t => cv_mem hX hg t
  have hwc : ContinuousOn (fun t => gN (γ t) ^ (-a)) (Metric.closedBall (0:ℝ) 1) := by
    intro t _
    exact (ContinuousAt.comp_of_eq (g := fun x : ℝ => x ^ (-a)) (f := fun t => gN (γ t))
      (Real.continuousAt_rpow_const _ _ (Or.inl (gN_pos (hγG t)).ne'))
      ((continuous_gN.comp hγc).continuousAt) rfl).continuousWithinAt
  obtain ⟨Bw, hBw⟩ := (isCompact_closedBall (0:ℝ) 1).exists_bound_of_continuousOn hwc
  have hεa : Tendsto (fun n => |ε n|) atTop (𝓝 0) := by simpa using hε.abs
  have hbd : ∀ t ∈ Metric.ball (0:ℝ) 1, ∀ n, gN (γ t) ^ (-a) * ε n ≤ Bw * |ε n| := by
    intro t ht n
    calc gN (γ t) ^ (-a) * ε n ≤ |gN (γ t) ^ (-a) * ε n| := le_abs_self _
      _ = ‖gN (γ t) ^ (-a)‖ * |ε n| := by rw [abs_mul, Real.norm_eq_abs]
      _ ≤ Bw * |ε n| := mul_le_mul_of_nonneg_right (hBw t (Metric.ball_subset_closedBall ht))
          (abs_nonneg _)
  have tu0 : TendstoUniformlyOn (fun n t => Hn n (γ t)) (fun t => H0 (γ t)) atTop (Metric.ball (0:ℝ) 1) :=
    tuo_of_bound hεa fun n t ht => le_trans (h0 n _ (hγG t)) (hbd t ht n)
  have tu1 : TendstoUniformlyOn (fun n t => op b X (Hn n) (γ t)) (fun t => H1 (γ t)) atTop
      (Metric.ball (0:ℝ) 1) :=
    tuo_of_bound hεa fun n t ht => le_trans (h1 n _ (hγG t)) (hbd t ht n)
  have hder : ∀ n, ∀ t ∈ Metric.ball (0:ℝ) 1,
      HasDerivAt (fun t => Hn n (γ t)) (op b X (Hn n) (γ t)) t := by
    intro n t _
    have hd := ckOn_diff 0 b (hC n) hX (hγG t)
    have e : (fun t' => Hn n (γ t')) = fun t' => Hn n (cv b X (t' - t) (γ t)) := by
      funext t'; simp only [hγ]; rw [← cv_add]; congr 2; ring
    rw [e]
    have h2 : HasDerivAt (fun s => Hn n (cv b X s (γ t))) (op b X (Hn n) (γ t)) (t - t) := by
      rw [sub_self]; exact hd.hasDerivAt
    exact h2.comp_sub_const t t
  have key := hasDerivAt_of_tendstoUniformlyOn (l := atTop) (f := fun n t => Hn n (γ t))
    (g := fun t => H0 (γ t)) (f' := fun n t => op b X (Hn n) (γ t)) (g' := fun t => H1 (γ t))
    Metric.isOpen_ball tu1 (Eventually.of_forall hder) (fun t ht => tu0.tendsto_at ht)
    (Metric.mem_ball_self one_pos)
  have e0 : γ 0 = g := cv_zero b X g
  show deriv (fun t => H0 (cv b X t g)) 0 = H1 g
  rw [key.deriv]
  simp only [e0]

lemma limit_ident {a : ℝ} {mm : ℕ} (Fs : ℕ → Mat k r → E)
    (hC : ∀ n, CkOn ((mm : ℕ) : ℕ∞) (GV k r) (Fs n))
    (K : List (Mat k r) → List (Mat k r) → Mat k r → E) (ε : ℕ → ℝ) (hε : Tendsto ε atTop (𝓝 0))
    (hb : ∀ n (u w : List (Mat k r)), (∀ X ∈ u, unitLie k r X) → (∀ X ∈ w, unitLie k r X) →
      u.length + w.length ≤ mm → ∀ g ∈ GV k r, ‖dLR u w (Fs n) g - K u w g‖ ≤ gN g ^ (-a) * ε n) :
    ∀ u w : List (Mat k r), (∀ X ∈ u, unitLie k r X) → (∀ X ∈ w, unitLie k r X) →
      u.length + w.length ≤ mm → ∀ g ∈ GV k r, dLR u w (K [] []) g = K u w g := by
  have hck : ∀ n (u w : List (Mat k r)), (∀ X ∈ u, unitLie k r X) → (∀ X ∈ w, unitLie k r X) →
      u.length + w.length + 1 ≤ mm → CkOn ((1 : ℕ) : ℕ∞) (GV k r) (dLR u w (Fs n)) := by
    intro n u w hu hw hl
    rw [dLR_eq]
    exact smooth_on_of_word_derivatives _ (allLie_lr hu hw) 1 (ckOn_mono (by rw [length_lr]; omega) (hC n))
  have base : ∀ w : List (Mat k r), (∀ X ∈ w, unitLie k r X) → w.length ≤ mm →
      ∀ g ∈ GV k r, dLR [] w (K [] []) g = K [] w g := by
    intro w
    induction w with
    | nil => intro _ _ g _; rfl
    | cons X w ih =>
      intro hw hl g hg
      have hw' : ∀ Y ∈ w, unitLie k r Y := fun Y hY => hw Y (List.mem_cons_of_mem _ hY)
      have hX := hw X List.mem_cons_self
      have hl' : w.length + 1 ≤ mm := by simpa using hl
      show op false X (dLR [] w (K [] [])) g = K [] (X :: w) g
      rw [op_congr false hX.1 (ih hw' (by omega)) g hg]
      exact stepD hX.1 hg a (fun n => dLR [] w (Fs n)) (K [] w) (K [] (X :: w)) ε hε
        (fun n => hck n [] w (by simp) hw' (by simpa using hl'))
        (fun n h hh => hb n [] w (by simp) hw' (by simp; omega) h hh)
        (fun n h hh => hb n [] (X :: w) (by simp) hw (by simpa using hl) h hh)
  intro u
  induction u with
  | nil => intro w _ hw hl; exact base w hw (by simpa using hl)
  | cons X u ih =>
    intro w hu hw hl g hg
    have hu' : ∀ Y ∈ u, unitLie k r Y := fun Y hY => hu Y (List.mem_cons_of_mem _ hY)
    have hX := hu X List.mem_cons_self
    have hl' : u.length + w.length + 1 ≤ mm := by simp at hl; omega
    show op true X (dLR u w (K [] [])) g = K (X :: u) w g
    rw [op_congr true hX.1 (ih w hu' hw (by omega)) g hg]
    exact stepD hX.1 hg a (fun n => dLR u w (Fs n)) (K u w) (K (X :: u) w) ε hε
      (fun n => hck n u w hu' hw hl')
      (fun n h hh => hb n u w hu' hw (by omega) h hh)
      (fun n h hh => hb n (X :: u) w hu hw hl h hh)

lemma cont_chart {g0 : Mat k r} (hg0 : g0 ∈ GV k r) {H : Mat k r → E}
    (hH : CkOn ((0 : ℕ) : ℕ∞) (GV k r) H) : ContinuousOn (fun Y => H (chart g0 Y)) (Dom k r) := by
  intro Y hY
  apply ContinuousAt.continuousWithinAt
  obtain ⟨U, h', hU, hcU, hcd, hff⟩ := hH _ (chart_mem hg0 hY)
  have hchc : ContinuousAt (chart g0) Y := (chart_diff g0 hY).continuousAt
  have h1 : ContinuousAt (fun Y' => h' (chart g0 Y')) Y :=
    ContinuousAt.comp (g := h') (hcd.continuousOn.continuousAt (hU.mem_nhds hcU)) hchc
  refine h1.congr ?_
  filter_upwards [hchc.preimage_mem_nhds (hU.mem_nhds hcU), dom_open.mem_nhds hY] with Y' h1 h2
  exact (hff _ h1 (chart_mem hg0 h2)).symm

def rho (g0 : Mat k r) (x : Mat k r) : J k r → ℝ := co (iot (x * g0⁻¹))

def Sr (g0 : Mat k r) : Set (Mat k r) := {x | IsUnit (x * g0⁻¹ + 1).det}

lemma sr_open (g0 : Mat k r) : IsOpen (Sr g0) := by
  have hc : Continuous (fun x : Mat k r => (x * g0⁻¹ + 1).det) :=
    ((continuous_id.matrix_mul continuous_const).add continuous_const).matrix_det
  have : Sr g0 = {x : Mat k r | (x * g0⁻¹ + 1).det ≠ (fun _ => (0 : ℂ)) x} := by
    ext x; simp [Sr, isUnit_iff_ne_zero]
  rw [this]
  exact isOpen_ne_fun hc continuous_const

lemma rho_cd (g0 : Mat k r) : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (rho g0) (Sr g0) := by
  have h1 : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun x : Mat k r => x * g0⁻¹) (Sr g0) :=
    cdm_mul contDiffOn_id contDiffOn_const
  have h2 : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun x => iot (x * g0⁻¹)) (Sr g0) := by
    unfold iot
    exact cdm_mul (h1.sub contDiffOn_const) (cdm_inv (h1.add contDiffOn_const) fun x hx => hx)
  exact contDiffOn_pi.2 fun i => cd_co h2 i

lemma limit_ck {a : ℝ} {mm : ℕ} (Fs : ℕ → Mat k r → E)
    (hC : ∀ n, CkOn ((mm : ℕ) : ℕ∞) (GV k r) (Fs n))
    (K : List (Mat k r) → List (Mat k r) → Mat k r → E) (ε : ℕ → ℝ) (hε : Tendsto ε atTop (𝓝 0))
    (hε0 : ∀ n, 0 ≤ ε n)
    (hb : ∀ n (u w : List (Mat k r)), (∀ X ∈ u, unitLie k r X) → (∀ X ∈ w, unitLie k r X) →
      u.length + w.length ≤ mm → ∀ g ∈ GV k r, ‖dLR u w (Fs n) g - K u w g‖ ≤ gN g ^ (-a) * ε n) :
    CkOn ((mm : ℕ) : ℕ∞) (GV k r) (K [] []) := by
  intro g0 hg0

  obtain ⟨δ0, hδ0, hball⟩ := Metric.mem_nhds_iff.1 (dom_open.mem_nhds (zero_mem_dom (k := k) (r := r)))
  set δ := δ0 / 2 with hδ
  have hcl : Metric.closedBall (0 : J k r → ℝ) δ ⊆ Dom k r :=
    (Metric.closedBall_subset_ball (by rw [hδ]; linarith)).trans hball
  have hΩ : Metric.ball (0 : J k r → ℝ) δ ⊆ Dom k r := Metric.ball_subset_closedBall.trans hcl
  have hcomp : IsCompact (Metric.closedBall (0 : J k r → ℝ) δ) := isCompact_closedBall _ _

  have hwc : ContinuousOn (fun Y => gN (chart g0 Y) ^ (-a)) (Metric.closedBall (0 : J k r → ℝ) δ) :=
    (continuous_gN.comp_continuousOn ((chart_cd g0).continuousOn.mono hcl)).rpow_const
      fun Y hY => Or.inl (gN_pos (chart_mem hg0 (hcl hY))).ne'
  obtain ⟨Bw, hBw⟩ := hcomp.exists_bound_of_continuousOn hwc

  have hac : ContinuousOn (fun Y => ∑ i, ‖aC g0 i Y‖) (Metric.closedBall (0 : J k r → ℝ) δ) :=
    continuousOn_finsetSum _ fun i _ => ((aC_cd hg0 i).continuousOn.mono hcl).norm
  obtain ⟨Ba, hBa⟩ := hcomp.exists_bound_of_continuousOn hac
  have hBa' : ∀ i, ∀ Y ∈ Metric.ball (0 : J k r → ℝ) δ, ‖aC g0 i Y‖ ≤ Ba := by
    intro i Y hY
    have h1 := hBa Y (Metric.ball_subset_closedBall hY)
    rw [Real.norm_eq_abs, abs_of_nonneg (Finset.sum_nonneg fun _ _ => norm_nonneg _)] at h1
    exact (Finset.single_le_sum (f := fun i => ‖aC g0 i Y‖) (fun _ _ => norm_nonneg _)
      (Finset.mem_univ i)).trans h1
  have hunit : ∀ w : List (J k r), ∀ X ∈ w.map Lt, unitLie k r X := by
    intro w X hX
    obtain ⟨i, _, rfl⟩ := List.mem_map.1 hX
    exact Lt_unit i
  have hckw : ∀ n (w : List (J k r)) (m : ℕ), m + w.length ≤ mm →
      CkOn ((m : ℕ) : ℕ∞) (GV k r) (dLR (w.map Lt) [] (Fs n)) := by
    intro n w m hm
    rw [dLR_eq]
    exact smooth_on_of_word_derivatives _ (allLie_lr (hunit w) (by simp)) m
      (ckOn_mono (by rw [length_lr]; simp; omega) (hC n))
  have hAL := AL (𝔤 := J k r → ℝ) (E := E) Metric.isOpen_ball (aC g0)
    (fun i => (aC_cd hg0 i).mono hΩ) Ba hBa' mm
    (fun w n Y => dLR (w.map Lt) [] (Fs n) (chart g0 Y)) (fun w Y => K (w.map Lt) [] (chart g0 Y))
    (fun w hw n => (cont_chart hg0 (hckw n w 0 (by omega))).mono hΩ)
    (fun w hw n Y hY => hasFDeriv_chart hg0 (hckw n w 1 (by omega)) (hΩ hY))
    (fun w hw => tuo_of_bound hε fun n Y hY => by
      refine (hb n (w.map Lt) [] (hunit w) (by simp) (by simpa using hw) _ (chart_mem hg0 (hΩ hY))).trans ?_
      have h1 := hBw Y (Metric.ball_subset_closedBall hY)
      rw [Real.norm_eq_abs] at h1
      exact mul_le_mul_of_nonneg_right ((le_abs_self _).trans h1) (hε0 n))

  have hgu : IsUnit g0.det := Formalism.QuantumDeterminants.WeylGroupFacts.isUnit_of_uh hg0
  have hg1 : g0 * g0⁻¹ = 1 := Matrix.mul_nonsing_inv _ hgu
  set U := Sr g0 ∩ rho g0 ⁻¹' Metric.ball (0 : J k r → ℝ) δ with hUdef
  have hUo : IsOpen U := (rho_cd g0).continuousOn.isOpen_inter_preimage (sr_open g0) Metric.isOpen_ball
  have hg0U : g0 ∈ U := by
    have h2 : (1 + 1 : Mat k r) = (2 : ℂ) • (1 : Mat k r) := by rw [two_smul]
    refine ⟨?_, ?_⟩
    · show IsUnit (g0 * g0⁻¹ + 1).det
      rw [hg1, h2, Matrix.det_smul, Matrix.det_one, mul_one]
      exact (isUnit_iff_ne_zero.2 two_ne_zero).pow _
    · show rho g0 g0 ∈ Metric.ball (0 : J k r → ℝ) δ
      have h3 : rho g0 g0 = 0 := by
        funext i
        simp only [rho, hg1, iot, sub_self, Matrix.zero_mul]
        exact co_zero i
      rw [h3]; exact Metric.mem_ball_self (by rw [hδ]; linarith)
  refine ⟨U, fun x => K [] [] (chart g0 (rho g0 x)), hUo, hg0U, ?_, ?_⟩
  · have h4 : ContDiffOn ℝ ((mm : ℕ) : WithTop ℕ∞) (rho g0) U :=
      ((rho_cd g0).mono Set.inter_subset_left).of_le (by exact_mod_cast le_top)
    exact hAL.comp h4 (by intro x hx; exact hx.2)
  · intro x hx hxG
    have hh : x * g0⁻¹ ∈ GV k r := Formalism.FourierDecayAlt.P.BetaSesquilinearity.gv_mul hxG (Formalism.FourierDecayAlt.P.BetaSesquilinearity.gv_inv hg0)
    obtain ⟨hl, -, hk⟩ := iot_facts hh hx.1
    show K [] [] x = K [] [] (kap (prj (Mv (co (iot (x * g0⁻¹))))) * g0)
    rw [Mv_co, prj_of_lie hl, hk, Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hgu, Matrix.mul_one]

def Vd (mm : ℕ) (u w : List (Mat k r)) (g : Mat k r) : Prop :=
  (∀ X ∈ u, unitLie k r X) ∧ (∀ X ∈ w, unitLie k r X) ∧ u.length + w.length ≤ mm ∧ g ∈ GV k r

abbrev Idx (k r mm : ℕ) : Type := {p : (List (Mat k r) × List (Mat k r)) × Mat k r // Vd mm p.1.1 p.1.2 p.2}

abbrev Lp (k r mm : ℕ) (E : Type*) [NormedAddCommGroup E] : Type _ := lp (fun _ : Idx k r mm => E) ⊤

def Tf (a : ℝ) (mm : ℕ) (F : Mat k r → E) : Idx k r mm → E :=
  fun i => ((gN i.1.2 ^ a : ℝ) : ℂ) • dLR i.1.1.1 i.1.1.2 F i.1.2

open Classical in

def Kf (a : ℝ) {mm : ℕ} (x : Idx k r mm → E) (u w : List (Mat k r)) (g : Mat k r) : E :=
  if h : Vd mm u w g then ((gN g ^ (-a) : ℝ) : ℂ) • x ⟨((u, w), g), h⟩ else 0

lemma Kf_add (a : ℝ) {mm : ℕ} (f f' : Idx k r mm → E) (u w : List (Mat k r)) (g : Mat k r) :
    Kf a (f + f') u w g = Kf a f u w g + Kf a f' u w g := by
  unfold Kf; split_ifs
  · rw [Pi.add_apply, smul_add]
  · simp

lemma Kf_smul (a : ℝ) {mm : ℕ} (s : ℂ) (f : Idx k r mm → E) (u w : List (Mat k r)) (g : Mat k r) :
    Kf a (s • f) u w g = s • Kf a f u w g := by
  unfold Kf; split_ifs
  · rw [Pi.smul_apply, smul_comm]
  · simp

lemma norm_rsmul (x : ℝ) (hx : 0 ≤ x) (e : E) : ‖((x : ℝ) : ℂ) • e‖ = x * ‖e‖ := by
  rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hx]

lemma rsmul_cancel {g : Mat k r} (hg : g ∈ GV k r) (a : ℝ) (e : E) :
    ((gN g ^ (-a) : ℝ) : ℂ) • ((gN g ^ a : ℝ) : ℂ) • e = e := by
  rw [smul_smul, ← Complex.ofReal_mul, ← Real.rpow_add (gN_pos hg), neg_add_cancel, Real.rpow_zero,
    Complex.ofReal_one, one_smul]

lemma rsmul_cancel' {g : Mat k r} (hg : g ∈ GV k r) (a : ℝ) (e : E) :
    ((gN g ^ a : ℝ) : ℂ) • ((gN g ^ (-a) : ℝ) : ℂ) • e = e := by
  rw [smul_smul, ← Complex.ofReal_mul, ← Real.rpow_add (gN_pos hg), add_neg_cancel, Real.rpow_zero,
    Complex.ofReal_one, one_smul]

lemma Tf_inv {a : ℝ} {mm : ℕ} {x : Idx k r mm → E} {F : Mat k r → E} (hx : x = Tf a mm F)
    {u w : List (Mat k r)} {g : Mat k r} (h : Vd mm u w g) :
    dLR u w F g = ((gN g ^ (-a) : ℝ) : ℂ) • x ⟨((u, w), g), h⟩ := by
  rw [hx]; exact (rsmul_cancel h.2.2.2 a _).symm

lemma Kf_eq {a : ℝ} {mm : ℕ} {x : Idx k r mm → E} {F : Mat k r → E} (hx : x = Tf a mm F)
    {g : Mat k r} (hg : g ∈ GV k r) : Kf a x [] [] g = F g := by
  have h : Vd mm [] [] g := ⟨by simp, by simp, by simp, hg⟩
  rw [Kf, dif_pos h, ← Tf_inv hx h]; rfl

lemma dLR_zero (u v : List (Mat k r)) : dLR u v (0 : Mat k r → E) = 0 := by
  rw [dLR_eq]
  have := W_smul (lr u v) (0 : ℂ) (0 : Mat k r → E)
  simpa using this

lemma cc_zero (A : ℝ) (m : ℕ) : CCle A m (0 : Mat k r → E) 0 :=
  ⟨fun _ _ => ⟨Set.univ, 0, isOpen_univ, trivial, contDiffOn_const, fun _ _ _ => rfl⟩,
    fun u v _ _ _ g _ => by simp [dLR_zero]⟩

lemma ckOn_congr {F F' : Mat k r → E} {m : ℕ∞} (h : ∀ g ∈ GV k r, F g = F' g)
    (hF : CkOn m (GV k r) F) : CkOn m (GV k r) F' := by
  intro g0 hg0
  obtain ⟨U, f', hU, hgU, hc, hff⟩ := hF g0 hg0
  exact ⟨U, f', hU, hgU, hc, fun g hg hgG => (h g hgG).symm.trans (hff g hg hgG)⟩

lemma cc_congr {F F' : Mat k r → E} {A c : ℝ} {m : ℕ} (h : ∀ g ∈ GV k r, F g = F' g)
    (hF : CCle A m F c) : CCle A m F' c := by
  refine ⟨ckOn_congr h hF.1, fun u v hu hv hl g hg => ?_⟩
  have e : dLR u v F g = dLR u v F' g := by
    rw [dLR_eq, dLR_eq]; exact W_congr _ (allLie_lr hu hv) h g hg
  rw [← e]; exact hF.2 u v hu hv hl g hg

lemma dLR_add' {F F' : Mat k r → E} {A c c' : ℝ} {m : ℕ} (hF : CCle A m F c) (hF' : CCle A m F' c')
    {u v : List (Mat k r)} {g : Mat k r} (h : Vd m u v g) :
    dLR u v (F + F') g = dLR u v F g + dLR u v F' g := by
  have hl' : (lr u v).length ≤ m := by rw [length_lr]; exact h.2.2.1
  rw [dLR_eq, dLR_eq, dLR_eq]
  exact W_add _ (allLie_lr h.1 h.2.1) (ckOn_mono hl' hF.1) (ckOn_mono hl' hF'.1) g h.2.2.2

def Vs (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] (a : ℝ) (mm : ℕ) (S : Set (Mat k r)) : Submodule ℂ (Lp k r mm E) where
  carrier := {x | ∃ F : Mat k r → E, InCC a mm F ∧ (∀ g ∈ GV k r, g ∉ S → F g = 0) ∧ ⇑x = Tf a mm F}
  zero_mem' := ⟨0, ⟨0, cc_zero a mm⟩, fun _ _ _ => rfl, by funext i; simp [Tf, dLR_zero]⟩
  add_mem' := by
    rintro x y ⟨F, ⟨c, hF⟩, hFS, hx⟩ ⟨F', ⟨c', hF'⟩, hF'S, hy⟩
    refine ⟨F + F', ⟨c + c', (matrix_coefficient_linear k r E a mm F F' c c' 1 hF hF').1⟩,
      fun g hg hgS => by simp [hFS g hg hgS, hF'S g hg hgS], ?_⟩
    rw [lp.coeFn_add, hx, hy]
    funext i
    simp only [Pi.add_apply, Tf]
    rw [dLR_add' hF hF' i.2, smul_add]
  smul_mem' := by
    rintro s x ⟨F, ⟨c, hF⟩, hFS, hx⟩
    refine ⟨s • F, ⟨‖s‖ * c, (matrix_coefficient_linear k r E a mm F F c c s hF hF).2⟩,
      fun g hg hgS => by simp [hFS g hg hgS], ?_⟩
    rw [lp.coeFn_smul, hx]
    funext i
    simp only [Pi.smul_apply, Tf]
    have e : dLR i.1.1.1 i.1.1.2 (s • F) i.1.2 = s • dLR i.1.1.1 i.1.1.2 F i.1.2 := by
      rw [dLR_eq, dLR_eq, W_smul]; rfl
    rw [e, smul_comm]

lemma vs_closed {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] (a : ℝ) (mm : ℕ) (S : Set (Mat k r)) :
    IsClosed (Vs E a mm S : Set (Lp k r mm E)) := by
  refine IsSeqClosed.isClosed ?_
  intro xs v hxs hlim
  have hxs' : ∀ n, ∃ F : Mat k r → E, InCC a mm F ∧ (∀ g ∈ GV k r, g ∉ S → F g = 0) ∧
      ⇑(xs n) = Tf a mm F := hxs
  choose Fs hFs using hxs'
  set ε : ℕ → ℝ := fun n => ‖xs n - v‖ with hεdef
  have hε : Tendsto ε atTop (𝓝 0) := (tendsto_iff_norm_sub_tendsto_zero).1 hlim
  have hε0 : ∀ n, 0 ≤ ε n := fun n => norm_nonneg _
  have hC : ∀ n, CkOn ((mm : ℕ) : ℕ∞) (GV k r) (Fs n) := fun n => (hFs n).1.choose_spec.1
  set K := Kf a (⇑v) with hK
  have hb : ∀ n (u w : List (Mat k r)), (∀ X ∈ u, unitLie k r X) → (∀ X ∈ w, unitLie k r X) →
      u.length + w.length ≤ mm → ∀ g ∈ GV k r, ‖dLR u w (Fs n) g - K u w g‖ ≤ gN g ^ (-a) * ε n := by
    intro n u w hu hw hl g hg
    have h : Vd mm u w g := ⟨hu, hw, hl, hg⟩
    rw [Tf_inv (hFs n).2.2 h, hK, Kf, dif_pos h, ← smul_sub,
      norm_rsmul _ (Real.rpow_nonneg (gN_pos hg).le _)]
    refine mul_le_mul_of_nonneg_left ?_ (Real.rpow_nonneg (gN_pos hg).le _)
    have := lp.norm_apply_le_norm (p := ⊤) (by simp) (xs n - v) ⟨((u, w), g), h⟩
    simp only [lp.coeFn_sub, Pi.sub_apply] at this
    exact this
  have hid := limit_ident Fs hC K ε hε hb
  have hck := limit_ck Fs hC K ε hε hε0 hb
  refine ⟨K [] [], ⟨‖v‖, hck, ?_⟩, ?_, ?_⟩
  · intro u w hu hw hl g hg
    have h : Vd mm u w g := ⟨hu, hw, hl, hg⟩
    rw [hid u w hu hw hl g hg, hK, Kf, dif_pos h, norm_rsmul _ (Real.rpow_nonneg (gN_pos hg).le _),
      ← mul_assoc, ← Real.rpow_add (gN_pos hg), add_neg_cancel, Real.rpow_zero, one_mul]
    exact lp.norm_apply_le_norm (by simp) _ _
  · intro g hg hgS
    have h : Vd mm [] [] g := ⟨by simp, by simp, by simp, hg⟩
    have hz : ∀ n, xs n ⟨(([], []), g), h⟩ = 0 := by
      intro n
      rw [(hFs n).2.2]
      show ((gN g ^ a : ℝ) : ℂ) • Fs n g = 0
      rw [(hFs n).2.1 g hg hgS, smul_zero]
    have hv : ‖v ⟨(([], []), g), h⟩‖ ≤ 0 := by
      refine ge_of_tendsto' hε fun n => ?_
      have := lp.norm_apply_le_norm (p := ⊤) (by simp) (xs n - v) ⟨(([], []), g), h⟩
      simp only [lp.coeFn_sub, Pi.sub_apply, hz n, zero_sub, norm_neg] at this
      exact this
    rw [hK, Kf, dif_pos h, norm_le_zero_iff.1 hv, smul_zero]
  · funext i
    obtain ⟨⟨⟨u, w⟩, g⟩, h⟩ := i
    show v ⟨((u, w), g), h⟩ = ((gN g ^ a : ℝ) : ℂ) • dLR u w (K [] []) g
    rw [hid u w h.1 h.2.1 h.2.2.1 g h.2.2.2, hK, Kf, dif_pos h, rsmul_cancel' h.2.2.2]

def evL {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] (a : ℝ) (mm : ℕ) (S : Set (Mat k r)) :
    Vs E a mm S →ₗ[ℂ] (Mat k r → E) where
  toFun x := Kf a (⇑(x : Lp k r mm E)) [] []
  map_add' x y := by
    funext g
    show Kf a (⇑((x + y : Vs E a mm S) : Lp k r mm E)) [] [] g =
      Kf a (⇑(x : Lp k r mm E)) [] [] g + Kf a (⇑(y : Lp k r mm E)) [] [] g
    rw [Submodule.coe_add, lp.coeFn_add, Kf_add]
  map_smul' s x := by
    funext g
    show Kf a (⇑((s • x : Vs E a mm S) : Lp k r mm E)) [] [] g = s • Kf a (⇑(x : Lp k r mm E)) [] [] g
    rw [Submodule.coe_smul, lp.coeFn_smul, Kf_smul]

lemma mem_vs {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {a : ℝ} {mm : ℕ} {S : Set (Mat k r)}
    (x : Vs E a mm S) : ∃ F : Mat k r → E, InCC a mm F ∧ (∀ g ∈ GV k r, g ∉ S → F g = 0) ∧
      ⇑(x : Lp k r mm E) = Tf a mm F := x.2

def model {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] (a : ℝ) (mm : ℕ) (S : Set (Mat k r)) :
    Formalism.FourierDecayAlt.U.CCModel k r E a mm S (Vs E a mm S) where
  ev := evL a mm S
  mem x := by
    obtain ⟨F, ⟨c, hF⟩, -, hx⟩ := mem_vs x
    refine cc_congr (fun g hg => (Kf_eq hx hg).symm) ⟨hF.1, fun u v hu hv hl g hg => ?_⟩
    have h : Vd mm u v g := ⟨hu, hv, hl, hg⟩
    have e : ‖(x : Lp k r mm E) ⟨((u, v), g), h⟩‖ = gN g ^ a * ‖dLR u v F g‖ := by
      rw [hx]; exact norm_rsmul _ (Real.rpow_nonneg (gN_pos hg).le _) _
    rw [← e]; exact lp.norm_apply_le_norm (by simp) _ _
  least x c hc := by
    obtain ⟨F, -, -, hx⟩ := mem_vs x
    have hF : CCle a mm F c := cc_congr (fun g hg => Kf_eq hx hg) hc
    show ‖(x : Lp k r mm E)‖ ≤ c
    refine lp.norm_le_of_forall_le (cc_nonneg hF) fun i => ?_
    rw [hx]
    show ‖((gN i.1.2 ^ a : ℝ) : ℂ) • dLR i.1.1.1 i.1.1.2 F i.1.2‖ ≤ c
    rw [norm_rsmul _ (Real.rpow_nonneg (gN_pos i.2.2.2.2).le _)]
    exact hF.2 _ _ i.2.1 i.2.2.1 i.2.2.2.1 _ i.2.2.2.2
  off x g hg hgS := by
    obtain ⟨F, -, hFS, hx⟩ := mem_vs x
    show Kf a (⇑(x : Lp k r mm E)) [] [] g = 0
    rw [Kf_eq hx hg]; exact hFS g hg hgS
  surj F hF hFS := by
    obtain ⟨c, hc⟩ := hF
    have hm : Memℓp (Tf a mm F) ⊤ := by
      rw [memℓp_infty_iff]
      refine ⟨c, ?_⟩
      rintro _ ⟨i, rfl⟩
      show ‖((gN i.1.2 ^ a : ℝ) : ℂ) • dLR i.1.1.1 i.1.1.2 F i.1.2‖ ≤ c
      rw [norm_rsmul _ (Real.rpow_nonneg (gN_pos i.2.2.2.2).le _)]
      exact hc.2 _ _ i.2.1 i.2.2.1 i.2.2.2.1 _ i.2.2.2.2
    exact ⟨⟨⟨Tf a mm F, hm⟩, F, ⟨c, hc⟩, hFS, rfl⟩, fun g hg => Kf_eq rfl hg⟩

end Formalism.FourierDecayAlt.P.Ux1

namespace Formalism.FourierDecayAlt.P

theorem compactly_supported_banach_model : Formalism.FourierDecayAlt.U.CCModelExists := by
  intro k ρ E _ _ _ a mm S
  have : IsClosed (Ux1.Vs E a mm S : Set (Ux1.Lp k ρ mm E)) := Ux1.vs_closed a mm S
  exact ⟨Ux1.Vs E a mm S, inferInstance, inferInstance, IsClosed.completeSpace_coe,
    ⟨Ux1.model a mm S⟩⟩

end Formalism.FourierDecayAlt.P
