import Formalism.HermitianCurvature.HermitianCurvatureProofs.BigCellExpansionOfSubadditive

namespace Formalism.FourierDecayAlt.P.CutBP

open Formalism.FourierDecayAlt Formalism.QuantumDeterminants MeasureTheory Finset
open scoped ENNReal

noncomputable section

namespace LatticeNorms

def eI {n : ℕ} (I : Finset (Fin n)) : Fin n → ℤ := fun i => if i ∈ I then 1 else 0

def N1 {n : ℕ} (x : Fin n → ℤ) : ℕ := ∑ i, (x i).natAbs

def Ninf {n : ℕ} (x : Fin n → ℤ) : ℕ := Finset.univ.sup fun i => (x i).natAbs

lemma n1_add_le {n : ℕ} (x y : Fin n → ℤ) : N1 (x + y) ≤ N1 x + N1 y := by
  unfold N1
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun i _ => ?_
  simpa [Pi.add_apply] using Int.natAbs_add_le (x i) (y i)

lemma Ninf_add {n : ℕ} (x y : Fin n → ℤ) : Ninf (x + y) ≤ Ninf x + Ninf y := by
  unfold Ninf
  refine Finset.sup_le fun i hi => ?_
  have h := Int.natAbs_add_le (x i) (y i)
  have h1 : (x i).natAbs ≤ Finset.univ.sup fun i => (x i).natAbs := Finset.le_sup (f := fun i => (x i).natAbs) hi
  have h2 : (y i).natAbs ≤ Finset.univ.sup fun i => (y i).natAbs := Finset.le_sup (f := fun i => (y i).natAbs) hi
  simp only [Pi.add_apply]
  omega

lemma n1_zero {n : ℕ} : N1 (0 : Fin n → ℤ) = 0 := by
  simp [N1]

lemma Ninf_zero {n : ℕ} : Ninf (0 : Fin n → ℤ) = 0 := by
  unfold Ninf
  apply Nat.eq_zero_of_le_zero
  exact Finset.sup_le fun i _ => by simp

lemma n1_eI_eq_card {n : ℕ} (I : Finset (Fin n)) : N1 (eI I) = I.card := by
  unfold N1 eI
  have h : ∀ i, (if i ∈ I then (1 : ℤ) else 0).natAbs = if i ∈ I then 1 else 0 := fun i => by
    split_ifs <;> rfl
  simp only [h]
  rw [Finset.sum_boole]
  simp [Finset.filter_mem_eq_inter]

lemma Ninf_eI {n : ℕ} (I : Finset (Fin n)) : Ninf (eI I) ≤ 1 := by
  unfold Ninf
  refine Finset.sup_le fun i _ => ?_
  unfold eI
  split_ifs <;> simp

lemma eI_inj {n : ℕ} : Function.Injective (eI (n := n)) := by
  intro I J h
  ext i
  have := congrFun h i
  unfold eI at this
  by_cases hI : i ∈ I <;> by_cases hJ : i ∈ J <;> simp_all

open Classical in

def aF {n : ℕ} (S : Finset (Finset (Fin n))) (co : Finset (Fin n) → ℂ) : (Fin n → ℤ) →₀ ℂ :=
  Finsupp.mapDomain eI (Finsupp.onFinset S (fun I => if I ∈ S then co I else 0)
    (fun I hI => by by_contra h'; exact hI (if_neg h')))

lemma aF_sum {M : Type*} [AddCommMonoid M] {n : ℕ} (S : Finset (Finset (Fin n))) (co : Finset (Fin n) → ℂ)
    (h : (Fin n → ℤ) → ℂ → M) (h0 : ∀ ν, h ν 0 = 0) : (aF S co).sum h = ∑ I ∈ S, h (eI I) (co I) := by
  unfold aF
  rw [Finsupp.sum_mapDomain_index_inj eI_inj, Finsupp.onFinset_sum _ (fun a => h0 _)]
  exact Finset.sum_congr rfl fun I hI => by rw [if_pos hI]

lemma mem_supp_aF {n : ℕ} (S : Finset (Finset (Fin n))) (co : Finset (Fin n) → ℂ) (ν : Fin n → ℤ)
    (hν : ν ∈ (aF S co).support) : ∃ I ∈ S, ν = eI I := by
  classical
  have h1 := Finsupp.mapDomain_support hν
  rw [Finset.mem_image] at h1
  obtain ⟨I, hI, rfl⟩ := h1
  exact ⟨I, Finsupp.support_onFinset_subset hI, rfl⟩

end LatticeNorms

section place

variable {P : M.Par} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]

def scF (p : KB.Pl P Wp Wq) (F : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) : ℝ := (Real.sqrt (TBB.jN2 p F).toReal)⁻¹

def unitF (p : KB.Pl P Wp Wq) (F : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) : B.Mat P.k P.r → (Wq →L[ℂ] Wp) :=
  fun g => ((scF p F : ℝ) : ℂ) • F g

lemma V_csmul (p : KB.Pl P Wp Wq) (F : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (c : ℂ) (γ : C.LPt) :
    p.V (fun g => c • F g) γ = c • p.V F γ := by
  unfold KB.Pl.V D.vecV
  split_ifs with h1 h2
  · refine JCx1.needs.orbJ_smul_of_ae _ _ _ _ _ c (ae_of_all _ fun q => ?_)
    simp only [D.orbIntegrand, B.rho, ContinuousLinearMap.comp_smul, ContinuousLinearMap.smul_comp]
    rw [smul_comm]
  · simp
  · simp

lemma Ew_csmul (p : KB.Pl P Wp Wq) (F : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (c : ℂ) (γ : C.LPt) :
    TBB.Ew p (fun _ => 1) (fun g => c • F g) (P.r + 1) [] γ = ‖c‖ ^ 2 * TBB.Ew p (fun _ => 1) F (P.r + 1) [] γ := by
  have hv : ∀ A : Wq →L[ℂ] Wp, B.hsVec (c • A) = c • B.hsVec A := fun A => by
    ext i
    simp [B.hsVec]
  have hV : D.vecV p.T.base p.ν' p.m₀ (fun g => c • F g) γ = c • D.vecV p.T.base p.ν' p.m₀ F γ :=
    V_csmul p F c γ
  have hr : ¬ (P.r + 1 ≤ P.r) := by omega
  have hRR : p.RR (fun g => c • F g) (P.r + 1) [] γ γ = ((‖c‖ ^ 2 : ℝ) : ℂ) * p.RR F (P.r + 1) [] γ γ := by
    by_cases h : D.IsLocPt γ (P.r + 1)
    · simp only [KB.Pl.RR, D.RRplace, h, and_self, hr, dite_true, dite_false, if_true]
      rw [hV]
      unfold B.hsInner
      rw [hv, inner_smul_left, inner_smul_right, ← mul_assoc, Complex.conj_mul']
      push_cast
      ring
    · simp [KB.Pl.RR, D.RRplace, h]
  unfold TBB.Ew TBB.NP
  rw [hRR, ← mul_assoc, ← Complex.ofReal_mul, Complex.re_ofReal_mul, Complex.re_ofReal_mul]
  ring

lemma norm_sq_const_smul (p : KB.Pl P Wp Wq) (F : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (c : ℂ) :
    TBB.jN2 p (fun g => c • F g) = ENNReal.ofReal (‖c‖ ^ 2) * TBB.jN2 p F := by
  unfold TBB.jN2
  simp_rw [Ew_csmul, ENNReal.ofReal_mul (sq_nonneg ‖c‖)]
  exact MeasureTheory.lintegral_const_mul' _ _ ENNReal.ofReal_ne_top

lemma norm_sq_unit_normalization (p : KB.Pl P Wp Wq) (F : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (h0 : 0 < TBB.jN2 p F)
    (ht : TBB.jN2 p F < ⊤) : TBB.jN2 p (unitF p F) = 1 := by
  unfold unitF
  rw [norm_sq_const_smul]
  have ht0 : 0 < (TBB.jN2 p F).toReal := ENNReal.toReal_pos h0.ne' ht.ne
  have hs : ‖((scF p F : ℝ) : ℂ)‖ ^ 2 = ((TBB.jN2 p F).toReal)⁻¹ := by
    rw [Complex.norm_real, Real.norm_eq_abs, sq_abs, scF, inv_pow, Real.sq_sqrt ht0.le]
  rw [hs, ENNReal.ofReal_inv_of_pos ht0, ENNReal.ofReal_toReal ht.ne]
  exact ENNReal.inv_mul_cancel h0.ne' ht.ne

lemma norm_sq_unit_normalization_le (p : KB.Pl P Wp Wq) (F : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) : TBB.jN2 p (unitF p F) ≤ 1 := by
  rcases eq_or_ne (TBB.jN2 p F) 0 with h0 | h0
  · unfold unitF
    rw [norm_sq_const_smul, h0, mul_zero]
    exact zero_le_one
  rcases eq_or_ne (TBB.jN2 p F) ⊤ with ht | ht
  · unfold unitF
    rw [norm_sq_const_smul]
    have hs : scF p F = 0 := by simp [scF, ht]
    rw [hs]
    simp
  · exact (norm_sq_unit_normalization p F (pos_iff_ne_zero.mpr h0) (lt_top_iff_ne_top.mpr ht)).le

lemma meas_unitF (p : KB.Pl P Wp Wq) (F : B.Mat P.k P.r → (Wq →L[ℂ] Wp))
    (hm : AEMeasurable fun c : Fin (P.r + 1) → ℂ =>
      ENNReal.ofReal (TBB.Ew p (fun _ => 1) F (P.r + 1) [] (TBB.bigPt P.r c))) :
    AEMeasurable fun c : Fin (P.r + 1) → ℂ =>
      ENNReal.ofReal (TBB.Ew p (fun _ => 1) (unitF p F) (P.r + 1) [] (TBB.bigPt P.r c)) := by
  unfold unitF
  simp_rw [Ew_csmul, ENNReal.ofReal_mul (sq_nonneg ‖((scF p F : ℝ) : ℂ)‖)]
  exact hm.const_mul _

structure PieriExpansionData (P : M.Par) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] where
  n : ℕ
  J : (Fin n → ℤ) → B.Mat P.k P.r → (Wq →L[ℂ] Wp)
  lam : Fin n → ℤ
  tau : (Fin n → ℤ) → Finset (Fin n) → ℂ
  c0 : ℕ
  q0 : ℕ
  H : ℝ

def PieriExpansion (p : KB.Pl P Wp Wq) (d : PieriExpansionData P Wp Wq) : Prop :=
  ∀ μ, LatticeNorms.N1 (μ - d.lam) + d.c0 ≤ d.q0 → ∀ c : Fin (P.r + 1) → ℂ, D.IsLocPt (TBB.bigPt P.r c) (P.r + 1) →
    0 < TBB.Gp p (TBB.bigPt P.r c) →
    (D.ptMatN (TBB.bigPt P.r c) (P.r + 1)).det • p.V (d.J μ) (TBB.bigPt P.r c) =
      ∑ I ∈ powersetCard (P.r + 1) (univ : Finset (Fin d.n)),
        d.tau μ I • p.V (d.J (μ + LatticeNorms.eI I)) (TBB.bigPt P.r c)

def PieriCoefficientBound (d : PieriExpansionData P Wp Wq) : Prop :=
  ∀ μ, LatticeNorms.N1 (μ - d.lam) + d.c0 ≤ d.q0 → ∀ I ∈ powersetCard (P.r + 1) (univ : Finset (Fin d.n)),
    ‖d.tau μ I‖ ≤ d.H ^ (P.r + 1)

def PieriDegreeConditions (p : KB.Pl P Wp Wq) (d : PieriExpansionData P Wp Wq) : Prop :=
  0 < TBB.jN2 p (d.J d.lam) ∧
  (∀ μ, LatticeNorms.N1 (μ - d.lam) ≤ d.q0 → TBB.jN2 p (d.J μ) < ⊤ ∧
    (TBB.jN2 p (d.J μ) = 0 → ∀ c : Fin (P.r + 1) → ℂ, D.IsLocPt (TBB.bigPt P.r c) (P.r + 1) →
      0 < TBB.Gp p (TBB.bigPt P.r c) → p.V (d.J μ) (TBB.bigPt P.r c) = 0)) ∧
  ∀ μ, LatticeNorms.N1 (μ - d.lam) + d.c0 ≤ d.q0 → TBB.jN2 p (d.J μ) ≠ 0 →
    ∀ I ∈ powersetCard (P.r + 1) (univ : Finset (Fin d.n)),
    TBB.jN2 p (d.J (μ + LatticeNorms.eI I)) ≤ ENNReal.ofReal ((Real.exp 1 * d.n) ^ (P.r + 1)) * TBB.jN2 p (d.J μ)

def PieriMeasurability (p : KB.Pl P Wp Wq) (d : PieriExpansionData P Wp Wq) : Prop :=
  ∀ μ, AEMeasurable fun c : Fin (P.r + 1) → ℂ =>
    ENNReal.ofReal (TBB.Ew p (fun _ => 1) (d.J μ) (P.r + 1) [] (TBB.bigPt P.r c))

def pieriExpansionUnitFamily (p : KB.Pl P Wp Wq) (d : PieriExpansionData P Wp Wq) (μ : Fin d.n → ℤ) : B.Mat P.k P.r → (Wq →L[ℂ] Wp) :=
  unitF p (d.J μ)

theorem family_expansion_of_parts (p : KB.Pl P Wp Wq) (f : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (b C₃ : ℝ) (a₁ : ℕ)
    (d : PieriExpansionData P Wp Wq) (hf : f = unitF p (d.J d.lam)) (hH : 0 ≤ d.H) (hc0 : P.r + 1 ≤ d.c0)
    (hrange : (P.r + 1) * a₁ + d.c0 ≤ d.q0)
    (hGb : (2 * (d.n : ℝ) ^ (3 / 2 : ℝ) * d.H) ^ (P.r + 1) ≤ b ^ (C₃ * ((2 * P.r + 2 : ℕ) : ℝ) ^ 2))
    (hP : PieriExpansion p d) (hT : PieriCoefficientBound d) (hD : PieriDegreeConditions p d) (hM : PieriMeasurability p d) : FamilyDerivativeExpansion p f b C₃ a₁ := by
  classical
  have hn0 : (0 : ℝ) ≤ (d.n : ℝ) := Nat.cast_nonneg _
  have hGam0 : 0 ≤ 2 * (d.n : ℝ) ^ (3 / 2 : ℝ) * d.H :=
    mul_nonneg (mul_nonneg (by norm_num) (Real.rpow_nonneg hn0 _)) hH
  have hV0 : ∀ (F : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (c : Fin (P.r + 1) → ℂ),
      ¬ (D.IsLocPt (TBB.bigPt P.r c) (P.r + 1) ∧ 0 < TBB.Gp p (TBB.bigPt P.r c)) →
      p.V F (TBB.bigPt P.r c) = 0 := by
    intro F c hc
    unfold KB.Pl.V D.vecV
    split_ifs with h1 <;> first | rfl | exact absurd h1 hc
  have hfamV : ∀ ν (c : Fin (P.r + 1) → ℂ), p.V (pieriExpansionUnitFamily p d ν) (TBB.bigPt P.r c) =
      ((scF p (d.J ν) : ℝ) : ℂ) • p.V (d.J ν) (TBB.bigPt P.r c) := fun ν c => V_csmul p (d.J ν) _ _
  have hJV : ∀ ν (c : Fin (P.r + 1) → ℂ), LatticeNorms.N1 (ν - d.lam) ≤ d.q0 →
      D.IsLocPt (TBB.bigPt P.r c) (P.r + 1) → 0 < TBB.Gp p (TBB.bigPt P.r c) →
      p.V (d.J ν) (TBB.bigPt P.r c) =
        ((Real.sqrt (TBB.jN2 p (d.J ν)).toReal : ℝ) : ℂ) • p.V (pieriExpansionUnitFamily p d ν) (TBB.bigPt P.r c) := by
    intro ν c hν hl hg
    rw [hfamV, smul_smul, ← Complex.ofReal_mul]
    by_cases h0 : TBB.jN2 p (d.J ν) = 0
    · rw [(hD.2.1 ν hν).2 h0 c hl hg, smul_zero]
    · have ht := (hD.2.1 ν hν).1
      have hpos : 0 < Real.sqrt (TBB.jN2 p (d.J ν)).toReal :=
        Real.sqrt_pos.mpr (ENNReal.toReal_pos h0 ht.ne)
      rw [scF, mul_inv_cancel₀ hpos.ne', Complex.ofReal_one, one_smul]
  refine ⟨Fin d.n → ℤ, inferInstance, pieriExpansionUnitFamily p d, d.lam, LatticeNorms.N1, LatticeNorms.Ninf, d.c0, d.q0,
    2 * (d.n : ℝ) ^ (3 / 2 : ℝ) * d.H, ?_, hGam0, LatticeNorms.n1_add_le, LatticeNorms.Ninf_add, LatticeNorms.n1_zero, LatticeNorms.Ninf_zero, ?_,
    hrange, hGb, ?_, fun μ => meas_unitF p _ (hM μ)⟩
  · rw [hf]; rfl
  rotate_left
  · intro μ
    have hl : LatticeNorms.N1 (d.lam - d.lam) ≤ d.q0 := by rw [sub_self, LatticeNorms.n1_zero]; exact Nat.zero_le _
    rw [hf, norm_sq_unit_normalization p _ hD.1 (hD.2.1 d.lam hl).1]
    exact norm_sq_unit_normalization_le p _
  intro μ hμ
  set S := powersetCard (P.r + 1) (univ : Finset (Fin d.n)) with hS
  have hrngI : ∀ I ∈ S, LatticeNorms.N1 (μ + LatticeNorms.eI I - d.lam) ≤ d.q0 := by
    intro I hI
    have hc := (Finset.mem_powersetCard.mp hI).2
    calc LatticeNorms.N1 (μ + LatticeNorms.eI I - d.lam) = LatticeNorms.N1 ((μ - d.lam) + LatticeNorms.eI I) := by congr 1; abel
      _ ≤ LatticeNorms.N1 (μ - d.lam) + LatticeNorms.N1 (LatticeNorms.eI I) := LatticeNorms.n1_add_le _ _
      _ ≤ d.q0 := by rw [LatticeNorms.n1_eI_eq_card, hc]; omega
  let co : Finset (Fin d.n) → ℂ := fun I =>
    ((scF p (d.J μ) : ℝ) : ℂ) * d.tau μ I * ((Real.sqrt (TBB.jN2 p (d.J (μ + LatticeNorms.eI I))).toReal : ℝ) : ℂ)
  refine ⟨LatticeNorms.aF S co, ?_, ?_, ?_⟩
  · funext c
    rw [LatticeNorms.aF_sum S co (fun ν z => z • fun c => p.V (pieriExpansionUnitFamily p d (μ + ν)) (TBB.bigPt P.r c))
      (fun ν => zero_smul _ _), Finset.sum_apply]
    simp only [Pi.smul_apply]
    by_cases hg : D.IsLocPt (TBB.bigPt P.r c) (P.r + 1) ∧ 0 < TBB.Gp p (TBB.bigPt P.r c)
    · obtain ⟨hl, hG⟩ := hg
      rw [hfamV, smul_comm, hP μ hμ c hl hG, Finset.smul_sum]
      refine Finset.sum_congr rfl fun I hI => ?_
      rw [hJV _ c (hrngI I hI) hl hG, smul_smul, smul_smul]
    · rw [hV0 _ c hg, smul_zero]
      exact (Finset.sum_eq_zero fun I _ => by rw [hV0 _ c hg, smul_zero]).symm
  rotate_left
  · intro ν hν
    obtain ⟨I, hI, rfl⟩ := LatticeNorms.mem_supp_aF S co ν hν
    exact ⟨by rw [LatticeNorms.n1_eI_eq_card, (Finset.mem_powersetCard.mp hI).2], LatticeNorms.Ninf_eI I⟩
  rw [LatticeNorms.aF_sum S co (fun _ z => ‖z‖) (fun _ => norm_zero)]
  have hE0 : 0 ≤ (Real.exp 1 * d.n) ^ (P.r + 1) := pow_nonneg (mul_nonneg (Real.exp_pos 1).le hn0) _
  have hco : ∀ I ∈ S, ‖co I‖ ≤ d.H ^ (P.r + 1) * Real.sqrt ((Real.exp 1 * d.n) ^ (P.r + 1)) := by
    intro I hI
    have hbd : 0 ≤ d.H ^ (P.r + 1) * Real.sqrt ((Real.exp 1 * d.n) ^ (P.r + 1)) :=
      mul_nonneg (pow_nonneg hH _) (Real.sqrt_nonneg _)
    have hτ := hT μ hμ I hI
    by_cases h0 : TBB.jN2 p (d.J μ) = 0
    · have hz : scF p (d.J μ) = 0 := by simp [scF, h0]
      simp only [co, hz, Complex.ofReal_zero, zero_mul, norm_zero]
      exact hbd
    · have hμ' : LatticeNorms.N1 (μ - d.lam) ≤ d.q0 := by omega
      have ht := (hD.2.1 μ hμ').1
      have htpos : 0 < (TBB.jN2 p (d.J μ)).toReal := ENNReal.toReal_pos h0 ht.ne
      have hsμ : 0 < Real.sqrt (TBB.jN2 p (d.J μ)).toReal := Real.sqrt_pos.mpr htpos
      have hdeg := hD.2.2 μ hμ h0 I hI
      have hfin : ENNReal.ofReal ((Real.exp 1 * d.n) ^ (P.r + 1)) * TBB.jN2 p (d.J μ) ≠ ⊤ :=
        ENNReal.mul_ne_top ENNReal.ofReal_ne_top ht.ne
      have htI : (TBB.jN2 p (d.J (μ + LatticeNorms.eI I))).toReal ≤
          (Real.exp 1 * d.n) ^ (P.r + 1) * (TBB.jN2 p (d.J μ)).toReal := by
        have h1 := ENNReal.toReal_mono hfin hdeg
        rwa [ENNReal.toReal_mul, ENNReal.toReal_ofReal hE0] at h1
      have hsI : Real.sqrt (TBB.jN2 p (d.J (μ + LatticeNorms.eI I))).toReal ≤
          Real.sqrt ((Real.exp 1 * d.n) ^ (P.r + 1)) * Real.sqrt (TBB.jN2 p (d.J μ)).toReal := by
        rw [← Real.sqrt_mul hE0]
        exact Real.sqrt_le_sqrt htI
      have hnorm : ‖co I‖ = ‖d.tau μ I‖ * ((Real.sqrt (TBB.jN2 p (d.J μ)).toReal)⁻¹ *
          Real.sqrt (TBB.jN2 p (d.J (μ + LatticeNorms.eI I))).toReal) := by
        simp only [co, scF, norm_mul, Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg (inv_nonneg.mpr (Real.sqrt_nonneg (TBB.jN2 p (d.J μ)).toReal)),
          abs_of_nonneg (Real.sqrt_nonneg (TBB.jN2 p (d.J (μ + LatticeNorms.eI I))).toReal)]
        ring
      rw [hnorm]
      have hratio : (Real.sqrt (TBB.jN2 p (d.J μ)).toReal)⁻¹ *
          Real.sqrt (TBB.jN2 p (d.J (μ + LatticeNorms.eI I))).toReal ≤ Real.sqrt ((Real.exp 1 * d.n) ^ (P.r + 1)) := by
        calc _ ≤ (Real.sqrt (TBB.jN2 p (d.J μ)).toReal)⁻¹ * (Real.sqrt ((Real.exp 1 * d.n) ^ (P.r + 1)) *
              Real.sqrt (TBB.jN2 p (d.J μ)).toReal) := mul_le_mul_of_nonneg_left hsI (inv_nonneg.mpr hsμ.le)
          _ = Real.sqrt ((Real.exp 1 * d.n) ^ (P.r + 1)) := by
            rw [mul_comm (Real.sqrt ((Real.exp 1 * d.n) ^ (P.r + 1))), inv_mul_cancel_left₀ hsμ.ne']
      exact mul_le_mul hτ hratio (mul_nonneg (inv_nonneg.mpr hsμ.le) (Real.sqrt_nonneg _)) (pow_nonneg hH _)
  have hsq : Real.sqrt ((Real.exp 1 * d.n) ^ (P.r + 1)) =
      (Real.sqrt (Real.exp 1) * Real.sqrt d.n) ^ (P.r + 1) := by
    rw [← Real.sqrt_mul (Real.exp_pos 1).le, ← Real.sqrt_sq (pow_nonneg (Real.sqrt_nonneg (Real.exp 1 * d.n)) (P.r + 1))]
    congr 1
    rw [← pow_mul, mul_comm (P.r + 1) 2, pow_mul, Real.sq_sqrt (mul_nonneg (Real.exp_pos 1).le hn0)]
  have hn32 : (d.n : ℝ) ^ (3 / 2 : ℝ) = d.n * Real.sqrt d.n := by
    rw [show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num, Real.rpow_add' hn0 (by norm_num), Real.rpow_one,
      Real.sqrt_eq_rpow]
  have hse : Real.sqrt (Real.exp 1) ≤ 2 := by
    have h4 : Real.exp 1 ≤ 2 ^ 2 := by
      have := Real.exp_one_lt_d9
      norm_num at this ⊢
      linarith
    calc Real.sqrt (Real.exp 1) ≤ Real.sqrt (2 ^ 2) := Real.sqrt_le_sqrt h4
      _ = 2 := Real.sqrt_sq (by norm_num)
  have hcard : ((S.card : ℕ) : ℝ) ≤ (d.n : ℝ) ^ (P.r + 1) := by
    rw [hS, Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin]
    exact_mod_cast (Nat.choose_le_descFactorial _ _).trans (Nat.descFactorial_le_pow _ _)
  have hbase : 0 ≤ (d.n : ℝ) * d.H * (Real.sqrt (Real.exp 1) * Real.sqrt d.n) :=
    mul_nonneg (mul_nonneg hn0 hH) (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
  have hb2 : (d.n : ℝ) * d.H * (Real.sqrt (Real.exp 1) * Real.sqrt d.n) ≤ 2 * (d.n * Real.sqrt d.n) * d.H := by
    have h1 := mul_le_mul_of_nonneg_left hse (mul_nonneg (mul_nonneg hn0 hH) (Real.sqrt_nonneg (d.n : ℝ)))
    nlinarith [h1]
  calc ∑ I ∈ S, ‖co I‖ ≤ ∑ I ∈ S, d.H ^ (P.r + 1) * Real.sqrt ((Real.exp 1 * d.n) ^ (P.r + 1)) :=
        Finset.sum_le_sum hco
    _ = (S.card : ℝ) * (d.H ^ (P.r + 1) * Real.sqrt ((Real.exp 1 * d.n) ^ (P.r + 1))) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (d.n : ℝ) ^ (P.r + 1) * (d.H ^ (P.r + 1) * Real.sqrt ((Real.exp 1 * d.n) ^ (P.r + 1))) :=
        mul_le_mul_of_nonneg_right hcard (mul_nonneg (pow_nonneg hH _) (Real.sqrt_nonneg _))
    _ = ((d.n : ℝ) * d.H * (Real.sqrt (Real.exp 1) * Real.sqrt d.n)) ^ (P.r + 1) := by rw [hsq]; ring
    _ ≤ (2 * (d.n * Real.sqrt d.n) * d.H) ^ (P.r + 1) := by
        first
          | exact pow_le_pow_left₀ hbase hb2 _
          | exact pow_le_pow_left hbase hb2 _
    _ = (2 * (d.n : ℝ) ^ (3 / 2 : ℝ) * d.H) ^ (P.r + 1) := by rw [hn32]

theorem coefficient_growth_le_power (n r : ℕ) (b H CH C₃ : ℝ) (hb : 2 ≤ b) (hn : (n : ℝ) ≤ b) (hH : 0 ≤ H)
    (hHb : H ≤ b ^ (CH * ((2 * r + 2 : ℕ) : ℝ))) (hC : CH / 2 + 5 / 8 ≤ C₃) :
    (2 * (n : ℝ) ^ (3 / 2 : ℝ) * H) ^ (r + 1) ≤ b ^ (C₃ * ((2 * r + 2 : ℕ) : ℝ) ^ 2) := by
  have hb1 : (1 : ℝ) ≤ b := by linarith
  have hb0 : (0 : ℝ) < b := by linarith
  have hm : ((2 * r + 2 : ℕ) : ℝ) = 2 * (r : ℝ) + 2 := by push_cast; ring
  rw [hm] at hHb ⊢
  have hr0 : (0 : ℝ) ≤ r := Nat.cast_nonneg r
  have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  have h32 : (n : ℝ) ^ (3 / 2 : ℝ) ≤ b ^ (3 / 2 : ℝ) := Real.rpow_le_rpow hn0 hn (by norm_num)
  have hn32 : (0 : ℝ) ≤ (n : ℝ) ^ (3 / 2 : ℝ) := Real.rpow_nonneg hn0 _
  have hX0 : 0 ≤ 2 * (n : ℝ) ^ (3 / 2 : ℝ) * H := mul_nonneg (by positivity) hH
  have hX : 2 * (n : ℝ) ^ (3 / 2 : ℝ) * H ≤ b ^ ((5 / 2 : ℝ) + CH * (2 * (r : ℝ) + 2)) := by
    have e : b ^ ((5 / 2 : ℝ) + CH * (2 * (r : ℝ) + 2)) = b * b ^ (3 / 2 : ℝ) * b ^ (CH * (2 * (r : ℝ) + 2)) := by
      rw [Real.rpow_add hb0, show (5 / 2 : ℝ) = 1 + 3 / 2 by norm_num, Real.rpow_add hb0, Real.rpow_one]
    rw [e]
    have h1 : 2 * (n : ℝ) ^ (3 / 2 : ℝ) ≤ b * b ^ (3 / 2 : ℝ) := mul_le_mul hb h32 hn32 hb0.le
    exact mul_le_mul h1 hHb hH (mul_pos hb0 (Real.rpow_pos_of_pos hb0 _)).le
  have hpow : (2 * (n : ℝ) ^ (3 / 2 : ℝ) * H) ^ (r + 1) ≤ (b ^ ((5 / 2 : ℝ) + CH * (2 * (r : ℝ) + 2))) ^ (r + 1) := by
    first
      | exact pow_le_pow_left₀ hX0 hX (r + 1)
      | exact pow_le_pow_left hX0 hX (r + 1)
  refine hpow.trans ?_
  rw [← Real.rpow_natCast, ← Real.rpow_mul hb0.le]
  apply Real.rpow_le_rpow_of_exponent_le hb1
  push_cast
  nlinarith [mul_le_mul_of_nonneg_right hC (sq_nonneg (2 * (r : ℝ) + 2))]

theorem big_cell_expansion_of_parts (p : KB.Pl P Wp Wq) (f : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (b C₃ CH : ℝ) (a₁ : ℕ)
    (d : PieriExpansionData P Wp Wq) (hf : f = unitF p (d.J d.lam)) (hb : 2 ≤ b) (hn : (d.n : ℝ) ≤ b) (hH : 0 ≤ d.H)
    (hHb : d.H ≤ b ^ (CH * ((2 * P.r + 2 : ℕ) : ℝ))) (hC : CH / 2 + 5 / 8 ≤ C₃) (hc0 : P.r + 1 ≤ d.c0)
    (hrange : (P.r + 1) * a₁ + d.c0 ≤ d.q0)
    (hP : PieriExpansion p d) (hT : PieriCoefficientBound d) (hD : PieriDegreeConditions p d) (hM : PieriMeasurability p d) : BigCellDerivativeExpansion p f b C₃ a₁ :=
  big_cell_expansion_of_family p f b C₃ a₁ (by linarith)
    (family_expansion_of_parts p f b C₃ a₁ d hf hH hc0 hrange (coefficient_growth_le_power d.n P.r b d.H CH C₃ hb hn hH hHb hC) hP hT hD hM)

end place

end

end Formalism.FourierDecayAlt.P.CutBP
