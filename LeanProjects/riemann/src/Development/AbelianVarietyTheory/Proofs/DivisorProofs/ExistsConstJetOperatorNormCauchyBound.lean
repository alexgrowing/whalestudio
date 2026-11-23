import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EmbLLMem
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PairIntAt
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.SumFinsuppAntidiagProdPowDivMultiFactorial
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsMulOfApprox
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FockNormExtremalVectorEqBoundedNat
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.MonomialDerivCauchyBoundGaussianGrowth
import Formalism.GradedWeylDivisibility.FockSpaceTableaux.SumIcoTsubTelescope

open MvPolynomial Formalism.BasicNotions Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.MvPoly
open GlobalTheory.IndefiniteRowSideFullHecke.SubstitutionAdjoint (sharp)
open GlobalTheory.JetPoint (expL expR)

noncomputable section

namespace GlobalTheory.FockJetBound

theorem fockS_self {σ : Type} (f : MvPolynomial σ ℂ) : fockS f f = ((fockNormSq f : ℝ) : ℂ) := by
  simp only [fockS, fockNormSq, Complex.ofReal_sum, Complex.ofReal_mul, Complex.ofReal_pow, Complex.ofReal_natCast]
  refine Finset.sum_congr rfl fun m _ => ?_
  have hm : (mfact m : ℂ) = (multiFactorial m : ℂ) := rfl
  rw [show star (f.coeff m) = (starRingEnd ℂ) (f.coeff m) from rfl, Complex.conj_mul', hm]
  ring

def eNorm {n : ℕ} (l : DomWeight n) : ℝ := fockNormSq (extremal ℂ n l)

theorem one_le_eNorm {n : ℕ} (l : DomWeight n) : 1 ≤ eNorm l := by
  obtain ⟨s, hs, -, h⟩ := GlobalTheory.ExtremalNorm.fockS_extremal_eq_nat n l (∑ i, l.natW i)
    (fun i => Finset.single_le_sum (fun j _ => Nat.zero_le _) (Finset.mem_univ i))
  have h2 := h ℂ
  rw [fockS_self] at h2
  have h3 : fockNormSq (extremal ℂ n l) = (s : ℝ) := by exact_mod_cast h2
  unfold eNorm
  rw [h3]
  exact_mod_cast hs

theorem pairK_re {ι : Type} [Fintype ι] {n : ℕ} (lam : ι → DomWeight n) (v : VV ℂ lam) :
    (pairK lam (fun _ => (1 : Matrix (Fin n) (Fin n) ℂ)) v v).re =
      fockNormSq (v : Pol ℂ ι n) / ∏ τ, eNorm (lam τ) := by
  have hG : gramTw lam (fun _ : ι => (1 : Matrix (Fin n) (Fin n) ℂ)) = 1 := by
    simp [gramTw]
  have hE : extNorm ℂ lam = ((∏ τ, eNorm (lam τ) : ℝ) : ℂ) := by
    simp only [extNorm, fockS_self, eNorm, Complex.ofReal_prod]
  simp only [pairK, pairP, LinearMap.domRestrict₁₂_apply, LinearMap.smul_apply, LinearMap.compl₂_apply,
    Matrix.transpose_one, blockAct_one, hG, hE, AlgHom.toLinearMap_apply, AlgHom.id_apply, fockL_apply,
    fockS_self, smul_eq_mul]
  rw [show (1 : ℂ) / ((∏ τ, eNorm (lam τ) : ℝ) : ℂ) * ((fockNormSq (v : Pol ℂ ι n) : ℝ) : ℂ) =
      ((fockNormSq (v : Pol ℂ ι n) / ∏ τ, eNorm (lam τ) : ℝ) : ℂ) by push_cast; ring, Complex.ofReal_re]

private theorem sum_support_eq_degree_of_isHomogeneous {σ : Type} {P : MvPolynomial σ ℂ} {d : ℕ} (h : P.IsHomogeneous d)
    {α : σ →₀ ℕ} (hα : α ∈ P.support) : ∑ i ∈ α.support, α i = d := by
  have hw := h (mem_support_iff.mp hα)
  simpa [Finsupp.weight_apply, Finsupp.sum] using hw

private theorem multiFactorial_le_factorial_of_isHomogeneous {σ : Type} {P : MvPolynomial σ ℂ} {d : ℕ} (h : P.IsHomogeneous d)
    {α : σ →₀ ℕ} (hα : α ∈ P.support) : (multiFactorial α : ℝ) ≤ d.factorial := by
  have hdiv := Nat.prod_factorial_dvd_factorial_sum α.support α
  rw [sum_support_eq_degree_of_isHomogeneous h hα] at hdiv
  have hle := Nat.le_of_dvd (Nat.factorial_pos _) hdiv
  unfold multiFactorial Finsupp.prod
  exact_mod_cast hle

theorem fockNormSq_le_l1Norm_sq {σ : Type} {P : MvPolynomial σ ℂ} {d : ℕ} (h : P.IsHomogeneous d) :
    fockNormSq P ≤ d.factorial * l1Norm P ^ 2 := by
  unfold fockNormSq l1Norm
  calc ∑ α ∈ P.support, (multiFactorial α : ℝ) * ‖P.coeff α‖ ^ 2
      ≤ ∑ α ∈ P.support, (d.factorial : ℝ) * ‖P.coeff α‖ ^ 2 :=
        Finset.sum_le_sum fun α hα => mul_le_mul_of_nonneg_right (multiFactorial_le_factorial_of_isHomogeneous h hα) (sq_nonneg _)
    _ = (d.factorial : ℝ) * ∑ α ∈ P.support, ‖P.coeff α‖ ^ 2 := by rw [Finset.mul_sum]
    _ ≤ (d.factorial : ℝ) * (∑ α ∈ P.support, ‖P.coeff α‖) ^ 2 :=
        mul_le_mul_of_nonneg_left (Finset.sum_sq_le_sq_sum_of_nonneg fun _ _ => norm_nonneg _) (by positivity)

private theorem card_support_le_of_isHomogeneous {σ : Type} [Fintype σ] {P : MvPolynomial σ ℂ} {d : ℕ}
    (h : P.IsHomogeneous d) : (P.support.card : ℝ) ≤ (1 + d) ^ Fintype.card σ := by
  classical
  have hle : ∀ α ∈ P.support, ∀ i, α i ≤ d := by
    intro α hα i
    have hs : ∑ j ∈ α.support, α j = d := by
      have hw := h (mem_support_iff.mp hα)
      simpa [Finsupp.weight_apply, Finsupp.sum] using hw
    by_cases hi : i ∈ α.support
    · rw [← hs]; exact Finset.single_le_sum (fun j _ => Nat.zero_le _) hi
    · rw [Finsupp.notMem_support_iff.mp hi]; exact Nat.zero_le _
  have hcard : P.support.card ≤ (Fintype.piFinset fun _ : σ => Finset.range (d + 1)).card := by
    refine Finset.card_le_card_of_injOn (fun α : σ →₀ ℕ => (α : σ → ℕ)) ?_ ?_
    · intro α hα
      simp only [Finset.mem_coe, Fintype.mem_piFinset, Finset.mem_range]
      exact fun i => Nat.lt_succ_of_le (hle α (Finset.mem_coe.mp hα) i)
    · intro α _ β _ hαβ
      exact DFunLike.coe_injective hαβ
  rw [Fintype.card_piFinset, Finset.prod_const, Finset.card_range, Finset.card_univ] at hcard
  have : ((P.support.card : ℕ) : ℝ) ≤ ((d + 1) ^ Fintype.card σ : ℕ) := by exact_mod_cast hcard
  push_cast at this
  rw [add_comm (1 : ℝ) (d : ℝ)]
  exact this

private theorem one_le_multiFactorial {σ : Type} (α : σ →₀ ℕ) : (1 : ℝ) ≤ multiFactorial α := by
  unfold multiFactorial Finsupp.prod
  exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Finset.prod_ne_zero_iff.mpr fun i _ => Nat.factorial_ne_zero _)

theorem l1Norm_sq_le_mul_fockNormSq {σ : Type} [Fintype σ] {P : MvPolynomial σ ℂ} {d : ℕ} (h : P.IsHomogeneous d) :
    l1Norm P ^ 2 ≤ (1 + d) ^ Fintype.card σ * fockNormSq P := by
  unfold fockNormSq l1Norm
  calc (∑ α ∈ P.support, ‖P.coeff α‖) ^ 2 ≤ (P.support.card : ℝ) * ∑ α ∈ P.support, ‖P.coeff α‖ ^ 2 :=
        sq_sum_le_card_mul_sum_sq
    _ ≤ (1 + d) ^ Fintype.card σ * ∑ α ∈ P.support, ‖P.coeff α‖ ^ 2 :=
        mul_le_mul_of_nonneg_right (card_support_le_of_isHomogeneous h) (Finset.sum_nonneg fun _ _ => sq_nonneg _)
    _ ≤ (1 + d) ^ Fintype.card σ * ∑ α ∈ P.support, (multiFactorial α : ℝ) * ‖P.coeff α‖ ^ 2 := by
        refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun α _ => ?_) (by positivity)
        exact le_mul_of_one_le_left (sq_nonneg _) (one_le_multiFactorial α)

theorem l1Norm_det_X_matrix_le {σ : Type} {k : ℕ} (g : Fin k → Fin k → σ) :
    l1Norm (Matrix.of fun p q => (X (g p q) : MvPolynomial σ ℂ)).det ≤ (k : ℝ) ^ k := by
  rw [Matrix.det_apply]
  calc l1Norm (∑ e : Equiv.Perm (Fin k), Equiv.Perm.sign e •
        ∏ i, (Matrix.of fun p q => (X (g p q) : MvPolynomial σ ℂ)) (e i) i)
      ≤ ∑ e : Equiv.Perm (Fin k), l1Norm (Equiv.Perm.sign e •
        ∏ i, (Matrix.of fun p q => (X (g p q) : MvPolynomial σ ℂ)) (e i) i) := l1Norm_sum_le _ _
    _ ≤ ∑ _e : Equiv.Perm (Fin k), (1 : ℝ) := by
        refine Finset.sum_le_sum fun e _ => ?_
        have hp : l1Norm (∏ i, (Matrix.of fun p q => (X (g p q) : MvPolynomial σ ℂ)) (e i) i) ≤ 1 := by
          calc _ ≤ ∏ i, l1Norm ((Matrix.of fun p q => (X (g p q) : MvPolynomial σ ℂ)) (e i) i) :=
                l1Norm_prod_le _ _
            _ = 1 := by simp [l1Norm_X]
        rcases Int.units_eq_one_or (Equiv.Perm.sign e) with h | h
        · rw [h, one_smul]; exact hp
        · rw [h, Units.neg_smul, one_smul, l1Norm_neg]; exact hp
    _ = (Nat.factorial k : ℝ) := by simp [Fintype.card_perm]
    _ ≤ (k : ℝ) ^ k := by exact_mod_cast Nat.factorial_le_pow k

private theorem isHomogeneous_det_X_matrix {σ : Type} {k : ℕ} (g : Fin k → Fin k → σ) :
    (Matrix.of fun p q => (X (g p q) : MvPolynomial σ ℂ)).det.IsHomogeneous k := by
  rw [Matrix.det_apply]
  refine MvPolynomial.IsHomogeneous.sum _ _ _ fun e _ => ?_
  have hp : (∏ i, (Matrix.of fun p q => (X (g p q) : MvPolynomial σ ℂ)) (e i) i).IsHomogeneous k := by
    have := MvPolynomial.IsHomogeneous.prod (Finset.univ : Finset (Fin k))
      (fun i => (Matrix.of fun p q => (X (g p q) : MvPolynomial σ ℂ)) (e i) i) (fun _ => 1)
      (fun i _ => by simpa only [Matrix.of_apply] using isHomogeneous_X ℂ (g (e i) i))
    simpa using this
  rcases Int.units_eq_one_or (Equiv.Perm.sign e) with h | h
  · rw [h, one_smul]; exact hp
  · rw [h, Units.neg_smul, one_smul]; exact hp.neg

private theorem sum_succ_mul_sub_nuNext_eq_sum_of_antitone {n : ℕ} (ν : Fin n → ℕ) (hν : Antitone ν) :
    ∑ s : Fin n, (s.val + 1) * (ν s - Formalism.GradedWeylDivisibility.nuNext ν s) = ∑ s, ν s := by
  have h := Formalism.GradedWeylDivisibility.hw_weight_eq ν hν
  have h2 : ∀ t, ∑ s : Fin n, (ν s - Formalism.GradedWeylDivisibility.nuNext ν s) * Formalism.GradedWeylDivisibility.initW n (s.val + 1) t = ν t := by
    intro t
    have := congrFun h t
    simpa [Finset.sum_apply, smul_eq_mul] using this
  have h3 : ∀ s : Fin n, ∑ t : Fin n, Formalism.GradedWeylDivisibility.initW n (s.val + 1) t = s.val + 1 := by
    intro s
    rw [← Formalism.GradedWeylDivisibility.sum_single_castLE (show s.val + 1 ≤ n by omega)]
    simp only [Finset.sum_apply]
    rw [Finset.sum_comm]
    simp [Pi.single_apply]
  calc ∑ s : Fin n, (s.val + 1) * (ν s - Formalism.GradedWeylDivisibility.nuNext ν s)
      = ∑ s : Fin n, ∑ t : Fin n, (ν s - Formalism.GradedWeylDivisibility.nuNext ν s) * Formalism.GradedWeylDivisibility.initW n (s.val + 1) t := by
        refine Finset.sum_congr rfl fun s _ => ?_
        rw [← Finset.mul_sum, h3 s, mul_comm]
    _ = ∑ t, ν t := by
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun t _ => h2 t

theorem eNorm_le {n : ℕ} (l : DomWeight n) :
    eNorm l ≤ (∑ i, l.natW i).factorial * ((n : ℝ) ^ (∑ i, l.natW i)) ^ 2 := by
  have hanti : Antitone l.natW := fun i j hij => by
    have := l.anti hij
    simp only [DomWeight.natW]
    exact Int.toNat_le_toNat (by omega)
  have hsum := sum_succ_mul_sub_nuNext_eq_sum_of_antitone l.natW hanti
  have hE : extremal ℂ n l = ∏ s : Fin n, (Formalism.GradedWeylDivisibility.lpMinor ℂ (s.val + 1) (by omega) (by omega) :
      MvPolynomial (Fin n × Fin n) ℂ) ^ (l.natW s - Formalism.GradedWeylDivisibility.nuNext l.natW s) := rfl
  have hhom : (extremal ℂ n l).IsHomogeneous (∑ i, l.natW i) := by
    rw [hE, ← hsum]
    exact MvPolynomial.IsHomogeneous.prod _ _ _ fun s _ => (isHomogeneous_det_X_matrix _).pow _
  have hl1 : l1Norm (extremal ℂ n l) ≤ (n : ℝ) ^ (∑ i, l.natW i) := by
    rw [hE]
    calc _ ≤ ∏ s : Fin n, ((n : ℝ) ^ (s.val + 1)) ^ (l.natW s - Formalism.GradedWeylDivisibility.nuNext l.natW s) := by
          refine l1Norm_prod_pow_le _ _ _ _ fun s _ => ?_
          calc _ ≤ ((s.val + 1 : ℕ) : ℝ) ^ (s.val + 1) := l1Norm_det_X_matrix_le _
            _ ≤ (n : ℝ) ^ (s.val + 1) := by
                gcongr
                exact_mod_cast s.isLt
      _ = (n : ℝ) ^ (∑ i, l.natW i) := by
          simp only [← pow_mul]
          rw [Finset.prod_pow_eq_pow_sum, hsum]
  unfold eNorm
  calc fockNormSq (extremal ℂ n l) ≤ (∑ i, l.natW i).factorial * l1Norm (extremal ℂ n l) ^ 2 := fockNormSq_le_l1Norm_sq hhom
    _ ≤ _ := by
        gcongr
        exact l1Norm_nonneg _

variable {ι : Type} [Fintype ι] {a b : ℕ}

theorem hom_of_posW [DecidableEq ι] {P : Pol ℂ ι a} {e : ι → ℕ}
    (h : ∀ τ, IsWeightedHomogeneous (GlobalTheory.JetDeg.posW a τ) P (e τ)) : P.IsHomogeneous (∑ τ, e τ) := by
  intro m hm
  have key : ∀ τ, Finsupp.weight (GlobalTheory.JetDeg.posW a τ) m = e τ := fun τ => h τ hm
  simp_rw [← key]
  simp only [Finsupp.weight_apply, Finsupp.sum, Pi.one_apply, smul_eq_mul, mul_one]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun v _ => ?_
  simp [GlobalTheory.JetDeg.posW]

omit [Fintype ι] in
theorem subD_hom (w : (ι × Fin b × Fin b) ⊕ DVar ι a b → ℕ) (hw : ∀ x y, w (Sum.inl x) + w (Sum.inr y) = 1)
    {P : Pol ℂ ι a} {d : ℕ} (hP : P.IsHomogeneous d) : IsWeightedHomogeneous w (subD ℂ ι a b P) d := by
  have hX : ∀ v : ι × Fin a × Fin a, IsWeightedHomogeneous w (subD ℂ ι a b (X v))
      ((AddMonoidHom.id ℕ) ((1 : ι × Fin a × Fin a → ℕ) v)) := by
    intro v
    simp only [subD, aeval_X, AddMonoidHom.id_apply, Pi.one_apply]
    split_ifs with hv
    · refine IsWeightedHomogeneous.sum _ _ _ fun β _ => ?_
      rw [← hw (v.1, β, ⟨v.2.2.1, hv⟩) (v.1, β, v.2.1)]
      exact (isWeightedHomogeneous_X ℂ w _).mul (isWeightedHomogeneous_X ℂ w _)
    · exact isWeightedHomogeneous_zero ℂ w 1
  exact GlobalTheory.JetDeg.algHom_hom (1 : ι × Fin a × Fin a → ℕ) w (AddMonoidHom.id ℕ) (subD ℂ ι a b) hX hP

theorem degree_exp {P : Pol ℂ ι a} {d : ℕ} (hP : P.IsHomogeneous d) {μ} (hμ : μ ∈ (subD ℂ ι a b P).support) :
    (expL μ).degree = d ∧ (expR μ).degree = d := by
  have hc : (subD ℂ ι a b P).coeff μ ≠ 0 := MvPolynomial.mem_support_iff.mp hμ
  have h1 := subD_hom (b := b) (Sum.elim 1 0) (fun _ _ => rfl) hP hc
  have h2 := subD_hom (b := b) (Sum.elim 0 1) (fun _ _ => rfl) hP hc
  rw [Finsupp.weight_apply, Finsupp.sum_fintype _ _ (fun _ => by simp), Fintype.sum_sum_type] at h1 h2
  simp only [Sum.elim_inl, Sum.elim_inr, Pi.one_apply, Pi.zero_apply, smul_eq_mul, mul_one, mul_zero,
    Finset.sum_const_zero, add_zero, zero_add] at h1 h2
  refine ⟨?_, ?_⟩
  · simpa [Finsupp.degree_eq_sum, expL, Finsupp.comapDomain_apply] using h1
  · simpa [Finsupp.degree_eq_sum, expR, Finsupp.comapDomain_apply] using h2

omit [Fintype ι] in
theorem l1Norm_subD_le_mul_pow {P : Pol ℂ ι a} {d : ℕ} (hP : P.IsHomogeneous d) :
    l1Norm (subD ℂ ι a b P) ≤ l1Norm P * (b : ℝ) ^ d := by
  refine l1Norm_bind_le_mul_pow_of_isHomogeneous _ hP fun v => ?_
  split_ifs with h
  · refine (l1Norm_sum_le _ _).trans ?_
    refine (Finset.sum_le_sum (g := fun _ => (1 : ℝ)) fun β _ => (l1Norm_mul_le _ _).trans
      (le_of_eq (by rw [l1Norm_X, l1Norm_X, one_mul]))).trans (le_of_eq ?_)
    simp
  · simp

theorem l1Norm_sharp_le_mul_pow (n : ι → ℕ) (P : Pol ℂ ι a) : l1Norm (sharp n P) ≤ l1Norm P * (a : ℝ) ^ (∑ τ, n τ * a) := by
  show l1Norm (P * ∏ τ, frDet ℂ a τ ^ n τ) ≤ _
  refine (l1Norm_mul_le _ _).trans (mul_le_mul_of_nonneg_left ?_ (l1Norm_nonneg _))
  refine (l1Norm_prod_pow_le Finset.univ (fun τ => frDet ℂ a τ) n (fun _ => (a : ℝ) ^ a)
    (fun τ _ => ?_)).trans (le_of_eq ?_)
  · exact l1Norm_det_X_matrix_le (fun p q => (τ, p, q))
  · rw [← Finset.prod_pow_eq_pow_sum]
    exact Finset.prod_congr rfl fun τ _ => by ring

theorem jet_hom (J : (DVar ι a b →₀ ℕ) → ℂ) (n : ι → ℕ) {P : Pol ℂ ι a} {d : ℕ} (hP : (sharp n P).IsHomogeneous d) :
    (jetMap J n P).IsHomogeneous d := by
  rw [GlobalTheory.JetPoint.jetMap_eq_sum]
  refine IsHomogeneous.sum _ _ _ fun μ hμ => ?_
  rw [smul_monomial]
  exact isHomogeneous_monomial _ (degree_exp hP hμ).1

theorem l1Norm_jetMap_le_of_isHomogeneous (J : (DVar ι a b →₀ ℕ) → ℂ) (n : ι → ℕ) {P : Pol ℂ ι a} {d : ℕ} (hP : (sharp n P).IsHomogeneous d)
    {M : ℝ} (hM0 : 0 ≤ M) (hM : ∀ m, m.degree = d → ‖J m‖ ≤ M) :
    l1Norm (jetMap J n P) ≤ M * (l1Norm P * (a : ℝ) ^ (∑ τ, n τ * a) * (b : ℝ) ^ d) := by
  have hsum : l1Norm (jetMap J n P) ≤ M * l1Norm (subD ℂ ι a b (sharp n P)) := by
    rw [GlobalTheory.JetPoint.jetMap_eq_sum]
    refine (l1Norm_sum_le _ _).trans ?_
    rw [l1Norm, Finset.mul_sum]
    refine Finset.sum_le_sum fun μ hμ => ?_
    refine (l1Norm_smul_le _ _).trans ?_
    rw [l1Norm_monomial]
    exact mul_le_mul_of_nonneg_right (hM _ (degree_exp hP hμ).2) (norm_nonneg _)
  refine hsum.trans (mul_le_mul_of_nonneg_left ?_ hM0)
  refine (l1Norm_subD_le_mul_pow hP).trans ?_
  exact mul_le_mul_of_nonneg_right (l1Norm_sharp_le_mul_pow n P) (pow_nonneg (Nat.cast_nonneg _) _)

theorem fact_le {d : ℕ} {T : ℝ} (h : (d : ℝ) ≤ T) : (d.factorial : ℝ) ≤ T ^ d := by
  calc (d.factorial : ℝ) ≤ ((d ^ d : ℕ) : ℝ) := by exact_mod_cast Nat.factorial_le_pow d
    _ = (d : ℝ) ^ d := by push_cast; ring
    _ ≤ T ^ d := pow_le_pow_left₀ (Nat.cast_nonneg d) h d

theorem prod_eNorm_le (lam : ι → DomWeight a) {T : ℝ} (ha : (a : ℝ) ≤ T)
    (hd : ((∑ τ, ∑ i, (lam τ).natW i : ℕ) : ℝ) ≤ T) :
    ∏ τ, eNorm (lam τ) ≤ T ^ (3 * ∑ τ, ∑ i, (lam τ).natW i) := by
  have hT : (0 : ℝ) ≤ T := le_trans (Nat.cast_nonneg _) ha
  rw [Finset.mul_sum, ← Finset.prod_pow_eq_pow_sum]
  apply Finset.prod_le_prod
  · intro τ _
    exact le_trans zero_le_one (one_le_eNorm _)
  · intro τ _
    have hdτ : ((∑ i, (lam τ).natW i : ℕ) : ℝ) ≤ T := by
      refine le_trans (Nat.cast_le.mpr ?_) hd
      exact Finset.single_le_sum (f := fun τ => ∑ i, (lam τ).natW i) (fun _ _ => Nat.zero_le _)
        (Finset.mem_univ τ)
    have h2 : ((∑ i, (lam τ).natW i).factorial : ℝ) ≤ T ^ (∑ i, (lam τ).natW i) := fact_le hdτ
    have h3 : ((a : ℝ) ^ (∑ i, (lam τ).natW i)) ^ 2 ≤ (T ^ (∑ i, (lam τ).natW i)) ^ 2 :=
      pow_le_pow_left₀ (by positivity) (pow_le_pow_left₀ (Nat.cast_nonneg _) ha _) 2
    calc eNorm (lam τ)
        ≤ ((∑ i, (lam τ).natW i).factorial : ℝ) * ((a : ℝ) ^ (∑ i, (lam τ).natW i)) ^ 2 := eNorm_le (lam τ)
      _ ≤ T ^ (∑ i, (lam τ).natW i) * (T ^ (∑ i, (lam τ).natW i)) ^ 2 :=
          mul_le_mul h2 h3 (by positivity) (pow_nonneg hT _)
      _ = T ^ (3 * ∑ i, (lam τ).natW i) := by ring

private theorem fQ_div_le_of_bounds {M T F E E' fQ lQ lP A B fac c1 : ℝ} {D D' c : ℕ}
    (hM0 : 0 ≤ M) (h1 : 1 ≤ T) (hF0 : 0 ≤ F) (hfQ0 : 0 ≤ fQ) (hE : 0 < E) (hE1' : 1 ≤ E')
    (hET : E ≤ T ^ (3 * D)) (hf1 : fQ ≤ fac * lQ ^ 2) (hfac0 : 0 ≤ fac) (hfac : fac ≤ T ^ D')
    (hlQ0 : 0 ≤ lQ) (hl1 : lQ ≤ Real.sqrt M * (lP * A * B)) (hf2 : lP ^ 2 ≤ c1 * F)
    (hc10 : 0 ≤ c1) (hc1 : c1 ≤ T ^ c) (hA0 : 0 ≤ A) (hA : A ≤ T ^ D') (hB0 : 0 ≤ B)
    (hB : B ≤ T ^ D') :
    fQ / E' ≤ M * T ^ (5 * D' + c + 3 * D) * (F / E) := by
  have hT0 : (0 : ℝ) ≤ T := le_trans zero_le_one h1
  have hlQ2 : lQ ^ 2 ≤ M * (lP ^ 2 * A ^ 2 * B ^ 2) := by
    have h := pow_le_pow_left₀ hlQ0 hl1 2
    rw [mul_pow, Real.sq_sqrt hM0, mul_pow, mul_pow] at h
    exact h
  have hin : lP ^ 2 * A ^ 2 * B ^ 2 ≤ c1 * F * A ^ 2 * B ^ 2 := by
    have := mul_le_mul_of_nonneg_right hf2 (sq_nonneg A)
    exact mul_le_mul_of_nonneg_right this (sq_nonneg B)
  have step1 : fQ ≤ fac * (M * (c1 * F * A ^ 2 * B ^ 2)) :=
    le_trans hf1 (mul_le_mul_of_nonneg_left (le_trans hlQ2 (mul_le_mul_of_nonneg_left hin hM0)) hfac0)
  have step2 : fac * (M * (c1 * F * A ^ 2 * B ^ 2)) = M * F * (fac * c1 * (A ^ 2 * B ^ 2)) := by ring
  have hAB : A ^ 2 * B ^ 2 ≤ (T ^ D') ^ 2 * (T ^ D') ^ 2 :=
    mul_le_mul (pow_le_pow_left₀ hA0 hA 2) (pow_le_pow_left₀ hB0 hB 2) (by positivity) (by positivity)
  have h4 : fac * c1 ≤ T ^ D' * T ^ c := mul_le_mul hfac hc1 hc10 (pow_nonneg hT0 _)
  have h5 : fac * c1 * (A ^ 2 * B ^ 2) ≤ T ^ D' * T ^ c * ((T ^ D') ^ 2 * (T ^ D') ^ 2) :=
    mul_le_mul h4 hAB (by positivity) (mul_nonneg (pow_nonneg hT0 _) (pow_nonneg hT0 _))
  have h6 := mul_le_mul h5 hET hE.le
    (mul_nonneg (mul_nonneg (pow_nonneg hT0 _) (pow_nonneg hT0 _)) (by positivity))
  have hX : fac * c1 * (A ^ 2 * B ^ 2) * E ≤ T ^ (5 * D' + c + 3 * D) :=
    h6.trans (le_of_eq (by ring))
  calc fQ / E' ≤ fQ := div_le_self hfQ0 hE1'
    _ ≤ M * F * (fac * c1 * (A ^ 2 * B ^ 2)) := step2 ▸ step1
    _ ≤ M * F * (T ^ (5 * D' + c + 3 * D) / E) :=
        mul_le_mul_of_nonneg_left ((le_div_iff₀ hE).mpr hX) (mul_nonneg hM0 hF0)
    _ = M * T ^ (5 * D' + c + 3 * D) * (F / E) := by ring

theorem jetOp_le (lam : ι → DomWeight a) (lam' : ι → DomWeight b) (n : ι → ℕ) (hV : JetInVV ℂ lam lam' n)
    (J : (DVar ι a b →₀ ℕ) → ℂ) {M T : ℝ} (hM0 : 0 ≤ M)
    (hM : ∀ m, m.degree = ∑ τ, ∑ i, (lam' τ).natW i → ‖J m‖ ^ 2 ≤ M) (h1 : 1 ≤ T) (ha : (a : ℝ) ≤ T) (hb : (b : ℝ) ≤ T)
    (hd : 1 + ((∑ τ, ∑ i, (lam τ).natW i : ℕ) : ℝ) ≤ T) (hd' : ((∑ τ, ∑ i, (lam' τ).natW i : ℕ) : ℝ) ≤ T)
    (v : VV ℂ lam) :
    fockNormSq ((jetOp lam lam' J n v : VV ℂ lam') : Pol ℂ ι b) / ∏ τ, eNorm (lam' τ) ≤
      M * T ^ (5 * (∑ τ, ∑ i, (lam' τ).natW i) + Fintype.card ι * (a * a) + 3 * ∑ τ, ∑ i, (lam τ).natW i) *
        (fockNormSq (v : Pol ℂ ι a) / ∏ τ, eNorm (lam τ)) := by
  classical
  have hT0 : (0 : ℝ) ≤ T := le_trans zero_le_one h1
  have hPV : (v : Pol ℂ ι a) ∈ Formalism.L2.DIV.VV ℂ lam := v.2
  have hQV : jetMap J n (v : Pol ℂ ι a) ∈ Formalism.L2.DIV.VV ℂ lam' := hV J _ hPV
  rw [GlobalTheory.JetPoint.coe_jetOp lam lam' J n v hQV]
  have hone : ∀ lm : ι → DomWeight a, (1 : ℝ) ≤ ∏ τ, eNorm (lm τ) := fun lm => by
    simpa using Finset.prod_le_prod (s := Finset.univ) (f := fun _ => (1 : ℝ))
      (g := fun τ => eNorm (lm τ)) (fun _ _ => zero_le_one) (fun τ _ => one_le_eNorm _)
  have hone' : (1 : ℝ) ≤ ∏ τ, eNorm (lam' τ) := by
    simpa using Finset.prod_le_prod (s := Finset.univ) (f := fun _ => (1 : ℝ))
      (g := fun τ => eNorm (lam' τ)) (fun _ _ => zero_le_one) (fun τ _ => one_le_eNorm _)
  have hEpos : (0 : ℝ) < ∏ τ, eNorm (lam τ) := lt_of_lt_of_le zero_lt_one (hone lam)
  have hPh : (v : Pol ℂ ι a).IsHomogeneous (∑ τ, ∑ i, (lam τ).natW i) :=
    hom_of_posW fun τ => GlobalTheory.JetDeg.VV_hom lam τ hPV
  have hSh : (sharp n (v : Pol ℂ ι a)).IsHomogeneous (∑ τ, (∑ i, (lam τ).natW i + n τ * a)) :=
    hom_of_posW fun τ => GlobalTheory.JetDeg.sharp_hom n τ (GlobalTheory.JetDeg.VV_hom lam τ hPV)
  have hQh := jet_hom J n hSh
  have hQh' : (jetMap J n (v : Pol ℂ ι a)).IsHomogeneous (∑ τ, ∑ i, (lam' τ).natW i) :=
    hom_of_posW fun τ => GlobalTheory.JetDeg.VV_hom lam' τ hQV
  by_cases hQ0 : jetMap J n (v : Pol ℂ ι a) = 0
  · rw [hQ0, GlobalTheory.MvPoly.fockNormSq_zero, zero_div]
    exact mul_nonneg (mul_nonneg hM0 (pow_nonneg hT0 _))
      (div_nonneg (GlobalTheory.MvPoly.fockNormSq_nonneg _) hEpos.le)
  have hdeq := hQh.inj_right hQh' hQ0
  have hsq : ∀ m : DVar ι a b →₀ ℕ, m.degree = ∑ τ, (∑ i, (lam τ).natW i + n τ * a) →
      ‖J m‖ ≤ Real.sqrt M := fun m hm => by
    have h := Real.abs_le_sqrt (hM m (hm.trans hdeq))
    rwa [abs_norm] at h
  have hl1 := l1Norm_jetMap_le_of_isHomogeneous J n hSh (Real.sqrt_nonneg M) hsq
  rw [hdeq] at hl1
  have hsum : ∑ τ, n τ * a ≤ ∑ τ, ∑ i, (lam' τ).natW i := by
    rw [← hdeq, Finset.sum_add_distrib]
    exact Nat.le_add_left _ _
  have hf2 := l1Norm_sq_le_mul_fockNormSq hPh
  simp only [Fintype.card_prod, Fintype.card_fin] at hf2
  exact fQ_div_le_of_bounds hM0 h1 (GlobalTheory.MvPoly.fockNormSq_nonneg _) (GlobalTheory.MvPoly.fockNormSq_nonneg _) hEpos
    hone' (prod_eNorm_le lam ha (by linarith)) (fockNormSq_le_l1Norm_sq hQh') (Nat.cast_nonneg _) (fact_le hd')
    (GlobalTheory.MvPoly.l1Norm_nonneg _) hl1 hf2 (by positivity)
    (pow_le_pow_left₀ (by positivity) (by push_cast at hd ⊢; linarith) _)
    (by positivity) ((pow_le_pow_left₀ (Nat.cast_nonneg _) ha _).trans (pow_le_pow_right₀ h1 hsum))
    (by positivity) (pow_le_pow_left₀ (Nat.cast_nonneg _) hb _)

end GlobalTheory.FockJetBound

end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim GlobalTheory.TestLat
open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.SumSize GlobalTheory.KerConjMean

theorem GlobalTheory.FockJetBound.jetOp_norm_le : ∃ K : ℝ, 0 ≤ K ∧ ∀ (D : D7) (a b : ℕ) (lam : D.what₂.Tau → DomWeight a) (lam' : D.what₂.Tau → DomWeight b)
  (n : D.what₂.Tau → ℕ), Formalism.L2.Ker.JetInVV ℂ lam lam' n → (∀ v, 0 ≤ nrm lam (fun _ => 1) v) ∧
  ∃ Kx : ℝ, 0 < Kx ∧ Real.log Kx ≤ K * ((∑ τ, ∑ i, ((lam τ).natW i : ℝ)) + (∑ τ, ∑ i, ((lam' τ).natW i : ℝ)) +
      (Fintype.card D.what₂.Tau : ℝ) * ((a : ℝ) + b) ^ 2 + 1) *
      Real.log (2 + (∑ τ, ∑ i, ((lam τ).natW i : ℝ)) + (∑ τ, ∑ i, ((lam' τ).natW i : ℝ)) + a + b + Fintype.card D.what₂.Tau) ∧
    ∀ (H : VC D a b → ℂ) (S A : ℝ), 0 < A → 0 ≤ S → Differentiable ℂ H →
      (∀ z, ‖H z‖ ^ 2 ≤ S * Real.exp (Real.pi * (∑ τ, ∑ i, ∑ j, ‖z τ i j‖ ^ 2) / A)) → ∀ v,
      nrm lam' (fun _ => 1) (Formalism.L2.Ker.jetOp lam lam' (fun m => GL3Theta.applyAt0 D (MvPolynomial.monomial m 1) H) n v) ≤
        S * Kx * max 1 A⁻¹ ^ (∑ τ, ∑ i, (lam' τ).natW i) * nrm lam (fun _ => 1) v := by
  classical
  refine ⟨11, by norm_num, ?_⟩
  intro D a b lam lam' n hV
  have hE : ∀ {N : ℕ} (l : D.what₂.Tau → DomWeight N), 0 < ∏ τ, GlobalTheory.FockJetBound.eNorm (l τ) :=
    fun l => Finset.prod_pos fun τ _ => lt_of_lt_of_le one_pos (GlobalTheory.FockJetBound.one_le_eNorm (l τ))
  unfold GlobalTheory.SumSize.nrm
  refine ⟨fun v => ?_, ?_⟩
  · rw [GlobalTheory.FockJetBound.pairK_re]
    exact div_nonneg (GlobalTheory.MvPoly.fockNormSq_nonneg _) (hE lam).le
  set dn : ℕ := ∑ τ, ∑ i, (lam τ).natW i with hdn
  set dn' : ℕ := ∑ τ, ∑ i, (lam' τ).natW i with hdn'
  have cd : (∑ τ, ∑ i, ((lam τ).natW i : ℝ)) = (dn : ℝ) := by simp only [hdn, Nat.cast_sum]
  have cd' : (∑ τ, ∑ i, ((lam' τ).natW i : ℝ)) = (dn' : ℝ) := by simp only [hdn', Nat.cast_sum]
  rw [cd, cd']
  have h0 : (0 : ℝ) ≤ dn := Nat.cast_nonneg _
  have h0' : (0 : ℝ) ≤ dn' := Nat.cast_nonneg _
  have ha0 : (0 : ℝ) ≤ a := Nat.cast_nonneg _
  have hb0 : (0 : ℝ) ≤ b := Nat.cast_nonneg _
  have hc0 : (0 : ℝ) ≤ Fintype.card D.what₂.Tau := Nat.cast_nonneg _
  obtain ⟨Y, hY⟩ : ∃ Y : ℝ, Y = 2 + (dn : ℝ) + dn' + a + b + Fintype.card D.what₂.Tau := ⟨_, rfl⟩
  rw [← hY]
  have hY2 : 2 ≤ Y := by rw [hY]; linarith
  refine ⟨Y ^ (6 * dn' + (5 * dn' + Fintype.card D.what₂.Tau * (a * a) + 3 * dn)), pow_pos (by linarith) _, ?_, ?_⟩
  · rw [Real.log_pow]
    have hlog : 0 ≤ Real.log Y := Real.log_nonneg (by linarith)
    apply mul_le_mul_of_nonneg_right _ hlog
    have hsq : (Fintype.card D.what₂.Tau : ℝ) * ((a : ℝ) * a) ≤ Fintype.card D.what₂.Tau * ((a : ℝ) + b) ^ 2 :=
      mul_le_mul_of_nonneg_left (by nlinarith) hc0
    push_cast
    nlinarith
  · intro H S A hA hS hH hgr v
    rw [GlobalTheory.FockJetBound.pairK_re, GlobalTheory.FockJetBound.pairK_re]
    obtain ⟨B, hB⟩ : ∃ B : ℝ, B = (dn' : ℝ) + 1 := ⟨_, rfl⟩
    have hB1 : 1 ≤ B := by rw [hB]; linarith
    have hBY : B ≤ Y := by rw [hB, hY]; linarith
    have hX0 : 0 ≤ 2 * Real.exp 1 * Real.pi * B / A :=
      div_nonneg (mul_nonneg (by positivity) (by linarith)) hA.le
    have hM0 : 0 ≤ S * (2 * Real.exp 1 * Real.pi * B / A) ^ dn' := mul_nonneg hS (pow_nonneg hX0 _)
    have hJ : ∀ m : Formalism.L2.Ker.DVar D.what₂.Tau a b →₀ ℕ, m.degree = dn' →
        ‖GL3Theta.applyAt0 D (MvPolynomial.monomial m 1) H‖ ^ 2 ≤ S * (2 * Real.exp 1 * Real.pi * B / A) ^ dn' := by
      intro m hm
      have hk : ∀ k, (m k : ℝ) ≤ 2 * B := by
        intro k
        have h1 := Finsupp.le_degree k m
        rw [hm] at h1
        have h2 : (m k : ℝ) ≤ dn' := by exact_mod_cast h1
        rw [hB]; linarith
      have key := GlobalTheory.GaussCauchy.monomial_deriv_bound D a b H S A B hA hB1 hS hH hgr m hk
      have hs : (m.sum fun _ n => n) = dn' := by rw [← hm]; rfl
      rw [hs] at key
      have happ : GL3Theta.applyAt0 D (MvPolynomial.monomial m 1) H =
          (m.prod fun _ n => (n.factorial : ℂ)) * taylor D H m := by
        rw [Formalism.MainNotions.GL3Theta.applyAt0, MvPolynomial.support_monomial, if_neg one_ne_zero, Finset.sum_singleton,
          MvPolynomial.coeff_monomial, if_pos rfl, one_mul]
      rw [happ]; exact key
    have hT1 : (1 : ℝ) ≤ 1 + (dn : ℝ) + dn' + a + b := by linarith
    have hTY : (1 : ℝ) + (dn : ℝ) + dn' + a + b ≤ Y := by rw [hY]; linarith
    have main := GlobalTheory.FockJetBound.jetOp_le lam lam' n hV (fun m => GL3Theta.applyAt0 D (MvPolynomial.monomial m 1) H)
      hM0 hJ hT1 (by linarith) (by linarith) (by linarith) (by linarith) v
    refine main.trans ?_
    apply mul_le_mul_of_nonneg_right _ (div_nonneg (GlobalTheory.MvPoly.fockNormSq_nonneg _) (hE lam).le)
    have he : Real.exp 1 < 2.7182818286 := Real.exp_one_lt_d9
    have hpi := Real.pi_le_four
    have h32 : (2 : ℝ) ^ 5 ≤ Y ^ 5 := pow_le_pow_left₀ (by norm_num) hY2 5
    have hc : 2 * Real.exp 1 * Real.pi ≤ 32 := by nlinarith [Real.exp_pos 1, Real.pi_pos]
    have hnum : 2 * Real.exp 1 * Real.pi * B ≤ Y ^ 6 :=
      calc 2 * Real.exp 1 * Real.pi * B ≤ 32 * Y := mul_le_mul hc hBY (by linarith) (by norm_num)
        _ = 2 ^ 5 * Y := by norm_num
        _ ≤ Y ^ 5 * Y := mul_le_mul_of_nonneg_right h32 (by linarith)
        _ = Y ^ 6 := by ring
    have hbase : 2 * Real.exp 1 * Real.pi * B / A ≤ Y ^ 6 * max 1 A⁻¹ := by
      rw [div_eq_mul_inv]
      exact mul_le_mul hnum (le_max_right _ _) (inv_nonneg.mpr hA.le) (pow_nonneg (by linarith) _)
    calc S * (2 * Real.exp 1 * Real.pi * B / A) ^ dn' *
          (1 + (dn : ℝ) + dn' + a + b) ^ (5 * dn' + Fintype.card D.what₂.Tau * (a * a) + 3 * dn)
        ≤ S * (Y ^ 6 * max 1 A⁻¹) ^ dn' * Y ^ (5 * dn' + Fintype.card D.what₂.Tau * (a * a) + 3 * dn) :=
          mul_le_mul (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hX0 hbase dn') hS)
            (pow_le_pow_left₀ (by linarith) hTY _) (pow_nonneg (by linarith) _)
            (mul_nonneg hS (pow_nonneg (mul_nonneg (pow_nonneg (by linarith) _) (le_trans zero_le_one (le_max_left _ _))) _))
      _ = S * Y ^ (6 * dn' + (5 * dn' + Fintype.card D.what₂.Tau * (a * a) + 3 * dn)) * max 1 A⁻¹ ^ dn' := by
          rw [mul_pow, ← pow_mul, pow_add]; ring
