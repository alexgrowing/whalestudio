import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Formalism.PairingDivisors.StatementH
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.MulVSubRight
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RationalPointsIntegralPointsMembership
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsLatticeOfAdelicPoint
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsDvdMulInvolutionAddOne
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DetRationalMatrixTwoSidedMulEqProdEmbeddingsStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RationalMatrixMulThetaLatticesStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.UnitaryThetaConstantEqInverseDeterminantPhaseStatement
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.RatEqui
open scoped BigOperators

noncomputable section

namespace GlobalTheory.RatRow

variable {D : D7} {N N' : ℕ}

theorem conj_conj (x : D.host.E) : D.host.conj (D.host.conj x) = x := by
  apply D.host.φ₀.injective
  have h : ∀ y, D.host.φ₀ (D.host.conj y) = (starRingEnd ℂ) (D.host.φ₀ y) := fun y =>
    D.host.conjE_apply _ y
  rw [h, h, Complex.conj_conj]

theorem adj_adj {n : ℕ} (M : Matrix (Fin n) (Fin n) D.host.E) : adj D (adj D M) = M := by
  refine Matrix.ext fun i j => ?_
  simp [adj, conj_conj]

theorem moves_one (D : D7) (N : ℕ) : Moves D ((1 : GA D N) : GL (Fin N) (AE D)) (stdL D N) := by
  obtain ⟨Lt, h1, h2, -⟩ := exists_lattice_of_adelic_point D N
  rw [← h2]; exact (h1 _).1

theorem sd_of_moves {g : GA D N} {L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)}
    (h : Moves D (g : GL (Fin N) (AE D)) L) : SD D L := by
  obtain ⟨Lt, h1, -⟩ := exists_lattice_of_adelic_point D N
  have : L = Lt g := by
    ext x; rw [h x, (h1 g).1 x]
  rw [this]; exact (h1 g).2

theorem klat (T : Tor D) {g : GA D N} {g' : GA D N'} {L₁ L₁'}
    (h : Moves D (g : GL (Fin N) (AE D)) L₁) (h' : Moves D (g' : GL (Fin N') (AE D)) L₁') :
    KLat D T (La D T L₁ L₁') := Or.inr ⟨_, _, sd_of_moves h, sd_of_moves h', rfl⟩

theorem isRat_one (D : D7) (N : ℕ) : IsRat D ((1 : GA D N) : GL (Fin N) (AE D)) 1 := by
  unfold IsRat
  rw [Matrix.map_one _ (map_zero _) (map_one _)]
  rfl

theorem hf_unitary (T : Tor D) {M' : Matrix (Fin N') (Fin N') D.host.E} {M : Matrix (Fin N) (Fin N) D.host.E}
    (h' : adj D M' * M' = 1) (h : M * adj D M = 1) (z w : VC D N N') :
    Hf D T (mulV D M' M z) (mulV D M' M w) = Hf D T z w := by
  rw [Hf_mulV, mulV_mulV, h', h, mulV_one]

theorem mulV_comm (M' : Matrix (Fin N') (Fin N') D.host.E) (M : Matrix (Fin N) (Fin N) D.host.E) (z : VC D N N') :
    mulV D M' 1 (mulV D 1 M z) = mulV D 1 M (mulV D M' 1 z) := by
  simp only [mulV_mulV, Matrix.mul_one, Matrix.one_mul]

theorem mulV_scalar (a : D.host.E) (z : VC D N N') (τ : D.what₂.Tau) (i : Fin N') (j : Fin N) :
    mulV D (Matrix.diagonal fun _ => a) 1 z τ i j = embT D τ a * z τ i j := by
  rw [mulV_apply, Matrix.map_one _ (map_zero _) (map_one _), Matrix.mul_one,
    Matrix.diagonal_map (map_zero _), Matrix.diagonal_mul]
  rfl

def revM (D : D7) (n : ℕ) : Matrix (Fin n) (Fin n) D.host.E := Matrix.of fun i j => if j = i.rev then 1 else 0

def halfM (D : D7) (n : ℕ) : Matrix (Fin n) (Fin n) D.host.E :=
  Matrix.diagonal fun i => if i < i.rev then 1 else 0

theorem revM_mul_self (n : ℕ) : revM D n * revM D n = 1 := by
  refine Matrix.ext fun i j => ?_
  rw [Matrix.mul_apply, Finset.sum_eq_single i.rev (fun k _ hk => by simp [revM, hk]) (by simp)]
  simp [revM, Matrix.one_apply, eq_comm]

theorem adj_revM (n : ℕ) : adj D (revM D n) = revM D n := by
  refine Matrix.ext fun i j => ?_
  have : i = j.rev ↔ j = i.rev := by
    constructor <;> rintro rfl <;> simp
  simp only [adj, revM, Matrix.transpose_apply, Matrix.map_apply, Matrix.of_apply, this]
  split_ifs <;> simp

theorem halfM_mul_self (n : ℕ) : halfM D n * halfM D n = halfM D n := by
  rw [halfM, Matrix.diagonal_mul_diagonal]
  congr 1
  funext i
  split_ifs <;> simp

theorem adj_halfM (n : ℕ) : adj D (halfM D n) = halfM D n := by
  rw [adj, halfM, Matrix.diagonal_map (map_zero _), Matrix.diagonal_transpose]
  congr 1
  funext i
  split_ifs <;> simp

theorem revM_mul_halfM {n : ℕ} (hn : Even n) : revM D n * halfM D n = revM D n - halfM D n * revM D n := by
  refine Matrix.ext fun i j => ?_
  obtain ⟨k, rfl⟩ := hn
  simp only [halfM, Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.sub_apply, revM, Matrix.of_apply]
  by_cases h : j = i.rev
  · subst h
    have hi := i.2
    by_cases h1 : i < i.rev
    · have h2 : ¬ i.rev < i := not_lt.2 h1.le
      simp [h1, h2]
    · have h2 : i.rev < i := by
        rw [Fin.lt_def, Fin.val_rev] at *
        omega
      simp [h1, h2]
  · simp [h]

theorem integral_diagonal {n : ℕ} {d : Fin n → D.host.E} (hd : ∀ i, IsIntegral ℤ (d i)) (i j : Fin n) :
    IsIntegral ℤ (Matrix.diagonal d i j) := by
  rw [Matrix.diagonal_apply]
  split_ifs
  · exact hd i
  · exact isIntegral_zero

theorem integral_one {n : ℕ} (i j : Fin n) : IsIntegral ℤ ((1 : Matrix (Fin n) (Fin n) D.host.E) i j) :=
  integral_diagonal (fun _ => isIntegral_one) i j

theorem det_adj {n : ℕ} (M : Matrix (Fin n) (Fin n) D.host.E) : (adj D M).det = D.host.conj M.det := by
  rw [adj, Matrix.det_transpose]
  exact ((D.host.conj : D.host.E →+* D.host.E).map_det M).symm

theorem adj_one_sub {n : ℕ} (M : Matrix (Fin n) (Fin n) D.host.E) : adj D (1 - M) = 1 - adj D M := by
  refine Matrix.ext fun i j => ?_
  simp [adj, Matrix.one_apply, eq_comm]

theorem det_mul_conj (hN : Even N) {γ : Matrix (Fin N) (Fin N) D.host.E} (h : γ * adj D γ = 1) :
    γ.det * D.host.conj (1 - γ).det = (1 - γ).det := by
  rw [← det_adj, adj_one_sub, ← Matrix.det_mul, Matrix.mul_sub, h, Matrix.mul_one, ← neg_sub, Matrix.det_neg,
    Fintype.card_fin, hN.neg_one_pow, one_mul]

theorem phase {g w : ℂ} (hw : w ≠ 0) (h : g * (starRingEnd ℂ) w = w) (k : ℕ) :
    ((‖w ^ (k + k)‖ : ℝ) : ℂ) / w ^ (k + k) = g ^ (-(k : ℤ)) := by
  have hg : g ≠ 0 := by rintro rfl; exact hw (by simpa using h.symm)
  have h1 : ((‖w ^ (k + k)‖ : ℝ) : ℂ) = (w * (starRingEnd ℂ) w) ^ k := by
    rw [Complex.mul_conj', norm_pow, ← two_mul, pow_mul]; push_cast; rfl
  rw [h1, zpow_neg, zpow_natCast, div_eq_iff (pow_ne_zero _ hw), eq_inv_mul_iff_mul_eq₀ (pow_ne_zero _ hg), ← mul_pow,
    mul_left_comm, h, mul_pow, pow_add]

theorem pull_eq_smul_iop : ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ), Crv D cc δ → ∀ (N N' : ℕ), Even N → Even N' → ∀ th ∈ Th D (tor0 D cc δ) (stdL D N) (stdL D N'), ∀ (γA : GA D N) (γ : Matrix (Fin N) (Fin N) D.host.E) (L₁ : Submodule (𝓞 D.host.E) (Fin N → D.host.E)), IsRat D (γA : GL (Fin N) (AE D)) γ → (1 - γ).det ≠ 0 → Moves D (γA : GL (Fin N) (AE D)) L₁ → pull D (tor0 D cc δ) γ 1 th = (∏ τ, embT D τ γ.det ^ (-((N' / 2 : ℕ) : ℤ))) • Iop D (tor0 D cc δ) (La0 D (tor0 D cc δ) N N') (La D (tor0 D cc δ) L₁ (stdL D N')) th := by
  intro D cc δ hc N N' hN hN' th hth γA γ L₁ hr hdet hm
  have hu : γ * adj D γ = 1 := (mem_ratG_intG D N).2.2.2.1 γA γ hr
  have hu' : adj D γ * γ = 1 := mul_eq_one_comm.1 hu
  obtain ⟨hint, hden, hmov⟩ := GlobalTheory.T.rationalMatrixMul_thetaLattices D cc δ hc N N'
  let u : VC D N N' ≃ₗ[ℂ] VC D N N' := LinearEquiv.ofLinear (mulV D 1 (adj D γ)) (mulV D 1 γ)
    (LinearMap.ext fun z => by simp [mulV_mulV, hu, mulV_one])
    (LinearMap.ext fun z => by simp [mulV_mulV, hu', mulV_one])
  have ua : ∀ z, u z = mulV D 1 (adj D γ) z := fun _ => rfl
  have us : ∀ z, u.symm z = mulV D 1 γ z := fun _ => rfl
  have hid : LinearMap.id - (u.symm : VC D N N' →ₗ[ℂ] VC D N N') = mulV D 1 (1 - γ) :=
    LinearMap.ext fun z => by rw [mulV_sub_right, mulV_one]; rfl
  have hd : LinearMap.det (LinearMap.id - (u.symm : VC D N N' →ₗ[ℂ] VC D N N')) =
      ∏ τ, embT D τ (1 - γ).det ^ N' := by
    rw [hid, GlobalTheory.T.det_rationalMatrixTwoSidedMul_eq_prod_embeddings]; simp
  have hw : ∀ τ, embT D τ (1 - γ).det ≠ 0 := fun τ => (map_ne_zero _).2 hdet
  have key := GlobalTheory.T.unitaryThetaConstant_eq_inverseDeterminantPhase D cc δ hc N N' (La0 D (tor0 D cc δ) N N') (La D (tor0 D cc δ) L₁ (stdL D N'))
    (klat _ (moves_one D N) (moves_one D N')) (klat _ hm (moves_one D N')) u
    (hf_unitary _ (by rw [adj_one, Matrix.one_mul]) (by rw [adj_adj, hu']))
    (hmov γA 1 γ 1 L₁ _ hr (isRat_one D N') hm (moves_one D N'))
    (by rw [hd]; exact Finset.prod_ne_zero_iff.2 fun τ _ => pow_ne_zero _ (hw τ)) ?_
    (mulV D (halfM D N') 1) (mulV D (revM D N') 1) ?_
    (fun x => by rw [mulV_mulV, halfM_mul_self, Matrix.one_mul])
    (fun x y => by rw [Hf_mulV, adj_halfM, adj_one])
    (fun x => by rw [mulV_mulV, revM_mul_self, Matrix.one_mul, mulV_one])
    (hf_unitary _ (by rw [adj_revM, revM_mul_self]) (by rw [adj_one, Matrix.one_mul]))
    (fun x => by rw [mulV_mulV, mulV_mulV, revM_mul_halfM hN', Matrix.one_mul, mulV_sub_left])
    (fun x => mulV_comm _ _ x) (fun x => mulV_comm _ _ x) ?_ th hth
  · rw [pull_eq, adj_one]
    refine key.trans ?_
    congr 1
    obtain ⟨k, rfl⟩ := hN'
    rw [hd, norm_prod, Complex.ofReal_prod, ← Finset.prod_div_distrib, show (k + k) / 2 = k by omega]
    refine Finset.prod_congr rfl fun τ _ => phase (hw τ) ?_ k
    rw [← embT_conj, ← map_mul, det_mul_conj hN hu]
  · obtain ⟨m₁, h₁, g₁⟩ := hden 1 (1 - γ)⁻¹
    obtain ⟨m₂, h₂, g₂⟩ := hden 1 ((1 - γ)⁻¹ * γ)
    have e : ∀ x : VC D N N', u.symm ((m₁ * m₂) • mulV D 1 (1 - γ)⁻¹ x) = (m₁ * m₂) • mulV D 1 ((1 - γ)⁻¹ * γ) x := by
      intro x
      rw [map_nsmul, us, mulV_mulV, Matrix.one_mul]
    refine ⟨m₁ * m₂, Nat.mul_pos h₁ h₂, fun x hx => ⟨(m₁ * m₂) • mulV D 1 (1 - γ)⁻¹ x, ?_, ?_, ?_⟩⟩
    · rw [mul_comm, mul_smul]; exact nsmul_mem (g₁ x hx) _
    · rw [e, mul_smul]; exact nsmul_mem (g₂ x hx) _
    · have h1 : (1 - γ)⁻¹ - (1 - γ)⁻¹ * γ = 1 := by
        have := Matrix.nonsing_inv_mul (1 - γ) (Ne.isUnit hdet)
        rwa [Matrix.mul_sub, Matrix.mul_one] at this
      rw [e, ← smul_sub, ← mulV_sub_right, h1, mulV_one]
  · refine fun x hx => ⟨hint _ _ (integral_diagonal fun i => ?_) integral_one x hx,
      hint _ _ (fun i j => ?_) integral_one x hx⟩
    · split_ifs
      · exact isIntegral_one
      · exact isIntegral_zero
    · rw [revM, Matrix.of_apply]
      split_ifs
      · exact isIntegral_one
      · exact isIntegral_zero
  · intro M hM
    obtain ⟨l, b, hlb⟩ := GlobalTheory.NegOneNorm.exists_norm_eq_neg_one D M hM
    have hM' : (M : D.host.E) ≠ 0 := Nat.cast_ne_zero.2 hM.ne'
    have hb : D.host.conj (b : D.host.E) = b := by
      have := congrArg D.host.conj hlb
      rw [map_mul, conj_conj, mul_comm, hlb, map_add, map_neg, map_one, map_mul, map_natCast] at this
      exact (mul_left_cancel₀ hM' (add_left_cancel this)).symm
    refine ⟨mulV D (Matrix.diagonal fun _ => (l : D.host.E)) 1, mulV D (Matrix.diagonal fun _ => (b : D.host.E)) 1,
      fun x hx => ⟨hint _ _ (integral_diagonal fun _ => l.2) integral_one x hx,
        hint _ _ (integral_diagonal fun _ => b.2) integral_one x hx⟩,
      fun x => mulV_comm _ _ x, fun x => mulV_comm _ _ x, fun x => ?_, fun x y => ?_, fun x y => ?_⟩
    · rw [mulV_mulV, mulV_mulV, halfM, Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
      simp only [mul_comm]
    · rw [Hf_mulV, adj_one, adj, Matrix.diagonal_map (map_zero _), Matrix.diagonal_transpose]
      simp only [hb]
    · have h : ∀ τ, embT D τ l * (starRingEnd ℂ) (embT D τ l) = -1 + M * embT D τ b := by
        intro τ
        rw [← embT_conj, ← map_mul, hlb]; simp
      simp only [Hf, mulV_scalar, ← neg_div, ← mul_div_assoc, ← add_div, Finset.mul_sum, ← Finset.sum_neg_distrib,
        ← Finset.sum_add_distrib, map_mul]
      congr 1
      refine Finset.sum_congr rfl fun τ _ => Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      linear_combination (x τ i j * (starRingEnd ℂ) (y τ i j)) * h τ

end GlobalTheory.RatRow
