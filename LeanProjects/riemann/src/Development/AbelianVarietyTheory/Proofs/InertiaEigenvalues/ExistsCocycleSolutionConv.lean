import Mathlib
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NotFullBot
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ConvZero
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CyclotomicFrobeniusSystemContinuationOpenDisc
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsInvariantBasisConvergingOpenDisc
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RingsCyclotomic

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct GlobalTheory.HWL GlobalTheory.Cyc PowerSeries

namespace GlobalTheory.NL.WCont

open GlobalTheory.HWL.InvCont GlobalTheory.Cyc.Cont GlobalTheory.Cyc.InvBasis

section Block

variable {R S κ : Type} [CommRing R] [CommRing S] [Fintype κ] [DecidableEq κ]

def blk (A : Matrix κ κ R) (u : κ → R) : Matrix (κ ⊕ Unit) (κ ⊕ Unit) R :=
  Matrix.fromBlocks A (Matrix.of fun i _ => u i) 0 1

theorem blk_mul (A B : Matrix κ κ R) (u v : κ → R) : blk A u * blk B v = blk (A * B) (A.mulVec v + u) := by
  ext (i | i) (j | j) <;> simp [blk, Matrix.mul_apply, Matrix.mulVec, dotProduct]

omit [Fintype κ] [DecidableEq κ] in
theorem blk_map {F : Type} [FunLike F R S] [RingHomClass F R S] (f : F) (A : Matrix κ κ R) (u : κ → R) :
    (blk A u).map f = blk (A.map f) (fun i => f (u i)) := by
  ext (i | i) (j | j) <;> simp [blk]

omit [Fintype κ] in
theorem blk_one : blk (1 : Matrix κ κ R) 0 = 1 := by
  ext (i | i) (j | j) <;> simp [blk, Matrix.one_apply]

end Block

theorem block_relation {L κ : Type} [Field L] [Fintype κ] [DecidableEq κ] (γ φ : L⟦X⟧ →ₐ[L] L⟦X⟧)
    (G G' P P' : Matrix κ κ L⟦X⟧) (y z z' : κ → L⟦X⟧) (Q Λ T a b : L⟦X⟧) (m k : ℕ)
    (U U' V V' : Matrix (κ ⊕ Unit) (κ ⊕ Unit) L⟦X⟧)
    (hU : ∀ c : κ ⊕ Unit → L⟦X⟧, (blk G z).mulVec (fun i => γ (c i)) = c →
      c = U.mulVec fun i => C (constantCoeff (c i)))
    (hUV : U * V = 1) (hUV' : U' * V' = 1) (hGU' : blk G' z' * U'.map γ = U') (hQ : IsUnit Q) (hΛ : IsUnit Λ)
    (hc : ∀ a, γ (φ a) = φ (γ a)) (hP : P * P' = Q ^ k • (1 : Matrix κ κ L⟦X⟧))
    (hGP : γ Q ^ m • (P * G'.map φ) = Q ^ m • (G * P.map γ))
    (hy : (Q ^ m * Λ) • G.mulVec (fun j => γ (y j)) - (Q ^ m * γ Λ) • y =
      (Λ * γ Λ) • (P.mulVec (fun j => φ (z' j)) - Q ^ m • z))
    (ha : Q ^ m * a * φ T = T) (hb : Λ * b = T) :
    ∃ B : Matrix (κ ⊕ Unit) (κ ⊕ Unit) L,
      blk (T • 1) 0 * U = blk (a • P) (b • y) * (blk (T • 1) 0 * U').map φ * B.map C := by
  obtain ⟨q, hq⟩ := hQ.exists_right_inv
  obtain ⟨e, he⟩ := hΛ.exists_right_inv
  have hqm : ∀ k : ℕ, Q ^ k * q ^ k = 1 := fun k => by rw [← mul_pow, hq, one_pow]
  have hγq : γ Q ^ m * γ q ^ m = 1 := by rw [← mul_pow, ← map_mul, hq, map_one, one_pow]
  have hγe : γ Λ * γ e = 1 := by rw [← map_mul, he, map_one]
  have hinv : (q ^ m • P) * ((Q ^ m * q ^ k) • P') = 1 := by
    rw [Matrix.smul_mul, Matrix.mul_smul, hP, smul_smul, smul_smul,
      show q ^ m * (Q ^ m * q ^ k) * Q ^ k = (Q ^ m * q ^ m) * (Q ^ k * q ^ k) by ring, hqm, hqm, one_mul, one_smul]
  obtain ⟨-, B, -, hB, -⟩ := frob_relation γ φ (blk G z) (blk G' z') U U' V V' (blk (q ^ m • P) (e • y))
    (blk ((Q ^ m * q ^ k) • P') (-((Q ^ m * q ^ k) • P').mulVec (e • y))) 1 0 0 hU hUV hUV' hGU' isUnit_one hc
    (by rw [blk_mul, hinv, Matrix.mulVec_neg, Matrix.mulVec_mulVec, hinv, Matrix.one_mulVec, neg_add_cancel,
      blk_one, pow_zero, one_smul])
    (by
      rw [pow_zero, pow_zero, one_smul, one_smul, blk_map, blk_map, blk_mul, blk_mul]
      congr 1
      · ext1 i j
        have h := congrFun (congrFun hGP i) j
        have h1 : (G * (q ^ m • P).map γ) i j = γ q ^ m * (G * P.map γ) i j := by
          simp [Matrix.mul_apply, Finset.mul_sum, mul_left_comm]
        rw [h1, Matrix.smul_mul]
        simp only [Matrix.smul_apply, smul_eq_mul] at h ⊢
        linear_combination (q ^ m * γ q ^ m) * h - (q ^ m * (P * G'.map φ) i j) * hγq +
          (γ q ^ m * (G * P.map γ) i j) * hqm m
      · funext i
        have h := congrFun hy i
        have h1 : G.mulVec (fun j => γ (e * y j)) i = γ e * G.mulVec (fun j => γ (y j)) i := by
          simp [Matrix.mulVec, dotProduct, Finset.mul_sum, mul_left_comm]
        simp only [Pi.add_apply, h1, Matrix.smul_mulVec, Pi.smul_apply, Pi.sub_apply, smul_eq_mul] at h ⊢
        set g := G.mulVec (fun j => γ (y j)) i
        set f := P.mulVec (fun j => φ (z' j)) i
        have h3 : Q ^ m * (γ e * g - e * y i) = f - Q ^ m * z i := by
          linear_combination (e * γ e) * h - (Q ^ m * γ e * g - γ Λ * γ e * (f - Q ^ m * z i)) * he +
            (Q ^ m * e * y i + (f - Q ^ m * z i)) * hγe
        linear_combination (-q ^ m) * h3 + (γ e * g - e * y i + z i) * hqm m)
  refine ⟨B, ?_⟩
  simp only [add_zero, pow_zero, one_smul] at hB
  have h4 : blk (T • 1) 0 * blk (q ^ m • P) (e • y) = blk (a • P) (b • y) * (blk (T • (1 : Matrix κ κ L⟦X⟧)) 0).map φ := by
    have h5 : (T • (1 : Matrix κ κ L⟦X⟧)).map φ = φ T • 1 := by
      ext1 i j; by_cases hij : i = j <;> simp [hij]
    rw [blk_map, h5, blk_mul, blk_mul]
    congr 1
    · rw [Matrix.smul_mul, Matrix.one_mul, Matrix.mul_smul, Matrix.mul_one, smul_smul, smul_smul]
      congr 1
      linear_combination (-q ^ m) * ha + (a * φ T) * hqm m
    · funext i
      have h6 : (fun i => φ ((0 : κ → L⟦X⟧) i)) = 0 := funext fun _ => map_zero φ
      rw [h6, Matrix.mulVec_zero, Matrix.smul_mulVec, Matrix.one_mulVec]
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
      linear_combination (-e * y i) * hb + (b * y i) * he
  rw [Matrix.map_mul, ← mul_assoc, ← h4, mul_assoc, mul_assoc, ← mul_assoc _ (U'.map φ), ← hB]

variable {l : ℕ} [hl : Fact l.Prime] {LL : FinExt l}

theorem exists_basis_bd {ι : Type} [Fintype ι] [DecidableEq ι] (s : ℕ) (u : ℤ_[l]ˣ) (hs : 1 ≤ s) (h2 : l = 2 → 2 ≤ s)
    (hu : ‖(u : ℤ_[l]) - 1‖ = (l : ℝ) ^ (-(s : ℤ))) :
    ∃ ρ : ℝ, 0 < ρ ∧ ρ < 1 ∧ ∀ G : Matrix ι ι (↥(OL LL))⟦X⟧, G.map constantCoeff = 1 →
      ∃ U V : Matrix ι ι (↥LL.1)⟦X⟧, U * V = 1 ∧ U.map constantCoeff = 1 ∧
      G.map (PowerSeries.map (algebraMap ↥(OL LL) ↥LL.1)) * U.map (act l ↥LL.1 u) = U ∧
      (∀ c : ι → (↥LL.1)⟦X⟧, (G.map (PowerSeries.map (algebraMap ↥(OL LL) ↥LL.1))).mulVec
        (fun i => act l ↥LL.1 u (c i)) = c → c = U.mulVec fun i => C (constantCoeff (c i))) ∧
      ∀ i j, ∃ c, Bd ρ c (U i j) := by
  have hρ : (0 : ℝ) < (l : ℝ) ^ (-((s : ℝ) + 1 / ((l : ℝ) - 1))) :=
    Real.rpow_pos_of_pos (Nat.cast_pos.2 hl.out.pos) _
  obtain ⟨ρ, h0, h1⟩ := exists_between (lt_min hρ one_pos)
  refine ⟨ρ, h0, h1.trans_le (min_le_right _ _), fun G hG => ?_⟩
  set e := Fintype.equivFin ι
  obtain ⟨U, V, hUV, hU0, hGU, hU, hc⟩ := exists_invariant_basis l LL s _ u hs h2 hu (G.submatrix e.symm e.symm)
    (by rw [← Matrix.submatrix_map, hG, Matrix.submatrix_one_equiv])
  refine ⟨U.submatrix e e, V.submatrix e e, ?_, ?_, ?_, fun c h => ?_, fun i j => ?_⟩
  · rw [Matrix.submatrix_mul_equiv, hUV, Matrix.submatrix_one_equiv]
  · rw [← Matrix.submatrix_map, hU0, Matrix.submatrix_one_equiv]
  · conv_rhs => rw [← hGU, ← Matrix.submatrix_mul_equiv _ _ _ e]
    simp [Matrix.submatrix_map]
  · have h' := hU (fun i => c (e.symm i)) (by
      funext i
      rw [← congrFun h (e.symm i)]
      exact Fintype.sum_equiv e.symm _ _ fun _ => rfl)
    funext i
    have h3 := congrFun h' (e i)
    rw [e.symm_apply_apply] at h3
    rw [h3]
    exact (Fintype.sum_equiv e _ _ fun j => by simp).symm
  · exact bd_of_tendsto ((hc _ _).1 ρ h0 (h1.trans_le (min_le_left _ _)))

theorem eq_C_of_fixed (s : ℕ) (u : ℤ_[l]ˣ) (hs : 1 ≤ s) (h2 : l = 2 → 2 ≤ s)
    (hu : ‖(u : ℤ_[l]) - 1‖ = (l : ℝ) ^ (-(s : ℤ))) (a : (↥LL.1)⟦X⟧) (ha : act l ↥LL.1 u a = a) :
    a = C (constantCoeff a) := by
  obtain ⟨ρ, -, -, h⟩ := exists_basis_bd (LL := LL) (ι := Unit) s u hs h2 hu
  obtain ⟨U, -, -, -, -, hU, -⟩ := h 1 (Matrix.map_one _ (map_zero _) (map_one _))
  rw [Matrix.map_one _ (map_zero _) (map_one _)] at hU
  have h1 := congrFun (hU (fun _ => 1) (by simp)) ()
  have h2 := congrFun (hU (fun _ => a) (by simp [ha])) ()
  simp only [Matrix.mulVec, dotProduct, Finset.univ_unique, Finset.sum_singleton, map_one, mul_one] at h1 h2
  rwa [← h1, one_mul] at h2

def Bded (a : (↥LL.1)⟦X⟧) : Prop := ∀ r : ℝ, 0 < r → r < 1 → ∃ c, Bd r c a

theorem Bded.mul {a b : (↥LL.1)⟦X⟧} (ha : Bded a) (hb : Bded b) : Bded (a * b) :=
  fun r h0 h1 => ex_mul h0 (ha r h0 h1) (hb r h0 h1)

theorem Bded.pow {a : (↥LL.1)⟦X⟧} (ha : Bded a) (k : ℕ) : Bded (a ^ k) := fun r h0 h1 => by
  obtain ⟨c, hc⟩ := ha r h0 h1
  exact ⟨_, hc.pow h0 k⟩

theorem bded_C (x : ↥LL.1) : Bded (C x) := fun r _ _ => ⟨_, bd_C r x⟩

theorem bded_map (a : (↥(OL LL))⟦X⟧) : Bded (PowerSeries.map (algebraMap ↥(OL LL) ↥LL.1) a) :=
  fun _ h0 h1 => ⟨1, bd_map _ (norm_OL l LL) h0 h1.le a⟩

theorem Bded.phi_pow {a : (↥LL.1)⟦X⟧} (ha : Bded a) (j : ℕ) : Bded ((phi l ↥LL.1 ^ j) a) :=
  fun r h0 h1 => ex_phi_pow l LL j h0 h1 (ha r h0 h1)

theorem Bded.conv {a : (↥LL.1)⟦X⟧} (ha : Bded a) : Conv a := fun r h0 h1 => by
  obtain ⟨y, hry, hy⟩ := exists_between h1
  obtain ⟨c, hc⟩ := ha y (h0.trans hry) hy
  exact hc.tendsto h0 hry

theorem tau_eq (s : ℕ) (hs : 1 ≤ s) (τ : (↥LL.1)⟦X⟧) (hτ : XX l ↥LL.1 s * τ = logS LL) :
    QQ l ↥LL.1 s * C ((l : ↥LL.1)⁻¹) * phi l ↥LL.1 τ = τ := by
  have hX : XX l ↥LL.1 s ≠ 0 := fun h => by
    have h1 := logS_deriv (LL := LL)
    rw [h, zero_mul] at hτ
    simp [← hτ] at h1
  have hl0 : (l : ↥LL.1) ≠ 0 := by exact_mod_cast hl.out.ne_zero
  have hinv : C ((l : ↥LL.1)⁻¹) * (l : (↥LL.1)⟦X⟧) = 1 := by
    rw [← map_natCast (C (R := ↥LL.1)), ← map_mul, inv_mul_cancel₀ hl0, map_one]
  have hQ : QQ l ↥LL.1 s * phi l ↥LL.1 τ = (l : (↥LL.1)⟦X⟧) * τ := by
    apply mul_left_cancel₀ hX
    rw [← mul_assoc, ← (XX_QQ_properties l _ s hs).1, ← map_mul, hτ,
      phi_log_series l ↥LL.1 (logS LL) (logS_const (LL := LL)) (logS_deriv (LL := LL)), ← hτ]
    ring
  linear_combination C ((l : ↥LL.1)⁻¹) * hQ + τ * hinv

theorem phi_pow_QQ_dvd (s : ℕ) (hs : 1 ≤ s) (τ : (↥LL.1)⟦X⟧) (hτ : XX l ↥LL.1 s * τ = logS LL) (j : ℕ) :
    ∃ b, Bded b ∧ (phi l ↥LL.1 ^ j) (QQ l ↥LL.1 s) * b = τ := by
  have hQ : Bded (QQ l ↥LL.1 s) := map_QQ (l := l) (O := ↥(OL LL)) (L := ↥LL.1) s ▸ bded_map _
  have hb : Bded τ := bd_tau l LL s _ τ logS_const logS_deriv hτ
  have h1 : ∀ j : ℕ, (phi l ↥LL.1 ^ j) (QQ l ↥LL.1 s) * C ((l : ↥LL.1)⁻¹) * (phi l ↥LL.1 ^ (j + 1)) τ =
      (phi l ↥LL.1 ^ j) τ := fun j => by
    conv_rhs => rw [← tau_eq s hs τ hτ, map_mul, map_mul, apply_C]
    rw [pow_succ, AlgHom.mul_apply]
  have h2 : ∀ j : ℕ, ∃ c, Bded c ∧ c * (phi l ↥LL.1 ^ j) τ = τ := fun j => by
    induction j with
    | zero => exact ⟨C 1, bded_C 1, by simp⟩
    | succ j ih =>
      obtain ⟨c, hc, h⟩ := ih
      exact ⟨_, hc.mul ((hQ.phi_pow j).mul (bded_C _)), by rw [mul_assoc, h1, h]⟩
  obtain ⟨c, hc, h⟩ := h2 j
  exact ⟨_, hc.mul ((bded_C ((l : ↥LL.1)⁻¹)).mul (hb.phi_pow (j + 1))), by linear_combination c * h1 j + h⟩

theorem map_phi_pow (j : ℕ) (a : (↥(OL LL))⟦X⟧) : PowerSeries.map (algebraMap ↥(OL LL) ↥LL.1)
    ((phi l ↥(OL LL) ^ j) a) = (phi l ↥LL.1 ^ j) (PowerSeries.map (algebraMap ↥(OL LL) ↥LL.1) a) := by
  induction j with
  | zero => rfl
  | succ j ih => rw [pow_succ', pow_succ', AlgHom.mul_apply, AlgHom.mul_apply, ← ih]; exact map_act _ _

theorem isUnit_QQ (s : ℕ) (hs : 1 ≤ s) : IsUnit (QQ l ↥LL.1 s) := by
  rw [isUnit_iff_constantCoeff, (XX_QQ_properties l _ s hs).2.2.1]
  exact (Nat.cast_ne_zero.2 hl.out.ne_zero : (l : ↥LL.1) ≠ 0).isUnit

theorem prod_dvd (s : ℕ) (hs : 1 ≤ s) (τ : (↥LL.1)⟦X⟧) (hτ : XX l ↥LL.1 s * τ = logS LL) (J : Multiset ℕ) :
    IsUnit (PowerSeries.map (algebraMap ↥(OL LL) ↥LL.1)
      (J.map fun j => (phi l ↥(OL LL) ^ j) (QQ l ↥(OL LL) s)).prod) ∧
    ∃ b, Bded b ∧ PowerSeries.map (algebraMap ↥(OL LL) ↥LL.1)
      (J.map fun j => (phi l ↥(OL LL) ^ j) (QQ l ↥(OL LL) s)).prod * b = τ ^ J.card := by
  induction J using Multiset.induction_on with
  | empty =>
    rw [Multiset.map_zero, Multiset.prod_zero, map_one]
    exact ⟨isUnit_one, C 1, bded_C 1, by simp⟩
  | cons j J ih =>
    obtain ⟨hu, b, hb, h⟩ := ih
    obtain ⟨c, hc, h'⟩ := phi_pow_QQ_dvd s hs τ hτ j
    have e := map_phi_pow (LL := LL) j (QQ l ↥(OL LL) s)
    rw [map_QQ] at e
    simp only [Multiset.map_cons, Multiset.prod_cons, map_mul, e, Multiset.card_cons]
    exact ⟨((isUnit_QQ s hs).map _).mul hu, _, hc.mul hb, by rw [mul_mul_mul_comm, h, h', pow_succ']⟩

theorem bded_blk {κ : Type} (A : Matrix κ κ (↥LL.1)⟦X⟧) (u : κ → (↥LL.1)⟦X⟧) (hA : ∀ i j, Bded (A i j))
    (hu : ∀ i, Bded (u i)) (a c : κ ⊕ Unit) : Bded (blk A u a c) := by
  rcases a with a | a <;> rcases c with c | c
  · exact hA a c
  · exact hu a
  · exact (show C 0 = blk A u (Sum.inr a) (Sum.inl c) by simp [blk]) ▸ bded_C 0
  · exact (show C 1 = blk A u (Sum.inr a) (Sum.inr c) by simp [blk]) ▸ bded_C 1

set_option maxHeartbeats 1000000 in

theorem letterwise (s r n m k : ℕ) [NeZero n] (hs : 1 ≤ s) (h2 : l = 2 → 2 ≤ s) (u : ℤ_[l]ˣ)
    (hu : ‖(u : ℤ_[l]) - 1‖ = (l : ℝ) ^ (-(s : ℤ))) (J : Multiset ℕ) (Λ : (↥(OL LL))⟦X⟧)
    (hΛ : Λ = (J.map fun j => (phi l ↥(OL LL) ^ j) (QQ l ↥(OL LL) s)).prod)
    (G P P' : ZMod n → Matrix (Fin r) (Fin r) (↥(OL LL))⟦X⟧) (y z : ZMod n → Fin r → (↥(OL LL))⟦X⟧)
    (hG : ∀ i, (G i).map constantCoeff = 1) (hz : ∀ i j, constantCoeff (z i j) = 0)
    (hP : ∀ i, P i * P' i = QQ l ↥(OL LL) s ^ k • (1 : Matrix (Fin r) (Fin r) (↥(OL LL))⟦X⟧))
    (hGP : ∀ i, act l _ u (QQ l ↥(OL LL) s) ^ m • (P i * (G (i - 1)).map (phi l _)) =
      QQ l ↥(OL LL) s ^ m • (G i * (P i).map (act l _ u)))
    (hy : ∀ i, (QQ l ↥(OL LL) s ^ m * Λ) • (G i).mulVec (fun j => act l _ u (y i j)) -
      (QQ l ↥(OL LL) s ^ m * act l _ u Λ) • y i = (Λ * act l _ u Λ) •
        ((P i).mulVec (fun j => phi l _ (z (i - 1) j)) - QQ l ↥(OL LL) s ^ m • z i)) :
    ∃ w : ZMod n → Fin r → (↥LL.1)⟦X⟧, (∀ i j, constantCoeff (w i j) = 0) ∧
      (∀ i j, Conv (logS LL ^ (m + J.card) * w i j)) ∧
      ∀ i, ((G i).map (PowerSeries.map (algebraMap ↥(OL LL) ↥LL.1))).mulVec (fun j => act l ↥LL.1 u (w i j)) - w i =
        fun j => PowerSeries.map (algebraMap ↥(OL LL) ↥LL.1) (z i j) := by
  obtain ⟨τ, hτ⟩ := exists_logS_div (LL := LL) s
  obtain ⟨hΛu, b, hb, hbΛ⟩ := prod_dvd s hs τ hτ J
  rw [← hΛ] at hΛu hbΛ
  have hτb : Bded τ := bd_tau l LL s _ τ logS_const logS_deriv hτ
  have hQb : Bded (QQ l ↥LL.1 s) := map_QQ (l := l) (O := ↥(OL LL)) (L := ↥LL.1) s ▸ bded_map _
  obtain ⟨ρ, hρ, hρ1, hex⟩ := exists_basis_bd (LL := LL) (ι := Fin r ⊕ Unit) s u hs h2 hu
  choose U V hUV hU0 hGU hU hbd using fun i => hex (blk (G i) (z i)) (by
    rw [blk_map, hG, funext (hz i)]; exact blk_one)
  set ι : (↥(OL LL))⟦X⟧ →+* (↥LL.1)⟦X⟧ := PowerSeries.map (algebraMap ↥(OL LL) ↥LL.1) with hι
  simp only [blk_map] at hGU hU
  have hact : ∀ (x : ℤ_[l]) (a : (↥(OL LL))⟦X⟧), ι (act l _ x a) = act l _ x (ι a) := fun x a => map_act x a
  have hphi : ∀ (a : (↥(OL LL))⟦X⟧), ι (phi l _ a) = phi l _ (ι a) := fun a => map_act _ a
  have hQ : ι (QQ l _ s) = QQ l _ s := map_QQ s
  have hlast : ∀ i c, U i (Sum.inr ()) c = (1 : Matrix (Fin r ⊕ Unit) (Fin r ⊕ Unit) (↥LL.1)⟦X⟧) (Sum.inr ()) c :=
    fun i c => by
      have h := congrFun (congrFun (hGU i) (Sum.inr ())) c
      have h0 := congrFun (congrFun (hU0 i) (Sum.inr ())) c
      rw [Matrix.map_apply] at h0
      rw [eq_C_of_fixed s u hs h2 hu (U i (Sum.inr ()) c) (by simpa [blk, Matrix.mul_apply] using h), h0,
        Matrix.one_apply, Matrix.one_apply]
      split_ifs
      exacts [map_one _, map_zero _]
  choose B hB using fun i => block_relation (act l ↥LL.1 u) (phi l ↥LL.1) ((G i).map ι) ((G (i - 1)).map ι)
    ((P i).map ι) ((P' i).map ι) (fun j => ι (y i j)) (fun j => ι (z i j)) (fun j => ι (z (i - 1) j))
    (QQ l ↥LL.1 s) (ι Λ) (τ ^ (m + J.card)) (QQ l ↥LL.1 s ^ J.card * C ((l : ↥LL.1)⁻¹) ^ (m + J.card))
    (b * τ ^ m) m k (U i) (U (i - 1)) (V i) (V (i - 1)) (hU i) (hUV i) (hUV (i - 1)) (hGU (i - 1))
    (isUnit_QQ s hs) hΛu (fun a => act_comm' l _ _ _ a)
    (by
      ext1 a c
      have h := congrArg ι (congrFun (congrFun (hP i) a) c)
      rw [← Matrix.map_mul, Matrix.map_apply, h, Matrix.smul_apply, Matrix.smul_apply, smul_eq_mul, smul_eq_mul,
        map_mul, map_pow, hQ, Matrix.one_apply, Matrix.one_apply, apply_ite ι, map_one, map_zero])
    (by
      ext1 a c
      have h := congrArg ι (congrFun (congrFun (hGP i) a) c)
      simpa only [Matrix.smul_apply, smul_eq_mul, Matrix.mul_apply, Matrix.map_apply, map_mul, map_pow, map_sum,
        hact, hphi, hQ] using h)
    (by
      funext a
      have h := congrArg ι (congrFun (hy i) a)
      simpa only [Pi.smul_apply, Pi.sub_apply, smul_eq_mul, Matrix.mulVec, dotProduct, Matrix.map_apply, map_mul,
        map_pow, map_sum, map_sub, hact, hphi, hQ] using h)
    (by rw [← mul_assoc, ← pow_add, map_pow, ← mul_pow, ← mul_pow, tau_eq s hs τ hτ])
    (by rw [← mul_assoc, hbΛ, ← pow_add, add_comm])
  have hrow : ∀ i a c, (blk ((τ ^ (m + J.card)) • (1 : Matrix (Fin r) (Fin r) (↥LL.1)⟦X⟧)) 0 * U i) (Sum.inl a) c =
      τ ^ (m + J.card) * U i (Sum.inl a) c := fun i a c => by
    simp [blk, Matrix.mul_apply, Matrix.one_apply]
  have key := continuation_abstract (phi l ↥LL.1) (phi_X_const l _) _ (inv_lt_one l) (bd_phi_X l LL)
    (fun i : ZMod n => i - 1) _ _ _
    (fun x hx hx1 i a c => bded_blk _ _ (fun _ _ => ((hQb.pow _).mul ((bded_C _).pow _)).mul (bded_map _))
      (fun _ => (hb.mul (hτb.pow _)).mul (bded_map _)) a c x hx hx1)
    (fun x _ _ i a c => ⟨_, bd_C x _⟩) hB ρ hρ
    (fun i a c => by
      rcases a with a | a
      · rw [hrow]
        exact ex_mul hρ (hτb.pow _ ρ hρ hρ1) (hbd i _ _)
      · simpa [blk, Matrix.mul_apply] using hbd i (Sum.inr ()) c)
  refine ⟨fun i j => -U i (Sum.inl j) (Sum.inr ()), fun i j => ?_, fun i j => ?_, fun i => ?_⟩
  · have h0 := congrFun (congrFun (hU0 i) (Sum.inl j)) (Sum.inr ())
    rw [Matrix.map_apply, Matrix.one_apply_ne Sum.inl_ne_inr] at h0
    rw [map_neg, h0, neg_zero]
  · rw [mul_neg, ← hτ, mul_pow, mul_assoc, ← hrow]
    exact conv_neg (conv_XX_pow_mul s _ (Bded.conv fun x hx hx1 => key x hx hx1 i _ _))
  · funext j
    have h := congrFun (congrFun (hGU i) (Sum.inl j)) (Sum.inr ())
    simp only [blk, Matrix.mul_apply, Fintype.sum_sum_type, Finset.univ_unique, Finset.sum_singleton,
      Matrix.map_apply, PUnit.default_eq_unit, hlast, Matrix.one_apply_eq, map_one, mul_one,
      Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂, Matrix.of_apply] at h
    simp only [Pi.sub_apply, Matrix.mulVec, dotProduct, map_neg, mul_neg, Finset.sum_neg_distrib, Matrix.map_apply]
    linear_combination -h

theorem letφ_pow_const {O : Type} [CommRing O] {n : ℕ} (φ : O⟦X⟧ →ₐ[O] O⟦X⟧) (q : O⟦X⟧) (j : ℕ) :
    (letφ (n := n) φ ^ j) (fun _ => q) = fun _ => (φ ^ j) q := by
  induction j with
  | zero => rfl
  | succ j ih => rw [pow_succ', pow_succ', AlgHom.mul_apply, AlgHom.mul_apply, ih]; rfl

theorem mulVec_letter {O : Type} [CommRing O] {r n : ℕ} (M : Matrix (Fin r) (Fin r) (LetA O n))
    (v : Fin r → LetA O n) (i : Fin r) (k : ZMod n) :
    M.mulVec v i k = (M.map (· k)).mulVec (fun j => v j k) i := by
  simp [Matrix.mulVec, dotProduct, Finset.sum_apply]

theorem const_of_mem {O : Type} [CommRing O] {n : ℕ} {a : LetA O n} (h : a ∈ Ideal.span {(letπ : LetA O n)})
    (k : ZMod n) : constantCoeff (a k) = 0 := by
  obtain ⟨b, rfl⟩ := Ideal.mem_span_singleton.1 h
  simp [letπ]

set_option maxHeartbeats 1000000 in

theorem over_letters (s r n m k : ℕ) [NeZero n] (hs : 1 ≤ s) (h2 : l = 2 → 2 ≤ s) (u : ℤ_[l]ˣ)
    (hu : ‖(u : ℤ_[l]) - 1‖ = (l : ℝ) ^ (-(s : ℤ))) (J : Multiset ℕ) (Q Λ : LetA ↥(OL LL) n)
    (hQ : Q = fun _ => QQ l ↥(OL LL) s) (hΛ : Λ = (J.map fun j => (letφ (phi l ↥(OL LL)) ^ j) Q).prod)
    (G P P' : Matrix (Fin r) (Fin r) (LetA ↥(OL LL) n)) (y z : Fin r → LetA ↥(OL LL) n)
    (hG : ∀ i j, (G - 1) i j ∈ Ideal.span {(letπ : LetA ↥(OL LL) n)})
    (hP : P * P' = Q ^ k • (1 : Matrix (Fin r) (Fin r) (LetA ↥(OL LL) n)))
    (hGP : letγ (act l ↥(OL LL) u) Q ^ m • (P * G.map (letφ (phi l ↥(OL LL)))) =
      Q ^ m • (G * P.map (letγ (act l ↥(OL LL) u))))
    (hz : ∀ j, z j ∈ Ideal.span {(letπ : LetA ↥(OL LL) n)})
    (hy : (Q ^ m * Λ) • G.mulVec (fun j => letγ (act l ↥(OL LL) u) (y j)) - (Q ^ m * letγ (act l ↥(OL LL) u) Λ) • y =
      (Λ * letγ (act l ↥(OL LL) u) Λ) • (P.mulVec (fun j => letφ (phi l ↥(OL LL)) (z j)) - Q ^ m • z)) :
    ∃ w : Fin r → LetA ↥LL.1 n, (∀ j i, constantCoeff (w j i) = 0) ∧
      (∀ j i, Conv (logS LL ^ (m + J.card) * w j i)) ∧
      (G.map toLL).mulVec (fun j i => act l ↥LL.1 u (w j i)) - w = fun j => toLL (z j) := by
  have hΛ' : Λ = fun _ => (J.map fun j => (phi l ↥(OL LL) ^ j) (QQ l ↥(OL LL) s)).prod := by
    rw [hΛ, hQ]
    simp only [letφ_pow_const]
    funext i
    rw [Pi.multiset_prod_apply, Multiset.map_map]
    rfl
  obtain ⟨w, h0, hc, hw⟩ := letterwise (LL := LL) s r n m k hs h2 u hu J _ rfl (fun i => G.map (· i))
    (fun i => P.map (· i)) (fun i => P'.map (· i)) (fun i j => y j i) (fun i j => z j i)
    (fun i => by
      ext1 a c
      have h := const_of_mem (hG a c) i
      rw [Matrix.sub_apply, Pi.sub_apply, map_sub, sub_eq_zero, ← one_letter] at h
      rw [Matrix.map_apply, Matrix.map_apply, h, Matrix.one_apply, Matrix.one_apply]
      split_ifs
      exacts [map_one _, map_zero _])
    (fun i j => const_of_mem (hz j) i)
    (fun i => by
      ext1 a c
      have h := congrFun (congrFun (congrFun hP a) c) i
      rw [mul_letter, hQ] at h
      rw [h, Matrix.smul_apply, Matrix.smul_apply, one_letter a c i]
      rfl)
    (fun i => by
      ext1 a c
      have h := congrFun (congrFun (congrFun hGP a) c) i
      simp only [Matrix.smul_apply, smul_eq_mul, Pi.mul_apply, Pi.pow_apply] at h ⊢
      rw [mul_letter, mul_letter, hQ] at h
      exact h)
    (fun i => by
      funext a
      have h' := congrFun hy a
      simp only [Pi.smul_apply, Pi.sub_apply, smul_eq_mul] at h' ⊢
      have h := congrFun h' i
      simp only [Pi.sub_apply, Pi.mul_apply, Pi.pow_apply] at h
      rw [mulVec_letter, mulVec_letter, hQ, hΛ'] at h
      exact h)
  refine ⟨fun j i => w i j, fun j i => h0 i j, fun j i => hc i j, ?_⟩
  funext j i
  rw [Pi.sub_apply, Pi.sub_apply, mulVec_letter]
  exact congrFun (hw i) j

end GlobalTheory.NL.WCont

namespace GlobalTheory.NL

open WCont GlobalTheory.HWL.InvCont

set_option maxHeartbeats 1000000 in

theorem exists_cocycle_solution_conv : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL), let W := (HW l).W K s LL h; ∀ (r m k : ℕ) (J : Multiset ℕ) (G Pm Pm' : Matrix (Fin r) (Fin r) (AA K LL)) (y z : Fin r → AA K LL), let Λ : AA K LL := (J.map fun j => (W.φA ^ j) W.Q).prod; let γL : LetA ↥LL.1 (Module.finrank ℚ_[l] ↥(K0 K)) → LetA ↥LL.1 (Module.finrank ℚ_[l] ↥(K0 K)) := fun a i => PowerSeries.subst (PowerSeries.map (algebraMap ↥(OL LL) ↥LL.1) (W.γ₀ W.gam PowerSeries.X)) (a i); (∀ i j, (G - 1) i j ∈ Ideal.span {(letπ : AA K LL)}) → Pm * Pm' = (W.Q ^ k) • (1 : Matrix (Fin r) (Fin r) (AA K LL)) → (W.γA W.gam W.Q ^ m) • (Pm * G.map W.φA) = (W.Q ^ m) • (G * Pm.map (W.γA W.gam)) → (∀ j, z j ∈ Ideal.span {(letπ : AA K LL)}) → (W.Q ^ m * Λ) • G.mulVec (fun j => W.γA W.gam (y j)) - (W.Q ^ m * W.γA W.gam Λ) • y = (Λ * W.γA W.gam Λ) • (Pm.mulVec (fun j => W.φA (z j)) - (W.Q ^ m) • z) → ∃ (w : Fin r → LetA ↥LL.1 (Module.finrank ℚ_[l] ↥(K0 K))) (p : ℕ), (∀ j i, PowerSeries.constantCoeff (w j i) = 0) ∧ (∀ j i, GlobalTheory.HWL.Conv (GlobalTheory.HWL.logS LL ^ p * w j i)) ∧ (G.map GlobalTheory.HWL.toLL).mulVec (fun j => γL (w j)) - w = fun j => GlobalTheory.HWL.toLL (z j) := by
  intro D HW l _ K s LL h W r m k J G Pm Pm' y z Λ γL hG hP hGP hz hy
  haveI : FiniteDimensional ℚ_[l] ↥K.1 := K.2
  have hle : K0 K ≤ K.1 := inf_le_left
  haveI : FiniteDimensional ℚ_[l] ↥(K0 K) := FiniteDimensional.of_injective
    (IntermediateField.inclusion hle).toLinearMap (IntermediateField.inclusion_injective hle)
  haveI : NeZero (Module.finrank ℚ_[l] ↥(K0 K)) := ⟨Module.finrank_pos.ne'⟩
  obtain ⟨χ, -, hφ, hγ, -, hQ, hu, -⟩ := GlobalTheory.NL.CycRing.rings_cyclotomic D HW l K s LL h
  have eφ : W.φA = letφ (phi l ↥(OL LL)) := congrArg letφ hφ
  have eγ : W.γA W.gam = letγ (act l ↥(OL LL) (χ W.gam : ℤ_[l])) := congrArg letγ (hγ _)
  have eL : γL = fun a i => act l ↥LL.1 (χ W.gam : ℤ_[l]) (a i) := by
    funext a i
    change PowerSeries.subst (PowerSeries.map _ (W.γ₀ W.gam X)) _ = _
    rw [show W.γ₀ W.gam = _ from hγ _, act_X, map_cyc, act_apply]
  rw [eγ, eφ] at hGP hy
  obtain ⟨w, h0, hc, hw⟩ := over_letters s r _ m k h.1 h.2.1 (χ W.gam) hu J W.Q Λ (funext hQ) (by rw [← eφ])
    G Pm Pm' y z hG hP hGP hz hy
  exact ⟨w, _, h0, hc, by rw [eL]; exact hw⟩

end GlobalTheory.NL
