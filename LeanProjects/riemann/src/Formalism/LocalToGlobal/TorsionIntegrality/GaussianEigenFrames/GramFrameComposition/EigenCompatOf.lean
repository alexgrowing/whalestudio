import Formalism.LocalToGlobal.TorsionIntegrality.GaussianEigenFrames.StatementF
import Formalism.LocalToGlobal.TorsionIntegrality.GaussianEigenFrames.GramFrameComposition.MatrixFormDiagBlocksBlockEmbed

noncomputable section
open scoped BigOperators ComplexConjugate

namespace Formalism.L2.Th1.GD

open Formalism.L2.Th1.H (cmL CmOK matH stdH stdLat blk4 pow4 imgLat relIdx IsIsom)
open Formalism.L2.Th1.D.GaussNormEstimates (normZ_le)

namespace GramDeterminantPositive

open GramFrameLatticeLemmas

section Norm

variable {K : Type} [NormedField K] [IsUltrametricDist K]

lemma nsum {α : Type} (s : Finset α) (f : α → K) (h : ∀ i ∈ s, ‖f i‖ ≤ 1) : ‖∑ i ∈ s, f i‖ ≤ 1 := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact (IsUltrametricDist.norm_add_le_max _ _).trans
      (max_le (h a (Finset.mem_insert_self a s)) (ih fun i hi => h i (Finset.mem_insert_of_mem hi)))

omit [IsUltrametricDist K] in
lemma nmul {x y : K} (hx : ‖x‖ ≤ 1) (hy : ‖y‖ ≤ 1) : ‖x * y‖ ≤ 1 := by
  rw [norm_mul]
  exact mul_le_one₀ hx (norm_nonneg _) hy

lemma nadd {x y : K} (hx : ‖x‖ ≤ 1) (hy : ‖y‖ ≤ 1) : ‖x + y‖ ≤ 1 := by
  exact (IsUltrametricDist.norm_add_le_max x y).trans (max_le hx hy)

omit [IsUltrametricDist K] in
lemma nneg {x : K} (hx : ‖x‖ ≤ 1) : ‖-x‖ ≤ 1 := by
  rw [norm_neg]
  exact hx

lemma nsub {x y : K} (hx : ‖x‖ ≤ 1) (hy : ‖y‖ ≤ 1) : ‖x - y‖ ≤ 1 := by
  rw [sub_eq_add_neg]
  exact nadd hx (nneg hy)

lemma nbil {J : Type} [Fintype J] {q : J → J → K} {X Y : J → K} (hq : ∀ j k, ‖q j k‖ ≤ 1) (hX : ∀ j, ‖X j‖ ≤ 1)
    (hY : ∀ j, ‖Y j‖ ≤ 1) : ‖∑ j, ∑ k, X j * q j k * Y k‖ ≤ 1 := by
  exact nsum _ _ fun j _ => nsum _ _ fun k _ => nmul (nmul (hX j) (hq j k)) (hY k)

end Norm

lemma bb_eq {K : Type} [Field K] {J Wt : Type} [Fintype J] [Fintype Wt] (W q : J → J → K) (D : Wt → J → K) (θ : K)
    (hQ : ∀ j k, ∑ w, D w j * D w k = W j k + θ * q j k) (X Y : J → K) :
    ∑ j, ∑ k, X j * W j k * Y k =
      ∑ w, (∑ j, X j * D w j) * (∑ k, Y k * D w k) - θ * ∑ j, ∑ k, X j * q j k * Y k := by
  have hW : ∀ j k, W j k = ∑ w, D w j * D w k - θ * q j k := fun j k => by rw [hQ]; ring
  have e1 : ∑ j, ∑ k, X j * (∑ w, D w j * D w k) * Y k =
      ∑ w, (∑ j, X j * D w j) * (∑ k, Y k * D w k) := by
    have r1 : ∀ w, (∑ j, X j * D w j) * (∑ k, Y k * D w k) =
        ∑ j, ∑ k, X j * D w j * (Y k * D w k) := fun w => by rw [Finset.sum_mul_sum]
    have l1 : ∀ j k, X j * (∑ w, D w j * D w k) * Y k = ∑ w, X j * D w j * (Y k * D w k) :=
      fun j k => by
        rw [Finset.mul_sum, Finset.sum_mul]
        exact Finset.sum_congr rfl fun w _ => by ring
    simp only [r1, l1]
    exact (Finset.sum_congr rfl fun j _ => Finset.sum_comm).trans Finset.sum_comm
  simp only [hW, mul_sub, sub_mul, Finset.sum_sub_distrib]
  rw [e1]
  congr 1
  simp only [Finset.mul_sum]
  exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => by ring

lemma lin_apply {n m : Type} [Fintype n] [DecidableEq n] (T : (n → ℂ) →ₗ[ℂ] (m → ℂ)) (y : n → ℂ) (i : m) :
    T y i = ∑ i', T (Pi.single i' 1) i * y i' := by
  conv_lhs => rw [show y = ∑ i', y i' • Pi.single i' (1 : ℂ) by
    ext j
    simp [Finset.sum_apply, Pi.single_apply]]
  rw [map_sum, Finset.sum_apply]
  simp only [map_smul, Pi.smul_apply, smul_eq_mul]
  exact Finset.sum_congr rfl fun _ _ => mul_comm _ _

lemma gamma_inj {K : Type} [Field K] (ι : ℂ ≃+* K) {Wt : Type} [Fintype Wt] [DecidableEq Wt]
    (g : (Wt → ℂ) ≃ₗ[ℂ] (Wt → ℂ)) (u : Wt → K)
    (h : ∀ w', ∑ w, ι (g.symm (Pi.single w 1) w') * u w = 0) (w : Wt) : u w = 0 := by
  have h' : ∀ w', ∑ w, g.symm (Pi.single w 1) w' * ι.symm (u w) = 0 := fun w' => by
    have h1 := congrArg ι.symm (h w')
    simpa [map_sum, map_mul] using h1
  have hz : g.symm (fun w => ι.symm (u w)) = 0 := by
    ext w'
    rw [show g.symm (fun w => ι.symm (u w)) w' =
      (g.symm : (Wt → ℂ) →ₗ[ℂ] (Wt → ℂ)) (fun w => ι.symm (u w)) w' from rfl, lin_apply]
    exact h' w'
  have h2 := congrArg (fun f => f w) (g.symm.injective (hz.trans (map_zero g.symm).symm))
  simpa using h2

def cf {K : Type} [Field K] (ι : ℂ ≃+* K) (L : PeriodPair) {n : Type} [Fintype n] (h : Matrix n n ℂ) (y : n → ℂ) (i : n) : K :=
  ι (((Formalism.L2.Th1.F.area L : ℝ) : ℂ) * ∑ i', h i i' * conj (y i'))

lemma iota_hOK {K : Type} [Field K] (ι : ℂ ≃+* K) (L : PeriodPair) {n : Type} [Fintype n] (h : Matrix n n ℂ) (x y : n → ℂ) :
    ι (hOK L h x y) = ∑ i, ι (x i) * cf ι L h y i := by
  unfold hOK cf
  have e : ((Formalism.L2.Th1.F.area L : ℝ) : ℂ) * matH h x y =
      ∑ i, x i * (((Formalism.L2.Th1.F.area L : ℝ) : ℂ) * ∑ i', h i i' * conj (y i')) := by
    simp only [matH, LinearMap.mk₂'ₛₗ_apply, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  rw [e, map_sum]
  simp only [map_mul]

lemma first_position {K : Type} [Field K] (ι : ℂ ≃+* K) (L : PeriodPair) {n : Type} [Fintype n] (h : Matrix n n ℂ)
    {J : Type} [Fintype J] (x : J → n → ℂ) (a : J → K) (y : n → ℂ) :
    ∑ j, a j * ι (hOK L h (x j) y) = ∑ i, (∑ j, a j * ι (x j i)) * cf ι L h y i := by
  simp only [iota_hOK, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

lemma mapVec_comb {K : Type} [Field K] (ι : ℂ ≃+* K) {n : Type} [Fintype n] [DecidableEq n]
    (T : (n → ℂ) →ₗ[ℂ] (n → ℂ)) {J : Type} [Fintype J] (v : J → n → ℂ) (X : J → K) (i : n) :
    mapVec (ι : ℂ →+* K) T (fun i' => ∑ j, ι (v j i') * X j) i = ∑ j, ι (T (v j) i) * X j := by
  have hv : ∀ j, ι (T (v j) i) = ∑ i', ι (T (Pi.single i' 1) i) * ι (v j i') := fun j => by
    rw [lin_apply T (v j) i, map_sum]
    simp only [map_mul]
  unfold mapVec
  simp only [hv, RingEquiv.coe_toRingHom, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

end GramDeterminantPositive

open GramDeterminantPositive

theorem GramBasic_of (hG : GramTransfer) (hI : IotaOK) : GramBasic := by
  intro a b c d ha hd lam hlam hcm n _ _ h Λ g hg p _ ι hp J _ v hv B' B hB' hB
  obtain ⟨D, q0, hD, hq0, hDg, hDD⟩ := hG a b c d ha hd lam hlam hcm n h Λ g hg p ι hp J v hv
  have hd4 : d % 4 = 3 := by have := hcm.2.2.1; omega
  have hθ : ‖ι (Complex.I * ((Real.sqrt d : ℝ) : ℂ))‖ ≤ 1 := by
    rw [(hI d hd4 p ι).1]
    exact Real.rpow_le_one (norm_nonneg _) (IsUltrametricDist.norm_natCast_le_one _ _) (by norm_num)
  let W : Fin 4 × J → Fin 4 × J → ℂ_[p] := fun x y =>
    if x.1 = y.1 then ι (hOK (cmL a b d ha hd lam hlam) h (v x.2) (v y.2)) else 0
  have hQ : ∀ x y, ∑ w, D w x * D w y = W x y + ι (Complex.I * ((Real.sqrt d : ℝ) : ℂ)) * q0 x y := hDD
  let ext : (J → ℂ_[p]) → Fin 4 × J → ℂ_[p] := fun B0 x => if x.1 = 0 then B0 x.2 else 0
  have hext : ∀ B0 : J → ℂ_[p], (∀ j, ‖B0 j‖ ≤ 1) → ∀ x, ‖ext B0 x‖ ≤ 1 := by
    intro B0 hB0 x
    simp only [ext]
    split_ifs
    · exact hB0 _
    · simp
  have hS : ∀ B1 B2 : J → ℂ_[p], ∑ x, ∑ y, ext B1 x * W x y * ext B2 y =
      ∑ j, ∑ k, B1 j * ι (hOK (cmL a b d ha hd lam hlam) h (v j) (v k)) * B2 k := by
    intro B1 B2
    simp [ext, W, Fintype.sum_prod_type, Fin.sum_univ_four]
  have hbb := fun B1 B2 => bb_eq W q0 D (ι (Complex.I * ((Real.sqrt d : ℝ) : ℂ))) hQ (ext B1) (ext B2)
  have hPn : ∀ B1 B2 : J → ℂ_[p], (∀ j, ‖B1 j‖ ≤ 1) → (∀ j, ‖B2 j‖ ≤ 1) →
      ‖∑ w, (∑ x, ext B1 x * D w x) * (∑ y, ext B2 y * D w y)‖ ≤ 1 := fun B1 B2 h1 h2 =>
    nsum _ _ fun w _ => nmul (nsum _ _ fun x _ => nmul (hext B1 h1 x) (hD w x))
      (nsum _ _ fun y _ => nmul (hext B2 h2 y) (hD w y))
  have hu : ∀ B0 : J → ℂ_[p], (∀ i, ∑ k, B0 k * ι (v k i) = 0) → ∀ w, ∑ y, ext B0 y * D w y = 0 := by
    intro B0 h0 w
    refine gamma_inj ι g (fun w => ∑ y, ext B0 y * D w y) (fun w' => ?_) w
    obtain ⟨a', i⟩ := w'
    calc ∑ w, ι (g.symm (Pi.single w 1) (a', i)) * ∑ y, ext B0 y * D w y
        = ∑ y, ext B0 y * ∑ w, ι (g.symm (Pi.single w 1) (a', i)) * D w y := by
          simp only [Finset.mul_sum]
          rw [Finset.sum_comm]
          exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
      _ = 0 := by
          rw [Fintype.sum_prod_type, Finset.sum_eq_single (0 : Fin 4)]
          · simp only [ext, hDg]
            by_cases ha' : a' = 0
            · simp [ha', h0 i]
            · simp [ha']
          · intro b' _ hb'
            simp [ext, hb']
          · simp
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← hS B' B, hbb]
    exact nsub (hPn B' B hB' hB) (nmul hθ (nbil hq0 (hext B' hB') (hext B hB)))
  · have hP : ∑ w, (∑ x, ext B' x * D w x) * (∑ y, ext B y * D w y) =
        ∑ w, (∑ x, ext B x * D w x) * (∑ y, ext B' y * D w y) :=
      Finset.sum_congr rfl fun w _ => mul_comm _ _
    refine ⟨_, nsub (nbil hq0 (hext B hB) (hext B' hB')) (nbil hq0 (hext B' hB') (hext B hB)), ?_⟩
    rw [← hS B' B, ← hS B B', hbb, hbb]
    linear_combination hP
  · intro h0
    refine ⟨_, nneg (nbil hq0 (hext B' hB') (hext B hB)), ?_⟩
    rw [← hS B' B, hbb, Finset.sum_eq_zero fun w _ => by rw [hu B h0 w, mul_zero]]
    ring
  · intro h0
    rw [Finset.sum_comm]
    refine Finset.sum_eq_zero fun k _ => ?_
    rw [← Finset.sum_mul, first_position ι _ h v B' (v k)]
    simp [h0]

theorem EigenCompat_of (hB : GramBasic) : EigenCompat := by
  intro a b c d ha hd lam hlam hcm n _ _ h Λ g hg p _ ι hp J _ v hv T T' hTT' hΛ B' B χ χ' hB'n hBn hχ'
    hT hT'
  let v2 : J ⊕ J → n → ℂ := Sum.elim v fun k => T' (v k)
  have hv2 : ∀ x, InMul (cmL a b d ha hd lam hlam) Λ (v2 x) := by
    rintro (j | k)
    · exact hv j
    · intro ω hω
      show ω • T' (v k) ∈ Λ
      rw [← map_smul]
      exact hΛ _ (hv k ω hω)
  let B1 : J ⊕ J → ℂ_[p] := Sum.elim B' 0
  let C : J ⊕ J → ℂ_[p] := Sum.elim (fun k => -χ' * B k) B
  have hB1 : ∀ x, ‖B1 x‖ ≤ 1 := by
    rintro (j | k)
    · exact hB'n j
    · simp [B1]
  have hC : ∀ x, ‖C x‖ ≤ 1 := by
    rintro (j | k)
    · simp only [C, Sum.elim_inl, norm_neg, norm_mul]
      exact mul_le_one₀ hχ' (norm_nonneg _) (hBn j)
    · exact hBn k
  obtain ⟨-, -, h3, -⟩ := hB a b c d ha hd lam hlam hcm n h Λ g hg p ι hp (J ⊕ J) v2 hv2 B1 C hB1 hC
  have hCz : ∀ i, ∑ x, C x * ι (v2 x i) = 0 := by
    intro i
    have e1 : ∑ k, B k * ι (T' (v k) i) = χ' * ∑ k, B k * ι (v k i) := by
      have h1 := hT' i
      rw [mapVec_comb] at h1
      simpa only [mul_comm (B _)] using h1
    rw [Fintype.sum_sum_type]
    simp only [C, v2, Sum.elim_inl, Sum.elim_inr]
    rw [e1, Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_eq_zero fun k _ => by ring
  obtain ⟨e, he, hSe⟩ := h3 hCz
  refine ⟨e, he, ?_⟩
  rw [← hSe]
  have key : ∀ k, ∑ j, B' j * ι (hOK (cmL a b d ha hd lam hlam) h (v j) (T' (v k))) =
      χ * ∑ j, B' j * ι (hOK (cmL a b d ha hd lam hlam) h (v j) (v k)) := by
    intro k
    have hadj : ∀ j, hOK (cmL a b d ha hd lam hlam) h (v j) (T' (v k)) =
        hOK (cmL a b d ha hd lam hlam) h (T (v j)) (v k) := fun j => by
      simp only [hOK, hTT']
    simp only [hadj]
    rw [first_position ι _ h (fun j => T (v j)) B' (v k), first_position ι _ h v B' (v k), Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    have h1 := hT i
    rw [mapVec_comb] at h1
    rw [← mul_assoc]
    congr 1
    simpa only [mul_comm (B' _)] using h1
  have key2 : ∑ j, ∑ k, B' j * ι (hOK (cmL a b d ha hd lam hlam) h (v j) (T' (v k))) * B k =
      χ * ∑ j, ∑ k, B' j * ι (hOK (cmL a b d ha hd lam hlam) h (v j) (v k)) * B k := by
    have hk : ∀ k, ∑ j, B' j * ι (hOK (cmL a b d ha hd lam hlam) h (v j) (T' (v k))) * B k =
        χ * ∑ j, B' j * ι (hOK (cmL a b d ha hd lam hlam) h (v j) (v k)) * B k := fun k => by
      rw [← Finset.sum_mul, key, ← Finset.sum_mul, mul_assoc]
    rw [Finset.sum_comm, Finset.sum_congr rfl fun k _ => hk k, ← Finset.mul_sum, Finset.sum_comm]
  simp only [Fintype.sum_sum_type, B1, C, v2, Sum.elim_inl, Sum.elim_inr, Pi.zero_apply, zero_mul,
    Finset.sum_const_zero, add_zero, Finset.sum_add_distrib]
  rw [key2, sub_mul]
  have key3 : ∑ j, ∑ k, B' j * ι (hOK (cmL a b d ha hd lam hlam) h (v j) (v k)) * (-χ' * B k) =
      -(χ' * ∑ j, ∑ k, B' j * ι (hOK (cmL a b d ha hd lam hlam) h (v j) (v k)) * B k) := by
    rw [← neg_mul, Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun k _ => by ring
  rw [key3]
  ring

end Formalism.L2.Th1.GD
