import Mathlib
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ConvZero
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GeomSumOneAddPrime
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AlgHomExtOfConstantCoeffZero
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IntegersCompleteDVR
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsInvariantBasis
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CyclotomicFrobeniusSystemContinuationOpenDiscStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsIntegralCyclotomicChar
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NormCoeAlgebraMap

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct GlobalTheory.HWL GlobalTheory.Cyc PowerSeries

namespace GlobalTheory.HWL.InvCont

section Formal

variable {L : Type} [Field L] {ι : Type} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in

theorem eq_mul_const (γ : L⟦X⟧ →ₐ[L] L⟦X⟧) (G U : Matrix ι ι L⟦X⟧)
    (hU : ∀ c : ι → L⟦X⟧, G.mulVec (fun i => γ (c i)) = c →
      c = U.mulVec fun i => C (constantCoeff (c i)))
    (W : Matrix ι ι L⟦X⟧) (hW : G * W.map γ = W) : W = U * (W.map constantCoeff).map C := by
  ext1 i k
  exact congrFun (hU (fun j => W j k) (funext fun j => congrFun (congrFun hW j) k)) i

theorem invariant_of_comm (γ g : L⟦X⟧ →ₐ[L] L⟦X⟧) (G H U : Matrix ι ι L⟦X⟧)
    (hU : ∀ c : ι → L⟦X⟧, G.mulVec (fun i => γ (c i)) = c →
      c = U.mulVec fun i => C (constantCoeff (c i)))
    (hU0 : U.map constantCoeff = 1) (hGU : G * U.map γ = U) (hH0 : H.map constantCoeff = 1)
    (hg : ∀ a, constantCoeff (g a) = constantCoeff a) (hc : ∀ a, γ (g a) = g (γ a))
    (hGH : G * H.map γ = H * G.map g) : H * U.map g = U := by
  have h1 : (U.map g).map γ = (U.map γ).map g := by ext1 i j; exact hc _
  have h2 : (U.map g).map constantCoeff = 1 := by rw [← hU0]; ext1 i j; exact hg _
  have h := eq_mul_const γ G U hU (H * U.map g) (by
    rw [Matrix.map_mul, ← mul_assoc, hGH, h1, mul_assoc, ← Matrix.map_mul, hGU])
  rwa [Matrix.map_mul, hH0, h2, one_mul, Matrix.map_one _ (map_zero _) (map_one _), mul_one] at h

theorem frob_relation (γ φ : L⟦X⟧ →ₐ[L] L⟦X⟧) (G G' U U' V V' P P' : Matrix ι ι L⟦X⟧) (Q : L⟦X⟧) (m m' : ℕ)
    (hU : ∀ c : ι → L⟦X⟧, G.mulVec (fun i => γ (c i)) = c →
      c = U.mulVec fun i => C (constantCoeff (c i)))
    (hUV : U * V = 1) (hUV' : U' * V' = 1) (hGU' : G' * U'.map γ = U') (hQ : IsUnit Q)
    (hc : ∀ a, γ (φ a) = φ (γ a)) (hP : P * P' = Q ^ m' • (1 : Matrix ι ι L⟦X⟧))
    (hGP : γ Q ^ m • (P * G'.map φ) = Q ^ m • (G * P.map γ)) :
    ∃ A B : Matrix ι ι L, P * U'.map φ = Q ^ m • (U * A.map C) ∧
      Q ^ (m + m') • U = (Q ^ m' • P) * U'.map φ * B.map C ∧
      Q ^ (m + m') • V.transpose =
        (Q ^ (m + m) • P'.transpose) * V'.transpose.map φ * A.transpose.map C := by
  obtain ⟨q, hq⟩ := hQ.exists_right_inv
  have hqm : ∀ k : ℕ, Q ^ k * q ^ k = 1 := fun k => by rw [← mul_pow, hq, one_pow]
  have hγq : γ q ^ m * γ Q ^ m = 1 := by rw [← mul_pow, ← map_mul, mul_comm, hq, map_one, one_pow]
  have h1 : (U'.map φ).map γ = (U'.map γ).map φ := by ext1 i j; exact hc _
  have hφ : U'.map φ * V'.map φ = 1 := by
    rw [← Matrix.map_mul, hUV', Matrix.map_one _ (map_zero _) (map_one _)]
  have hVU : V * U = 1 := mul_eq_one_comm.1 hUV
  set W : Matrix ι ι L⟦X⟧ := q ^ m • (P * U'.map φ) with hWdef
  have hWγ : W.map γ = γ q ^ m • (P.map γ * (U'.map γ).map φ) := by
    rw [← h1, ← Matrix.map_mul]; ext1 i j
    simp only [hWdef, Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, map_mul, map_pow]
  have hGP' : G * P.map γ = (q ^ m * γ Q ^ m) • (P * G'.map φ) := by
    rw [mul_smul, hGP, smul_smul, mul_comm, hqm, one_smul]
  have hW := eq_mul_const γ G U hU W (by
    rw [hWγ, Matrix.mul_smul, ← mul_assoc, hGP', Matrix.smul_mul, mul_assoc, ← Matrix.map_mul, hGU',
      smul_smul, mul_left_comm, hγq, mul_one])
  have hinv : W * ((Q ^ m * q ^ m') • (V'.map φ * P')) = 1 := by
    rw [hWdef, Matrix.smul_mul, Matrix.mul_smul, mul_assoc, ← mul_assoc (U'.map φ), hφ, one_mul, hP,
      smul_smul, smul_smul, show q ^ m * (Q ^ m * q ^ m') * Q ^ m' = (Q ^ m * q ^ m) * (Q ^ m' * q ^ m') by ring,
      hqm, hqm, one_mul, one_smul]
  have hAB := congrArg (fun M : Matrix ι ι L⟦X⟧ => (M.map constantCoeff).map C) hinv
  simp only [Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _)] at hAB
  set A := W.map constantCoeff
  have hA : P * U'.map φ = Q ^ m • (U * A.map C) := by
    rw [← hW, hWdef, smul_smul, hqm, one_smul]
  refine ⟨A, ((Q ^ m * q ^ m') • (V'.map φ * P')).map constantCoeff, hA, ?_, ?_⟩
  · rw [Matrix.smul_mul, hA, smul_smul, Matrix.smul_mul, mul_assoc, hAB, mul_one, pow_add, mul_comm]
  · have h3 : Q ^ m' • V = Q ^ m • (A.map C * V'.map φ * P') := by
      have : V * (P * U'.map φ) * (V'.map φ * P') = V * (Q ^ m • (U * A.map C)) * (V'.map φ * P') := by
        rw [hA]
      rwa [mul_assoc, mul_assoc, ← mul_assoc (U'.map φ), hφ, one_mul, hP, Matrix.mul_smul, mul_one,
        Matrix.mul_smul, Matrix.smul_mul, ← mul_assoc V, hVU, one_mul, ← mul_assoc] at this
    rw [Matrix.transpose_map, Matrix.transpose_map, Matrix.smul_mul, Matrix.smul_mul,
      ← Matrix.transpose_mul, ← Matrix.transpose_mul, ← mul_assoc, pow_add, pow_add, mul_smul, mul_smul,
      ← Matrix.transpose_smul (Q ^ m') V, h3, Matrix.transpose_smul]

end Formal

variable {l : ℕ} [Fact l.Prime] {LL : FinExt l}

theorem conv_add {a b : PowerSeries ↥LL.1} (ha : Conv a) (hb : Conv b) : Conv (a + b) := fun r h0 h1 => by
  have h := (ha r h0 h1).add (hb r h0 h1)
  rw [add_zero] at h
  refine squeeze_zero (fun k => by positivity) (fun k => ?_) h
  rw [← add_mul, map_add, IntermediateField.coe_add]
  exact mul_le_mul_of_nonneg_right (norm_add_le _ _) (by positivity)

theorem conv_neg {a : PowerSeries ↥LL.1} (ha : Conv a) : Conv (-a) := fun r h0 h1 => by
  simpa using ha r h0 h1

theorem conv_X_mul {a : PowerSeries ↥LL.1} (ha : Conv a) : Conv (X * a) := fun r h0 h1 => by
  have h := (ha r h0 h1).mul_const r
  rw [zero_mul] at h
  rw [← Filter.tendsto_add_atTop_iff_nat 1]
  simpa only [coeff_succ_X_mul, pow_succ, mul_assoc] using h

theorem conv_XX_mul (s : ℕ) {a : PowerSeries ↥LL.1} (ha : Conv a) : Conv (XX l ↥LL.1 s * a) := by
  have h : ∀ k : ℕ, Conv ((1 + X) ^ k * a) := fun k => by
    induction k with
    | zero => simpa using ha
    | succ k ih =>
      rw [pow_succ', mul_assoc, add_mul, one_mul]
      exact conv_add ih (conv_X_mul ih)
  rw [XX, sub_mul, one_mul, sub_eq_add_neg]
  exact conv_add (h _) (conv_neg ha)

theorem conv_XX_pow_mul (s k : ℕ) {a : PowerSeries ↥LL.1} (ha : Conv a) : Conv (XX l ↥LL.1 s ^ k * a) := by
  induction k with
  | zero => simpa using ha
  | succ k ih => rw [pow_succ', mul_assoc]; exact conv_XX_mul s ih

theorem logS_const : constantCoeff (logS LL) = 0 := by simp [logS]

theorem logS_deriv : (1 + X) * derivative ↥LL.1 (logS LL) = 1 := by
  have h : ∀ k, coeff k (derivative ↥LL.1 (logS LL)) = (-1) ^ k := fun k => by
    have : ((k : ↥LL.1) + 1) ≠ 0 := Nat.cast_add_one_ne_zero k
    rw [coeff_derivative, logS, coeff_mk]
    push_cast
    field_simp
    ring
  ext k
  rw [add_mul, one_mul, map_add]
  rcases k with _ | k
  · simp [h]
  · rw [coeff_succ_X_mul, h, h, coeff_one, if_neg k.succ_ne_zero, pow_succ]
    simp

theorem exists_logS_div (s : ℕ) : ∃ τ, XX l ↥LL.1 s * τ = logS LL := by
  obtain ⟨b, hb⟩ := cyc_eq_X_mul l ↥LL.1 ((l ^ (s - 1) : ℕ) : ℤ_[l])
  rw [cyc_natCast] at hb
  obtain ⟨t, ht⟩ := X_dvd_iff.2 (logS_const (LL := LL))
  have hu : IsUnit (C (algebraMap ℤ_[l] ↥LL.1 ((l ^ (s - 1) : ℕ) : ℤ_[l])) + X * b) := by
    rw [isUnit_iff_constantCoeff, map_natCast]
    have := (Fact.out : l.Prime).ne_zero
    simp [this]
  obtain ⟨v, hv⟩ := hu.exists_right_inv
  exact ⟨v * t, by rw [XX, hb, ht]; linear_combination (X * t) * hv⟩

section Generic

variable {O L : Type} [CommRing O] [Field L] [Algebra ℤ_[l] O] [Algebra ℤ_[l] L] [Algebra O L]
  [IsScalarTower ℤ_[l] O L]

theorem map_cyc (c : ℤ_[l]) : PowerSeries.map (algebraMap O L) (cyc l O c) = cyc l L c := by
  rw [cyc, cyc, map_sub, map_one, IsScalarTower.algebraMap_eq ℤ_[l] O L, PowerSeries.map_comp]
  rfl

theorem map_act (c : ℤ_[l]) (a : PowerSeries O) :
    PowerSeries.map (algebraMap O L) (act l O c a) = act l L c (PowerSeries.map (algebraMap O L) a) := by
  rw [act_apply, act_apply, ← map_cyc (O := O)]
  exact PowerSeries.map_subst (HasSubst.of_constantCoeff_zero' (cyc_const l _ c)) a

omit [Algebra ℤ_[l] O] [Algebra ℤ_[l] L] [IsScalarTower ℤ_[l] O L] [Fact l.Prime] in
theorem map_QQ (s : ℕ) : PowerSeries.map (algebraMap O L) (QQ l O s) = QQ l L s := by
  simp [QQ, XX, map_sum]

theorem const_act (c : ℤ_[l]) (a : PowerSeries O) : constantCoeff (act l O c a) = constantCoeff a := by
  obtain ⟨b, hb⟩ : X ∣ a - C (constantCoeff a) := by rw [X_dvd_iff]; simp
  rw [sub_eq_iff_eq_add] at hb
  conv_lhs => rw [hb]
  rw [map_add, map_mul, act_C, act_X]
  simp [cyc_const]

theorem letter_formal (s r n m m' : ℕ) (hs : 1 ≤ s) (hl : (l : L) ≠ 0) {I : Type} (c : I → ℤ_[l])
    (i₀ : I) (G : I → ZMod n → Matrix (Fin r) (Fin r) (PowerSeries O))
    (Pm Pm' : ZMod n → Matrix (Fin r) (Fin r) (PowerSeries O))
    (hG0 : ∀ g k, (G g k).map constantCoeff = 1)
    (hc : ∀ g k, G i₀ k * (G g k).map (act l _ (c i₀)) = G g k * (G i₀ k).map (act l _ (c g)))
    (hP : ∀ k, Pm k * Pm' k = QQ l O s ^ m' • (1 : Matrix (Fin r) (Fin r) (PowerSeries O)))
    (hGP : ∀ k, act l _ (c i₀) (QQ l O s) ^ m • (Pm k * (G i₀ (k - 1)).map (phi l _)) =
      QQ l O s ^ m • (G i₀ k * (Pm k).map (act l _ (c i₀))))
    (U V : ZMod n → Matrix (Fin r) (Fin r) (PowerSeries L)) (hUV : ∀ k, U k * V k = 1)
    (hU0 : ∀ k, (U k).map constantCoeff = 1)
    (hGU : ∀ k, (G i₀ k).map (PowerSeries.map (algebraMap O L)) * (U k).map (act l L (c i₀)) = U k)
    (hU : ∀ k (b : Fin r → PowerSeries L), ((G i₀ k).map (PowerSeries.map (algebraMap O L))).mulVec
      (fun i => act l L (c i₀) (b i)) = b → b = (U k).mulVec fun i => C (constantCoeff (b i))) :
    (∀ g k, (G g k).map (PowerSeries.map (algebraMap O L)) * (U k).map (act l _ (c g)) = U k) ∧
      ∃ A B : ZMod n → Matrix (Fin r) (Fin r) L, (∀ k,
        (Pm k).map (PowerSeries.map (algebraMap O L)) * (U (k - 1)).map (phi l _) =
          QQ l L s ^ m • (U k * (A k).map C)) ∧
        (∀ k, QQ l L s ^ (m + m') • U k = (QQ l O s ^ m' • Pm k).map (PowerSeries.map (algebraMap O L)) *
          (U (k - 1)).map (phi l L) * (B k).map C) ∧
        ∀ k, QQ l L s ^ (m + m') • (V k).transpose =
          (QQ l O s ^ (m + m) • (Pm' k).transpose).map (PowerSeries.map (algebraMap O L)) *
          (V (k - 1)).transpose.map (phi l L) * (A k).transpose.map C := by
  set ι : PowerSeries O →+* PowerSeries L := PowerSeries.map (algebraMap O L) with hι
  have hact : ∀ (x : ℤ_[l]) (M : Matrix (Fin r) (Fin r) (PowerSeries O)),
      (M.map (act l _ x)).map ι = (M.map ι).map (act l _ x) := fun x M => by
    ext1 i j; exact map_act x _
  have hsm : ∀ (a : PowerSeries O) (M : Matrix (Fin r) (Fin r) (PowerSeries O)),
      (a • M).map ι = ι a • M.map ι := fun a M => by
    ext1 i j; simp
  have hQ : IsUnit (QQ l L s) := by
    rw [isUnit_iff_constantCoeff, (XX_QQ_properties l _ s hs).2.2.1]
    exact hl.isUnit
  choose A B hA hB hV using fun k => frob_relation (act l _ (c i₀)) (phi l _) _ _ (U k) (U (k - 1)) (V k)
    (V (k - 1)) ((Pm k).map ι) ((Pm' k).map ι) (QQ l L s) m m' (hU k) (hUV k) (hUV (k - 1)) (hGU (k - 1)) hQ
    (fun a => act_comm' l _ _ _ a)
    (by rw [← Matrix.map_mul, hP, hsm, map_pow, map_QQ, Matrix.map_one _ (map_zero _) (map_one _)])
    (by
      have h := congrArg (fun M => M.map ι) (hGP k)
      simp only [hsm, Matrix.map_mul, map_pow] at h
      rw [map_act, map_QQ, phi, hact, hact] at h
      exact h)
  refine ⟨fun g k => ?_, A, B, hA, fun k => by rw [hB k, hsm, map_pow, map_QQ],
    fun k => by rw [hV k, hsm, map_pow, map_QQ, Matrix.transpose_map (M := Pm' k)]⟩
  refine invariant_of_comm (act l _ (c i₀)) (act l _ (c g)) _ _ _ (hU k) (hU0 k) (hGU k) ?_ (const_act _)
    (fun a => act_comm' l _ _ _ a) ?_
  · ext i j
    have : constantCoeff (G g k i j) = (1 : Matrix (Fin r) (Fin r) O) i j := by rw [← hG0 g k]; rfl
    rw [Matrix.map_apply, Matrix.map_apply, ← coeff_zero_eq_constantCoeff_apply, hι, coeff_map,
      coeff_zero_eq_constantCoeff_apply, this, Matrix.one_apply, Matrix.one_apply]
    split_ifs <;> simp
  · rw [← hact, ← hact, ← Matrix.map_mul, ← Matrix.map_mul, hc]

omit [Fact l.Prime] [Algebra ℤ_[l] O] in

theorem letφ_pow (n : ℕ) (φ : O⟦X⟧ →ₐ[O] O⟦X⟧) (q : O⟦X⟧) (hq : X * q = (1 + X) ^ l - 1) (hφ : φ X = X * q)
    (j : ℕ) : ∀ k, (letφ (n := n) φ ^ j) (fun _ => q) k = ∑ i ∈ Finset.range l, ((1 + X) ^ l ^ j) ^ i := by
  induction j with
  | zero =>
    intro k
    refine X_mul_cancel ?_
    have h := geom_sum_mul (1 + X : PowerSeries O) l
    simp only [pow_zero, pow_one, AlgHom.one_apply]
    rw [hq]
    linear_combination -h
  | succ j ih =>
    intro k
    rw [pow_succ', AlgHom.mul_apply]
    change φ ((letφ (n := n) φ ^ j) (fun _ => q) (k - 1)) = _
    rw [ih, map_sum]
    simp only [map_pow, map_add, map_one, hφ, hq, add_sub_cancel, ← pow_mul, pow_succ', mul_assoc]

omit [Algebra ℤ_[l] O] in

theorem mul_letter {r n : ℕ} (M N : Matrix (Fin r) (Fin r) (LetA O n)) (i j : Fin r) (k : ZMod n) :
    (M * N) i j k = (M.map (· k) * N.map (· k)) i j := by
  simp [Matrix.mul_apply, Finset.sum_apply]

omit [Algebra ℤ_[l] O] in

theorem one_letter {r n : ℕ} (i j : Fin r) (k : ZMod n) :
    (1 : Matrix (Fin r) (Fin r) O⟦X⟧) i j = (1 : Matrix (Fin r) (Fin r) (LetA O n)) i j k := by
  rw [Matrix.one_apply, Matrix.one_apply]
  split_ifs <;> rfl

theorem to_letters (s r n m m' : ℕ) {I : Type} [CommGroup I] (c : I → ℤ_[l]) (i₀ : I) (Q : LetA O n)
    (hQ : ∀ k, Q k = QQ l O s) (Gm : I → Matrix (Fin r) (Fin r) (LetA O n))
    (Pm Pm' : Matrix (Fin r) (Fin r) (LetA O n))
    (hmul : ∀ g h, Gm (g * h) = Gm g * (Gm h).map (letγ (act l O (c g))))
    (hP : Pm * Pm' = Q ^ m' • (1 : Matrix (Fin r) (Fin r) (LetA O n)))
    (hGP : (letγ (act l O (c i₀)) Q ^ m) • (Pm * (Gm i₀).map (letφ (phi l O))) =
      (Q ^ m) • (Gm i₀ * Pm.map (letγ (act l O (c i₀))))) :
    (∀ g k, (Gm i₀).map (· k) * ((Gm g).map (· k)).map (act l _ (c i₀)) =
      (Gm g).map (· k) * ((Gm i₀).map (· k)).map (act l _ (c g))) ∧
    (∀ k, Pm.map (· k) * Pm'.map (· k) = QQ l O s ^ m' • (1 : Matrix (Fin r) (Fin r) (PowerSeries O))) ∧
    ∀ k, act l _ (c i₀) (QQ l O s) ^ m • (Pm.map (· k) * ((Gm i₀).map (· (k - 1))).map (phi l _)) =
      QQ l O s ^ m • ((Gm i₀).map (· k) * (Pm.map (· k)).map (act l _ (c i₀))) := by
  refine ⟨fun g k => ?_, fun k => ?_, fun k => ?_⟩
  · have h := (hmul i₀ g).symm.trans ((congrArg Gm (mul_comm _ _)).trans (hmul g i₀))
    ext1 i j
    have h' := congrFun (congrFun (congrFun h i) j) k
    rw [mul_letter, mul_letter] at h'
    exact h'
  · ext1 i j
    have h' := congrFun (congrFun (congrFun hP i) j) k
    rw [mul_letter] at h'
    rw [h', ← hQ k]
    by_cases hij : i = j <;> simp [hij]
  · ext1 i j
    have h' := congrFun (congrFun (congrFun hGP i) j) k
    simp only [Matrix.smul_apply, smul_eq_mul, Pi.mul_apply, Pi.pow_apply] at h' ⊢
    rw [mul_letter, mul_letter] at h'
    rw [← hQ k]
    exact h'

end Generic

set_option maxHeartbeats 1000000 in

theorem letterwise (s r n m m' : ℕ) [NeZero n] (hs : 1 ≤ s) (h2 : l = 2 → 2 ≤ s) {I : Type} [CommGroup I]
    (c : I → ℤ_[l]ˣ) (i₀ : I) (hu : ‖(c i₀ : ℤ_[l]) - 1‖ = (l : ℝ) ^ (-(s : ℤ))) (Q : LetA ↥(OL LL) n)
    (hQ : ∀ k, Q k = QQ l ↥(OL LL) s) (Gm : I → Matrix (Fin r) (Fin r) (LetA ↥(OL LL) n))
    (Pm Pm' : Matrix (Fin r) (Fin r) (LetA ↥(OL LL) n))
    (hmul : ∀ g h, Gm (g * h) = Gm g * (Gm h).map (letγ (act l ↥(OL LL) (c g))))
    (h0 : ∀ g i j k, constantCoeff (Gm g i j k) = if i = j then 1 else 0)
    (hP : Pm * Pm' = Q ^ m' • (1 : Matrix (Fin r) (Fin r) (LetA ↥(OL LL) n)))
    (hGP : (letγ (act l ↥(OL LL) (c i₀)) Q ^ m) • (Pm * (Gm i₀).map (letφ (phi l ↥(OL LL)))) =
      (Q ^ m) • (Gm i₀ * Pm.map (letγ (act l ↥(OL LL) (c i₀))))) :
    ∃ (U V : Matrix (Fin r) (Fin r) (LetA ↥LL.1 n)), U * V = 1 ∧
      (∀ i j k, constantCoeff (U i j k) = if i = j then 1 else 0) ∧
      (∀ i j k, Conv (logS LL ^ (m + m') * U i j k) ∧ Conv (logS LL ^ (m + m') * V i j k)) ∧
      (∀ g, (Gm g).map toLL * U.map (fun a k => act l ↥LL.1 (c g) (a k)) = U) ∧
      ∃ Cm : Matrix (Fin r) (Fin r) (ZMod n → ↥LL.1),
        Pm.map toLL * U.map (fun a k => phi l ↥LL.1 (a (k - 1))) =
          (toLL Q ^ m) • (U * Cm.map (fun c k => C (c k))) := by
  have hG0 : ∀ g k, ((Gm g).map (· k)).map constantCoeff = 1 := fun g k => by
    ext1 i j; rw [Matrix.map_apply, Matrix.map_apply, h0, Matrix.one_apply]
  obtain ⟨e1, e2, e3⟩ := to_letters s r n m m' (fun g => (c g : ℤ_[l])) i₀ Q hQ Gm Pm Pm' hmul hP hGP
  choose U V hUV hU0 hGU hU hconv using fun k =>
    exists_invariant_basis l LL s r (c i₀) hs h2 hu ((Gm i₀).map (· k)) (hG0 i₀ k)
  obtain ⟨hinv, A, B, hA, hB, hV⟩ := letter_formal (L := ↥LL.1) s r n m m' hs
    (Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero) (fun g => (c g : ℤ_[l])) i₀
    (fun g k => (Gm g).map (· k)) (fun k => Pm.map (· k)) (fun k => Pm'.map (· k)) hG0 e1 e2 e3 U V hUV hU0 hGU hU
  obtain ⟨τ, hτ⟩ := exists_logS_div (LL := LL) s
  have hρ : (0 : ℝ) < (l : ℝ) ^ (-((s : ℝ) + 1 / ((l : ℝ) - 1))) :=
    Real.rpow_pos_of_pos (Nat.cast_pos.2 (Fact.out : l.Prime).pos) _
  have c1 := GlobalTheory.T.cyclotomicFrobenius_system_continuation_open_disc l LL s r n (m + m') hs _ τ logS_const logS_deriv hτ U _ B _ hρ hB
    (fun k i j => (hconv k i j).1)
  have c2 := GlobalTheory.T.cyclotomicFrobenius_system_continuation_open_disc l LL s r n (m + m') hs _ τ logS_const logS_deriv hτ (fun k => (V k).transpose)
    _ (fun k => (A k).transpose) _ hρ hV (fun k i j => (hconv k j i).2)
  refine ⟨Matrix.of fun i j k => U k i j, Matrix.of fun i j k => V k i j, ?_, fun i j k => ?_,
    fun i j k => ?_, fun g => ?_, Matrix.of fun i j k => A k i j, ?_⟩
  · ext1 i j
    funext k
    rw [mul_letter]
    exact (congrFun (congrFun (hUV k) i) j).trans (one_letter i j k)
  · exact (congrFun (congrFun (hU0 k) i) j).trans Matrix.one_apply
  · rw [← hτ, mul_pow, mul_assoc, mul_assoc]
    exact ⟨conv_XX_pow_mul s _ (c1 k i j), conv_XX_pow_mul s _ (c2 k j i)⟩
  · ext1 i j
    funext k
    rw [mul_letter]
    exact congrFun (congrFun (hinv g k) i) j
  · ext1 i j
    funext k
    rw [Matrix.smul_apply, smul_eq_mul, Pi.mul_apply, Pi.pow_apply, mul_letter, mul_letter, toLL, hQ, map_QQ]
    exact congrFun (congrFun (hA k) i) j

variable {P : LocPrime l} {K : FinExt l} {s : ℕ} {Γ : GamS P K s LL}

theorem exists_char (Γ : GamS P K s LL) : ∃ c : Γ.Gam → ℤ_[l]ˣ, ‖(c Γ.gam : ℤ_[l]) - 1‖ = (l : ℝ) ^ (-(s : ℤ)) ∧
    ∀ g, (Γ.χΓ g : ↥(OL LL)) = algebraMap ℤ_[l] ↥(OL LL) (c g) := by
  obtain ⟨χ, hχ, -⟩ := GlobalTheory.Cyc.exists_integral_cyclotomicChar l P
  have hex : ∀ g : Γ.Gam, ∃ c : ℤ_[l]ˣ, (Γ.χΓ g : ↥(OL LL)) = algebraMap ℤ_[l] ↥(OL LL) c := fun g => by
    obtain ⟨x, rfl⟩ := Γ.resΓ_onto g
    refine ⟨χ x, Subtype.ext ?_⟩
    have h := Γ.χΓ_res x
    rw [P.PD_χ, ← hχ] at h
    exact h
  choose c hc using hex
  refine ⟨c, ?_, hc⟩
  have h := Γ.gam_gen
  have hs : ((s : ℚ) : WithTop ℚ) = (s : WithTop ℚ) := by norm_cast
  rw [← hs, (GlobalTheory.HWL.NormVal.locPrime_v_normalised l P LL).1, hc, GroupLayer.norm_sub_one] at h
  rw [h, ← Real.rpow_intCast]; push_cast; rfl

set_option maxHeartbeats 1000000 in

theorem pinned (R : WSer Γ) : ∃ c : Γ.Gam → ℤ_[l]ˣ, ‖(c Γ.gam : ℤ_[l]) - 1‖ = (l : ℝ) ^ (-(s : ℤ)) ∧
    R.φ₀ = phi l _ ∧ (∀ g, R.γ₀ g = act l _ (c g)) ∧ ∀ k, R.Q k = QQ l ↥(OL LL) s := by
  obtain ⟨c, hu, hc⟩ := exists_char Γ
  obtain ⟨_, hO, hl0, hl1, -⟩ := GlobalTheory.Per.integers_completeDVR l LL
  have hq : X * R.q₀ = (1 + X) ^ l - 1 := by rw [R.q₀_def, P.PD_p]
  have hpin := fun g => act_unique l ↥(OL LL) hl0 hl1 (R.γ₀ g) R.φ₀ (c g) (R.φ₀_X.trans hq) (R.γ₀_comm g)
    (R.γ₀_X g).1 ((R.γ₀_X g).2.trans (hc g))
  refine ⟨c, hu, (hpin 1).1, fun g => (hpin g).2, fun k => ?_⟩
  rw [WSer.Q, letφ_pow _ _ _ hq R.φ₀_X, QQ, XX, add_sub_cancel]

end GlobalTheory.HWL.InvCont

namespace GlobalTheory.HWL

open InvCont

set_option maxHeartbeats 1000000 in

theorem exists_invariant_basis_conv : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (K : FinExt l) (s : ℕ) (LL : FinExt l), Good K s LL → ∀ (Γ : GamS P K s LL) (R : WSer Γ), ∀ (r m m' : ℕ) (Gm : Γ.Gam → Matrix (Fin r) (Fin r) (LetA ↥(OL LL) (Module.finrank ℚ_[l] ↥(K0 K)))) (Pm Pm' : Matrix (Fin r) (Fin r) (LetA ↥(OL LL) (Module.finrank ℚ_[l] ↥(K0 K)))), (∀ g h, Gm (g * h) = Gm g * (Gm h).map (letγ (R.γ₀ g))) → (∀ g i j k, PowerSeries.constantCoeff (Gm g i j k) = if i = j then 1 else 0) → Pm * Pm' = (R.Q ^ m') • (1 : Matrix (Fin r) (Fin r) (LetA ↥(OL LL) (Module.finrank ℚ_[l] ↥(K0 K)))) → (∀ g, (letγ (R.γ₀ g) R.Q ^ m) • (Pm * (Gm g).map (letφ R.φ₀)) = (R.Q ^ m) • (Gm g * Pm.map (letγ (R.γ₀ g)))) → ∃ (U V : Matrix (Fin r) (Fin r) (LetA ↥LL.1 (Module.finrank ℚ_[l] ↥(K0 K)))) (w : ℕ), U * V = 1 ∧ (∀ i j k, PowerSeries.constantCoeff (U i j k) = if i = j then 1 else 0) ∧ (∀ i j k, Conv (logS LL ^ w * U i j k) ∧ Conv (logS LL ^ w * V i j k)) ∧ (∀ g, (Gm g).map toLL * U.map (fun a k => PowerSeries.subst (PowerSeries.map (algebraMap ↥(OL LL) ↥LL.1) (R.γ₀ g PowerSeries.X)) (a k)) = U) ∧ ∃ Cm : Matrix (Fin r) (Fin r) (ZMod (Module.finrank ℚ_[l] ↥(K0 K)) → ↥LL.1), Pm.map toLL * U.map (fun a k => PowerSeries.subst ((1 + PowerSeries.X) ^ l - 1 : PowerSeries ↥LL.1) (a (k - 1))) = (toLL R.Q ^ m) • (U * Cm.map (fun c k => PowerSeries.C (c k))) := by
  intro l _ P K s LL hgood Γ R r m m' Gm Pm Pm' hmul h0 hP hGP
  haveI : FiniteDimensional ℚ_[l] ↥K.1 := K.2
  have hle : K0 K ≤ K.1 := inf_le_left
  haveI : FiniteDimensional ℚ_[l] ↥(K0 K) := FiniteDimensional.of_injective
    (IntermediateField.inclusion hle).toLinearMap (IntermediateField.inclusion_injective hle)
  haveI : NeZero (Module.finrank ℚ_[l] ↥(K0 K)) := ⟨Module.finrank_pos.ne'⟩
  obtain ⟨c, hu, hφ, hγ, hQ⟩ := pinned R
  simp only [hγ, hφ] at hmul hGP
  obtain ⟨U, V, h1, h2, h3, h4, h5⟩ := letterwise s r _ m m' hgood.1 hgood.2.1 c Γ.gam hu R.Q hQ Gm Pm Pm'
    hmul h0 hP (hGP Γ.gam)
  refine ⟨U, V, m + m', h1, h2, h3, fun g => ?_, ?_⟩
  · rw [hγ, act_X, map_cyc]
    simpa only [act_apply] using h4 g
  · rw [← cyc_natCast l ↥LL.1 l]
    simpa only [phi, act_apply] using h5

end GlobalTheory.HWL
