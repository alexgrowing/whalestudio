import Mathlib
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsSystem
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsHeatZero
import Development.AbelianVarietyTheory.Definitions.ThetaValues.MemAnalyticAtZeroOfEventuallyDifferentiableAt
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.DifferentiablePolyDeriv
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.DblZMemHn
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.PolyDerivEqSumList
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.InvariantPolynomialEqAevalPairingsStatement
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.PolyDerivPairingEqZeroOfIsHeatStatement

open Matrix Complex NumberField MeasureTheory GlobalTheory GlobalTheory.SW GlobalTheory.ThFr ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD
open scoped ComplexConjugate ComplexOrder Real Classical
open ReciprocityTheory.ChartRestriction.G.I2 (polyDeriv)

namespace GlobalTheory.SW.InvKill

noncomputable section

section General

open MvPolynomial

variable {ι σ W : Type} [Fintype σ] [DecidableEq σ] [NormedAddCommGroup W] [NormedSpace ℂ W]

def lin (d : σ → ℂ) : MvPolynomial σ ℂ := ∑ v, C (d v) * X v

omit [DecidableEq σ] in
theorem eval_lin (d y : σ → ℂ) : eval y (lin d) = d ⬝ᵥ y := by
  simp [lin, dotProduct]

omit [DecidableEq σ] in
theorem eval_aeval_lin (d : ι → σ → ℂ) (y : σ → ℂ) (P : MvPolynomial ι ℂ) :
    eval y (aeval (fun l => lin (d l)) P) = eval (fun l => d l ⬝ᵥ y) P := by
  induction P using MvPolynomial.induction_on with
  | C a => simp
  | add P Q hP hQ => simp only [map_add, hP, hQ]
  | mul_X P l hP => simp only [map_mul, hP, aeval_X, eval_X, eval_lin]

abbrev crdDir (σ : Type) [DecidableEq σ] : σ → σ → ℂ := fun v => Pi.single v 1

omit [DecidableEq σ] in
theorem smooth {F : (σ → ℂ) → ℂ} (hF : Differentiable ℂ F) : ContDiff ℂ (⊤ : ℕ∞) F :=
  (SCV.analyticOnNhd_of_differentiable hF Set.univ).contDiff

theorem polyDeriv_C (a : ℂ) (u : ι → W) (F : W → ℂ) (x : W) : polyDeriv (C a) u F x = a * F x := by
  have h : (C a : MvPolynomial ι ℂ) = a • monomial 0 1 := by simp [smul_eq_C_mul]
  rw [h]
  simp [I2.polyDeriv_smul, I2.polyDeriv_monomial_one, I2.pdTerm_eq_itD, -smul_monomial,
    -monomial_zero', I2.itD_nil]

theorem polyDeriv_aeval_lin {F : (σ → ℂ) → ℂ} (hF : Differentiable ℂ F) (d : ι → σ → ℂ)
    (P : MvPolynomial ι ℂ) (x : σ → ℂ) :
    polyDeriv (aeval (fun l => lin (d l)) P) (crdDir σ) F x = polyDeriv P d F x := by
  induction P using MvPolynomial.induction_on generalizing x with
  | C a => rw [algHom_C, algebraMap_eq, polyDeriv_C, polyDeriv_C]
  | add P Q hP hQ => simp only [map_add, I2.polyDeriv_add, hP, hQ]
  | mul_X P l hP =>
    rw [map_mul, aeval_X, lin, Finset.mul_sum, I2.jof_polyDeriv_sum,
      polyDeriv_mul_X (smooth hF)]
    conv_rhs => rw [pi_eq_sum_univ' (d l), map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [mul_left_comm, C_mul', I2.polyDeriv_smul, polyDeriv_mul_X (smooth hF), funext hP]
    simp

theorem polyDeriv_mul {F : (σ → ℂ) → ℂ} (hF : Differentiable ℂ F) (u : ι → σ → ℂ)
    (P Q : MvPolynomial ι ℂ) (x : σ → ℂ) :
    polyDeriv (P * Q) u F x = polyDeriv P u (fun y => polyDeriv Q u F y) x := by
  induction P using MvPolynomial.induction_on generalizing x with
  | C a => rw [C_mul', I2.polyDeriv_smul, polyDeriv_C]
  | add P P' hP hP' => simp only [add_mul, I2.polyDeriv_add, hP, hP']
  | mul_X P l hP =>
    rw [mul_right_comm, polyDeriv_mul_X (smooth hF),
      polyDeriv_mul_X (smooth (differentiable_polyDeriv (smooth hF) Q u)), funext hP]

theorem polyDeriv_bi {G : (σ → ℂ) → ℂ} (hG : Differentiable ℂ G) (A B : W →L[ℂ] (σ → ℂ))
    (u : ι → W) (P Q : MvPolynomial ι ℂ) :
    polyDeriv P u (fun z => polyDeriv Q u (fun w => G (A z + B w)) 0) 0 =
      polyDeriv (aeval (fun l => lin (A (u l))) P * aeval (fun l => lin (B (u l))) Q)
        (crdDir σ) G 0 := by
  have h1 (z : W) : polyDeriv Q u (fun w => G (A z + B w)) 0 =
      ((fun y => polyDeriv Q (B ∘ u) G y) ∘ A) z := by
    have h := Jet.polyDeriv_comp_clm Q u (F := fun v => G (A z + v)) (by fun_prop) B 0
    refine h.trans ?_
    simp only [polyDeriv, iteratedFDeriv_comp_add_left, map_zero, add_zero, Function.comp_apply]
  have hd := differentiable_polyDeriv (smooth hG) Q (B ∘ u)
  rw [funext h1, Jet.polyDeriv_comp_clm P u hd, map_zero, polyDeriv_mul hG,
    funext (polyDeriv_aeval_lin hG _ Q)]
  exact (polyDeriv_aeval_lin hd _ P 0).symm

theorem exists_absorb {K : (σ → ℂ) → ℂ} (hK : Differentiable ℂ K) (Q : MvPolynomial σ ℂ) :
    ∃ p : MvPolynomial σ ℂ, ∀ F : (σ → ℂ) → ℂ, Differentiable ℂ F →
      polyDeriv Q (crdDir σ) (fun x => K x * F x) 0 = polyDeriv p (crdDir σ) F 0 := by
  refine ⟨∑ m ∈ Q.support, ∑ c ∈ Finset.HasAntidiagonal.antidiagonal m,
    (Q.coeff m * ((∏ i, (m i).factorial : ℕ) : ℂ) * MvPowerSeries.coeff c.1 (taylor K) *
      ((∏ i, (c.2 i).factorial : ℕ) : ℂ)⁻¹) • monomial c.2 1, fun F hF => ?_⟩
  have hK' := SCV.analyticOnNhd_of_differentiable hK Set.univ 0 trivial
  have hF' := SCV.analyticOnNhd_of_differentiable hF Set.univ 0 trivial
  rw [dirPolyDeriv_eq_sum_coeff_taylor, show (fun x => K x * F x) = K * F from rfl,
    taylor_mul hK' hF', I2.jof_polyDeriv_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [I2.jof_polyDeriv_sum, MvPowerSeries.coeff_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [I2.polyDeriv_smul, coeff_taylor F]
  ring

theorem absorb_invariant {K : (σ → ℂ) → ℂ} (hK : Differentiable ℂ K) {Q p : MvPolynomial σ ℂ}
    (hp : ∀ F : (σ → ℂ) → ℂ, Differentiable ℂ F →
      polyDeriv Q (crdDir σ) (fun x => K x * F x) 0 = polyDeriv p (crdDir σ) F 0)
    (S : (σ → ℂ) → σ → ℂ) (S' : (σ → ℂ) →L[ℂ] (σ → ℂ)) (hS : ∀ x y, x ⬝ᵥ S y = S' x ⬝ᵥ y)
    (hQ : ∀ y, eval (S y) Q = eval y Q) (hK' : ∀ x, K (S' x) = K x) (y : σ → ℂ) :
    eval (S y) p = eval y p := by
  have hd (y : σ → ℂ) : Differentiable ℂ fun x : σ → ℂ => cexp (x ⬝ᵥ y) := by
    unfold dotProduct; fun_prop
  have h1 (y : σ → ℂ) : eval y p = polyDeriv Q (crdDir σ) (fun x => K x * cexp (x ⬝ᵥ y)) 0 := by
    rw [hp _ (hd y)]
    have h := KernSym.polyDeriv_exp p (crdDir σ)
      (LinearMap.toContinuousLinearMap ((dotProductBilin ℂ ℂ).flip y)) 1
    simpa using h.symm
  have h2 : aeval (fun v => lin (S' (crdDir σ v))) Q = Q := by
    refine MvPolynomial.funext fun y => ?_
    rw [eval_aeval_lin, ← hQ y]
    simp [← hS]
  have h3 : (fun x => K x * cexp (x ⬝ᵥ S y)) = (fun x => K x * cexp (x ⬝ᵥ y)) ∘ S' := by
    funext x
    simp [hS, hK']
  rw [h1, h1, h3, Jet.polyDeriv_comp_clm _ _ (hK.fun_mul (hd y)), map_zero,
    ← polyDeriv_aeval_lin (hK.fun_mul (hd y))]
  exact congrArg (fun R => polyDeriv R _ _ _) h2

end General

section Letters

open MvPolynomial

variable {T J : Type} [Fintype T] [Fintype J] {n r g p q : ℕ}

abbrev Ell (T : Type) (n r : ℕ) : Type := T × Bool × Fin n × Fin r

def act (c : T → Bool → Matrix (Fin n) (Fin n) ℂ) : (Ell T n r → ℂ) →L[ℂ] (Ell T n r → ℂ) :=
  LinearMap.toContinuousLinearMap
    { toFun := fun y v => ∑ l, c v.1 v.2.1 v.2.2.1 l * y (v.1, v.2.1, l, v.2.2.2)
      map_add' := fun x y => by funext v; simp [mul_add, Finset.sum_add_distrib]
      map_smul' := fun a x => by funext v; simp [Finset.mul_sum, mul_left_comm] }

theorem act_apply (c : T → Bool → Matrix (Fin n) (Fin n) ℂ) (y : Ell T n r → ℂ) (v : Ell T n r) :
    act c y v = ∑ l, c v.1 v.2.1 v.2.2.1 l * y (v.1, v.2.1, l, v.2.2.2) := rfl

theorem dotProduct_act (c : T → Bool → Matrix (Fin n) (Fin n) ℂ) (x y : Ell T n r → ℂ) :
    x ⬝ᵥ act c y = act (fun t b => (c t b)ᵀ) x ⬝ᵥ y := by
  simp only [dotProduct, act_apply, Fintype.sum_prod_type, Finset.mul_sum, Finset.sum_mul,
    transpose_apply]
  refine Finset.sum_congr rfl fun t _ => Finset.sum_congr rfl fun b _ => ?_
  rw [Finset.sum_comm]
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => by ring

def uc (u : T → Matrix (Fin n) (Fin n) ℂ) (t : T) (b : Bool) : Matrix (Fin n) (Fin n) ℂ :=
  Matrix.of fun k l => if b then u t k l else conj (u t k l)

def gauss (c : T → ℂ) (M : T → Matrix (Fin r) (Fin r) ℂ) (x : Ell T n r → ℂ) : ℂ :=
  ∏ τ, c τ * cexp (Real.pi * ∑ k, (fun a => x (τ, true, k, a)) ⬝ᵥ M τ *ᵥ
    fun a => x (τ, false, k, a))

theorem differentiable_gauss (c : T → ℂ) (M : T → Matrix (Fin r) (Fin r) ℂ) :
    Differentiable ℂ (gauss (n := n) c M) := by
  unfold gauss mulVec dotProduct
  fun_prop

theorem gauss_act (c : T → ℂ) (M : T → Matrix (Fin r) (Fin r) ℂ)
    {u : T → Matrix (Fin n) (Fin n) ℂ} (hu : ∀ t, u t ∈ Matrix.unitaryGroup (Fin n) ℂ)
    (x : Ell T n r → ℂ) : gauss c M (act (fun t b => (uc u t b)ᵀ) x) = gauss c M x := by
  refine Finset.prod_congr rfl fun τ _ => ?_
  congr 3
  have h0 (Z Z' : Matrix (Fin n) (Fin r) ℂ) :
      ∑ k, Z' k ⬝ᵥ M τ *ᵥ Z k = (Z' * M τ * Zᵀ).trace := by
    simp only [dotProduct_mulVec]
    rfl
  have h1 : (u τ)ᴴᵀ * (u τ)ᵀ = 1 := by
    rw [← transpose_mul, ← star_eq_conjTranspose, Matrix.mem_unitaryGroup_iff.1 (hu τ),
      transpose_one]
  have h2 := h0 ((u τ)ᴴ * Matrix.of fun k a => x (τ, false, k, a))
    ((u τ)ᵀ * Matrix.of fun k a => x (τ, true, k, a))
  rw [transpose_mul, ← Matrix.mul_assoc, trace_mul_comm, Matrix.mul_assoc (u τ)ᵀ,
    Matrix.mul_assoc (u τ)ᵀ, ← Matrix.mul_assoc, h1, Matrix.one_mul, ← h0] at h2
  exact h2

def lift (idx : Fin g ≃ T × Fin r) (N : T → Bool → Fin r → Fin r → ℂ) :
    (Fin n → Fin g → ℂ) →L[ℂ] (Ell T n r → ℂ) :=
  LinearMap.toContinuousLinearMap
    { toFun := fun z v => ∑ a, N v.1 v.2.1 v.2.2.2 a * z v.2.2.1 (idx.symm (v.1, a))
      map_add' := fun x y => by funext v; simp [mul_add, Finset.sum_add_distrib]
      map_smul' := fun a x => by funext v; simp [Finset.mul_sum, mul_left_comm] }

omit [Fintype T] in
theorem lift_apply (idx : Fin g ≃ T × Fin r) (N : T → Bool → Fin r → Fin r → ℂ)
    (z : Fin n → Fin g → ℂ) (v : Ell T n r) :
    lift idx N z v = ∑ a, N v.1 v.2.1 v.2.2.2 a * z v.2.2.1 (idx.symm (v.1, a)) := rfl

theorem lift_single (idx : Fin g ≃ T × Fin r) (N : T → Bool → Fin r → Fin r → ℂ) (τ : T)
    (a : Fin r) (k : Fin n) (y : Ell T n r → ℂ) :
    lift idx N (Pi.single k (Pi.single (idx.symm (τ, a)) 1)) ⬝ᵥ y =
      ∑ b, ∑ c, N τ b c a * y (τ, b, k, c) := by
  have h (v : Ell T n r) : lift idx N (Pi.single k (Pi.single (idx.symm (τ, a)) 1)) v =
      if v.1 = τ then if v.2.2.1 = k then N τ v.2.1 v.2.2.2 a else 0 else 0 := by
    obtain ⟨t, b, l, c⟩ := v
    rw [lift_apply]
    by_cases hl : l = k <;> by_cases ht : t = τ <;> simp [Pi.single_apply, hl, ht]
  simp only [dotProduct, h, Fintype.sum_prod_type]
  rw [Finset.sum_eq_single τ (by simp +contextual) (by simp)]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [Finset.sum_eq_single k (by simp +contextual) (by simp)]
  simp

theorem lift_single_act (idx : Fin g ≃ T × Fin r) (N : T → Bool → Fin r → Fin r → ℂ) (τ : T)
    (a : Fin r) (b : Bool) (hN : ∀ c, N τ (!b) c a = 0) (k : Fin n)
    (s : T → Bool → Matrix (Fin n) (Fin n) ℂ) (y : Ell T n r → ℂ) :
    lift idx N (Pi.single k (Pi.single (idx.symm (τ, a)) 1)) ⬝ᵥ act s y =
      ∑ l, s τ b k l * lift idx N (Pi.single l (Pi.single (idx.symm (τ, a)) 1)) ⬝ᵥ y := by
  simp only [lift_single, act_apply, Fintype.sum_bool]
  cases b <;> simp only [Bool.not_false, Bool.not_true] at hN <;>
    simp only [hN, zero_mul, Finset.sum_const_zero, zero_add, add_zero, Finset.mul_sum] <;>
    rw [Finset.sum_comm] <;>
    exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => by ring

theorem eval_barP {σ : Type} (y : σ → ℂ) (P : MvPolynomial σ ℂ) :
    eval y (barP P) = conj (eval (fun l => conj (y l)) P) := by
  induction P using MvPolynomial.induction_on with
  | C a => simp [barP]
  | add P Q hP hQ => simp only [barP, map_add] at *; rw [hP, hQ]
  | mul_X P l hP => simp only [barP, map_mul, map_X, eval_X, conj_conj] at *; rw [hP]

omit [Fintype T] in

theorem invFam_eval {P : J → Harm.Poly ℂ T p q (Fin n)} (hP : InvFam P)
    {u : T → Matrix (Fin n) (Fin n) ℂ} (hu : ∀ t, u t ∈ Matrix.unitaryGroup (Fin n) ℂ)
    (z w z' w' : Harm.Var T p q (Fin n) → ℂ)
    (hz : ∀ t ρ k, z' (t, ρ, k) = ∑ l, uc u t ρ.isLeft k l * z (t, ρ, l))
    (hw : ∀ t ρ k, w' (t, ρ, k) = ∑ l, uc u t ρ.isRight k l * w (t, ρ, l)) :
    ∑ j, eval z' (P j) * eval w' (barP (P j)) = ∑ j, eval z (P j) * eval w (barP (P j)) := by
  let γ : T → GL (Fin n) ℂ := fun t =>
    ⟨star (u t), u t, Matrix.mem_unitaryGroup_iff'.1 (hu t), Matrix.mem_unitaryGroup_iff.1 (hu t)⟩
  have h := hP γ (fun t => Unitary.star_mem (hu t)) z fun l => conj (w l)
  simp only [eval_barP]
  rw [← h]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Harm.colActHom, Harm.eval_colSubst, Harm.eval_colSubst]
  congr 4 <;> funext ⟨t, ρ, k⟩ <;> cases ρ <;>
    simp [hz, hw, uc, γ, mulVec, vecMul, dotProduct, mul_comm]

end Letters

section Core

open MvPolynomial

variable {T J : Type} [Fintype T] [DecidableEq T] [Fintype J] {n r g p q : ℕ}

theorem exists_invariant (idx : Fin g ≃ T × Fin r) (ρ : Fin q ⊕ Fin p → Fin r)
    (NA NB : T → Bool → Fin r → Fin r → ℂ)
    (hA : ∀ τ i c, NA τ (!i.isLeft) c (ρ i) = 0) (hB : ∀ τ i c, NB τ (!i.isRight) c (ρ i) = 0)
    {P : J → Harm.Poly ℂ T q p (Fin n)} (hP : InvFam P) (c : T → ℂ)
    (M : T → Matrix (Fin r) (Fin r) ℂ) (d : Harm.Var T q p (Fin n) → Fin n → Fin g → ℂ)
    (hd : ∀ t i k, d (t, i, k) = Pi.single k (Pi.single (idx.symm (t, ρ i)) 1)) :
    ∃ R : MvPolynomial (Ell T n r) ℂ,
      (∀ u : T → Matrix (Fin n) (Fin n) ℂ, (∀ t, u t ∈ Matrix.unitaryGroup (Fin n) ℂ) →
        ∀ y, eval (act (uc u) y) R = eval y R) ∧
      ∀ F : (Ell T n r → ℂ) → ℂ, Differentiable ℂ F →
        ∑ j, polyDeriv (P j) d (fun z => polyDeriv (barP (P j)) d (fun w =>
          gauss c M (lift idx NA z + lift idx NB w) * F (lift idx NA z + lift idx NB w)) 0) 0 =
        polyDeriv R (crdDir _) F 0 := by
  obtain ⟨R, hR⟩ := exists_absorb (differentiable_gauss (n := n) c M)
    (∑ j, aeval (fun l => lin (lift idx NA (d l))) (P j) *
      aeval (fun l => lin (lift idx NB (d l))) (barP (P j)))
  refine ⟨R, fun u hu => absorb_invariant (differentiable_gauss c M) hR _ _
    (dotProduct_act (uc u)) (fun y => ?_) (gauss_act c M hu), fun F hF => ?_⟩
  · simp only [map_sum, map_mul, eval_aeval_lin]
    refine invFam_eval hP hu _ _ _ _ (fun t i k => ?_) fun t i k => ?_
    · simp only [hd]
      convert lift_single_act idx NA t (ρ i) _ (hA t i) k (uc u) y
    · simp only [hd]
      convert lift_single_act idx NB t (ρ i) _ (hB t i) k (uc u) y
  · rw [← hR F hF, I2.jof_polyDeriv_sum]
    exact Finset.sum_congr rfl fun j _ =>
      polyDeriv_bi ((differentiable_gauss c M).fun_mul hF) _ _ _ _ _

end Core

section Doubled

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r g n : ℕ} (X : Data E r)
  (idx : Fin g ≃ X.Ψ × Fin r) (x₁ x₂ : Frame X.Ψ r)

def ellM (τ : X.Ψ) (b : Bool) : Matrix (Fin r) (Fin r) ℂ :=
  if b then (τ.1 X.κ0 / 2) • ((X.Gm.map τ.1)ᵀ * (aLin X x₁ x₂ τ)⁻¹)
  else (-(τ.1 X.κ0 / 2)) • (X.Gm.map τ.1 * (aAnti X x₁ x₂ τ)⁻¹)

def ellN (s : Bool) (τ : X.Ψ) (b : Bool) (c a : Fin r) : ℂ :=
  if ((a : ℕ) < X.p0 ↔ b = s) then ellM X x₁ x₂ τ b c a else 0

theorem dblz_eq (z w : Fin n → Fin g → ℂ) : dblz X idx x₁ x₂ z w = fun τ => Matrix.of fun k a =>
    (lift idx (ellN X x₁ x₂ false) z + lift idx (ellN X x₁ x₂ true) w) (τ, false, k, a) := by
  funext τ
  ext k c
  simp only [dblz, of_apply, Pi.add_apply, lift_apply, mulVec_mulVec, ← smul_mulVec,
    ← Finset.sum_add_distrib]
  rw [mulVec, dotProduct]
  refine Finset.sum_congr rfl fun a _ => ?_
  by_cases h : (a : ℕ) < X.p0 <;> simp [ellN, ellM, h]

theorem dblz'_eq (z w : Fin n → Fin g → ℂ) : dblz' X idx x₁ x₂ z w = fun τ => Matrix.of fun k a =>
    (lift idx (ellN X x₁ x₂ false) z + lift idx (ellN X x₁ x₂ true) w) (τ, true, k, a) := by
  funext τ
  ext k c
  simp only [dblz', of_apply, Pi.add_apply, lift_apply, ← mulVec_transpose, mulVec_mulVec,
    ← smul_mulVec, ← Finset.sum_add_distrib]
  rw [mulVec, dotProduct]
  refine Finset.sum_congr rfl fun a _ => ?_
  by_cases h : (a : ℕ) < X.p0 <;> simp [ellN, ellM, h]

end Doubled

end

end GlobalTheory.SW.InvKill

namespace GlobalTheory.SW

open InvKill

theorem biDeriv_kZero_mul_heat_eq_zero : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E]
    (r : ℕ) (X : Data E r) (g q0 : ℕ) (hr : X.p0 + q0 = r) (idx : Fin g ≃ X.Ψ × Fin r) (n m : ℕ)
    (P : Fin m → Harm.Poly ℂ X.Ψ q0 X.p0 (Fin n)), r ≤ n → InvFam P →
    ∀ D : CM X.Ψ r r → CM X.Ψ n r → CM X.Ψ n r → ℂ, IsHeat X.Ψ D → (∀ Z ∈ Hn X.Ψ r, D Z 0 0 = 0) →
    ∀ x₁ ∈ X.dom, ∀ x₂ ∈ X.dom, biDeriv X hr idx P (fun z₁ w => kZero X idx x₁ x₂ z₁ w *
      D (dblZ X x₁ x₂) (dblz X idx x₁ x₂ z₁ w) (dblz' X idx x₁ x₂ z₁ w)) = 0 := by
  intro E _ _ _ r X g q0 hr idx n m P hn hP D hD h0 x₁ h₁ x₂ h₂
  have hZ := (dblZ_mem_Hn E r X x₁ h₁ x₂ h₂).2.1
  obtain ⟨R, hR, hR'⟩ := exists_invariant idx (rowIdx hr) (ellN X x₁ x₂ false) (ellN X x₁ x₂ true)
    (by rintro τ (i | i) c <;> have := i.isLt <;> simp [ellN] <;> omega)
    (by rintro τ (i | i) c <;> have := i.isLt <;> simp [ellN] <;> omega) hP
    (fun τ => (((aLin X x₁ x₂ τ).det * (aAnti X x₁ x₂ τ).det) ^ (n / 2))⁻¹)
    (fun τ => (imH (dblZ X x₁ x₂ τ))⁻¹) (letterDir X hr idx) (fun _ _ _ => rfl)
  obtain ⟨s, rfl⟩ := GlobalTheory.T.exists_aeval_pairings_eq_of_invariant X.Ψ n r hn R hR
  have hF : Differentiable ℂ fun w : Ell X.Ψ n r → ℂ => D (dblZ X x₁ x₂)
      (fun τ => Matrix.of fun k a => w (τ, false, k, a))
      (fun τ => Matrix.of fun k a => w (τ, true, k, a)) := by
    have h := hD.1.comp (f := fun w : Ell X.Ψ n r → ℂ => ((dblZ X x₁ x₂,
      fun τ k a => w (τ, false, k, a), fun τ k a => w (τ, true, k, a)) :
        CF X.Ψ r r × CF X.Ψ n r × CF X.Ψ n r)) (s := Set.univ) (by fun_prop) fun _ _ => hZ
    exact differentiableOn_univ.1 h
  refine Eq.trans ?_ ((hR' _ hF).trans ?_)
  · simp only [biDeriv, kZero, dblz_eq, dblz'_eq]
    rfl
  · convert GlobalTheory.T.polyDeriv_aeval_pairings_eq_zero_of_isHeat E X.Ψ n r D hD h0 _ hZ s

end GlobalTheory.SW
