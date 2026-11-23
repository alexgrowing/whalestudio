import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.HermitianCurvatureForms
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CovariantSecondFundamentalForm
import Development.AbelianVarietyTheory.Definitions.Divisors.DiagValExtTraceNonneg

open Matrix Complex ComplexConjugate Filter Topology
open scoped ComplexOrder ContDiff
open GlobalTheory.HermFrame GlobalTheory.IndefiniteRowSideFullHecke.HermitianCurvatureForms

noncomputable section

namespace GlobalTheory.SubQuotChTwo

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] [NormedSpace ℝ V]
  [IsScalarTower ℝ ℂ V]

section Calc

variable {m n : Type} [Fintype m] [Fintype n]

theorem dbar_trace_mul {X : V → Matrix n m ℂ} {Y : V → Matrix m n ℂ} {z : V}
    (hX : MContDiffAt 1 X z) (hY : MContDiffAt 1 Y z) (η : V) :
    dbar (fun x => (X x * Y x).trace) z η = (mdbar X z η * Y z).trace + (X z * mdbar Y z η).trace := by
  have e : (fun x => (X x * Y x).trace) = fun x => ∑ a, (X x * Y x) a a := rfl
  rw [e, dbar_sum (fun a _ => ((hX.mul hY).diff a a))]
  have := mdbar_mul hX hY η
  simp only [ContinuousLinearMap.sum_apply, Matrix.trace, Matrix.diag]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun a _ => ?_
  have h2 := congrFun (congrFun this a) a
  simp only [mdbar_apply, Matrix.add_apply] at h2
  rw [h2, add_comm]

variable [DecidableEq m] [DecidableEq n]

theorem del_trace_mul {A : V → Matrix m m ℂ} {B : V → Matrix n n ℂ} {X : V → Matrix n m ℂ}
    {Y : V → Matrix m n ℂ} {z : V} (hX : MContDiffAt 1 X z) (hY : MContDiffAt 1 Y z) (ξ : V) :
    del (fun x => (X x * Y x).trace) z ξ =
      (homDel A B X z ξ * Y z).trace + (X z * homDel B A Y z ξ).trace := by
  have e : (fun x => (X x * Y x).trace) = fun x => ∑ a, (X x * Y x) a a := rfl
  rw [e, del_sum (fun a _ => (hX.mul hY).diff a a)]
  simp only [ContinuousLinearMap.sum_apply]
  have h1 : ∑ a, del (fun x => (X x * Y x) a a) z ξ = (mdel (fun x => X x * Y x) z ξ).trace := rfl
  rw [h1, mdel_mul hX hY]
  simp only [homDel, Matrix.add_mul, Matrix.sub_mul, Matrix.mul_add, Matrix.mul_sub,
    Matrix.trace_add, Matrix.trace_sub, Matrix.mul_assoc]
  rw [Matrix.trace_mul_comm (conn B z ξ)]
  simp only [Matrix.mul_assoc]
  ring

theorem mdbar_homDel {A : V → Matrix m m ℂ} {B : V → Matrix n n ℂ} {T : V → Matrix n m ℂ} {z : V}
    (hA : MContDiffAt 2 A z) (hAu : IsUnit (A z).det) (hB : MContDiffAt 2 B z)
    (hBu : IsUnit (B z).det) (hT : MContDiffAt 2 T z) (ξ η : V) :
    mdbar (fun x => homDel A B T x ξ) z η =
      homDel A B (fun x => mdbar T x η) z ξ - curv B z ξ η * T z + T z * curv A z ξ η := by
  have hT1 : MContDiffAt 1 T z := hT.of_le one_le_two
  have hcA : MContDiffAt 1 (fun x => conn A x ξ) z := hA.conn hAu (by norm_num) ξ
  have hcB : MContDiffAt 1 (fun x => conn B x ξ) z := hB.conn hBu (by norm_num) ξ
  have hdT : MContDiffAt 1 (fun x => mdel T x ξ) z := hT.mdel (by norm_num) ξ
  show mdbar (fun x => mdel T x ξ + conn B x ξ * T x - T x * conn A x ξ) z η = _
  rw [show (fun x => mdel T x ξ + conn B x ξ * T x - T x * conn A x ξ) =
      fun x => (mdel T x ξ + conn B x ξ * T x) + -(T x * conn A x ξ) from
      funext fun x => sub_eq_add_neg _ _]
  rw [mdbar_add (hdT.add (hcB.mul hT1)) (hT1.mul hcA).neg, mdbar_neg,
    mdbar_add hdT (hcB.mul hT1), mdbar_mul hcB hT1, mdbar_mul hT1 hcA, mdbar_mdel hT]
  simp only [homDel, curv, mdel_mdbar hT, Matrix.neg_mul, Matrix.mul_neg]
  abel

theorem mContDiffAt_homDel {A : V → Matrix m m ℂ} {B : V → Matrix n n ℂ} {T : V → Matrix n m ℂ}
    {z : V} (hA : MContDiffAt ∞ A z) (hAu : IsUnit (A z).det) (hB : MContDiffAt ∞ B z)
    (hBu : IsUnit (B z).det) (hT : MContDiffAt ∞ T z) (ξ : V) :
    MContDiffAt 1 (fun x => homDel A B T x ξ) z := by
  have hA2 : MContDiffAt 2 A z := hA.of_le (by norm_cast)
  have hB2 : MContDiffAt 2 B z := hB.of_le (by norm_cast)
  have hT2 : MContDiffAt 2 T z := hT.of_le (by norm_cast)
  exact ((hT2.mdel (by norm_num) ξ).add ((hB2.conn hBu (by norm_num) ξ).mul
    (hT2.of_le one_le_two))).sub ((hT2.of_le one_le_two).mul (hA2.conn hAu (by norm_num) ξ))

end Calc

theorem chTwo_eq_trace {n : Type} [Fintype n] [DecidableEq n] (H : V → Matrix n n ℂ)
    (z ξ₁ η₁ ξ₂ η₂ : V) : chTwo H z ξ₁ η₁ ξ₂ η₂ = kappa ^ 2 / 2 *
      ((curv H z ξ₁ η₁ * curv H z ξ₂ η₂).trace + (curv H z ξ₂ η₂ * curv H z ξ₁ η₁).trace
        - (curv H z ξ₁ η₂ * curv H z ξ₂ η₁).trace - (curv H z ξ₂ η₁ * curv H z ξ₁ η₂).trace) := by
  simp only [chTwo, wedge, Matrix.trace, Matrix.diag, Matrix.mul_apply, Finset.sum_add_distrib,
    Finset.sum_sub_distrib]

variable {m l : Type} [Fintype m] [Fintype l] [DecidableEq m] [DecidableEq l]

theorem trace_mul_eq_blocks (H K K' : Matrix (m ⊕ l) (m ⊕ l) ℂ) :
    (K * K').trace = (blockSS H K * blockSS H K').trace + (blockSQ H K * blockQS K').trace +
      (blockQS K * blockSQ H K').trace + (blockQQ H K * blockQQ H K').trace := by
  have hP := incl_mul_orthProj_add (m := m) (l := l) H
  have e : K * K' = K * (incl m l * orthProj H + orthLift H * quotMap m l) * K' *
      (incl m l * orthProj H + orthLift H * quotMap m l) := by rw [hP]; simp
  rw [e]
  simp only [blockSS, blockSQ, blockQS, blockQQ, Matrix.mul_add, Matrix.add_mul, Matrix.trace_add,
    Matrix.mul_assoc, Matrix.trace_mul_comm (orthProj H), Matrix.trace_mul_comm (quotMap m l)]
  ring

section Deriv

variable {U : Set V} {H : V → Matrix (m ⊕ l) (m ⊕ l) ℂ} {z : V}

theorem ddbar_extTrace (h : IsHermFrame U H) (hs : ∀ x ∈ U, IsUnit (subGram (H x)).det)
    (hz : z ∈ U) (ξ η ξ' η' : V) :
    ddbar (fun x => extTrace H x ξ' η') z ξ η = kappa *
      ((mdbar (fun x => homDel (gramS H) (gramQ H) (fun y => extFormAdj H y ξ') x ξ) z η *
          extForm H z η').trace +
        (homDel (gramS H) (gramQ H) (fun y => extFormAdj H y ξ') z ξ *
          mdbar (fun y => extForm H y η') z η).trace +
        (mdbar (fun y => extFormAdj H y ξ') z η *
          homDel (gramQ H) (gramS H) (fun y => extForm H y η') z ξ).trace +
        (extFormAdj H z ξ' *
          (homDel (gramQ H) (gramS H) (fun x => mdbar (fun y => extForm H y η') x η) z ξ -
            curv (gramS H) z ξ η * extForm H z η' + extForm H z η' * curv (gramQ H) z ξ η)).trace) := by
  have hS := h.sub hs
  have hQ := h.quot hs
  have hSu : ∀ x ∈ U, IsUnit (gramS H x).det := hs
  have hQu : ∀ x ∈ U, IsUnit (gramQ H x).det := fun x hx => hQ.isUnit x hx
  have sγ : ∀ x ∈ U, MContDiffAt ∞ (fun y => extFormAdj H y ξ') x := fun x hx =>
    GlobalTheory.IndefiniteRowSideFullHecke.CovariantSecondFundamentalForm.smooth_extFormAdj h hs hx ξ'
  have sβ : ∀ x ∈ U, MContDiffAt ∞ (fun y => extForm H y η') x := fun x hx =>
    GlobalTheory.IndefiniteRowSideFullHecke.CovariantSecondFundamentalForm.smooth_extForm h hs hx η'
  have one : ∀ {p q : Type} {F : V → Matrix p q ℂ} {x : V}, MContDiffAt ∞ F x →
      MContDiffAt 1 F x := fun hF => hF.of_le (by norm_cast)
  have two : ∀ {p q : Type} {F : V → Matrix p q ℂ} {x : V}, MContDiffAt ∞ F x →
      MContDiffAt 2 F x := fun hF => hF.of_le (by norm_cast)
  have htr : ContDiffAt ℝ 2 (fun x => (extFormAdj H x ξ' * extForm H x η').trace) z := by
    have hM := (two (sγ z hz)).mul (two (sβ z hz))
    simp only [Matrix.trace, Matrix.diag]
    exact ContDiffAt.sum fun a _ => hM a a
  have e : (fun x => extTrace H x ξ' η') =
      fun x => kappa • (extFormAdj H x ξ' * extForm H x η').trace := rfl
  rw [e, ddbar_const_smul kappa htr, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.smul_apply, smul_eq_mul, ddbar_eq_dbar_del htr]
  congr 1
  have ev : (fun x => del (fun y => (extFormAdj H y ξ' * extForm H y η').trace) x ξ) =ᶠ[𝓝 z]
      fun x => (homDel (gramS H) (gramQ H) (fun y => extFormAdj H y ξ') x ξ * extForm H x η').trace +
        (extFormAdj H x ξ' * homDel (gramQ H) (gramS H) (fun y => extForm H y η') x ξ).trace := by
    filter_upwards [h.isOpen.mem_nhds hz] with x hx
    exact del_trace_mul (one (sγ x hx)) (one (sβ x hx)) ξ
  have hD1 : MContDiffAt 1 (fun x => homDel (gramS H) (gramQ H) (fun y => extFormAdj H y ξ') x ξ) z :=
    mContDiffAt_homDel (hS.mContDiffAt hz) (hSu z hz) (hQ.mContDiffAt hz) (hQu z hz) (sγ z hz) ξ
  have hD2 : MContDiffAt 1 (fun x => homDel (gramQ H) (gramS H) (fun y => extForm H y η') x ξ) z :=
    mContDiffAt_homDel (hQ.mContDiffAt hz) (hQu z hz) (hS.mContDiffAt hz) (hSu z hz) (sβ z hz) ξ
  have dtr : ∀ {F : V → Matrix l m ℂ} {G : V → Matrix m l ℂ}, MContDiffAt 1 F z →
      MContDiffAt 1 G z → DifferentiableAt ℝ (fun x => (F x * G x).trace) z := fun hF hG => by
    have hM := hF.mul hG
    simp only [Matrix.trace, Matrix.diag]
    exact DifferentiableAt.fun_sum fun a _ => hM.diff a a
  rw [dbar_congr ev, dbar_add (dtr hD1 (one (sβ z hz))) (dtr (one (sγ z hz)) hD2),
    ContinuousLinearMap.add_apply, dbar_trace_mul hD1 (one (sβ z hz)),
    dbar_trace_mul (one (sγ z hz)) hD2,
    mdbar_homDel (A := gramQ H) (B := gramS H) (two (hQ.mContDiffAt hz)) (hQu z hz) (two (hS.mContDiffAt hz)) (hSu z hz)
      (two (sβ z hz)) ξ η]
  ring

end Deriv

theorem ddcForm_extTrace_eq : ∀ {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]
    [NormedSpace ℝ V] [IsScalarTower ℝ ℂ V] {m l : Type} [Fintype m] [Fintype l] [DecidableEq m]
    [DecidableEq l] {U : Set V} {H : V → Matrix (m ⊕ l) (m ⊕ l) ℂ} {z : V} (h : IsHermFrame U H)
    (hs : ∀ x ∈ U, IsUnit (subGram (H x)).det) (hz : z ∈ U) (hb : ∀ x ∈ U, ExtBlocksAt H x)
    (ξ₁ η₁ ξ₂ η₂ : V), ddcForm (extTrace H) z ξ₁ η₁ ξ₂ η₂ =
      chTwo (gramS H) z ξ₁ η₁ ξ₂ η₂ + chTwo (gramQ H) z ξ₁ η₁ ξ₂ η₂ - chTwo H z ξ₁ η₁ ξ₂ η₂ := by
  intro V _ _ _ _ m l _ _ _ _ U H z h hs hz hb ξ₁ η₁ ξ₂ η₂
  have hU : U ∈ 𝓝 z := h.isOpen.mem_nhds hz

  have hFD : ∀ η, mdbar (fun x => homDel (gramS H) (gramQ H) (fun y => extFormAdj H y ξ₂) x ξ₁) z η =
      mdbar (fun x => homDel (gramS H) (gramQ H) (fun y => extFormAdj H y ξ₁) x ξ₂) z η := by
    intro η
    refine mdbar_congr ?_ η
    filter_upwards [hU] with x hx
    exact sub_eq_zero.1 ((hb x hx).2.2.2.2.2.2.2.2 ξ₁ ξ₂)
  have hG : homDel (gramS H) (gramQ H) (fun y => extFormAdj H y ξ₂) z ξ₁ =
      homDel (gramS H) (gramQ H) (fun y => extFormAdj H y ξ₁) z ξ₂ :=
    sub_eq_zero.1 ((hb z hz).2.2.2.2.2.2.2.2 ξ₁ ξ₂)
  have hBd : mdbar (fun y => extForm H y η₂) z η₁ = mdbar (fun y => extForm H y η₁) z η₂ :=
    sub_eq_zero.1 ((hb z hz).2.2.2.2.2.2.2.1 η₁ η₂)
  have hHm : ∀ ξ, homDel (gramQ H) (gramS H) (fun x => mdbar (fun y => extForm H y η₂) x η₁) z ξ =
      homDel (gramQ H) (gramS H) (fun x => mdbar (fun y => extForm H y η₁) x η₂) z ξ := by
    intro ξ
    have ev : (fun x => mdbar (fun y => extForm H y η₂) x η₁) =ᶠ[𝓝 z]
        fun x => mdbar (fun y => extForm H y η₁) x η₂ := by
      filter_upwards [hU] with x hx
      exact sub_eq_zero.1 ((hb x hx).2.2.2.2.2.2.2.1 η₁ η₂)
    simp only [homDel]
    rw [mdel_congr ev ξ, hBd]

  obtain ⟨-, -, -, hSS, hSQ, hQS, hQQ, -, -⟩ := hb z hz
  have hK : ∀ ξ η ξ' η', (curv H z ξ η * curv H z ξ' η').trace =
      ((curv (gramS H) z ξ η + extForm H z η * extFormAdj H z ξ) *
        (curv (gramS H) z ξ' η' + extForm H z η' * extFormAdj H z ξ')).trace +
      (homDel (gramQ H) (gramS H) (fun y => extForm H y η) z ξ *
        mdbar (fun y => extFormAdj H y ξ') z η').trace +
      (mdbar (fun y => extFormAdj H y ξ) z η *
        homDel (gramQ H) (gramS H) (fun y => extForm H y η') z ξ').trace +
      ((curv (gramQ H) z ξ η - extFormAdj H z ξ * extForm H z η) *
        (curv (gramQ H) z ξ' η' - extFormAdj H z ξ' * extForm H z η')).trace := by
    intro ξ η ξ' η'
    rw [trace_mul_eq_blocks (H z)]
    simp only [hSS, hSQ, hQS, hQQ, wedgeAntiHol, wedgeHolAnti, covDelAnti, dbarHol, neg_neg,
      sub_neg_eq_add]

  have c1 : ∀ (X : Matrix m m ℂ) (P : Matrix m l ℂ) (Q : Matrix l m ℂ),
      (X * (P * Q)).trace = (Q * (X * P)).trace := fun X P Q => by
    rw [← Matrix.mul_assoc, Matrix.trace_mul_comm]
  have c3 : ∀ (Y : Matrix l l ℂ) (Q : Matrix l m ℂ) (P : Matrix m l ℂ),
      (Y * (Q * P)).trace = (Q * (P * Y)).trace := fun Y Q P => by
    rw [Matrix.trace_mul_comm, Matrix.mul_assoc]
  have c4 : ∀ (P : Matrix m l ℂ) (Q : Matrix l m ℂ), (P * Q).trace = (Q * P).trace :=
    fun P Q => Matrix.trace_mul_comm P Q
  simp only [ddcForm, ddbar_extTrace h hs hz, chTwo_eq_trace, hK]
  simp only [hFD, hG, hBd, hHm]
  simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_sub, Matrix.sub_mul, Matrix.trace_add,
    Matrix.trace_sub, Matrix.mul_assoc]
  simp only [c1, c3, c4, Matrix.mul_assoc]
  ring

end GlobalTheory.SubQuotChTwo
