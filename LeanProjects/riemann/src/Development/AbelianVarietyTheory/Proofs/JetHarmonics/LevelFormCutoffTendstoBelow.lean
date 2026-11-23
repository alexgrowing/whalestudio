import Mathlib
import Formalism.HermitianCurvature.HermitianCurvatureProofs.LimitOfModuleForms
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.BetaFinsetSumSmulOfXiExists

noncomputable section

namespace GlobalTheory.GivenXi

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

section sesq

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Matrix Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.BetaSesquilinearity Formalism.FourierDecayAlt.P.JCx2 Formalism.FourierDecayAlt.P.JCx4
open scoped ComplexConjugate

theorem formLev_sesquilinear (hΞ : B.XiExists) {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P0 : M.Par)
    (T : D.LevTower P0.k P0.r Wp Wq) (s : ℂ) (j : Fin (P0.r + 1)) (w : List C.Letter) (A : ℝ) (mm : ℕ)
    (hA : P5.Auser P0 w.length + 1 ≤ A) (hmm : P5.mmUser P0 w.length ≤ mm)
    (x x' y : Wd.Ix (Fin w.length) → B.Mat P0.k (P0.r - j) → (Wq →L[ℂ] Wp)) (c : ℂ)
    (hx : ∀ a, InCC A mm (x a)) (hx' : ∀ a, InCC A mm (x' a)) (hy : ∀ a, InCC A mm (y a)) :
    D.formLev T s j w (x + c • x') y = D.formLev T s j w x y + c * D.formLev T s j w x' y ∧
      D.formLev T s j w y (x + c • x') = D.formLev T s j w y x + starRingEnd ℂ c * D.formLev T s j w y x' := by
  have hS := ma_hS P0 T s j w

  have hAB : AB P0.k (P0.r - ↑j) ≤ A - 2 * (w.length : ℝ) := by
    have h1 := pd_thr_AB P0 j w.length A hA
    linarith
  have hm5 : 5 + (2 * (P0.r - ↑j) + P0.k + 1) * w.length ≤ mm := pd_thr_mm P0 j w.length mm hmm
  have hN0 : (0 : ℝ) ≤ w.length := Nat.cast_nonneg _

  have hin : ∀ {F : B.Mat P0.k (P0.r - j) → (Wq →L[ℂ] Wp)}, InCC A mm F →
      InCC (A - 2 * (w.length : ℝ) + ((2 * w.length : ℕ) : ℝ)) (5 + (2 * (P0.r - ↑j) + P0.k + 1) * w.length) F :=
    fun h => sq_inCC_mono (by push_cast; linarith) hm5 h

  have hvec : ∀ v : Wd.Ix (Fin w.length) → B.Mat P0.k (P0.r - j) → (Wq →L[ℂ] Wp),
      (∀ a, InCC A mm (v a)) → ∀ a,
        InCC (A - 2 * (w.length : ℝ)) 5 (D.actOp (D.RRlev T s j w) v a) := by
    intro v hv a
    rw [ma_actOp_eq]
    exact sq_inCC_sum Finset.univ (fun b => (D.RRlev T s j w a b) (v b)) (fun b _ => ma_inCC (hS a b) (hin (hv b)))
  have hlow : ∀ {F : B.Mat P0.k (P0.r - j) → (Wq →L[ℂ] Wp)}, InCC A mm F →
      InCC (A - 2 * (w.length : ℝ)) 5 F := fun h =>
    sq_inCC_mono (by linarith) (by omega) h
  refine ⟨?_, ?_⟩
  · show ∑ a, beta (T.bs j) (D.actOp (D.RRlev T s j w) (x + c • x') a) (y a) =
      ∑ a, beta (T.bs j) (D.actOp (D.RRlev T s j w) x a) (y a) +
        c * ∑ a, beta (T.bs j) (D.actOp (D.RRlev T s j w) x' a) (y a)
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun a _ => ?_
    have hGV : ∀ g ∈ GV P0.k (P0.r - j), D.actOp (D.RRlev T s j w) (x + c • x') a g =
        (D.actOp (D.RRlev T s j w) x a + c • D.actOp (D.RRlev T s j w) x' a) g := by
      intro g hg
      show (∑ b, D.ap (D.RRlev T s j w a b) ((x + c • x') b)) g =
        (∑ b, D.ap (D.RRlev T s j w a b) (x b) + c • ∑ b, D.ap (D.RRlev T s j w a b) (x' b)) g
      rw [Finset.sum_apply, Pi.add_apply, Pi.smul_apply, Finset.sum_apply, Finset.sum_apply, Finset.smul_sum,
        ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun b _ => ?_
      exact (hS a b).2.1 _ _ (x b) (x' b) c (hin (hx b)) (hin (hx' b)) g hg
    rw [sq_beta_congr (T.bs j) hGV]
    exact (GlobalTheory.BetaSum.beta_sesq hΞ (T.bs j) hAB (hvec x hx a) (hvec x' hx' a) (hlow (hy a)) c).1
  · show ∑ a, beta (T.bs j) (D.actOp (D.RRlev T s j w) y a) ((x + c • x') a) =
      ∑ a, beta (T.bs j) (D.actOp (D.RRlev T s j w) y a) (x a) +
        conj c * ∑ a, beta (T.bs j) (D.actOp (D.RRlev T s j w) y a) (x' a)
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun a _ => ?_
    exact (GlobalTheory.BetaSum.beta_sesq hΞ (T.bs j) hAB (hlow (hx a)) (hlow (hx' a)) (hvec y hy a) c).2

theorem formLev_norm_le (hΞ : B.XiExists) {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P0 : M.Par)
    (T : D.LevTower P0.k P0.r Wp Wq) (s : ℂ) (j : Fin (P0.r + 1)) (w : List C.Letter) (A : ℝ)
    (hA : P5.Auser P0 w.length + 1 ≤ A) :
    ∃ Cf : ℝ, 0 ≤ Cf ∧ ∀ (u v : Wd.Ix (Fin w.length) → B.Mat P0.k (P0.r - j) → (Wq →L[ℂ] Wp)) (cu cv : ℝ),
      (∀ b, CCle (A - 1) (5 + (2 * (P0.r - (j : ℕ)) + P0.k + 1) * w.length) (u b) cu) →
      (∀ a, CCle (A - 1 - 2 * (w.length : ℝ)) 5 (v a) cv) →
      ‖D.formLev T s j w u v‖ ≤ Cf * cu * cv := by
  have hR := ma_hS P0 T s j w
  set A'' : ℝ := A - 1 - 2 * (w.length : ℝ) with hA''
  have hop : ∀ a b, ∃ K : ℝ, 0 ≤ K ∧ ∀ (F : Mat P0.k (P0.r - j) → (Wq →L[ℂ] Wp)) (c : ℝ),
      CCle (A'' + ((2 * w.length : ℕ) : ℝ)) (5 + (2 * (P0.r - j) + P0.k + 1) * w.length) F c →
      CCle A'' 5 (D.RRlev T s j w a b F) (K * c) := fun a b => (hR a b).1 A'' 5
  choose K hK0 hK using hop
  set KK : ℝ := ∑ a, ∑ b, K a b with hKK
  have hKK0 : 0 ≤ KK := Finset.sum_nonneg fun a _ => Finset.sum_nonneg fun b _ => hK0 a b
  have hKab : ∀ a, ∑ b, K a b ≤ KK := fun a =>
    Finset.single_le_sum (f := fun a => ∑ b, K a b) (fun a _ => Finset.sum_nonneg fun b _ => hK0 a b)
      (Finset.mem_univ a)
  have hAB : AB P0.k (P0.r - j) ≤ A'' := pd_thr_AB P0 j w.length A hA
  obtain ⟨_, _, _, hB1, _, _, _⟩ := (BXiAsm.any_of hΞ) P0.k (P0.r - j) Wp Wq (T.bs j) A'' hAB
  obtain ⟨Cβ, hCβ⟩ := hB1
  have hA2 : A'' + ((2 * w.length : ℕ) : ℝ) = A - 1 := by rw [hA'']; push_cast; ring
  set card : ℝ := (Fintype.card (Wd.Ix (Fin w.length)) : ℝ)
  have hcard : 0 ≤ card := Nat.cast_nonneg _
  refine ⟨card * (|Cβ| * KK), mul_nonneg hcard (mul_nonneg (abs_nonneg _) hKK0), ?_⟩
  intro u v cu cv hcu hcv
  have hcu0 : 0 ≤ cu := pd_ccle_nonneg (hcu (Classical.arbitrary _))
  have hcv0 : 0 ≤ cv := pd_ccle_nonneg (hcv (Classical.arbitrary _))
  have hu' : ∀ b, CCle (A'' + ((2 * w.length : ℕ) : ℝ)) (5 + (2 * (P0.r - j) + P0.k + 1) * w.length) (u b) cu :=
    fun b => pd_ccle_mono (le_of_eq hA2) le_rfl (hcu b)
  have hRu : ∀ a, CCle A'' 5 (D.actOp (D.RRlev T s j w) u a) (KK * cu) := by
    intro a
    rw [ma_actOp_eq]
    refine pd_ccle_mono_c (pd_ccle_sum Finset.univ (fun b => D.RRlev T s j w a b (u b)) (fun b => K a b * cu)
      fun b _ => hK a b (u b) cu (hu' b)) ?_
    rw [← Finset.sum_mul]
    exact mul_le_mul_of_nonneg_right (hKab a) hcu0
  unfold D.formLev
  refine (norm_sum_le _ _).trans ?_
  have hterm : ∀ a, ‖B.beta (T.bs j) (D.actOp (D.RRlev T s j w) u a) (v a)‖ ≤ |Cβ| * (KK * cu) * cv := by
    intro a
    have h := (hCβ _ _ _ _ ⟨_, hRu a⟩ ⟨_, hcv a⟩ (pd_ccle_mono le_rfl (by norm_num) (hRu a))
      (pd_ccle_mono le_rfl (by norm_num) (hcv a))).2.2
    refine h.trans ?_
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_abs_self _) (mul_nonneg hKK0 hcu0)) hcv0
  refine (Finset.sum_le_sum fun a _ => hterm a).trans ?_
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  apply le_of_eq
  ring

theorem formLev_sesquilinear_finiteReg (hΞ : B.XiExists) : Formalism.FourierDecayAlt.JC.FormLevSesqMM := by
  intro Wp Wq _ _ _ _ _ _ P0 T s j w A mm ε _ hA hmm x x' y c hx hx' hy
  exact formLev_sesquilinear hΞ P0 T s j w A mm hA hmm x x' y c (fun a => (hx a).2.1) (fun a => (hx' a).2.1)
    (fun a => (hy a).2.1)

end sesq

section limit

open Matrix MeasureTheory Filter Topology
open scoped ContDiff
open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.PBE Formalism.FourierDecayAlt.P.JCTx6.Lev0

theorem formLev_tendsto (hΞ : B.XiExists) {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P0 : M.Par)
    (T : D.LevTower P0.k P0.r Wp Wq) (s : ℂ) (j : Fin (P0.r + 1)) (w : List C.Letter) (N : ℕ) (hw : w.length ≤ N)
    (ε₀ : ℝ) (hε₀ : 0 < ε₀)
    (x y : Wd.Ix (Fin w.length) → B.Mat P0.k (P0.r - j) → (Wq →L[ℂ] Wp))
    (xn yn : ℕ → Wd.Ix (Fin w.length) → B.Mat P0.k (P0.r - j) → (Wq →L[ℂ] Wp)) (Bd : ℝ) (dn : ℕ → ℝ)
    (hdn : Tendsto dn atTop (𝓝 0))
    (hx : ∀ e, JC.CCCoefM (T.bs j) (P5.Auser P0 N + 1) (P5.mmUser P0 N) ε₀ (x e) ∧
      B.CCle (P5.Auser P0 N + 1) (P5.mmUser P0 N) (x e) Bd)
    (hy : ∀ e, JC.CCCoefM (T.bs j) (P5.Auser P0 N + 1) (P5.mmUser P0 N) ε₀ (y e) ∧
      B.CCle (P5.Auser P0 N + 1) (P5.mmUser P0 N) (y e) Bd)
    (hxn : ∀ n e, JC.CCCoefM (T.bs j) (P5.Auser P0 N + 1) (P5.mmUser P0 N) ε₀ (xn n e) ∧
      B.CCle (P5.Auser P0 N + 1) (P5.mmUser P0 N) (xn n e) Bd)
    (hyn : ∀ n e, JC.CCCoefM (T.bs j) (P5.Auser P0 N + 1) (P5.mmUser P0 N) ε₀ (yn n e) ∧
      B.CCle (P5.Auser P0 N + 1) (P5.mmUser P0 N) (yn n e) Bd)
    (hdx : ∀ n e, JC.CCCoefM (T.bs j) (P5.Auser P0 N + 1) (P5.mmUser P0 N) ε₀ (xn n e - x e) ∧
      B.CCle (P5.Auser P0 N + 1) (P5.mmUser P0 N) (xn n e - x e) (dn n))
    (hdy : ∀ n e, JC.CCCoefM (T.bs j) (P5.Auser P0 N + 1) (P5.mmUser P0 N) ε₀ (yn n e - y e) ∧
      B.CCle (P5.Auser P0 N + 1) (P5.mmUser P0 N) (yn n e - y e) (dn n)) :
    Tendsto (fun n => D.formLev T s j w (xn n) (yn n)) atTop (𝓝 (D.formLev T s j w x y)) := by
  have hAu : P5.Auser P0 w.length + 1 ≤ P5.Auser P0 N + 1 := by linarith [auser_mono P0 hw]
  have hmu : P5.mmUser P0 w.length ≤ P5.mmUser P0 N := mmUser_mono P0 hw
  have hS := formLev_sesquilinear_finiteReg hΞ Wp Wq P0 T s j w (P5.Auser P0 N + 1) (P5.mmUser P0 N) ε₀ hε₀ hAu hmu
  obtain ⟨Cf, hCf0, hCf⟩ := formLev_norm_le hΞ P0 T s j w (P5.Auser P0 N + 1 + 1) (by linarith)
  have hmm5 : 5 + (2 * (P0.r - (j : ℕ)) + P0.k + 1) * w.length ≤ P5.mmUser P0 N := by
    have := Formalism.FourierDecayAlt.P.JCx2.pd_thr_mm P0 j N (P5.mmUser P0 N) le_rfl
    have h2 : (2 * (P0.r - (j : ℕ)) + P0.k + 1) * w.length ≤ (2 * (P0.r - (j : ℕ)) + P0.k + 1) * N :=
      Nat.mul_le_mul_left _ hw
    omega
  have h5 : 5 ≤ P5.mmUser P0 N := by unfold P5.mmUser; omega
  have hu : ∀ (u : Wd.Ix (Fin w.length) → B.Mat P0.k (P0.r - j) → (Wq →L[ℂ] Wp)) (cu : ℝ),
      (∀ e, B.CCle (P5.Auser P0 N + 1) (P5.mmUser P0 N) (u e) cu) →
      ∀ e, B.CCle (P5.Auser P0 N + 1 + 1 - 1) (5 + (2 * (P0.r - (j : ℕ)) + P0.k + 1) * w.length) (u e) cu := by
    intro u cu h e
    exact Formalism.FourierDecayAlt.P.BetaSesquilinearity.CCle_mono_A (by linarith) (Formalism.FourierDecayAlt.P.BetaSesquilinearity.CCle_mono_m hmm5 (h e))
  have hv : ∀ (u : Wd.Ix (Fin w.length) → B.Mat P0.k (P0.r - j) → (Wq →L[ℂ] Wp)) (cu : ℝ),
      (∀ e, B.CCle (P5.Auser P0 N + 1) (P5.mmUser P0 N) (u e) cu) →
      ∀ e, B.CCle (P5.Auser P0 N + 1 + 1 - 1 - 2 * (w.length : ℝ)) 5 (u e) cu := by
    intro u cu h e
    have hw0 : (0 : ℝ) ≤ w.length := Nat.cast_nonneg _
    exact Formalism.FourierDecayAlt.P.BetaSesquilinearity.CCle_mono_A (by linarith) (Formalism.FourierDecayAlt.P.BetaSesquilinearity.CCle_mono_m h5 (h e))
  have key : ∀ n, D.formLev T s j w (xn n) (yn n) - D.formLev T s j w x y =
      D.formLev T s j w (xn n - x) (yn n) + D.formLev T s j w x (yn n - y) := by
    intro n
    have e1 : xn n = x + (1 : ℂ) • (xn n - x) := by simp
    have e2 : yn n = y + (1 : ℂ) • (yn n - y) := by simp
    have s1 := (hS x (xn n - x) (yn n) 1 (fun e => (hx e).1) (fun e => (hdx n e).1) (fun e => (hyn n e).1)).1
    have s2 := (hS y (yn n - y) x 1 (fun e => (hy e).1) (fun e => (hdy n e).1) (fun e => (hx e).1)).2
    rw [← e1] at s1
    rw [← e2] at s2
    rw [s1, s2]
    simp
    ring
  have hbd : ∀ n, ‖D.formLev T s j w (xn n) (yn n) - D.formLev T s j w x y‖ ≤ 2 * Cf * Bd * dn n := by
    intro n
    rw [key n]
    have b1 := hCf (xn n - x) (yn n) (dn n) Bd (hu _ _ fun e => (hdx n e).2) (hv _ _ fun e => (hyn n e).2)
    have b2 := hCf x (yn n - y) Bd (dn n) (hu _ _ fun e => (hx e).2) (hv _ _ fun e => (hdy n e).2)
    calc _ ≤ ‖D.formLev T s j w (xn n - x) (yn n)‖ + ‖D.formLev T s j w x (yn n - y)‖ := norm_add_le _ _
      _ ≤ Cf * dn n * Bd + Cf * Bd * dn n := add_le_add b1 b2
      _ = 2 * Cf * Bd * dn n := by ring
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hlim : Tendsto (fun n => 2 * Cf * Bd * dn n) atTop (𝓝 0) := by
    simpa using hdn.const_mul (2 * Cf * Bd)
  exact squeeze_zero (fun n => norm_nonneg _) hbd hlim

theorem levelForm_cutoff_tendsto_below (hΞ : B.XiExists) : ∃ Cl : ℝ, 0 ≤ Cl ∧ ∀ Cc : ℝ, Cl ≤ Cc →
    ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq)
    (f : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (χ : ℝ → ℝ) (ε A : ℝ) (N : ℕ) (cut : ℕ → B.Mat P.k P.r → ℂ),
    C6.IsCut0 χ → 0 < ε → B.CkOn ⊤ (B.GV P.k P.r) f → (∀ m : ℕ, B.InCC A m f) →
    Cc * ((P.r : ℝ) + 1) ^ 4 * ((N : ℝ) * (2 * (P.r : ℝ) + P.k + 1) ^ 2 + (2 * (P.r : ℝ) + P.k + 1) ^ 3) ≤ A →
    (∀ n g, cut n g = ((Real.smoothTransition
      ((4 - ∑ i, ∑ j, Complex.normSq ((((n : ℝ) + 1)⁻¹ • g) i j)) / 3) : ℝ) : ℂ)) →
    ∀ i, i ≤ P.r → ∀ w : List C.Letter, w.length ≤ N → ∀ a b,
      Tendsto (fun n => p.RR (fun g => cut n g • D.cutF p.T.base χ f ε g) i w a b) atTop
        (𝓝 (p.RR (D.cutF p.T.base χ f ε) i w a b)) := by
  obtain ⟨Cs, hCs0, hSQ⟩ := sliceQ
  refine ⟨Cs + 1, by positivity, ?_⟩
  intro Cc hCc Wp Wq _ _ _ _ _ _ P p f χ ε A N cut hχ hε hf hfA hA hcut i hi w hw a b
  have hk2 : 2 ≤ P.k := p.hl.2.2
  set X : ℝ := (N : ℝ) * (2 * (P.r : ℝ) + P.k + 1) ^ 2 + (2 * (P.r : ℝ) + P.k + 1) ^ 3 with hX
  have hX1 : 1 ≤ X := by
    have h1 : (1 : ℝ) ≤ 2 * (P.r : ℝ) + P.k + 1 := by
      have : (0 : ℝ) ≤ P.r := Nat.cast_nonneg _
      have : (0 : ℝ) ≤ P.k := Nat.cast_nonneg _
      linarith
    have : 1 ≤ (2 * (P.r : ℝ) + P.k + 1) ^ 3 := one_le_pow₀ h1
    have : 0 ≤ (N : ℝ) * (2 * (P.r : ℝ) + P.k + 1) ^ 2 := by positivity
    linarith
  have hR4 : 1 ≤ ((P.r : ℝ) + 1) ^ 4 := one_le_pow₀ (by have : (0 : ℝ) ≤ P.r := Nat.cast_nonneg _; linarith)
  have hA' : Cs * ((P.r : ℝ) + 1) ^ 4 * X ≤ A - 1 := by
    have h1 : (Cs + 1) * ((P.r : ℝ) + 1) ^ 4 * X ≤ A :=
      le_trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hCc (by positivity)) (by positivity)) hA
    have h2 : 1 ≤ ((P.r : ℝ) + 1) ^ 4 * X := by nlinarith
    nlinarith
  set M := 3 * (11 * (N * (2 * P.r + P.k + 1) ^ 2 + (2 * P.r + P.k + 1) ^ 3) + 5) with hM
  obtain ⟨bf, hbf⟩ := hfA M
  have hbf0 : 0 ≤ bf := JCx2.pd_ccle_nonneg hbf
  have hbf' : B.CCle (A - 1) M f bf := BetaSesquilinearity.CCle_mono_A (by linarith) hbf
  obtain ⟨Kp, hKp0, hKp⟩ := JCx2.pd_cut_ccle (k := P.k) (r := P.r) (E := Wq →L[ℂ] Wp) M
  have hψ : ∀ n : ℕ, B.CCle (A - 1) M (fun g => JCx2.pdPsi ((n : ℝ) + 1) g • f g) (Kp * bf / ((n : ℝ) + 1)) :=
    fun n => hKp _ (by positivity) A f bf hbf
  have hψs : ∀ n : ℕ, B.CkOn ⊤ (B.GV P.k P.r) (fun g => JCx2.pdPsi ((n : ℝ) + 1) g • f g) :=
    fun n => JCx2.pd_smooth_smul (JCx2.pd_psi_cd _) hf
  set hn : ℕ → B.Mat P.k P.r → (Wq →L[ℂ] Wp) := fun n g => cut n g • f g with hhn
  have hneq : ∀ n, hn n = fun g => f g + (-1 : ℂ) • (JCx2.pdPsi ((n : ℝ) + 1) g • f g) := by
    intro n; funext g
    simp only [hhn, cut_eq cut hcut n g, sub_smul, one_smul]
    simp [sub_eq_add_neg]
  have hnC : ∀ n, B.CCle (A - 1) M (hn n) (bf + Kp * bf) := by
    intro n
    rw [hneq n]
    refine JCx2.pd_ccle_mono_c (BetaSesquilinearity.CCle_add hbf' (BetaSesquilinearity.CCle_smul (-1) (hψ n))) ?_
    have h1 : Kp * bf / ((n : ℝ) + 1) ≤ Kp * bf := div_le_self (by positivity) (by
      have : (0 : ℝ) ≤ n := Nat.cast_nonneg n; linarith)
    simp only [norm_neg, norm_one, one_mul]
    linarith
  have hns : ∀ n, B.CkOn ⊤ (B.GV P.k P.r) (hn n) := by
    intro n
    rw [hneq n]
    exact BetaSesquilinearity.CkOn_add hf (BetaSesquilinearity.CkOn_smul (-1) (hψs n))
  have hsub : ∀ n, (fun g => f g - hn n g) = fun g => JCx2.pdPsi ((n : ℝ) + 1) g • f g := by
    intro n; funext g
    rw [hneq n]; simp
  have hFn : ∀ n, (fun g => cut n g • D.cutF p.T.base χ f ε g) = D.cutF p.T.base χ (hn n) ε := by
    intro n; funext g
    simp only [D.cutF, hhn]
    rw [smul_comm]
  simp only [KB.Pl.RR, hFn]
  unfold D.RRplace
  by_cases hab : D.IsLocPt a i ∧ D.IsLocPt b i
  swap
  · simp only [dif_neg hab]; exact tendsto_const_nhds
  simp only [dif_pos hab, dif_pos hi]
  have hca : P.r - i = P.r - D.ptSize a := by simp [hab.1.2]
  have hcb : P.r - i = P.r - D.ptSize b := by simp [hab.2.2]
  have hQa := fun e => hSQ Cs le_rfl P.k P.r Wp Wq p.T χ (A - 1) N P rfl rfl hk2 hχ hA' ε hε i hi w hw a hca hab.1 e
  have hQb := fun e => hSQ Cs le_rfl P.k P.r Wp Wq p.T χ (A - 1) N P rfl rfl hk2 hχ hA' ε hε i hi w hw b hcb hab.2 e
  choose εa Ka hεa hKa hQ1a hQ2a using hQa
  choose εb Kb hεb hKb hQ1b hQ2b using hQb
  set S : ℝ := ∑ e, (εa e)⁻¹ + ∑ e, (εb e)⁻¹ with hS
  have hSa : ∀ e, (εa e)⁻¹ ≤ S := by
    intro e
    have h1 : (εa e)⁻¹ ≤ ∑ e, (εa e)⁻¹ :=
      Finset.single_le_sum (f := fun e => (εa e)⁻¹) (fun e _ => (inv_pos.2 (hεa e)).le) (Finset.mem_univ e)
    have h2 : 0 ≤ ∑ e, (εb e)⁻¹ := Finset.sum_nonneg fun e _ => (inv_pos.2 (hεb e)).le
    linarith
  have hSb : ∀ e, (εb e)⁻¹ ≤ S := by
    intro e
    have h1 : (εb e)⁻¹ ≤ ∑ e, (εb e)⁻¹ :=
      Finset.single_le_sum (f := fun e => (εb e)⁻¹) (fun e _ => (inv_pos.2 (hεb e)).le) (Finset.mem_univ e)
    have h2 : 0 ≤ ∑ e, (εa e)⁻¹ := Finset.sum_nonneg fun e _ => (inv_pos.2 (hεa e)).le
    linarith
  have hS0 : 0 < S := lt_of_lt_of_le (inv_pos.2 (hεa Wd.e1)) (hSa Wd.e1)
  have hε₀a : ∀ e, S⁻¹ ≤ εa e := fun e => by
    have := inv_anti₀ (inv_pos.2 (hεa e)) (hSa e); rwa [inv_inv] at this
  have hε₀b : ∀ e, S⁻¹ ≤ εb e := fun e => by
    have := inv_anti₀ (inv_pos.2 (hεb e)) (hSb e); rwa [inv_inv] at this
  set KK : ℝ := ∑ e, Ka e + ∑ e, Kb e with hKK
  have hKa' : ∀ e, Ka e ≤ KK := by
    intro e
    have h1 : Ka e ≤ ∑ e, Ka e := Finset.single_le_sum (f := Ka) (fun e _ => hKa e) (Finset.mem_univ e)
    have h2 : 0 ≤ ∑ e, Kb e := Finset.sum_nonneg fun e _ => hKb e
    linarith
  have hKb' : ∀ e, Kb e ≤ KK := by
    intro e
    have h1 : Kb e ≤ ∑ e, Kb e := Finset.single_le_sum (f := Kb) (fun e _ => hKb e) (Finset.mem_univ e)
    have h2 : 0 ≤ ∑ e, Ka e := Finset.sum_nonneg fun e _ => hKa e
    linarith
  have hKK0 : 0 ≤ KK := le_trans (hKa Wd.e1) (hKa' Wd.e1)
  have hB1 : bf ≤ bf + Kp * bf := by nlinarith

  have main : ∀ (q : C.LPt) (hcq : P.r - i = P.r - D.ptSize q) (εq Kq : Wd.Ix (Fin w.length) → ℝ),
      (∀ e, S⁻¹ ≤ εq e) → (∀ e, 0 ≤ Kq e) → (∀ e, Kq e ≤ KK) →
      (∀ e (h : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (c : ℝ), B.CkOn ⊤ (B.GV P.k P.r) h → B.CCle (A - 1) M h c →
        JC.CCCoefM (p.T.bs i) (P5.Auser P N + 1) (P5.mmUser P N) (εq e) (xs p.T χ ε i hi w q hcq h e) ∧
        B.CCle (P5.Auser P N + 1) (P5.mmUser P N) (xs p.T χ ε i hi w q hcq h e) (Kq e * c)) →
      (∀ e (h₁ h₂ : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (c₁ c₂ : ℝ), B.CkOn ⊤ (B.GV P.k P.r) h₁ →
        B.CkOn ⊤ (B.GV P.k P.r) h₂ → B.CCle (A - 1) M h₁ c₁ → B.CCle (A - 1) M h₂ c₂ →
        ∀ γ ∈ B.GV P.k (P.r - i), xs p.T χ ε i hi w q hcq h₁ e γ - xs p.T χ ε i hi w q hcq h₂ e γ =
          xs p.T χ ε i hi w q hcq (fun g => h₁ g - h₂ g) e γ) →
      (∀ e, JC.CCCoefM (p.T.bs i) (P5.Auser P N + 1) (P5.mmUser P N) S⁻¹ (xs p.T χ ε i hi w q hcq f e) ∧
        B.CCle (P5.Auser P N + 1) (P5.mmUser P N) (xs p.T χ ε i hi w q hcq f e) (KK * (bf + Kp * bf))) ∧
      (∀ n e, JC.CCCoefM (p.T.bs i) (P5.Auser P N + 1) (P5.mmUser P N) S⁻¹ (xs p.T χ ε i hi w q hcq (hn n) e) ∧
        B.CCle (P5.Auser P N + 1) (P5.mmUser P N) (xs p.T χ ε i hi w q hcq (hn n) e) (KK * (bf + Kp * bf))) ∧
      (∀ n e, JC.CCCoefM (p.T.bs i) (P5.Auser P N + 1) (P5.mmUser P N) S⁻¹
          (xs p.T χ ε i hi w q hcq (hn n) e - xs p.T χ ε i hi w q hcq f e) ∧
        B.CCle (P5.Auser P N + 1) (P5.mmUser P N)
          (xs p.T χ ε i hi w q hcq (hn n) e - xs p.T χ ε i hi w q hcq f e) (KK * (Kp * bf / ((n : ℝ) + 1)))) := by
    intro q hcq εq Kq hεq hKq hKq' hQ1 hQ2
    refine ⟨fun e => ?_, fun n e => ?_, fun n e => ?_⟩
    · obtain ⟨h1, h2⟩ := hQ1 e f bf hf hbf'
      exact ⟨cccoef_mono h1 (hεq e), JCx2.pd_ccle_mono_c h2 (mul_le_mul (hKq' e) hB1 hbf0 hKK0)⟩
    · obtain ⟨h1, h2⟩ := hQ1 e (hn n) _ (hns n) (hnC n)
      exact ⟨cccoef_mono h1 (hεq e), JCx2.pd_ccle_mono_c h2 (mul_le_mul_of_nonneg_right (hKq' e) (by positivity))⟩
    · obtain ⟨h1, h2⟩ := hQ1 e _ _ (hψs n) (hψ n)
      have hd : ∀ γ ∈ B.GV P.k (P.r - i), (fun γ => (-1 : ℂ) • xs p.T χ ε i hi w q hcq
          (fun g => JCx2.pdPsi ((n : ℝ) + 1) g • f g) e γ) γ =
          (xs p.T χ ε i hi w q hcq (hn n) e - xs p.T χ ε i hi w q hcq f e) γ := by
        intro γ hγ
        have := hQ2 e f (hn n) bf _ hf (hns n) hbf' (hnC n) γ hγ
        rw [hsub n] at this
        simp only [Pi.sub_apply, ← this]
        simp
      have hC2 := Formalism.FourierDecayAlt.P.Ux1.cc_congr hd (BetaSesquilinearity.CCle_smul (-1) h2)
      simp only [norm_neg, norm_one, one_mul] at hC2
      have hC3 := JCx2.pd_ccle_mono_c hC2 (mul_le_mul_of_nonneg_right (hKq' e) (by positivity))
      refine ⟨⟨hC3.1, ⟨_, hC3⟩, fun γ hγ hne => ?_⟩, hC3⟩
      rw [← hd γ hγ] at hne
      have hne' : xs p.T χ ε i hi w q hcq (fun g => JCx2.pdPsi ((n : ℝ) + 1) g • f g) e γ ≠ 0 := by
        intro h0; apply hne; simp [h0]
      exact (hεq e).trans (h1.2.2 γ hγ hne')
  obtain ⟨ma1, ma2, ma3⟩ := main a hca εa Ka hε₀a hKa hKa' hQ1a hQ2a
  obtain ⟨mb1, mb2, mb3⟩ := main b hcb εb Kb hε₀b hKb hKb' hQ1b hQ2b
  have hdn : Tendsto (fun n : ℕ => KK * (Kp * bf / ((n : ℝ) + 1))) atTop (𝓝 0) := by
    have h1 : Tendsto (fun n : ℕ => ((n : ℝ) + 1)⁻¹) atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat.congr
      (fun n => by simp)
    have := (h1.const_mul (Kp * bf)).const_mul KK
    simpa [div_eq_mul_inv, mul_assoc] using this
  exact formLev_tendsto hΞ P p.T _ ⟨i, by omega⟩ w N hw S⁻¹ (inv_pos.2 hS0)
    (xs p.T χ ε i hi w a hca f) (xs p.T χ ε i hi w b hcb f)
    (fun n => xs p.T χ ε i hi w a hca (hn n)) (fun n => xs p.T χ ε i hi w b hcb (hn n))
    (KK * (bf + Kp * bf)) (fun n => KK * (Kp * bf / ((n : ℝ) + 1))) hdn ma1 mb1 ma2 mb2 ma3 mb3

theorem levelForm_cutoff_tendsto (hΞ : B.XiExists) : Formalism.FourierDecayAlt.KB.FormLimit := by
  intro Cb
  obtain ⟨Cl, _, hL⟩ := levelForm_cutoff_tendsto_below hΞ
  obtain ⟨Ct, hT⟩ := PBE.formLimit_top Cb
  refine ⟨max Cl Ct, ?_⟩
  intro Wp Wq _ _ _ _ _ _ P0 p f χ ε A N cut hDD hχ hε hf hfA hA hcut
  refine ⟨fun n => PBE.cutCpt P0 p.T.base f χ ε cut hχ hε hf hcut n, ?_⟩
  intro i w hwc hw a b
  have hX : 0 ≤ ((P0.r : ℝ) + 1) ^ 4 * ((N : ℝ) * (2 * (P0.r : ℝ) + P0.k + 1) ^ 2 + (2 * (P0.r : ℝ) + P0.k + 1) ^ 3) := by
    positivity
  rcases lt_trichotomy i (P0.r + 1) with hlt | heq | hgt
  · exact hL (max Cl Ct) (le_max_left _ _) Wp Wq P0 p f χ ε A N cut hχ hε hf hfA hA hcut i (by omega) w hw a b
  · subst heq
    refine hT Wp Wq P0 p f χ ε A N cut hDD hχ hε hf hfA ?_ hcut w hwc hw a b
    refine le_trans ?_ hA
    have := mul_le_mul_of_nonneg_right (le_max_right Cl Ct) hX
    nlinarith
  · have h0 : ∀ F, p.RR F i w a b = 0 := by
      intro F
      unfold KB.Pl.RR D.RRplace
      split_ifs <;> first | rfl | (exfalso; omega)
    simp only [h0]
    exact tendsto_const_nhds

end limit

end GlobalTheory.GivenXi

end
