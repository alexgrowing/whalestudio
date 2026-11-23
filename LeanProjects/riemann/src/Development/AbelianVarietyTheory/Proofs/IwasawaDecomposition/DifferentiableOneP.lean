import Mathlib
import Formalism.LocalToGlobal.BesselHermitianTheta.AllTied
import Formalism.LocalToGlobal.IndefiniteReal.DatumVec
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.AdelicDataRowMeasureScaleTrivialTuple
import Development.AbelianVarietyTheory.Counterexamples.HeightSurvey.ConjAtFixedIff

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.Mem.Th MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct ContDiff

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.AutSpace

variable {D : D7} (θ : InfF D) (V : HSp D)

def SmFun : Submodule ℂ (GA D V → ℂ) where
  carrier := {φ | ∀ (k : ℕ) (τs : Fin k → D.what₂.Tau) (Xs : Fin k → Matrix (Fin V.rank) (Fin V.rank) ℂ),
    (∀ i, Xs i ∈ lieAt V (τs i)) → ∀ g,
      ContDiff ℝ ∞ fun t : Fin k → ℝ => φ (g * (List.ofFn fun i => oneP θ V (τs i) (Xs i) (t i)).prod)}
  add_mem' := fun ha hb k τs Xs h g => (ha k τs Xs h g).add (hb k τs Xs h g)
  zero_mem' := fun _ _ _ _ _ => contDiff_const
  smul_mem' := fun c _ ha k τs Xs h g => (ha k τs Xs h g).const_smul c

variable {θ V}

theorem differentiable_oneP {φ : GA D V → ℂ} (hφ : φ ∈ SmFun θ V) {τ : D.what₂.Tau}
    {X : Matrix (Fin V.rank) (Fin V.rank) ℂ} (hX : X ∈ lieAt V τ) (g : GA D V) :
    Differentiable ℝ fun t : ℝ => φ (g * oneP θ V τ X t) := by
  have h := hφ 1 (fun _ => τ) (fun _ => X) (fun _ => hX) g
  have h2 : ContDiff ℝ ∞ fun t : ℝ => (fun _ : Fin 1 => t) := contDiff_pi.2 fun _ => contDiff_id
  have h3 := (h.comp h2).differentiable (by simp)
  simpa [Function.comp_def] using h3

theorem Rder_add {φ ψ : GA D V → ℂ} (hφ : φ ∈ SmFun θ V) (hψ : ψ ∈ SmFun θ V) {τ : D.what₂.Tau}
    {X : Matrix (Fin V.rank) (Fin V.rank) ℂ} (hX : X ∈ lieAt V τ) :
    Rder θ V τ X (φ + ψ) = Rder θ V τ X φ + Rder θ V τ X ψ := by
  funext g
  exact deriv_fun_add (differentiable_oneP hφ hX g 0) (differentiable_oneP hψ hX g 0)

theorem Rder_smul (c : ℂ) (φ : GA D V → ℂ) (τ : D.what₂.Tau) (X : Matrix (Fin V.rank) (Fin V.rank) ℂ) :
    Rder θ V τ X (c • φ) = c • Rder θ V τ X φ := by
  funext g
  exact deriv_const_mul_field c

theorem Rder_mem {φ : GA D V → ℂ} (hφ : φ ∈ SmFun θ V) {τ : D.what₂.Tau}
    {X : Matrix (Fin V.rank) (Fin V.rank) ℂ} (hX : X ∈ lieAt V τ) : Rder θ V τ X φ ∈ SmFun θ V := by
  intro k τs Xs h g
  have h1 := hφ (k + 1) (Fin.snoc (α := fun _ => D.what₂.Tau) τs τ)
    (Fin.snoc (α := fun _ => Matrix (Fin V.rank) (Fin V.rank) ℂ) Xs X)
    (fun i => by
      refine Fin.lastCases ?_ (fun j => ?_) i
      · simpa using hX
      · simpa using h j) g
  have h2 : ContDiff ℝ ∞ fun p : (Fin k → ℝ) × ℝ => (Fin.snoc (α := fun _ => ℝ) p.1 p.2 : Fin (k + 1) → ℝ) := by
    refine contDiff_pi.2 fun i => ?_
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simpa using contDiff_snd
    · simp only [Fin.snoc_castSucc]
      fun_prop
  have h3 : ContDiff ℝ ∞ (Function.uncurry fun (t : Fin k → ℝ) (s : ℝ) =>
      φ (g * (List.ofFn fun i => oneP θ V (τs i) (Xs i) (t i)).prod * oneP θ V τ X s)) := by
    convert h1.comp h2 using 1
    funext p
    simp [Function.uncurry, List.ofFn_succ', mul_assoc, -List.ofFn_succ]
  have h4 := ContDiff.fderiv (n := ∞) h3 (contDiff_const (c := (0 : ℝ))) (by simp)
  exact h4.clm_apply (contDiff_const (c := (1 : ℝ)))

variable (θ V) in

structure LinOnSm (T : (GA D V → ℂ) → (GA D V → ℂ)) : Prop where
  mem : ∀ φ ∈ SmFun θ V, T φ ∈ SmFun θ V
  add : ∀ φ ∈ SmFun θ V, ∀ ψ ∈ SmFun θ V, T (φ + ψ) = T φ + T ψ
  smul : ∀ (c : ℂ) φ, T (c • φ) = c • T φ

theorem linOnSm_Rder {τ : D.what₂.Tau} {X : Matrix (Fin V.rank) (Fin V.rank) ℂ} (hX : X ∈ lieAt V τ) :
    LinOnSm θ V (Rder θ V τ X) :=
  ⟨fun _ h => Rder_mem h hX, fun _ h _ h' => Rder_add h h' hX, fun c φ => Rder_smul c φ τ X⟩

theorem linOnSm_RderC (τ : D.what₂.Tau) (Z : Matrix (Fin V.rank) (Fin V.rank) ℂ) : LinOnSm θ V (RderC θ V τ Z) := by
  obtain ⟨h1, h2⟩ := GlobalTheory.SmoothAutCheck.parts_mem V τ Z
  refine ⟨fun φ h => ?_, fun φ h ψ h' => ?_, fun c φ => ?_⟩
  · exact add_mem (Rder_mem h h1) (Submodule.smul_mem _ _ (Rder_mem h h2))
  · simp only [RderC]
    rw [Rder_add h h' h1, Rder_add h h' h2, smul_add Complex.I, add_add_add_comm]
  · simp only [RderC]
    rw [Rder_smul, Rder_smul, smul_add c, smul_comm c Complex.I]

theorem linOnSm_foldr {α : Type} (T : α → (GA D V → ℂ) → (GA D V → ℂ)) (l : List α)
    (hl : ∀ a ∈ l, LinOnSm θ V (T a)) : LinOnSm θ V fun φ => l.foldr (fun a f => T a f) φ := by
  induction l with
  | nil => exact ⟨fun _ h => h, fun _ _ _ _ => rfl, fun _ _ => rfl⟩
  | cons a l ih =>
    have h1 := hl a (by simp)
    have h2 := ih fun b hb => hl b (by simp [hb])
    refine ⟨fun φ h => h1.mem _ (h2.mem φ h), fun φ h ψ h' => ?_, fun c φ => ?_⟩
    · simp only [List.foldr_cons]
      rw [h2.add φ h ψ h', h1.add _ (h2.mem φ h) _ (h2.mem ψ h')]
    · simp only [List.foldr_cons]
      rw [h2.smul, h1.smul]

theorem linOnSm_gelf (τ : D.what₂.Tau) (k : ℕ) : LinOnSm θ V (gelf θ V τ k) := by
  have h : ∀ idx : Fin (k + 1) → Fin V.rank, LinOnSm θ V fun φ =>
      (List.ofFn fun a : Fin (k + 1) => RderC θ V τ (Matrix.single (idx a) (idx (a + 1)) 1)).foldr
        (fun f acc => f acc) φ := fun idx =>
    linOnSm_foldr (fun f => f) _ fun f hf => by
      obtain ⟨a, rfl⟩ := List.mem_ofFn.1 hf
      exact linOnSm_RderC τ _
  refine ⟨fun φ hφ => Submodule.sum_mem _ fun idx _ => (h idx).mem φ hφ, fun φ hφ ψ hψ => ?_, fun c φ => ?_⟩
  · simp only [gelf]
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun idx _ => (h idx).add φ hφ ψ hψ
  · simp only [gelf]
    rw [Finset.smul_sum]
    exact Finset.sum_congr rfl fun idx _ => (h idx).smul c φ

theorem one_le_sum_norm {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℂ) (h : A * B = 1) (i : Fin n) :
    1 ≤ ∑ a, ∑ b, (‖A a b‖ + ‖B a b‖) := by
  set S := ∑ a, ∑ b, (‖A a b‖ + ‖B a b‖) with hS
  have hS0 : 0 ≤ S := by positivity
  have hle : ∀ a b, ‖A a b‖ + ‖B a b‖ ≤ S := fun a b =>
    (Finset.single_le_sum (f := fun b => ‖A a b‖ + ‖B a b‖) (fun _ _ => by positivity) (Finset.mem_univ b)).trans
      (Finset.single_le_sum (f := fun a => ∑ b, (‖A a b‖ + ‖B a b‖)) (fun _ _ => by positivity) (Finset.mem_univ a))
  have hrow : ∑ b, ‖A i b‖ ≤ S :=
    (Finset.sum_le_sum fun b _ => le_add_of_nonneg_right (norm_nonneg (B i b))).trans
      (Finset.single_le_sum (f := fun a => ∑ b, (‖A a b‖ + ‖B a b‖)) (fun _ _ => by positivity) (Finset.mem_univ i))
  have h1 : (1 : ℝ) ≤ S * S := by
    have e : (1 : ℂ) = ∑ b, A i b * B b i := by rw [← Matrix.mul_apply, h, Matrix.one_apply_eq]
    calc (1 : ℝ) = ‖∑ b, A i b * B b i‖ := by rw [← e, norm_one]
      _ ≤ ∑ b, ‖A i b‖ * S := (norm_sum_le _ _).trans (Finset.sum_le_sum fun b _ => by
          rw [norm_mul]
          exact mul_le_mul_of_nonneg_left ((le_add_of_nonneg_left (norm_nonneg (A b i))).trans (hle b i))
            (norm_nonneg _))
      _ ≤ S * S := by rw [← Finset.sum_mul]; exact mul_le_mul_of_nonneg_right hrow hS0
  nlinarith

variable (θ V) in
theorem infMat_mul_inv (τ : D.what₂.Tau) (g : GA D V) :
    infMat D.sp.cm.sig V.gram (θ τ) g * infMat D.sp.cm.sig V.gram (θ τ) g⁻¹ = 1 := by
  have e : ∀ h : GA D V, infMat D.sp.cm.sig V.gram (θ τ) h = (infHom V h).1.map (θ τ) := fun _ => rfl
  rw [e, e, ← Matrix.map_mul, ← Units.val_mul, ← map_mul, mul_inv_cancel, map_one, Units.val_one,
    Matrix.map_one _ (map_zero _) (map_one _)]

variable (θ V) in

theorem normInf_dichotomy : (∀ g, normInf θ V g = 0) ∨ ∀ g, 1 ≤ normInf θ V g := by
  by_cases h : Nonempty D.what₂.Tau ∧ Nonempty (Fin V.rank)
  · obtain ⟨⟨τ⟩, ⟨i⟩⟩ := h
    refine Or.inr fun g => (one_le_sum_norm _ _ (infMat_mul_inv θ V τ g) i).trans ?_
    exact Finset.single_le_sum (f := fun τ => ∑ i, ∑ j, (‖infMat D.sp.cm.sig V.gram (θ τ) g i j‖ +
      ‖infMat D.sp.cm.sig V.gram (θ τ) g⁻¹ i j‖)) (fun _ _ => by positivity) (Finset.mem_univ τ)
  · refine Or.inl fun g => Finset.sum_eq_zero fun τ _ => Finset.sum_eq_zero fun i _ => ?_
    exact (h ⟨⟨τ⟩, ⟨i⟩⟩).elim

variable (θ V) in
theorem exists_pow_ge (a b : ℕ) :
    ∃ N : ℕ, ∀ g, normInf θ V g ^ a ≤ normInf θ V g ^ N ∧ normInf θ V g ^ b ≤ normInf θ V g ^ N := by
  rcases normInf_dichotomy θ V with h | h
  · refine ⟨0, fun g => ?_⟩
    rw [h g, pow_zero]
    exact ⟨pow_le_one₀ le_rfl zero_le_one, pow_le_one₀ le_rfl zero_le_one⟩
  · exact ⟨max a b, fun g => ⟨pow_le_pow_right₀ (h g) (le_max_left _ _), pow_le_pow_right₀ (h g) (le_max_right _ _)⟩⟩

theorem normInf_nonneg (g : GA D V) : 0 ≤ normInf θ V g := by
  unfold normInf
  positivity

theorem isAutFunSm_smul (c : ℂ) {φ : GA D V → ℂ} (h : IsAutFunSm θ V φ) : IsAutFunSm θ V (c • φ) := by
  refine ⟨⟨fun γ hγ g => ?_, ?_, h.cont.const_smul c⟩, (SmFun θ V).smul_mem c h.smooth, ?_, ?_⟩
  · simp only [Pi.smul_apply, h.left γ hγ g]
  · obtain ⟨U, hU, hk⟩ := h.level
    exact ⟨U, hU, fun k h1 h2 g => by simp only [Pi.smul_apply, hk k h1 h2 g]⟩
  · obtain ⟨W, hW, h1, h2⟩ := h.zfin
    exact ⟨W, hW, W.smul_mem c h1, h2⟩
  · obtain ⟨N, hN⟩ := h.growth
    refine ⟨N, fun l hl x => ?_⟩
    obtain ⟨C, hC⟩ := hN l hl x
    refine ⟨‖c‖ * C, fun g hg => ?_⟩
    have := (linOnSm_foldr (θ := θ) (fun p : D.what₂.Tau × Matrix (Fin V.rank) (Fin V.rank) ℂ => Rder θ V p.1 p.2) l
      fun p hp => linOnSm_Rder (hl p hp)).smul c φ
    rw [this, Pi.smul_apply, norm_smul, mul_assoc]
    exact mul_le_mul_of_nonneg_left (hC g hg) (norm_nonneg c)

variable (θ V) in
theorem isAutFunSm_zero : IsAutFunSm θ V 0 := by
  refine ⟨⟨fun _ _ _ => rfl, ⟨⊤, isOpen_univ, fun _ _ _ _ => rfl⟩, continuous_const⟩, (SmFun θ V).zero_mem,
    ⟨⊥, inferInstance, zero_mem _, fun τ k f hf => ?_⟩, ⟨0, fun l hl x => ⟨0, fun g _ => ?_⟩⟩⟩
  · have := (linOnSm_gelf (θ := θ) (V := V) τ k).smul 0 f
    rw [(Submodule.mem_bot ℂ).1 hf, zero_smul, zero_smul] at this
    rw [(Submodule.mem_bot ℂ).1 hf, this]
    exact zero_mem _
  · have := (linOnSm_foldr (θ := θ) (fun p : D.what₂.Tau × Matrix (Fin V.rank) (Fin V.rank) ℂ => Rder θ V p.1 p.2) l
      fun p hp => linOnSm_Rder (hl p hp)).smul 0 0
    rw [zero_smul, zero_smul] at this
    rw [this]
    simp

theorem isAutFunSm_add {φ ψ : GA D V → ℂ} (h : IsAutFunSm θ V φ) (h' : IsAutFunSm θ V ψ) :
    IsAutFunSm θ V (φ + ψ) := by
  refine ⟨⟨fun γ hγ g => ?_, ?_, h.cont.add h'.cont⟩, (SmFun θ V).add_mem h.smooth h'.smooth, ?_, ?_⟩
  · simp only [Pi.add_apply, h.left γ hγ g, h'.left γ hγ g]
  · obtain ⟨U, hU, hk⟩ := h.level
    obtain ⟨U', hU', hk'⟩ := h'.level
    exact ⟨U ⊓ U', hU.inter hU', fun k h1 h2 g => by simp only [Pi.add_apply, hk k h1.1 h2 g, hk' k h1.2 h2 g]⟩
  · obtain ⟨W, hW, h1, h2⟩ := h.zfin
    obtain ⟨W', hW', h1', h2'⟩ := h'.zfin
    refine ⟨(W ⊓ SmFun θ V) ⊔ (W' ⊓ SmFun θ V), inferInstance,
      Submodule.add_mem_sup ⟨h1, h.smooth⟩ ⟨h1', h'.smooth⟩, fun τ k f hf => ?_⟩
    obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.1 hf
    have hg := linOnSm_gelf (θ := θ) (V := V) τ k
    rw [hg.add a ha.2 b hb.2]
    exact Submodule.add_mem_sup ⟨h2 τ k a ha.1, hg.mem a ha.2⟩ ⟨h2' τ k b hb.1, hg.mem b hb.2⟩
  · obtain ⟨N, hN⟩ := h.growth
    obtain ⟨N', hN'⟩ := h'.growth
    obtain ⟨M, hM⟩ := exists_pow_ge θ V N N'
    refine ⟨M, fun l hl x => ?_⟩
    obtain ⟨C, hC⟩ := hN l hl x
    obtain ⟨C', hC'⟩ := hN' l hl x
    refine ⟨|C| + |C'|, fun g hg => ?_⟩
    have := (linOnSm_foldr (θ := θ) (fun p : D.what₂.Tau × Matrix (Fin V.rank) (Fin V.rank) ℂ => Rder θ V p.1 p.2) l
      fun p hp => linOnSm_Rder (hl p hp)).add φ h.smooth ψ h'.smooth
    rw [this, Pi.add_apply, add_mul]
    have h0 := normInf_nonneg (θ := θ) g
    refine (norm_add_le _ _).trans (add_le_add ((hC g hg).trans ?_) ((hC' g hg).trans ?_))
    · exact mul_le_mul (le_abs_self _) (hM g).1 (pow_nonneg h0 _) (abs_nonneg _)
    · exact mul_le_mul (le_abs_self _) (hM g).2 (pow_nonneg h0 _) (abs_nonneg _)

theorem mem_AFs_iff : ∀ (D : D7) (θ : InfF D), IsInfFam θ → ∀ (V : HSp D) (φ : GA D V → ℂ),
    φ ∈ AFs θ V ↔ IsAutFunSm θ V φ := by
  intro D θ _ V φ
  refine ⟨fun h => ?_, fun h => Submodule.subset_span h⟩
  induction h using Submodule.span_induction with
  | mem x hx => exact hx
  | zero => exact isAutFunSm_zero θ V
  | add x y _ _ hx hy => exact isAutFunSm_add hx hy
  | smul c x _ hx => exact isAutFunSm_smul c hx

end GlobalTheory.Mem.AutSpace

end
