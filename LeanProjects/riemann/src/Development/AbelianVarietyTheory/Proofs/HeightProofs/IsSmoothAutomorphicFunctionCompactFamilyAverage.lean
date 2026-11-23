import Mathlib
import Formalism.LocalToGlobal.BesselHermitianTheta.AllTied
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NormDwLeSobNorm
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DifferentiableOneP
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsSmoothAutomorphicFunctionTranslateAtRealPlace
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousOnAtTau
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RderMemAutFormsCuspForms
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.GrowthSizeRWordNeTopOfLe
import Development.AbelianVarietyTheory.Proofs.HeightProofs.CompactAverageSmoothFamilyClosedUnderDerivativesStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta MeasureTheory Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.RealAverage

open GlobalTheory.Mem.AutSpace GlobalTheory.PointAtPlaceHom GlobalTheory.Mem.RealTranslate

variable {D : D7} {θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)} {V : HSp D} {τ : D.what₂.Tau}
  {K : Type} [TopologicalSpace K] {κ : K → Matrix (Fin V.rank) (Fin V.rank) ℂ}

theorem continuous_atTau (hθ : IsInfFam θ) (hκ : Continuous κ) (hU : ∀ k, κ k ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ)) :
    Continuous fun k => atTau θ V τ (κ k) :=
  (continuousOn_atTau hθ V τ).comp_continuous hκ hU

theorem continuous_infMat_atTau (hθ : IsInfFam θ) (hκ : Continuous κ) (hU : ∀ k, κ k ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ))
    (τ' : D.what₂.Tau) : Continuous fun k => infMat D.sp.cm.sig V.gram (θ τ') (atTau θ V τ (κ k)) := by
  by_cases c : τ' = τ
  · subst c
    exact hκ.congr fun k => ((atTau_spec hθ V τ' (hU k)).2.1).symm
  · exact continuous_const.congr fun k => ((atTau_spec hθ V τ (hU k)).2.2 τ' c).symm

theorem continuous_infMat_atTau_inv (hθ : IsInfFam θ) (hκ : Continuous κ)
    (hU : ∀ k, κ k ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ)) (τ' : D.what₂.Tau) :
    Continuous fun k => infMat D.sp.cm.sig V.gram (θ τ') (atTau θ V τ (κ k))⁻¹ := by
  by_cases c : τ' = τ
  · subst c
    have c1 : Continuous fun k => (gramAt D V τ')⁻¹ * (κ k)ᴴ * gramAt D V τ' :=
      (continuous_const.matrix_mul hκ.matrix_conjTranspose).matrix_mul continuous_const
    exact c1.congr fun k => ((isAtTau_inv V τ' (hU k) (atTau_spec hθ V τ' (hU k))).2.1).symm
  · exact continuous_const.congr fun k => ((isAtTau_inv V τ (hU k) (atTau_spec hθ V τ (hU k))).2.2 τ' c).symm

theorem continuous_normInf_atTau (hθ : IsInfFam θ) (hκ : Continuous κ)
    (hU : ∀ k, κ k ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ)) : Continuous fun k => normInf θ V (atTau θ V τ (κ k)) := by
  unfold normInf
  refine continuous_finset_sum _ fun τ' _ => continuous_finset_sum _ fun i _ => continuous_finset_sum _ fun j _ => ?_
  exact (((continuous_infMat_atTau hθ hκ hU τ').matrix_elem i j).norm).add
    (((continuous_infMat_atTau_inv hθ hκ hU τ').matrix_elem i j).norm)

theorem continuous_adAt_atTau (hθ : IsInfFam θ) (hκ : Continuous κ)
    (hU : ∀ k, κ k ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ)) (τ' : D.what₂.Tau) (X : Matrix (Fin V.rank) (Fin V.rank) ℂ) :
    Continuous fun k => adAt θ (atTau θ V τ (κ k)) τ' X :=
  ((continuous_infMat_atTau_inv hθ hκ hU τ').matrix_mul continuous_const).matrix_mul
    (continuous_infMat_atTau hθ hκ hU τ')

variable (θ V τ κ) in

def famSpan (𝒟 : Set (GA D V → ℂ)) : Submodule ℂ (K → GA D V → ℂ) :=
  Submodule.span ℂ {F | ∃ c : K → ℂ, Continuous c ∧ ∃ ψ ∈ 𝒟, F = fun k x => c k * ψ (x * atTau θ V τ (κ k))}

section Fam

variable {𝒟 : Set (GA D V → ℂ)} (hθ : IsInfFam θ) (hκ : Continuous κ)
  (hU : ∀ k, κ k ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ)) (h𝒟 : ∀ ψ ∈ 𝒟, IsAutFunSm θ V ψ)
include hθ hκ hU h𝒟

theorem famSpan_cont : ∀ F ∈ famSpan θ V τ κ 𝒟, Continuous fun p : K × GA D V => F p.1 p.2 := by
  haveI : IsTopologicalGroup (GA D V) := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.topGroupHA _ _
  intro F hF
  induction hF using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨c, hc, ψ, hψ, rfl⟩ := hx
    exact (hc.comp continuous_fst).mul
      ((h𝒟 ψ hψ).cont.comp (continuous_snd.mul ((continuous_atTau hθ hκ hU).comp continuous_fst)))
  | zero => exact continuous_const
  | add x y _ _ hx hy => exact hx.add hy
  | smul a x _ hx => exact continuous_const.mul hx

omit hκ in
theorem famSpan_sm : ∀ F ∈ famSpan θ V τ κ 𝒟, ∀ k, F k ∈ SmFun θ V := by
  intro F hF
  induction hF using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨c, hc, ψ, hψ, rfl⟩ := hx
    intro k
    exact (SmFun θ V).smul_mem (c k) (rTr_mem hθ (isRealPt_atTau hθ τ (hU k)) (h𝒟 ψ hψ).smooth)
  | zero => exact fun _ => zero_mem _
  | add x y _ _ hx hy => exact fun k => add_mem (hx k) (hy k)
  | smul a x _ hx => exact fun k => (SmFun θ V).smul_mem a (hx k)

end Fam

section Der

variable {𝒟 : Set (GA D V → ℂ)} (hθ : IsInfFam θ) (hκ : Continuous κ)
  (hU : ∀ k, κ k ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ)) (h𝒟 : ∀ ψ ∈ 𝒟, IsAutFunSm θ V ψ)
  (hR : ∀ ψ ∈ 𝒟, ∀ τ' X, X ∈ lieAt V τ' → Rder θ V τ' X ψ ∈ 𝒟)
include hθ hκ hU h𝒟 hR

theorem famSpan_Rder_gen {c : K → ℂ} (hc : Continuous c) {ψ : GA D V → ℂ} (hψ : ψ ∈ 𝒟) (τ' : D.what₂.Tau)
    {X : Matrix (Fin V.rank) (Fin V.rank) ℂ} (hX : X ∈ lieAt V τ') :
    (fun k => Rder θ V τ' X (fun x => c k * ψ (x * atTau θ V τ (κ k)))) ∈ famSpan θ V τ κ 𝒟 := by
  set Z : Fin V.rank × Fin V.rank → Matrix (Fin V.rank) (Fin V.rank) ℂ := fun a => Matrix.single a.1 a.2 1
  set X1 := fun a => (1 / 2 : ℂ) • (Z a + conjAt V τ' (Z a))
  set X2 := fun a => (1 / (2 * Complex.I) : ℂ) • (Z a - conjAt V τ' (Z a))
  set Y := fun k => adAt θ (atTau θ V τ (κ k)) τ' X
  have e : (fun k => Rder θ V τ' X (fun x => c k * ψ (x * atTau θ V τ (κ k)))) =
      ∑ a : Fin V.rank × Fin V.rank, ((fun k x => (c k * Y k a.1 a.2) * Rder θ V τ' (X1 a) ψ (x * atTau θ V τ (κ k))) +
        (fun k x => (c k * Y k a.1 a.2 * Complex.I) * Rder θ V τ' (X2 a) ψ (x * atTau θ V τ (κ k)))) := by
    funext k
    have hh := isRealPt_atTau hθ τ (hU k)
    have hsm : ψ ∈ SmFun θ V := (h𝒟 ψ hψ).smooth
    rw [show (fun x => c k * ψ (x * atTau θ V τ (κ k))) = c k • rTr V (atTau θ V τ (κ k)) ψ from rfl, Rder_smul,
      Rder_rTr hθ hh hX, GlobalTheory.Size.Rder_eq_sum_glDer hθ hsm (adAt_mem hh hX)]
    funext x
    simp only [Pi.smul_apply, rTr, Finset.sum_apply, smul_eq_mul, GlobalTheory.Size.glDer, RderC, Pi.add_apply,
      Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    simp only [Y, X1, X2, Z]
    ring
  rw [e]
  have cY : ∀ a : Fin V.rank × Fin V.rank, Continuous fun k => c k * Y k a.1 a.2 := fun a =>
    hc.mul ((continuous_adAt_atTau hθ hκ hU τ' X).matrix_elem a.1 a.2)
  refine Submodule.sum_mem _ fun a _ => add_mem (Submodule.subset_span ⟨_, cY a, _, hR ψ hψ τ' _ ?_, rfl⟩)
    (Submodule.subset_span ⟨_, (cY a).mul continuous_const, _, hR ψ hψ τ' _ ?_, rfl⟩)
  · exact (GlobalTheory.SmoothAutCheck.parts_mem V τ' (Z a)).1
  · exact (GlobalTheory.SmoothAutCheck.parts_mem V τ' (Z a)).2

theorem famSpan_Rder : ∀ F ∈ famSpan θ V τ κ 𝒟, ∀ τ', ∀ X ∈ lieAt V τ',
    (fun k => Rder θ V τ' X (F k)) ∈ famSpan θ V τ κ 𝒟 := by
  intro F hF τ' X hX
  induction hF using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨c, hc, ψ, hψ, rfl⟩ := hx
    exact famSpan_Rder_gen hθ hκ hU h𝒟 hR hc hψ τ' hX
  | zero =>
    have e : (fun k => Rder θ V τ' X ((0 : K → GA D V → ℂ) k)) = 0 := by
      funext k g
      simp [Rder]
    rw [e]
    exact zero_mem _
  | add x y hx' hy' hx hy =>
    have sx := famSpan_sm hθ hU h𝒟 x hx'
    have sy := famSpan_sm hθ hU h𝒟 y hy'
    have e : (fun k => Rder θ V τ' X ((x + y) k)) = (fun k => Rder θ V τ' X (x k)) + fun k => Rder θ V τ' X (y k) := by
      funext k
      exact Rder_add (sx k) (sy k) hX
    rw [e]
    exact add_mem hx hy
  | smul a x _ hx =>
    have e : (fun k => Rder θ V τ' X ((a • x) k)) = a • fun k => Rder θ V τ' X (x k) := by
      funext k
      exact Rder_smul a (x k) τ' X
    rw [e]
    exact Submodule.smul_mem _ a hx

end Der

variable (θ V) in

def growN (N : ℕ) : Set (GA D V → ℂ) :=
  {ψ | IsAutFunSm θ V ψ ∧ ∀ l : List (D.what₂.Tau × Matrix (Fin V.rank) (Fin V.rank) ℂ), (∀ p ∈ l, p.2 ∈ lieAt V p.1) →
    ∀ x, ∃ C, ∀ g ∈ GinfC V, ‖l.foldr (fun p f => Rder θ V p.1 p.2 f) ψ (x * g)‖ ≤ C * normInf θ V g ^ N}

theorem growN_Rder (hθ : IsInfFam θ) (N : ℕ) :
    ∀ ψ ∈ growN θ V N, ∀ τ' X, X ∈ lieAt V τ' → Rder θ V τ' X ψ ∈ growN θ V N := by
  intro ψ hψ τ' X hX
  refine ⟨GlobalTheory.CuspLie.isAutFunSm_Rder hθ hX hψ.1, fun l hl x => ?_⟩
  have := hψ.2 (l ++ [(τ', X)]) (fun p hp => ?_) x
  · simpa only [List.foldr_append, List.foldr_cons, List.foldr_nil] using this
  · rcases List.mem_append.1 hp with h | h
    · exact hl p h
    · rw [List.mem_singleton.1 h]; exact hX

theorem famSpan_growth [CompactSpace K] (hθ : IsInfFam θ) (hκ : Continuous κ)
    (hU : ∀ k, κ k ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ)) (N : ℕ) :
    ∀ F ∈ famSpan θ V τ κ (growN θ V N), ∀ x, ∃ C, ∀ k, ∀ g ∈ GinfC V, ‖F k (x * g)‖ ≤ C * normInf θ V g ^ N := by
  intro F hF
  induction hF using Submodule.span_induction with
  | mem F hF =>
    obtain ⟨c, hc, ψ, hψ, rfl⟩ := hF
    intro x
    obtain ⟨C', hC'⟩ := hψ.2 [] (by simp) x
    set Mc := ‖(⟨c, hc⟩ : C(K, ℂ))‖
    set Mh := ‖(⟨_, continuous_normInf_atTau hθ hκ hU⟩ : C(K, ℝ))‖
    refine ⟨Mc * (|C'| * Mh ^ N), fun k g hg => ?_⟩
    have h1 : ‖c k‖ ≤ Mc := ContinuousMap.norm_coe_le_norm (⟨c, hc⟩ : C(K, ℂ)) k
    have h2 : normInf θ V (atTau θ V τ (κ k)) ≤ Mh := by
      have := ContinuousMap.norm_coe_le_norm (⟨_, continuous_normInf_atTau hθ hκ hU⟩ : C(K, ℝ)) k
      exact (le_abs_self _).trans (by simpa only [Real.norm_eq_abs, ContinuousMap.coe_mk] using this)
    have h3 := hC' (g * atTau θ V τ (κ k)) (mul_mem hg (atTau_mem (θ := θ) V τ (κ k)))
    simp only [List.foldr_nil] at h3
    have h4 : normInf θ V (g * atTau θ V τ (κ k)) ^ N ≤ (normInf θ V g * Mh) ^ N :=
      pow_le_pow_left₀ (normInf_nonneg _)
        (((GlobalTheory.T.normInf_submultiplicative_le_adelicHeight D θ V).1 _ _).trans (mul_le_mul_of_nonneg_left h2 (normInf_nonneg _))) N
    have h5 : ‖ψ (x * g * atTau θ V τ (κ k))‖ ≤ |C'| * (Mh ^ N * normInf θ V g ^ N) := by
      rw [mul_assoc x]
      refine h3.trans (mul_le_mul (le_abs_self _) ?_ (pow_nonneg (normInf_nonneg _) _) (abs_nonneg _))
      rw [← mul_pow, mul_comm Mh]
      exact h4
    calc ‖c k * ψ (x * g * atTau θ V τ (κ k))‖ = ‖c k‖ * ‖ψ (x * g * atTau θ V τ (κ k))‖ := norm_mul _ _
      _ ≤ Mc * (|C'| * (Mh ^ N * normInf θ V g ^ N)) := mul_le_mul h1 h5 (norm_nonneg _) ((norm_nonneg _).trans h1)
      _ = Mc * (|C'| * Mh ^ N) * normInf θ V g ^ N := by ring
  | zero => exact fun x => ⟨0, fun k g _ => by simp⟩
  | add F G _ _ hF hG =>
    intro x
    obtain ⟨C1, hC1⟩ := hF x
    obtain ⟨C2, hC2⟩ := hG x
    refine ⟨|C1| + |C2|, fun k g hg => ?_⟩
    have h0 := pow_nonneg (normInf_nonneg (θ := θ) g) N
    rw [add_mul]
    exact (norm_add_le _ _).trans (add_le_add ((hC1 k g hg).trans (mul_le_mul_of_nonneg_right (le_abs_self _) h0))
      ((hC2 k g hg).trans (mul_le_mul_of_nonneg_right (le_abs_self _) h0)))
  | smul a F _ hF =>
    intro x
    obtain ⟨C, hC⟩ := hF x
    refine ⟨‖a‖ * C, fun k g hg => ?_⟩
    rw [Pi.smul_apply, Pi.smul_apply, norm_smul, mul_assoc]
    exact mul_le_mul_of_nonneg_left (hC k g hg) (norm_nonneg a)

theorem famSpan_words {𝒟 : Set (GA D V → ℂ)} (hθ : IsInfFam θ) (hκ : Continuous κ)
    (hU : ∀ k, κ k ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ)) (h𝒟 : ∀ ψ ∈ 𝒟, IsAutFunSm θ V ψ)
    (hR : ∀ ψ ∈ 𝒟, ∀ τ' X, X ∈ lieAt V τ' → Rder θ V τ' X ψ ∈ 𝒟) {F : K → GA D V → ℂ}
    (hF : F ∈ famSpan θ V τ κ 𝒟) (l : List (D.what₂.Tau × Matrix (Fin V.rank) (Fin V.rank) ℂ))
    (hl : ∀ p ∈ l, p.2 ∈ lieAt V p.1) :
    (fun k => l.foldr (fun p f => Rder θ V p.1 p.2 f) (F k)) ∈ famSpan θ V τ κ 𝒟 := by
  induction l with
  | nil => exact hF
  | cons p l ih =>
    exact famSpan_Rder hθ hκ hU h𝒟 hR _ (ih fun q hq => hl q (List.mem_cons_of_mem _ hq)) p.1 p.2
      (hl p List.mem_cons_self)

theorem isAutFunSm_RderC (hθ : IsInfFam θ) (τ' : D.what₂.Tau) (Z : Matrix (Fin V.rank) (Fin V.rank) ℂ)
    {ψ : GA D V → ℂ} (h : IsAutFunSm θ V ψ) : IsAutFunSm θ V (RderC θ V τ' Z ψ) := by
  obtain ⟨h1, h2⟩ := GlobalTheory.SmoothAutCheck.parts_mem V τ' Z
  exact isAutFunSm_add (GlobalTheory.CuspLie.isAutFunSm_Rder hθ h1 h) (isAutFunSm_smul _ (GlobalTheory.CuspLie.isAutFunSm_Rder hθ h2 h))

theorem isAutFunSm_gelf (hθ : IsInfFam θ) (τ' : D.what₂.Tau) (j : ℕ) {ψ : GA D V → ℂ} (h : IsAutFunSm θ V ψ) :
    IsAutFunSm θ V (gelf θ V τ' j ψ) := by
  have key : ∀ l : List ((GA D V → ℂ) → GA D V → ℂ), (∀ f ∈ l, ∀ ψ, IsAutFunSm θ V ψ → IsAutFunSm θ V (f ψ)) →
      IsAutFunSm θ V (l.foldr (fun f acc => f acc) ψ) := by
    intro l hl
    induction l with
    | nil => exact h
    | cons f l ih =>
      exact hl f List.mem_cons_self _ (ih fun g hg => hl g (List.mem_cons_of_mem _ hg))
  unfold gelf
  refine (mem_AFs_iff D θ hθ V _).1 (Submodule.sum_mem _ fun idx _ => (mem_AFs_iff D θ hθ V _).2 (key _ ?_))
  intro f hf
  obtain ⟨a, rfl⟩ := List.mem_ofFn.1 hf
  exact fun ψ hψ => isAutFunSm_RderC hθ τ' _ hψ

theorem integrable_avg [CompactSpace K] [MeasurableSpace K] [BorelSpace K] (μ : Measure K) [IsFiniteMeasure μ]
    (hθ : IsInfFam θ) (hκ : Continuous κ) (hU : ∀ k, κ k ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ)) {e : K → ℂ}
    (he : Continuous e) {ψ : GA D V → ℂ} (hψ : Continuous ψ) (x : GA D V) :
    Integrable (fun k => e k * ψ (x * atTau θ V τ (κ k))) μ := by
  haveI : IsTopologicalGroup (GA D V) := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.topGroupHA _ _
  exact (he.mul (hψ.comp (continuous_const.mul (continuous_atTau hθ hκ hU)))).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

theorem isAutFunSm_average : ∀ (D : D7) (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)), IsInfFam (D := D) θ →
    ∀ (V : HSp D) (τ : D.what₂.Tau) (K : Type) [TopologicalSpace K] [CompactSpace K] [MeasurableSpace K] [BorelSpace K]
    (μ : Measure K) [IsFiniteMeasure μ] (κ : K → Matrix (Fin V.rank) (Fin V.rank) ℂ), Continuous κ →
    (∀ k, κ k ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ)) → ∀ e : K → ℂ, Continuous e → ∀ φ : GA D V → ℂ, IsAutFunSm θ V φ →
    IsAutFunSm θ V (fun x => ∫ k, e k * φ (x * atTau θ V τ (κ k)) ∂μ) := by
  intro D θ hθ V τ K _ _ _ _ μ _ κ hκ hU e he φ hφ
  set 𝒟 : Set (GA D V → ℂ) := {ψ | IsAutFunSm θ V ψ}
  have h𝒟 : ∀ ψ ∈ 𝒟, IsAutFunSm θ V ψ := fun _ h => h
  have hR : ∀ ψ ∈ 𝒟, ∀ τ' X, X ∈ lieAt V τ' → Rder θ V τ' X ψ ∈ 𝒟 :=
    fun _ h _ _ hX => GlobalTheory.CuspLie.isAutFunSm_Rder hθ hX h
  have FAM := fun ψ (h : IsAutFunSm θ V ψ) => GlobalTheory.T.compactAverage_smoothFamily_closedUnderDerivatives D θ hθ V K μ (famSpan θ V τ κ 𝒟)
    (famSpan_cont hθ hκ hU h𝒟) (famSpan_sm hθ hU h𝒟) (famSpan_Rder hθ hκ hU h𝒟 hR)
    (fun k x => e k * ψ (x * atTau θ V τ (κ k))) (Submodule.subset_span ⟨e, he, ψ, h, rfl⟩)
  have F0 := FAM φ hφ
  refine { left := fun γ hγ g => ?_, level := ?_, cont := F0.1, smooth := F0.2.1, zfin := ?_, growth := ?_ }
  · show ∫ k, e k * φ (γ * g * atTau θ V τ (κ k)) ∂μ = ∫ k, e k * φ (g * atTau θ V τ (κ k)) ∂μ
    congr 1
    funext k
    rw [mul_assoc, hφ.left γ hγ]
  · obtain ⟨U, hUo, hk⟩ := hφ.level
    refine ⟨U, hUo, fun u hu hf g => ?_⟩
    show ∫ k, e k * φ (g * u * atTau θ V τ (κ k)) ∂μ = ∫ k, e k * φ (g * atTau θ V τ (κ k)) ∂μ
    congr 1
    funext k
    rw [mul_assoc, ← comm_of_mem V (atTau_mem (θ := θ) V τ (κ k)) hf, ← mul_assoc, hk u hu hf]
  · obtain ⟨W, hWf, hm, hs⟩ := hφ.zfin
    let A : GlobalTheory.Mem.Th.AFs θ V →ₗ[ℂ] (GA D V → ℂ) :=
      { toFun := fun ψ x => ∫ k, e k * ψ.1 (x * atTau θ V τ (κ k)) ∂μ
        map_add' := fun ψ ψ' => by
          funext x
          have c1 := ((mem_AFs_iff D θ hθ V _).1 ψ.2).cont
          have c2 := ((mem_AFs_iff D θ hθ V _).1 ψ'.2).cont
          simp only [Submodule.coe_add, Pi.add_apply, mul_add]
          exact integral_add (integrable_avg μ hθ hκ hU he c1 x) (integrable_avg μ hθ hκ hU he c2 x)
        map_smul' := fun c ψ => by
          funext x
          simp only [Submodule.coe_smul, Pi.smul_apply, smul_eq_mul, RingHom.id_apply, mul_left_comm _ c]
          exact integral_const_mul c _ }
    let Wa : Submodule ℂ (GlobalTheory.Mem.Th.AFs θ V) := W.comap (GlobalTheory.Mem.Th.AFs θ V).subtype
    haveI : FiniteDimensional ℂ Wa := Module.Finite.of_injective
      (((GlobalTheory.Mem.Th.AFs θ V).subtype.comp Wa.subtype).codRestrict W fun x => x.2)
      fun a b hab => by
        have h := congrArg (fun z : W => (z : GA D V → ℂ)) hab
        exact Subtype.val_injective (Subtype.val_injective h)
    refine ⟨Wa.map A, Module.Finite.map Wa A,
      Submodule.mem_map.2 ⟨⟨φ, (mem_AFs_iff D θ hθ V φ).2 hφ⟩, hm, rfl⟩, fun τ' j f hf => ?_⟩
    obtain ⟨ψ, hψ, rfl⟩ := Submodule.mem_map.1 hf
    have hψs := (mem_AFs_iff D θ hθ V _).1 ψ.2
    refine Submodule.mem_map.2 ⟨⟨gelf θ V τ' j ψ.1, (mem_AFs_iff D θ hθ V _).2 (isAutFunSm_gelf hθ τ' j hψs)⟩,
      hs τ' j _ hψ, ?_⟩
    have G := (FAM ψ.1 hψs).2.2.2 τ' j
    show (fun x => ∫ k, e k * gelf θ V τ' j ψ.1 (x * atTau θ V τ (κ k)) ∂μ) =
      gelf θ V τ' j (fun x => ∫ k, e k * ψ.1 (x * atTau θ V τ (κ k)) ∂μ)
    rw [G]
    funext x
    congr 1
    funext k
    have e1 : (fun x => e k * ψ.1 (x * atTau θ V τ (κ k))) = e k • rTr V (atTau θ V τ (κ k)) ψ.1 := rfl
    rw [e1, (linOnSm_gelf τ' j).smul, gelf_rTr hθ (isRealPt_atTau hθ τ (hU k)) τ' j hψs.smooth]
    rfl
  · obtain ⟨N, hN⟩ := hφ.growth
    have h𝒟N : ∀ ψ ∈ growN θ V N, IsAutFunSm θ V ψ := fun _ h => h.1
    have hRN := growN_Rder (V := V) hθ N
    have hF0 : (fun k x => e k * φ (x * atTau θ V τ (κ k))) ∈ famSpan θ V τ κ (growN θ V N) :=
      Submodule.subset_span ⟨e, he, φ, ⟨hφ, hN⟩, rfl⟩
    have FN := GlobalTheory.T.compactAverage_smoothFamily_closedUnderDerivatives D θ hθ V K μ (famSpan θ V τ κ (growN θ V N))
      (famSpan_cont hθ hκ hU h𝒟N) (famSpan_sm hθ hU h𝒟N) (famSpan_Rder hθ hκ hU h𝒟N hRN) _ hF0
    refine ⟨N, fun l hl x => ?_⟩
    rw [FN.2.2.1 l hl]
    obtain ⟨C, hC⟩ := famSpan_growth hθ hκ hU N _ (famSpan_words hθ hκ hU h𝒟N hRN hF0 l hl) x
    refine ⟨C * μ.real Set.univ, fun g hg => ?_⟩
    have := norm_integral_le_of_norm_le_const (μ := μ) (Filter.Eventually.of_forall fun k => hC k g hg)
    calc _ ≤ _ := this
      _ = _ := by ring

end GlobalTheory.RealAverage

end
