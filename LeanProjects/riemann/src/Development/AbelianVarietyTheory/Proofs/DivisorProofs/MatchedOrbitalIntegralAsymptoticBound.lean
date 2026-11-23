import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiffsZeroOfLev
import Development.AbelianVarietyTheory.Definitions.Divisors.RankEqCardIffExistsFrameMatrixFirstColumnBlock
import Development.AbelianVarietyTheory.Definitions.Divisors.PairsOfSquareTriple
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MatchedDiffsInvariantSubspace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DifferencesSpanIntertwinersStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaActionExists
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalMatchingExistsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PairHypPlaneSplitStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaLiftHypPlaneSplitStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MatchedTripleIsotropicTowerStepTen
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MeasureFundDomLtTopSmul
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConstantTermUnipotentIntegral
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicSchwartzFinitePureTensors
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPurelyImaginaryElement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsMulRightInvariantOfFundamentalDomain

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

open GlobalTheory.ThK.DescB
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.ThK.GlobLocal

section Abstract

variable {M A S Y : Type} [AddCommGroup M] [Module ℂ M] [AddCommGroup A] [Module ℂ A] [AddCommGroup S] [Module ℂ S]
  [AddCommGroup Y] [Module ℂ Y]

theorem exists_ne_of_span (N : Submodule ℂ M) (l : M → ℂ) (hadd : ∀ x ∈ N, ∀ y ∈ N, l (x + y) = l x + l y)
    (hsmul : ∀ (c : ℂ), ∀ x ∈ N, l x = 0 → l (c • x) = 0) {s : Set M} (hs : s ⊆ N) {f : M}
    (hf : f ∈ Submodule.span ℂ s) (h : l f ≠ 0) : ∃ x ∈ s, l x ≠ 0 := by
  by_contra hc
  push_neg at hc
  have hle : Submodule.span ℂ s ≤ N := Submodule.span_le.2 hs
  refine h ?_
  clear h
  induction hf using Submodule.span_induction with
  | mem x hx => exact hc x hx
  | zero =>
    have := hadd 0 N.zero_mem 0 N.zero_mem
    rw [add_zero] at this
    linear_combination -this
  | add x y hx hy h1 h2 => rw [hadd x (hle hx) y (hle hy), h1, h2, add_zero]
  | smul c x hx h1 => exact hsmul c x (hle hx) h1

theorem exists_form (N : Submodule ℂ M) (sch : Submodule ℂ A) (s : Submodule ℂ S) (t : Submodule ℂ Y) (L : M → A → ℂ)
    (add₁ : ∀ x ∈ N, ∀ y ∈ N, ∀ a ∈ sch, L (x + y) a = L x a + L y a)
    (smul₁ : ∀ (c : ℂ) x a, L (c • x) a = c * L x a)
    (add₂ : ∀ x ∈ N, ∀ a ∈ sch, ∀ b ∈ sch, L x (a + b) = L x a + L x b)
    (smul₂ : ∀ (c : ℂ) x a, L x (c • a) = starRingEnd ℂ c * L x a)
    (ι : S →ₗ[ℂ] Y) (hι : Set.BijOn ι (s : Set S) (t : Set Y)) (T : S →ₗ[ℂ] M) (hT : ∀ φ ∈ s, T φ ∈ N)
    (U : S →ₗ[ℂ] A) (hU : ∀ φ ∈ s, U φ ∈ sch) :
    ∃ Bf : t →ₗ[ℂ] t →ₗ⋆[ℂ] ℂ, ∀ φ ∈ s, ∀ φ' ∈ s, ∀ Ψ Ψ' : t, Ψ.1 = ι φ → Ψ'.1 = ι φ' → Bf Ψ Ψ' = L (T φ) (U φ') := by
  let ι₀ : s →ₗ[ℂ] t := ι.restrict fun x hx => hι.mapsTo hx
  have hb : Function.Bijective ι₀ := by
    refine ⟨fun x y h => Subtype.ext (hι.injOn x.2 y.2 (congrArg Subtype.val h)), fun y => ?_⟩
    obtain ⟨x, hx, e⟩ := hι.surjOn y.2
    exact ⟨⟨x, hx⟩, Subtype.ext e⟩
  let j : t ≃ₗ[ℂ] s := (LinearEquiv.ofBijective ι₀ hb).symm
  have hj : ∀ φ ∈ s, ∀ Ψ : t, Ψ.1 = ι φ → (j Ψ).1 = φ := fun φ hφ Ψ h => by
    have : j Ψ = ⟨φ, hφ⟩ := by
      rw [LinearEquiv.symm_apply_eq]
      exact Subtype.ext h
    rw [this]
  refine ⟨LinearMap.mk₂'ₛₗ (RingHom.id ℂ) (starRingEnd ℂ) (fun Ψ Ψ' => L (T (j Ψ).1) (U (j Ψ').1)) ?_ ?_ ?_ ?_, ?_⟩
  · intro x y z
    rw [map_add, Submodule.coe_add, map_add, add₁ _ (hT _ (j x).2) _ (hT _ (j y).2) _ (hU _ (j z).2)]
  · intro c x z
    rw [map_smul, Submodule.coe_smul, map_smul, smul₁]
    rfl
  · intro x y z
    rw [map_add, Submodule.coe_add, map_add, add₂ _ (hT _ (j x).2) _ (hU _ (j y).2) _ (hU _ (j z).2)]
  · intro c x z
    rw [map_smul, Submodule.coe_smul, map_smul, smul₂]
    rfl
  · intro φ hφ φ' hφ' Ψ Ψ' h h'
    rw [LinearMap.mk₂'ₛₗ_apply, hj φ hφ Ψ h, hj φ' hφ' Ψ' h']

end Abstract

section Analysis

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
  {n : ℕ} {J : Matrix (Fin n) (Fin n) E}

variable (σ J) in

def Dec : Submodule ℂ (UA σ J → ℂ) where
  carrier := {f | Continuous f ∧ (∀ γ ∈ ratU σ J, ∀ x, f (γ * x) = f x) ∧
    ∀ N : ℕ, ∃ C : ℝ, ∀ h, ‖f h‖ * (qht h : ℝ) ^ N ≤ C}
  zero_mem' := ⟨continuous_const, fun _ _ _ => rfl, fun _ => ⟨0, fun h => by simp⟩⟩
  add_mem' := by
    rintro f g ⟨c1, i1, d1⟩ ⟨c2, i2, d2⟩
    refine ⟨c1.add c2, fun γ hγ x => by simp only [Pi.add_apply, i1 γ hγ, i2 γ hγ], fun N => ?_⟩
    obtain ⟨C1, h1⟩ := d1 N
    obtain ⟨C2, h2⟩ := d2 N
    refine ⟨C1 + C2, fun h => ?_⟩
    calc ‖(f + g) h‖ * (qht h : ℝ) ^ N ≤ (‖f h‖ + ‖g h‖) * (qht h : ℝ) ^ N :=
          mul_le_mul_of_nonneg_right (norm_add_le _ _) (by positivity)
      _ ≤ C1 + C2 := by rw [add_mul]; exact add_le_add (h1 h) (h2 h)
  smul_mem' := by
    rintro c f ⟨c1, i1, d1⟩
    refine ⟨continuous_const.smul c1, fun γ hγ x => by simp only [Pi.smul_apply, i1 γ hγ], fun N => ?_⟩
    obtain ⟨C1, h1⟩ := d1 N
    refine ⟨‖c‖ * C1, fun h => ?_⟩
    rw [Pi.smul_apply, norm_smul, mul_assoc]
    exact mul_le_mul_of_nonneg_left (h1 h) (norm_nonneg _)

theorem qht_le_mul (h y : UA σ J) : qht h ≤ qht (h * y) * ht y⁻¹ := by
  rw [show qht (h * y) = ⨅ γ : ratU σ J, ht (γ.1 * (h * y)) from rfl, NNReal.iInf_mul]
  refine le_ciInf fun γ => ciInf_le_of_le (OrderBot.bddBelow _) γ ?_
  have e : γ.1 * h = γ.1 * (h * y) * y⁻¹ := by group
  rw [e]
  exact heightGL_mul_le F _ _

theorem shift_mem_Dec (y : UA σ J) {f : UA σ J → ℂ} (hf : f ∈ Dec σ J) : (fun h => f (h * y)) ∈ Dec σ J := by
  obtain ⟨c1, i1, d1⟩ := hf
  haveI := (GlobalTheory.UnipCT.topFacts σ J).1
  refine ⟨c1.comp (continuous_id.mul continuous_const), fun γ hγ x => by simp only [mul_assoc, i1 γ hγ], fun N => ?_⟩
  obtain ⟨C, hC⟩ := d1 N
  refine ⟨C * (ht y⁻¹ : ℝ) ^ N, fun h => ?_⟩
  have h1 : (qht h : ℝ) ≤ qht (h * y) * ht y⁻¹ := by exact_mod_cast qht_le_mul h y
  calc ‖f (h * y)‖ * (qht h : ℝ) ^ N ≤ ‖f (h * y)‖ * ((qht (h * y) : ℝ) * ht y⁻¹) ^ N :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) h1 N) (norm_nonneg _)
    _ = ‖f (h * y)‖ * (qht (h * y) : ℝ) ^ N * (ht y⁻¹ : ℝ) ^ N := by ring
    _ ≤ C * (ht y⁻¹ : ℝ) ^ N := mul_le_mul_of_nonneg_right (hC _) (by positivity)

theorem integrableOn_mul_conj {μ : Measure (UA σ J)} {𝓕 : Set (UA σ J)} (hfin : μ 𝓕 ≠ ⊤) {f k : UA σ J → ℂ}
    (hf : f ∈ Dec σ J) (kc : Continuous k) (ki : ∀ γ ∈ ratU σ J, ∀ x, k (γ * x) = k x)
    (kb : ∃ (C : ℝ) (m : ℕ), ∀ h, ‖k h‖ ≤ C * (ht h : ℝ) ^ m) :
    IntegrableOn (fun h => f h * starRingEnd ℂ (k h)) 𝓕 μ := by
  obtain ⟨C, m, hC⟩ := kb
  obtain ⟨Cf, hCf⟩ := hf.2.2 m
  haveI : IsFiniteMeasure (μ.restrict 𝓕) := isFiniteMeasure_restrict.2 hfin
  haveI : BorelSpace (UA σ J) := ⟨rfl⟩
  refine Integrable.mono' (integrable_const (max C 0 * Cf))
    (hf.1.mul (Complex.continuous_conj.comp kc)).aestronglyMeasurable (Eventually.of_forall fun h => ?_)
  rw [norm_mul, Complex.norm_conj]
  calc ‖f h‖ * ‖k h‖ ≤ ‖f h‖ * (max C 0 * (qht h : ℝ) ^ m) :=
        mul_le_mul_of_nonneg_left (GlobalTheory.ThKOrthVInt.norm_le_qht_of_le_ht ki hC h) (norm_nonneg _)
    _ = max C 0 * (‖f h‖ * (qht h : ℝ) ^ m) := by ring
    _ ≤ max C 0 * Cf := mul_le_mul_of_nonneg_left (hCf h) (le_max_right _ _)

theorem setIntegral_shift {μ : Measure (UA σ J)} [μ.IsHaarMeasure] {𝓕 : Set (UA σ J)}
    (h𝓕 : IsFundamentalDomain (ratU σ J) 𝓕 μ) (h0 : μ 𝓕 ≠ 0) (h1 : μ 𝓕 ≠ ⊤) {φ : UA σ J → ℂ}
    (hφ : ∀ γ ∈ ratU σ J, ∀ x, φ (γ * x) = φ x) (y : UA σ J) :
    ∫ h in 𝓕, φ (h * y) ∂μ = ∫ h in 𝓕, φ h ∂μ := by
  obtain ⟨i1, i2, i3, -⟩ := GlobalTheory.UnipCT.topFacts σ J
  haveI : BorelSpace (UA σ J) := ⟨rfl⟩
  haveI := GlobalTheory.UnitaryVol.countable_ratU σ J
  haveI := GlobalTheory.UnitU.isMulRightInvariant_of_fundamentalDomain (ratU σ J) μ h𝓕 h0 h1
  have hmp : MeasurePreserving (· * y⁻¹) μ μ := measurePreserving_mul_right μ y⁻¹
  have h2 : IsFundamentalDomain (ratU σ J) ((· * y⁻¹) ⁻¹' 𝓕) μ :=
    h𝓕.preimage_of_equiv hmp.quasiMeasurePreserving (e := id) Function.bijective_id fun γ x => by
      simp only [id, Subgroup.smul_def, smul_eq_mul, mul_assoc]
  have h3 := hmp.setIntegral_preimage_emb (MeasurableEquiv.mulRight y⁻¹).measurableEmbedding (fun h => φ (h * y)) 𝓕
  simp only [inv_mul_cancel_right] at h3
  rw [← h3]
  haveI : MeasurableConstSMul (ratU σ J) (UA σ J) :=
    ⟨fun γ => (continuous_const.mul continuous_id : Continuous fun x : UA σ J => γ.1 * x).measurable⟩
  haveI : SMulInvariantMeasure (ratU σ J) (UA σ J) μ := ⟨fun γ A _ => measure_preimage_mul μ γ.1 A⟩
  exact h2.setIntegral_eq h𝓕 fun γ x => hφ γ.1 γ.2 x

end Analysis

section Local

variable {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ]

def tensL (v : Pl F) (r : (κ → AF F) → ℂ) : ((κ → Fv F v) → ℂ) →ₗ[ℂ] ((κ → AF F) → ℂ) where
  toFun φ := tens (evFin F v) φ r
  map_add' φ φ' := funext fun x => by simp only [tens, Pi.add_apply]; ring
  map_smul' c φ := funext fun x => by simp only [tens, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; ring

theorem mem_span_tens (v : Pl F) {Ψ : (κ → AF F) → ℂ} (hΨ : Ψ ∈ schA F κ) :
    Ψ ∈ Submodule.span ℂ {Φ | ∃ r, (∀ φ ∈ SB (κ → Fv F v), Rest (evFin F v) φ r) ∧
      ∃ φ ∈ SB (κ → Fv F v), Φ = tens (evFin F v) φ r} := by
  classical
  obtain ⟨T, m, f, φ, hSB, hstd, rfl⟩ := GlobalTheory.SchADecomp.exists_sum_pure F κ Ψ hΨ
  refine Submodule.sum_mem _ fun i _ => Submodule.subset_span ?_
  have hc : ∀ᶠ w in cofinite, φ i w = Set.indicator {x | ∀ j, x j ∈ w.adicCompletionIntegers F} 1 :=
    T.eventually_cofinite_notMem.mono fun w hw => hstd i w hw
  obtain ⟨r, hr, e⟩ := GlobalTheory.PureFactor.exists_rest_factor v (f i) (φ i) hc
  refine ⟨r, fun ψ hψ => ⟨hr, ?_⟩, φ i v, hSB i v, by rw [e, Function.update_eq_self]⟩
  rw [e]
  refine GlobalTheory.TensUniq.pure_mem_schA _ _ (fun w => ?_) (GlobalTheory.PureFactor.update_eventually _ v ψ hc)
  by_cases hw : w = v
  · subst hw
    rw [Function.update_self]; exact hψ
  · rw [Function.update_of_ne hw]; exact hSB i w

end Local

section Maps

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
  {B : Base F E} {a a' : ℕ} {G : Geo σ a a'} {X : Chars F E} {om : Rep σ G.V G.W} {om' : Rep σ G.V' G.W}
  {R : RealMaps F a a'} {Rf : FinMaps F a a'}

variable (B G om) in

def mapVals (N : Submodule ℂ (UA σ G.W.J → ℂ)) : Set (UA σ G.W.J → ℂ) :=
  {F₀ | ∃ T : ((Fin a × Fin (a + a') → Fv F B.v₁) → ℂ) →ₗ[ℂ] (UA σ G.W.J → ℂ),
    (∀ φ ∈ SB (Fin a × Fin (a + a') → Fv F B.v₁), T φ ∈ N) ∧ augAt om B.v₁ ≤ LinearMap.ker T ∧
    (∀ y ∈ UAt σ G.W (evFin F B.v₁), ∀ φ ∈ SB (Fin a × Fin (a + a') → Fv F B.v₁),
      ∀ φ₁ ∈ SB (Fin a × Fin (a + a') → Fv F B.v₁),
      Acts (evFin F B.v₁) (om (1, y)) φ φ₁ → ∀ h, T φ₁ h = T φ (h * y)) ∧
    ∃ φ ∈ SB (Fin a × Fin (a + a') → Fv F B.v₁), F₀ = T φ}

variable (B G om' Rf) in

def piVals : Set (UA σ G.W.J → ℂ) :=
  {f | ∃ T : Rf.Pi B.v₁ →ₗ[ℂ] (UA σ G.W.J → ℂ),
    (∀ y ∈ UAt σ G.W (evFin F B.v₁), ∀ φ ∈ SB (Fin a' × Fin (a + a') → Fv F B.v₁),
      ∀ φ₁ ∈ SB (Fin a' × Fin (a + a') → Fv F B.v₁),
      Acts (evFin F B.v₁) (om' (1, y)) φ φ₁ → ∀ h, T (Rf.p' B.v₁ φ₁) h = T (Rf.p' B.v₁ φ) (h * y)) ∧ ∃ ξ, f = T ξ}

theorem diffs_le_piVals (hKP : KP) (hM : IsMatched B G X om om' R Rf) (c : ℂ) :
    Diffs B G X om om' R Rf c ≤ Submodule.span ℂ (piVals B G om' Rf) :=
  (GlobalTheory.T.differences_span_intertwiners hKP F E σ B a a' G X om om' R Rf hM c).trans
    (Submodule.span_mono fun _ ⟨T, _, h2, h3⟩ => ⟨T, h2, h3⟩)

theorem diff_mem_sup (hKP : KP) (hM : IsMatched B G X om om' R Rf) (c : ℂ) {Φ : Fn F a (a + a')} (hΦ : Φ ∈ PolData B G.M)
    {Φ' : Fn F a' (a + a')} (hΦ' : Φ' ∈ PolData B G.M' ⊓ G.M'.So B.ψ B.τ₁) :
    (fun h => G.M.I om Φ h - c * G.M'.I om' Φ' h) ∈ Diffs B G X om om' R Rf c ⊔ Diffs B G X om om' R Rf 0 := by
  obtain ⟨m1, m2, -⟩ := GlobalTheory.T.local_matching_exists hKP F E σ B a a' G X om om' R Rf hM
  obtain ⟨Φ₁', hS₁, hP₁⟩ := m1 Φ hΦ
  obtain ⟨Φ₂, hP₂⟩ := m2 Φ' hΦ'.1
  have e : (fun h => G.M.I om Φ h - c * G.M'.I om' Φ' h) = (fun h => G.M.I om Φ₂ h - c * G.M'.I om' Φ' h) +
      ((fun h => G.M.I om Φ h - 0 * G.M'.I om' Φ₁' h) - fun h => G.M.I om Φ₂ h - 0 * G.M'.I om' Φ' h) := by
    funext h
    simp only [Pi.add_apply, Pi.sub_apply]
    ring
  rw [e]
  exact Submodule.add_mem_sup (Submodule.subset_span ⟨Φ₂, Φ', hΦ'.2, hP₂, rfl⟩)
    (Submodule.sub_mem _ (Submodule.subset_span ⟨Φ, Φ₁', hS₁, hP₁, rfl⟩) (Submodule.subset_span ⟨Φ₂, Φ', hΦ'.2, hP₂, rfl⟩))

theorem mem_span_mapVals (hKP : KP) (hM : IsMatched B G X om om' R Rf) (N : Submodule ℂ (UA σ G.W.J → ℂ))
    (hN : ∀ y ∈ UAt σ G.W (evFin F B.v₁), ∀ F₀ ∈ N, (fun h => F₀ (h * y)) ∈ N) {f : UA σ G.W.J → ℂ}
    (hI : f ∈ Submodule.span ℂ (piVals B G om' Rf)) (hfN : f ∈ N) : f ∈ Submodule.span ℂ (mapVals B G om N) := by
  have hA := GlobalTheory.ThK.LocalOps.actsEx hKP.base
  have ex := (hA F E σ B _ _ _ _ G.M _ _ om _ _ _ _ (GlobalTheory.ThK.Inhab.pairV hM.triple) B.v₁).1
  have ex' := (hA F E σ B _ _ _ _ G.M' _ _ om' _ _ _ _ (GlobalTheory.ThK.Inhab.pairV' hM.triple) B.v₁).1
  have one_mem : ∀ {n : ℕ} (Y : Spc F E n), (1 : UA σ Y.J) ∈ UAt σ Y (evFin F B.v₁) := by
    intro n Y u _
    change u • ((1 : Matrix (Fin n) (Fin n) (AE F E)) - 1) = 0
    rw [sub_self, smul_zero]
  let ι := UAt σ G.W (evFin F B.v₁)
  let Rel : ι → Rf.Pi B.v₁ → Rf.Pi B.v₁ → Prop := fun y ξ ξ₁ =>
    ∃ φ ∈ SB (Fin a × Fin (a + a') → Fv F B.v₁), ∃ φ₁ ∈ SB (Fin a × Fin (a + a') → Fv F B.v₁),
      Acts (evFin F B.v₁) (om (1, y.1)) φ φ₁ ∧ Rf.p B.v₁ φ = ξ ∧ Rf.p B.v₁ φ₁ = ξ₁
  let ρ : ι → (UA σ G.W.J → ℂ) →ₗ[ℂ] (UA σ G.W.J → ℂ) := fun y => LinearMap.funLeft ℂ ℂ (· * y.1)
  have ρ_apply : ∀ y (F₀ : UA σ G.W.J → ℂ) h, ρ y F₀ h = F₀ (h * y.1) := fun _ _ _ => rfl
  have onto : ∀ ξ, ∃ φ ∈ SB (Fin a × Fin (a + a') → Fv F B.v₁), Rf.p B.v₁ φ = ξ := fun ξ => by
    have : ξ ∈ (SB _).map (Rf.p B.v₁) := by rw [hM.fin.onto B.v₁]; trivial
    exact Submodule.mem_map.1 this
  have onto' : ∀ ξ, ∃ φ ∈ SB (Fin a' × Fin (a + a') → Fv F B.v₁), Rf.p' B.v₁ φ = ξ := fun ξ => by
    have : ξ ∈ (SB _).map (Rf.p' B.v₁) := by rw [hM.fin.onto' B.v₁]; trivial
    exact Submodule.mem_map.1 this
  have tot : ∀ y ξ, ∃ ξ₁, Rel y ξ ξ₁ := by
    intro y ξ
    obtain ⟨φ, hφ, rfl⟩ := onto ξ
    obtain ⟨φ₁, hφ₁, hact⟩ := (ex 1 (one_mem G.V) y.1 y.2 φ hφ).exists
    exact ⟨_, φ, hφ, φ₁, hφ₁, hact, rfl, rfl⟩
  have irred : ∀ Q : Submodule ℂ (Rf.Pi B.v₁), (∀ y ξ ξ₁, Rel y ξ ξ₁ → ξ ∈ Q → ξ₁ ∈ Q) → Q = ⊥ ∨ Q = ⊤ :=
    fun Q hQ => hM.fin.irred B.v₁ Q fun h hh φ hφ φ₁ hφ₁ hact hmem =>
      hQ ⟨h, hh⟩ _ _ ⟨φ, hφ, φ₁, hφ₁, hact, rfl, rfl⟩ hmem
  have hN' : ∀ y, ∀ x ∈ N, ρ y x ∈ N := fun y x hx => hN y.1 y.2 x hx
  have transfer : ∀ T : Rf.Pi B.v₁ →ₗ[ℂ] (UA σ G.W.J → ℂ),
      (∀ y ∈ UAt σ G.W (evFin F B.v₁), ∀ φ ∈ SB (Fin a' × Fin (a + a') → Fv F B.v₁),
        ∀ φ₁ ∈ SB (Fin a' × Fin (a + a') → Fv F B.v₁),
        Acts (evFin F B.v₁) (om' (1, y)) φ φ₁ → ∀ h, T (Rf.p' B.v₁ φ₁) h = T (Rf.p' B.v₁ φ) (h * y)) →
      ∀ y ξ ξ₁, Rel y ξ ξ₁ → T ξ₁ = ρ y (T ξ) := by
    rintro T hT y _ _ ⟨φ, hφ, φ₁, hφ₁, hact, rfl, rfl⟩
    obtain ⟨φ', hφ', he⟩ := onto' (Rf.p B.v₁ φ)
    obtain ⟨φ₁', hφ₁', hact'⟩ := (ex' 1 (one_mem G.V') y.1 y.2 φ' hφ').exists
    have e₁ := hM.fin.equiv B.v₁ y.1 y.2 φ hφ φ' hφ' φ₁ hφ₁ φ₁' hφ₁' hact hact' he.symm
    funext h
    rw [e₁, hT y.1 y.2 φ' hφ' φ₁' hφ₁' hact' h, ρ_apply, he]
  obtain ⟨m, k, g, hg⟩ := Submodule.mem_span_set'.1 hI
  choose T hTe ξ hξ using fun j => (g j).2
  have hsum : f = ∑ j, T j (k j • ξ j) := by
    rw [← hg]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_smul, ← hξ j]
  have key := TransMaps.sum_mem_span Rel ρ tot irred N hN' T (fun j => transfer (T j) (hTe j)) (fun j => k j • ξ j)
    (hsum ▸ hfN)
  rw [hsum]
  refine Submodule.span_mono ?_ key
  rintro _ ⟨S, hSN, hSe, ζ, rfl⟩
  obtain ⟨φ, hφ, rfl⟩ := onto ζ
  refine ⟨S ∘ₗ Rf.p B.v₁, fun _ _ => hSN _, fun z hz => ?_, ?_, φ, hφ, rfl⟩
  · have : z ∈ LinearMap.ker (Rf.p B.v₁) := hM.fin.inv B.v₁ hz
    rw [LinearMap.mem_ker] at this ⊢
    simp [this]
  · intro y hy φ₀ hφ₀ φ₁ hφ₁ hact h
    have := hSe ⟨y, hy⟩ _ _ ⟨φ₀, hφ₀, φ₁, hφ₁, hact, rfl, rfl⟩
    exact congrFun this h

end Maps

section Global

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
  {B : Base F E} {a a' : ℕ} {G : Geo σ a a'} {X : Chars F E} {om : Rep σ G.V G.W} {om' : Rep σ G.V' G.W}

theorem form_of_span (hKP : KP) (hT : IsTriple B G X om om') {f : UA σ G.W.J → ℂ}
    (hf : f ∈ Submodule.span ℂ (mapVals B G om (Dec σ G.W.J))) {d₂ : ℕ} (H : Plane E a d₂)
    (hH : d₂ + 2 = a ∧ form σ G.V.J H.x H.x = 0 ∧ form σ G.V.J H.y H.y = 0 ∧ form σ G.V.J H.x H.y = 1 ∧
      (∀ u, form σ G.V.J (H.ι *ᵥ u) H.x = 0 ∧ form σ G.V.J (H.ι *ᵥ u) H.y = 0) ∧ Function.Injective H.ι.mulVec)
    (V₁ : Spc F E d₂) (M₁ : Model σ V₁ G.W) (e : Fn F a (a + a') →ₗ[ℂ] Fn F d₂ (a + a'))
    (hV₁ : V₁.J = H.ιᵀ * G.V.J * H.ι.map σ) (hM₁ : M₁.IsGood B.ψ)
    (he : IsEv B G.M M₁ H.ι 1 {u | ∃ z, u = Matrix.vecMulVec (incV F H.x) z} e)
    (μ : Measure (UA σ G.W.J)) (𝓕 : Set (UA σ G.W.J)) (hμ : μ.IsHaarMeasure) (h𝓕 : IsFundamentalDomain (ratU σ G.W.J) 𝓕 μ)
    (g : UA σ G.V.J) (Ψ : Fn F a (a + a')) (hΨ : Ψ ∈ schA F (Fin a × Fin (a + a')))
    (hne : ∫ h in 𝓕, f h * (starRingEnd ℂ) (thetaSum F (e (om (g, h) Ψ))) ∂μ ≠ 0) :
    ∃ (ν₀ β₀ : (Fv F B.v₁)ˣ →* ℂˣ) (ℓ : Fin a → Fv F B.v₁) (ψv : AddChar (Fv F B.v₁) ℂ)
      (Bf : GlobalTheory.WeilM.SB (Matrix (Fin a) (Fin (a + a')) (Fv F B.v₁)) →ₗ[ℂ] GlobalTheory.WeilM.SB (Matrix (Fin a) (Fin (a + a')) (Fv F B.v₁)) →ₗ⋆[ℂ] ℂ),
      GlobalTheory.SmGL.IsSmoothChar ν₀ ∧ GlobalTheory.SmGL.IsUnitaryChar ν₀ ∧ GlobalTheory.SmGL.IsSmoothChar β₀ ∧ GlobalTheory.SmGL.IsUnitaryChar β₀ ∧
      (∀ m : ℕ, 0 < m → ∀ r : ℝ, ((ν₀ (unifAt B.v₁) : ℂ)) ^ m ≠ (r : ℂ)) ∧ ℓ ≠ 0 ∧ Continuous ψv ∧ ψv ≠ 1 ∧ Bf ≠ 0 ∧
      (∀ (g : GL (Fin a) (Fv F B.v₁)) (Ψ₁ Ψ₁' Ψ₂ : GlobalTheory.WeilM.SB (Matrix (Fin a) (Fin (a + a')) (Fv F B.v₁))),
        Ψ₁'.1 = GlobalTheory.SplitFlip.omA ν₀ β₀ g 1 Ψ₁.1 → Bf Ψ₁' Ψ₂ = Bf Ψ₁ Ψ₂) ∧
      (∀ (h : GL (Fin (a + a')) (Fv F B.v₁)) (Ψ₁ Ψ₁' Ψ₂ Ψ₂' : GlobalTheory.WeilM.SB (Matrix (Fin a) (Fin (a + a')) (Fv F B.v₁))),
        Ψ₁'.1 = GlobalTheory.SplitFlip.omA ν₀ β₀ 1 h Ψ₁.1 → Ψ₂'.1 = GlobalTheory.SplitFlip.omA ν₀ β₀ 1 h Ψ₂.1 → Bf Ψ₁' Ψ₂' = Bf Ψ₁ Ψ₂) ∧
      (∀ (z : Fin (a + a') → Fv F B.v₁) (Ψ₁ Ψ₂ Ψ₂' : GlobalTheory.WeilM.SB (Matrix (Fin a) (Fin (a + a')) (Fv F B.v₁))),
        Ψ₂'.1 = (fun Y => ψv (ℓ ⬝ᵥ (Y *ᵥ z)) * Ψ₂.1 Y) → Bf Ψ₁ Ψ₂' = Bf Ψ₁ Ψ₂) := by
  obtain ⟨ν₀, β₀, ι, ℓ, ψv, s1, s2, s3, s4, s5, s6, s7, s8, hι, mV, mW, mH⟩ :=
    GlobalTheory.T.theta_lift_hyp_plane_split hKP F E σ B a a' G X om om' hT d₂ H hH
  have hker := GlobalTheory.T.pair_hyp_plane_split hKP F E σ B _ _ G.V G.W G.M _ _ om _ _ _ _ (GlobalTheory.ThK.Inhab.pairV hT) d₂ H hH V₁ M₁ e hV₁ hM₁ he
  have hsp := IsUWeilPair.isUSplitting hT.weil
  have pres : ∀ x, ∀ Φ ∈ schA F (Fin a × Fin (a + a')), om x Φ ∈ schA F (Fin a × Fin (a + a')) := hsp.pres

  have hcm := hT.base.cm
  have hσ : ∀ x, σ (σ x) = x := GlobalTheory.SiegelSet.sigma_sigma hcm
  have hd := GlobalTheory.ThK.DescB.Nondeg.det_ne_zero_of_cartan B G.W hT.geo.hW.cartan
  obtain ⟨c₀, hc₀, hcs⟩ := GlobalTheory.CMImag.exists_imag_ne_zero F E σ hcm
  have hJ := GlobalTheory.ThKOrthVInt.isHermND_smul_of_skew hσ hT.geo.hW.skew hd hc₀ hcs
  have hfin := (GlobalTheory.ThKOrthVInt.measure_fundDom_lt_top_smul hKP.siegelSetUnitary hcm hc₀ hJ h𝓕).ne
  have h0 : μ 𝓕 ≠ 0 := fun h => hne (by rw [Measure.restrict_eq_zero.2 h, integral_zero_measure])

  let K : Fn F a (a + a') → UA σ G.W.J → ℂ := fun Φ h => thetaSum F (e (om (1, h) Φ))
  let L : (UA σ G.W.J → ℂ) → Fn F a (a + a') → ℂ := fun F₀ Φ => ∫ h in 𝓕, F₀ h * starRingEnd ℂ (K Φ h) ∂μ
  have hint : ∀ F₀ ∈ Dec σ G.W.J, ∀ Φ ∈ schA F (Fin a × Fin (a + a')),
      IntegrableOn (fun h => F₀ h * starRingEnd ℂ (K Φ h)) 𝓕 μ := fun F₀ hF₀ Φ hΦ =>
    integrableOn_mul_conj hfin hF₀ (hker Φ hΦ).1 (hker Φ hΦ).2.1 (hker Φ hΦ).2.2
  have add₁ : ∀ x ∈ Dec σ G.W.J, ∀ y ∈ Dec σ G.W.J, ∀ Φ ∈ schA F (Fin a × Fin (a + a')), L (x + y) Φ = L x Φ + L y Φ := by
    intro x hx y hy Φ hΦ
    simp only [L, Pi.add_apply, add_mul]
    exact integral_add (hint x hx Φ hΦ) (hint y hy Φ hΦ)
  have smul₁ : ∀ (c : ℂ) x Φ, L (c • x) Φ = c * L x Φ := by
    intro c x Φ
    simp only [L, Pi.smul_apply, smul_eq_mul, mul_assoc]
    exact integral_const_mul _ _
  have add₂ : ∀ x ∈ Dec σ G.W.J, ∀ Φ ∈ schA F (Fin a × Fin (a + a')), ∀ Φ₂ ∈ schA F (Fin a × Fin (a + a')),
      L x (Φ + Φ₂) = L x Φ + L x Φ₂ := by
    intro x hx Φ hΦ Φ₂ hΦ₂
    have hK : ∀ h, K (Φ + Φ₂) h = K Φ h + K Φ₂ h := fun h => by
      simp only [K, map_add]
      exact thetaSum_add F (he.maps _ (pres _ _ hΦ)) (he.maps _ (pres _ _ hΦ₂))
    simp only [L, hK, map_add, mul_add]
    exact integral_add (hint x hx Φ hΦ) (hint x hx Φ₂ hΦ₂)
  have smul₂ : ∀ (c : ℂ) x Φ, L x (c • Φ) = starRingEnd ℂ c * L x Φ := by
    intro c x Φ
    have hK : ∀ h, K (c • Φ) h = c * K Φ h := fun h => by
      simp only [K, map_smul]
      exact thetaSum_smul F c _
    simp only [L, hK, map_mul]
    rw [← integral_const_mul]
    refine integral_congr_ae (Eventually.of_forall fun h => ?_)
    ring

  have hΨ₀ := pres (g, 1) Ψ hΨ
  have hne₀ : L f (om (g, 1) Ψ) ≠ 0 := by
    have hK : ∀ h, K (om (g, 1) Ψ) h = thetaSum F (e (om (g, h) Ψ)) := fun h => by
      have : om (1, h) (om (g, 1) Ψ) = om (g, h) Ψ := by
        rw [← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk, one_mul, mul_one]
      simp only [K, this]
    simpa only [L, hK] using hne
  obtain ⟨_, ⟨T, hTN, hTa, hTe, φ₀, hφ₀, rfl⟩, hne₁⟩ := exists_ne_of_span (Dec σ G.W.J) (fun x => L x (om (g, 1) Ψ))
    (fun x hx y hy => add₁ x hx y hy _ hΨ₀) (fun c x _ h => by simp only [smul₁, h, mul_zero])
    (by rintro _ ⟨T, hTN, -, -, φ, hφ, rfl⟩; exact hTN φ hφ) hf hne₀
  obtain ⟨_, ⟨r, hr, φ₂, hφ₂, rfl⟩, hne₂⟩ := exists_ne_of_span (schA F (Fin a × Fin (a + a'))) (fun Φ => L (T φ₀) Φ)
    (add₂ _ (hTN φ₀ hφ₀)) (fun c x _ h => by simp only [smul₂, h, mul_zero])
    (by rintro _ ⟨r, hr, φ, hφ, rfl⟩; exact (hr φ hφ).2) (mem_span_tens B.v₁ hΨ₀) hne₁
  obtain ⟨Bf, hB⟩ := exists_form (Dec σ G.W.J) (schA F (Fin a × Fin (a + a'))) (SB _) (SB _) L add₁ smul₁ add₂ smul₂ ι hι T hTN
    (tensL B.v₁ r) (fun φ hφ => (hr φ hφ).2)
  have hU : ∀ φ, tensL B.v₁ r φ = tens (evFin F B.v₁) φ r := fun _ => rfl
  have pre : ∀ Ψ₁ : SB (Matrix (Fin a) (Fin (a + a')) (Fv F B.v₁)), ∃ φ ∈ SB (Fin a × Fin (a + a') → Fv F B.v₁),
      Ψ₁.1 = ι φ := fun Ψ₁ => by
    obtain ⟨φ, hφ, h⟩ := hι.surjOn Ψ₁.2
    exact ⟨φ, hφ, h.symm⟩
  refine ⟨ν₀, β₀, ℓ, ψv, Bf, s1, s2, s3, s4, s5, s6, s7, s8, fun hz => hne₂ ?_, ?_, ?_, ?_⟩
  · have := hB φ₀ hφ₀ φ₂ hφ₂ ⟨_, hι.mapsTo hφ₀⟩ ⟨_, hι.mapsTo hφ₂⟩ rfl rfl
    rw [hz] at this
    exact this.symm
  · intro g' Ψ₁ Ψ₁' Ψ₂ h
    obtain ⟨φ, hφ, e₁⟩ := pre Ψ₁
    obtain ⟨φ', hφ', e₂⟩ := pre Ψ₂
    obtain ⟨x, hx, hmod⟩ := mV g'
    obtain ⟨φ₁, hφ₁, hact, e₃⟩ := hmod φ hφ
    have hk : T φ₁ = T φ := by
      have : φ₁ - φ ∈ LinearMap.ker T := hTa (Submodule.subset_span ⟨x, hx, φ, hφ, φ₁, hφ₁, hact, rfl⟩)
      rwa [LinearMap.mem_ker, map_sub, sub_eq_zero] at this
    rw [hB φ₁ hφ₁ φ' hφ' Ψ₁' Ψ₂ (by rw [h, e₁, e₃]) e₂, hB φ hφ φ' hφ' Ψ₁ Ψ₂ e₁ e₂, hk]
  · intro h' Ψ₁ Ψ₁' Ψ₂ Ψ₂' h₁ h₂
    obtain ⟨φ, hφ, e₁⟩ := pre Ψ₁
    obtain ⟨φ', hφ', e₂⟩ := pre Ψ₂
    obtain ⟨y, hy, hmod⟩ := mW h'
    obtain ⟨φ₁, hφ₁, hact, e₃⟩ := hmod φ hφ
    obtain ⟨φ₁', hφ₁', hact', e₄⟩ := hmod φ' hφ'
    rw [hB φ₁ hφ₁ φ₁' hφ₁' Ψ₁' Ψ₂' (by rw [h₁, e₁, e₃]) (by rw [h₂, e₂, e₄]), hB φ hφ φ' hφ' Ψ₁ Ψ₂ e₁ e₂, hU, hU,
      ← hact' r (hr φ' hφ')]
    have hK : ∀ h, K (om (1, y) (tens (evFin F B.v₁) φ' r)) h = K (tens (evFin F B.v₁) φ' r) (h * y) := fun h => by
      have : om (1, h) (om (1, y) (tens (evFin F B.v₁) φ' r)) = om (1, h * y) (tens (evFin F B.v₁) φ' r) := by
        rw [← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk, one_mul]
      simp only [K, this]
    simp only [L, hK, hTe y hy φ hφ φ₁ hφ₁ hact]
    refine setIntegral_shift h𝓕 h0 hfin (φ := fun h => T φ h * starRingEnd ℂ (K (tens (evFin F B.v₁) φ' r) h))
      (fun γ hγ x => ?_) y
    have i1 := (hTN φ hφ).2.1 γ hγ x
    have i2 := (hker _ (hr φ' hφ').2).2.1 γ hγ x
    simp only [K, i1, i2]
  · intro z Ψ₁ Ψ₂ Ψ₂' h₂
    obtain ⟨φ, hφ, e₁⟩ := pre Ψ₁
    obtain ⟨φ', hφ', e₂⟩ := pre Ψ₂
    obtain ⟨u, ⟨w, hw⟩, -, hmod⟩ := mH z
    obtain ⟨φ₁', hφ₁', hact', e₄⟩ := hmod φ' hφ'
    rw [hB φ hφ φ₁' hφ₁' Ψ₁ Ψ₂' e₁ (by rw [h₂, e₂, e₄]), hB φ hφ φ' hφ' Ψ₁ Ψ₂ e₁ e₂, hU, hU, ← hact' r (hr φ' hφ')]
    have hK : ∀ h, K (G.M.co.rho B.ψ u (tens (evFin F B.v₁) φ' r)) h = K (tens (evFin F B.v₁) φ' r) h := fun h => by
      have h3 := hsp.impl ((1 : UA σ G.V.J), h) u _ (hr φ' hφ').2
      have h4 : actAB (cA σ) ((1 : UA σ G.V.J), h) u = Matrix.vecMulVec (incV F H.x) (mat h *ᵥ w) := by
        show (1 : Matrix (Fin a) (Fin a) (AE F E)) * u * (mat h)ᵀ = _
        rw [Matrix.one_mul, hw]
        ext i j
        simp only [Matrix.mul_apply, Matrix.vecMulVec_apply, Matrix.transpose_apply, Matrix.mulVec, dotProduct,
          Finset.mul_sum]
        exact Finset.sum_congr rfl fun k _ => by ring
      rw [h4] at h3
      simp only [K]
      rw [h3, he.inv _ ⟨_, rfl⟩ _ (pres _ _ (hr φ' hφ').2)]
    simp only [L, hK]

theorem form_of_integral_ne_zero : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (a a' : ℕ) (G : Geo σ a a') (X : Chars F E)
    (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W) (R : RealMaps F a a') (Rf : FinMaps F a a'), IsMatched B G X om om' R Rf →
    ∀ c : ℂ, ∀ Φ ∈ PolData B G.M, ∀ Φ' ∈ PolData B G.M' ⊓ G.M'.So B.ψ B.τ₁,
    (∀ N : ℕ, ∃ C : ℝ, ∀ h, ‖G.M.I om Φ h - c * G.M'.I om' Φ' h‖ * (qht h : ℝ) ^ N ≤ C) →
    ∀ (d₂ : ℕ) (H : Plane E a d₂), (d₂ + 2 = a ∧ form σ G.V.J H.x H.x = 0 ∧ form σ G.V.J H.y H.y = 0 ∧ form σ G.V.J H.x H.y = 1 ∧
          (∀ u, form σ G.V.J (H.ι *ᵥ u) H.x = 0 ∧ form σ G.V.J (H.ι *ᵥ u) H.y = 0) ∧ Function.Injective H.ι.mulVec) →
    ∀ (V₁ : Spc F E d₂) (M₁ : Model σ V₁ G.W) (e : Fn F a (a + a') →ₗ[ℂ] Fn F d₂ (a + a')),
      V₁.J = H.ιᵀ * G.V.J * H.ι.map σ → M₁.IsGood B.ψ →
      IsEv B G.M M₁ H.ι 1 {u | ∃ z, u = Matrix.vecMulVec (incV F H.x) z} e →
    ∀ (μ : Measure (UA σ G.W.J)) (𝓕 : Set (UA σ G.W.J)), μ.IsHaarMeasure → IsFundamentalDomain (ratU σ G.W.J) 𝓕 μ →
    ∀ (g : UA σ G.V.J), ∀ Ψ ∈ schA F (Fin a × Fin (a + a')),
      ∫ h in 𝓕, (G.M.I om Φ h - c * G.M'.I om' Φ' h) * (starRingEnd ℂ) (thetaSum F (e (om (g, h) Ψ))) ∂μ ≠ 0 →
    ∃ (ν₀ β₀ : (Fv F B.v₁)ˣ →* ℂˣ) (ℓ : Fin a → Fv F B.v₁) (ψv : AddChar (Fv F B.v₁) ℂ)
      (Bf : GlobalTheory.WeilM.SB (Matrix (Fin a) (Fin (a + a')) (Fv F B.v₁)) →ₗ[ℂ] GlobalTheory.WeilM.SB (Matrix (Fin a) (Fin (a + a')) (Fv F B.v₁)) →ₗ⋆[ℂ] ℂ),
      GlobalTheory.SmGL.IsSmoothChar ν₀ ∧ GlobalTheory.SmGL.IsUnitaryChar ν₀ ∧ GlobalTheory.SmGL.IsSmoothChar β₀ ∧ GlobalTheory.SmGL.IsUnitaryChar β₀ ∧
      (∀ m : ℕ, 0 < m → ∀ r : ℝ, ((ν₀ (unifAt B.v₁) : ℂ)) ^ m ≠ (r : ℂ)) ∧ ℓ ≠ 0 ∧ Continuous ψv ∧ ψv ≠ 1 ∧ Bf ≠ 0 ∧
      (∀ (g : GL (Fin a) (Fv F B.v₁)) (Ψ₁ Ψ₁' Ψ₂ : GlobalTheory.WeilM.SB (Matrix (Fin a) (Fin (a + a')) (Fv F B.v₁))),
        Ψ₁'.1 = GlobalTheory.SplitFlip.omA ν₀ β₀ g 1 Ψ₁.1 → Bf Ψ₁' Ψ₂ = Bf Ψ₁ Ψ₂) ∧
      (∀ (h : GL (Fin (a + a')) (Fv F B.v₁)) (Ψ₁ Ψ₁' Ψ₂ Ψ₂' : GlobalTheory.WeilM.SB (Matrix (Fin a) (Fin (a + a')) (Fv F B.v₁))),
        Ψ₁'.1 = GlobalTheory.SplitFlip.omA ν₀ β₀ 1 h Ψ₁.1 → Ψ₂'.1 = GlobalTheory.SplitFlip.omA ν₀ β₀ 1 h Ψ₂.1 → Bf Ψ₁' Ψ₂' = Bf Ψ₁ Ψ₂) ∧
      (∀ (z : Fin (a + a') → Fv F B.v₁) (Ψ₁ Ψ₂ Ψ₂' : GlobalTheory.WeilM.SB (Matrix (Fin a) (Fin (a + a')) (Fv F B.v₁))),
        Ψ₂'.1 = (fun Y => ψv (ℓ ⬝ᵥ (Y *ᵥ z)) * Ψ₂.1 Y) → Bf Ψ₁ Ψ₂' = Bf Ψ₁ Ψ₂) := by
  intro hKP F E _ _ _ _ _ σ B a a' G X om om' R Rf hM c Φ hΦ Φ' hΦ' hdec d₂ H hH V₁ M₁ e hV₁ hM₁ he μ 𝓕 hμ h𝓕 g Ψ hΨ hne
  have hsup := diff_mem_sup hKP hM c hΦ hΦ'
  have hreg : Continuous (fun h => G.M.I om Φ h - c * G.M'.I om' Φ' h) ∧
      ∀ γ ∈ ratU σ G.W.J, ∀ x, (fun h => G.M.I om Φ h - c * G.M'.I om' Φ' h) (γ * x) =
        (fun h => G.M.I om Φ h - c * G.M'.I om' Φ' h) x := by
    obtain ⟨f₁, h₁, f₂, h₂, e₀⟩ := Submodule.mem_sup.1 hsup
    obtain ⟨c1, i1⟩ := Nondeg.diffs_reg hKP hM c f₁ h₁
    obtain ⟨c2, i2⟩ := Nondeg.diffs_reg hKP hM 0 f₂ h₂
    rw [← e₀]
    exact ⟨c1.add c2, fun γ hγ x => by simp only [Pi.add_apply, i1 γ hγ, i2 γ hγ]⟩
  have hspan := mem_span_mapVals hKP hM (Dec σ G.W.J) (fun y _ F₀ hF₀ => shift_mem_Dec y hF₀)
    (sup_le (diffs_le_piVals hKP hM c) (diffs_le_piVals hKP hM 0) hsup) ⟨hreg.1, hreg.2, hdec⟩
  exact form_of_span hKP hM.triple hspan H hH V₁ M₁ e hV₁ hM₁ he μ 𝓕 hμ h𝓕 g Ψ hΨ hne

end Global

end GlobalTheory.ThK.GlobLocal
