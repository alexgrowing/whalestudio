import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AverageDerivativeL1Bound
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WaveSolutionExistence
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WaveKernelExistence
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DifferentiableAtOfSmooth
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsMultOfFintype
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.KTypeLemma.RightHolRightHolEq

noncomputable section

open MeasureTheory Matrix Filter Topology
open scoped ContDiff
open PositivityTheory.RgTw (Mat G)
open PositivityTheory.RgBcC GlobalTheory.CompanionTheory.WaveK GlobalTheory.CompanionTheory

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

namespace GlobalTheory.CompanionTheory.WaveK.Word

variable {n : ℕ}

section Defs

variable {L : Type} [NormedAddCommGroup L] [NormedSpace ℂ L]

def lift (D : (Mat n → L) → Mat n → L) (K : Mat n → Mat n → L) : Mat n → Mat n → L :=
  fun x y => D (fun x' => K x' y) x

structure Cl (K : Mat n → Mat n → L) : Prop where
  smooth : ContDiffOn ℝ ∞ (Function.uncurry K) (GLs n ×ˢ GLs n)
  supp : ∃ R, ∀ x ∈ GLs n, ∀ y ∈ GLs n, R + lg x < lg y → K x y = 0

def kK (k : Mat n → L) : Mat n → Mat n → L := fun x y => k (x⁻¹ * y)

def Iop {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] [MeasurableSpace (G n)] (μ : Measure (G n))
    (K : Mat n → Mat n → (V →L[ℂ] V)) (φ : Mat n → V) : Mat n → V :=
  fun x => ∫ y : G n, K x y.val (φ y.val) ∂μ

end Defs

section ClB
variable {L : Type} [NormedAddCommGroup L] [NormedSpace ℂ L]

theorem Cl.slice' {K : Mat n → Mat n → L} (h : Cl K) {x : Mat n} (hx : x ∈ GLs n) :
    ContDiffOn ℝ ∞ (fun y => K x y) (GLs n) :=
  h.smooth.comp (f := fun y => (x, y)) (contDiff_const.prodMk contDiff_id).contDiffOn fun _ hy => ⟨hx, hy⟩

end ClB

section Lem
variable {L : Type} [NormedAddCommGroup L] [NormedSpace ℂ L]

theorem contDiff_ent (a b : Fin n) : ContDiff ℝ ∞ (fun y : Mat n => y a b) :=
  (LinearMap.toContinuousLinearMap (Matrix.entryLinearMap ℝ ℂ a b)).contDiff

theorem contDiffOn_invMul : ContDiffOn ℝ ∞ (fun p : Mat n × Mat n => p.1⁻¹ * p.2) (GLs n ×ˢ GLs n) := by
  have hinv : ContDiffOn ℝ ∞ (fun p : Mat n × Mat n => p.1⁻¹) (GLs n ×ˢ GLs n) :=
    (ReciprocityTheory.ChartRestriction.DS.Lap.LemK.contDiffOn_inv_det_ne_zero.restrict_scalars ℝ).comp (f := Prod.fst) contDiff_fst.contDiffOn
      fun p hp => hp.1
  refine contDiffOn_pi.2 fun a => contDiffOn_pi.2 fun b => ?_
  simp only [Matrix.mul_apply]
  refine ContDiffOn.sum fun c _ => ContDiffOn.mul ?_ ?_
  · exact (contDiff_ent a c).comp_contDiffOn hinv
  · exact ((contDiff_ent c b).comp contDiff_snd).contDiffOn

theorem cl_kK (hL : LgFacts) {k : Mat n → L} (hk : ContDiffOn ℝ ∞ k (GLs n)) {R : ℝ}
    (hR : ∀ y ∈ GLs n, R < lg y → k y = 0) : Cl (kK k) := by
  refine ⟨hk.comp contDiffOn_invMul fun p hp => GlobalTheory.CompanionTheory.WaveAll.mul_mem_GLs (GlobalTheory.CompanionTheory.WaveMult.inv_mem_GLs hp.1) hp.2,
    R, fun x hx y hy hl => ?_⟩
  have hz := GlobalTheory.CompanionTheory.WaveAll.mul_mem_GLs (GlobalTheory.CompanionTheory.WaveMult.inv_mem_GLs hx) hy
  refine hR _ hz ?_
  have h := (hL n).1 x hx _ hz
  rw [Matrix.mul_nonsing_inv_cancel_left _ _ (isUnit_iff_ne_zero.2 hx)] at h
  linarith

theorem Rd_clm (T : L →L[ℂ] L) (X : Mat n) {f : Mat n → L} (hf : ContDiffOn ℝ ∞ f (GLs n)) :
    Set.EqOn (Rd X fun x => T (f x)) (fun x => T (Rd X f x)) (GLs n) := by
  intro g hg
  have hd := (GlobalTheory.CompanionTheory.RCalc.differentiableAt_of_smooth hf hg).hasFDerivAt
  have h : HasFDerivAt (fun x => T (f x)) ((T.restrictScalars ℝ).comp (fderiv ℝ f g)) g :=
    (T.restrictScalars ℝ).hasFDerivAt.comp g hd
  show fderiv ℝ (fun x => T (f x)) g (g * X) = _
  rw [h.fderiv]
  rfl

theorem Eu_clm (T : L →L[ℂ] L) (s : Bool) (a b : Fin n) {f : Mat n → L} (hf : ContDiffOn ℝ ∞ f (GLs n)) :
    Set.EqOn (Eu s a b fun x => T (f x)) (fun x => T (Eu s a b f x)) (GLs n) := by
  intro g hg
  simp only [Eu, Pi.smul_apply, Pi.add_apply, Rd_clm T _ hf hg, map_smul, map_add]

theorem Epow_clm (hR : RCalc) (T : L →L[ℂ] L) (s : Bool) {f : Mat n → L} (hf : ContDiffOn ℝ ∞ f (GLs n)) (m : ℕ) :
    ∀ a b : Fin n, Set.EqOn (Epow s m a b fun x => T (f x)) (fun x => T (Epow s m a b f x)) (GLs n) := by
  induction m with
  | zero =>
    intro a b x _
    by_cases hab : a = b <;> simp [Epow, hab]
  | succ m ih =>
    intro a b x hx
    simp only [Epow, Finset.sum_apply, map_sum]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [GlobalTheory.CompanionTheory.WaveAll.Eu_congr GlobalTheory.CompanionTheory.WaveAll.isOpen_GLs (ih c b) s a c hx]
    exact Eu_clm T s a c (GlobalTheory.CompanionTheory.WaveAll.Epow_smooth hR hf s m c b) hx

theorem zOp_congr (w : List (Bool × ℕ)) {f f' : Mat n → L} (h : Set.EqOn f f' (GLs n)) :
    Set.EqOn (zOp w f) (zOp w f') (GLs n) := by
  induction w with
  | nil => exact h
  | cons p w ih => exact GlobalTheory.CompanionTheory.WaveAll.gel_congr GlobalTheory.CompanionTheory.WaveAll.isOpen_GLs ih p.1 p.2

end Lem

theorem secondCountable_G : SecondCountableTopology (G n) := by
  haveI : SecondCountableTopology (Mat n) := inferInstanceAs (SecondCountableTopology (Fin n → Fin n → ℂ))
  haveI : SecondCountableTopology (Mat n)ᵐᵒᵖ := MulOpposite.opHomeomorph.symm.isEmbedding.secondCountableTopology
  exact Units.isEmbedding_embedProduct.secondCountableTopology

section Lem2
variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] [CompleteSpace V]
  [MeasurableSpace (G n)] [BorelSpace (G n)] (μ : Measure (G n)) [μ.IsHaarMeasure]

theorem J_integrable (hL : LgFacts) {P : Mat n → Mat n → V} (hP : Cl P) {x : Mat n} (hx : x ∈ GLs n) :
    Integrable (fun y : G n => P x y.val) μ := by
  haveI : SecondCountableTopology (G n) := secondCountable_G
  obtain ⟨R, hR⟩ := hP.supp
  have hc : Continuous fun y : G n => P x y.val :=
    (hP.slice' hx).continuousOn.comp_continuous Units.continuous_val fun y => WaveKer.val_mem_GLs y
  refine hc.integrable_of_hasCompactSupport (HasCompactSupport.intro ((hL n).2.2.2.2.1 (R + lg x)) fun y hy => ?_)
  exact hR x hx _ (WaveKer.val_mem_GLs y) (by simpa [add_comm] using hy)

end Lem2

section Lem3
variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] [CompleteSpace V]
  [MeasurableSpace (G n)] [BorelSpace (G n)] (μ : Measure (G n)) [μ.IsHaarMeasure]

theorem cl_ev {K : Mat n → Mat n → (V →L[ℂ] V)} (hK : Cl K) {φ : Mat n → V} (hφ : ContDiffOn ℝ ∞ φ (GLs n)) :
    Cl fun x y => K x y (φ y) := by
  obtain ⟨R, hR⟩ := hK.supp
  refine ⟨?_, R, fun x hx y hy hl => by simp [hR x hx y hy hl]⟩
  have h1 : ContDiffOn ℝ ∞ (fun p : Mat n × Mat n => (ContinuousLinearMap.restrictScalarsL ℂ V V ℝ ℝ)
      (Function.uncurry K p)) (GLs n ×ˢ GLs n) :=
    (ContinuousLinearMap.restrictScalarsL ℂ V V ℝ ℝ).contDiff.comp_contDiffOn hK.smooth
  have h2 : ContDiffOn ℝ ∞ (fun p : Mat n × Mat n => φ p.2) (GLs n ×ˢ GLs n) :=
    hφ.comp (f := Prod.snd) contDiff_snd.contDiffOn fun p hp => hp.2
  exact h1.clm_apply h2

theorem Iop_integrable (hL : LgFacts) {K : Mat n → Mat n → (V →L[ℂ] V)} (hK : Cl K) {φ : Mat n → V}
    (hφ : ContDiffOn ℝ ∞ φ (GLs n)) {x : Mat n} (hx : x ∈ GLs n) :
    Integrable (fun y : G n => K x y.val (φ y.val)) μ :=
  J_integrable μ hL (cl_ev hK hφ) hx

end Lem3

section Basic
variable {L : Type} [NormedAddCommGroup L] [NormedSpace ℂ L]

theorem one_mem : (1 : Mat n) ∈ GLs n := WaveKer.one_mem_GLs n

theorem Cl.zero : Cl (0 : Mat n → Mat n → L) :=
  ⟨contDiffOn_const (c := (0 : L)), 0, fun _ _ _ _ _ => rfl⟩

theorem Cl.add {K K' : Mat n → Mat n → L} (h : Cl K) (h' : Cl K') : Cl (K + K') := by
  obtain ⟨R, hR⟩ := h.supp
  obtain ⟨R', hR'⟩ := h'.supp
  refine ⟨h.smooth.add h'.smooth, max R R', fun x hx y hy hl => ?_⟩
  have h1 : R + lg x < lg y := by linarith [le_max_left R R']
  have h2 : R' + lg x < lg y := by linarith [le_max_right R R']
  simp [hR x hx y hy h1, hR' x hx y hy h2]

theorem Cl.smul (c : ℂ) {K : Mat n → Mat n → L} (h : Cl K) : Cl (c • K) := by
  obtain ⟨R, hR⟩ := h.supp
  exact ⟨h.smooth.const_smul c, R, fun x hx y hy hl => by simp [hR x hx y hy hl]⟩

end Basic

section Pairs

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] [CompleteSpace V]
  [MeasurableSpace (G n)] [BorelSpace (G n)] (μ : Measure (G n)) [μ.IsHaarMeasure]

def Pr (φ : Mat n → V) (DL : (Mat n → (V →L[ℂ] V)) → Mat n → (V →L[ℂ] V)) (DV : (Mat n → V) → Mat n → V) : Prop :=
  (∀ f f', Set.EqOn f f' (GLs n) → Set.EqOn (DV f) (DV f') (GLs n)) ∧
    ∀ K, Cl K → Cl (lift DL K) ∧ Set.EqOn (DV (Iop μ K φ)) (Iop μ (lift DL K) φ) (GLs n)

variable {μ} {φ : Mat n → V}

theorem Iop_zero : Iop μ (0 : Mat n → Mat n → (V →L[ℂ] V)) φ = 0 := by
  funext x
  simp [Iop]

theorem Iop_add (hL : LgFacts) {K K' : Mat n → Mat n → (V →L[ℂ] V)} (hK : Cl K) (hK' : Cl K')
    (hφ : ContDiffOn ℝ ∞ φ (GLs n)) {x : Mat n} (hx : x ∈ GLs n) :
    Iop μ (K + K') φ x = Iop μ K φ x + Iop μ K' φ x := by
  simp only [Iop, Pi.add_apply, ContinuousLinearMap.add_apply]
  exact integral_add (Iop_integrable μ hL hK hφ hx) (Iop_integrable μ hL hK' hφ hx)

theorem Iop_smul (c : ℂ) (K : Mat n → Mat n → (V →L[ℂ] V)) (x : Mat n) :
    Iop μ (c • K) φ x = c • Iop μ K φ x := by
  simp only [Iop, Pi.smul_apply, ContinuousLinearMap.smul_apply]
  exact integral_smul c _

theorem Pr.zero : Pr μ φ (fun _ => 0) (fun _ => 0) := by
  refine ⟨fun _ _ _ _ _ => rfl, fun K _ => ⟨Cl.zero, fun x _ => ?_⟩⟩
  have e : lift (fun _ => (0 : Mat n → (V →L[ℂ] V))) K = 0 := rfl
  rw [e, Iop_zero]

theorem Pr.comp {D₁ D₂ : (Mat n → (V →L[ℂ] V)) → Mat n → (V →L[ℂ] V)} {C₁ C₂ : (Mat n → V) → Mat n → V}
    (h₁ : Pr μ φ D₁ C₁) (h₂ : Pr μ φ D₂ C₂) : Pr μ φ (fun f => D₁ (D₂ f)) (fun f => C₁ (C₂ f)) := by
  refine ⟨fun f f' h => h₁.1 _ _ (h₂.1 _ _ h), fun K hK => ?_⟩
  obtain ⟨c₂, e₂⟩ := h₂.2 K hK
  obtain ⟨c₁, e₁⟩ := h₁.2 _ c₂
  exact ⟨c₁, fun x hx => (h₁.1 _ _ e₂ hx).trans (e₁ hx)⟩

theorem Pr.add (hL : LgFacts) (hφ : ContDiffOn ℝ ∞ φ (GLs n)) {D₁ D₂ : (Mat n → (V →L[ℂ] V)) → Mat n → (V →L[ℂ] V)}
    {C₁ C₂ : (Mat n → V) → Mat n → V} (h₁ : Pr μ φ D₁ C₁) (h₂ : Pr μ φ D₂ C₂) :
    Pr μ φ (fun f => D₁ f + D₂ f) (fun f => C₁ f + C₂ f) := by
  refine ⟨fun f f' h x hx => ?_, fun K hK => ?_⟩
  · simp only [Pi.add_apply, h₁.1 _ _ h hx, h₂.1 _ _ h hx]
  · obtain ⟨c₁, e₁⟩ := h₁.2 K hK
    obtain ⟨c₂, e₂⟩ := h₂.2 K hK
    have e : lift (fun f => D₁ f + D₂ f) K = lift D₁ K + lift D₂ K := rfl
    rw [e]
    refine ⟨c₁.add c₂, fun x hx => ?_⟩
    rw [Iop_add hL c₁ c₂ hφ hx]
    simp only [Pi.add_apply, e₁ hx, e₂ hx]

theorem Pr.smul (c : ℂ) {D : (Mat n → (V →L[ℂ] V)) → Mat n → (V →L[ℂ] V)} {C : (Mat n → V) → Mat n → V}
    (h : Pr μ φ D C) : Pr μ φ (fun f => c • D f) (fun f => c • C f) := by
  refine ⟨fun f f' e x hx => ?_, fun K hK => ?_⟩
  · simp only [Pi.smul_apply, h.1 _ _ e hx]
  · obtain ⟨c₁, e₁⟩ := h.2 K hK
    have e : lift (fun f => c • D f) K = c • lift D K := rfl
    rw [e]
    refine ⟨c₁.smul c, fun x hx => ?_⟩
    rw [Iop_smul]
    simp only [Pi.smul_apply, e₁ hx]

theorem Pr.sum (hL : LgFacts) (hφ : ContDiffOn ℝ ∞ φ (GLs n)) {ι : Type} (s : Finset ι)
    {D : ι → (Mat n → (V →L[ℂ] V)) → Mat n → (V →L[ℂ] V)} {C : ι → (Mat n → V) → Mat n → V}
    (h : ∀ i, Pr μ φ (D i) (C i)) : Pr μ φ (fun f => ∑ i ∈ s, D i f) (fun f => ∑ i ∈ s, C i f) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using Pr.zero
  | insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    exact Pr.add hL hφ (h a) ih

theorem act_eq_Iop (E : KMod n) (k : Mat n → (E.V →L[ℂ] E.V)) (f : Mat n → E.V) {x : Mat n} (hx : x ∈ GLs n) :
    act μ E k f x = Iop μ (kK k) f x := by
  let xG : G n := Matrix.GeneralLinearGroup.mkOfDetNeZero x hx
  have hv : xG.val = x := rfl
  have hdet : IsUnit x.det := isUnit_iff_ne_zero.2 hx
  have h := integral_mul_left_eq_self (μ := μ) (fun y : G n => k (x⁻¹ * y.val) (f y.val)) xG
  simp only [Iop, kK, act]
  rw [← h]
  refine integral_congr_ae (ae_of_all _ fun y => ?_)
  simp only [Units.val_mul, hv, Matrix.nonsing_inv_mul_cancel_left _ _ hdet]

end Pairs

end GlobalTheory.CompanionTheory.WaveK.Word
