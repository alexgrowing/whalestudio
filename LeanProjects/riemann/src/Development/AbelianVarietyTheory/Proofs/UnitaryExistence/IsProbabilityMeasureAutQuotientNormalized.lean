import Mathlib
import Formalism.LocalToGlobal.ProjectiveLattices.NormsFree
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.OrthonormalFlagTranslateHolds
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.FourierCoefficientDomain
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.MajLactRmul
import Development.AbelianVarietyTheory.BlockTheory.ExistenceTori.UnitaryHaarVolume

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.PeterssonCompare

open MeasureTheory NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHaarVolume
open scoped ENNReal

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

section Adelic

variable {G : Type} [Group G] (Γ : Subgroup G) {Comp : Type}

abbrev AutQ : Type := Quotient (QuotientGroup.rightRel Γ)

def adel {X : Comp → Data E r} (dict : G → Σ k, Frame (X k).Ψ r) (mu : G → ℂ) : FDSec X →ₗ[ℂ] (G → ℂ) where
  toFun P := fun g => mu g * P (dict g).1 (dict g).2
  map_add' P Q := by funext g; simp [mul_add]
  map_smul' a P := by funext g; simp [mul_left_comm]

def onQ : (G → ℂ) →ₗ[ℂ] (AutQ Γ → ℂ) where
  toFun φ := fun q => φ q.out
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def MuUnit {X : Comp → Data E r} (dict : G → Σ k, Frame (X k).Ψ r) (mu : G → ℂ) : Prop :=
  (∀ g g', mu (g * g') = mu g * mu g') ∧ (∀ g, ‖mu g‖ = 1) ∧ (∀ γ ∈ Γ, mu γ = 1) ∧
    ∀ g τ i, ‖dmin (X (dict g).1).Gm (dict g).2 τ i‖ = 1

variable {K : Type} [Field K] {C : Type} [AddCommGroup C] [Module K C] (σ : K →+* ℂ)

def jFn {X : Comp → Data E r} (rd : C →ₛₗ[σ] FDSec X) (dict : G → Σ k, Frame (X k).Ψ r) (mu : G → ℂ) :
    C →ₛₗ[σ] (AutQ Γ → ℂ) :=
  (onQ Γ ∘ₗ adel dict mu).comp rd

variable [MeasurableSpace G] (μ₀ : Measure (AutQ Γ))

open Classical in

def muQ1 : Measure (AutQ Γ) :=
  if μ₀ Set.univ ≠ 0 ∧ μ₀ Set.univ ≠ ⊤ then (μ₀ Set.univ)⁻¹ • μ₀ else Measure.dirac (Quotient.mk _ 1)

instance isProbabilityMeasure_autQuotientNormalized : IsProbabilityMeasure (muQ1 Γ μ₀) := by
  unfold muQ1
  split_ifs with h
  · exact ⟨by rw [Measure.smul_apply, smul_eq_mul, ENNReal.inv_mul_cancel h.1 h.2]⟩
  · infer_instance

def JMemL2 {X : Comp → Data E r} (rd : C →ₛₗ[σ] FDSec X) (dict : G → Σ k, Frame (X k).Ψ r) (mu : G → ℂ) : Prop :=
  ∀ f, MemLp (jFn Γ σ rd dict mu f) 2 (muQ1 Γ μ₀)

def l2NormAlt {X : Comp → Data E r} (rd : C →ₛₗ[σ] FDSec X) (dict : G → Σ k, Frame (X k).Ψ r) (mu : G → ℂ)
    (h : JMemL2 Γ σ μ₀ rd dict mu) (f : C) : ℝ :=
  ‖(h f).toLp _‖

def L2Definite {X : Comp → Data E r} (rd : C →ₛₗ[σ] FDSec X) (dict : G → Σ k, Frame (X k).Ψ r) (mu : G → ℂ)
    (h : JMemL2 Γ σ μ₀ rd dict mu) : Prop :=
  ∀ f, l2NormAlt Γ σ μ₀ rd dict mu h f = 0 → f = 0

end Adelic

variable {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l}

section AdelicCusp

variable (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (σ : c.F →+* ℂ) {G : Type} [Group G] [MeasurableSpace G]
  (Γ : Subgroup G) (μ₀ : Measure (AutQ Γ)) (dict : G → Σ k, Frame ((U σ).X k).Ψ r) (mu : G → ℂ)

def CuspL2 : Prop := ∀ a n, Dom a n → JMemL2 Γ σ μ₀ (rdC U σ a n) dict mu

open Classical in

def l2C (x : ℝ) (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) (h : JMemL2 Γ σ μ₀ (rdC U σ a n) dict mu) (f : Rul Xo c) : ℝ :=
  if hf : f ∈ cusp Xo c U a n then lieFac Dw x a * l2NormAlt Γ σ μ₀ (rdC U σ a n) dict mu h ⟨f, hf⟩ else 0

def L2DefiniteCuspForms (h : CuspL2 U σ Γ μ₀ dict mu) : Prop :=
  ∀ a n (hd : Dom a n), L2Definite Γ σ μ₀ (rdC U σ a n) dict mu (h a n hd)

def JMeas (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) : Prop :=
  ∀ f, AEStronglyMeasurable (jFn Γ σ (rdC U σ a n) dict mu f) (muQ1 Γ μ₀)

def LiesOver : Prop :=
  ∀ F : ∀ k, Frame ((U σ).X k).Ψ r → ℝ≥0∞, (∀ k, Measurable (F k)) →
    (∀ k, ∀ γ ∈ ((U σ).X k).Γ, ∀ x ∈ ((U σ).X k).dom, F k (lact γ x) = F k x) →
    (∀ k, ∀ b ∈ Bor ((U σ).X k).Ψ r, ∀ x ∈ ((U σ).X k).dom, F k (rmul x b) = F k x) →
    (∫⁻ q, F (dict q.out).1 (dict q.out).2 ∂(muQ1 Γ μ₀)) * totVol (U σ) = totInt (U σ) F

structure Tied (x : ℝ) : Prop where
  dom : ∀ g, (dict g).2 ∈ ((U σ).X (dict g).1).dom
  unit : MuUnit Γ dict mu
  xi : ∀ k (τ : E →+* ℂ), ‖τ ((U σ).X k).ξ0‖ = x
  vol : FinVol (U σ)
  lies : LiesOver U σ Γ μ₀ dict

variable {U σ Γ μ₀ dict mu}

end AdelicCusp

section Fundamental

variable {G : Type} [Group G] [MeasurableSpace G] [MeasurableMul G] {μ : Measure G} [μ.IsMulLeftInvariant]
  {Λ : Subgroup G} [Countable Λ] {𝓕 : Set G}

open scoped Pointwise in

theorem iSup_inj_eq (h𝓕 : IsFundamentalDomain Λ 𝓕 μ) {Φ : G → ℝ≥0∞} (hΦ : ∀ (s : Λ) g, Φ (s • g) = Φ g) :
    ⨆ (D : Set G) (_ : MeasurableSet D) (_ : ∀ s : Λ, ∀ g ∈ D, s • g ∈ D → s = 1), ∫⁻ g in D, Φ g ∂μ =
      ∫⁻ g in 𝓕, Φ g ∂μ := by
  apply le_antisymm
  · refine iSup_le fun D => iSup_le fun hD => iSup_le fun hi => ?_
    rw [h𝓕.setLIntegral_eq_tsum' Φ D]
    simp only [hΦ]
    rw [← lintegral_iUnion₀ (fun s => ((hD.const_smul s).nullMeasurableSet).inter h𝓕.nullMeasurableSet)]
    · exact lintegral_mono_set (Set.iUnion_subset fun _ => Set.inter_subset_right)
    · intro s t hst
      refine Disjoint.aedisjoint (Set.disjoint_left.2 ?_)
      rintro _ ⟨⟨g, hg, rfl⟩, -⟩ ⟨ht, -⟩
      rw [Set.mem_smul_set_iff_inv_smul_mem, ← mul_smul] at ht
      exact hst (inv_mul_eq_one.1 (hi _ g hg ht)).symm
  · set A := toMeasurable μ 𝓕
    have hA : MeasurableSet A := measurableSet_toMeasurable _ _
    have hAe : A =ᵐ[μ] 𝓕 := h𝓕.nullMeasurableSet.toMeasurable_ae_eq
    set B : Set G := ⋃ s : {s : Λ // s ≠ 1}, s.1 • A
    have hB : MeasurableSet B := MeasurableSet.iUnion fun s => hA.const_smul _
    have h0 : μ (A ∩ B) = 0 := by
      rw [Set.inter_iUnion]
      refine measure_iUnion_null fun s => ?_
      have h1 : AEDisjoint μ ((1 : Λ) • 𝓕) (s.1 • 𝓕) := h𝓕.aedisjoint s.2.symm
      rw [one_smul] at h1
      exact (measure_congr (hAe.inter ((smul_set_ae_eq s.1).2 hAe))).trans h1
    have hD : (A \ B : Set G) =ᵐ[μ] 𝓕 := (diff_ae_eq_self.2 h0).trans hAe
    refine le_iSup_of_le (A \ B) (le_iSup_of_le (hA.diff hB) (le_iSup_of_le ?_ (setLIntegral_congr hD).ge))
    intro s g hg hs
    by_contra hne
    exact hs.2 (Set.mem_iUnion.2 ⟨⟨s, hne⟩, Set.smul_mem_smul_set hg.1⟩)

end Fundamental

section Model

variable (X : Data E r)

instance secondCountable_Upq (r p : ℕ) : SecondCountableTopology (Upq r p) := by
  haveI : SecondCountableTopology (Matrix (Fin r) (Fin r) ℂ) :=
    inferInstanceAs (SecondCountableTopology (Fin r → Fin r → ℂ))
  haveI : SecondCountableTopology (Matrix (Fin r) (Fin r) ℂ)ᵐᵒᵖ := MulOpposite.opHomeomorph.symm.secondCountableTopology
  haveI : SecondCountableTopology (GL (Fin r) ℂ) := Units.isEmbedding_embedProduct.secondCountableTopology
  exact Topology.IsEmbedding.subtypeVal.secondCountableTopology

instance haarU_haar (r p : ℕ) : (haarU r p).IsHaarMeasure := by unfold haarU; infer_instance

instance haarR_left : (haarR X).IsMulLeftInvariant := by unfold haarR; infer_instance

theorem mat_frameOf (g : RealGrp X) (τ : X.Ψ) :
    mat (frameOf X g) τ = mat (baseFr X) τ * ((g τ : GL (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ) := rfl

theorem det_baseFr (τ : X.Ψ) : (mat (baseFr X) τ).det ≠ 0 := (X.signature τ).choose_spec.1

theorem dmin_frameOf (g : RealGrp X) (τ : X.Ψ) (i : Fin (r + 1)) :
    dmin X.Gm (frameOf X g) τ i = (psgn X.p0 i : ℂ) := by
  have h : gram τ.1 X.Gm (mat (frameOf X g) τ) = sgnMat r X.p0 := by
    rw [mat_frameOf, FrameDegreeData.gram_mul, baseFr_mem X τ]
    exact (g τ).2
  unfold dmin lminor
  rw [h, sgnMat, Matrix.submatrix_diagonal _ _ (Fin.castLE_injective _), Matrix.det_diagonal, psgn,
    Finset.prod_range]
  simp

theorem abs_psgn (p i : ℕ) : |psgn p i| = 1 := by
  unfold psgn
  rw [Finset.abs_prod]
  refine Finset.prod_eq_one fun a _ => ?_
  unfold sgn
  split_ifs <;> simp

theorem frameOf_mem_dom (g : RealGrp X) : frameOf X g ∈ X.dom := by
  intro τ
  refine ⟨?_, fun i => ?_⟩
  · rw [mat_frameOf, Matrix.det_mul]
    exact mul_ne_zero (det_baseFr X τ) (g τ).1.det_ne_zero
  · rw [dmin_frameOf, Complex.ofReal_re, ← sq, ← sq_abs, abs_psgn]
    norm_num

theorem frameOf_injective : Function.Injective (frameOf X) := by
  intro g g' h
  funext τ
  have h1 := congrArg (fun x => mat x τ) h
  simp only [mat_frameOf] at h1
  have hu : IsUnit (mat (baseFr X) τ) := (Matrix.isUnit_iff_isUnit_det _).2 (det_baseFr X τ).isUnit
  exact Subtype.ext (Units.ext (hu.mul_left_cancel h1))

theorem measurable_frameOf : Measurable (frameOf X) := by
  refine measurable_pi_lambda _ fun τ => ?_
  have h : Continuous fun u : Upq r X.p0 =>
      mat (baseFr X) τ * ((u : GL (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ) :=
    continuous_const.matrix_mul (Units.continuous_val.comp continuous_subtype_val)
  exact measurable_pi_lambda _ fun a => measurable_pi_lambda _ fun b =>
    (h.matrix_elem a b).measurable.comp (measurable_pi_apply τ)

theorem lact_frameOf {γ : GL (Fin r) E} {s : RealGrp X} (h : lact γ (baseFr X) = frameOf X s) (g : RealGrp X) :
    lact γ (frameOf X g) = frameOf X (s * g) := by
  funext τ
  have h1 : (γ : Matrix (Fin r) (Fin r) E).map τ.1 * mat (baseFr X) τ = mat (frameOf X s) τ := congrFun h τ
  show (γ : Matrix (Fin r) (Fin r) E).map τ.1 * mat (frameOf X g) τ = mat (frameOf X (s * g)) τ
  rw [mat_frameOf, ← Matrix.mul_assoc, h1, mat_frameOf, mat_frameOf, Matrix.mul_assoc]
  rfl

theorem exists_translation {γ : GL (Fin r) E} (hγ : γ ∈ X.Γ) : ∃ s, lact γ (baseFr X) = frameOf X s := by
  have key : ∀ τ : X.Ψ, ∃ u : Upq r X.p0, mat (lact γ (baseFr X)) τ =
      mat (baseFr X) τ * ((u : GL (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ) := by
    intro τ
    have hb := det_baseFr X τ
    have hd : ((mat (baseFr X) τ)⁻¹ * mat (lact γ (baseFr X)) τ).det ≠ 0 := by
      have e : mat (lact γ (baseFr X)) τ = τ.1.mapMatrix (γ : Matrix (Fin r) (Fin r) E) * mat (baseFr X) τ := rfl
      rw [e, Matrix.det_mul, Matrix.det_mul, ← RingHom.map_det, Matrix.det_nonsing_inv, Ring.inverse_eq_inv']
      exact mul_ne_zero (inv_ne_zero hb) (mul_ne_zero ((map_ne_zero _).2 γ.det_ne_zero) hb)
    have e : mat (lact γ (baseFr X)) τ = mat (baseFr X) τ * ((mat (baseFr X) τ)⁻¹ * mat (lact γ (baseFr X)) τ) :=
      (Matrix.mul_nonsing_inv_cancel_left _ _ hb.isUnit).symm
    refine ⟨⟨Matrix.GeneralLinearGroup.mkOfDetNeZero _ hd, ?_⟩, e⟩
    have h1 := MajInv.gram_lact X (X.Γ_stab γ hγ) (baseFr X) τ
    rw [e, FrameDegreeData.gram_mul, baseFr_mem X τ] at h1
    exact h1
  choose s hs using key
  exact ⟨s, funext hs⟩

theorem quotInt_eq {Λ : Subgroup (RealGrp X)} [Countable Λ]
    (hΛ : ∀ s, s ∈ Λ ↔ ∃ γ ∈ X.Γ, lact γ (baseFr X) = frameOf X s) {𝓕 : Set (RealGrp X)}
    (h𝓕 : IsFundamentalDomain Λ 𝓕 (haarR X)) {F : Frame X.Ψ r → ℝ≥0∞}
    (hF : ∀ γ ∈ X.Γ, ∀ x ∈ X.dom, F (lact γ x) = F x) :
    quotInt X F = ∫⁻ g in 𝓕, F (frameOf X g) ∂(haarR X) := by
  rw [← iSup_inj_eq h𝓕 (Φ := fun g => F (frameOf X g))]
  · unfold quotInt
    refine iSup_congr fun D => iSup_congr fun _ => iSup_congr_Prop ⟨fun h s g hg hs => ?_, fun h γ hγ g hg g' hg' e => ?_⟩
      fun _ => rfl
    · obtain ⟨γ, hγ, e⟩ := (hΛ s).1 s.2
      have h1 := h γ hγ g hg _ hs (lact_frameOf X e g)
      have h2 : frameOf X s = frameOf X 1 := by
        rw [← e, h1]
        funext τ
        show ((1 : GL (Fin r) E) : Matrix (Fin r) (Fin r) E).map τ.1 * mat (baseFr X) τ = mat (frameOf X 1) τ
        rw [mat_frameOf]
        simp
      exact Subtype.ext (frameOf_injective X h2)
    · obtain ⟨s, hs⟩ := exists_translation X hγ
      have h1 : s * g = g' := frameOf_injective X ((lact_frameOf X hs g).symm.trans e)
      have h2 : s = 1 := congrArg Subtype.val (h ⟨s, (hΛ s).2 ⟨γ, hγ, hs⟩⟩ g hg (by
        show s * g ∈ D
        rw [h1]; exact hg'))
      refine X.Γ_free γ hγ _ (frameOf_mem_dom X g) (fun _ => (1 : Matrix (Fin r) (Fin r) ℂ))
        (fun τ => ⟨?_, fun a b hab => Matrix.one_apply_ne hab.ne'⟩) ?_
      · show (1 : Matrix (Fin r) (Fin r) ℂ).det ≠ 0
        simp
      · rw [lact_frameOf X hs, h2, one_mul]
        funext τ
        exact (Matrix.mul_one (mat (frameOf X g) τ)).symm
  · intro s g
    obtain ⟨γ, hγ, e⟩ := (hΛ s).1 s.2
    show F (frameOf X (s * g)) = _
    rw [← lact_frameOf X e, hF γ hγ _ (frameOf_mem_dom X g)]

end Model

theorem isSec_of_mem_holSub {Comp : Type} (X : Comp → Data E r) (la : ∀ k, Wt (X k).Ψ r) {P : FDSec X}
    (h : P ∈ holSub X la) (k : Comp) : (X k).IsSec (la k) (P k) := by
  induction h using Submodule.span_induction with
  | mem P hP => exact (hP k).1.1
  | zero => exact ⟨differentiableOn_const _, fun _ _ _ _ => by simp, fun _ _ _ _ => by simp⟩
  | add P Q _ _ hP hQ =>
    exact ⟨hP.1.add hQ.1, fun x hx b hb => by simp only [Pi.add_apply, hP.2.1 x hx b hb, hQ.2.1 x hx b hb]; ring,
      fun γ hγ x hx => by simp only [Pi.add_apply, hP.2.2 γ hγ x hx, hQ.2.2 γ hγ x hx]; ring⟩
  | smul a P _ hP =>
    exact ⟨hP.1.const_smul a,
      fun x hx b hb => by simp only [Pi.smul_apply, smul_eq_mul, hP.2.1 x hx b hb]; ring,
      fun γ hγ x hx => by simp only [Pi.smul_apply, smul_eq_mul, hP.2.2 γ hγ x hx]; ring⟩

theorem pnorm_lact (X : Data E r) {la : Wt X.Ψ r} {P : Frame X.Ψ r → ℂ} (hP : X.IsSec la P)
    {γ : GL (Fin r) E} (hγ : γ ∈ X.Γ) {x : Frame X.Ψ r} (hx : x ∈ X.dom) :
    X.pnorm la P (lact γ x) = X.pnorm la P x := by
  have hχ : ‖X.χ la γ‖ = 1 := by
    obtain ⟨n, hn, h⟩ := X.χ_fin la
    have := congrArg norm (h γ hγ)
    rw [norm_pow, norm_one] at this
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) hn.ne').1 this
  unfold Data.pnorm dmin
  simp only [MajInv.gram_lact X (X.Γ_stab γ hγ)]
  rw [hP.2.2 γ hγ _ hx, norm_mul, hχ, one_mul]

theorem continuous_dmin (X : Data E r) (τ : X.Ψ) (i : Fin (r + 1)) :
    Continuous fun x : Frame X.Ψ r => dmin X.Gm x τ i := by
  unfold dmin lminor
  refine Continuous.matrix_det (Continuous.matrix_submatrix ?_ _ _)
  refine continuous_pi fun a => continuous_pi fun c => ?_
  simp only [gram, hermC, ReciprocityTheory.ChartRestriction.G.FD.col, mat, Matrix.of_apply]
  fun_prop

theorem measurable_pnorm (X : Data E r) (la : Wt X.Ψ r) {P : Frame X.Ψ r → ℂ} (hP : ContinuousOn P X.dom)
    (h0 : ∀ x ∉ X.dom, P x = 0) : Measurable (X.pnorm la P) := by
  classical
  have hm : Measurable P := by
    have : P = X.dom.piecewise P fun _ => 0 := by
      funext x
      by_cases hx : x ∈ X.dom
      · rw [Set.piecewise_eq_of_mem _ _ _ hx]
      · rw [Set.piecewise_eq_of_notMem _ _ _ hx, h0 x hx]
    rw [this]
    exact hP.measurable_piecewise continuousOn_const (FourierCoefficientDomain.isOpen_dom X).measurableSet
  unfold Data.pnorm
  refine hm.norm.mul (Finset.measurable_prod _ fun τ _ => Finset.measurable_prod _ fun i _ => ?_)
  exact ((continuous_dmin X τ _).measurable.div (continuous_dmin X τ _).measurable).norm.pow_const _

section One

variable {U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r} {σ : c.F →+* ℂ} {G : Type} [Group G] [MeasurableSpace G]
  {Γ : Subgroup G} {μ₀ : Measure (AutQ Γ)} {dict : G → Σ k, Frame ((U σ).X k).Ψ r} {mu : G → ℂ} {x : ℝ}
  {a : (E →+* ℂ) × ℕ → ℕ} {n : ℕ}

end One

section All

variable (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) {G : (c.F →+* ℂ) → Type} [∀ σ, Group (G σ)]
  [∀ σ, MeasurableSpace (G σ)] (Γ : ∀ σ, Subgroup (G σ)) (μ₀ : ∀ σ, Measure (AutQ (Γ σ)))
  (dict : ∀ σ, G σ → Σ k, Frame ((U σ).X k).Ψ r) (mu : ∀ σ, G σ → ℂ) (x : ℝ)

def l2At (h : ∀ σ, GoodEmb c σ → CuspL2 U σ (Γ σ) (μ₀ σ) (dict σ) (mu σ)) (σ : c.F →+* ℂ)
    (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) (hd : Dom a n) : Rul Xo c → ℝ :=
  l2C U (goodOf c σ) (Γ _) (μ₀ _) (dict _) (mu _) x a n (h _ (goodEmb_goodOf _ σ) _ _ hd)

end All

end GlobalTheory.PeterssonCompare
