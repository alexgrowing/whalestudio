import Mathlib
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.MarkSpec
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.Hat1
import Formalism.LocalToGlobal.ProjectiveLattices.FreeBridge
import Formalism.LocalToGlobal.ProjectiveLattices.ComponentWModel
import Formalism.LocalToGlobal.ProjectiveLattices.NormLaws
import Formalism.LocalToGlobal.ProjectiveLattices.VolProofs
import Formalism.LocalToGlobal.ProjectiveLattices.DatProofs
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import Development.AbelianVarietyTheory.PublishedTheorems.Landherr₂.ExistsNormTensor
import Formalism.LocalToGlobal.GlobalTheory.GL5.FamilyMassVolumeIdentityOfClassDecomp

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Semi
open scoped TensorProduct Topology
open GlobalTheory.RecDict

noncomputable section

namespace GlobalTheory.CuspSqInt

open MeasureTheory
open scoped Pointwise

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Adelic

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
variable {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H} {l : Level H} (Xo : Moduli Dw l) (c : Coeff l)

def frInv {Ψ : Finset (E →+* ℂ)} (b : Frame Ψ r) : Frame Ψ r := fun τ => ((mat b τ)⁻¹ : Matrix (Fin r) (Fin r) ℂ)

theorem mat_frInv {Ψ : Finset (E →+* ℂ)} (b : Frame Ψ r) (τ : Ψ) : mat (frInv b) τ = (mat b τ)⁻¹ := rfl

theorem mat_rmul {Ψ : Finset (E →+* ℂ)} (x b : Frame Ψ r) (τ : Ψ) : mat (rmul x b) τ = mat x τ * mat b τ := rfl

theorem eq_zero_of_orbit (X : Data E r) (la : Wt X.Ψ r) (P : Frame X.Ψ r → ℂ)
    (hB : ∀ x ∈ X.dom, ∀ b ∈ Bor X.Ψ r, P (rmul x b) = bchar la b * P x)
    (hΓ : ∀ γ ∈ X.Γ, ∀ x ∈ X.dom, P (lact γ x) = X.χ la γ * P x)
    {x : Frame X.Ψ r} (hx : x ∈ X.dom) {γ : GL (Fin r) E} (hγ : γ ∈ X.Γ) {b : Frame X.Ψ r} (hb : b ∈ Bor X.Ψ r)
    (hz : rmul (lact γ x) b ∈ X.dom) (h0 : P (rmul (lact γ x) b) = 0) : P x = 0 := by
  classical
  have hdet : ∀ τ, (mat b τ).det ≠ 0 := fun τ => (hb τ).1
  have hbinv : frInv b ∈ Bor X.Ψ r := by
    intro τ
    refine ⟨?_, fun a c hca => ?_⟩
    · rw [mat_frInv]
      exact (Matrix.isUnit_nonsing_inv_det _ (isUnit_iff_ne_zero.2 (hdet τ))).ne_zero
    · haveI : Invertible (mat b τ) := Matrix.invertibleOfIsUnitDet _ (isUnit_iff_ne_zero.2 (hdet τ))
      have ht : Matrix.BlockTriangular (mat b τ) id := fun i j hij => (hb τ).2 i j hij
      have := Matrix.blockTriangular_inv_of_blockTriangular ht hca
      rw [← mat_frInv] at this
      exact this
  have hcancel : rmul (rmul (lact γ x) b) (frInv b) = lact γ x := by
    funext τ
    have e : mat (rmul (rmul (lact γ x) b) (frInv b)) τ = mat (lact γ x) τ := by
      rw [mat_rmul, mat_rmul, mat_frInv]
      exact Matrix.mul_nonsing_inv_cancel_right _ _ (isUnit_iff_ne_zero.2 (hdet τ))
    exact Matrix.of.injective e
  have h1 : P (lact γ x) = 0 := by
    have := hB _ hz (frInv b) hbinv
    rw [hcancel, h0, mul_zero] at this
    exact this
  rw [hΓ γ hγ x hx] at h1
  obtain ⟨n, hn, hχ⟩ := X.χ_fin la
  have hne : X.χ la γ ≠ 0 := by
    intro h
    have := hχ γ hγ
    rw [h, zero_pow hn.ne'] at this
    exact zero_ne_one this
  exact (mul_eq_zero.1 h1).resolve_left hne

theorem eqv_holSub {Comp : Type} (X : Comp → Data E r) (la : ∀ k, Wt (X k).Ψ r) {P : FDSec X}
    (hP : P ∈ holSub X la) :
    (∀ k, ∀ x ∈ (X k).dom, ∀ b ∈ Bor (X k).Ψ r, P k (rmul x b) = bchar (la k) b * P k x) ∧
      (∀ k, ∀ γ ∈ (X k).Γ, ∀ x ∈ (X k).dom, P k (lact γ x) = (X k).χ (la k) γ * P k x) := by
  induction hP using Submodule.span_induction with
  | mem P hP => exact ⟨fun k => (hP k).1.1.2.1, fun k => (hP k).1.1.2.2⟩
  | zero => exact ⟨fun k x _ b _ => by simp, fun k γ _ x _ => by simp⟩
  | add P Q _ _ h1 h2 =>
    exact ⟨fun k x hx b hb => by simp only [Pi.add_apply]; rw [h1.1 k x hx b hb, h2.1 k x hx b hb, mul_add],
      fun k γ hγ x hx => by simp only [Pi.add_apply]; rw [h1.2 k γ hγ x hx, h2.2 k γ hγ x hx, mul_add]⟩
  | smul a P _ h1 =>
    exact ⟨fun k x hx b hb => by simp only [Pi.smul_apply, smul_eq_mul]; rw [h1.1 k x hx b hb]; ring,
      fun k γ hγ x hx => by simp only [Pi.smul_apply, smul_eq_mul]; rw [h1.2 k γ hγ x hx]; ring⟩

variable {D : D7} {Comp : Type}

section Defs

variable {X : Comp → Data E r} (V : HSp D) (dict : GA D V → Σ k, Frame (X k).Ψ r)
  (mu : GA D V → ℂ)

def AdelAut : Prop :=
  ∀ (la : ∀ k, Wt (X k).Ψ r) (P : FDSec X), IsHolCusp X la P →
    (∀ γ ∈ GQ V, ∀ g, adel V dict mu P (γ * g) = adel V dict mu P g) ∧ Continuous (adel V dict mu P)

def QuotSupp : Prop :=
  ∀ φ : GA D V → ℂ, Continuous φ → (∀ γ ∈ GQ V, ∀ g, φ (γ * g) = φ g) → onQ V φ =ᵐ[muQ1 V] 0 → ∀ g, φ g = 0

variable {V dict mu}

theorem adelAut_holSub (h : AdelAut V dict mu) (la : ∀ k, Wt (X k).Ψ r) {P : FDSec X} (hP : P ∈ holSub X la) :
    (∀ γ ∈ GQ V, ∀ g, adel V dict mu P (γ * g) = adel V dict mu P g) ∧ Continuous (adel V dict mu P) := by
  induction hP using Submodule.span_induction with
  | mem P hP => exact h la P hP
  | zero => exact ⟨fun γ _ g => by simp, by rw [map_zero]; exact continuous_const⟩
  | add P Q _ _ h1 h2 =>
    refine ⟨fun γ hγ g => ?_, ?_⟩
    · rw [map_add]; simp only [Pi.add_apply]; rw [h1.1 γ hγ g, h2.1 γ hγ g]
    · rw [map_add]; exact h1.2.add h2.2
  | smul a P _ h1 =>
    refine ⟨fun γ hγ g => ?_, ?_⟩
    · rw [map_smul]; simp only [Pi.smul_apply]; rw [h1.1 γ hγ g]
    · rw [map_smul]; exact h1.2.const_smul a

theorem onQ_eq_lift (φ : GA D V → ℂ) (hL : ∀ γ ∈ GQ V, ∀ g, φ (γ * g) = φ g) :
    onQ V φ = Quotient.lift φ (fun a b hab => by
      have h' : b * a⁻¹ ∈ GQ V := QuotientGroup.rightRel_apply.1 hab
      have := hL _ h' a
      rw [inv_mul_cancel_right] at this
      exact this.symm) := by
  funext q
  show φ q.out = _
  conv_rhs => rw [← Quotient.out_eq q]
  rfl

theorem adelMeas_of_aut {U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r} {σ : c.F →+* ℂ} {V : HSp D}
    {dict : GA D V → Σ k, Frame ((U σ).X k).Ψ r} {mu : GA D V → ℂ}
    (h : AdelAut V dict mu) : AdelMeas U σ V dict mu := by
  intro la P hP
  obtain ⟨hL, hC⟩ := h la P hP
  haveI : BorelSpace (GA D V) := ⟨rfl⟩
  rw [onQ_eq_lift _ hL]
  refine Measurable.aestronglyMeasurable ?_
  exact measurable_from_quotient.2 hC.measurable

theorem aeDom_of_aut {U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r} {σ : c.F →+* ℂ} {V : HSp D}
    {dict : GA D V → Σ k, Frame ((U σ).X k).Ψ r} {mu : GA D V → ℂ} {Kf : Subgroup (GA D V)}
    {th : ∀ k, ((U σ).X k).Ψ → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)} {hr : V.rank = r}
    (hA : AdelAut V dict mu) (hQ : QuotSupp V) (hmu : MuUnit V dict mu) (hd : DictIsUnif V dict Kf th hr) :
    AeDom U σ V dict mu := by
  intro la P hP hae k x hx
  have hA' := adelAut_holSub hA la hP
  have hz : ∀ g, adel V dict mu P g = 0 := hQ _ hA'.2 hA'.1 hae
  have hEq := eqv_holSub (U σ).X la hP
  obtain ⟨g, γ, hγ, b, hb, hg⟩ := hd.2.2.2.2.1 k x hx
  have hdom := hd.2.2.2.1 g
  have h0 := hz g
  change mu g * P (dict g).1 (dict g).2 = 0 at h0
  rw [hg] at h0 hdom
  have hmu0 : mu g ≠ 0 := by
    intro h
    have := hmu.2.1 g
    rw [h, norm_zero] at this
    exact zero_ne_one this
  exact eq_zero_of_orbit _ (la k) (P k) (hEq.1 k) (hEq.2 k) hx hγ hb hdom ((mul_eq_zero.1 h0).resolve_left hmu0)

end Defs

theorem volPair_of_tie (hT : VolTieG D) (V : HSp D) (hs : V.SigOK) : ∃ p : Measure (GA D V) × Set (GA D V), IsVolPair D V p.1 p.2 := by
  obtain ⟨⟨μ, hμ⟩, h2⟩ := hT V hs
  obtain ⟨⟨𝓕, h𝓕⟩, _⟩ := h2 μ hμ
  exact ⟨(μ, 𝓕), hμ, h𝓕⟩

theorem quotSupp_of (V : HSp D) (hV : FinVol V) (hP : ∃ p : Measure (GA D V) × Set (GA D V), IsVolPair D V p.1 p.2) :
    QuotSupp V := by
  intro φ hc hL hae g0
  have hvp : IsVolPair D V (volPair V).1 (volPair V).2 := by
    unfold volPair
    rw [dif_pos hP]
    exact hP.choose_spec
  haveI := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.topGroupHA D.sp.cm.sig V.gram
  haveI := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.borelHA D.sp.cm.sig V.gram
  haveI := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.measurableMulHA D.sp.cm.sig V.gram
  haveI : Countable (GQ V) := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.countableGamma D.sp.cm.sig V.gram
  haveI : (volPair V).1.IsHaarMeasure := hvp.1.1
  haveI := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.measurableConstSMul_subgroup (GQ V)
  haveI := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.smulInvariant_subgroup (GQ V) (volPair V).1

  have h1 : onQ V φ =ᵐ[muQ V] 0 := by
    have hq : muQ1 V = (muQ V Set.univ)⁻¹ • muQ V := by
      unfold muQ1; rw [if_pos (show muQ V Set.univ ≠ 0 ∧ muQ V Set.univ ≠ ⊤ from hV)]
    rw [hq] at hae
    rw [Filter.EventuallyEq, ae_iff] at hae ⊢
    rw [Measure.smul_apply, smul_eq_mul] at hae
    exact (mul_eq_zero.1 hae).resolve_left (ENNReal.inv_ne_zero.2 hV.2)

  have h2 : ∀ᵐ g ∂((volPair V).1.restrict (volPair V).2), φ g = 0 := by
    have hm : AEMeasurable (autMk V) ((volPair V).1.restrict (volPair V).2) :=
      (measurable_quotient_mk'' (s := QuotientGroup.rightRel (GQ V))).aemeasurable
    have := ae_of_ae_map hm (show ∀ᵐ q ∂(muQ V), onQ V φ q = (0 : AutQ V → ℂ) q from h1)
    filter_upwards [this] with g hg
    rw [onQ_eq_lift φ hL] at hg
    exact hg
  let t : Set (GA D V) := {g | φ g ≠ 0}
  have ht : IsOpen t := hc.isOpen_preimage _ isOpen_ne
  have htm : MeasurableSet t := ht.measurableSet
  have h3 : (volPair V).1 (t ∩ (volPair V).2) = 0 := by
    rw [← Measure.restrict_apply htm]
    exact ae_iff.1 h2
  have hinv : ∀ γ : GQ V, γ • t = t := by
    intro γ
    ext x
    rw [Set.mem_smul_set_iff_inv_smul_mem]
    show φ (γ⁻¹ • x) ≠ 0 ↔ φ x ≠ 0
    rw [Subgroup.smul_def, smul_eq_mul, hL _ (γ⁻¹).2 x]
  have h4 : (volPair V).1 t = 0 := hvp.2.measure_zero_of_invariant t hinv h3
  have h5 : t = ∅ := (ht.measure_eq_zero_iff (volPair V).1).1 h4
  by_contra hne
  have : g0 ∈ t := hne
  rw [h5] at this
  exact this

theorem adel_leftInv_triv {X : Comp → Data E r} {V : HSp D} {dict : GA D V → Σ k, Frame (X k).Ψ r}
    {mu : GA D V → ℂ} (hχ : ∀ k la γ, (X k).χ la γ = 1)
    (hd : ∀ γ ∈ GQ V, ∀ g, ∃ γ' ∈ (X (dict g).1).Γ, dict (γ * g) = ⟨(dict g).1, lact γ' (dict g).2⟩)
    (hdom : ∀ g, (dict g).2 ∈ (X (dict g).1).dom) (hm : MuUnit V dict mu)
    (la : ∀ k, Wt (X k).Ψ r) {P : FDSec X} (hP : IsHolCusp X la P) :
    ∀ γ ∈ GQ V, ∀ g, adel V dict mu P (γ * g) = adel V dict mu P g := by
  intro γ hγ g
  obtain ⟨γ', hγ', he⟩ := hd γ hγ g
  have hE := (eqv_holSub X la (holCusp_mem_holSub X la hP)).2 (dict g).1 γ' hγ' (dict g).2 (hdom g)
  show mu (γ * g) * P (dict (γ * g)).1 (dict (γ * g)).2 = mu g * P (dict g).1 (dict g).2
  rw [he, hm.1, hm.2.2.1 γ hγ, one_mul]
  show mu g * P (dict g).1 (lact γ' (dict g).2) = _
  rw [hE, hχ, one_mul]

theorem adelCont_of {V : HSp D} {X : Comp → Data E r} {dict : GA D V → Σ k, Frame (X k).Ψ r}
    {mu : GA D V → ℂ} (hχ : ∀ k la γ, (X k).χ la γ = 1) (hL : ∀ g₀ : GA D V, ∃ N ∈ 𝓝 g₀, ∃ (k : Comp) (x : GA D V → Frame (X k).Ψ r), ContinuousOn x N ∧
      ∀ g ∈ N, x g ∈ (X k).dom ∧ ∃ γ ∈ (X k).Γ, dict g = ⟨k, lact γ (x g)⟩) (hm : Continuous mu) :
    ∀ (la : ∀ k, Wt (X k).Ψ r) (P : FDSec X), IsHolCusp X la P → Continuous (adel V dict mu P) := by
  intro la P hP
  rw [continuous_iff_continuousAt]
  intro g₀
  obtain ⟨N, hN, k, x, hx, hs⟩ := hL g₀
  have hsec : (X k).IsSec (la k) (P k) := (hP k).1.1
  have hPc : ContinuousOn (P k) (X k).dom := hsec.1.continuousOn
  have hc : ContinuousOn (fun g => mu g * P k (x g)) N :=
    hm.continuousOn.mul (hPc.comp hx fun g hg => (hs g hg).1)
  have heq : (fun g => mu g * P k (x g)) =ᶠ[𝓝 g₀] adel V dict mu P := by
    filter_upwards [hN] with g hg
    obtain ⟨hd, γ, hγ, he⟩ := hs g hg
    show mu g * P k (x g) = mu g * P (dict g).1 (dict g).2
    rw [he]
    show mu g * P k (x g) = mu g * P k (lact γ (x g))
    rw [hsec.2.2 γ hγ (x g) hd, hχ, one_mul]
  exact (hc.continuousAt hN).congr heq

end Adelic

theorem cusp_l2_and_definite : ∀ (D : D7) (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (σ : c.F →+* ℂ) (V : HSp D) (dict : GA D V → Σ k, Frame ((U σ).X k).Ψ r) (mu : GA D V → ℂ) (Kf : Subgroup (GA D V)) (th : ∀ k, ((U σ).X k).Ψ → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (hr : V.rank = r), VolTieG D → V.SigOK → GoodEmb c σ → (∀ k la γ, ((U σ).X k).χ la γ = 1) → DictIsUnif V dict Kf th hr → MuUnit V dict mu → Continuous mu → (∀ g₀ : GA D V, ∃ N ∈ 𝓝 g₀, ∃ (k : _) (x : GA D V → Frame ((U σ).X k).Ψ _), ContinuousOn x N ∧ ∀ g ∈ N, x g ∈ ((U σ).X k).dom ∧ ∃ γ ∈ ((U σ).X k).Γ, dict g = ⟨k, lact γ (x g)⟩) → SupDef Xo c U → ∃ h : CuspL2 U σ V dict mu, L2DefiniteCuspForms U σ V dict mu h := by
  intro D H Dw l Xo c r U σ V dict mu Kf th hr hT hs hσ hχ hd hm hmc hL hsup
  have hA : AdelAut V dict mu := fun la P hP =>
    ⟨adel_leftInv_triv hχ hd.1 hd.2.2.2.1 hm la hP, adelCont_of hχ hL hmc la P hP⟩
  have h := cusp_L2_of_measurable hσ (dict_dom_of hd) hm (adelMeas_of_aut Xo c hA)
  exact ⟨h, l2Def_of_cusp hσ hsup (aeDom_of_aut Xo c hA
    (quotSupp_of V (finVol_of_volTie hT V hs) (volPair_of_tie hT V hs)) hm hd) h⟩

end GlobalTheory.CuspSqInt
