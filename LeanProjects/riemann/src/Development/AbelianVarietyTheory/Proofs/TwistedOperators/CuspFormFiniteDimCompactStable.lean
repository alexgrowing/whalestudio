import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RangeSndRel
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CuspAlongSmoothRows
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsAllTiedNotStable
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.DiscreteSeriesHermitianUniqueOfClassification
import Development.AbelianVarietyTheory.BlockTheory.HeightDefect.FinitePartTypes
import Development.AbelianVarietyTheory.Proofs.HeightProofs.AutomorphicFormUniformLimitDiscreteSeriesSeriesStatement
import Formalism.LocalToGlobal.IndefiniteReal.MultLemmas
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsSumOfMemMultSpan
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RderMemAutFormsCuspForms
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContDiffDerivSnoc
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IntegrationByPartsRightDerivativeAdelicQuotient
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteVolumeAdelicUnitaryQuotient
import Development.AbelianVarietyTheory.Counterexamples.HeightSurvey.ConjAtFixedIff

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open scoped TensorProduct
open Classical

noncomputable section

namespace GlobalTheory.CuspGKPet

open Matrix GlobalTheory.PointAtPlaceHom GlobalTheory.Mem.RealTranslate GlobalTheory.CuspGK GlobalTheory.CuspDecay GlobalTheory.Mem.Lift

theorem setIntegral_star_mul_self_pos {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [MeasurableSpace G] [BorelSpace G] (Γ : Subgroup G) [Countable Γ] (μ : Measure G) [μ.IsHaarMeasure] {𝓕 : Set G}
    (h : IsFundamentalDomain Γ 𝓕 μ) {x : G → ℂ} (hx : ∀ γ ∈ Γ, ∀ g, x (γ * g) = x g) (hc : Continuous x)
    (hi : IntegrableOn (fun g => star (x g) * x g) 𝓕 μ) (h0 : x ≠ 0) : 0 < (∫ g in 𝓕, star (x g) * x g ∂μ).re := by

  have hpt : ∀ g, (star (x g) * x g).re = ‖x g‖ ^ 2 := by
    intro g
    rw [Complex.star_def, Complex.conj_mul']
    norm_cast
  have hre : (∫ g in 𝓕, star (x g) * x g ∂μ).re = ∫ g in 𝓕, ‖x g‖ ^ 2 ∂μ := by
    have h1 := integral_re hi
    simp only [RCLike.re_to_complex] at h1
    rw [← h1]
    congr 1
    funext g
    exact hpt g
  have hint : IntegrableOn (fun g => ‖x g‖ ^ 2) 𝓕 μ := by
    refine (Integrable.norm hi).congr (Filter.Eventually.of_forall fun g => ?_)
    simp only [norm_mul, norm_star, sq]
  rw [hre, setIntegral_pos_iff_support_of_nonneg_ae (ae_of_all _ fun g => by positivity) hint]

  have hsupp : Function.support (fun g => ‖x g‖ ^ 2) = Function.support x := by
    ext g
    simp [Function.mem_support]
  rw [hsupp]
  have ht_open : IsOpen (Function.support x) := hc.isOpen_support
  have ht_ne : (Function.support x).Nonempty := by
    obtain ⟨g, hg⟩ := Function.ne_iff.mp h0
    exact ⟨g, hg⟩
  have ht_pos : 0 < μ (Function.support x) := ht_open.measure_pos μ ht_ne
  open Pointwise in
  have hinv : ∀ γ : Γ, γ • Function.support x = Function.support x := by
    intro γ
    ext g
    rw [Set.mem_smul_set_iff_inv_smul_mem]
    show x (((γ⁻¹ : Γ) : G) * g) ≠ 0 ↔ x g ≠ 0
    rw [hx _ (γ⁻¹).2 g]

  refine pos_iff_ne_zero.mpr fun hz => ht_pos.ne' ?_
  exact h.measure_zero_of_invariant _ hinv hz

private theorem natCast_inv_and_sub_one_inv_bounds_of_eleven_le {D : D7} {θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)} {V : HSp D}
    (hθ : IsInfFam θ) {τ : D.what₂.Tau} {k : Matrix (Fin V.rank) (Fin V.rank) ℂ}
    (hk : k ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ)) :
    k * k⁻¹ = 1 ∧ k⁻¹ ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ) ∧ IsAtTau θ V τ k⁻¹ (atTau θ V τ k)⁻¹ := by
  have hs : IsAtTau θ V τ k (atTau θ V τ k) := GlobalTheory.PointAtPlaceHom.atTau_spec hθ V τ hk

  have hmul : k * infMat D.sp.cm.sig V.gram (θ τ) (atTau θ V τ k)⁻¹ = 1 := by
    calc k * infMat D.sp.cm.sig V.gram (θ τ) (atTau θ V τ k)⁻¹
        = infMat D.sp.cm.sig V.gram (θ τ) (atTau θ V τ k) * infMat D.sp.cm.sig V.gram (θ τ) (atTau θ V τ k)⁻¹ := by
          rw [hs.2.1]
      _ = 1 := by rw [← GlobalTheory.PointAtPlaceHom.infMat_mul, mul_inv_cancel, GlobalTheory.PointAtPlaceHom.infMat_one]
  have hkinv : k⁻¹ = infMat D.sp.cm.sig V.gram (θ τ) (atTau θ V τ k)⁻¹ := Matrix.inv_eq_right_inv hmul
  have hkk : k * k⁻¹ = 1 := by rw [hkinv]; exact hmul
  have hk0 : kᴴ * gramAt D V τ * k = gramAt D V τ := hk
  refine ⟨hkk, ?_, ⟨inv_mem hs.1, hkinv.symm, fun τ' hτ' => ?_⟩⟩
  · show (k⁻¹)ᴴ * gramAt D V τ * k⁻¹ = gramAt D V τ
    calc (k⁻¹)ᴴ * gramAt D V τ * k⁻¹ = (k⁻¹)ᴴ * (kᴴ * gramAt D V τ * k) * k⁻¹ := by rw [hk0]
      _ = ((k⁻¹)ᴴ * kᴴ) * gramAt D V τ * (k * k⁻¹) := by simp only [Matrix.mul_assoc]
      _ = gramAt D V τ := by
        rw [← Matrix.conjTranspose_mul, hkk, Matrix.conjTranspose_one, Matrix.one_mul, Matrix.mul_one]
  · calc infMat D.sp.cm.sig V.gram (θ τ') (atTau θ V τ k)⁻¹
        = infMat D.sp.cm.sig V.gram (θ τ') (atTau θ V τ k)⁻¹ * infMat D.sp.cm.sig V.gram (θ τ') (atTau θ V τ k) := by
          rw [hs.2.2 τ' hτ', Matrix.mul_one]
      _ = 1 := by rw [← GlobalTheory.PointAtPlaceHom.infMat_mul, inv_mul_cancel, GlobalTheory.PointAtPlaceHom.infMat_one]

variable {D : D7} {θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)} {V : HSp D}

theorem atTau_inv (hθ : IsInfFam θ) {τ : D.what₂.Tau} {k : Matrix (Fin V.rank) (Fin V.rank) ℂ}
    (hk : k ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ)) : atTau θ V τ k⁻¹ = (atTau θ V τ k)⁻¹ := by
  obtain ⟨-, hk', hat⟩ := natCast_inv_and_sub_one_inv_bounds_of_eleven_le hθ hk
  exact ((GlobalTheory.PointAtPlaceHom.atTau_laws D θ hθ V τ).1 k⁻¹ hk').unique
    (GlobalTheory.PointAtPlaceHom.atTau_spec hθ V τ hk') hat

variable (θ V) in

def cuspSub : Submodule ℂ (GA D V → ℂ) where
  carrier := {f | IsAutFunSm θ V f ∧ IsCuspFun V f}
  zero_mem' := ⟨Formalism.IndefR.Mult.isAutFunSm_zero θ V, Formalism.IndefR.Mult.isCuspFun_zero V⟩
  add_mem' := fun a b => ⟨GlobalTheory.Mem.AutSpace.isAutFunSm_add a.1 b.1,
    GlobalTheory.MultMem.isCuspFun_add a.1.toIsAutFun b.1.toIsAutFun a.2 b.2⟩
  smul_mem' := fun c _ a => ⟨GlobalTheory.Mem.AutSpace.isAutFunSm_smul c a.1, Formalism.IndefR.Mult.isCuspFun_smul V a.2 c⟩

theorem rTr_mem_cuspSub (hθ : IsInfFam θ) {τ : D.what₂.Tau} {k : Matrix (Fin V.rank) (Fin V.rank) ℂ}
    (hk : k ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ)) {f : GA D V → ℂ} (hf : f ∈ cuspSub θ V) :
    rTr V (atTau θ V τ k) f ∈ cuspSub θ V := by
  have hf' : IsAutFunSm θ V f ∧ IsCuspFun V f := hf
  show IsAutFunSm θ V _ ∧ IsCuspFun V _
  refine ⟨GlobalTheory.Mem.RealTranslate.isAutFunSm_rTr_atTau D θ hθ V f hf'.1 τ k hk, ?_⟩
  intro r C hC μ 𝓕 hμ h𝓕 g
  have h1 := hf'.2 r C hC μ 𝓕 hμ h𝓕 (g * atTau θ V τ k)
  simpa only [rTr, mul_assoc] using h1

theorem Rder_mem_cuspSub (hθ : IsInfFam θ) {τ : D.what₂.Tau} {X : Matrix (Fin V.rank) (Fin V.rank) ℂ}
    (hX : X ∈ lieAt V τ) {f : GA D V → ℂ} (hf : f ∈ cuspSub θ V) : Rder θ V τ X f ∈ cuspSub θ V := by
  have hf' : IsAutFunSm θ V f ∧ IsCuspFun V f := hf
  show IsAutFunSm θ V _ ∧ IsCuspFun V _
  exact ⟨GlobalTheory.CuspLie.isAutFunSm_Rder hθ hX hf'.1, GlobalTheory.CuspLie.isCuspFun_Rder hθ hX hf'.1 hf'.2⟩

private theorem det_gram_ne_zero' {D : D7} (V : HSp D) : V.gram.det ≠ 0 := by
  intro h0
  obtain ⟨c, hc0, hc⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr h0
  apply hc0

  have hfr : ∀ i, V.hT (V.frame i) (∑ j, c j • V.frame j) = 0 := by
    intro i
    have h1 := congrFun hc i
    simp only [Matrix.mulVec, dotProduct, Pi.zero_apply] at h1
    rw [map_sum]
    simp only [map_smul, smul_eq_mul]
    rw [← h1]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [mul_comm]
    rfl
  have hflip : V.hT.flip (∑ j, c j • V.frame j) = 0 := V.frame.ext fun i => by simpa using hfr i
  have hall : ∀ x, V.hT x (∑ j, c j • V.frame j) = 0 := fun x => by
    simpa using LinearMap.congr_fun hflip x
  have hv0 : ∑ j, c j • V.frame j = 0 := V.nondeg.2 _ hall
  exact funext fun j => Fintype.linearIndependent_iff.mp V.frame.linearIndependent c hv0 j

private theorem det_gramAt_ne_zero {D : D7} (V : HSp D) (τ : D.what₂.Tau) : (gramAt D V τ).det ≠ 0 := by
  intro h
  have h' : (V.gram.map (tauE D τ)).det = 0 := h
  apply det_gram_ne_zero' V
  apply (tauE D τ).injective
  rw [RingHom.map_det, map_zero]
  exact h'

private theorem oneP_add_twisted_operators (hθ : IsInfFam θ) {τ : D.what₂.Tau} {X : Matrix (Fin V.rank) (Fin V.rank) ℂ}
    (hX : X ∈ lieAt V τ) (s t : ℝ) : oneP θ V τ X (s + t) = oneP θ V τ X s * oneP θ V τ X t := by
  have hJ : IsUnit (gramAt D V τ).det := (det_gramAt_ne_zero V τ).isUnit
  have hX' : Xᴴ * gramAt D V τ + gramAt D V τ * X = 0 := hX
  have hmem : ∀ r : ℝ, NormedSpace.exp (r • X) ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ) := fun r =>
    GlobalTheory.SmoothForms.exp_mem_UH hJ (by
      rw [Matrix.conjTranspose_smul, star_trivial, Matrix.smul_mul, Matrix.mul_smul, ← smul_add, hX', smul_zero])
  simp only [oneP]
  rw [add_smul, Matrix.exp_add_of_commute _ _ (((Commute.refl X).smul_left s).smul_right t)]
  exact GlobalTheory.PointAtPlaceHom.atTau_mul hθ V τ (hmem s) (hmem t)

private theorem hasDerivAt_comp_mul_oneP (hθ : IsInfFam θ) {τ : D.what₂.Tau} {X : Matrix (Fin V.rank) (Fin V.rank) ℂ}
    (hX : X ∈ lieAt V τ) {φ : GA D V → ℂ} (hφ : IsAutFunSm θ V φ) (g : GA D V) (t : ℝ) :
    HasDerivAt (fun s : ℝ => φ (g * oneP θ V τ X s)) (Rder θ V τ X φ (g * oneP θ V τ X t)) t := by
  have hd := ((GlobalTheory.MultMem.diff_oneP (GlobalTheory.MultMem.mem_smFun hφ) hX g) t).hasDerivAt

  have hshift : (fun u : ℝ => φ (g * oneP θ V τ X t * oneP θ V τ X u)) =
      fun u : ℝ => (fun s : ℝ => φ (g * oneP θ V τ X s)) (u + t) := by
    funext u
    rw [mul_assoc, ← oneP_add_twisted_operators hθ hX t u, add_comm]
  refine hd.congr_deriv ?_
  show _ = deriv (fun u : ℝ => φ (g * oneP θ V τ X t * oneP θ V τ X u)) 0
  rw [hshift]
  have h2 := deriv_comp_add_const (f := fun s : ℝ => φ (g * oneP θ V τ X s)) (a := t) (x := (0 : ℝ))
  exact (h2.trans (congrArg (deriv fun s : ℝ => φ (g * oneP θ V τ X s)) (zero_add t))).symm

theorem exists_form_cuspSub (hP : GlobalTheory.Published.CuspRapidDecay) (hθ : IsInfFam θ) :
    ∃ b : (GA D V → ℂ) →ₗ⋆[ℂ] (GA D V → ℂ) →ₗ[ℂ] ℂ,
      (∀ x ∈ cuspSub θ V, x ≠ 0 → 0 < (b x x).re) ∧
      (∀ x ∈ cuspSub θ V, ∀ y ∈ cuspSub θ V, star (b x y) = b y x) ∧
      (∀ τ, ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ), ∀ x ∈ cuspSub θ V, ∀ y ∈ cuspSub θ V,
        b x (rTr V (atTau θ V τ g) y) = b (rTr V (atTau θ V τ g⁻¹) x) y) ∧
      (∀ τ, ∀ X ∈ lieAt V τ, ∀ x ∈ cuspSub θ V, ∀ y ∈ cuspSub θ V,
        b x (Rder θ V τ X y) = -b (Rder θ V τ X x) y) := by
  classical
  obtain ⟨μ, hμ⟩ : ∃ μ : Measure (GA D V), μ.IsHaarMeasure := ⟨Measure.haar, inferInstance⟩
  obtain ⟨hR, 𝓕, h𝓕⟩ := GlobalTheory.Mem.AdelicGroupFund.rightInvariant_and_exists_fundamentalDomain D V μ hμ
  have hfin : μ 𝓕 ≠ ⊤ := (GlobalTheory.CuspDecay.measure_lt_top GlobalTheory.Mem.VolFin.finVol V μ 𝓕 hμ h𝓕).ne
  have hint : ∀ {ψ φ : GA D V → ℂ}, IsAutFunSm θ V ψ → IsAutFunSm θ V φ → IsCuspFun V φ →
      IntegrableOn (fun g => star (ψ g) * φ g) 𝓕 μ := fun hψ h hc =>
    GlobalTheory.CuspDecay.integrableOn_star_mul hP GlobalTheory.Mem.VolFin.finVol hθ μ 𝓕 hμ h𝓕 hψ h hc

  obtain ⟨q, hq⟩ := Submodule.exists_isCompl (cuspSub θ V)
  let P : (GA D V → ℂ) →ₗ[ℂ] (GA D V → ℂ) := (cuspSub θ V).subtype ∘ₗ Submodule.linearProjOfIsCompl _ q hq
  have hPm : ∀ x, IsAutFunSm θ V (P x) ∧ IsCuspFun V (P x) := fun x =>
    (Submodule.linearProjOfIsCompl (cuspSub θ V) q hq x).2
  have hPfix : ∀ x ∈ cuspSub θ V, P x = x := fun x hx =>
    congrArg Subtype.val (Submodule.linearProjOfIsCompl_apply_left hq ⟨x, hx⟩)
  have hPI : ∀ x y, IntegrableOn (fun g => star (P x g) * P y g) 𝓕 μ := fun x y =>
    hint (hPm x).1 (hPm y).1 (hPm y).2
  let B : (GA D V → ℂ) → (GA D V → ℂ) → ℂ := fun x y => ∫ g in 𝓕, star (P x g) * P y g ∂μ
  let b : (GA D V → ℂ) →ₗ⋆[ℂ] (GA D V → ℂ) →ₗ[ℂ] ℂ := LinearMap.mk₂'ₛₗ (starRingEnd ℂ) (RingHom.id ℂ) B
    (fun x x' y => by
      simp only [B, map_add, Pi.add_apply, star_add, add_mul]
      exact integral_add (hPI x y) (hPI x' y))
    (fun c x y => by
      simp only [B, map_smul, Pi.smul_apply, smul_eq_mul, star_mul', starRingEnd_apply, mul_assoc]
      exact integral_const_mul _ _)
    (fun x y y' => by
      simp only [B, map_add, Pi.add_apply, mul_add]
      exact integral_add (hPI x y) (hPI x y'))
    (fun c x y => by
      simp only [B, map_smul, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
      rw [← integral_const_mul]
      congr 1
      funext g
      ring)
  have hb : ∀ x ∈ cuspSub θ V, ∀ y ∈ cuspSub θ V, b x y = ∫ g in 𝓕, star (x g) * y g ∂μ := by
    intro x hx y hy
    change ∫ g in 𝓕, star (P x g) * P y g ∂μ = _
    rw [hPfix x hx, hPfix y hy]
  have mem : ∀ {x}, x ∈ cuspSub θ V → IsAutFunSm θ V x ∧ IsCuspFun V x := fun hx => hx
  refine ⟨b, ?_, ?_, ?_, ?_⟩
  ·
    intro x hx hx0
    rw [hb x hx x hx]
    exact setIntegral_star_mul_self_pos (GQ V) μ h𝓕 (mem hx).1.toIsAutFun.left (mem hx).1.toIsAutFun.cont
      (hint (mem hx).1 (mem hx).1 (mem hx).2) hx0
  ·
    intro x hx y hy
    rw [hb x hx y hy, hb y hy x hx, ← starRingEnd_apply, ← integral_conj]
    congr 1
    funext g
    rw [map_mul]
    simp only [starRingEnd_apply, star_star]
    ring
  ·
    intro τ g hg x hx y hy
    obtain ⟨-, hg', -⟩ := natCast_inv_and_sub_one_inv_bounds_of_eleven_le hθ hg
    rw [hb x hx _ (rTr_mem_cuspSub hθ hg hy), hb _ (rTr_mem_cuspSub hθ hg' hx) y hy, atTau_inv hθ hg]
    set k := atTau θ V τ g
    have h1 := GlobalTheory.Mem.IntByParts.setIntegral_mul_right (GQ V) μ h𝓕
      (Φ := fun h => star (x (h * k⁻¹)) * y h)
      (fun γ hγ h => by
        simp only [mul_assoc, (mem hx).1.toIsAutFun.left γ hγ, (mem hy).1.toIsAutFun.left γ hγ]) k
    simp only [mul_inv_cancel_right] at h1
    simpa only [rTr] using h1
  ·
    intro τ X hX x hx y hy
    have hRx := Rder_mem_cuspSub hθ hX hx
    have hRy := Rder_mem_cuspSub hθ hX hy
    rw [hb x hx _ hRy, hb _ hRx y hy]
    obtain ⟨B0, hB0⟩ := GlobalTheory.CuspDecay.mul_bounded_of_cuspForm hP hθ (mem hx).1 (mem hy).1 (mem hy).2
    obtain ⟨B1, hB1⟩ := GlobalTheory.CuspDecay.mul_bounded_of_cuspForm hP hθ (mem hRx).1 (mem hy).1 (mem hy).2
    obtain ⟨B2, hB2⟩ := GlobalTheory.CuspDecay.mul_bounded_of_cuspForm hP hθ (mem hx).1 (mem hRy).1 (mem hRy).2
    have hxc := (mem hx).1.toIsAutFun.cont
    have hyc := (mem hy).1.toIsAutFun.cont
    have hRxc := (mem hRx).1.toIsAutFun.cont
    have hRyc := (mem hRy).1.toIsAutFun.cont
    have h0 : oneP θ V τ X 0 = 1 := by
      simp only [oneP, zero_smul, NormedSpace.exp_zero]
      exact GlobalTheory.PointAtPlaceHom.atTau_one hθ V τ
    have key := GlobalTheory.Mem.IntByParts.setIntegral_deriv_eq_zero (GQ V) μ h𝓕 hfin
      (Φ := fun h => star (x h) * y h)
      (Φ' := fun h => star (Rder θ V τ X x h) * y h + star (x h) * Rder θ V τ X y h)
      (fun γ hγ h => by
        simp only [(mem hx).1.toIsAutFun.left γ hγ, (mem hy).1.toIsAutFun.left γ hγ])
      (hxc.star.mul hyc) ((hRxc.star.mul hyc).add (hxc.star.mul hRyc))
      (fun g => by rw [norm_mul, norm_star]; exact hB0 g)
      (fun g => (norm_add_le _ _).trans (add_le_add (by rw [norm_mul, norm_star]; exact hB1 g)
        (by rw [norm_mul, norm_star]; exact hB2 g)))
      (a := oneP θ V τ X) h0
      (fun g t => ((hasDerivAt_comp_mul_oneP hθ hX (mem hx).1 g t).star).mul (hasDerivAt_comp_mul_oneP hθ hX (mem hy).1 g t))
    rw [integral_add (hint (mem hRx).1 (mem hy).1 (mem hy).2) (hint (mem hx).1 (mem hRy).1 (mem hRy).2)] at key
    linear_combination key

theorem exists_petersson_gkGen : GlobalTheory.FunPr.Hypotheses₂ → ∀ {D : D7} (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (V : HSp D)
    (S : D.what₂.Tau → SPar) (M : Formalism.IndefR.Mult.DSModel V S), IsInfFam (D := D) θ →
    ∀ ψ : GA D V → ℂ, IsAutFunSm θ V ψ → IsCuspFun V ψ →
    (∃ W : Submodule ℂ (GA D V → ℂ), FiniteDimensional ℂ W ∧ ψ ∈ W ∧ ∀ τ, ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ),
      M.fr τ * g * (M.fr τ)⁻¹ ∈ Formalism.REAL.Kset (M.ε τ) → ∀ f ∈ W, rTr V (atTau θ V τ g) f ∈ W) →
    ∃ b : (GA D V → ℂ) →ₗ⋆[ℂ] (GA D V → ℂ) →ₗ[ℂ] ℂ,
      (∀ x ∈ GlobalTheory.CuspGK.gkGen θ M ψ, x ≠ 0 → 0 < (b x x).re) ∧
      (∀ x ∈ GlobalTheory.CuspGK.gkGen θ M ψ, ∀ y ∈ GlobalTheory.CuspGK.gkGen θ M ψ, star (b x y) = b y x) ∧
      (∀ τ g, GlobalTheory.CuspGK.InK M τ g → ∀ x ∈ GlobalTheory.CuspGK.gkGen θ M ψ, ∀ y ∈ GlobalTheory.CuspGK.gkGen θ M ψ,
        b x (rTr V (atTau θ V τ g) y) = b (rTr V (atTau θ V τ g⁻¹) x) y) ∧
      (∀ τ, ∀ X ∈ lieAt V τ, ∀ x ∈ GlobalTheory.CuspGK.gkGen θ M ψ, ∀ y ∈ GlobalTheory.CuspGK.gkGen θ M ψ,
        b x (Rder θ V τ X y) = -b (Rder θ V τ X x) y) := by
  intro hPr D θ V S M hθ ψ hψ hψc _
  obtain ⟨b, hpos, hherm, htr, hlie⟩ := exists_form_cuspSub (θ := θ) (V := V) hPr.cuspRapidDecay hθ
  have hle : GlobalTheory.CuspGK.gkGen θ M ψ ≤ cuspSub θ V :=
    GlobalTheory.CuspGK.gkGen_le θ M (show IsAutFunSm θ V ψ ∧ IsCuspFun V ψ from ⟨hψ, hψc⟩)
      ⟨fun τ g hg f hf => rTr_mem_cuspSub hθ (show _ ∧ _ from hg).1 hf,
        fun τ X hX f hf => Rder_mem_cuspSub hθ hX hf⟩
  exact ⟨b, fun x hx hx0 => hpos x (hle hx) hx0, fun x hx y hy => hherm x (hle hx) y (hle hy),
    fun τ g hg x hx y hy => htr τ g (show _ ∧ _ from hg).1 x (hle hx) y (hle hy),
    fun τ X hX x hx y hy => hlie τ X hX x (hle hx) y (hle hy)⟩

end GlobalTheory.CuspGKPet

end
