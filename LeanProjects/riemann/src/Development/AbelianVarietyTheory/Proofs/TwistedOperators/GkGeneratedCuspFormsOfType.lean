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
import Development.AbelianVarietyTheory.Proofs.HeightProofs.TypeAtOfDiscreteSeries
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RderMemAutFormsCuspForms
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContDiffDerivSnoc
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HasTypeAllAddOfEquiv
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RealPlacePointCommuteOfNePlace
import Development.AbelianVarietyTheory.Counterexamples.HeightSurvey.ConjAtFixedIff
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.SignatureExists
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open scoped TensorProduct
open Classical

noncomputable section

namespace GlobalTheory.CuspGKForms

open Matrix Filter Topology GlobalTheory.TypeSum GlobalTheory.PointAtPlaceHom GlobalTheory.Mem.AutSpace GlobalTheory.Mem.RealTranslate GlobalTheory.IndefiniteRowSideFullHecke.FinitePartTypes GlobalTheory.CuspGK
open Formalism.IndefR.Mult

variable {D : D7} {θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)} {V : HSp D}

theorem exists_sigOK (V : HSp D) : ∃ s, (GlobalTheory.SmoothAutCheck.reSig V s).SigOK := by
  have h : ∀ ρ : D.host.E →+* ℂ, ∃ pq : ℕ × ℕ, Formalism.UG.HasSignature (V.gram.map ρ) pq.1 pq.2 := fun ρ => by
    have hd : IsUnit (V.gram.map ρ).det := by
      have : (V.gram.map ρ).det = ρ V.gram.det := (RingHom.map_det _ _).symm
      rw [this, isUnit_iff_ne_zero]
      exact (map_ne_zero _).2 (GlobalTheory.SmoothAutCheck.gram_det_ne V)
    have hh : Formalism.UG.IsHerm (starRingEnd ℂ) (V.gram.map ρ) := by
      ext i j
      have hcm := D.host.isCMField_hostE
      have h1 : star (V.hT (V.frame j) (V.frame i)) = V.hT (V.frame i) (V.frame j) := V.herm.eq _ _
      simp only [Formalism.UG.cT, transpose_apply, map_apply, HSpace.gram]
      rw [← h1]
      exact (NumberField.IsCMField.complexEmbedding_complexConj _ ρ _).symm
    obtain ⟨p, q, h⟩ := Formalism.UG.P.signature_exists _ _ hh hd
    exact ⟨(p, q), h⟩
  choose s hs using h
  exact ⟨s, hs⟩

theorem goodPar_of_isTypeAt (hV : V.SigOK) {τ : D.what₂.Tau} {S : SPar} {φ : GA D V → ℂ} (h : IsTypeAt θ V τ S φ) :
    GoodPar V.rank (V.sig (tauE D τ)).1 (V.sig (tauE D τ)).2 S := by
  obtain ⟨H, _, _, σ, lam, ε, P, hE, hD, hP, hJ, -⟩ := h
  obtain ⟨e1, e2⟩ := GlobalTheory.TypeAtCompare.card_eq_of_congr hP hJ (hV (tauE D τ))
  exact ⟨lam, ε, hE, GlobalTheory.Published.HermitianUnique.isHCParam_of_isDS hE.1 hD, e1, e2⟩

theorem isTypeAt_rTr_same (hθ : IsInfFam θ) {τ : D.what₂.Tau} {S : SPar} {φ : GA D V → ℂ} (h : IsTypeAt θ V τ S φ)
    {k : Matrix (Fin V.rank) (Fin V.rank) ℂ} (hk : k ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ)) :
    IsTypeAt θ V τ S (rTr V (atTau θ V τ k) φ) := by
  obtain ⟨H, _, _, σ, lam, ε, P, hE, hD, hP, hJ, h⟩ := h
  refine ⟨H, _, _, σ, lam, ε, P, hE, hD, hP, hJ, fun x => ?_⟩
  have hσ := hD.2.2.1
  have hG : IsUnit (gramAt D V τ) := (isUnit_iff_isUnit_det _).2 (GlobalTheory.SmoothAutCheck.gramAt_unit V τ)
  have hk' : kᴴ * gramAt D V τ * k = gramAt D V τ := hk
  have hku : IsUnit k := by
    have := congrArg Matrix.det hk'
    rw [det_mul] at this
    rw [isUnit_iff_isUnit_det]
    exact isUnit_of_mul_isUnit_right (this ▸ GlobalTheory.SmoothAutCheck.gramAt_unit V τ)
  have a1 : k * k⁻¹ = 1 := Matrix.mul_nonsing_inv _ ((isUnit_iff_isUnit_det _).1 hku)
  have a2 : k⁻¹ * k = 1 := Matrix.nonsing_inv_mul _ ((isUnit_iff_isUnit_det _).1 hku)
  have b2 : P⁻¹ * P = 1 := Matrix.nonsing_inv_mul _ ((isUnit_iff_isUnit_det _).1 hP)
  have hki : k⁻¹ ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ) := by
    show (k⁻¹)ᴴ * gramAt D V τ * k⁻¹ = gramAt D V τ
    calc (k⁻¹)ᴴ * gramAt D V τ * k⁻¹ = (k⁻¹)ᴴ * (kᴴ * gramAt D V τ * k) * k⁻¹ := by rw [hk']
      _ = (k * k⁻¹)ᴴ * gramAt D V τ * (k * k⁻¹) := by simp only [conjTranspose_mul, Matrix.mul_assoc]
      _ = _ := by rw [a1]; simp
  have hm := GlobalTheory.TypeAtCompare.conj_mem hP hJ hk
  have t0 : HasTypeAll (lieOf (gramAt D V τ)) (Formalism.QuantumDeterminants.UH (gramAt D V τ)) (fun g => σ (P * g * P⁻¹))
      fun g => φ (x * atTau θ V τ k * atTau θ V τ g) := hasTypeAll_iff.2 (h (x * atTau θ V τ k))
  have t1 := hasTypeAll_transport _ H H (fun g => σ (P * g * P⁻¹)) (fun g => σ (P * g * P⁻¹)) _ _ k hG hku hk'
    (opEquiv hσ hm) (fun g hg v => by
      have m1 := GlobalTheory.TypeAtCompare.conj_mem hP hJ hg
      have m2 := GlobalTheory.TypeAtCompare.conj_mem hP hJ (mul_mem_UH (mul_mem_UH hk hg) hki)
      show σ (P * k * P⁻¹) (σ (P * g * P⁻¹) v) = σ (P * (k * g * k⁻¹) * P⁻¹) (σ (P * k * P⁻¹) v)
      rw [← sigma_mul hσ hm m1, ← sigma_mul hσ m2 hm]
      congr 2
      calc P * k * P⁻¹ * (P * g * P⁻¹) = P * k * (P⁻¹ * P) * g * (k⁻¹ * k) * P⁻¹ := by
            rw [a2, Matrix.mul_one]; simp only [Matrix.mul_assoc]
        _ = P * k * g * k⁻¹ * (P⁻¹ * P) * k * P⁻¹ := by rw [b2]; simp only [Matrix.mul_assoc, Matrix.mul_one, Matrix.one_mul]
        _ = _ := by simp only [Matrix.mul_assoc]) _ t0
  obtain ⟨v, h1, ℓ, h2, h3, h4⟩ := hasTypeAll_iff.1 t1
  refine ⟨v, h1, ℓ, h2, h3, fun g hg => ?_⟩
  have e : x * atTau θ V τ k * atTau θ V τ (k⁻¹ * g * k) = x * atTau θ V τ g * atTau θ V τ k := by
    rw [mul_assoc x, mul_assoc x, ← atTau_mul hθ V τ hk (mul_mem_UH (mul_mem_UH hki hg) hk), ← atTau_mul hθ V τ hg hk,
      ← Matrix.mul_assoc, ← Matrix.mul_assoc, a1, Matrix.one_mul]
  have := h4 g hg
  simp only [e] at this
  exact this

theorem isTypeAt_rTr (hθ : IsInfFam θ) {τ τ' : D.what₂.Tau} {S : SPar} {φ : GA D V → ℂ} (h : IsTypeAt θ V τ' S φ)
    {k : Matrix (Fin V.rank) (Fin V.rank) ℂ} (hk : k ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ)) :
    IsTypeAt θ V τ' S (rTr V (atTau θ V τ k) φ) := by
  by_cases c : τ = τ'
  · subst c
    exact isTypeAt_rTr_same hθ h hk
  obtain ⟨H, _, _, σ, lam, ε, P, hE, hD, hP, hJ, h⟩ := h
  refine ⟨H, _, _, σ, lam, ε, P, hE, hD, hP, hJ, fun x => ?_⟩
  obtain ⟨v, h1, ℓ, h2, h3, h4⟩ := h (x * atTau θ V τ k)
  refine ⟨v, h1, ℓ, h2, h3, fun g hg => ?_⟩
  have := h4 g hg
  rw [mul_assoc x, GlobalTheory.PointAtPlaceComm.atTau_comm D θ hθ V τ τ' c k hk g hg, ← mul_assoc x] at this
  exact this

theorem exists_quotient_near (hθ : IsInfFam θ) {τ : D.what₂.Tau} {X : Matrix (Fin V.rank) (Fin V.rank) ℂ}
    (hX : X ∈ lieAt V τ) {φ : GA D V → ℂ} (hφ : IsAutFunSm θ V φ) {C : Set (GA D V)} (hC : IsCompact C) {δ : ℝ}
    (hδ : 0 < δ) : ∃ t : ℝ, ∀ x ∈ C,
      ‖Rder θ V τ X φ x - (((t : ℂ)⁻¹) • (rTr V (oneP θ V τ X t) φ + (-1 : ℂ) • φ)) x‖ < δ := by
  haveI : IsTopologicalGroup (GA D V) := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.topGroupHA _ _
  have hc := (GlobalTheory.CuspLie.isAutFunSm_Rder hθ hX hφ).cont
  have hu := GlobalTheory.Mem.Lift.continuous_oneP hθ hX
  have h0 := GlobalTheory.Mem.Lift.oneP_zero (V := V) (τ := τ) (X := X) hθ
  have hd := GlobalTheory.Mem.Lift.hasDerivAt_oneP hθ hX (GlobalTheory.Mem.Lift.hasDerivAt_Rder hφ.smooth hX)
  set ψ := Rder θ V τ X φ
  have ev : ∀ᶠ t in 𝓝 (0 : ℝ), ∀ x ∈ C, ‖ψ (x * oneP θ V τ X t) - ψ x‖ < δ / 2 := by
    refine hC.eventually_forall_of_forall_eventually fun y _ => ?_
    have cF : Continuous fun z : ℝ × GA D V => ‖ψ (z.2 * oneP θ V τ X z.1) - ψ z.2‖ :=
      ((hc.comp (continuous_snd.mul (hu.comp continuous_fst))).sub (hc.comp continuous_snd)).norm
    refine cF.continuousAt.eventually_lt continuousAt_const ?_
    simp only [h0, mul_one, sub_self, norm_zero]
    linarith
  obtain ⟨η, hη, hb⟩ := Metric.eventually_nhds_iff.1 ev
  refine ⟨η / 2, fun x hx => ?_⟩
  have hp : 0 < η / 2 := by linarith
  have key := norm_image_sub_le_of_norm_deriv_le_segment' (f := fun s : ℝ => φ (x * oneP θ V τ X s) - (s : ℂ) * ψ x)
    (f' := fun s => ψ (x * oneP θ V τ X s) - ψ x) (a := 0) (b := η / 2) (C := δ / 2)
    (fun s _ => by
      have := (hd x s).fun_sub ((Complex.ofRealCLM.hasDerivAt (x := s)).mul_const (ψ x))
      simpa using this.hasDerivWithinAt)
    (fun s hs => (hb (by rw [Real.dist_eq, sub_zero, abs_of_nonneg hs.1]; linarith [hs.2]) x hx).le)
    (η / 2) ⟨hp.le, le_rfl⟩
  set t := η / 2
  have ht : (t : ℂ) ≠ 0 := by exact_mod_cast hp.ne'
  have e : ψ x - (((t : ℂ)⁻¹) • (rTr V (oneP θ V τ X t) φ + (-1 : ℂ) • φ)) x =
      -(t : ℂ)⁻¹ * ((φ (x * oneP θ V τ X t) - (t : ℂ) * ψ x) - (φ (x * oneP θ V τ X 0) - ((0 : ℝ) : ℂ) * ψ x)) := by
    simp only [h0, mul_one, Pi.smul_apply, Pi.add_apply, rTr, smul_eq_mul, Complex.ofReal_zero]
    field_simp
    ring
  rw [e, norm_mul, norm_neg, norm_inv, Complex.norm_real, Real.norm_of_nonneg hp.le, inv_mul_lt_iff₀ hp]
  refine key.trans_lt ?_
  nlinarith

section Sig

variable (hPr : GlobalTheory.FunPr.Hypotheses₂) (hθ : IsInfFam θ) {τ τ' : D.what₂.Tau} {S : SPar} {φ ψ : GA D V → ℂ}
include hPr hθ

theorem hasTypeAt_of (hV : V.SigOK) (hφ : IsAutFunSm θ V φ) (h : IsTypeAt θ V τ S φ) : φ ∈ typeSub θ V τ S :=
  GlobalTheory.SeriesToClosure.hasTypeAt_of_isTypeAt θ V τ S φ hPr.discreteSeriesUpqExists
    (GlobalTheory.Published.discreteSeriesHermitianUnique_iff.1 hPr.discreteSeriesHermitianUnique) hPr.harishChandraModules
    hPr.casselmanWallach hθ hV (goodPar_of_isTypeAt hV h) hφ h

theorem isTypeAt_of (hV : V.SigOK) (h : IsTypeAt θ V τ S φ) (hψ : IsAutFunSm θ V ψ) (h' : ψ ∈ typeSub θ V τ S) :
    IsTypeAt θ V τ S ψ :=
  GlobalTheory.T.automorphicForm_uniformLimit_discreteSeries_series θ V τ S ψ hPr.discreteSeriesUpqExists
    (GlobalTheory.Published.discreteSeriesHermitianUnique_iff.1 hPr.discreteSeriesHermitianUnique) hPr.harishChandraModules
    hPr.casselmanWallach hθ hV (goodPar_of_isTypeAt hV h) hψ h'

theorem isTypeAt_add_sig (hV : V.SigOK) (hφ : IsAutFunSm θ V φ) (hψ : IsAutFunSm θ V ψ) (h : IsTypeAt θ V τ S φ)
    (h' : IsTypeAt θ V τ S ψ) : IsTypeAt θ V τ S (φ + ψ) :=
  isTypeAt_of hPr hθ hV h (GlobalTheory.Mem.AutSpace.isAutFunSm_add hφ hψ)
    (add_mem (hasTypeAt_of hPr hθ hV hφ h) (hasTypeAt_of hPr hθ hV hψ h'))

theorem isTypeAt_Rder_sig (hV : V.SigOK) {X : Matrix (Fin V.rank) (Fin V.rank) ℂ} (hX : X ∈ lieAt V τ)
    (hφ : IsAutFunSm θ V φ) (h : IsTypeAt θ V τ' S φ) : IsTypeAt θ V τ' S (Rder θ V τ X φ) := by
  refine isTypeAt_of hPr hθ hV h (GlobalTheory.CuspLie.isAutFunSm_Rder hθ hX hφ) fun C hC δ hδ => ?_
  obtain ⟨t, ht⟩ := exists_quotient_near hθ hX hφ hC (half_pos hδ)
  have hk := GlobalTheory.Mem.Lift.exp_mem hX t
  have m1 : rTr V (oneP θ V τ X t) φ ∈ typeSub θ V τ' S :=
    hasTypeAt_of hPr hθ hV (isAutFunSm_rTr_atTau D θ hθ V φ hφ τ _ hk) (isTypeAt_rTr hθ h hk)
  have m2 : ((t : ℂ)⁻¹) • (rTr V (oneP θ V τ X t) φ + (-1 : ℂ) • φ) ∈ typeSub θ V τ' S :=
    Submodule.smul_mem _ _ (add_mem m1 (Submodule.smul_mem _ _ (hasTypeAt_of hPr hθ hV hφ h)))
  obtain ⟨χ, hχ, h2⟩ := m2 C hC (δ / 2) (half_pos hδ)
  refine ⟨χ, hχ, fun x hx => ?_⟩
  have := norm_sub_le_norm_sub_add_norm_sub (Rder θ V τ X φ x)
    ((((t : ℂ)⁻¹) • (rTr V (oneP θ V τ X t) φ + (-1 : ℂ) • φ)) x) (χ x)
  linarith [ht x hx, h2 x hx]

theorem isTypeAt_add (hφ : IsAutFunSm θ V φ) (hψ : IsAutFunSm θ V ψ) (h : IsTypeAt θ V τ S φ)
    (h' : IsTypeAt θ V τ S ψ) : IsTypeAt θ V τ S (φ + ψ) := by
  obtain ⟨s, hs⟩ := exists_sigOK V
  exact isTypeAt_add_sig (V := GlobalTheory.SmoothAutCheck.reSig V s) hPr hθ hs
    ((GlobalTheory.SmoothAutCheck.isAutFunSm_reSig θ V s φ).2 hφ) ((GlobalTheory.SmoothAutCheck.isAutFunSm_reSig θ V s ψ).2 hψ) h h'

theorem isTypeAt_Rder {X : Matrix (Fin V.rank) (Fin V.rank) ℂ} (hX : X ∈ lieAt V τ)
    (hφ : IsAutFunSm θ V φ) (h : IsTypeAt θ V τ' S φ) : IsTypeAt θ V τ' S (Rder θ V τ X φ) := by
  obtain ⟨s, hs⟩ := exists_sigOK V
  exact isTypeAt_Rder_sig (V := GlobalTheory.SmoothAutCheck.reSig V s) hPr hθ hs hX
    ((GlobalTheory.SmoothAutCheck.isAutFunSm_reSig θ V s φ).2 hφ) h

end Sig

variable {S : D.what₂.Tau → SPar}

def formSub (hPr : GlobalTheory.FunPr.Hypotheses₂) (hθ : IsInfFam θ) (M : DSModel V S) : Submodule ℂ (GA D V → ℂ) where
  carrier := {f | IsKFinCuspOfType θ M f}
  zero_mem' := ⟨Formalism.IndefR.Mult.isAutFunSm_zero θ V, Formalism.IndefR.Mult.isCuspFun_zero V,
    fun τ => (GlobalTheory.TypeAtTest.isTypeAt_zero θ V).2
      ⟨M.H τ, _, _, M.σ τ, M.lam τ, M.ε τ, M.fr τ, M.enum τ, M.ds τ, M.fr_unit τ, M.fr_gram τ⟩,
    ⊥, inferInstance, zero_mem _, fun τ g _ _ h hh => by
      rw [Submodule.mem_bot] at hh ⊢
      subst hh
      rfl⟩
  add_mem' := by
    rintro a b ⟨a1, a2, a3, W, hW, a4, a5⟩ ⟨b1, b2, b3, W', hW', b4, b5⟩
    refine ⟨GlobalTheory.Mem.AutSpace.isAutFunSm_add a1 b1, GlobalTheory.MultMem.isCuspFun_add a1.toIsAutFun b1.toIsAutFun a2 b2,
      fun τ => isTypeAt_add hPr hθ a1 b1 (a3 τ) (b3 τ), W ⊔ W', inferInstance, Submodule.add_mem_sup a4 b4,
      fun τ g hg hk h hh => ?_⟩
    obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.1 hh
    exact Submodule.add_mem_sup (a5 τ g hg hk y hy) (b5 τ g hg hk z hz)
  smul_mem' := by
    rintro c a ⟨a1, a2, a3, W, hW, a4, a5⟩
    exact ⟨GlobalTheory.Mem.AutSpace.isAutFunSm_smul c a1, Formalism.IndefR.Mult.isCuspFun_smul V a2 c,
      fun τ => GlobalTheory.Mem.Th.isTypeAt_smul c (a3 τ), W, hW, W.smul_mem c a4, a5⟩

theorem isGKSub_formSub (hPr : GlobalTheory.FunPr.Hypotheses₂) (hθ : IsInfFam θ) (M : DSModel V S) :
    IsGKSub θ M (formSub hPr hθ M) where
  k τ g hg f hf := by
    obtain ⟨a1, a2, a3, W, hW, a4, a5⟩ := hf
    exact ⟨isAutFunSm_rTr_atTau D θ hθ V f a1 τ g hg.1, GlobalTheory.Cusp.isCuspFun_rTr a2 _,
      fun τ' => isTypeAt_rTr hθ (a3 τ') hg.1, W, hW, a5 τ g hg.1 hg.2 f a4, a5⟩
  lie τ X hX f hf := by
    obtain ⟨a1, a2, a3, W, hW, a4, a5⟩ := hf
    refine ⟨GlobalTheory.CuspLie.isAutFunSm_Rder hθ hX a1, GlobalTheory.CuspLie.isCuspFun_Rder hθ hX a1 a2,
      fun τ' => isTypeAt_Rder hPr hθ hX a1 (a3 τ'),
      (Submodule.map₂ (derEnd hθ τ) ⊤ (W.comap (SmFun θ V).subtype)).map (SmFun θ V).subtype,
      Module.Finite.iff_fg.2 ((Submodule.FG.map₂ _ Module.Finite.fg_top (GlobalTheory.CuspLie.fg_comap hW)).map _),
      ⟨derEnd hθ τ X ⟨f, a1.smooth⟩,
        Submodule.apply_mem_map₂ _ (Submodule.mem_top (x := X)) (n := (⟨f, a1.smooth⟩ : SmFun θ V)) a4,
        GlobalTheory.CuspLie.derEnd_coe hθ hX ⟨f, a1.smooth⟩⟩, fun τ' g hg hk => ?_⟩
    have hr := isRealPt_atTau hθ τ' hg
    have hi : IsRealPt θ (atTau θ V τ' g)⁻¹ :=
      ⟨inv_mem hr.1, GlobalTheory.FockCompare.RealAction.infMat_mem_UH hθ V _⟩
    set k := atTau θ V τ' g
    have hle : Submodule.map₂ (derEnd hθ τ) ⊤ (W.comap (SmFun θ V).subtype) ≤
        (((Submodule.map₂ (derEnd hθ τ) ⊤ (W.comap (SmFun θ V).subtype)).map (SmFun θ V).subtype).comap
          (rTrLin k)).comap (SmFun θ V).subtype := by
      refine Submodule.map₂_le.2 fun Z _ u hu => ?_
      refine ⟨_, Submodule.apply_mem_map₂ _ (Submodule.mem_top (x := adAt θ k⁻¹ τ Z))
        (n := ⟨rTr V k u.1, rTr_mem hθ hr u.2⟩) (a5 τ' g hg hk _ hu), ?_⟩
      show RderC θ V τ (adAt θ k⁻¹ τ Z) (rTr V k u.1) = rTr V k (RderC θ V τ Z u.1)
      funext y
      have := congrFun (RderC_rTr hθ hi τ Z (rTr V k u.1)) (y * k)
      rw [show rTr V k⁻¹ (rTr V k u.1) = u.1 from funext fun y => by simp [rTr]] at this
      rw [rTr, this, rTr, mul_inv_cancel_right]
    rintro _ ⟨u, hu, rfl⟩
    exact hle hu

theorem isKFinCuspOfType_of_mem_gkGen : GlobalTheory.FunPr.Hypotheses₂ → ∀ {D : D7} (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (V : HSp D)
    (S : D.what₂.Tau → SPar) (M : Formalism.IndefR.Mult.DSModel V S), IsInfFam (D := D) θ →
    ∀ ψ : GA D V → ℂ, GlobalTheory.CuspGK.IsKFinCuspOfType θ M ψ → ∀ f ∈ GlobalTheory.CuspGK.gkGen θ M ψ, GlobalTheory.CuspGK.IsKFinCuspOfType θ M f :=
  fun hPr _ θ _ _ M hθ _ hψ _ hf => gkGen_le θ M (A := formSub hPr hθ M) hψ (isGKSub_formSub hPr hθ M) hf

end GlobalTheory.CuspGKForms

end
