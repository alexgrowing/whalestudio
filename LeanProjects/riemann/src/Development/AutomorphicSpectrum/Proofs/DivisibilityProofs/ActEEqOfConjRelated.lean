import Mathlib
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.EdgesRouteSmall
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DsExistsOfDiscreteSeriesExists
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.UnifModGrowthOfIsUnifModerate
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NotIsCompactUnivFv
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.UnitaryConjugation
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.LevelPlusSubgroup
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil
import Formalism.LocalToGlobal.IndefiniteReal.BaseLiftsPackageOfPrimitiveLinks
import Formalism.LocalToGlobal.IndefiniteReal.RationalAdjoints.RatZOfTests
import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGoodPlaceTranslateCombinationLatticeIndica
import Development.WeilBound.CoreStatements.TorusUniformisation.SiegelCompactSupport.ExistsRouteDatumTranslationCombinationGoodPlace
import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.AdlEqZeroOfMemNbhd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSplittingSplitOm
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open Formalism.IndefR.Mult IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.CompanionTheory.Ar.RT
open scoped TensorProduct ComplexConjugate GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.SplitFlip GlobalTheory.SplitWeil
open ValuativeRel

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.SvN

open Matrix
open scoped PositivityTheory.Member.ZakTransform
open PositivityTheory.Member.ZakTransform (schr_tens lift lift_tens lift_schr lift_adm lift_lift lift_one lift_mem psv psv_apply evP offP
  offP_eq evalEmbedding_smul evalPoints_add Indep indep_pure ep ep_mul ep_ep ev_ep at_iff schr_zero schr_mem_SB cont_at spM spM_fst spM_snd
  spM_off mat_ext coB ev_symp map_smul_piW map_cA_piW incM_piW ev_dot stdF stdF_mem sub sub_mem hasSig_det schur
  exists_bump rest_zero tens_at pure_update pure_mem good_std Good)
open PositivityTheory.Member.ZakTransform.Z (psi_re re trace_emb)
open GlobalTheory.EmbChart (atPlace evFin_atPlace)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (AE cA incM UA Spc Model Rep mat UAt At Rest Acts tens piW)

theorem isCharAF_of_isStd {F : Type} [Field F] [NumberField F] {ψ : AddChar (AF F) ℂ}
    (h : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsStd ψ) : IsCharAF F ψ := by
  obtain ⟨K, hK, hx⟩ := Formalism.IndefR.Eqv.G5.adl_cocompact (F := F)
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn h.1.continuousOn
  have bd : ∀ x, ‖ψ x‖ ≤ C := fun x => by
    obtain ⟨a, ha⟩ := hx x
    have e : ψ x = ψ (x - algebraMap F _ a) := by
      have : x = (x - algebraMap F _ a) + algebraMap F _ a := by ring
      conv_lhs => rw [this, AddChar.map_add_eq_mul, h.2.1 a, mul_one]
    rw [e]
    exact hC _ ha
  have le1 : ∀ x, ‖ψ x‖ ≤ 1 := fun x => by
    by_contra hlt
    obtain ⟨m, hm⟩ := pow_unbounded_of_one_lt C (not_le.1 hlt)
    have := bd (m • x)
    rw [AddChar.map_nsmul_eq_pow, norm_pow] at this
    linarith
  have hn : ∀ x, ‖ψ x‖ = 1 := fun x => by
    have e : ‖ψ x‖ * ‖ψ (-x)‖ = 1 := by
      rw [← norm_mul, ← AddChar.map_add_eq_mul, add_neg_cancel, AddChar.map_zero_eq_one, norm_one]
    nlinarith [le1 x, le1 (-x), norm_nonneg (ψ x), norm_nonneg (ψ (-x))]
  refine ⟨h.1, hn, h.2.1, ?_⟩
  have hN : ((Module.finrank ℚ F : ℕ) : ℝ) ≠ 0 := by
    exact_mod_cast (Module.finrank_pos (R := ℚ) (M := F)).ne'
  have tr1 : Algebra.trace ℝ (mixedEmbedding.mixedSpace F) 1 = (Module.finrank ℚ F : ℝ) := by
    have := trace_emb (F := F) 1
    have e1 : Algebra.trace ℚ F 1 = (Module.finrank ℚ F : ℚ) := by
      have := Algebra.trace_algebraMap (S := F) (1 : ℚ)
      simpa using this
    rw [map_one, e1] at this
    simpa using this
  refine ⟨re F (((2 * (Module.finrank ℚ F : ℝ))⁻¹ : ℝ) • (1 : mixedEmbedding.mixedSpace F)), ?_⟩
  rw [psi_re h, map_smul, tr1, smul_eq_mul]
  have : ((2 * (Module.finrank ℚ F : ℝ))⁻¹ * (Module.finrank ℚ F : ℝ)) = (2⁻¹ : ℝ) := by
    field_simp
  rw [this]
  push_cast
  have e : -(2 * (Real.pi : ℂ) * Complex.I) * 2⁻¹ = -(Real.pi * Complex.I) := by ring
  rw [e, Complex.exp_neg, Complex.exp_pi_mul_I]
  norm_num

section Inverse

end Inverse

def gT {k : Type} [CommRing k] {n : ℕ} (g : GL (Fin n) k) : GL (Fin n) k :=
  ⟨g.1ᵀ, (g⁻¹).1ᵀ, by rw [← transpose_mul, Units.inv_mul, transpose_one],
    by rw [← transpose_mul, Units.mul_inv, transpose_one]⟩

section Local

variable {F : Type} [Field F] [NumberField F] {v : HeightOneSpectrum (𝓞 F)} {n d : ℕ}

def cj (I : ((Fin n × Fin d → Fv F v) → ℂ) →ₗ[ℂ] (Matrix (Fin n) (Fin d) (Fv F v) → ℂ))
    (J : (Matrix (Fin n) (Fin d) (Fv F v) → ℂ) →ₗ[ℂ] ((Fin n × Fin d → Fv F v) → ℂ)) (γ : GL (Fin n) (Fv F v)) :
    Module.End ℂ ((Fin n × Fin d → Fv F v) → ℂ) := J ∘ₗ sub γ ∘ₗ I

variable {I : ((Fin n × Fin d → Fv F v) → ℂ) →ₗ[ℂ] (Matrix (Fin n) (Fin d) (Fv F v) → ℂ)}
  {J : (Matrix (Fin n) (Fin d) (Fv F v) → ℂ) →ₗ[ℂ] ((Fin n × Fin d → Fv F v) → ℂ)}

theorem cj_mem (hI : ∀ φ ∈ GlobalTheory.WeilM.SB (Fin n × Fin d → Fv F v), I φ ∈ GlobalTheory.WeilM.SB (Matrix (Fin n) (Fin d) (Fv F v)) ∧ J (I φ) = φ)
    (hJ : ∀ f ∈ GlobalTheory.WeilM.SB (Matrix (Fin n) (Fin d) (Fv F v)), J f ∈ GlobalTheory.WeilM.SB (Fin n × Fin d → Fv F v) ∧ I (J f) = f)
    (γ : GL (Fin n) (Fv F v)) {φ : (Fin n × Fin d → Fv F v) → ℂ} (h : φ ∈ GlobalTheory.WeilM.SB _) : cj I J γ φ ∈ GlobalTheory.WeilM.SB _ :=
  (hJ _ (sub_mem γ (hI φ h).1)).1

theorem I_cj (hI : ∀ φ ∈ GlobalTheory.WeilM.SB (Fin n × Fin d → Fv F v), I φ ∈ GlobalTheory.WeilM.SB (Matrix (Fin n) (Fin d) (Fv F v)) ∧ J (I φ) = φ)
    (hJ : ∀ f ∈ GlobalTheory.WeilM.SB (Matrix (Fin n) (Fin d) (Fv F v)), J f ∈ GlobalTheory.WeilM.SB (Fin n × Fin d → Fv F v) ∧ I (J f) = f)
    (γ : GL (Fin n) (Fv F v)) {φ : (Fin n × Fin d → Fv F v) → ℂ} (h : φ ∈ GlobalTheory.WeilM.SB _) (Y : Matrix (Fin n) (Fin d) (Fv F v)) :
    I (cj I J γ φ) Y = I φ (γ.1 * Y) :=
  congrFun (hJ _ (sub_mem γ (hI φ h).1)).2 Y

theorem inj_I (hI : ∀ φ ∈ GlobalTheory.WeilM.SB (Fin n × Fin d → Fv F v), I φ ∈ GlobalTheory.WeilM.SB (Matrix (Fin n) (Fin d) (Fv F v)) ∧ J (I φ) = φ)
    {φ φ' : (Fin n × Fin d → Fv F v) → ℂ} (h : φ ∈ GlobalTheory.WeilM.SB _) (h' : φ' ∈ GlobalTheory.WeilM.SB _) (e : I φ = I φ') : φ = φ' := by
  rw [← (hI φ h).2, e, (hI φ' h').2]

theorem cj_cj_inv (hI : ∀ φ ∈ GlobalTheory.WeilM.SB (Fin n × Fin d → Fv F v), I φ ∈ GlobalTheory.WeilM.SB (Matrix (Fin n) (Fin d) (Fv F v)) ∧ J (I φ) = φ)
    (hJ : ∀ f ∈ GlobalTheory.WeilM.SB (Matrix (Fin n) (Fin d) (Fv F v)), J f ∈ GlobalTheory.WeilM.SB (Fin n × Fin d → Fv F v) ∧ I (J f) = f)
    (γ : GL (Fin n) (Fv F v)) {φ : (Fin n × Fin d → Fv F v) → ℂ} (h : φ ∈ GlobalTheory.WeilM.SB _) : cj I J γ (cj I J γ⁻¹ φ) = φ :=
  inj_I hI (cj_mem hI hJ _ (cj_mem hI hJ _ h)) h (funext fun Y => by
    rw [I_cj hI hJ _ (cj_mem hI hJ _ h), I_cj hI hJ _ h, ← Matrix.mul_assoc, Units.inv_mul, Matrix.one_mul])

theorem cj_comm (ψv : AddChar (Fv F v) ℂ) (hc : Continuous ψv)
    (e : (Matrix (Fin n) (Fin d) (Fv F v) × Matrix (Fin n) (Fin d) (Fv F v)) ≃ₗ[Fv F v] (Fin n × Fin d → Fv F v) × (Fin n × Fin d → Fv F v))
    (he : ∀ w w', (e w).1 ⬝ᵥ (e w').2 - (e w').1 ⬝ᵥ (e w).2 = trace (w.1 * w'.2ᵀ) - trace (w'.1 * w.2ᵀ))
    (hI : ∀ φ ∈ GlobalTheory.WeilM.SB (Fin n × Fin d → Fv F v), I φ ∈ GlobalTheory.WeilM.SB (Matrix (Fin n) (Fin d) (Fv F v)) ∧ J (I φ) = φ)
    (hJ : ∀ f ∈ GlobalTheory.WeilM.SB (Matrix (Fin n) (Fin d) (Fv F v)), J f ∈ GlobalTheory.WeilM.SB (Fin n × Fin d → Fv F v) ∧ I (J f) = f)
    (htr : ∀ φ ∈ GlobalTheory.WeilM.SB (Fin n × Fin d → Fv F v), ∀ Y₀ Y, I (schr ψv (e (Y₀, 0)) φ) Y = I φ (Y + Y₀))
    (hmod : ∀ φ ∈ GlobalTheory.WeilM.SB (Fin n × Fin d → Fv F v), ∀ Z Y, I (schr ψv (e (0, Z)) φ) Y = ψv (trace (Y * Zᵀ)) * I φ Y)
    (γ : GL (Fin n) (Fv F v)) {φ : (Fin n × Fin d → Fv F v) → ℂ} (h : φ ∈ GlobalTheory.WeilM.SB _) (Y₀ Z : Matrix (Fin n) (Fin d) (Fv F v)) :
    cj I J γ (schr ψv (e (γ.1 * Y₀, (γ⁻¹).1ᵀ * Z)) φ) = schr ψv (e (Y₀, Z)) (cj I J γ φ) := by
  have hfull : ∀ φ ∈ GlobalTheory.WeilM.SB (Fin n × Fin d → Fv F v), ∀ Y₀ Z Y, I (schr ψv (e (Y₀, Z)) φ) Y =
      ψv (-(⅟2 * trace (Y₀ * Zᵀ))) * (ψv (trace ((Y + Y₀) * Zᵀ)) * I φ (Y + Y₀)) := fun φ hφ Y₀ Z Y => by
    have := congrArg (fun f => I f Y) (GlobalTheory.WeilM.schr_schr ψv (e (Y₀, 0)) (e (0, Z)) φ)
    simp only [he, ← map_add, Prod.mk_add_mk, add_zero, zero_add, map_smul, Pi.smul_apply, smul_eq_mul, Matrix.zero_mul,
      trace_zero, sub_zero] at this
    rw [htr _ (schr_mem_SB hc _ hφ), hmod _ hφ] at this
    rw [this, ← mul_assoc, ← AddChar.map_add_eq_mul, neg_add_cancel, AddChar.map_zero_eq_one, one_mul]
  refine inj_I hI (cj_mem hI hJ _ (schr_mem_SB hc _ h)) (schr_mem_SB hc _ (cj_mem hI hJ _ h)) (funext fun Y => ?_)
  have t : ∀ A : Matrix (Fin n) (Fin d) (Fv F v), trace (γ.1 * A * ((γ⁻¹).1ᵀ * Z)ᵀ) = trace (A * Zᵀ) := fun A => by
    rw [transpose_mul, transpose_transpose, Matrix.mul_assoc, trace_mul_comm, ← Matrix.mul_assoc, Matrix.mul_assoc,
      Units.inv_mul, Matrix.mul_one]
  rw [I_cj hI hJ _ (schr_mem_SB hc _ h), hfull _ h, hfull _ (cj_mem hI hJ _ h), I_cj hI hJ _ h, ← Matrix.mul_add, t, t]

end Local

section Split

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
  {v : HeightOneSpectrum (𝓞 F)} {n d : ℕ} {X : Spc F E n} {W : Spc F E d}

theorem indep_of {κ : Type} [Fintype κ] {r : (κ → AF F) → ℂ}
    (h : ∀ x z, At (evFin F v) z → r (x + z) = r x) : Indep v r := fun x t =>
  h x _ ((at_iff _).2 (funext fun i => by
    show ep v * atPlace v (t i) = _
    rw [ep_mul, evFin_atPlace]))

theorem acts_schr (M : Model σ X W) (ψ : AddChar (AF F) ℂ) {u : Matrix (Fin n) (Fin d) (AE F E)} (hu : ep v • u = u)
    (φ : (Fin n × Fin d → Fv F v) → ℂ) :
    Acts (evFin F v) (M.co.rho ψ u) φ (schr (psv v ψ) (evP v (M.co.e u)) φ) := by
  intro r hr
  have hw : ep v • M.co.e u = M.co.e u := by rw [← map_smul, hu]
  show schr ψ (M.co.e u) _ = _
  rw [schr_tens ψ _ _ (indep_of hr.1), offP_eq, sub_smul, hw, one_smul, sub_self, schr_zero]

end Split

section Main

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
  {v : HeightOneSpectrum (𝓞 F)} {n d : ℕ} {X : Spc F E n} {W : Spc F E d}

theorem coords_move (t : E →ₐ[F] Fv F v) (k : UA σ X.J) (g : GL (Fin n) (Fv F v))
    (hg : (mat k).map (piW t) = g.1) (u : Matrix (Fin n) (Fin d) (AE F E)) :
    coB σ X W t (mat k * u) = ((gT g)⁻¹).1 * coB σ X W t u ∧
      -(mat k * u).map (piW t) = (((gT g)⁻¹)⁻¹).1ᵀ * (-u.map (piW t)) := by
  have hU : (mat k)ᵀ * incM F X.J * (mat k).map (cA σ) = incM F X.J := k.2
  have hP : g.1ᵀ * X.J.map t * (mat k).map (piW (t.comp σ)) = X.J.map t := by
    have := congrArg (fun A => A.map (piW t)) hU
    simp only [Matrix.map_mul, transpose_map, incM_piW, map_cA_piW, hg] at this
    exact this
  have hP' : X.J.map t * (mat k).map (piW (t.comp σ)) = (g⁻¹).1ᵀ * X.J.map t := by
    have h2 : (g⁻¹).1ᵀ * g.1ᵀ = 1 := by rw [← transpose_mul, Units.mul_inv, transpose_one]
    calc X.J.map t * (mat k).map (piW (t.comp σ))
        = (g⁻¹).1ᵀ * (g.1ᵀ * X.J.map t * (mat k).map (piW (t.comp σ))) := by
          rw [Matrix.mul_assoc g.1ᵀ, ← Matrix.mul_assoc, h2, Matrix.one_mul]
      _ = _ := by rw [hP]
  constructor
  · show -(X.J.map t * (mat k * u).map (piW (t.comp σ)) * (W.J.map t)ᵀ) =
      (g⁻¹).1ᵀ * -(X.J.map t * u.map (piW (t.comp σ)) * (W.J.map t)ᵀ)
    rw [Matrix.map_mul, ← Matrix.mul_assoc, hP', Matrix.mul_neg]
    simp only [Matrix.mul_assoc]
  · rw [inv_inv]
    show -(mat k * u).map (piW t) = g.1ᵀᵀ * _
    rw [Matrix.map_mul, hg, transpose_transpose, Matrix.mul_neg]

theorem exists_scalar [IsTotallyReal F] (t : E →ₐ[F] Fv F v) (M : Model σ X W) (ψ : AddChar (AF F) ℂ)
    (hψ : IsCharAF F ψ) (hstd : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsStd ψ) (hc : Continuous (psv v ψ)) (om : Rep σ X W)
    (hom : IsUSplitting (adeleClass F) ψ M.co (actAB (cA σ)) om)
    (e : (Matrix (Fin n) (Fin d) (Fv F v) × Matrix (Fin n) (Fin d) (Fv F v)) ≃ₗ[Fv F v] (Fin n × Fin d → Fv F v) × (Fin n × Fin d → Fv F v))
    (he : ∀ w w', (e w).1 ⬝ᵥ (e w').2 - (e w').1 ⬝ᵥ (e w).2 = trace (w.1 * w'.2ᵀ) - trace (w'.1 * w.2ᵀ))
    (key : ∀ w, e (coB σ X W t w, -w.map (piW t)) = evP v (M.co.e w))
    {I : ((Fin n × Fin d → Fv F v) → ℂ) →ₗ[ℂ] (Matrix (Fin n) (Fin d) (Fv F v) → ℂ)} {J : (Matrix (Fin n) (Fin d) (Fv F v) → ℂ) →ₗ[ℂ] ((Fin n × Fin d → Fv F v) → ℂ)}
    (hI : ∀ φ ∈ GlobalTheory.WeilM.SB (Fin n × Fin d → Fv F v), I φ ∈ GlobalTheory.WeilM.SB (Matrix (Fin n) (Fin d) (Fv F v)) ∧ J (I φ) = φ)
    (hJ : ∀ f ∈ GlobalTheory.WeilM.SB (Matrix (Fin n) (Fin d) (Fv F v)), J f ∈ GlobalTheory.WeilM.SB (Fin n × Fin d → Fv F v) ∧ I (J f) = f)
    (htr : ∀ φ ∈ GlobalTheory.WeilM.SB (Fin n × Fin d → Fv F v), ∀ Y₀ Y, I (schr (psv v ψ) (e (Y₀, 0)) φ) Y = I φ (Y + Y₀))
    (hmod : ∀ φ ∈ GlobalTheory.WeilM.SB (Fin n × Fin d → Fv F v), ∀ Z Y, I (schr (psv v ψ) (e (0, Z)) φ) Y =
      psv v ψ (trace (Y * Zᵀ)) * I φ Y)
    (k : UA σ X.J) (g : GL (Fin n) (Fv F v)) (hk : k ∈ UAt σ X (evFin F v)) (hg : (mat k).map (piW t) = g.1) :
    ∃ a : ℂ, ∀ Φ ∈ schA F (Fin n × Fin d), om (k, 1) Φ = a • lift v (cj I J (gT g)) Φ := by
  have hS := fun (γ : GL (Fin n) (Fv F v)) φ (h : φ ∈ GlobalTheory.WeilM.SB _) => cj_mem hI hJ γ h
  have hk' : ep v • (mat k - 1) = mat k - 1 := (at_iff _).1 hk
  have e1 : ∀ u : Matrix (Fin n) (Fin d) (AE F E), actAB (cA σ) (k, (1 : UA σ W.J)) u = mat k * u := fun u =>
    (congrArg _ transpose_one).trans (Matrix.mul_one _)
  have hoff : ∀ u : Matrix (Fin n) (Fin d) (AE F E), (1 - ep v) • (mat k * u) = (1 - ep v) • u := fun u => by
    have h0 : (1 - ep v) • (mat k - 1) = 0 := by rw [sub_smul, one_smul, hk', sub_self]
    have : mat k * u = (mat k - 1) * u + u := by rw [Matrix.sub_mul, Matrix.one_mul, sub_add_cancel]
    rw [this, smul_add, ← Matrix.smul_mul, h0, Matrix.zero_mul, zero_add]
  obtain ⟨a, ha⟩ := schur F ψ hψ hstd (lift v (cj I J (gT g)⁻¹) * om (k, 1))
    (fun l hl => hom.adm _ _ (lift_adm (hS _) l hl)) fun w Φ hΦ => by
      obtain ⟨u, rfl⟩ := M.co.e.surjective w
      have h1 : om (k, 1) (schr ψ (M.co.e u) Φ) = schr ψ (M.co.e (mat k * u)) (om (k, 1) Φ) := by
        have := hom.impl (k, 1) u Φ hΦ
        rwa [e1] at this
      rw [Module.End.mul_apply, Module.End.mul_apply, h1]
      refine lift_schr ψ ?_ (fun φ hφ => ?_) (hom.pres _ Φ hΦ)
      · rw [offP_eq, offP_eq, ← map_smul, ← map_smul, hoff]
      · obtain ⟨m1, m2⟩ := coords_move (W := W) t k g hg u
        rw [← key, ← key, m1, m2]
        exact cj_comm _ hc e he hI hJ htr hmod _ hφ _ _
  refine ⟨a, fun Φ hΦ => ?_⟩
  rw [← map_smul, ← ha Φ hΦ, Module.End.mul_apply,
    lift_lift (S'' := 1) (hS _) (fun φ h => cj_cj_inv hI hJ _ h) (hom.pres _ Φ hΦ), lift_one]

end Main

end GlobalTheory.CompanionTheory.Ar.SvN
