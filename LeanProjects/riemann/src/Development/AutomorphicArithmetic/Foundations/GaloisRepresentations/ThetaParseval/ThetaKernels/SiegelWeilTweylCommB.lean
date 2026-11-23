import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.SchrodingerCommutation.TthetaComm
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.SplitStab
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.IsLatRepL
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilDatumProperties
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilTweylBase
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilTweylCommA
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilTweylComm

set_option synthInstance.maxHeartbeats 200000

section
set_option linter.unusedSectionVars false
noncomputable section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl PositivityTheory.Rg.Sw
namespace PositivityTheory.SiegelWeilFormula.tweyl
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
variable (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ)
theorem comm_k (hT : _root_.PositivityTheory.SiegelWeilFormula.TBij_k) (g : UA σ d.A.J) : ∀ Φ ∈ d.sch, ∀ x, d.om x (d.S g Φ) = d.S g (d.om x Φ) := by
  classical
  choose cf hcf using _root_.PositivityTheory.SiegelWeilFormula.tweyl.exists_scalar_k d g
  have hsp : ∀ y, ∀ φ ∈ schA F d.κ, d.om y φ ∈ schA F d.κ := fun y φ hφ => (_root_.PositivityTheory.SiegelWeilFormula.tweyl.hO_k d).pres y φ hφ
  have hinv : ∀ y (φ : d.Fn), d.om y (d.om y⁻¹ φ) = φ := fun y φ => by
    rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
  have hSinv : ∀ φ : d.Fn, d.S g⁻¹ (d.S g φ) = φ := fun φ => by
    rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
  have hSinv' : ∀ φ : d.Fn, d.S g (d.S g⁻¹ φ) = φ := fun φ => by
    rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
  obtain ⟨φz, hφz, hφz0⟩ := GlobalTheory.T.exists_adelicSchwartz_ne_zero_at_origin F d.κ
  have huniq : ∀ y (c : ℂ), (∀ φ ∈ schA F d.κ, (d.S g * d.om y * d.S g⁻¹) φ = c • d.om y φ) → c = cf y :=
    fun y c hc => by
      have h1 := hc _ (hsp y⁻¹ φz hφz)
      rw [hcf y _ (hsp y⁻¹ φz hφz), hinv] at h1
      have h2 := congrFun h1 0
      simp only [Pi.smul_apply, smul_eq_mul] at h2
      exact (mul_right_cancel₀ hφz0 h2).symm
  have hmul : ∀ y z, cf (y * z) = cf y * cf z := fun y z => (huniq (y * z) _ fun φ hφ => by
    have hR : (d.S g * d.om (y * z) * d.S g⁻¹) φ =
        (d.S g * d.om y * d.S g⁻¹) ((d.S g * d.om z * d.S g⁻¹) φ) := by
      simp only [Module.End.mul_apply, map_mul, hSinv]
    rw [hR, hcf z φ hφ, map_smul, hcf y _ (hsp z φ hφ), smul_smul, map_mul, Module.End.mul_apply, mul_comm]).symm
  have hone : cf 1 = 1 := (huniq 1 1 fun φ _ => by
    simp only [Module.End.mul_apply, map_one, Module.End.one_apply, hSinv', one_smul]).symm
  let cM : d.G →* ℂ := { toFun := cf, map_one' := hone, map_mul' := hmul }
  let c := cM.toHomUnits
  have hcv : ∀ p, ((c p : ℂˣ) : ℂ) = cf p := fun p => rfl
  have hcont_cf : Continuous cf := by
    refine continuous_iff_continuousAt.2 fun p₀ => ?_
    have hφ := hsp p₀⁻¹ φz hφz
    have hf := (_root_.PositivityTheory.SiegelWeilFormula.tweyl.hO_k d).cont _ (GlobalTheory.WeilSchUnique.evalZero_mem_adelicSchwartzAdmittedForms d.κ) _ hφ
    have hh := (_root_.PositivityTheory.SiegelWeilFormula.tweyl.hO_k d).cont _ ((_root_.PositivityTheory.SiegelWeilFormula.tweyl.hS_k d).adm g _ (GlobalTheory.WeilSchUnique.evalZero_mem_adelicSchwartzAdmittedForms d.κ)) _ ((_root_.PositivityTheory.SiegelWeilFormula.tweyl.hS_k d).pres g⁻¹ _ hφ)
    simp only [LinearMap.proj_apply, LinearMap.comp_apply] at hf hh
    have h0 : d.om p₀ (d.om p₀⁻¹ φz) 0 ≠ 0 := by rw [hinv]; exact hφz0
    refine (hh.continuousAt.div hf.continuousAt h0).congr ?_
    filter_upwards [hf.continuousAt.eventually_ne h0] with p hp
    show d.S g (d.om p (d.S g⁻¹ (d.om p₀⁻¹ φz))) 0 / d.om p (d.om p₀⁻¹ φz) 0 = cf p
    have e := hcf p _ hφ
    simp only [Module.End.mul_apply] at e
    rw [e]
    simp only [Pi.smul_apply, smul_eq_mul]
    field_simp
  have hcont : Continuous c := by
    refine Units.continuous_iff.2 ⟨hcont_cf, ?_⟩
    have : (fun p => ((c p)⁻¹ : ℂˣ).val) = fun p => (cf p)⁻¹ := funext fun p => by
      rw [Units.val_inv_eq_inv_val, hcv]
    rw [this]
    exact hcont_cf.inv₀ fun p => by rw [← hcv]; exact (c p).ne_zero
  obtain ⟨φl, hφl, hl0⟩ := _root_.PositivityTheory.SiegelWeilFormula.tweyl.exists_l_ne_k d hT
  have hP : ∀ (p : d.G) (t : GL (Fin d.n) (AE F E)),
      (p.1.1 : Matrix _ _ (AE F E)) * diagCols (Fin d.n) = diagCols (Fin d.n) * t.1 → c p = 1 := fun p t hpt => by
    have K := _root_.PositivityTheory.SiegelWeilFormula.tweyl.hR_k d d.l d.ok.dbl.adm (fun z φ hφ => d.ok.dbl.kill z φ hφ) p t hpt
    have e1 := hcf p φl hφl
    have e2 := congrArg d.l e1
    simp only [Module.End.mul_apply, map_smul, smul_eq_mul] at e2
    rw [d.ok.dbl.fix g _ (hsp p _ ((_root_.PositivityTheory.SiegelWeilFormula.tweyl.hS_k d).pres _ _ hφl)), K _ ((_root_.PositivityTheory.SiegelWeilFormula.tweyl.hS_k d).pres _ _ hφl), d.ok.dbl.fix g⁻¹ φl hφl,
      K φl hφl] at e2
    have hK := siegel_factor_ne (d.χ) (Matrix.GeneralLinearGroup.det t) (adeleClass F).modu
      (Units.map (Algebra.norm (AF F) : AE F E →* AF F) (Matrix.GeneralLinearGroup.det t))
      ((Fintype.card (Fin d.m) : ℝ) / 2)
    refine Units.ext ?_
    rw [hcv, Units.val_one]
    have hne := mul_ne_zero hK hl0
    rw [mul_assoc] at hne
    apply mul_right_cancel₀ hne
    rw [one_mul]
    simpa only [mul_assoc] using e2.symm
  obtain ⟨ε, hε⟩ := _root_.PositivityTheory.SiegelWeilFormula.tweyl.signY_k d
  have hc1 := GlobalTheory.T.doubledUnitary_character_trivial_of_siegel F E σ (_root_.PositivityTheory.SiegelWeilFormula.tweyl.cm_k d) d.n d.Y.J ε hε (_root_.PositivityTheory.SiegelWeilFormula.tweyl.detY_k d) c hcont hP
  intro Φ hΦ x
  have e := hcf x _ ((_root_.PositivityTheory.SiegelWeilFormula.tweyl.hS_k d).pres g Φ hΦ)
  have hcf1 : cf x = 1 := by rw [← hcv, hc1]; rfl
  rw [hcf1, one_smul] at e
  simp only [Module.End.mul_apply, hSinv] at e
  exact e.symm
theorem tthetaComm_k (hT : _root_.PositivityTheory.SiegelWeilFormula.TBij_k) : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ), ∀ Φ ∈ d.sch, ∀ x g, d.om x (d.S g Φ) = d.S g (d.om x Φ) :=
  fun _ _ _ _ _ _ _ _ d Φ hΦ x g => _root_.PositivityTheory.SiegelWeilFormula.tweyl.comm_k d hT g Φ hΦ x
end PositivityTheory.SiegelWeilFormula.tweyl
end
end
