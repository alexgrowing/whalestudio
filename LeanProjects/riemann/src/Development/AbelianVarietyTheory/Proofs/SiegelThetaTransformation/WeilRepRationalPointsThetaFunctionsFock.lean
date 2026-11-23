import Mathlib
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsWeakOfDatum
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsHeatZero
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ThetaKernelOrthonormalFrameInDomainPeriodLinearStatement
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ThetaFunctionSpaceHeisenbergLawsStatement
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.RationalUnitaryGroupStructureStatement
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.AdelicZakThetaExistsUniqueStatement
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ThetaKernelTestFunctionMapLinearInjectiveEquivarStatement
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.WeakWeilRepCarriesDerivativesVacuaFockVectorsStatement

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.L2.Pj MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker
open GlobalTheory.SW hiding Level
open GlobalTheory.Dict (hx pv)
open ReciprocityTheory.ChartRestriction.G.I2 (polyDeriv)
open scoped TensorProduct ComplexConjugate Real Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Ker.OmRat

variable {D : D7} {S T : HSp D}

theorem mt_mul' (V : HSp D) (g g' : GA D V) : mt V (g * g') = mt V g * mt V g' := by simp [Formalism.L2.Theta.mt]

theorem mt_one' (V : HSp D) : mt V 1 = 1 := by simp [Formalism.L2.Theta.mt]

theorem actO_inv_cancel (g : GA D S) (h : GA D T) (w : WO S T) :
    actO S T g h (actO S T g⁻¹ h⁻¹ w) = w := by
  unfold actO
  rw [inv_inv]
  simp only [Matrix.mul_assoc]
  rw [← mt_mul', mul_inv_cancel, mt_one', Matrix.mul_one, ← Matrix.mul_assoc, ← mt_mul', mul_inv_cancel,
    mt_one', Matrix.one_mul]

theorem heisO_at_zero (ψ : AddChar (AF D.host.F) ℂ) (w : WO S T) (f : WO S T → ℂ) :
    heisO ψ S T w f 0 = f w := by
  have h : hO S T 0 w = 0 := by simp [hO]
  simp [heisO, symplOH, symplO, h]

theorem compAt_one' (θ : InfFam D) (τ : D.what₂.Tau) :
    compAt θ τ (mt S 1) = 1 := by
  rw [mt_one']
  unfold compAt
  ext i j
  by_cases h : i = j <;> simp [Matrix.one_apply, h]

theorem om_subst (C : Ctx S T) (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)) (H : IsWeak C.ψ S T om)
    (γ : GA D S) (hγ : γ ∈ GQ S) (γ' : GA D T) (hγ' : γ' ∈ GQ T) (f : WO S T → ℂ) (hf : C.IsTh f) (w : WO S T) :
    om (γ, γ') f w = f (actO S T γ⁻¹ γ'⁻¹ w) := by
  have h1 := H.om_heis γ γ' (actO S T γ⁻¹ γ'⁻¹ w) f hf
  have h2 := H.om_aut γ hγ γ' hγ' _ (((GlobalTheory.T.thetaFunction_space_heisenberg_laws D S T C).2.2 f hf).2.1 (actO S T γ⁻¹ γ'⁻¹ w))
  rw [actO_inv_cancel] at h1
  rw [← heisO_at_zero C.ψ w (om (γ, γ') f), ← h1]
  exact h2.trans (heisO_at_zero _ _ _)

theorem om_rat : ∀ (D : D7) (S T : HSp D) (C : Ctx S T), ∀ om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ), IsWeak C.ψ S T om → (∀ γ ∈ GQ S, ∀ γ' ∈ GQ T, ∀ f, C.IsTh f → ∀ w, om (γ, γ') f w = f (actO S T γ⁻¹ γ'⁻¹ w)) ∧ ∀ (ga : GL (Fin T.rank) D.host.E) (γ : GA D T), IsRatOf T ga γ → ∀ φ : TF S.rank C.g, SW.IsSB φ → (∀ x ∈ C.X.dom, om (1, γ) (C.Th x φ) = C.Th (lact ga x) (wG C.X C.bas C.idx ga φ)) ∧ ∀ B, C.IsB B → ∀ Q : MvPolynomial (FVar D T.rank S.rank) ℂ, om (1, γ) (C.fvec B (C.Th (C.xB B) φ) Q) = C.fvec (C.mvB γ B) (C.Th (C.xB (C.mvB γ B)) (wG C.X C.bas C.idx ga φ)) Q := by
  intro D S T C om H
  refine ⟨fun γ hγ γ' hγ' f hf w => om_subst C om H γ hγ γ' hγ' f hf w, ?_⟩
  intro ga γ hr φ hφ
  have hγ : γ ∈ GQ T := ((GlobalTheory.T.rational_unitary_group_structure D S T C).2.1 γ γ ga ga hr hr).2.2.1
  have key : ∀ x ∈ C.X.dom, om (1, γ) (C.Th x φ) = C.Th (lact ga x) (wG C.X C.bas C.idx ga φ) := by
    intro x hx
    funext w
    rw [om_subst C om H 1 (one_mem _) γ hγ _ (GlobalTheory.T.adelicZakTheta_exists_unique D S T C x hx φ hφ).1.1 w, inv_one]
    exact ((GlobalTheory.T.thetaKernel_testFunction_map_linear_injective_equivariant D S T C x hx φ hφ).2.2.2 ga γ hr w).symm
  refine ⟨key, ?_⟩
  intro B hB Q
  have hJ := (GlobalTheory.T.thetaKernel_orthonormalFrame_inDomain_periodLinear D S T C).2 B hB
  have hx := hJ.2.1
  have hm : C.xB (C.mvB γ B) = lact ga (C.xB B) := (hJ.2.2.2.2.2 γ).2.2.2.2.2 ga hr
  have h5 := ((GlobalTheory.T.weakWeilRep_carries_derivatives_vacua_fockVectors D S T C om H 1 γ _ (GlobalTheory.T.adelicZakTheta_exists_unique D S T C _ hx φ hφ).1.1).2 B hB).2 Q
  rw [h5, key _ hx, hm]
  simp only [compAt_one']
  rfl

end GlobalTheory.Ker.OmRat
