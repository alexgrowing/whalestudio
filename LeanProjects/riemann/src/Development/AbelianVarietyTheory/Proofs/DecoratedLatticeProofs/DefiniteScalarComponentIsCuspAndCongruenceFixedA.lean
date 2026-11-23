import Development.AbelianVarietyTheory.Definitions.LatticeFrames.PrinInf
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.TransferOn
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ParamsEx
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AdjFormula
import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HeckeLPartialContinuationHolds
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaIntegrandIntegrable
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MulAntiOfUnitary
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FiniteDimensionalModel
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.IsBesPosOfBesselTied
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ExistsPlacesSingleton
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LevelAveragesThetaPairZeroWithoutCharacter
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DownLift GlobalTheory.Core.Rk.Exh

noncomputable section

namespace GlobalTheory.DownLift.DefiniteComp

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

theorem extV_mul_inf (R : RealDat D A Ks) (i : Fin D.R.m) (t : T) (y : (R.HV i t).H)
    {k : GA D (Vc D i)} (hk : k ∈ GinfC (Vc D i)) (h : GA D (Vc D i)) :
    R.extV i t y (h * k) = (R.cV i).ρ k⁻¹ (R.extV i t y h) := by
  have hr : (finHom (Vc D i)).rangeRestrict (h * k) = (finHom (Vc D i)).rangeRestrict h := by
    apply Subtype.ext
    simp [MonoidHom.mem_ker.1 hk]
  show (R.cV i).ρ (h * k)⁻¹ ((R.HV i t).e y ((finHom (Vc D i)).rangeRestrict (h * k))) =
    (R.cV i).ρ k⁻¹ ((R.cV i).ρ h⁻¹ ((R.HV i t).e y ((finHom (Vc D i)).rangeRestrict h)))
  refine (congrArg ((R.cV i).ρ (h * k)⁻¹) (congrArg ((R.HV i t).e y) hr)).trans ?_
  have e : (R.cV i).ρ (h * k)⁻¹ = (R.cV i).ρ k⁻¹ * (R.cV i).ρ h⁻¹ := by rw [_root_.mul_inv_rev, map_mul]
  exact congrArg (fun f : Module.End ℂ (R.cV i).W => f ((R.HV i t).e y ((finHom (Vc D i)).rangeRestrict h))) e

theorem extV_mul_Kg (R : RealDat D A Ks) (hM : R.IsModels) (i : Fin D.R.m) (t : T) (y : (R.HV i t).H)
    {κ : GA D (Vc D i)} (hκ : κ ∈ GfC (Vc D i))
    (hK : finE (Vc D i) κ ∈ Kg D.sp.cm (Vc D i).gram (R.βV i) (R.Pg ∪ R.Q t)) (h : GA D (Vc D i)) :
    R.extV i t y (h * κ) = R.extV i t y h := by
  have h2 : Kg D.sp.cm (Vc D i).gram (R.βV i) (R.Pg ∪ R.Q t) ≤
      lev D.sp.cm (Vc D i).gram (R.βV i) (flag1L (R.datVt i t)) :=
    Kg_le_lev (D := flag1L (R.datVt i t)) Finset.subset_union_left Finset.subset_union_right
  have hlev : κ ∈ levG (Vc D i) (R.βV i) (flag1L (R.datVt i t)) := mem_levA.2 ⟨hκ, h2 hK⟩
  have hred : ∀ PP ∈ R.Pg ∪ R.Q t, redFn (R.βV i) PP (finE (Vc D i) κ) = 1 := fun PP hP =>
    (mem_princAt.1 (Subgroup.mem_iInf.1 (Subgroup.mem_iInf.1 hK.2 PP) hP)).2
  have hfn : levFn (R.βV i) (flag1L (R.datVt i t)) (finE (Vc D i) κ) = 1 :=
    GlobalTheory.ThetaIntegrand.levFn_eq_one (R.βV i) _ (flag1L (R.datVt i t))
      (fun PP hP => hred PP (Finset.mem_union_left _ hP)) (fun PP hP => hred PP (Finset.mem_union_right _ hP))
  have hchi : levChi (Vc D i) (R.βV i) (flag1L (R.datVt i t)) κ = 1 :=
    (congrArg (fun u : ℂˣ => (u : ℂ)) hfn).trans Units.val_one
  exact (GlobalTheory.DownLift.GenFinite.extV_type R hM i t y κ hlev h).trans (by simp only [hchi, one_smul])

def compL (R : RealDat D A Ks) (i : Fin D.R.m) (t : T) (y : (R.HV i t).H) :
    ((R.cV i).W →ₗ[ℂ] ℂ) →ₗ[ℂ] (GA D (Vc D i) → ℂ) :=
  LinearMap.pi fun g => LinearMap.applyₗ (R := ℂ) (R.extV i t y g)

theorem mul_inf_mem_range (R : RealDat D A Ks) (i : Fin D.R.m) (t : T) (y : (R.HV i t).H) (l : (R.cV i).W →ₗ[ℂ] ℂ)
    {k : GA D (Vc D i)} (hk : k ∈ GinfC (Vc D i)) :
    (fun g => l (R.extV i t y (g * k))) ∈ LinearMap.range (compL R i t y) :=
  ⟨l ∘ₗ (R.cV i).ρ k⁻¹, funext fun g => (congrArg l (extV_mul_inf R i t y hk g)).symm⟩

theorem definiteScalarComponent_isCusp_and_congruence_fixed : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.LiftRows.Given R F → R.FullP → ∀ i t cA a, Defin R.θ (Vc D i) cA a → ∀ (y : (R.HV i t).H) (l : (R.cV i).W →ₗ[ℂ] ℂ), (fun g => l (R.extV i t y g)) ∈ GlobalTheory.Cusp.A0 R.θ (Vc D i) cA ∧ ∀ κ ∈ prin (Vc D i) (R.βV i) (R.Pg ∪ R.Q t), ∀ g, l (R.extV i t y (g * κ)) = l (R.extV i t y g) := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F hG _ i t cA a hd y l
  have hM : R.IsModels := hG.core.models
  have hf : (R.HV i t).e y ∈ Formalism.IndefR.Bridge.AdForms (Formalism.IndefR.Bridge.ratF (Vc D i)) (R.cV i).coef.ρ
      (levEnv _ (R.βV i) (R.datVt i t)).J (levEnv _ (R.βV i) (R.datVt i t)).χ :=
    (hM.HV i t).2.1.le (LinearMap.mem_range_self _ y)
  have hcont : Continuous fun g => l (R.extV i t y g) :=
    (LinearMap.continuous_of_finiteDimensional l).comp
      (GlobalTheory.ThetaIntegrand.ext_continuous (R.cV i) (hM.cV i) (R.βV i) (R.datVt i t) hf)
  have hleft : ∀ γ ∈ GQ (Vc D i), ∀ g, l (R.extV i t y (γ * g)) = l (R.extV i t y g) := fun γ hγ g =>
    congrArg l (GlobalTheory.ThetaIntegrand.ext_invariant (R.cV i) hf γ hγ g)
  have hlevel : ∃ U : Subgroup (GA D (Vc D i)), IsOpen (U : Set (GA D (Vc D i))) ∧
      ∀ k ∈ U, k ∈ GfC (Vc D i) → ∀ g, l (R.extV i t y (g * k)) = l (R.extV i t y g) :=
    ⟨_, GlobalTheory.DefiniteEnd.isOpen_Kg (Vc D i) (R.βV i) (R.Pg ∪ R.Q t), fun k hk hkf g =>
      congrArg l (extV_mul_Kg R hM i t y hkf hk g)⟩
  have hkfin : FiniteDimensional ℂ (Submodule.span ℂ {ψ : GA D (Vc D i) → ℂ |
      ∃ k ∈ GinfC (Vc D i), ψ = rTr (Vc D i) k fun g => l (R.extV i t y g)}) :=
    Submodule.finiteDimensional_of_le (Submodule.span_le.2 (by
      rintro _ ⟨k, hk, rfl⟩
      exact mul_inf_mem_range R i t y l hk))
  have hdef : IsAutFunDef (Vc D i) fun g => l (R.extV i t y g) := ⟨⟨hleft, hlevel, hcont⟩, hkfin⟩
  have hdefn : (Vc D i).IsDefinite := fun τ => Or.inl (hd.pos τ)
  have hsm := ((GlobalTheory.DefiniteForms.autFunDefIffSm D) R.θ hd.inf (Vc D i) hd.sig hdefn _).1 hdef
  have hcusp : IsCuspFun (Vc D i) fun g => l (R.extV i t y g) := fun r C hC =>
    absurd hC (GlobalTheory.Per.isAniso_of_posDef hd.sig hd.pos r C)
  have hK : GlobalTheory.Doubling.IsKFinite (GlobalTheory.Cusp.Kinf R.θ (Vc D i) cA) fun g => l (R.extV i t y g) :=
    GlobalTheory.Doubling.isKFinite_iff.2 ⟨LinearMap.range (compL R i t y), inferInstance, fun k hk =>
      mul_inf_mem_range R i t y l (GlobalTheory.Cusp.Kinf_le hk)⟩
  refine ⟨GlobalTheory.Cusp.mem_cuspForms.2 ⟨⟨hsm, hcusp⟩, hK⟩, fun κ hκ g => ?_⟩
  have h1 := mem_levA.1 hκ
  have h2 : finE (Vc D i) κ ∈ Kg D.sp.cm (Vc D i).gram (R.βV i) (R.Pg ∪ R.Q t) :=
    (Model.lev_prinDat (Vc D i) (R.βV i) (R.Pg ∪ R.Q t)) ▸ h1.2
  exact congrArg l (extV_mul_Kg R hM i t y h1.1 h2 g)

end GlobalTheory.DownLift.DefiniteComp
