import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TwoMulRankWLt
import Development.AbelianVarietyTheory.Definitions.Foundations.ForallEventuallyFinLocIff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsOpenLevelGroupFiniteAdelic
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsCoefficientSpaceDualDiscreteSeriesModelPos
import Development.AbelianVarietyTheory.Proofs.HeightProofs.AdelicUnitaryActionAtRealPlace
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsCompactAdele
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousOnAtTau
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RawLift

noncomputable section

namespace GlobalTheory.LowCoefPos

theorem integral_lowCoefSq_pos : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), Laws R F → ∀ i, LevProd R i → ∀ v, IsUnitVec R i v → IntegrableOn (lowCoefSq R i v) (realLev R i) (R.νW i) → 0 < ∫ h in realLev R i, lowCoefSq R i v h ∂(R.νW i) := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F hL i hP v hv hI
  have hθ : IsInfFam R.θ := hL.models.inf
  have : (R.νW i).IsHaarMeasure := (hL.models.νW i).1.1

  have hrep : ∀ ρ (x : (R.MW i (sg0 D A)).H ρ), Continuous fun h : GA D (Wc D i) =>
      (R.MW i (sg0 D A)).rep ρ (infMat D.sp.cm.sig (Wc D i).gram (R.θ ρ) h) x := by
    intro ρ x
    have hmem : ∀ h : GA D (Wc D i), (R.MW i (sg0 D A)).fr ρ * infMat D.sp.cm.sig (Wc D i).gram (R.θ ρ) h * ((R.MW i (sg0 D A)).fr ρ)⁻¹ ∈ UJset ((R.MW i (sg0 D A)).ε ρ) :=
      fun h => GlobalTheory.DualCoef.frame_mem (R.MW i (sg0 D A)) ρ (GlobalTheory.FockCompare.RealAction.infMat_mem_UH hθ (Wc D i) h ρ)
    exact (((R.MW i (sg0 D A)).ds ρ).2.2.1.2.2 x).comp_continuous
      ((continuous_const.matrix_mul (GlobalTheory.Mem.VolExists.continuous_infMat (Wc D i).gram (hθ ρ))).matrix_mul
        continuous_const) hmem
  have hc : Continuous (lowCoefSq R i v) := by
    unfold lowCoefSq
    refine (continuous_finsetProd _ fun ρ _ => ?_).norm.pow 2
    exact continuous_const.inner (hrep ρ _)

  have h0 : ∀ h, 0 ≤ lowCoefSq R i v h := fun h => by unfold lowCoefSq; positivity

  have h1 : lowCoefSq R i v 1 = 1 := by
    unfold lowCoefSq
    have e : ∀ ρ, ⟪((v ρ : (R.MW i (sg0 D A)).sm ρ) : (R.MW i (sg0 D A)).H ρ), (R.MW i (sg0 D A)).rep ρ (infMat D.sp.cm.sig (Wc D i).gram (R.θ ρ) 1)
        ((v ρ : (R.MW i (sg0 D A)).sm ρ) : (R.MW i (sg0 D A)).H ρ)⟫_ℂ = 1 := by
      intro ρ
      rw [GlobalTheory.PointAtPlaceHom.infMat_one, GlobalTheory.DualCoef.rep_one, ContinuousLinearMap.one_apply,
        inner_self_eq_norm_sq_to_K, hv ρ]
      simp
    simp [e]

  set O : Set (GA D (Wc D i)) := GlobalTheory.AutMult.toFin (Wc D i) ⁻¹'
    {g : GfC (Wc D i) | (g : GA D (Wc D i)) ∈ levG _ (R.βW i) (R.datWp i R.triv)} with hO
  have hOo : IsOpen O := (GlobalTheory.LevelOpen.isOpen_levG _ _ _).preimage (GlobalTheory.AutMult.continuous_toFin _)
  have hOs : O ⊆ realLev R i := by
    intro h hh
    exact ⟨_, (GlobalTheory.AutMult.toInf (Wc D i) h).2, _, hh, (GlobalTheory.AutMult.toInf_mul_toFin h).symm⟩
  have h1O : (1 : GA D (Wc D i)) ∈ O := by
    show ((GlobalTheory.AutMult.toFin (Wc D i) 1 : GfC (Wc D i)) : GA D (Wc D i)) ∈ levG _ (R.βW i) (R.datWp i R.triv)
    rw [map_one]
    exact (levW R i).one_mem
  set U : Set (GA D (Wc D i)) := {h | (1 : ℝ) / 2 < lowCoefSq R i v h} ∩ O with hU
  have hUo : IsOpen U := (isOpen_lt continuous_const hc).inter hOo
  have h1U : (1 : GA D (Wc D i)) ∈ U := ⟨by rw [Set.mem_setOf_eq, h1]; norm_num, h1O⟩
  have hUs : U ⊆ Function.support (lowCoefSq R i v) ∩ realLev R i := by
    intro h hh
    refine ⟨?_, hOs hh.2⟩
    have := hh.1
    rw [Set.mem_setOf_eq] at this
    rw [Function.mem_support]
    linarith
  have hpos : 0 < R.νW i U := hUo.measure_pos _ ⟨1, h1U⟩
  rw [setIntegral_pos_iff_support_of_nonneg_ae (Filter.Eventually.of_forall h0) hI]
  exact lt_of_lt_of_le hpos (measure_mono hUs)

end GlobalTheory.LowCoefPos

end
