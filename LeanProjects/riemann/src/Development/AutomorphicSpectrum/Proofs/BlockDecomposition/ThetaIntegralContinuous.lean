import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.WeilSiegelTheta.BigCellDefs
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ThetaSumInvariantWeylInvolution
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SchwartzBoundFiniteInfinite
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaRestrictIsotropicQuotientWittTowerPropertie
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.CompanionTheory.BigCellJ

theorem integrable_schwartzA {D : D7} {θ : InfFam D} (hθ : IsInfFam θ) {m n : ℕ} {μ : Measure (Mx D m n)}
    {𝓕 : Set (Mx D m n)} (hμ : IsCovolOne (ratMx D m n) μ 𝓕) {φ : Mx D m n → ℂ}
    (hφ : φ ∈ schwartzA θ m n) : Integrable φ μ := by
  obtain ⟨i1, i2, i3, i4, i5, K, hK, hKc⟩ := GlobalTheory.TowerRestrict.lattice_Mx D m n
  haveI : BorelSpace (Mx D m n) := ⟨rfl⟩
  haveI := hμ.1
  haveI i6 : DiscreteTopology (ratMx D m n) := i5
  haveI : SecondCountableTopology (ratMx D m n) := TopologicalSpace.Subtype.secondCountableTopology _
  haveI : Countable (ratMx D m n) := TopologicalSpace.separableSpace_iff_countable.1 inferInstance
  have hc : Continuous φ := (GlobalTheory.CompanionTheory.WeilTheta.schwartzA_continuous_and_dominated D θ hθ _ _ φ hφ).1
  have hU : GlobalTheory.CompanionTheory.Hypotheses₂.OneV.PoiAbs.UnifSummable (ratMx D m n).subtype φ := fun Q hQ => by
    obtain ⟨b, hb1, hb2⟩ := GlobalTheory.CompanionTheory.ThetaPoisson.translates_bound hθ ⟨φ, hφ⟩ Q hQ
    refine ⟨b, hb1, fun c x hx => ?_⟩
    have h := hb2 x hx c
    rwa [add_comm] at h
  exact GlobalTheory.CompanionTheory.Hypotheses₂.OneV.PoiAbs.integrable_of_unif hc hU μ hK fun x => by
    obtain ⟨γ, hγ, h⟩ := hKc x
    refine ⟨⟨-γ, (ratMx D m n).neg_mem hγ⟩, ?_⟩
    simpa [sub_neg_eq_add, add_comm] using h

theorem continuous_halfTr {D : D7} : Continuous (halfTr : AE D → AF D.host.F) := by
  haveI := isTopologicalRing_tens (F := D.host.F) (E := D.host.E) (R := AF D.host.F)
  haveI : IsModuleTopology (AF D.host.F) (AE D) := ⟨rfl⟩
  have ht : Continuous (trA : AE D → AF D.host.F) :=
    IsModuleTopology.continuous_of_linearMap (Algebra.trace (AF D.host.F) (AE D))
  unfold halfTr
  exact continuous_const.mul ht

theorem continuous_integral_twist {X Y : Type*} [TopologicalSpace X] [FirstCountableTopology X]
    [TopologicalSpace Y] [SecondCountableTopology Y] [MeasurableSpace Y] [OpensMeasurableSpace Y]
    {μ : Measure Y} {φ : Y → ℂ} {g : X → Y → ℂ} (hi : Integrable φ μ)
    (hj : Continuous fun p : X × Y => g p.1 p.2) (hn : ∀ b y, ‖g b y‖ = 1) :
    Continuous fun b => ∫ y, φ y * g b y ∂μ := by
  have hg1 : ∀ b, AEStronglyMeasurable (g b) μ := fun b =>
    (hj.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable
  have hg2 : ∀ y, Continuous fun b => g b y := fun y =>
    hj.comp (continuous_id.prodMk continuous_const)
  refine continuous_of_dominated (bound := fun y => ‖φ y‖) (fun b => ?_) (fun b => ?_) hi.norm ?_
  · exact hi.aestronglyMeasurable.mul (hg1 b)
  · refine Filter.Eventually.of_forall fun y => ?_
    rw [norm_mul, hn, mul_one]
  · refine Filter.Eventually.of_forall fun y => ?_
    exact (hg2 y).const_mul (φ y)

theorem continuous_inner_self {D : D7} (V : HSp D) (r : ℕ) :
    Continuous fun y : Mx D V.rank r => (GlobalTheory.StdUnn.inner V y y : Mx D r r) := by
  haveI := isTopologicalRing_tens (F := D.host.F) (E := D.host.E) (R := AF D.host.F)
  unfold GlobalTheory.StdUnn.inner
  exact GlobalTheory.MixModel.continuous_adj.matrix_mul (continuous_const.matrix_mul continuous_id)

theorem continuous_phase {D : D7} (V : HSp D) (r : ℕ) {ψ : AddChar (AF D.host.F) ℂ}
    (hψ : IsCharAF D.host.F ψ) :
    Continuous fun p : hermA D r × Mx D V.rank r =>
      ψ (halfTr (Matrix.trace (HMul.hMul p.1.1 (GlobalTheory.StdUnn.inner V p.2 p.2) : Mx D r r))) := by
  haveI := isTopologicalRing_tens (F := D.host.F) (E := D.host.E) (R := AF D.host.F)
  exact hψ.1.comp (continuous_halfTr.comp
    ((continuous_subtype_val.comp continuous_fst).matrix_mul
      ((continuous_inner_self V r).comp continuous_snd)).matrix_trace)

theorem jt_continuous : ∀ (D : D7) (r : ℕ) (V : HSp D) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D)
    (μ : Measure (Mx D V.rank r)) (φ : Mx D V.rank r → ℂ), IsCharAF D.host.F ψ → IsInfFam θ →
    (∃ 𝓕, IsCovolOne (ratMx D V.rank r) μ 𝓕) → φ ∈ schwartzA θ V.rank r → Continuous (Jt ψ V μ φ) := by
  intro D r V ψ θ μ φ hψ hθ ⟨𝓕, hμ⟩ hφ
  obtain ⟨i1, i2, i3, i4, i5, -⟩ := GlobalTheory.TowerRestrict.lattice_Mx D V.rank r
  obtain ⟨j1, j2, j3, j4, j5, -⟩ := GlobalTheory.TowerRestrict.lattice_Mx D r r
  haveI : BorelSpace (Mx D V.rank r) := ⟨rfl⟩
  haveI : SecondCountableTopology (hermA D r) := TopologicalSpace.Subtype.secondCountableTopology _
  haveI : FirstCountableTopology (hermA D r) :=
    TopologicalSpace.SecondCountableTopology.to_firstCountableTopology _
  exact continuous_integral_twist (g := fun (b : hermA D r) (y : Mx D V.rank r) =>
      ψ (halfTr (Matrix.trace (HMul.hMul b.1 (GlobalTheory.StdUnn.inner V y y) : Mx D r r))))
    (integrable_schwartzA hθ hμ hφ) (continuous_phase V r hψ) (fun b y => hψ.2.1 _)

end GlobalTheory.CompanionTheory.BigCellJ

end
