import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.DifferenceQuotientIsometryExchangeAlt
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IntegrableStandardPairThetaWeilRange

noncomputable section

open scoped Matrix NNReal ComplexConjugate TensorProduct ENNReal Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn GlobalTheory.SiegelFormula
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace PositivityTheory.Rg.Sw.Glob.DHolH

variable {D : D7} {n : ℕ}

def thS (V : HSp D) (f : Mx D V.rank n → ℂ) (h : GA D V) : ℂ := ∑' ξ, f (invPt V h ξ)

theorem leftInv_thS (V : HSp D) (f : Mx D V.rank n → ℂ) : LeftInv (GQ V) (thS V f) := by
  intro γ hγ h
  obtain ⟨δ, -, hδ⟩ : ∃ δ : GL (Fin V.rank) D.host.E, _ ∧ Formalism.UG.bc (incA D) δ = Formalism.L2.Theta.matHom V γ⁻¹ := inv_mem hγ
  let e : Matrix (Fin V.rank) (Fin n) D.host.E ≃ Matrix (Fin V.rank) (Fin n) D.host.E :=
    ⟨fun ξ => δ.1 * ξ, fun ξ => δ⁻¹.1 * ξ, fun ξ => by simp, fun ξ => by simp⟩
  have h1 : Formalism.L2.Theta.mt V γ⁻¹ = δ.1.map (incA D) := (congrArg Units.val hδ).symm
  have h2 : Formalism.L2.Theta.mt V (γ * h)⁻¹ = Formalism.L2.Theta.mt V h⁻¹ * Formalism.L2.Theta.mt V γ⁻¹ := by rw [mul_inv_rev]; rfl
  refine (tsum_congr fun ξ => ?_).trans (e.tsum_eq fun ξ => f (invPt V h ξ))
  simp only [invPt, e, Equiv.coe_fn_mk, h2, h1, Matrix.mul_assoc, Matrix.map_mul]

theorem enorm_thS_le (V : HSp D) (f : Mx D V.rank n → ℂ) (h : GA D V) : ‖thS V f h‖ₑ ≤ absTheta V f h :=
  enorm_tsum_le_tsum_enorm

theorem absTheta_mono (V : HSp D) {f M : Mx D V.rank n → ℂ} (hfM : ∀ x, ‖f x‖ ≤ ‖M x‖) (h : GA D V) :
    absTheta V f h ≤ absTheta V M h :=
  ENNReal.tsum_le_tsum fun _ => enorm_le_iff_norm_le.2 (hfM _)

theorem absThetaInt_mono (V : HSp D) (ν : Measure (GA D V)) {f M : Mx D V.rank n → ℂ} (hfM : ∀ x, ‖f x‖ ≤ ‖M x‖) :
    absThetaInt V ν f ≤ absThetaInt V ν M :=
  lintegral_mono fun q => absTheta_mono V hfM _

theorem absThetaInt_smul_lt (V : HSp D) (ν : Measure (GA D V)) (c : ℂ) {M : Mx D V.rank n → ℂ}
    (hM : absThetaInt V ν M < ⊤) : absThetaInt V ν (c • M) < ⊤ := by
  unfold absThetaInt
  have : ∀ q, descend (GQ V) (absTheta V (c • M)) q = ‖c‖ₑ * descend (GQ V) (absTheta V M) q := fun q =>
    GlobalTheory.AbsThetaSemi.absTheta_smul V c M q.out
  simp_rw [this]
  rw [lintegral_const_mul' _ _ enorm_ne_top]
  exact ENNReal.mul_lt_top enorm_lt_top hM

theorem aestronglyMeasurable_thS (V : HSp D) (ν : Measure (GA D V)) [ν.IsHaarMeasure] {f : Mx D V.rank n → ℂ} (hf : Continuous f)
    (hfin : absThetaInt V ν f < ⊤) : AEStronglyMeasurable (descend (GQ V) (thS V f)) (autMeasure V ν) := by
  rw [autMeasure, aestronglyMeasurable_quotMeasure_iff_lift, (leftInv_thS V f).lift_descend]
  have hae : ∀ᵐ q ∂autMeasure V ν, descend (GQ V) (absTheta V f) q < ⊤ :=
    ae_lt_top (GlobalTheory.AbsThetaSemi.measurable_descend_absTheta V hf) hfin.ne
  have hae' : ∀ᵐ h ∂ν, absTheta V f h < ⊤ := by
    have := (quasiMeasurePreserving_mk (Γ := GQ V) (μ := ν)).ae hae
    filter_upwards [this] with h hh
    rwa [(leftInv_absTheta V f).descend_mk] at hh
  have := GlobalTheory.ThetaTransformMeas.countable_field D.host.E
  have : Countable (Matrix (Fin V.rank) (Fin n) D.host.E) :=
    inferInstanceAs (Countable (Fin V.rank → Fin n → D.host.E))
  have hsum : ∀ᵐ h ∂ν, Summable fun ξ : Matrix (Fin V.rank) (Fin n) D.host.E => f (invPt V h ξ) :=
    hae'.mono fun h hh => Summable.of_enorm hh.ne
  exact aestronglyMeasurable_of_tendsto_ae (μ := ν)
    (Filter.atTop : Filter (Finset (Matrix (Fin V.rank) (Fin n) D.host.E)))
    (f := fun F h => ∑ ξ ∈ F, f (invPt V h ξ))
    (fun F => (continuous_finsetSum F fun ξ _ =>
      hf.comp (GlobalTheory.AbsThetaSemi.continuous_invPt V ξ)).aestronglyMeasurable)
    (hsum.mono fun h hh => hh.hasSum)

theorem integrable_thS (V : HSp D) (ν : Measure (GA D V)) [ν.IsHaarMeasure] {f : Mx D V.rank n → ℂ} (hf : Continuous f)
    (hfin : absThetaInt V ν f < ⊤) : Integrable (descend (GQ V) (thS V f)) (autMeasure V ν) :=
  ⟨aestronglyMeasurable_thS V ν hf hfin,
    lt_of_le_of_lt (lintegral_mono fun q => enorm_thS_le V f q.out) hfin⟩

theorem ae_absTheta_lt (V : HSp D) (ν : Measure (GA D V)) [ν.IsHaarMeasure] {M : Mx D V.rank n → ℂ} (hM : Continuous M)
    (hfin : absThetaInt V ν M < ⊤) : ∀ᵐ q ∂autMeasure V ν, descend (GQ V) (absTheta V M) q < ⊤ :=
  ae_lt_top (GlobalTheory.AbsThetaSemi.measurable_descend_absTheta V hM) hfin.ne

theorem integrable_absTheta_toReal (V : HSp D) (ν : Measure (GA D V)) [ν.IsHaarMeasure] {M : Mx D V.rank n → ℂ} (hM : Continuous M)
    (hfin : absThetaInt V ν M < ⊤) :
    Integrable (fun q => (descend (GQ V) (absTheta V M) q).toReal) (autMeasure V ν) :=
  integrable_toReal_of_lintegral_ne_top (GlobalTheory.AbsThetaSemi.measurable_descend_absTheta V hM).aemeasurable hfin.ne

theorem sch_facts (hP : GlobalTheory.Published.WeilThetaConvergence) (V : HSp D) (hn : 1 ≤ n) (hr : n + Formalism.MainNotions.SchurIrreducible.wittIdx V < V.rank)
    (θ : InfFam D) (hθ : IsInfFam θ) (ν : Measure (GA D V)) (hν : ν.IsHaarMeasure) {M : Mx D V.rank n → ℂ}
    (hM : M ∈ schwartzA θ V.rank n) : Continuous M ∧ absThetaInt V ν M < ⊤ :=
  ⟨(GlobalTheory.T.schwartzBruhatAdelicMatrix_continuous_le_majorant D θ hθ _ _ M (GlobalTheory.SchwartzPure.isSchwartzBruhat_of_mem_schwartzA D θ hθ _ _ M hM)).1,
    hP D n V hn (Or.inr hr) θ hθ ν hν ⟨M, hM⟩⟩

end PositivityTheory.Rg.Sw.Glob.DHolH
