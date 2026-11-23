import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LabelTameCharacter
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SglobDzBigDef
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SplitLoc
import Development.AutomorphicArithmetic.Foundations.LocalLanglands.IsRecTOfIsRec
import Development.AbelianVarietyTheory.Definitions.Divisors.IsRecTLocRecT
import Development.AutomorphicArithmetic.Foundations.UnitarySphericalFixing.SatakeParameters.AbsCentralAlt

set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.SplitRead GlobalTheory.PendOf GlobalTheory.LevelType ValuativeRel Polynomial
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
namespace DiscreteGroups.sglob.DzType.Rt
open NumberField IsDedekindDomain GlobalTheory.SerSys.TameGen GlobalTheory.Published.DepthZeroModel GlobalTheory.TameCharLabel
theorem label_reduction_alt : _root_.DiscreteGroups.sglob.DzType.DepthZeroInertiaBigAlt → ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : Formalism.BasicNotions.D7) (Γ : GlobalTheory.HeightCounting.GrpSide D) (k : Fin 2) (v : D.nd.PlG k) (χ : ((D.naut.plGw k v).adicCompletion D.host.E)ˣ →* ℂˣ) (hχ : IsSmoothChar χ) (u : ZMod (D.host.g k)), IsTame χ → _root_.GlobalTheory.PendOf.localLabelPolynomial hL D k v (Irr.ofDet 1 χ hχ) = Polynomial.X - Polynomial.C u → haveI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩; resCard ((D.naut.plGw k v).adicCompletion D.host.E) = D.host.g k ∧ ∀ L : GlobalTheory.GLq.LabelDatum (D.host.g k), L.teich = D.ntypes.teichC k → L.gen = Γ.ζ k → ∃ θ : (ZMod (D.host.g k))ˣ →* ℂˣ, CharLift θ χ ∧ GlobalTheory.GLp.IsCharLab L θ u := by
  intro H hL D Γ k v χ hχ u htame hlab
  haveI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩
  haveI : IsTotallyComplex D.host.E := D.sp.cm.cmUnram.1
  have hp : resCard ((D.naut.plGw k v).adicCompletion D.host.E) = D.host.g k := by
    haveI : IsGalois ℚ D.host.E := D.host.hostE_isGalois
    obtain ⟨h1, -, -⟩ := GlobalTheory.Mem.Chr.splitsC_place (D.host.g_prime k) (D.nd.g_split k) _ (D.naut.plGw_over k v)
    exact (GlobalTheory.LocLanglands.resCard_eq_normV _).trans h1
  refine ⟨hp, fun L hteich hgen => ?_⟩
  obtain ⟨θ, hθ⟩ := exists_charLift hp htame
  set x := _root_.GlobalTheory.CuspRep.ParLawsT.locRecT hL (D.nd.plOm.2 (D.naut.plGw k v))
    (GlobalTheory.LocLanglands.cls (IrrRep.det (Fin 1) χ hχ)) with hx
  have hlab' : GlobalTheory.WeilDeligne.WD.lab (D.ntypes.teichC k) (D.ntypes.tg k v) x = X - C u := hlab
  refine ⟨θ, hθ, fun hu0 => ?_, fun u' hu' => ?_⟩
  · have := GlobalTheory.WeilDeligne.WD.lab_coeff_zero_ne_zero (D.ntypes.teichC k) (D.ntypes.tg k v) x
    rw [hlab', hu0] at this
    simp at this
  · obtain ⟨I⟩ := GlobalTheory.TypeIdent.nonempty_ident D
    obtain ⟨P, hP, hPe⟩ := exists_label L θ u' hu'
    have hT : Formalism.L2.NT.TameCoupled (D.nd.plOm.1 (D.naut.plGw k v)) (Γ.kv k v) (D.ntypes.tg k v) L.gen := by
      rw [hgen]; exact Γ.tg_tame k v
    have h1 := H D.host.E D.nd.Om (D.host.g k) _ _ (D.nd.plOm.2 (D.naut.plGw k v)) _
      (_root_.GlobalTheory.CuspRep.ParLawsT.isRecT_locRecT hL _) (I.i k v) (I.cont k v) (Γ.kv k v) L _ (D.ntypes.tg_mem k v) hT 1 (Or.inl rfl)
      (IrrRep.det (Fin 1) χ hχ) (GlobalTheory.LocGL.IrrGL.isCusp_ofChar χ hχ) (tauOne θ) P hP
      (inflates_det (I.i k v) (I.cont k v) hχ hθ)
    rw [hPe] at h1
    first | (have hOpn := UpperTheory.One.M.opn _ (_root_.GlobalTheory.CuspRep.ParLawsT.isRecT_locRecT hL (D.nd.plOm.2 (D.naut.plGw k v))); obtain ⟨a, ha, ε, hl⟩ := hOpn) | obtain ⟨a, ha, ε, -, hl⟩ := _root_.GlobalTheory.CuspRep.ParLawsT.isRecT_locRecT hL (D.nd.plOm.2 (D.naut.plGw k v))
    have hdim : x.lpDim = 1 := hl.dim _
    have h2 := GlobalTheory.WeilDeligne.WD.inePol_eq_of_natDegree_lab (D.ntypes.teichC k) (D.ntypes.tg k v) x
      (by rw [hlab', hdim, natDegree_X_sub_C])
    have hr : Formalism.CyclotomicNorms.rootsBar (X - C u) = {algebraMap (ZMod (D.host.g k)) (Formalism.CyclotomicNorms.Fbar (D.host.g k)) u} := by
      simp [Formalism.CyclotomicNorms.rootsBar]
    rw [hlab', hr, h1] at h2
    have h3 := congrArg (fun q => q.coeff 0) h2
    simp at h3
    rw [hteich]
    exact h3
set_option maxHeartbeats 1000000 in
theorem labAt_ofDet_tame_eq_X_sub_C : _root_.DiscreteGroups.sglob.DzType.DepthZeroInertiaBigAlt → ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : Formalism.BasicNotions.D7) (Γ : GlobalTheory.HeightCounting.GrpSide D) (k : Fin 2) (v : D.nd.PlG k) (χ : ((D.naut.plGw k v).adicCompletion D.host.E)ˣ →* ℂˣ) (hχ : IsSmoothChar χ) (u : ZMod (D.host.g k)), IsTame χ → _root_.GlobalTheory.PendOf.localLabelPolynomial hL D k v (Irr.ofDet 1 χ hχ) = Polynomial.X - Polynomial.C u → haveI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩; resCard ((D.naut.plGw k v).adicCompletion D.host.E) = D.host.g k ∧ ∀ L : GlobalTheory.GLq.LabelDatum (D.host.g k), L.teich = D.ntypes.teichC k → L.gen = Γ.ζ k → ∃ θ : (ZMod (D.host.g k))ˣ →* ℂˣ, CharLift θ χ ∧ GlobalTheory.GLp.IsCharLab L θ u :=
  _root_.DiscreteGroups.sglob.DzType.Rt.label_reduction_alt
end DiscreteGroups.sglob.DzType.Rt
end
end
