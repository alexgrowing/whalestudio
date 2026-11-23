import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsSphGL
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.WeilSiegelFormulaUnitary
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsIsSplitChartOfBasis
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsIsSplitChartOne
import Development.AbelianVarietyTheory.Definitions.Foundations.EqPlaceIdemOfIsPrimeIdem
import Development.AbelianVarietyTheory.Proofs.HeightProofs.EqOrConjOfPlaceOf
import Development.AbelianVarietyTheory.Definitions.Foundations.OfInfProjInfMulOfFinProjFin
open scoped ComplexConjugate Matrix NNReal ENNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec ThetaClause SectionClause CoefClause)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.IP GlobalTheory.Core.Rk.SWLaw
open GlobalTheory.Core.Rk.SW GlobalTheory.Core.Rk.SWQ
open Formalism.UG (IsUnifV qV Ov ordL diagJ)
open GlobalTheory.LFun (KGL toCompl IsSplitChart IsSatVecGL satEig)
open scoped Classical

namespace GlobalTheory.Core.Rk.SplitIota

open GlobalTheory.AdelicU.Supp GlobalTheory.LFun.ConjPlace
open scoped TensorProduct

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

omit [NumberField E] in
theorem sigR_compFin' (σ : E →ₐ[F] E) (v : HeightOneSpectrum (𝓞 F)) (z : AF F ⊗[F] E) :
    Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR _ σ (compFin F E v z) = compFin F E v (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR _ σ z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a x => rfl
  | add x y hx hy => simp only [map_add, hx, hy]

theorem continuous_complEquiv_symm {σ : E →ₐ[F] E} {v : HeightOneSpectrum (𝓞 F)} {w : HeightOneSpectrum (𝓞 E)}
    (hE : IsCMExt F E σ) (h : w.under (𝓞 F) = v) {τ : E →ₐ[F] Fv F v} (hτ : splitPrime τ = w) :
    Continuous (complEquiv hE h hτ).symm := by
  let _ : Algebra (Fv F v) (w.adicCompletion E) := (GlobalTheory.LFun.complMap h).toAlgebra
  have : ContinuousSMul (Fv F v) (w.adicCompletion E) :=
    continuousSMul_of_algebraMap _ _ (GlobalTheory.LFun.SplitChart.continuous_complMap h)
  let _ : NontriviallyNormedField (Fv F v) := Valued.toNontriviallyNormedField _ _
  let f : Fv F v ≃ₐ[Fv F v] w.adicCompletion E :=
    { complEquiv hE h hτ with commutes' := fun a => rfl }
  have : FiniteDimensional (Fv F v) (w.adicCompletion E) := f.toLinearEquiv.finiteDimensional
  have : IsModuleTopology (Fv F v) (w.adicCompletion E) := isModuleTopologyOfFiniteDimensional
  exact IsModuleTopology.continuous_of_linearMap f.symm.toLinearMap

theorem continuous_compW {v : HeightOneSpectrum (𝓞 F)} {w : HeightOneSpectrum (𝓞 E)} (h : w.under (𝓞 F) = v) :
    Continuous fun a : AF F ⊗[F] E => GlobalTheory.LFun.toCompl h (compFin F E v a) := by
  have : IsModuleTopology (AF F) (AF F ⊗[F] E) := ⟨rfl⟩
  refine IsModuleTopology.continuous_of_ringHom (R := AF F) ((GlobalTheory.LFun.toCompl h).comp (compFin F E v)) ?_
  have e : (((GlobalTheory.LFun.toCompl h).comp (compFin F E v)).comp (algebraMap (AF F) (AF F ⊗[F] E)) :
      AF F → w.adicCompletion E) = fun a => GlobalTheory.LFun.complMap h (evFin F v a) := by
    funext a
    exact (GlobalTheory.LFun.toCompl_tmul h (evFin F v a) (1 : E)).trans (by rw [map_one, mul_one])
  rw [e]
  exact (GlobalTheory.LFun.SplitChart.continuous_complMap h).comp ((RestrictedProduct.continuous_eval v).comp continuous_snd)

theorem exists_iota_gen {σ : E →ₐ[F] E} {v : HeightOneSpectrum (𝓞 F)} {w : HeightOneSpectrum (𝓞 E)}
    (hE : IsCMExt F E σ) (h : w.under (𝓞 F) = v) {τ : E →ₐ[F] Fv F v} (hτ : splitPrime τ = w) :
    ∃ ι : w.adicCompletion E →+ AF F ⊗[F] E, Continuous ι ∧
      (∀ x, GlobalTheory.LFun.toCompl h (compFin F E v (ι x)) = x) ∧
      (∀ x, GlobalTheory.LFun.toCompl h (compFin F E v (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR _ σ (ι x))) = 0) ∧
      (∀ x, algebraMap (AF F) (AF F ⊗[F] E) (pairA F 0 (singleFin v 1)) * ι x = ι x) ∧
      (∀ a x, a * ι x = ι (GlobalTheory.LFun.toCompl h (compFin F E v a) * x)) ∧
      (∀ a, algebraMap (AF F) (AF F ⊗[F] E) (pairA F 0 (singleFin v 1)) * a =
        ι (GlobalTheory.LFun.toCompl h (compFin F E v a)) +
          Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR _ σ (ι (GlobalTheory.LFun.toCompl h (compFin F E v (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR _ σ a))))) ∧
      ι 1 = singleTens E v (splitIdem hE τ) := by
  set c := complEquiv hE h hτ
  have hcw : ∀ y, GlobalTheory.LFun.toCompl h y = c (splitProj τ y) := fun y => toCompl_eq hE h hτ y
  have hcc : Continuous c.symm := continuous_complEquiv_symm hE h hτ
  let s : w.adicCompletion E →+ Fv F v ⊗[F] E :=
    (splitAlgEquiv hE τ).symm.toRingEquiv.toAddEquiv.toAddMonoidHom.comp
      ((AddMonoidHom.inl _ _).comp c.symm.toAddEquiv.toAddMonoidHom)
  have s1 : ∀ x, splitProj τ (s x) = c.symm x := fun x => splitProj_symm hE τ _
  have s2 : ∀ x, splitProj (τ.comp σ) (s x) = 0 := fun x => splitProj_comp_symm hE τ _
  have hs1 : s 1 = splitIdem hE τ := by
    show (splitAlgEquiv hE τ).symm (c.symm 1, 0) = _
    rw [map_one]; rfl
  have hsc : Continuous s :=
    (continuous_splitAlgEquiv_symm hE τ).comp ((continuous_id.prodMk continuous_const).comp hcc)
  clear_value s
  have hst : Continuous (singleTens E v) :=
    GlobalTheory.AutFunCompare.continuous_tensNU (E := E) _ _ (Continuous.prodMk continuous_const (continuous_singleFin v))
  have hpl : algebraMap (AF F) (AF F ⊗[F] E) (pairA F 0 (singleFin v 1)) = singleTens E v 1 := rfl
  refine ⟨(singleTens E v).toAddMonoidHom.comp s, hst.comp hsc, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro x
    show GlobalTheory.LFun.toCompl h (compFin F E v (singleTens E v (s x))) = x
    rw [compFin_singleTens_self, hcw, s1, RingEquiv.apply_symm_apply]
  · intro x
    show GlobalTheory.LFun.toCompl h (compFin F E v (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR _ σ (singleTens E v (s x)))) = 0
    rw [sigR_singleTens, compFin_singleTens_self, hcw, ← splitProj_comp, s2, map_zero]
  · intro x
    show _ * singleTens E v (s x) = singleTens E v (s x)
    rw [hpl, singleTens_mul, compFin_singleTens_self, one_mul]
  · intro a x
    show a * singleTens E v (s x) = singleTens E v (s _)
    rw [mul_comm, singleTens_mul]
    refine congrArg _ (split_ext hE τ ?_ ?_)
    · rw [map_mul, s1, s1, hcw, map_mul, RingEquiv.symm_apply_apply, mul_comm]
    · rw [map_mul, s2, s2, zero_mul]
  · intro a
    show _ = singleTens E v (s _) + Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR _ σ (singleTens E v (s _))
    rw [hpl, singleTens_mul, one_mul, sigR_singleTens, ← map_add]
    refine congrArg _ (split_ext hE τ ?_ ?_)
    · rw [map_add, s1, hcw, RingEquiv.symm_apply_apply, ← splitProj_comp, s2, add_zero]
    · rw [map_add, s2, zero_add, splitProj_comp_sigR hE, s1, hcw, RingEquiv.symm_apply_apply,
        ← sigR_compFin', splitProj_comp]
  · show singleTens E v (s 1) = _
    rw [hs1]

end GlobalTheory.Core.Rk.SplitIota

open scoped TensorProduct

open GlobalTheory.Core.Rk.SplitIota in

theorem GlobalTheory.Core.Rk.SplitIota.exists_iota : ∀ (D : D7) (q : FinPl D) (w : HeightOneSpectrum (𝓞 D.host.E)) (h : w.under (𝓞 D.host.F) = q), Formalism.MainNotions.SchurIrreducible.IsSplit (E := D.host.E) q → ∃ ι : w.adicCompletion D.host.E →+ AE D, Continuous ι ∧ (∀ x, cw h (ι x) = x) ∧ (∀ x, cw h (cA D (ι x)) = 0) ∧ (∀ x, algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 (singleFin q 1)) * ι x = ι x) ∧ (∀ a x, a * ι x = ι (cw h a * x)) ∧ (∀ a, algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 (singleFin q 1)) * a = ι (cw h a) + cA D (ι (cw h (cA D a)))) ∧ IsSplitIdem D (ι 1) ∧ Continuous (cw h) := by
  intro D q w h hs
  have hE := isCMExt_host D
  obtain ⟨P, Q, hPQ, hP, hQ⟩ := hs
  have hPu : P.under (𝓞 D.host.F) = q := HeightOneSpectrum.ext hP
  have hQu : Q.under (𝓞 D.host.F) = q := HeightOneSpectrum.ext hQ
  obtain ⟨w', hw', hw'u⟩ : ∃ w' : HeightOneSpectrum (𝓞 D.host.E), w ≠ w' ∧ w'.under (𝓞 D.host.F) = q := by
    by_cases e : w = P
    · exact ⟨Q, e ▸ hPQ, hQu⟩
    · exact ⟨P, e, hPu⟩
  obtain ⟨τ, hτ, -⟩ := GlobalTheory.AdelicU.existsUnique_splitPrime_eq hE hw' h hw'u
  obtain ⟨ι, h1, h2, h3, h4, h5, h6, h7⟩ := exists_iota_gen hE h hτ
  exact ⟨ι, h1, h2, h3, h4, h5, h6, GlobalTheory.AdelicU.Supp.isSplitIdem_iff_exists.2 ⟨q, τ, h7⟩, continuous_compW h⟩
