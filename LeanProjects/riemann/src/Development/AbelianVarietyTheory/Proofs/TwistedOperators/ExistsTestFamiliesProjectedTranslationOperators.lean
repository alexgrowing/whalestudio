import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HasTypeVec
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ExponentSeparation
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.EventuallyAlgebraMapMemIntegers
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HeckeOperatorConvolutionAndLeftTranslateStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ConvolutionFiniteAdelicPureTensorEqLocalConvolutStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsTypeIwahoriMaximalCompactIdempotentFamilyStatement
open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped Classical

noncomputable section

namespace GlobalTheory.TestFamTr

section Local

variable {G : Type} [Group G] [MeasurableSpace G] [MeasurableMul G] {μ : Measure G} [μ.IsMulLeftInvariant]

theorem conv_translate_left (f f' : G → ℂ) (c y : G) :
    GlobalTheory.AutomorphicL2Unitary.conv μ (fun x => f (c * x)) f' y = GlobalTheory.AutomorphicL2Unitary.conv μ f f' (c * y) := by
  simp only [GlobalTheory.AutomorphicL2Unitary.conv]
  rw [← integral_mul_left_eq_self _ c⁻¹]
  congr 1
  funext x
  simp [mul_assoc]

theorem conv_mul_left {f f' : G → ℂ} {k : G} (hf : ∀ y, f (k * y) = f y) (x : G) :
    GlobalTheory.AutomorphicL2Unitary.conv μ f f' (k * x) = GlobalTheory.AutomorphicL2Unitary.conv μ f f' x := by
  have := conv_translate_left (μ := μ) f f' k x
  rw [← this]
  simp only [hf]

omit [MeasurableMul G] [μ.IsMulLeftInvariant] in

theorem conv_mul_right {f f' : G → ℂ} {k : G} (hf' : ∀ y, f' (y * k) = f' y) (x : G) :
    GlobalTheory.AutomorphicL2Unitary.conv μ f f' (x * k) = GlobalTheory.AutomorphicL2Unitary.conv μ f f' x := by
  simp only [GlobalTheory.AutomorphicL2Unitary.conv, ← mul_assoc, hf']

end Local

theorem test_families : ∀ (D : D7) (V : HSp D) (T : TypeDataG V) (U : AuxiliaryPlaceHermitianSpace V), U.u ∉ T.S → ∀ (μf : ∀ v, Measure (GLoc D.sp.cm.sig V.gram v)), (∀ v, (μf v).IsHaarMeasure) → (∀ᶠ v in cofinite, μf v (Kv V v) = 1) → ∀ ν, IsFinMeas V μf ν → ∃ e, IsFinFamily D.sp.cm.sig V.gram (frameLat V) e ∧ (∀ (W : Type) [AddCommGroup W] [Module ℂ W] (σ : Representation ℂ (GfC V) W), GlobalTheory.PRep.IsSmooth σ → ∀ P, GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets.IsIntegralOp ν σ (finFn V e) P → P ∘ₗ P = P ∧ (HasTypeVec T σ → P ≠ 0)) ∧ ∀ g : GfC V, ∃ ff, IsFinFamily D.sp.cm.sig V.gram (frameLat V) ff ∧ (∀ k ∈ U.frame.iwahori, ∀ x, ff U.u (k * x) = ff U.u x) ∧ (∀ t ∈ strictTorus V.rank U.ϖ, IsTestFin T U μf (Function.update ff U.u (U.frame.cosetFn t)) ∧ SphRest T U (Function.update ff U.u (U.frame.cosetFn t))) ∧ ∀ (W : Type) [AddCommGroup W] [Module ℂ W] (σ : Representation ℂ (GfC V) W), GlobalTheory.PRep.IsSmooth σ → ∀ P, GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets.IsIntegralOp ν σ (finFn V e) P → GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets.IsIntegralOp ν σ (finFn V ff) (P ∘ₗ σ g ∘ₗ P) := by
  intro D V T U hu μf hμf h1 ν hν
  obtain ⟨e, heF, heS, hee, heI, heSph, heNZ⟩ := GlobalTheory.T.exists_typeIwahoriMaximalCompact_idempotentFamily D V T U hu μf hμf h1 ν hν
  obtain ⟨-, hconv, hSB⟩ := GlobalTheory.T.convolution_finiteAdelicPureTensor_eq_localConvolutions D V μf hμf h1 ν hν e e heF heF
  have hfe : GlobalTheory.AutomorphicL2Unitary.conv ν (finFn V e) (finFn V e) = finFn V e := by
    rw [← hconv]
    congr 1
    funext v
    exact hee v
  refine ⟨e, heF, ?_, ?_⟩
  · intro W _ _ σ hσ P hP
    haveI := hν.1
    have h := (GlobalTheory.T.heckeOperator_convolution_and_leftTranslate (GfC V) ν W σ hσ (finFn V e) hSB (finFn V e) hSB P P hP hP).1
    rw [hfe] at h
    exact ⟨h.unique hP, fun ht => heNZ W σ hσ ht P hP⟩
  · intro g
    haveI := hν.1
    set c : ∀ v, GLoc D.sp.cm.sig V.gram v := fun v => (proj D.sp.cm.sig V.gram v (g : GA D V))⁻¹ with hc
    set b : ∀ v, GLoc D.sp.cm.sig V.gram v → ℂ := fun v x => e v (c v * x) with hb
    have hbF : IsFinFamily D.sp.cm.sig V.gram (frameLat V) b := by
      refine ⟨fun v => comp_mem_SB (heF.1 v) (Homeomorph.mulLeft (c v)), ?_⟩
      filter_upwards [heF.2, eventually_proj_mem_stabLoc D.sp.cm.sig V.gram (frameLat V) (g : GA D V)] with v he hg
      funext x
      have hcv : c v ∈ stabLoc D.sp.cm.sig V.gram (frameLat V) v := inv_mem hg
      simp only [hb, he, unitLoc, Set.indicator, SetLike.mem_coe, Subgroup.mul_mem_cancel_left _ hcv, Pi.one_apply]
    have hbfin : finFn V b = fun x => finFn V e (g⁻¹ * x) := by
      funext x
      simp [finFn, hb, hc, map_mul, map_inv]
    obtain ⟨hffF, hffeq, -⟩ := GlobalTheory.T.convolution_finiteAdelicPureTensor_eq_localConvolutions D V μf hμf h1 ν hν e b heF hbF
    obtain ⟨-, -, hbSB⟩ := GlobalTheory.T.convolution_finiteAdelicPureTensor_eq_localConvolutions D V μf hμf h1 ν hν b b hbF hbF
    have hcb : ∀ v, GlobalTheory.AutomorphicL2Unitary.conv (μf v) (b v) (e v) = b v := fun v => by
      haveI := hμf v
      funext y
      rw [hb]
      simp only
      rw [conv_translate_left, hee v]
    refine ⟨fun v => GlobalTheory.AutomorphicL2Unitary.conv (μf v) (e v) (b v), hffF, ?_, ?_, ?_⟩
    · intro k hk x
      haveI := hμf U.u
      exact conv_mul_left (heI k hk) x
    · intro t ht
      have hne : ∀ v ∈ T.S, v ≠ U.u := fun v hv h => hu (h ▸ hv)
      refine ⟨⟨hu, fun v => ⟨b v, hbF.1 v, ?_⟩, ⟨t, ht, Function.update_self ..⟩, fun v _ hv' => ?_, ?_⟩, ?_⟩
      · haveI := hμf v
        have hcont : ∀ f ∈ GlobalTheory.SplitWeil.SB (GLoc D.sp.cm.sig V.gram v), Continuous f ∧ HasCompactSupport f :=
          fun f hf => ⟨hf.1.continuous, hf.2⟩
        rw [Function.update_of_ne (hne v v.2), ← heS v,
          GlobalTheory.Orb.conv_assoc (hcont _ (heF.1 v)).1 (hcont _ (heF.1 v)).2 (hcont _ (hbF.1 v)).1 (hcont _ (hbF.1 v)).2
            (hcont _ (heF.1 v)).1, hcb]
      · rw [Function.update_of_ne hv']
        exact hffF.1 v
      · filter_upwards [hffF.2, eventually_cofinite_ne U.u] with v hv hv'
        rw [Function.update_of_ne hv']
        exact hv
      · intro v hv hvu k hk k' hk' x
        haveI := hμf v
        simp only [Function.update_of_ne hvu]
        rw [conv_mul_right, conv_mul_left]
        · intro y
          simpa using heSph v hv hvu k hk 1 (one_mem _) y
        · intro y
          simp only [hb]
          simpa [mul_assoc] using heSph v hv hvu 1 (one_mem _) k' hk' (c v * y)
    · intro W _ _ σ hσ P hP
      have h2 := (GlobalTheory.T.heckeOperator_convolution_and_leftTranslate (GfC V) ν W σ hσ (finFn V e) hSB (finFn V e) hSB P P hP hP).2 g
      rw [← hbfin] at h2
      have h3 := (GlobalTheory.T.heckeOperator_convolution_and_leftTranslate (GfC V) ν W σ hσ (finFn V e) hSB (finFn V b) hbSB P _ hP h2).1
      rwa [← hffeq] at h3
