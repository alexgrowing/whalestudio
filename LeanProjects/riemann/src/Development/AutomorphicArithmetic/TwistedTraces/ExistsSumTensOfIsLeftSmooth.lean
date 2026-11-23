import Development.AutomorphicArithmetic.Foundations.Convolution.PowerSumTraces.DecayTraceClassAlt
import Development.AutomorphicArithmetic.Foundations.Convolution.TensFun
import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.KernelTransforms.TensApply
import GroundTheory.AutomorphicForms.CuspidalDiscreteness.DecayUniform
import GroundTheory.AutomorphicForms.CuspidalDiscreteness.CuspFormsHeight
import GroundTheory.AutomorphicForms.DixmierMalliavin
import Development.AutomorphicArithmetic.TwistedTraces.ExistsFiniteBasisLeftInvariantCompactSupport
import Development.AutomorphicArithmetic.TwistedTraces.ExistsSmoothTKbarEqRestriction

open MeasureTheory NumberField GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum PositivityTheory.Rg.Tf.Core UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C
open scoped ContDiff

private theorem split_pt {K : Type} [Field K] [NumberField K] {n : ℕ} (x : G1 K n) :
    x = archP K n (infPart K n (x : AdelicGLn.AdelicGL K n)) *
      MultiplicityOne.finProj K n (finPart K n (x : AdelicGLn.AdelicGL K n)) := by
  have h1 : retractOne (finEmb K n (finPart K n (x : AdelicGLn.AdelicGL K n))) =
      MultiplicityOne.finProj K n (finPart K n (x : AdelicGLn.AdelicGL K n)) := by
    ext1
    rfl
  rw [← h1, ← retract_infEmb, ← retractOne_mul, infEmb_infPart_mul_finEmb_finPart, retractOne_coe]

private theorem finPart_split {K : Type} [Field K] [NumberField K] {n : ℕ} (A : archGroup K n)
    (h : AdelicGLn.FiniteAdelicGL K n) :
    finPart K n ((archP K n A * MultiplicityOne.finProj K n h : G1 K n) : AdelicGLn.AdelicGL K n) = h := by
  have h1 : retractOne (finEmb K n h) = MultiplicityOne.finProj K n h := by
    ext1
    rfl
  rw [Subgroup.coe_mul, map_mul, finPart_archP, one_mul, ← h1, finPart_retract, finPart_finEmb]

theorem UpperTheory.exists_sum_tens_of_isLeftSmooth :
    ∀ (K : Type) [Field K] [NumberField K] (n : ℕ), 0 < n → ∀ a : CC K n, IsLeftSmooth a →
        ∃ (U : Subgroup (AdelicGLn.integralFiniteGL K n)) (_ : IsOpen (U : Set (AdelicGLn.integralFiniteGL K n)))
          (m : ℕ) (F : Fin m → TI K n) (e : Fin m → TF K n), (∀ j, SmoothT (F j)) ∧
          (∀ j, ∀ u ∈ U, ∀ h, e j ((u : AdelicGLn.FiniteAdelicGL K n) * h) = e j h) ∧ a = ∑ j, tens (F j) (e j) := by
  intro K _ _ n hn a ha
  obtain ⟨hsm, U, hU, hinv⟩ := ha
  have hVo : IsOpen (((finOpenSubgroup U hU).toSubgroup : Subgroup _) : Set (AdelicGLn.FiniteAdelicGL K n)) :=
    (finOpenSubgroup U hU).isOpen
  have hVc : IsCompact (((finOpenSubgroup U hU).toSubgroup : Subgroup _) : Set (AdelicGLn.FiniteAdelicGL K n)) :=
    isCompact_openSubgroupOf U hU
  have hS : IsCompact ((fun x : G1 K n => finPart K n (x : AdelicGLn.AdelicGL K n)) '' tsupport a) :=
    a.hasCompactSupport.isCompact.image (continuous_finPart.comp continuous_subtype_val)
  obtain ⟨m, b, e, heV, hE⟩ := UpperTheory.exists_finite_basis_leftInvariant_compactSupport _ (finOpenSubgroup U hU).toSubgroup hVo hVc _ hS
  choose F hF hFk using fun j => UpperTheory.exists_smoothT_kbar_eq_restriction K n hn a (MultiplicityOne.finProj K n (b j)) (hsm _)
  refine ⟨U, hU, m, F, e, hF, fun j u hu h => heV j _ (coe_mem_openSubgroupOf U hU hu) h, ?_⟩
  ext x
  have hsum : ∀ (s : Finset (Fin m)), (∑ j ∈ s, tens (F j) (e j)) x = ∑ j ∈ s, tens (F j) (e j) x := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp
    | insert i s hi ih =>
      rw [Finset.sum_insert hi, Finset.sum_insert hi, CompactlySupportedContinuousMap.add_apply, ih]
  rw [hsum Finset.univ]
  simp only [(UpperTheory.ConvolutionTheory.Tf.tensApply K n hn _ _).1, tensFun, hFk]
  have hfV : ∀ v ∈ (finOpenSubgroup U hU).toSubgroup, ∀ h,
      a (archP K n (infPart K n (x : AdelicGLn.AdelicGL K n)) * MultiplicityOne.finProj K n (v * h)) =
        a (archP K n (infPart K n (x : AdelicGLn.AdelicGL K n)) * MultiplicityOne.finProj K n h) := by
    intro v hv h
    have hv' : v ∈ (finOpenSubgroup U hU : Set (AdelicGLn.FiniteAdelicGL K n)) := hv
    rw [coe_openSubgroupOf] at hv'
    obtain ⟨u, hu, rfl⟩ := hv'
    rw [map_mul (MultiplicityOne.finProj K n), MultiplicityOne.finProj_eq_finOne, ← mul_assoc, archimedeanProjection_mul_finiteEmbedding_comm, mul_assoc, hinv u hu]
  have hfS : ∀ h, h ∉ (fun x : G1 K n => finPart K n (x : AdelicGLn.AdelicGL K n)) '' tsupport a →
      a (archP K n (infPart K n (x : AdelicGLn.AdelicGL K n)) * MultiplicityOne.finProj K n h) = 0 := by
    intro h hh
    by_contra hne
    exact hh ⟨_, subset_tsupport _ hne, finPart_split _ h⟩
  have key := hE (fun h => a (archP K n (infPart K n (x : AdelicGLn.AdelicGL K n)) * MultiplicityOne.finProj K n h))
    hfV hfS (finPart K n (x : AdelicGLn.AdelicGL K n))
  simp only [← split_pt x] at key
  rw [key]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [mul_comm]
