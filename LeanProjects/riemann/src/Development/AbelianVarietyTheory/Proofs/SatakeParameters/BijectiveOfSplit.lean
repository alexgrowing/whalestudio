import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.CyclicStrongAtCusp
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RamificationTowerCompatible
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsSubquotientComp
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.CuspRepSatakeParametersUniqueStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.PolarizedPairSatakeParameterConjugatePlace
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.PolOfSatOfThetaSat
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.ThetaSatakeParametersInverse
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AutomorphicFormsFiniteGL
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnramifiedFactorEqProductAbove
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.HeckeCharNormDescentStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.UnramifiedAtValueHeckeCharCompIdeleNormStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.UnderConjugatePlaceEqConjugatePlaceUnderStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.EventuallyCofiniteUnderOfEventuallyCofinitePlaceStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsNormVEqNormVUnderPowStatement
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.GLq
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.GalCut GlobalTheory.RoadU GlobalTheory.AboveL
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.CharLiftStep

open Matrix

variable {K M : Type} [Field K] [NumberField K] [Field M] [NumberField M] [Algebra K M]

theorem cycAt_or_split [IsGalois K M] (hp : (Module.finrank K M).Prime) (v : HeightOneSpectrum (𝓞 K))
    (u : HeightOneSpectrum (𝓞 M)) [u.asIdeal.LiesOver v.asIdeal] :
    GlobalTheory.FunExt.CycAt v u ∨ (u.asIdeal.ramificationIdx (𝓞 K) = 1 ∧ u.asIdeal.inertiaDeg (𝓞 K) = 1) := by
  have h2 := Ideal.ncard_primesOver_mul_ramificationIdxIn_mul_inertiaDegIn v.asIdeal (𝓞 M) Gal(M/K)
  rw [IsGalois.card_aut_eq_finrank, Ideal.ramificationIdxIn_eq_ramificationIdx v.asIdeal u.asIdeal Gal(M/K),
    Ideal.inertiaDegIn_eq_inertiaDeg v.asIdeal u.asIdeal Gal(M/K)] at h2
  have hp' := hp
  rw [← h2] at hp'
  rcases Nat.prime_mul_iff.1 hp' with ⟨-, h⟩ | ⟨-, h⟩
  · exact Or.inr (mul_eq_one.1 h)
  · left
    obtain ⟨a, ha⟩ := Set.ncard_eq_one.1 h
    have hu : u.under (𝓞 K) = v :=
      HeightOneSpectrum.ext (Ideal.LiesOver.over (P := u.asIdeal) (p := v.asIdeal)).symm
    refine ⟨inferInstance, hp, hu, fun u' hu' => ?_⟩
    have : u'.asIdeal.LiesOver v.asIdeal := ⟨by rw [← hu']; rfl⟩
    have m1 : u.asIdeal ∈ v.asIdeal.primesOver (𝓞 M) := ⟨u.isPrime, inferInstance⟩
    have m2 : u'.asIdeal ∈ v.asIdeal.primesOver (𝓞 M) := ⟨u'.isPrime, inferInstance⟩
    rw [ha, Set.mem_singleton_iff] at m1 m2
    exact HeightOneSpectrum.ext (m2.trans m1.symm)

section Split

variable (v : HeightOneSpectrum (𝓞 K)) (u : HeightOneSpectrum (𝓞 M)) [u.asIdeal.LiesOver v.asIdeal]

theorem bijective_of_split (he : u.asIdeal.ramificationIdx (𝓞 K) = 1) (hf : u.asIdeal.inertiaDeg (𝓞 K) = 1) :
    Function.Bijective (GroundTheory.Global.adicCompletionMap v u) := by
  letI : Algebra (v.adicCompletion K) (u.adicCompletion M) := (GroundTheory.Global.adicCompletionMap v u).toAlgebra
  have : ContinuousSMul (v.adicCompletion K) (u.adicCompletion M) :=
    continuousSMul_of_algebraMap _ _ (GroundTheory.Global.continuous_adicCompletionMap v u)
  have : IsScalarTower K (v.adicCompletion K) (u.adicCompletion M) :=
    .of_algebraMap_eq fun x => by
      show _ = GroundTheory.Global.adicCompletionMap v u _
      rw [GroundTheory.Global.adicCompletionMap_algebraMap, IsScalarTower.algebraMap_apply K M (u.adicCompletion M)]
  have h1 : Module.finrank (v.adicCompletion K) (u.adicCompletion M) = 1 := by
    rw [GroundTheory.Global.finrank_adicCompletion v u, he, hf]
  refine ⟨(GroundTheory.Global.adicCompletionMap v u).injective, fun y => ?_⟩
  have hy : y ∈ (⊥ : Subalgebra (v.adicCompletion K) (u.adicCompletion M)) :=
    (Subalgebra.bot_eq_top_of_finrank_eq_one h1) ▸ Algebra.mem_top
  obtain ⟨x, hx⟩ := Algebra.mem_bot.1 hy
  exact ⟨x, hx⟩

theorem normU_of_split (he : u.asIdeal.ramificationIdx (𝓞 K) = 1) (hf : u.asIdeal.inertiaDeg (𝓞 K) = 1) :
    Continuous (RingEquiv.ofBijective _ (bijective_of_split v u he hf)).symm ∧
      ∀ y : (u.adicCompletion M)ˣ, ((GlobalTheory.BCChar.normU v u y : (v.adicCompletion K)ˣ) : v.adicCompletion K) =
        (RingEquiv.ofBijective _ (bijective_of_split v u he hf)).symm y := by
  set i := RingEquiv.ofBijective _ (bijective_of_split v u he hf)
  letI : Algebra (v.adicCompletion K) (u.adicCompletion M) := (GroundTheory.Global.adicCompletionMap v u).toAlgebra
  have : ContinuousSMul (v.adicCompletion K) (u.adicCompletion M) :=
    continuousSMul_of_algebraMap _ _ (GroundTheory.Global.continuous_adicCompletionMap v u)
  have : IsScalarTower K (v.adicCompletion K) (u.adicCompletion M) :=
    .of_algebraMap_eq fun x => by
      show _ = GroundTheory.Global.adicCompletionMap v u _
      rw [GroundTheory.Global.adicCompletionMap_algebraMap, IsScalarTower.algebraMap_apply K M (u.adicCompletion M)]
  have h1 : Module.finrank (v.adicCompletion K) (u.adicCompletion M) = 1 := by
    rw [GroundTheory.Global.finrank_adicCompletion v u, he, hf]
  have hfd : FiniteDimensional (v.adicCompletion K) (u.adicCompletion M) := GroundTheory.Global.finite_adicCompletion v u
  have hc := (GlobalTheory.adicCompletion_trace_norm_continuous K M v u _ (GroundTheory.Global.continuous_adicCompletionMap v u) hfd).2
  have key : ∀ y : u.adicCompletion M, Algebra.norm (v.adicCompletion K) y = i.symm y := by
    intro y
    conv_lhs => rw [← i.apply_symm_apply y]
    show Algebra.norm (v.adicCompletion K) (algebraMap (v.adicCompletion K) (u.adicCompletion M) (i.symm y)) = _
    rw [Algebra.norm_algebraMap, h1, pow_one]
  refine ⟨?_, fun y => key y⟩
  have e : (i.symm : u.adicCompletion M → v.adicCompletion K) = fun y => Algebra.norm (v.adicCompletion K) y :=
    funext fun y => (key y).symm
  rw [e]
  exact hc

end Split

section Char

variable {k k' : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  [Field k'] [ValuativeRel k'] [TopologicalSpace k'] [IsNonarchimedeanLocalField k']

theorem trGL_ofChar (i : k ≃+* k') (hi' : Continuous i.symm) (χ : kˣ →* ℂˣ) (hχ : IsSmoothChar χ)
    (χ' : k'ˣ →* ℂˣ) (hχ' : IsSmoothChar χ')
    (h : ∀ y : k'ˣ, χ' y = χ (Units.map (i.symm : k' →* k) y)) :
    GlobalTheory.SuppIne.trGL i hi' (IrrGL.ofChar χ hχ) = IrrGL.ofChar χ' hχ' := by
  refine congrArg (Sigma.mk 1) (IrrRep.cl_eq_iff.2 ?_)
  obtain ⟨φ⟩ := IrrRep.nonempty_equiv_rep (IrrRep.det (Fin 1) χ hχ)
  refine ⟨Representation.Equiv.mk φ.toLinearEquiv fun g => ?_⟩
  have H := φ.toIntertwiningMap.isIntertwining' (Matrix.GeneralLinearGroup.map (n := Fin 1) i.symm.toRingHom g)
  refine LinearMap.ext fun x => ?_
  have Hx := LinearMap.congr_fun H x
  simp only [LinearMap.coe_comp, Function.comp_apply] at Hx ⊢
  change φ.toLinearEquiv _ = _
  refine Hx.trans ?_
  erw [Function.comp_apply, LinearMap.comp_apply, SmGL.twist_apply, SmGL.twist_apply]
  have e1 : ∀ g' : GL (Fin 1) k', (detChar (Fin 1) χ') g' =
      (detChar (Fin 1) χ) (GeneralLinearGroup.map i.symm.toRingHom g') := fun g' => by
    rw [detChar_apply, detChar_apply, Matrix.GeneralLinearGroup.map_det]; exact h _
  erw [e1 g]
  rfl

end Char

end GlobalTheory.CharLiftStep

end
