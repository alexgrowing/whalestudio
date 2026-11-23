import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.FinIso
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingSpecNormalisedCharacterEq
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RecProdRecSatakeLL
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StandardCosocleGL
import Formalism.SharpRestriction.LevelLetterCocycles.SphericalInertData
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteInertHeckeSupportCosets
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.InertSatakeParametersEqOfIso
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UnitaryDoubleCosetFiniteLeftCosets
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemMaxCompactOfTrivOutsideLocalIntegral
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.FiniteDimensionalForms
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteDoubleCosetsDefiniteUnitaryMaximalLevelStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HasSatakeGLOfIsSatVecGL
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsLevelFullAtInertPlacePrincipalElsewhereStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsSatUEigenvectorStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HeckeFunIAddSmulStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.InertHeckeOperatorPreservesProductLevelInvariancStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.InertHeckeOperatorMaximalCompactIndicatorEqIdStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.InertHeckeOperatorConvolutionEqCompStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host GlobalTheory.HeightCounting NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.FormDict GlobalTheory.DefiniteBC
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.SatExist

theorem exists_satAt : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (F : FinIso L n) (π : NG.AutRep L n) (U : Submodule ℂ (UA L n → ℂ)), Dict F π U → ∀ (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) (w : HeightOneSpectrum (𝓞 L)), NG.OverPl w v → π.SphAt v → ∀ Dv : InertDatum L n v w, ∃ α, NG.SatAt π Dv α := by
  classical
  intro L _ _ _ n F π U₀ _ v w _ hsph Dv
  obtain ⟨f₀, hf₀S, hf₀0, hf₀K⟩ := hsph
  obtain ⟨-, N, hN, hf₀N⟩ := π.irrS.1.le hf₀S
  obtain ⟨U, hCU, hU, hdec⟩ := GlobalTheory.T.exists_level_full_at_inert_place_principal_elsewhere L n v N hN
  have hdec' : ∀ κ ∈ U, ∃ a b : GAf L n, κ = a * b ∧ a ∈ Umax L n ∧ TrivOutside {v} a ∧ b ∈ U ∧
      ∀ x : GAf L n, TrivOutside {v} x → b * x = x * b := fun κ hκ => by
    obtain ⟨a, b, e, ha, hta, hb, hc⟩ := hdec κ hκ
    exact ⟨a, b, e, ha, hta, hCU b hb, hc⟩
  have hf₀U : ∀ κ ∈ U, NG.rt L n κ f₀ = f₀ := fun κ hκ => by
    obtain ⟨a, b, rfl, ha, hta, hb, -⟩ := hdec κ hκ
    funext g
    show f₀ (g * (a * b)) = f₀ g
    rw [← mul_assoc, hf₀N b hb]
    exact congrFun (hf₀K a ha hta) g
  let V : Submodule ℂ (GAf L n → π.W) :=
    { carrier := {f | f ∈ π.S ∧ ∀ κ ∈ U, NG.rt L n κ f = f}
      add_mem' := fun {f f'} hf hf' => ⟨π.S.add_mem hf.1 hf'.1, fun κ hκ => by
        rw [map_add, hf.2 κ hκ, hf'.2 κ hκ]⟩
      zero_mem' := ⟨π.S.zero_mem, fun κ _ => map_zero _⟩
      smul_mem' := fun c f hf => ⟨π.S.smul_mem c hf.1, fun κ hκ => by rw [map_smul, hf.2 κ hκ]⟩ }
  haveI : FiniteDimensional ℂ π.W := π.alg.1
  haveI := GlobalTheory.AlgFormsFin.fixedForms_finite L n π.ρ (GlobalTheory.T.finite_doubleCosets_definiteUnitary_maximalLevel L n) hN
  haveI hVfin : FiniteDimensional ℂ V :=
    Submodule.finiteDimensional_of_le (S₂ := GlobalTheory.AlgFormsFin.fixedForms L n π.ρ N) fun f hf =>
      ⟨(π.irrS.1.le hf.1).1, fun κ hκ g => congrFun (hf.2 κ (hCU κ hκ)) g⟩
  have hfin := fun h hh => GlobalTheory.SatInd.CosetFin.finite_inert_support L n v w Dv
    (GlobalTheory.SatInd.DCoset.finite_dcoset Dv.ϖ Dv.σw _ n Dv.unram)
    (GlobalTheory.InertUmax.mem_Umax_of_trivOutside_of_loc_integral L n v w Dv) U hU h hh
  have hmemV : ∀ h ∈ Formalism.UG.Hecke ℂ (Formalism.UG.KU Dv.σw n), ∀ f ∈ V, heckeFunI L n U Dv h f ∈ V := by
    intro h hh f hf
    refine ⟨?_, GlobalTheory.T.inertHeckeOperator_preserves_productLevel_invariance L n v w Dv U hU hdec' π.W h hh f hf.2⟩
    obtain ⟨C, a, x, hC⟩ := GlobalTheory.SatIso.heckeFunI_eq_sum Dv U h (hfin h hh)
    rw [hC]
    exact π.S.sum_mem fun c _ => π.S.smul_mem _ (π.irrS.1.stable _ _ hf.1)
  let T : (Formalism.UG.GU Dv.σw n → ℂ) → Module.End ℂ V := fun h =>
    if hh : h ∈ Formalism.UG.Hecke ℂ (Formalism.UG.KU Dv.σw n) then
      { toFun := fun f => ⟨heckeFunI L n U Dv h f, hmemV h hh f f.2⟩
        map_add' := fun f f' => Subtype.ext (by
          obtain ⟨C, a, x, hC⟩ := GlobalTheory.SatIso.heckeFunI_eq_sum Dv U h (hfin h hh)
          simp only [Submodule.coe_add, hC, map_add, smul_add, Finset.sum_add_distrib])
        map_smul' := fun c f => Subtype.ext (by
          obtain ⟨C, a, x, hC⟩ := GlobalTheory.SatIso.heckeFunI_eq_sum Dv U h (hfin h hh)
          simp only [Submodule.coe_smul, hC, map_smul, RingHom.id_apply, Finset.smul_sum]
          exact Finset.sum_congr rfl fun c' _ => smul_comm _ _ _) }
    else 0
  have hT : ∀ h (hh : h ∈ Formalism.UG.Hecke ℂ (Formalism.UG.KU Dv.σw n)) (f : V),
      ((T h f : V) : GAf L n → π.W) = heckeFunI L n U Dv h f := fun h hh f => by
    simp only [T, dif_pos hh]
    rfl
  have hK := Formalism.UG.P.isCommensurated_integral_unitary_of_unramified Dv.unram n
  obtain ⟨α, x, hx0, hx⟩ := GlobalTheory.T.exists_satU_eigenvector_alt Dv.ϖ Dv.σw _ n Dv.unram V T
    (fun h₁ hh₁ h₂ hh₂ => LinearMap.ext fun f => Subtype.ext (by
      rw [LinearMap.add_apply, Submodule.coe_add, hT (h₁ + h₂) (add_mem hh₁ hh₂) f, hT h₁ hh₁ f, hT h₂ hh₂ f]
      exact (GlobalTheory.T.heckeFunI_add_and_smul L n v w Dv U hU π.W h₁ h₂ hh₁ hh₂ 0 f).1))
    (fun c h hh => LinearMap.ext fun f => Subtype.ext (by
      rw [LinearMap.smul_apply, Submodule.coe_smul, hT (c • h) (Submodule.smul_mem _ c hh) f, hT h hh f]
      exact (GlobalTheory.T.heckeFunI_add_and_smul L n v w Dv U hU π.W h h hh hh c f).2))
    (LinearMap.ext fun f => Subtype.ext (by
      rw [hT _ (Formalism.UG.Final.DosetIndMem _ _ ℂ 1) f]
      exact GlobalTheory.T.inertHeckeOperator_maximalCompact_indicator_eq_id L n v w Dv U hU π.W f f.2.2))
    (fun h₁ hh₁ h₂ hh₂ => LinearMap.ext fun f => Subtype.ext (by
      rw [Module.End.mul_apply, hT _ (Formalism.UG.Final.HeckeConvMem _ _ ℂ hK _ hh₁ _ hh₂) f, hT h₁ hh₁ (T h₂ f), hT h₂ hh₂ f]
      exact GlobalTheory.T.inertHeckeOperator_convolution_eq_comp L n v w Dv U hU π.W h₁ h₂ hh₁ hh₂ f f.2.2))
    ⟨f₀, hf₀S, hf₀U⟩ (fun h => hf₀0 (congrArg Subtype.val h))
  refine ⟨α, x, x.2.1, fun h => hx0 (Subtype.ext h), U, x.2.2, hU, fun h hh => ?_⟩
  have e := congrArg Subtype.val (hx h hh)
  rw [hT h hh] at e
  exact e

end GlobalTheory.SatExist
