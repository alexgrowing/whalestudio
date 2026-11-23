import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.PlacesToAdeles
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FlatThetaMapsPreserveThetaFunctionsStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FlatThetaMapsConvergeThetaFunctionsStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HeisenbergOperatorThetaFunctionalMixedSourceModeStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HeisenbergThetaMixedModelTargetOfMixedModelStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MixedCoordinatesOfThetaFunctionAreThetaFunctionsStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BesselToJacobiFlatSchwartzEquivariantStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.JacobiToBesselFlatIntertwinesWeilActionStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FlatSchwartzTargetUnipotentConjBesselCharacterStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeilDatumDescendsToWittCoreStatement

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FlatLawsDuality

variable {D : D7}

theorem mixT_smul {S T T₀ : HSp D} {ρ : ℕ} (d : HypDec T T₀ ρ) (ψ : AddChar (AF D.host.F) ℂ)
    (μ : Measure (Mx D ρ S.rank)) (𝓕 : Set (Mx D ρ S.rank)) (c : ℂ) (f : WO S T → ℂ) (y : Mx D S.rank ρ) :
    d.mixT S ψ μ 𝓕 (c • f) y = c • d.mixT S ψ μ 𝓕 f y := by
  funext w
  simp only [HypDec.mixT, heisO, Pi.smul_apply, smul_eq_mul]
  rw [← integral_const_mul]
  congr 1; funext ξ; ring

theorem symplO_eq_of_symplOH {S T : HSp D} {a b a' b' : WO S T} (h : symplOH S T a b = symplOH S T a' b') :
    symplO S T a b = symplO S T a' b' := by
  have h2 : algebraMap D.host.F (AF D.host.F) 2 * algebraMap D.host.F (AF D.host.F) (1 / 2) = 1 := by
    rw [← map_mul]; norm_num
  unfold symplOH at h
  calc symplO S T a b = algebraMap D.host.F (AF D.host.F) 2 * (algebraMap D.host.F (AF D.host.F) (1 / 2) * symplO S T a b) := by
        rw [← mul_assoc, h2, one_mul]
    _ = _ := by rw [h, ← mul_assoc, h2, one_mul]

section Gen

variable {ψ : AddChar (AF D.host.F) ℂ} {V V₀ W W₀ : HSp D} {ρ σ : ℕ} (dV : HypDec V V₀ ρ) (dW : HypDec W W₀ σ)
  (vS : VolM D W.rank ρ) (vT : VolM D σ V₀.rank) (νU : Measure (UX D ρ)) (x : Mx D W.rank ρ) (y : Mx D V₀.rank σ)

theorem flatAt_dual (hψ : IsStdChar D ψ (-1)) (f : WO V W → ℂ) (hf : IsThetaFunO ψ V W f) (a : Mx D W.rank ρ)
    (ha : GlobalTheory.FinPl.UInv W x a) :
    flatAt ψ dV dW vS.μ vS.𝓕 vT.μ vT.𝓕 νU x y (heisO ψ V W (dV.extY W a) f) =
      ψ (symplO V W (dV.extX W x) (dV.extY W a)) • flatAt ψ dV dW vS.μ vS.𝓕 vT.μ vT.𝓕 νU x y f := by
  have key : ∀ u : UX D ρ, dV.mixS W ψ vS.μ vS.𝓕 (heisO ψ V W (dV.extY W a) f) (x ⬝ u.1.1) =
      ψ (symplO V W (dV.extX W x) (dV.extY W a)) • dV.mixS W ψ vS.μ vS.𝓕 f (x ⬝ u.1.1) := by
    intro u
    rw [(GlobalTheory.T.heisenbergOperator_thetaFunctional_mixedSourceModel D ψ hψ V V₀ W ρ dV vS f hf).2.1 (x ⬝ u.1.1) a]
    rw [symplO_eq_of_symplOH (a := dV.extX W (x ⬝ u.1.1)) (b := dV.extY W a) (a' := dV.extX W x) (b' := dV.extY W a)
      (by rw [dV.symplOH_extX_extY W, dV.symplOH_extX_extY W, ha u])]
  funext w
  simp only [flatAt, flatFun, evalAt, key, mixT_smul, Pi.smul_apply, smul_eq_mul]
  rw [← integral_const_mul]
  congr 1; funext u; ring

theorem flatAt_iso (hψ : IsStdChar D ψ (-1)) (f : WO V W → ℂ) (hf : IsThetaFunO ψ V W f) (ξ : Mx D σ V₀.rank) :
    flatAt ψ dV dW vS.μ vS.𝓕 vT.μ vT.𝓕 νU x y (heisO ψ V W (dV.ext0 W (dW.incX V₀ ξ)) f) =
      ψ (symplO V₀ W (dW.incAdj V₀ y) (dW.incX V₀ ξ)) • flatAt ψ dV dW vS.μ vS.𝓕 vT.μ vT.𝓕 νU x y f := by
  have key : ∀ u : UX D ρ, dW.mixT V₀ ψ vT.μ vT.𝓕
      (dV.mixS W ψ vS.μ vS.𝓕 (heisO ψ V W (dV.ext0 W (dW.incX V₀ ξ)) f) (x ⬝ u.1.1)) y =
      ψ (symplO V₀ W (dW.incAdj V₀ y) (dW.incX V₀ ξ)) •
        dW.mixT V₀ ψ vT.μ vT.𝓕 (dV.mixS W ψ vS.μ vS.𝓕 f (x ⬝ u.1.1)) y := by
    intro u
    rw [(GlobalTheory.T.heisenbergOperator_thetaFunctional_mixedSourceModel D ψ hψ V V₀ W ρ dV vS f hf).2.2.1 (x ⬝ u.1.1) (dW.incX V₀ ξ)]
    have hg := (GlobalTheory.T.mixedCoordinates_of_thetaFunction_are_thetaFunctions D ψ hψ).1 V V₀ W ρ dV vS.μ vS.𝓕 vS.covol f hf (x ⬝ u.1.1)
    exact (GlobalTheory.T.heisenbergThetaMixedModelTarget_of_mixedModel D ψ hψ V₀ W W₀ σ dW vT.μ vT.𝓕 vT.covol _ hg).1 ξ y
  funext w
  simp only [flatAt, flatFun, evalAt, key, Pi.smul_apply, smul_eq_mul]
  rw [← integral_const_mul]
  congr 1; funext u; ring

theorem flatAt_core (hψ : IsStdChar D ψ (-1)) (f : WO V W → ℂ) (hf : IsThetaFunO ψ V W f) (w₀ : WO V₀ W₀) :
    flatAt ψ dV dW vS.μ vS.𝓕 vT.μ vT.𝓕 νU x y (heisO ψ V W (dV.ext0 W (dW.inc0 V₀ w₀)) f) =
      heisO ψ V₀ W₀ w₀ (flatAt ψ dV dW vS.μ vS.𝓕 vT.μ vT.𝓕 νU x y f) := by
  have key : ∀ u : UX D ρ, dW.mixT V₀ ψ vT.μ vT.𝓕
      (dV.mixS W ψ vS.μ vS.𝓕 (heisO ψ V W (dV.ext0 W (dW.inc0 V₀ w₀)) f) (x ⬝ u.1.1)) y =
      heisO ψ V₀ W₀ w₀ (dW.mixT V₀ ψ vT.μ vT.𝓕 (dV.mixS W ψ vS.μ vS.𝓕 f (x ⬝ u.1.1)) y) := by
    intro u
    rw [(GlobalTheory.T.heisenbergOperator_thetaFunctional_mixedSourceModel D ψ hψ V V₀ W ρ dV vS f hf).2.2.1 (x ⬝ u.1.1) (dW.inc0 V₀ w₀)]
    have hg := (GlobalTheory.T.mixedCoordinates_of_thetaFunction_are_thetaFunctions D ψ hψ).1 V V₀ W ρ dV vS.μ vS.𝓕 vS.covol f hf (x ⬝ u.1.1)
    exact (GlobalTheory.T.heisenbergThetaMixedModelTarget_of_mixedModel D ψ hψ V₀ W W₀ σ dW vT.μ vT.𝓕 vT.covol _ hg).2.1 w₀ y
  funext w
  simp only [flatAt, flatFun, evalAt, key, heisO]
  rw [← integral_const_mul]
  congr 1; funext u; ring

end Gen

end GlobalTheory.FlatLawsDuality

namespace GlobalTheory.FlatLawsDuality

theorem flatBF_equiv : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (ρ : ℕ) (B : BesLev D ρ) (J : JacLev D ρ) (s : StepBF ψ B J) (f : WO B.V J.W → ℂ), IsThetaFunO ψ B.V J.W f → ∀ n ∈ flagN J.d, ∀ h : GA D J.W₀, flatBF s (s.om (1, n * J.d.emb0 h) f) = star (psiFlag ψ J.d n) • opA ψ J.d B.o B.ζ s.om₀ n h (flatBF s f) := by
  intro D ψ ρ B J s f hf n hn h
  obtain ⟨om', hom'⟩ := (GlobalTheory.T.weilDatum_descends_to_wittCore D ψ B.V J.W s.χV s.χW s.om s.weil).1 B.V₀ ρ B.d
  have e := GlobalTheory.T.besselToJacobiFlatSchwartz_equivariant D ψ ρ B J s om' hom' f hf 1 n hn h
  have e1 : embA B.d B.o 1 = 1 := map_one _
  have e2 : B.o.emb (1, 1) = 1 := map_one _
  rw [e1, e2] at e
  rw [e, show s.om₀ (1, 1) = 1 from map_one _, Module.End.one_apply]

theorem flatFB_equiv : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (σ : ℕ) (J : JacLev D (σ + 1)) (B : BesLev D σ) (s : StepFB ψ J B) (f : WO J.W B.V → ℂ), IsThetaFunO ψ J.W B.V f → ∀ n ∈ flagN B.d, ∀ h : GA D B.A, flatFB s (s.om (1, n * embA B.d B.o h) f) = star (psiBes ψ B.d 1 (vecB B.o B.ζ) n) • s.om₀ (1, B.o.emb (h, 1)) (flatFB s f) := by
  intro D ψ σ J B s f hf n hn h
  have hD : Descent D := GlobalTheory.T.weilDatum_descends_to_wittCore D
  have h1 : IsThetaFunO ψ J.W B.V (s.om (1, embA B.d B.o h) f) := s.weil.om_pres _ _ hf
  have e : s.om (1, n * embA B.d B.o h) f = s.om (1, n) (s.om (1, embA B.d B.o h) f) := by
    rw [← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk, one_mul]
  have c := GlobalTheory.T.jacobiToBesselFlat_intertwines_weilAction D hD ψ σ J B s f hf 1 h
  rw [map_one] at c
  rw [e, GlobalTheory.T.flatSchwartz_targetUnipotent_conj_besselCharacter D hD ψ σ J B s _ h1 n hn, c]

theorem flatLaws_all (D : D7) : GlobalTheory.FinPl.FlatLaws D := by
  intro ψ P
  refine ⟨fun ρ B J s => ?_, fun σ J B s => ?_⟩
  · have hψ : IsStdChar D ψ (-1) := s.weil.std
    exact
      { Heisenberg₂ :=
          { theta := fun f hf => (GlobalTheory.T.flatThetaMaps_preserve_thetaFunctions D (GlobalTheory.T.flatThetaMaps_converge_thetaFunctions D) ψ).1 ρ B J s f hf
            dual := fun f hf a _ ha => flatAt_dual B.d J.d s.vS s.vT s.vU.ν _ _ hψ f hf a ha
            iso := fun f hf ξ _ => flatAt_iso B.d J.d s.vS s.vT s.vU.ν _ _ hψ f hf ξ
            core := fun f hf w _ => flatAt_core B.d J.d s.vS s.vT s.vU.ν _ _ hψ f hf w }
        equiv := fun f hf n hn _ h _ => flatBF_equiv D ψ ρ B J s f hf n hn h }
  · have hψ : IsStdChar D ψ (-1) := s.weil.std
    exact
      { Heisenberg₂ :=
          { theta := fun f hf => (GlobalTheory.T.flatThetaMaps_preserve_thetaFunctions D (GlobalTheory.T.flatThetaMaps_converge_thetaFunctions D) ψ).2 σ J B s f hf
            dual := fun f hf a _ ha => flatAt_dual J.d B.d s.vS s.vT s.vU.ν _ _ hψ f hf a ha
            iso := fun f hf ξ _ => flatAt_iso J.d B.d s.vS s.vT s.vU.ν _ _ hψ f hf ξ
            core := fun f hf w _ => flatAt_core J.d B.d s.vS s.vT s.vU.ν _ _ hψ f hf w }
        equiv := fun f hf n hn _ h _ => flatFB_equiv D ψ σ J B s f hf n hn h }

end GlobalTheory.FlatLawsDuality

theorem GlobalTheory.FinPl.flatLaws_all : ∀ D : D7, GlobalTheory.FinPl.FlatLaws D := GlobalTheory.FlatLawsDuality.flatLaws_all
