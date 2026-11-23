import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ExistsIsFundU
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ThetaAbsoluteSum
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.TransvectionAction
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.WeilDatumExistence
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MixedModelFormulasWittSourceProofStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MixedModelFormulasWittTargetStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MixedCoordinatesOfThetaFunctionAreThetaFunctionsStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FlagUnipotentFourierJacobiGroupStructure

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf GlobalTheory.Unf.FB

noncomputable section

namespace GlobalTheory.Unf.FB

variable {D : D7}

theorem det_of_mem_UX {ρ : ℕ} {u : GL (Fin ρ) (AE D)} (hu : u ∈ UX D ρ) :
    Matrix.GeneralLinearGroup.det u = 1 := by
  have hb : Matrix.BlockTriangular u.1 id := fun i j h => (hu i j).1 h
  apply Units.ext
  rw [Matrix.GeneralLinearGroup.val_det_apply, Units.val_one]
  rw [Matrix.det_of_upperTriangular hb]
  exact Finset.prod_eq_one fun i _ => (hu i i).2

theorem halfMod_of_mem_UX {ρ : ℕ} (m : ℕ) {u : GL (Fin ρ) (AE D)} (hu : u ∈ UX D ρ) :
    GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule.halfMod m u = 1 := by
  rw [GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule.halfMod, det_of_mem_UX hu, map_one]
  simp

theorem mixT_zero_flagN {S T T₀ : HSp D} {σ : ℕ} (d : HypDec T T₀ σ) (ψ : AddChar (AF D.host.F) ℂ)
    (χS : (AE D)ˣ →* Circle) (om : Om S T) (om₀ : Om S T₀) (μ : Measure (Mx D σ S.rank)) (𝓕 : Set (Mx D σ S.rank))
    (hpres : ∀ p f, IsThetaFunO ψ S T f → IsThetaFunO ψ S T (om p f))
    (hF : ∀ f, IsThetaFunO ψ S T f → GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule.FormulasT d ψ χS om om₀ μ 𝓕 f)
    (f : WO S T → ℂ) (hf : IsThetaFunO ψ S T f) (n : GA D T) (hn : n ∈ flagN d) :
    d.mixT S ψ μ 𝓕 (om (1, n) f) 0 = d.mixT S ψ μ 𝓕 f 0 := by
  obtain ⟨u, hu, b, c, rfl⟩ := ((flag_jacobi_structure D T T₀ σ d).1 n).1 hn
  have e : ((1 : GA D S), d.levi u * (d.nB b * d.nC c)) = (1, d.levi u) * ((1, d.nB b) * (1, d.nC c)) := by
    simp
  have h3 := hpres (1, d.nC c) f hf
  have h2 := hpres (1, d.nB b) _ h3
  have hq : d.qT S c 0 = 0 := by
    simp [HypDec.qT, map_zero, symplOH_zero_left]
  have ha : GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule.ofAdj S T₀ 0 = 0 := by
    simp [GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule.ofAdj]
  rw [e, map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply, (hF _ h2).levi, Matrix.zero_mul,
    det_of_mem_UX hu, map_one, halfMod_of_mem_UX _ hu, (hF _ h3).unip, Matrix.zero_mul, ha, (hF _ hf).centre, hq]
  funext w
  rw [AddChar.map_zero_eq_one, one_smul]
  simp only [Circle.coe_one, Complex.ofReal_one, mul_one, one_smul]
  change ψ (symplOH S T₀ w 0) * _ = _
  rw [add_zero]
  rw [show symplOH S T₀ w 0 = 0 by
    first
    | exact symplOH_zero_right S T₀ w
    | exact GlobalTheory.MixModel.symplOH_zero_right S T₀ w
    | simp [symplOH, symplO, hO]]
  rw [AddChar.map_zero_eq_one, one_mul]

theorem evalAt_zero_equivariant : ∀ (D : D7), Descent D → ∀ (ψ : AddChar (AF D.host.F) ℂ) (σ : ℕ) (J : JacLev D (σ + 1))
    (B : BesLev D σ) (s : StepFB ψ J B), ∀ (Ψ : WO J.W B.V → ℂ), IsThetaFunO ψ J.W B.V Ψ → ∀ (g : GA D J.W₀),
    ∀ n ∈ flagN B.d, ∀ (h : GA D B.A) (x : Mx D B.V.rank (σ + 1)),
      evalAt ψ J.d B.d s.vS.μ s.vS.𝓕 s.vT.μ s.vT.𝓕 (s.om (J.d.emb0 g, n * embA B.d B.o h) Ψ) x 0 =
        s.om₀ (g, B.o.emb (h, 1)) (evalAt ψ J.d B.d s.vS.μ s.vS.𝓕 s.vT.μ s.vT.𝓕 Ψ (mt B.V (n * embA B.d B.o h)⁻¹ ⬝ x) 0) := by
  intro D hD ψ σ J B s Ψ hΨ g n hn h x
  obtain ⟨om₁, hom₁⟩ := (hD ψ J.W B.V s.χV s.χW s.om s.weil).1 J.W₀ (σ + 1) J.d
  have hS := GlobalTheory.T.mixedModelFormulasWittSource_proof D ψ J.W J.W₀ B.V (σ + 1) J.d s.χV s.χW s.om om₁ s.weil hom₁ s.vS.μ s.vS.𝓕 s.vS.covol
  have hT := GlobalTheory.T.mixedModelFormulas_wittTarget D ψ J.W₀ B.V B.V₀ σ B.d s.χV s.χW om₁ s.om₀ hom₁ s.weil₀ s.vT.μ s.vT.𝓕 s.vT.covol
  have hV := (GlobalTheory.T.mixedCoordinates_of_thetaFunction_are_thetaFunctions D ψ s.weil.std).1 J.W J.W₀ B.V (σ + 1) J.d s.vS.μ s.vS.𝓕 s.vS.covol Ψ hΨ
  have hΨk := s.weil.om_pres (1, n * embA B.d B.o h) Ψ hΨ
  simp only [evalAt]
  rw [show s.om (J.d.emb0 g, n * embA B.d B.o h) = s.om (J.d.emb0 g, 1) * s.om (1, n * embA B.d B.o h) by
    rw [← map_mul]; simp]
  rw [Module.End.mul_apply, (hS _ hΨk).core, (hS _ hΨ).target]
  have hFt := hV (mt B.V (n * embA B.d B.o h)⁻¹ ⬝ x)
  generalize J.d.mixS B.V ψ s.vS.μ s.vS.𝓕 Ψ (mt B.V (n * embA B.d B.o h)⁻¹ ⬝ x) = F at hFt ⊢
  have hF1 := hom₁.om_pres (1, B.d.emb0 (B.o.emb (h, 1))) F hFt
  have hF2 := hom₁.om_pres (1, n) _ hF1
  rw [show om₁ (1, n * embA B.d B.o h) = om₁ (1, n) * om₁ (1, B.d.emb0 (B.o.emb (h, 1))) by
    rw [← map_mul, embA_apply]; simp]
  rw [Module.End.mul_apply, (hT _ hF2).source, Matrix.mul_zero,
    mixT_zero_flagN B.d ψ s.χV om₁ s.om₀ s.vT.μ s.vT.𝓕 hom₁.om_pres hT _ hF1 n hn, (hT _ hFt).core,
    show s.om₀ (g, B.o.emb (h, 1)) = s.om₀ (g, 1) * s.om₀ (1, B.o.emb (h, 1)) by rw [← map_mul]; simp,
    Module.End.mul_apply]

end GlobalTheory.Unf.FB

end
