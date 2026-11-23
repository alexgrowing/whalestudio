import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.DiscreteSpectrumResidualClassification
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SquareTowerStageFiniteCompat
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.BernsteinUnitaryProductIrreducible
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.ExistsFinitePlaceThetaMatch
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.StageUniqueOfArchimedeanTriple
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SquareTowerStageFiniteCompatStatement

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset
open Formalism.DivisionValues (vw)
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.CMVal (IsHeckeL)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.SqTop
open GlobalTheory.ConstRatio (NegIdx Factor)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open MeasureTheory
open scoped TensorProduct
namespace GlobalTheory.StageFinNonzero
theorem theta_stage_finite_part_ne_zero : _root_.GlobalTheory.FunPr.ThetaLocalInputs → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.LocalMatching →
    GBig fun {D} {T} {Lc} {sc} G _ _ _ _ => ∀ (W : G.Weil) (i j : Fin D.R.m) (p q : ℕ) (A A' WW : HSp D)
    (X : Tri T A A' WW), GlobalTheory.SqTower.IsStageC W i j p q X →
    ∀ (FA : GlobalTheory.ChainFr.Fr A) (FA' : GlobalTheory.ChainFr.Fr A') (FW : GlobalTheory.ChainFr.Fr WW) (t : T),
    GlobalTheory.SquareComm.IsFinF W.ψ W.θ true FA FW (X.f t) → GlobalTheory.SquareComm.IsFinF W.ψ W.θ false FA' FW (X.f' t) →
    ∀ (Pi : ModuleCat.{0} ℂ) rf rl p p', GlobalTheory.SquareComm.IsMatch W.ψ W.θ FA FA' FW (Lc.mu t (j + 1) * Lc.eta ^ (rankV D i j % 2))
      (G.ch.chi (D.R.m - i) * Lc.eta ^ (rankV D i j % 2)) (X.ω t) (X.ω' t) Pi rf rl p p' →
    ∀ (Pr Pf : ModuleCat.{0} ℂ) (q : PolF D WW.rank A.rank →ₗ[ℂ] Pr) (q' : PolF D WW.rank A'.rank →ₗ[ℂ] Pr)
      (r : (WO A WW → ℂ) →ₗ[ℂ] Pf) (r' : (WO A' WW → ℂ) →ₗ[ℂ] Pf) (e : Pr ⊗[ℂ] Pf ≃ₗ[ℂ] Pi),
      Function.Surjective q → Function.Surjective q' →
      (∀ f, GlobalTheory.SquareComm.IsFinF W.ψ W.θ true FA FW f → ∀ P, p (GlobalTheory.SquareComm.fockF W.ψ W.θ true FA FW f P) = e (q P ⊗ₜ r f)) →
      (∀ f, GlobalTheory.SquareComm.IsFinF W.ψ W.θ false FA' FW f → ∀ P, p' (GlobalTheory.SquareComm.fockF W.ψ W.θ false FA' FW f P) = e (q' P ⊗ₜ r' f)) →
      r' (X.f' t) ≠ 0 := by
  intro hP hK hL
  refine gBig_of_two (_root_.GlobalTheory.T.finite_place_theta_matching hP hK hL) (_root_.GlobalTheory.T.theta_stage_unique hP hK hL) fun {D T Lc sc} G μ₀ C x b₀ hA hB => ?_
  intro W i j a b A A' WW X hX FA FA' FW t hf hf' Pi rf rl p p' hm Pr Pf q q' r r' e hq hq' hp hp'
  obtain ⟨Pi₀, rf₀, rl₀, p₀, p₀', hm₀, P, P', κ, hne, heq⟩ := hA W i j a b A A' WW X hX FA FA' FW t hf hf'
  obtain ⟨E, c, hc, hE, hE'⟩ := hB W i j a b A A' WW X hX FA FA' FW t Pi₀ rf₀ rl₀ p₀ p₀' Pi rf rl p p' hm₀ hm
  have m2 : GlobalTheory.SquareComm.fockF W.ψ W.θ false FA' FW (X.f' t) P' ∈ GlobalTheory.SquareComm.algF W.ψ W.θ false FA' FW :=
    Submodule.subset_span ⟨_, P', hf', rfl⟩
  have n0 : p₀' (GlobalTheory.SquareComm.fockF W.ψ W.θ false FA' FW (X.f' t) P') ≠ 0 := by
    intro h0
    rw [h0, smul_zero] at heq
    exact hne heq
  have n1 : p' (GlobalTheory.SquareComm.fockF W.ψ W.θ false FA' FW (X.f' t) P') ≠ 0 := by
    rw [hE' _ m2]
    exact (LinearEquiv.map_ne_zero_iff E).mpr n0
  intro h0
  rw [hp' _ hf' P', h0, TensorProduct.tmul_zero, map_zero] at n1
  exact n1 rfl
end GlobalTheory.StageFinNonzero
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset
open Formalism.DivisionValues (vw)
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.CMVal (IsHeckeL)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.SqTop
open GlobalTheory.ConstRatio (NegIdx Factor)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open MeasureTheory
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.theta_stage_nonzero_at_finite_places : _root_.GlobalTheory.FunPr.ThetaLocalInputs → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.LocalMatching →
    GBig fun {D} {T} {Lc} {sc} G _ _ _ _ => ∀ (W : G.Weil) (i j : Fin D.R.m) (p q : ℕ) (A A' WW : HSp D)
    (X : Tri T A A' WW), GlobalTheory.SqTower.IsStageC W i j p q X →
    ∀ (FA : GlobalTheory.ChainFr.Fr A) (FA' : GlobalTheory.ChainFr.Fr A') (FW : GlobalTheory.ChainFr.Fr WW) (t : T),
    GlobalTheory.SquareComm.IsFinF W.ψ W.θ true FA FW (X.f t) → GlobalTheory.SquareComm.IsFinF W.ψ W.θ false FA' FW (X.f' t) →
    ∀ (Pi : ModuleCat.{0} ℂ) rf rl p p', GlobalTheory.SquareComm.IsMatch W.ψ W.θ FA FA' FW (Lc.mu t (j + 1) * Lc.eta ^ (rankV D i j % 2))
      (G.ch.chi (D.R.m - i) * Lc.eta ^ (rankV D i j % 2)) (X.ω t) (X.ω' t) Pi rf rl p p' →
    ∀ (Pr Pf : ModuleCat.{0} ℂ) (q : PolF D WW.rank A.rank →ₗ[ℂ] Pr) (q' : PolF D WW.rank A'.rank →ₗ[ℂ] Pr)
      (r : (WO A WW → ℂ) →ₗ[ℂ] Pf) (r' : (WO A' WW → ℂ) →ₗ[ℂ] Pf) (e : Pr ⊗[ℂ] Pf ≃ₗ[ℂ] Pi),
      Function.Surjective q → Function.Surjective q' →
      (∀ f, GlobalTheory.SquareComm.IsFinF W.ψ W.θ true FA FW f → ∀ P, p (GlobalTheory.SquareComm.fockF W.ψ W.θ true FA FW f P) = e (q P ⊗ₜ r f)) →
      (∀ f, GlobalTheory.SquareComm.IsFinF W.ψ W.θ false FA' FW f → ∀ P, p' (GlobalTheory.SquareComm.fockF W.ψ W.θ false FA' FW f P) = e (q' P ⊗ₜ r' f)) →
      r' (X.f' t) ≠ 0 := by
  first | exact @_root_.GlobalTheory.StageFinNonzero.theta_stage_finite_part_ne_zero | exact _root_.GlobalTheory.StageFinNonzero.theta_stage_finite_part_ne_zero | (intros; apply _root_.GlobalTheory.StageFinNonzero.theta_stage_finite_part_ne_zero <;> assumption)
end
