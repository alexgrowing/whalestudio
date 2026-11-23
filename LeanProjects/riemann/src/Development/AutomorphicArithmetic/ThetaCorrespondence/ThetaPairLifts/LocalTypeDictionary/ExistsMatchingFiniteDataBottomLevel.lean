import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.DiscreteSpectrumResidualClassification
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BottomTriangleFiniteFactorExists
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.BernsteinUnitaryProductIrreducible
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.FockFImageEqZeroOrExistsEqSmul
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BottomTriangleFiniteFactorExistsStatement

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset MeasureTheory
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest GlobalTheory.SqTop GlobalTheory.SquareComm
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.BotFinRef
end GlobalTheory.BotFinRef
namespace GlobalTheory.BotFinRef
theorem exists_matching_finiteData_bottomLevel : GlobalTheory.Published.HoweDualityReal → _root_.GlobalTheory.FunPr.ThetaLocalInputs → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.LocalMatching → GBig fun {D} {T} {Lc} {sc} G _ _ _ _ => ∀ (W : G.Weil) (i j : Fin D.R.m) (A A' WW : HSp D) (X : Tri T A A' WW), IsBottomTri W i j X → ∀ (FA : GlobalTheory.ChainFr.Fr A) (FA' : GlobalTheory.ChainFr.Fr A') (FW : GlobalTheory.ChainFr.Fr WW) (t : T), IsFinF W.ψ W.θ true FA FW (X.f t) → IsFinF W.ψ W.θ false FA' FW (X.f' t) → ∃ (Pi : ModuleCat.{0} ℂ) (rf : GA D WW → Module.End ℂ Pi) (rl : D.what₂.Tau → Matrix (Fin WW.rank) (Fin WW.rank) ℂ → Module.End ℂ Pi) (p : (WO A WW → ℂ) →ₗ[ℂ] Pi) (p' : (WO A' WW → ℂ) →ₗ[ℂ] Pi), IsMatch W.ψ W.θ FA FA' FW (Lc.mu t (j + 1) * Lc.eta ^ (rankV D i j % 2)) (G.ch.chi (D.R.m - i) * Lc.eta ^ (rankV D i j % 2)) (X.ω t) (X.ω' t) Pi rf rl p p' ∧ ∀ (Pr Pf : ModuleCat.{0} ℂ) (q : PolF D WW.rank A.rank →ₗ[ℂ] Pr) (q' : PolF D WW.rank A'.rank →ₗ[ℂ] Pr) (r : (WO A WW → ℂ) →ₗ[ℂ] Pf) (r' : (WO A' WW → ℂ) →ₗ[ℂ] Pf) (e : Pr ⊗[ℂ] Pf ≃ₗ[ℂ] Pi), Function.Surjective q → Function.Surjective q' → (∀ f, IsFinF W.ψ W.θ true FA FW f → ∀ P, p (fockF W.ψ W.θ true FA FW f P) = e (q P ⊗ₜ r f)) → (∀ f, IsFinF W.ψ W.θ false FA' FW f → ∀ P, p' (fockF W.ψ W.θ false FA' FW f P) = e (q' P ⊗ₜ r' f)) → ∃ κ : ℂ, r (X.f t) = κ • r' (X.f' t) := by
  intro hH hP hK hL
  refine gBig_mono (_root_.GlobalTheory.T.fockF_image_eq_zero_or_exists_eq_smul hH hP hK hL) fun {D T Lc sc} G μ₀ C x b hA => ?_
  intro W i j A A' WW X hX FA FA' FW t hf hf'
  obtain ⟨Pi, rf, rl, p, p', hm, hc⟩ := hA W i j A A' WW X hX FA FA' FW t hf hf'
  refine ⟨Pi, rf, rl, p, p', hm, fun Pr Pf q q' r r' e hq hq' hp hp' => ?_⟩
  haveI : Nontrivial Pi := hm.irred.1
  exact exists_smul_of_factor q q' e hq (r (X.f t)) (r' (X.f' t)) (fun P => p (fockF W.ψ W.θ true FA FW (X.f t) P))
    (fun P' => p' (fockF W.ψ W.θ false FA' FW (X.f' t) P')) (hp _ hf) (hp' _ hf') hc
end GlobalTheory.BotFinRef
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset MeasureTheory
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest GlobalTheory.SqTop GlobalTheory.SquareComm
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.theta_bottomLevel_matches_finiteData : GlobalTheory.Published.HoweDualityReal → _root_.GlobalTheory.FunPr.ThetaLocalInputs → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.LocalMatching → GBig fun {D} {T} {Lc} {sc} G _ _ _ _ => ∀ (W : G.Weil) (i j : Fin D.R.m) (A A' WW : HSp D) (X : Tri T A A' WW), IsBottomTri W i j X → ∀ (FA : GlobalTheory.ChainFr.Fr A) (FA' : GlobalTheory.ChainFr.Fr A') (FW : GlobalTheory.ChainFr.Fr WW) (t : T), IsFinF W.ψ W.θ true FA FW (X.f t) → IsFinF W.ψ W.θ false FA' FW (X.f' t) → ∃ (Pi : ModuleCat.{0} ℂ) (rf : GA D WW → Module.End ℂ Pi) (rl : D.what₂.Tau → Matrix (Fin WW.rank) (Fin WW.rank) ℂ → Module.End ℂ Pi) (p : (WO A WW → ℂ) →ₗ[ℂ] Pi) (p' : (WO A' WW → ℂ) →ₗ[ℂ] Pi), IsMatch W.ψ W.θ FA FA' FW (Lc.mu t (j + 1) * Lc.eta ^ (rankV D i j % 2)) (G.ch.chi (D.R.m - i) * Lc.eta ^ (rankV D i j % 2)) (X.ω t) (X.ω' t) Pi rf rl p p' ∧ ∀ (Pr Pf : ModuleCat.{0} ℂ) (q : PolF D WW.rank A.rank →ₗ[ℂ] Pr) (q' : PolF D WW.rank A'.rank →ₗ[ℂ] Pr) (r : (WO A WW → ℂ) →ₗ[ℂ] Pf) (r' : (WO A' WW → ℂ) →ₗ[ℂ] Pf) (e : Pr ⊗[ℂ] Pf ≃ₗ[ℂ] Pi), Function.Surjective q → Function.Surjective q' → (∀ f, IsFinF W.ψ W.θ true FA FW f → ∀ P, p (fockF W.ψ W.θ true FA FW f P) = e (q P ⊗ₜ r f)) → (∀ f, IsFinF W.ψ W.θ false FA' FW f → ∀ P, p' (fockF W.ψ W.θ false FA' FW f P) = e (q' P ⊗ₜ r' f)) → ∃ κ : ℂ, r (X.f t) = κ • r' (X.f' t) := by
  first | exact @_root_.GlobalTheory.BotFinRef.exists_matching_finiteData_bottomLevel | exact _root_.GlobalTheory.BotFinRef.exists_matching_finiteData_bottomLevel | (intros; apply _root_.GlobalTheory.BotFinRef.exists_matching_finiteData_bottomLevel <;> assumption)
end
