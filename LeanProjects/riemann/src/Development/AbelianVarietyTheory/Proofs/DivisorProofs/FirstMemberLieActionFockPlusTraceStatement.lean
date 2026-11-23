import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FirstMemberLieActionFockPlusTrace
import Development.AbelianVarietyTheory.Definitions.Divisors.FramedDConst
open scoped TensorProduct Matrix Classical GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open NumberField MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions.TH GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RealLift
open GlobalTheory.HoweD
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.firstMember_lieAction_fock_plus_trace : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (α β κ : Type) [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] [Fintype κ] (P Q R S : InfinitePlace F → ℕ) (ψ : AddChar (AF F) ℂ) (τ : ∀ w : InfinitePlace F, EmbOver E w) (JA : Matrix α α (AE F E)) (JB : Matrix β β (AE F E)) (d : Darboux (symp (R := AF F) (cA σ) (-1) JA JB) κ) (d' : Darboux (symp (R := AF F) (cA σ) (-1) JB JA) κ) (a b : ℂ) (A : ∀ w : InfinitePlace F, Matrix α (Ix (P w) (Q w)) ℂ) (C : ∀ w : InfinitePlace F, Matrix β (Ix (R w) (S w)) ℂ) (Φ : TensD F P Q R S →ₗ[ℂ] SInf F κ) (om : UG (cA σ) JA →* Module.End ℂ ((κ → AF F) → ℂ)), IsCMExt F E σ → IsStd ψ → FramedD τ JA JB a b A C → IsFockMapD ψ τ d A C Φ → (∀ x : Matrix α β (AE F E), d'.e xᵀ = d.e x) → IsUSplitting (adeleClass F) ψ d' (actB (cA σ)) om → ∃ c, ActsByD τ A om Φ (fun w => fockAct1 (P w) (Q w) (R w) (S w)) c := by
  first | exact @GlobalTheory.HoweD.LieFirstD.lieFirstD | exact GlobalTheory.HoweD.LieFirstD.lieFirstD | (intros; apply GlobalTheory.HoweD.LieFirstD.lieFirstD <;> assumption)
