import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LagrangianDecomposition.SDarb
import Development.AbelianVarietyTheory.Definitions.Divisors.DblActId

noncomputable section

open scoped TensorProduct NNReal Matrix Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw

namespace PositivityTheory.SiegelWeilFormula.Ald

def BigT : Prop := TAll → AuxiliaryPrimeFunction → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (d : SD σ)
  (dd0 : Darboux (symp (R := AF F) (cA σ) (-1) (incM F d.A.J) (dbl (incM F d.Y.J))) (Fin d.m × Fin d.n × Fin 2)),
  IsAdapted d.bs d.A d.Y d.b dd0 →
  (∀ x : Matrix (Fin d.m) (Fin d.n ⊕ Fin d.n) E, ∃ y z : Fin d.m × Fin d.n × Fin 2 → F,
      dd0.e (incM F x) = (fun i => algebraMap F (AF F) (y i), fun i => algebraMap F (AF F) (z i))) →
  ∃ (S0 : ((d.κ → AF F) → ℂ) →ₗ[ℂ] ((Fin d.m × Fin d.n × Fin 2 → AF F) → ℂ))
    (S0' : ((Fin d.m × Fin d.n × Fin 2 → AF F) → ℂ) →ₗ[ℂ] ((d.κ → AF F) → ℂ)) (C : ℂ), C ≠ 0 ∧
    GlobalTheory.TowU.IsOp2 d.B.ψ (fun w => dd0.e (d.dd.e.symm w)) S0 S0' ∧ ∀ Φ ∈ d.sch, ∀ X, d.T Φ X = C * S0 Φ (crdB d.bs X)

def PartCharInv : Prop := ∀ (F : Type) [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ), IsStd ψ →
  ∀ (κ' κ'' : Type) [Fintype κ'] [Fintype κ''] (l : ((κ' ⊕ κ'' → AF F) → ℂ) →ₗ[ℂ] ℂ),
    l ∈ (adeleClass F).adm (κ' ⊕ κ'') →
    (∀ (y : κ'' → AF F), ∀ Ψ ∈ schA F (κ' ⊕ κ''), l (fun x => ψ ((x ∘ Sum.inr) ⬝ᵥ y) * Ψ x) = l Ψ) →
    ∀ Ψ ∈ schA F (κ' ⊕ κ''), (∀ x' : κ' → AF F, Ψ (Sum.elim x' 0) = 0) → l Ψ = 0

end PositivityTheory.SiegelWeilFormula.Ald

end
