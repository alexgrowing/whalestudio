import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LagrangianDecomposition.ChartFacts
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.SplitStab
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.IsLatRepL
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilDatumProperties
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilAldDefs

set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped TensorProduct NNReal Matrix Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
namespace PositivityTheory.SiegelWeilFormula.Ald
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
def ChartFacts_k : Prop := ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (n : ℕ) (h : n + 1 = d.n) (Y : Spc F E n) (b : GL (Fin n ⊕ Fin n) E)
  (j : G2 σ Y →* d.G) (ε : ℤˣ), 1 ≤ n → _root_.PositivityTheory.SiegelWeilFormula.Ald.SignOK_k d Y → IsFrame2 σ Y b →
  d.b.1ᵀ * dbl d.Y.J * d.b.1.map σ = jeps d.n ε → b.1ᵀ * dbl Y.J * b.1.map σ = jeps n ε → _root_.PositivityTheory.SiegelWeilFormula.Ald.IsJ_k d h b j →
  ∀ (dd0 : Darboux (symp (R := AF F) (cA σ) (-1) (incM F d.A.J) (dbl (incM F d.Y.J))) (Fin d.m × Fin d.n × Fin 2))
    (dd' : Darboux (symp (R := AF F) (cA σ) (-1) (incM F d.A.J) (dbl (incM F Y.J))) (Fin d.m × Fin n × Fin 2)),
    IsAdapted d.bs d.A d.Y d.b dd0 → IsAdapted d.bs d.A Y b dd' →
    (∀ w', (GlobalTheory.TowU.reindexD dd0 (eK d.m h).symm).e (emb h b d.b w') =
      (Sum.elim (dd'.e w').1 (0 : Fin d.m × Fin 2 → AF F), Sum.elim (dd'.e w').2 (0 : Fin d.m × Fin 2 → AF F))) ∧
    (∀ u v : Fin d.m × Fin 2 → AF F, ∃ w, (GlobalTheory.TowU.reindexD dd0 (eK d.m h).symm).e w =
      (Sum.elim (0 : Fin d.m × Fin n × Fin 2 → AF F) u, Sum.elim (0 : Fin d.m × Fin n × Fin 2 → AF F) v)) ∧
    (∀ g w, ((GlobalTheory.TowU.reindexD dd0 (eK d.m h).symm).e w).1 ∘ Sum.inl = 0 →
      ((GlobalTheory.TowU.reindexD dd0 (eK d.m h).symm).e w).2 ∘ Sum.inl = 0 → actB (cA σ) (j g) w = w) ∧
    (∀ g (w' : Matrix (Fin d.m) (Fin n ⊕ Fin n) (AE F E)), actB (cA σ) (j g) (emb h b d.b w') = emb h b d.b (actB (cA σ) g w')) ∧
    ∀ (u : UA σ d.A.J) (w' : Matrix (Fin d.m) (Fin n ⊕ Fin n) (AE F E)), mat u * emb h b d.b w' = emb h b d.b (mat u * w')
end PositivityTheory.SiegelWeilFormula.Ald
end
end
