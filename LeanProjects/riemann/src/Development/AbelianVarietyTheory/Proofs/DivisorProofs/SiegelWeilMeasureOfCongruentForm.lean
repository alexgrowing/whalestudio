import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPowMemConj
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PadicEmbeddingLiesOverOrComplexConjLiesOver
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.StabFin
open scoped TensorProduct Classical

namespace GlobalTheory.StabFinOver

theorem liesOver_comp_complexConj_of_not_liesOver : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p)
    (ψ : G.F →+* PadicAlgCl p), ¬ LiesOver G.Kq G.u ψ →
      LiesOver G.Kq G.u (ψ.comp (IsCMField.complexConj G.F : G.F →+* G.F)) := by
  intro p _ G ψ h x
  exact (GlobalTheory.HTGroupOver.liesOver_or_conj p G ψ).resolve_left h x

end GlobalTheory.StabFinOver

example : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (ψ : G.F →+* PadicAlgCl p), ¬ LiesOver G.Kq G.u ψ → LiesOver G.Kq G.u (ψ.comp (IsCMField.complexConj G.F : G.F →+* G.F)) :=
  GlobalTheory.StabFinOver.liesOver_comp_complexConj_of_not_liesOver
