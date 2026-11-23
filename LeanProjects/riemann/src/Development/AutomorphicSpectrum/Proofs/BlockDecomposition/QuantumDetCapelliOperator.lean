import Mathlib
import Formalism.RealPlaceAnalysis.ThirdArithmeticHolds
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SubsingletonRankZero
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.T2SpaceAdelicGeneralLinearGroupNumberField
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.IsNormalisedOfIsDiscrete
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.CuspDiscreteDecompositionGL
import Development.AutomorphicSpectrum.PublishedTheorems.PublishedGlobalResults.HasInfCharOfIsRegAlg
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.ClozelCohomologicalModel
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DiscreteSpectrumGLTwoOfCuspidalSpectrum
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ClozelPurity.EopV
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LieOperatorVectorEqStatement

open NumberField GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL MeasureTheory PositivityTheory.S2.Clozel

namespace GlobalTheory.CompanionTheory.Clozel

theorem qdet_restrict {V : Type} [AddCommGroup V] [Module ℂ V] (S : Submodule ℂ V) {n : ℕ}
    (X : Fin n → Fin n → Module.End ℂ S) (Y : Fin n → Fin n → Module.End ℂ V)
    (h : ∀ i j (x : S), (X i j x : V) = Y i j x) (w : ℂ) (x : S) :
    (Formalism.REAL.qdet X w x : V) = Formalism.REAL.qdet Y w x := by
  let P : Subalgebra ℂ (Module.End ℂ S × Module.End ℂ V) :=
    { carrier := {z | ∀ x : S, (z.1 x : V) = z.2 x}
      mul_mem' := fun {p q} hp hq x => by
        show ((p.1 (q.1 x) : S) : V) = p.2 (q.2 x)
        rw [hp, hq]
      add_mem' := fun {p q} hp hq x => by
        show ((p.1 x + q.1 x : S) : V) = p.2 x + q.2 x
        rw [Submodule.coe_add, hp, hq]
      algebraMap_mem' := fun c x => rfl }
  let Z : Fin n → Fin n → Module.End ℂ S × Module.End ℂ V := fun i j => (X i j, Y i j)
  have hZ : Formalism.REAL.qdet Z w ∈ P := by
    refine P.sum_mem fun σ _ => P.mul_mem (intCast_mem P _) (P.list_prod_mem fun y hy => ?_)
    obtain ⟨k, rfl⟩ := List.mem_ofFn.1 hy
    refine P.add_mem ?_ (fun x => h _ _ x)
    split_ifs
    · exact P.algebraMap_mem _
    · exact P.zero_mem
  have h1 : (Formalism.REAL.qdet Z w).1 = Formalism.REAL.qdet X w :=
    map_qdet (AlgHom.fst ℂ (Module.End ℂ S) (Module.End ℂ V)) Z w
  have h2 : (Formalism.REAL.qdet Z w).2 = Formalism.REAL.qdet Y w :=
    map_qdet (AlgHom.snd ℂ (Module.End ℂ S) (Module.End ℂ V)) Z w
  rw [← h1, ← h2]
  exact hZ x

theorem qdet_EopV_val : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (π : CuspSub E a)
    (τ : E →+* ℂ) (u : ℂ) (φ : π.V),
    (Formalism.REAL.qdet (EopV π τ) (u + ((a : ℂ) - 1) / 2) φ).1 = cap τ u φ.1 := by
  intro E _ _ _ a π τ u φ
  exact qdet_restrict π.V (EopV π τ) (Eop τ) (fun i j x => GlobalTheory.T.lie_operator_vector_eq E a π τ i j x) _ φ

end GlobalTheory.CompanionTheory.Clozel
