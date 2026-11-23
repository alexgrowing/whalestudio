import Mathlib
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.IntegrableComplexContinuousBoundedSupport
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MatrixUnitDerivativeDiscreteSeriesMatrixCoeffStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CoverFactoringRepresentationUnitaryGroupDictionaStatement
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.DiscreteSeriesClassificationIff
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsOfIsDSPar
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.DiscreteSpectrumKFiniteDecomposition
open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible Formalism.L2.Theta Matrix GlobalTheory.RealPar GlobalTheory.CoverDS
open GlobalTheory.IndefiniteRowSideFullHecke.IsotypicSignedParameters (SignedPar IsDSPar)
open Formalism.MainNotions.S (IsURepOn IsIrredOn IsKFin IsKStableOn IsWtOn IsKTypeOf IsDS IsSqIntOn UJset)

namespace GlobalTheory.CoverDS

theorem gelf_one_eq_sum {n : ℕ} (ε : Fin n → Bool) (f : Matrix (Fin n) (Fin n) ℂ → ℂ)
    (g : Matrix (Fin n) (Fin n) ℂ) :
    GlobalTheory.Dec.gelf ε 1 f g = ∑ a, ∑ b, Formalism.REAL.Eab ε a b (Formalism.REAL.Eab ε b a f) g := by
  unfold GlobalTheory.Dec.gelf
  rw [← Finset.sum_product', Finset.univ_product_univ]
  refine Fintype.sum_equiv (finTwoArrowEquiv (Fin n)) _ _ (fun a => ?_)
  simp [GlobalTheory.Dec.cycWord, Formalism.REAL.Eword, List.ofFn_succ]

theorem casimir_eq_gelfVal_of_hasInfChar : ∀ (p q n : ℕ) (e : Ix p q ≃ Fin n) (ε : Fin n → Bool) (T : GrpData p q) (R : DSRep T) (σ : Matrix (Fin n) (Fin n) ℂ → (R.U.H →L[ℂ] R.U.H)), BlockOrd e ε → Factors R.U e σ → ∀ χ : Fin n → ℂ, GlobalTheory.Dec.HasInfChar ε χ σ → ∀ v, casimir R.HK.act v = GlobalTheory.Dec.gelfVal χ 2 • v := by
  intro p q n e ε T R σ hb hf χ hχ v
  obtain ⟨hU, -, hK, -⟩ := GlobalTheory.T.coverFactoringRepresentation_unitaryGroup_dictionary p q n e ε T R.U σ hb hf
  have hkf : ∀ u : R.HK.V, IsKFin ε σ (R.ι u) := fun u =>
    (hK _).1 ((R.ι_range _).1 ⟨u, rfl⟩)
  have h1 : (1 : Matrix (Fin n) (Fin n) ℂ) ∈ UJset ε := by
    simp [UJset, Formalism.REAL.inUJ]
  have hσ1 : σ 1 = 1 := hU.1.1
  have key : ∀ u : R.HK.V,
      inner ℂ (R.ι u) (R.ι (casimir R.HK.act v - GlobalTheory.Dec.gelfVal χ 2 • v)) = 0 := by
    intro u
    have h := (hχ (R.ι v) (R.ι u) (hkf v) (hkf u)).2 1 1 h1
    rw [gelf_one_eq_sum, ← e.sum_comp] at h
    have h2 : ∀ a b : Ix p q,
        Formalism.REAL.Eab ε (e a) (e b) (Formalism.REAL.Eab ε (e b) (e a)
          (fun g => inner ℂ (R.ι u) (σ g (R.ι v)))) 1 =
        inner ℂ (R.ι u) (R.ι (R.HK.act (Eab a b) (R.HK.act (Eab b a) v))) := by
      intro a b
      rw [Formalism.REAL.lie_derivative_congr (e a) (e b)
        (fun x hx => GlobalTheory.T.matrixUnitDerivative_discreteSeriesMatrixCoeff p q n e ε T R σ hb hf b a v (R.ι u) x hx) h1,
        GlobalTheory.T.matrixUnitDerivative_discreteSeriesMatrixCoeff p q n e ε T R σ hb hf a b _ (R.ι u) 1 h1, hσ1]
      rfl
    have h3 : ∀ a : Ix p q, (∑ b : Fin n, Formalism.REAL.Eab ε (e a) b (Formalism.REAL.Eab ε b (e a)
          (fun g => inner ℂ (R.ι u) (σ g (R.ι v)))) 1) =
        ∑ b : Ix p q, inner ℂ (R.ι u) (R.ι (R.HK.act (Eab a b) (R.HK.act (Eab b a) v))) := by
      intro a
      rw [← e.sum_comp]
      exact Finset.sum_congr rfl (fun b _ => h2 a b)
    simp only [h3, hσ1] at h
    rw [map_sub, map_smul, inner_sub_right, inner_smul_right, sub_eq_zero]
    refine Eq.trans ?_ h
    simp only [casimir, LinearMap.sum_apply, Module.End.mul_apply, map_sum, inner_sum]
  have h0 := key (casimir R.HK.act v - GlobalTheory.Dec.gelfVal χ 2 • v)
  rw [inner_self_eq_zero] at h0
  exact sub_eq_zero.1 (R.ι_inj (h0.trans (map_zero _).symm))

end GlobalTheory.CoverDS
