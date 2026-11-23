import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.EigenvalueSeparation.StableEigenspaces.InterpolationL2Bound
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LieCentralElementTrace
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TraceOperatorEigenvalueSum
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CentralEigenExponential

noncomputable section

open NumberField GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.UnitaryBC PositivityTheory.S2.Clozel

namespace PositivityTheory.Rg.BcB.E.E3

namespace centeig

open Polynomial Formalism.REAL GroundTheory.BlockD.FourierDecayAlt.GaugeExists

theorem trace_eq {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ} (V : Submodule ℂ (Sm E a))
    (τ : E →+* ℂ) (m : Multiset ℂ) (hm : HasInfCharGL V τ m) :
    ∀ φ ∈ V, (∑ i : Fin a, Eop τ i i) φ = m.sum • φ := by
  intro φ hφ
  obtain ⟨hc, hu⟩ := hm
  rcases a with _ | n
  · obtain rfl : m = 0 := Multiset.card_eq_zero.1 hc
    simp
  · obtain ⟨l, rfl⟩ := Quot.exists_rep m
    refine GlobalTheory.CompanionTheory.CapelliTrace.trace_of_qdet (Eop τ) l (by simpa using hc) φ fun v => ?_
    have := hu (v - (n : ℂ) / 2) φ hφ
    rw [cap, show v - (n : ℂ) / 2 + (((n + 1 : ℕ) : ℂ) - 1) / 2 = v by push_cast; ring] at this
    simpa using this

end centeig

theorem centeig_holds : CentEig := by
  intro E _ _ _ N V m hm
  refine ⟨∑ τ : E →+* ℂ, (m τ).sum, fun φ hφ t g => ?_⟩
  refine GlobalTheory.CompanionTheory.Clozel.eigen_along_splitCentre E N φ _ ?_ t g
  rw [GlobalTheory.CompanionTheory.ClozelLie.lie_oneL_eq_sum_Eop, LinearMap.sum_apply, Finset.sum_smul]
  exact Finset.sum_congr rfl fun τ _ => centeig.trace_eq V τ (m τ) (hm τ) φ hφ

end PositivityTheory.Rg.BcB.E.E3

end
