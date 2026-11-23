import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsAuxiliaryHeckeCharacter
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ToricCharacterIsCMHostValueDatumStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsHeckeLEqToricSumNeZeroStatement

open NumberField IsDedekindDomain ReciprocityTheory.Gal Formalism.ConjugateSelfDual Formalism.BasicNotions Formalism.MainNotions Formalism.FrobeniusOrbits Formalism.L2.Host GlobalTheory.CMVal GlobalTheory.ToricDenom GlobalTheory.LamTie

namespace GlobalTheory.LamTie

theorem sum_th_empty_ne_zero : ∀ (D : D7) (N : NData D.R D.host D.what₂) (X : NTw D.R D.host D.what₂ D.LL0 N) (Z : LamDat D), Z.Ok → IsLamTie0 X Z → ∀ i, X.NonzeroIndexPlace i → ∀ lam : X.abelian₂ i, (∑ δ, X.th i ∅ lam δ) ≠ 0 ∧ ∃ s : ℤ, BlochKatoReduction.Gen.SOk X i lam s := by
  intro D N X Z hZ hT i hi lam
  obtain ⟨ι, j, a, s, hs, u, T, hu, hTs, hEq⟩ := hT i hi lam
  refine ⟨?_, s, hs⟩
  have h1 : 1 ≤ s := by
    have := hs.2.1
    exact_mod_cast this
  have h2 : (s : ℤ) ≤ (BlochKatoReduction.Gen.NFun D.R : ℤ) + 1 := hs.2.2
  obtain ⟨Λ, -, hne, hiff⟩ := GlobalTheory.T.exists_heckeL_eq_toricSum_ne_zero D.R D.host _ (phi D.host) s (Z.kap j a s) (cond0 D.host Z.w0)
    (Z.lam0 (X.l i) j a) (GlobalTheory.T.isHostDatum_kap_lam0_of_ok D Z hZ (X.l i) j a s h1 h2)
  have hT0 : T ≠ 0 := by rw [(hiff T).1 hTs]; exact hne
  intro h0
  rw [h0, map_zero] at hEq
  exact mul_ne_zero hu ((map_ne_zero ι).2 hT0) hEq.symm

end GlobalTheory.LamTie
