import Mathlib
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Development.AbelianVarietyTheory.Definitions.Foundations.HTBasis
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExpStar
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PowMulMemLatIff

noncomputable section

namespace GlobalTheory.ExpImage

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc

theorem act_root_eq_pow_of_chi_nat {l : ℕ} [Fact l.Prime] (P : LocPrime l) (g : GQ l) (u : ℕ)
    (hg : (P.χQ g : ℚ_[l]) = (u : ℚ_[l])) (m : ℕ) (ζ : Om l) (hζ : ζ ^ (l ^ m) = 1) :
    g ζ = ζ ^ u := by
  obtain ⟨a, ha, hga⟩ := P.χQ_cyc g m ζ hζ
  rw [hg] at ha
  have h2 : ‖((((u : ℤ) - (a : ℤ) : ℤ)) : ℚ_[l])‖ ≤ (l : ℝ) ^ (-(m : ℤ)) := by
    push_cast; exact ha
  have h3 : ((l : ℤ) ^ m) ∣ ((u : ℤ) - (a : ℤ)) := (Padic.norm_int_le_pow_iff_dvd _ _).mp h2
  have h4 : a ≡ u [MOD l ^ m] := by
    rw [Nat.modEq_iff_dvd]
    push_cast
    exact h3
  rw [hga, pow_eq_pow_mod a hζ, pow_eq_pow_mod u hζ, h4]

theorem actT_εroot_eq_pow : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (g : GQ l)
    (u : ℕ), (P.χQ g : ℚ_[l]) = (u : ℚ_[l]) →
      ∀ j : ℕ, AI.actT g (AI.εroot j) = AI.εroot j ^ u := by
  intro l _ P AI g u hg j
  have hz : ∀ m, P.ζQ m ^ l ^ m = 1 := by
    intro m
    induction m with
    | zero => simpa using P.ζQ_zero
    | succ m ih => rw [pow_succ', pow_mul, P.ζQ_succ, ih]
  refine Perfection.ext fun n => ?_
  have hc : PreTilt.coeff n (AI.εroot j) =
      Ideal.Quotient.mk (Ideal.span {((l : ℕ) : OC l)}) (AI.ζ (n + j)) := by
    rw [← AI.ε_coeff, LocAinf.εroot, PreTilt.coeff_iterate_frobeniusEquiv_symm]
  obtain ⟨y', h1, h2⟩ := AI.actT_coeff g _ n _ hc
  have h3 : y' = AI.ζ (n + j) ^ u := by
    apply Subtype.ext
    rw [h1, SubmonoidClass.coe_pow, AI.ζ_eq, AI.actC_ext,
      act_root_eq_pow_of_chi_nat P g u hg (n + j) _ (hz _)]
    exact map_pow (algebraMap (Om l) (PadicComplex l)) _ _
  change PreTilt.coeff n _ = PreTilt.coeff n _
  rw [h2, map_pow, hc, h3]
  exact map_pow _ _ _

end GlobalTheory.ExpImage
