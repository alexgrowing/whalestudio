import Mathlib
import Formalism.PairingDivisors.StatementA
import Development.AbelianVarietyTheory.Definitions.Divisors.IsFinSetSplitPlacesCoprimeConductor
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ValIotaLeOfMem
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SplitsInCMFieldTwoPrimesDegreeOneStatement

noncomputable section

open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.CMVal.Euler

namespace GlobalTheory.CMVal.Euler

theorem exists_split_unif_idele : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (v : HeightOneSpectrum (OF E)) (x : OF E),
    Splits v → (∀ P, Over P v → Valued.v (iota x P) = WithZero.exp (-1 : ℤ)) →
    ∃ π : (Af E)ˣ, (∀ P, Over P v → (π : Af E) P = iota x P) ∧ (∀ P, ¬ Over P v → (π : Af E) P = 1) ∧
      modF π = ((Ideal.absNorm v.asIdeal : ℕ) : ℝ)⁻¹ ^ 2 ∧ ∀ χ : HChar E, TrivOnF χ → finPart χ π = 1 := by
  classical
  intro E _ _ _ v x hv hx
  obtain ⟨h2, hN⟩ := GlobalTheory.T.splitsInCMField_two_primes_degree_one E v hv
  obtain ⟨P₁, P₂, hne, hP₁, hP₂⟩ := hv
  have hx0 : (x : maximalRealSubfield E) ≠ 0 := fun h => by
    have h0 : x = 0 := Subtype.ext h
    have h1 := hx P₁ hP₁
    rw [h0, iota_zero, zero_coord, map_zero] at h1
    exact WithZero.exp_ne_zero h1.symm
  let k : (maximalRealSubfield E)ˣ := Units.mk0 (x : maximalRealSubfield E) hx0
  let y : (Af E)ˣ := Units.map (algebraMap E (Af E)).toMonoidHom (Formalism.L2.Host.upF (maximalRealSubfield E) k)
  have hy : (y : Af E) = iota x := rfl
  set S := Formalism.L2.Host.aboveF (L := E) (maximalRealSubfield E) v with hS
  have hmem : ∀ P, P ∈ S ↔ Over P v := fun P => mem_aboveF P v
  have hin : ∀ P, Over P v → ((∏ P ∈ S, single P (coord P y) : (Af E)ˣ) : Af E) P = iota x P := fun P hP => by
    rw [Fibre.prod_single_apply, if_pos ((hmem P).2 hP), hy]
  have hout : ∀ P, ¬ Over P v → ((∏ P ∈ S, single P (coord P y) : (Af E)ˣ) : Af E) P = 1 := fun P hP => by
    rw [Fibre.prod_single_apply, if_neg (fun h => hP ((hmem P).1 h))]
  refine ⟨∏ P ∈ S, single P (coord P y), hin, hout, ?_, fun χ hχ => ?_⟩
  · have hS2 : S = {P₁, P₂} := by
      ext R
      rw [hmem, Finset.mem_insert, Finset.mem_singleton]
      exact ⟨h2 P₁ P₂ hP₁ hP₂ hne R, fun h => by rcases h with rfl | rfl <;> assumption⟩
    unfold modF
    rw [finprod_eq_prod_of_mulSupport_subset (s := S) _ (fun P hP => by
      by_contra h
      refine hP ?_
      beta_reduce
      rw [hout P (fun h' => h ((hmem P).2 h'))]
      simp)]
    rw [Finset.prod_congr rfl (g := fun _ => ((Ideal.absNorm v.asIdeal : ℕ) : ℝ)⁻¹) (fun P hP => by
      rw [hin P ((hmem P).1 hP), hx P ((hmem P).1 hP), WithZero.log_exp, (hN P ((hmem P).1 hP)).1, zpow_neg_one])]
    rw [Finset.prod_const, hS2, Finset.card_pair hne]
  · have h1 := hχ.1 v k
    unfold Formalism.L2.Host.HChar.resFin at h1
    rw [MonoidHom.finsetProd_apply] at h1
    rw [map_prod, ← h1]
    exact Finset.prod_congr rfl fun P _ => rfl

end GlobalTheory.CMVal.Euler
