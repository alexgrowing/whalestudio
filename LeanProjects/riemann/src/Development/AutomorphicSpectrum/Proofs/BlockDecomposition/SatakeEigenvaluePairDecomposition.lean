import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsIntZero
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.ReadMod

open NumberField IsDedekindDomain Matrix
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC GlobalTheory.BCT GlobalTheory.LFun Formalism.L2.Host
open PositivityTheory.Rg.Rs PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.SpectralAccumulation PositivityTheory.Rg.BcB.G8 PositivityTheory.Rg.BcB.F.RS GlobalTheory.CompanionTheory.CtS
open scoped Classical

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.CompanionTheory.CtS.SatConv

theorem esymm_cons_succ' (a : ℂ) (s : Multiset ℂ) (n : ℕ) :
    (a ::ₘ s).esymm (n + 1) = s.esymm (n + 1) + a * s.esymm n := by
  simp [Multiset.esymm, Multiset.powersetCard_cons, Multiset.map_map, Multiset.sum_map_mul_left]

theorem coeff_prod_one_add (s : Multiset ℂ) (n : ℕ) :
    ((s.map fun a => (1 + Polynomial.C a * Polynomial.X : Polynomial ℂ)).prod).coeff n = s.esymm n := by
  induction s using Multiset.induction_on generalizing n with
  | empty =>
    cases n with
    | zero => simp [Multiset.esymm]
    | succ n => simp [Multiset.esymm, Polynomial.coeff_one, Multiset.powersetCard_zero_right]
  | cons a s ih =>
    rw [Multiset.map_cons, Multiset.prod_cons, add_mul, one_mul, mul_assoc, Polynomial.coeff_add,
      Polynomial.coeff_C_mul]
    cases n with
    | zero => simp [ih, Multiset.esymm]
    | succ n => rw [Polynomial.coeff_X_mul, ih, ih, esymm_cons_succ']

theorem esymm_add_antidiagonal (s t : Multiset ℂ) (k : ℕ) :
    (s + t).esymm k = ∑ p ∈ Finset.HasAntidiagonal.antidiagonal k, s.esymm p.1 * t.esymm p.2 := by
  rw [← coeff_prod_one_add, Multiset.map_add, Multiset.prod_add, Polynomial.coeff_mul]
  simp only [coeff_prod_one_add]

theorem esymm_map_mul_unit (B : Multiset ℂˣ) (z : ℂˣ) (j : ℕ) :
    ((B.map (· * z)).map fun b : ℂˣ => (b : ℂ)).esymm j =
      (z : ℂ) ^ j * (B.map fun b : ℂˣ => (b : ℂ)).esymm j := by
  have h := Multiset.pow_smul_esymm (z : ℂ) j (B.map fun b : ℂˣ => (b : ℂ))
  simp only [smul_eq_mul, Multiset.map_map, Function.comp_def] at h
  simp only [Multiset.map_map, Function.comp_def, Units.val_mul, mul_comm _ (z : ℂ)]
  exact h.symm

theorem esymm_eq_zero_of_card_lt (s : Multiset ℂ) {k : ℕ} (h : s.card < k) : s.esymm k = 0 := by
  simp [Multiset.esymm, Multiset.powersetCard_eq_empty k h]

theorem satEig_join : ∀ (q n a b : ℕ) (c : ℂˣ) (Ba Bb : Multiset ℂˣ), q ≠ 0 → a + b = n → Ba.card = a → Bb.card = b → ∀ k ≤ n, satEig q n (Ba.map (· * c ^ b) + Bb.map (· * c ^ a)) k = ∑ p ∈ pairs a b k, coef q c a b p.1 p.2 * (satEig q a Ba p.1 * satEig q b Bb p.2) := by
  intro q n a b c Ba Bb hq hab hBa hBb k _
  have hq' : (q : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hq
  subst hab
  rw [pairs, Finset.sum_filter]
  simp only [satEig]
  rw [Multiset.map_add, esymm_add_antidiagonal, Finset.mul_sum]
  refine Finset.sum_congr rfl ?_
  rintro ⟨i, j⟩ hp
  have hk : i + j = k := by simpa using hp
  subst hk
  simp only [esymm_map_mul_unit]
  split_ifs with h
  · have hpow : (q : ℂ) ^ ((((i + j : ℕ) : ℂ) * (((a + b : ℕ) : ℂ) - ((i + j : ℕ) : ℂ))) / 2) =
        (q : ℂ) ^ (((i : ℂ) * b + (j : ℂ) * a) / 2 - (i : ℂ) * j) *
          ((q : ℂ) ^ (((i : ℂ) * ((a : ℂ) - i)) / 2) * (q : ℂ) ^ (((j : ℂ) * ((b : ℂ) - j)) / 2)) := by
      rw [← Complex.cpow_add _ _ hq', ← Complex.cpow_add _ _ hq']
      congr 1
      push_cast
      ring
    rw [hpow, coef]
    simp only [Units.val_pow_eq_pow_val]
    rw [pow_add, pow_mul, pow_mul, pow_right_comm (c : ℂ) i b, pow_right_comm (c : ℂ) j a]
    ring
  · have hz : (Ba.map fun x : ℂˣ => (x : ℂ)).esymm i = 0 ∨ (Bb.map fun x : ℂˣ => (x : ℂ)).esymm j = 0 := by
      by_cases hi : i ≤ a
      · right
        refine esymm_eq_zero_of_card_lt _ ?_
        rw [Multiset.card_map, hBb]
        by_contra hj
        exact h ⟨hi, by omega⟩
      · left
        refine esymm_eq_zero_of_card_lt _ ?_
        rw [Multiset.card_map, hBa]
        omega
    rcases hz with hz | hz <;> simp [hz]

end GlobalTheory.CompanionTheory.CtS.SatConv
