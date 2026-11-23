import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SmallFam
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.SmallSecTensTriv
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsAlgClosedBaseChange
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermLineBundlePairSectionsMulMemNormMul
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAmpleSectionClearingRationalFunctionDenomiStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPosNonzeroPairSectionOfAmpleStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSNef

set_option autoImplicit false

namespace GlobalTheory.HSNef.Den

variable {k : Type} [CommRing k] {X : Scheme.{0}} [IsIntegral X] {p : X ⟶ Sp k}

theorem one_mem_H (P : Pair p) : (1 : X.functionField) ∈ P.H 0 0 := by
  intro x i j _ _
  exact ⟨1, by simp [Pair.loc]⟩

theorem mul_mem_H {P : Pair p} {a b a' b' : ℤ} {f g : X.functionField} (hf : f ∈ P.H a b) (hg : g ∈ P.H a' b') :
    f * g ∈ P.H (a + a') (b + b') :=
  (NuMul.mul_mem_H_and_nu_mul k X p P a b a' b' f g hf hg).1

theorem prod_mem_H {P : Pair p} {J : Type} (s : Finset J) (c : J → ℕ) (g : J → X.functionField)
    (hg : ∀ j ∈ s, g j ∈ P.H 0 (c j)) : (∏ j ∈ s, g j) ∈ P.H 0 ((∑ j ∈ s, c j : ℕ) : ℤ) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using one_mem_H P
  | insert l s hl ih =>
    rw [Finset.prod_insert hl, Finset.sum_insert hl]
    have := mul_mem_H (hg l (Finset.mem_insert_self l s)) (ih fun j hj => hg j (Finset.mem_insert_of_mem hj))
    simpa using this

theorem exists_clear_denominators : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ (P : Pair p), IsAmpleLB P.A.B → ∀ (a : ℤ) (J : Type) [Finite J] (f : J → X.functionField), ∃ (c : ℕ) (g : X.functionField), 0 < c ∧ g ≠ 0 ∧ g ∈ P.H a c ∧ ∀ j, g * f j ∈ P.H a c := by
  intro k _ X _ p D hX P hA a J _ f
  classical
  have := Fintype.ofFinite J
  choose c g hc hg0 hg hgf using fun j => GlobalTheory.T.exists_ampleSection_clearing_rationalFunction_denominator k X p D hX P hA (f j)
  obtain ⟨c', h, hc', h0, hh⟩ := GlobalTheory.T.exists_pos_nonzero_pairSection_of_ample k X p D hX P hA a
  refine ⟨c' + ∑ j, c j, h * ∏ j, g j, by omega, mul_ne_zero h0 (Finset.prod_ne_zero_iff.2 fun j _ => hg0 j), ?_, fun j => ?_⟩
  · have := mul_mem_H hh (prod_mem_H Finset.univ c g fun j _ => hg j)
    simpa using this
  · have e : h * (∏ l, g l) * f j = h * ((g j * f j) * ∏ l ∈ Finset.univ.erase j, g l) := by
      rw [← Finset.mul_prod_erase Finset.univ g (Finset.mem_univ j)]; ring
    have es : ∑ l, c l = c j + ∑ l ∈ Finset.univ.erase j, c l := (Finset.add_sum_erase _ _ (Finset.mem_univ j)).symm
    rw [e, es]
    have := mul_mem_H hh (mul_mem_H (hgf j) (prod_mem_H (Finset.univ.erase j) c g fun l _ => hg l))
    simpa using this

end GlobalTheory.HSNef.Den
