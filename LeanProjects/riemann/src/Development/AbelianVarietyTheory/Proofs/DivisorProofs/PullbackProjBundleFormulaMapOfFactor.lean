import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProjectiveBundleFormulaOfUnitOnEtalePoints
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TrivV
import Development.AbelianVarietyTheory.Definitions.Divisors.SecClass
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CotDComp
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

noncomputable section

namespace GlobalTheory.EtC.PbfNatl

theorem pull_htCast' (q : ℕ) {E E' : Spc} (f : E ⟶ E') {n i n' i' : ℤ} (hn : n = n') (hi : i = i') (x : Ht q E' n i) :
    pull _ f _ _ (Ht.cast hn hi x) = Ht.cast hn hi (pull _ f _ _ x : Ht q E n i) := by
  subst hn; subst hi; rfl

theorem pull_cpow' (q : ℕ) [NeZero q] (hA : DivisorNaturality) {E E' : Spc} (f : E ⟶ E') (hE' : Inv q E') (x : Ht q E' 2 1) (k : ℕ) :
    pull _ f _ _ (cpow q x k) = cpow q (pull _ f _ _ x : Ht q E 2 1) k := by
  induction k with
  | zero => rw [cpow_zero, cpow_zero, pull_htCast', (hA q).2.1 f hE']
  | succ k ih => rw [cpow_succ, cpow_succ, pull_htCast', (hA q).1, ih]

theorem pull_pbfMap_of_factor : DivisorNaturality → ∀ (q : ℕ) [NeZero q] {E B P : Spc} {N : ℕ} (V : E ⟶ ofCat (glCat N))
    (L : B ⟶ ofCat (glCat 1)) (θ : P ⟶ pullback V (PGL.pr N)) (f : P ⟶ E) (g : P ⟶ B), Inv q B →
    Inv q (pullback V (PGL.pr N)) → θ ≫ pullback.fst _ _ = f → θ ≫ pullback.snd _ _ ≫ PGL.line N = g ≫ L →
    ∀ (n i : ℤ) (a : ∀ j : Fin N, Ht q E (n - 2 * (j : ℕ)) (i - (j : ℕ))),
    pull _ θ _ _ (pbfMap q V n i a) = ∑ j : Fin N, ((cup q (pull _ f _ _ (a j)) (pull _ g _ _ (cpow q (c1 q L) j))).cast (by ring) (by ring) : Ht q P n i) := by
  intro hA q _ E B P N V L θ f g hB hP hf hg n i a
  unfold pbfMap
  rw [map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [pull_htCast', (hA q).1, ← pull_comp, hf, pull_cpow' q hA _ hP, (hA q).2.2.1 _ _ hP,
    pull_cpow' q hA _ hB, (hA q).2.2.1 _ _ hB, hg]

end GlobalTheory.EtC.PbfNatl

end
