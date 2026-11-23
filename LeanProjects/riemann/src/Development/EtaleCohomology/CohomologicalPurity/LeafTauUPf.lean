import Development.EtaleCohomology.CohomologicalPurity.LeafTauPf

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.CohomologicalPurity.Thom

theorem pull_cast {q : ℕ} {E E' : Spc} (f : E ⟶ E') {n i n' i' : ℤ} (h1 : n = n') (h2 : i = i')
    (a : Ht q E' n i) : pull _ f (tw q i') n' (Ht.cast h1 h2 a) = Ht.cast h1 h2 (pull _ f (tw q i) n a) := by
  subst h1; subst h2; rfl

theorem pull_cpow (h6 : DivisorNaturality) (q : ℕ) [NeZero q] {E E' : Spc} (f : E ⟶ E') (hI : Inv q E')
    (x : Ht q E' 2 1) (k : ℕ) : pull _ f _ _ (cpow q x k) = cpow q (pull _ f _ _ x) k := by
  induction k with
  | zero => rw [cpow_zero, cpow_zero, pull_cast, (h6 q).2.1 f hI]
  | succ k ih => rw [cpow_succ, cpow_succ, pull_cast, (h6 q).1, ih]

theorem tail_fst (d : ℕ) (R : Type) [CommRing R] :
    (prod.map (Pj.tail d) (𝟙 _) : PR (d + 1) 1 R ⟶ PR d 0 R) ≫ prod.fst ≫ Pj.line d 0 =
      prod.fst ≫ Pj.line (d + 1) 1 := by
  rw [prod.map_fst_assoc, Pj.tail_line]

theorem pull_hyp (h6 : DivisorNaturality) (q : ℕ) [NeZero q] (d : ℕ) (R : Type) [CommRing R] (hI : Inv q (PR d 0 R)) :
    pull _ (prod.map (Pj.tail d) (𝟙 _) : PR (d + 1) 1 R ⟶ PR d 0 R) _ _ (hyp q d 0 R) = hyp q (d + 1) 1 R := by
  unfold hyp
  rw [(h6 q).2.2.1 _ _ hI, tail_fst]

theorem tail_poly (hG : LeafGeo) (h6 : DivisorNaturality) (q : ℕ) [NeZero q] (d : ℕ) (R : Type) [CommRing R]
    (hq : IsUnit (q : R)) (n i : ℤ) (a : ∀ j : Fin d, Ht q (sp R) (n - 2 * (j : ℕ)) (i - (j : ℕ))) :
    pull _ (prod.map (Pj.tail d) (𝟙 _) : PR (d + 1) 1 R ⟶ PR d 0 R) (tw q i) n (poly q d 0 R d n i a) =
      poly q (d + 1) 1 R d n i a := by
  have hI := hG.2.1 q d 0 R hq
  unfold poly
  rw [map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [pull_cast, (h6 q).1, ← pull_comp, prod.map_snd, Category.comp_id, pull_cpow h6 q _ hI, pull_hyp h6 q d R hI]

theorem LeafTauU_of (hG : LeafGeo) : LeafTauU := by
  intro hPB hTl H q _ d R _ hq n i
  have h6 : DivisorNaturality := H.2.2.2.2.1
  have hb := (hTl H q d R hq i n).comp (hPB H.1 h6 H.2.2.2.2.2.2.2.2.2.2.1 q d R hq n i)
  convert hb using 1
  funext a
  exact (tail_poly hG h6 q d R hq n i a).symm

end LateralTheory.CohomologicalPurity.Thom
