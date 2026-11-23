import Development.EtaleCohomology.CohomologicalPurity.LeafThomCut

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.CohomologicalPurity.Thom

theorem tn_pull_cast {q : ℕ} {E E' : Spc} (f : E ⟶ E') {n i n' i' : ℤ} (hn : n = n') (hi : i = i')
    (x : Ht q E' n i) : pull _ f _ _ (x.cast hn hi) = Ht.cast hn hi (pull _ f _ _ x) := by
  subst hn; subst hi; rfl

theorem tn_red_cast {q r : ℕ} {E : Spc} {n i n' i' : ℤ} (hn : n = n') (hi : i = i')
    (x : Ht q E n i) : red q r E _ _ (x.cast hn hi) = Ht.cast hn hi (red q r E _ _ x) := by
  subst hn; subst hi; rfl

theorem tn_pull_cpow (h : DivisorNaturality) (q : ℕ) [NeZero q] {E E' : Spc} (f : E ⟶ E') (hI : Inv q E')
    (x : Ht q E' 2 1) (k : ℕ) : pull _ f _ _ (cpow q x k) = cpow q (pull _ f _ _ x) k := by
  induction k with
  | zero => rw [cpow_zero, cpow_zero, tn_pull_cast, (h q).2.1 f hI]
  | succ k ih => rw [cpow_succ, cpow_succ, tn_pull_cast, (h q).1, ih]

theorem tn_red_cpow (h : A11) (q r : ℕ) [NeZero q] (hr : r ∣ q) {E : Spc} (hI : Inv q E)
    (L : E ⟶ ofCat (glCat 1)) (k : ℕ) : red q r E _ _ (cpow q (c1 q L) k) = cpow r (c1 r L) k := by
  induction k with
  | zero => rw [cpow_zero, cpow_zero, tn_red_cast, ((h q r hr E).2.1 hI).1]
  | succ k ih => rw [cpow_succ, cpow_succ, tn_red_cast, (h q r hr E).1, ih, ((h q r hr E).2.1 hI).2]

theorem tn_pull_hyp (h : DivisorNaturality) (q : ℕ) [NeZero q] (N : ℕ) {A B : Type} [CommRing A] [CommRing B]
    (f : PR N 0 B ⟶ PR N 0 A) (hI : Inv q (PR N 0 A))
    (hl : f ≫ prod.fst ≫ Pj.line N 0 = prod.fst ≫ Pj.line N 0) :
    pull _ f _ _ (hyp q N 0 A) = hyp q N 0 B := by
  unfold hyp
  rw [(h q).2.2.1 f _ hI, hl]

theorem tn_pull_poly (h : DivisorNaturality) (q : ℕ) [NeZero q] (N : ℕ) {A B : Type} [CommRing A] [CommRing B]
    (φ : A →+* B) (f : PR N 0 B ⟶ PR N 0 A) (hI : Inv q (PR N 0 A))
    (hl : f ≫ prod.fst ≫ Pj.line N 0 = prod.fst ≫ Pj.line N 0)
    (hs : f ≫ prod.snd = prod.snd ≫ spMap φ) (m : ℕ) (n i : ℤ)
    (a : ∀ j : Fin m, Ht q (sp A) (n - 2 * (j : ℕ)) (i - (j : ℕ))) :
    pull _ f _ _ (poly q N 0 A m n i a) = poly q N 0 B m n i (fun j => pull _ (spMap φ) _ _ (a j)) := by
  unfold poly
  rw [map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [tn_pull_cast, (h q).1, ← pull_comp, hs, pull_comp, tn_pull_cpow h q f hI, tn_pull_hyp h q N f hI hl]

theorem tn_red_poly (h : A11) (q r : ℕ) [NeZero q] (hr : r ∣ q) (N : ℕ) {A : Type} [CommRing A]
    (hI : Inv q (PR N 0 A)) (m : ℕ) (n i : ℤ)
    (a : ∀ j : Fin m, Ht q (sp A) (n - 2 * (j : ℕ)) (i - (j : ℕ))) :
    red q r _ _ _ (poly q N 0 A m n i a) = poly r N 0 A m n i (fun j => red q r _ _ _ (a j)) := by
  unfold poly
  rw [map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [tn_red_cast, (h q r hr _).1, ← pull_red]
  unfold hyp
  rw [tn_red_cpow h q r hr hI]

theorem LeafTauNat_of (hG : LeafGeo) : LeafTauNat := by
  intro h6 h11 q _ d A _ hq τ hτ
  obtain ⟨a, ha⟩ := hτ
  have hI : Inv q (PR (d + 1) 0 A) := hG.2.1 q (d + 1) 0 A hq
  refine ⟨fun B _ φ g hl hs => ⟨fun j => pull _ (spMap φ) _ _ (a j), ?_⟩,
    fun r hr τ' hτ' => ⟨fun j => red q r _ _ _ (a j), ?_⟩⟩
  · have e : Hs.fgt q (pr d B) _ _ (Hs.pull q g _ _ τ) =
        pull (E := PR (d + 1) 0 B) (E' := PR (d + 1) 0 A) _ g.right _ _
          (show Ht q (PR (d + 1) 0 A) _ _ from Hs.fgt q (pr d A) _ _ τ) := by
      change pull _ (dbl.inl _) _ _ (pull _ (dbl.map g) _ _ τ.1) =
        pull _ g.right _ _ (pull _ (dbl.inl _) _ _ τ.1)
      rw [← pull_comp, ← pull_comp, inl_map]
    rw [e, ha, map_add, tn_pull_cpow h6 q (E := PR (d + 1) 0 B) (E' := PR (d + 1) 0 A) g.right hI,
      tn_pull_hyp h6 q (d + 1) g.right hI hl, tn_pull_poly h6 q (d + 1) φ g.right hI hl hs]
  · have e : Hs.fgt r (pr d A) _ _ τ' = red q r (PR (d + 1) 0 A) _ _
        (show Ht q (PR (d + 1) 0 A) _ _ from Hs.fgt q (pr d A) _ _ τ) := by
      change pull _ (dbl.inl _) _ _ τ'.1 = red q r _ _ _ (pull _ (dbl.inl _) _ _ τ.1)
      rw [hτ', pull_red]
    rw [e, ha, map_add, tn_red_poly h11 q r hr (d + 1) hI]
    unfold hyp
    rw [tn_red_cpow h11 q r hr hI]

end LateralTheory.CohomologicalPurity.Thom
