import Development.EtaleCohomology.EtaleSheaves.InstCommRingR

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.E.D2

theorem pull_cast_nat {q : ℕ} {E E' : Spc} (f : E ⟶ E') {n i n' i' : ℤ} (hn : n = n') (hi : i = i') (x : Ht q E' n i) :
    pull _ f _ _ (x.cast hn hi) = Ht.cast hn hi (pull _ f _ _ x : Ht q E n i) := by
  subst hn hi; rfl

abbrev PB.over {E E' : Spc} (f : E ⟶ E') {N : ℕ} (V : E' ⟶ ofCat (glCat N)) : PB (f ≫ V) ⟶ PB V :=
  pullback.map (f ≫ V) (PGL.pr N) V (PGL.pr N) f (𝟙 _) (𝟙 _) (by simp) (by simp)

theorem PB.over_pr {E E' : Spc} (f : E ⟶ E') {N : ℕ} (V : E' ⟶ ofCat (glCat N)) :
    PB.over f V ≫ PB.pr V = PB.pr (f ≫ V) ≫ f := by
  simp only [PB.over, PB.pr, pullback.map, pullback.lift_fst]

theorem PB.over_line {E E' : Spc} (f : E ⟶ E') {N : ℕ} (V : E' ⟶ ofCat (glCat N)) :
    PB.over f V ≫ PB.line V = PB.line (f ≫ V) := by
  simp only [PB.over, PB.line, pullback.map, pullback.lift_snd_assoc, Category.comp_id]

theorem LeafNat_of (hA : LeafA6nat) : LeafNat := by
  intro q _ P E E' f h h' N V c hc
  obtain ⟨h0, hz, hs⟩ := hc
  refine ⟨?_, ?_, ?_⟩
  · rw [← P.map_ι f h h', h0, map_one]
  · intro j hj; simp [hz j hj]
  · have hg := congrArg (P.map (PB.over f V) (inv_of (PB.pr (f ≫ V)) h) (inv_of (PB.pr V) h')) hs
    rw [map_zero, map_sum] at hg
    rw [← hg]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [map_mul, map_pow, P.map_ι, Collected.deg1, pull_cast_nat, ← pull_comp, PB.over_pr]
    rw [(hA q).2.2.1 _ _ (inv_of (PB.pr V) h'), PB.over_line]

end LateralTheory.E.D2
