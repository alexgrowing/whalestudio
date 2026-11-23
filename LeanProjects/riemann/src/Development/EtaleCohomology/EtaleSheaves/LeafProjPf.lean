import Development.EtaleCohomology.EtaleSheaves.LeafChartRing

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex GlobalTheory.EtC

namespace LateralTheory.E.LeafProjPf

theorem pull_cast (q : ℕ) {E E' : Spc} (f : E ⟶ E') {n i n' i' : ℤ} (hn : n = n') (hi : i = i') (x : Ht q E' n i) :
    pull _ f _ _ (Ht.cast hn hi x) = Ht.cast hn hi (pull _ f _ _ x) := by
  subst hn; subst hi; rfl

theorem cast_zero (q : ℕ) {E : Spc} {n i n' i' : ℤ} (hn : n = n') (hi : i = i') :
    Ht.cast hn hi (0 : Ht q E n i) = 0 := by
  subst hn; subst hi; rfl

theorem pull_cpow (hN : DivisorNaturality) (q : ℕ) [NeZero q] {E E' : Spc} (f : E ⟶ E') (hE : Inv q E') (x : Ht q E' 2 1) (k : ℕ) :
    pull _ f _ _ (cpow q x k) = cpow q (pull _ f _ _ x) k := by
  induction k with
  | zero => rw [cpow_zero, cpow_zero, pull_cast, (hN q).2.1 f hE]
  | succ k ih => rw [cpow_succ, cpow_succ, pull_cast, (hN q).1, ih]

theorem inv_pb (q : ℕ) {E : Spc} {P : Spc} (g : P ⟶ E) (hE : Inv q E) : Inv q P :=
  fun U ⟨x⟩ => hE U ⟨LateralTheory.E.t_E6Cut.sxMap g x⟩

def Phi (q : ℕ) {E : Spc} {N : ℕ} (V : E ⟶ ofCat (glCat N)) (n i : ℤ) :
    (∀ j : Fin N, Ht q E (n - 2 * (j : ℕ)) (i - (j : ℕ))) → Ht q (pullback V (PGL.pr N)) n i := fun a =>
  ∑ j : Fin N, ((cup q (pull _ (pullback.fst V (PGL.pr N)) _ _ (a j))
      (cpow q (c1 q (pullback.snd V (PGL.pr N) ≫ PGL.line N)) j)).cast (by ring) (by ring) : Ht q _ n i)

theorem LeafProj_of (hNat : LateralTheory.E.t_E6Cut.LeafNat) : LateralTheory.E.t_E6Cut.LeafProj := by
  intro a1 a5 a7 a9 a10 d1 q _ i E N V V' hE s hs1 hs2
  have hN : DivisorNaturality := hNat a1 a5 a7 a9 a10
  have hP' : Inv q (pullback V' (PGL.pr (N + 1))) := inv_pb q (pullback.fst _ _) hE
  have term : ∀ {m k m' k' : ℤ} (x : Ht q E m k) (j : ℕ) (hn : m + 2 * (j : ℤ) = m') (hi : k + (j : ℤ) = k'),
      pull _ s _ _ (Ht.cast hn hi (cup q (pull _ (pullback.fst V' (PGL.pr (N + 1))) _ _ x)
        (cpow q (c1 q (pullback.snd V' (PGL.pr (N + 1)) ≫ PGL.line (N + 1))) j))) =
      Ht.cast hn hi (cup q (pull _ (pullback.fst V (PGL.pr N)) _ _ x)
        (cpow q (c1 q (pullback.snd V (PGL.pr N) ≫ PGL.line N)) j)) := by
    intro m k m' k' x j hn hi
    rw [pull_cast, (hN q).1, ← pull_comp, hs1, pull_cpow hN q s hP', (hN q).2.2.1 s _ hP', hs2]
  have key : ∀ n : ℤ, n < 2 * N → Function.Bijective (pull _ s (tw q i) n) := by
    intro n hn
    have hsub : Subsingleton (Ht q E (n - 2 * ((Fin.last N : Fin (N + 1)) : ℕ)) (i - ((Fin.last N : Fin (N + 1)) : ℕ))) :=
      (a9 (ZMod q) (tw q _)).1 E _ (by simp only [Fin.val_last]; omega)
    have h' : Function.Bijective (Phi q V' n i) := d1 q V' hE n i
    have h : Function.Bijective (Phi q V n i) := d1 q V hE n i
    have hcomp : ∀ a, pull _ s _ _ (Phi q V' n i a) = Phi q V n i (fun j => a j.castSucc) := by
      intro a
      simp only [Phi, map_sum]
      rw [Fin.sum_univ_castSucc]
      have hl : a (Fin.last N) = 0 := Subsingleton.elim _ _
      rw [hl, map_zero, map_zero, AddMonoidHom.zero_apply, cast_zero, map_zero, add_zero]
      refine Finset.sum_congr rfl fun j _ => ?_
      exact term _ _ _ _
    have hres : ∀ a b : (∀ j : Fin (N + 1), Ht q E (n - 2 * (j : ℕ)) (i - (j : ℕ))),
        (fun j : Fin N => a j.castSucc) = (fun j : Fin N => b j.castSucc) → a = b := by
      intro a b hab
      funext j
      refine Fin.lastCases ?_ (fun j => ?_) j
      · exact Subsingleton.elim _ _
      · exact congrFun hab j
    constructor
    · intro x y hxy
      obtain ⟨a, rfl⟩ := h'.2 x
      obtain ⟨b, rfl⟩ := h'.2 y
      rw [hcomp, hcomp] at hxy
      rw [hres a b (h.1 hxy)]
    · intro y
      obtain ⟨b, rfl⟩ := h.2 y
      refine ⟨Phi q V' n i (Fin.lastCases (motive := fun j : Fin (N + 1) => Ht q E (n - 2 * (j : ℕ)) (i - (j : ℕ))) 0
        (fun j => b j)), ?_⟩
      rw [hcomp]
      congr 1
      funext j
      exact Fin.lastCases_castSucc _
  intro n
  exact ⟨fun hn => key n (by omega), fun hn => (key n hn).1⟩

end LateralTheory.E.LeafProjPf
