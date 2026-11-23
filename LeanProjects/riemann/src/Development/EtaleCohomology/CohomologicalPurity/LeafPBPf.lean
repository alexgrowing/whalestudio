import Development.EtaleCohomology.CohomologicalPurity.LeafThomCut

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.CohomologicalPurity.Thom

def LeafPBInvSp : Prop := ∀ (q : ℕ) (R : Type) [CommRing R], IsUnit (q : R) → Inv q (sp R)

def LeafPBCmp : Prop := A1 → ∀ (q : ℕ) [NeZero q] (N : ℕ) (R : Type) [CommRing R], IsUnit (q : R) →
  ∃ (V : sp R ⟶ ofCat (glCat N)) (e : pullback V (PGL.pr N) ⟶ PR N 0 R),
    e ≫ prod.snd = pullback.fst V (PGL.pr N) ∧
    e ≫ prod.fst ≫ Pj.line N 0 = pullback.snd V (PGL.pr N) ≫ PGL.line N ∧
    ∀ i : ℤ, Eqv _ e (tw q i)

def LeafAffEqv : Prop := A1 → ∀ (q : ℕ) [NeZero q] {E E' : Spc} (e : E ⟶ E'),
  (∀ (n : ℕ) (A : Type) [CommRing A], Function.Bijective
    (fun x : Sx E n (Spec (CommRingCat.of A)) => (e.app (op (SimplexCategory.mk n))).app (op (Spec (CommRingCat.of A))) x)) →
  ∀ i : ℤ, Eqv _ e (tw q i)

def LeafPBMap : Prop := ∀ (N : ℕ) (R : Type) [CommRing R],
  ∃ (V : sp R ⟶ ofCat (glCat N)) (e : pullback V (PGL.pr N) ⟶ PR N 0 R),
    e ≫ prod.snd = pullback.fst V (PGL.pr N) ∧
    e ≫ prod.fst ≫ Pj.line N 0 = pullback.snd V (PGL.pr N) ≫ PGL.line N ∧
    ∀ (n : ℕ) (A : Type) [CommRing A], Function.Bijective
      (fun x : Sx (pullback V (PGL.pr N)) n (Spec (CommRingCat.of A)) =>
        (e.app (op (SimplexCategory.mk n))).app (op (Spec (CommRingCat.of A))) x)

theorem leafPBCmp_of (hMap : LeafPBMap) (hAff : LeafAffEqv) : LeafPBCmp := by
  intro hA1 q _ N R _ _
  obtain ⟨V, e, h1, h2, h3⟩ := hMap N R
  exact ⟨V, e, h1, h2, hAff hA1 q e h3⟩

theorem leafPBInvSp : LeafPBInvSp := by
  intro q R _ hq U ⟨x⟩
  have f : U ⟶ Spec (CommRingCat.of R) := x
  have h1 := hq.map (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom
  have h2 := h1.map f.appTop.hom
  simpa using h2

theorem pull_cast' {q : ℕ} {E E' : Spc} (f : E ⟶ E') {n i n' i' : ℤ} (hn : n = n') (hi : i = i')
    (x : Ht q E' n i) : pull _ f _ _ (Ht.cast hn hi x) = Ht.cast (E := E) hn hi (pull _ f _ _ x) := by
  subst hn; subst hi; rfl

theorem pull_cpow' (hA : DivisorNaturality) (q : ℕ) [NeZero q] {E E' : Spc} (f : E ⟶ E') (hE : Inv q E')
    (x : Ht q E' 2 1) (k : ℕ) : pull _ f _ _ (cpow q x k) = cpow q (pull _ f _ _ x) k := by
  induction k with
  | zero => rw [cpow_zero, cpow_zero, pull_cast', (hA q).2.1 f hE]
  | succ k ih =>
    show pull _ f _ _ ((cup q (cpow q x k) x).cast (by push_cast; ring) (by push_cast; ring)) =
      (cup q (cpow q (pull _ f _ _ x) k) (pull _ f _ _ x)).cast (by push_cast; ring) (by push_cast; ring)
    rw [pull_cast', (hA q).1, ih]

theorem LeafPB_of' (hGeo : LeafGeo) (hCmp : LeafPBCmp) : LeafPB := by
  have hInv := leafPBInvSp
  intro hA1 hA6 hD1 q _ N R _ hq n i
  obtain ⟨V, e, h1, h2, h3⟩ := hCmp hA1 q N R hq
  have hD := hD1 q V (hInv q R hq) n i
  have hPR : Inv q (PR N 0 R) := hGeo.2.1 q N 0 R hq
  refine (Function.Bijective.of_comp_iff' (h3 i n) _).1 ?_
  convert hD using 1
  funext a
  simp only [Function.comp_apply, poly, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [pull_cast', (hA6 q).1, pull_cpow' hA6 q e hPR, ← pull_comp, h1, hyp, (hA6 q).2.2.1 e _ hPR, h2]

theorem LeafPB_of (hGeo : LeafGeo) (hMap : LeafPBMap) (hAff : LeafAffEqv) : LeafPB :=
  LeafPB_of' hGeo (leafPBCmp_of hMap hAff)

end LateralTheory.CohomologicalPurity.Thom
