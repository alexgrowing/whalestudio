import Development.EtaleCohomology.EtaleSheaves.H0TwistOverClosedField

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC CochainComplex

namespace LateralTheory.E.LeafGhostCut
open LateralTheory.E.E4

def rmap (R : Type) [CommRing R] {U E U' E' : Spc} (f : U ⟶ E) (f' : U' ⟶ E') (u : U' ⟶ U) (e : E' ⟶ E)
    (comm : f' ≫ e = u ≫ f) : mappingCone ((chains R).map f') ⟶ mappingCone ((chains R).map f) :=
  mappingCone.map _ _ ((chains R).map u) ((chains R).map e) (by rw [← Functor.map_comp, ← Functor.map_comp, comm])

abbrev fgt (R : Type) [CommRing R] {U E : Spc} (f : U ⟶ E) (F : Shv R) (n : ℤ) : Hrel R f F n →+ H R E F n :=
  HK.pull R (mappingCone.inr ((chains R).map f)) F n

abbrev rpull (R : Type) [CommRing R] {U E U' E' : Spc} (f : U ⟶ E) (f' : U' ⟶ E') (u : U' ⟶ U) (e : E' ⟶ E)
    (comm : f' ≫ e = u ≫ f) (F : Shv R) (n : ℤ) : Hrel R f F n →+ Hrel R f' F n :=
  HK.pull R (rmap R f f' u e comm) F n

abbrev rpl (q : ℕ) (i : ℤ) {U E U' E' : Scheme.{0}} (f : U ⟶ E) (f' : U' ⟶ E') (u : U' ⟶ U) (e : E' ⟶ E)
    (comm : f' ≫ e = u ≫ f) (n : ℤ) : Hrel (ZMod q) (sch.map f) (tw q i) n →+ Hrel (ZMod q) (sch.map f') (tw q i) n :=
  rpull (ZMod q) (sch.map f) (sch.map f') (sch.map u) (sch.map e)
    (by rw [← Functor.map_comp, ← Functor.map_comp, comm]) (tw q i) n

def LeafRelExact : Prop := ∀ (R : Type) [CommRing R] (F : Shv R) {U E : Spc} (f : U ⟶ E) (n : ℤ) (x : H R E F n),
  pull R f F n x = 0 → ∃ y : Hrel R f F n, fgt R f F n y = x

def LeafRelNat : Prop := ∀ (R : Type) [CommRing R] (F : Shv R) {U E U' E' : Spc} (f : U ⟶ E) (f' : U' ⟶ E') (u : U' ⟶ U)
  (e : E' ⟶ E) (comm : f' ≫ e = u ≫ f) (n : ℤ) (y : Hrel R f F n),
  fgt R f' F n (rpull R f f' u e comm F n y) = pull R e F n (fgt R f F n y)

def LeafGhostRel : Prop := Hyps → ∀ (q : ℕ) [NeZero q] (k : Type) [Field k], IsUnit (q : k) → ∀ (i : ℤ)
  {B W Y0 Y1 Y2 : Scheme.{0}} (_ : B ⟶ Sp k) (ι : W ⟶ B) [IsClosedImmersion ι] (V : B.Opens), (V : Set B) = (Set.range ι)ᶜ →
  ∀ (p : Y0 ⟶ B) (g1 : Y1 ⟶ Y0) (g2 : Y2 ⟶ Y1), IsProper p → IsProper (g1 ≫ p) → IsProper (g2 ≫ g1 ≫ p) →
  (∀ (A : Type) [CommRing A] (t : Sp A ⟶ B), SH A → Set.range t ⊆ V →
    (∀ m, 3 ≤ m → Subsingleton (Ht q (sch.obj (pullback p t)) m i)) ∧ pl q i (fibMap g1 p t) 2 = 0 ∧
    pl q i (fibMap g2 (g1 ≫ p) t) 1 = 0 ∧ Function.Bijective (pl q i (pullback.snd (g2 ≫ g1 ≫ p) t) 0)) →
  ∀ (n : ℤ) (y : Hrel (ZMod q) (sch.map (pullback.fst p ι)) (tw q i) n),
    ∃ c : Hrel (ZMod q) (sch.map ι) (tw q i) n,
      rpl q i (pullback.fst p ι) (pullback.fst (g2 ≫ g1 ≫ p) ι)
          (pullback.map (g2 ≫ g1 ≫ p) ι p ι (g2 ≫ g1) (𝟙 W) (𝟙 B) (by simp) (by simp)) (g2 ≫ g1)
          (pullback.lift_fst _ _ _).symm n y =
        rpl q i ι (pullback.fst (g2 ≫ g1 ≫ p) ι) (pullback.snd (g2 ≫ g1 ≫ p) ι) (g2 ≫ g1 ≫ p) pullback.condition n c

open CochainComplex.HomComplex in
theorem relExact : LeafRelExact := by
  intro R _ F U E f n x hx
  obtain ⟨z, rfl⟩ := x.mk_surjective
  change CohomologyClass.mk (zcomp (Cocycle.ofHom ((chains R).map f)) z (zero_add n)) = 0 at hx
  rw [CohomologyClass.mk_eq_zero_iff] at hx
  obtain ⟨m, hm, β, hβ⟩ := hx
  refine ⟨CohomologyClass.mk (mappingCone.descCocycle _ (n.negOnePow • β) z hm ?_), ?_⟩
  · rw [δ_units_smul, hβ]
    simp [zcomp]
  · refine congrArg CohomologyClass.mk (Cocycle.ext ?_)
    simp [zcomp]

open CochainComplex.HomComplex in
theorem relNat : LeafRelNat := by
  intro R _ F U E U' E' f f' u e comm n y
  have key : mappingCone.inr ((chains R).map f') ≫ rmap R f f' u e comm =
      (chains R).map e ≫ mappingCone.inr ((chains R).map f) := by
    simp [rmap, mappingCone.map]
  obtain ⟨y, rfl⟩ := y.mk_surjective
  refine congrArg CohomologyClass.mk (Cocycle.ext ?_)
  simp only [zcomp, Cocycle.mk_coe, Cocycle.ofHom_coe]
  rw [← Cochain.comp_assoc_of_first_is_zero_cochain, ← Cochain.ofHom_comp, key, Cochain.ofHom_comp,
    Cochain.comp_assoc_of_first_is_zero_cochain]

theorem goal_of_all (hEx : LeafRelExact) (hNat : LeafRelNat) (hCore : LeafGhostRel) : LateralTheory.E.E4.LeafGhost := by
  intro hy q _ k _ hq i B W Y0 Y1 Y2 b ι _ V hV p g1 g2 h0 h1 h2 hA n a ha
  obtain ⟨y, rfl⟩ := hEx (ZMod q) (tw q i) (sch.map (pullback.fst p ι)) n a ha
  obtain ⟨c, hc⟩ := hCore hy q k hq i b ι V hV p g1 g2 h0 h1 h2 hA n y
  refine ⟨fgt (ZMod q) (sch.map ι) (tw q i) n c, ?_⟩
  have e1 := hNat (ZMod q) (tw q i) (sch.map ι) (sch.map (pullback.fst (g2 ≫ g1 ≫ p) ι))
    (sch.map (pullback.snd (g2 ≫ g1 ≫ p) ι)) (sch.map (g2 ≫ g1 ≫ p))
    (by rw [← Functor.map_comp, ← Functor.map_comp, pullback.condition]) n c
  have hsq : pullback.fst (g2 ≫ g1 ≫ p) ι ≫ (g2 ≫ g1) =
      pullback.map (g2 ≫ g1 ≫ p) ι p ι (g2 ≫ g1) (𝟙 W) (𝟙 B) (by simp) (by simp) ≫ pullback.fst p ι := (pullback.lift_fst _ _ _).symm
  have e2 := hNat (ZMod q) (tw q i) (sch.map (pullback.fst p ι)) (sch.map (pullback.fst (g2 ≫ g1 ≫ p) ι))
    (sch.map (pullback.map (g2 ≫ g1 ≫ p) ι p ι (g2 ≫ g1) (𝟙 W) (𝟙 B) (by simp) (by simp))) (sch.map (g2 ≫ g1))
    (by rw [← Functor.map_comp, ← Functor.map_comp, hsq]) n y
  change pull _ _ _ _ _ = pull _ _ _ _ _
  rw [← e1, ← e2]
  exact congrArg _ hc.symm

theorem goal_of (hCore : LeafGhostRel) : LateralTheory.E.E4.LeafGhost := goal_of_all relExact relNat hCore

end LateralTheory.E.LeafGhostCut

end
