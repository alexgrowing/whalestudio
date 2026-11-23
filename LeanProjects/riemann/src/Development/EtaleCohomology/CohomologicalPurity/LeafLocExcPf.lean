import Development.EtaleCohomology.CohomologicalPurity.LeafTubeCut

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.CohomologicalPurity.TubeCut

theorem five_bij {A1 A2 A3 A4 A5 B1 B2 B3 B4 B5 : Type*} [AddCommGroup A1] [AddCommGroup A2] [AddCommGroup A3]
    [AddCommGroup A4] [AddCommGroup A5] [AddCommGroup B1] [AddCommGroup B2] [AddCommGroup B3] [AddCommGroup B4]
    [AddCommGroup B5] (f1 : A1 →+ A2) (f2 : A2 →+ A3) (f3 : A3 →+ A4) (f4 : A4 →+ A5)
    (g1 : B1 →+ B2) (g2 : B2 →+ B3) (g3 : B3 →+ B4) (g4 : B4 →+ B5)
    (v1 : A1 →+ B1) (v2 : A2 →+ B2) (v3 : A3 →+ B3) (v4 : A4 →+ B4) (v5 : A5 →+ B5)
    (hf2 : Function.Exact f1 f2) (hf3 : Function.Exact f2 f3) (hf4 : Function.Exact f3 f4)
    (hg2 : Function.Exact g1 g2) (hg3 : Function.Exact g2 g3) (hg4 : Function.Exact g3 g4)
    (c1 : ∀ x, g1 (v1 x) = v2 (f1 x)) (c2 : ∀ x, g2 (v2 x) = v3 (f2 x)) (c3 : ∀ x, g3 (v3 x) = v4 (f3 x))
    (c4 : ∀ x, g4 (v4 x) = v5 (f4 x))
    (h1 : Function.Surjective v1) (h2 : Function.Bijective v2) (h4 : Function.Bijective v4)
    (h5 : Function.Injective v5) : Function.Bijective v3 := by
  refine ⟨(injective_iff_map_eq_zero v3).2 fun a ha => ?_, fun b => ?_⟩
  · have e4 : f3 a = 0 := h4.1 (by rw [← c3, ha]; simp)
    obtain ⟨a2, rfl⟩ := (hf3 a).1 e4
    have e2 : g2 (v2 a2) = 0 := by rw [c2, ha]
    obtain ⟨b1, hb1⟩ := (hg2 _).1 e2
    obtain ⟨a1, rfl⟩ := h1 b1
    have e1 : f1 a1 = a2 := h2.1 (by rw [← c1, hb1])
    subst e1
    exact (hf2 _).2 ⟨a1, rfl⟩
  · obtain ⟨a4, ha4⟩ := h4.2 (g3 b)
    have e5 : f4 a4 = 0 := h5 (by rw [← c4, ha4, map_zero]; exact (hg4 _).2 ⟨b, rfl⟩)
    obtain ⟨a3, ha3⟩ := (hf4 a4).1 e5
    have e3 : g3 (b - v3 a3) = 0 := by rw [map_sub, c3, ha3, ha4, sub_self]
    obtain ⟨b2, hb2⟩ := (hg3 _).1 e3
    obtain ⟨a2, rfl⟩ := h2.2 b2
    refine ⟨a3 + f2 a2, ?_⟩
    rw [map_add, ← c2, hb2]
    abel

theorem mono_sch_open {X : Scheme.{0}} (U : X.Opens) : Mono (sch.map U.ι) := by
  have hy : Mono (yoneda.map U.ι) := by
    refine @NatTrans.mono_of_mono_app _ _ _ _ _ _ _ fun T => ?_
    exact (mono_iff_injective _).2 fun a b h => (cancel_mono U.ι).1 h
  exact @NatTrans.mono_of_mono_app _ _ _ _ _ _ _ fun _ => hy

theorem eqv_of_loc (a1 : A1) {X : Scheme.{0}} {E : Spc} {π : E ⟶ sch.obj X} (L : Loc π) (R : Type) [CommRing R]
    {Y : Scheme.{0}} (g : Y ⟶ X) (F : Shv R) : Eqv R (pullback.snd π (sch.map g)) F :=
  fun n => @a1 R _ _ _ _ (L R Y g) F n

theorem eqv_base (a1 : A1) {X : Scheme.{0}} {E : Spc} {π : E ⟶ sch.obj X} (L : Loc π) (R : Type) [CommRing R]
    (F : Shv R) : Eqv R π F := by
  have hi : IsIso (sch.map (𝟙 X)) := inferInstance
  have e : pullback.fst π (sch.map (𝟙 X)) ≫ π = pullback.snd π (sch.map (𝟙 X)) ≫ sch.map (𝟙 X) := pullback.condition
  have h1 : Eqv R (pullback.fst π (sch.map (𝟙 X)) ≫ π) F := by
    rw [e]; exact eqv_comp (eqv_of_loc a1 L R _ F) (eqv_iso _ F)
  have e' : π = inv (pullback.fst π (sch.map (𝟙 X))) ≫ pullback.fst π (sch.map (𝟙 X)) ≫ π :=
    (IsIso.inv_hom_id_assoc _ _).symm
  rw [e']
  exact eqv_comp (eqv_iso _ F) h1

theorem fgt_nat (q : ℕ) {P' P : Arrow Spc} (φ : P' ⟶ P) (n i : ℤ) (x : Hs q P n i) :
    Hs.fgt q P' n i (Hs.pull q φ n i x) = pull _ φ.right _ _ (Hs.fgt q P n i x) := by
  have e : dbl.inl P' ≫ dbl.map φ = φ.right ≫ dbl.inl P := pushout.inl_desc _ _ _
  change pull _ (dbl.inl P') _ n (pull _ (dbl.map φ) _ n x.1) = pull _ φ.right _ n (pull _ (dbl.inl P) _ n x.1)
  rw [← pull_comp, ← pull_comp, e]

theorem hom_nat (q : ℕ) {P' P : Arrow Spc} (φ : P' ⟶ P) (n i : ℤ) (x : Ht q P.right n i) :
    pull _ P'.hom (tw q i) n (pull _ φ.right _ _ x) = pull _ φ.left _ _ (pull _ P.hom _ n x) := by
  rw [← pull_comp, ← pull_comp, Arrow.w φ]

theorem LeafLocExc_of (bd : LeafBd) : LeafLocExc := by
  intro a1 q X U E π L
  obtain ⟨δ, ex, nat, -⟩ := bd
  have hm : Mono (opn U).hom := mono_sch_open U
  have hm' : Mono (abv U π).hom := by
    change Mono (pullback.fst π (sch.map U.ι)); have := mono_sch_open U; infer_instance
  have eR : ∀ i n, Function.Bijective (pull _ (abvMap U π).right (tw q i) n) := fun i =>
    eqv_base a1 L (ZMod q) (tw q i)
  have eL : ∀ i n, Function.Bijective (pull _ (abvMap U π).left (tw q i) n) := fun i =>
    eqv_of_loc a1 L (ZMod q) U.ι (tw q i)
  intro n i
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by ring⟩
  exact five_bij (pull _ (opn U).hom (tw q i) m) (δ q (opn U) m i) (Hs.fgt q (opn U) (m + 1) i)
    (pull _ (opn U).hom (tw q i) (m + 1))
    (pull _ (abv U π).hom (tw q i) m) (δ q (abv U π) m i) (Hs.fgt q (abv U π) (m + 1) i)
    (pull _ (abv U π).hom (tw q i) (m + 1))
    (pull _ (abvMap U π).right _ _) (pull _ (abvMap U π).left _ _) (Hs.pull q (abvMap U π) (m + 1) i)
    (pull _ (abvMap U π).right _ _) (pull _ (abvMap U π).left _ _)
    (ex q _ hm m i).2.1 (ex q _ hm m i).2.2 (ex q _ hm (m + 1) i).1
    (ex q _ hm' m i).2.1 (ex q _ hm' m i).2.2 (ex q _ hm' (m + 1) i).1
    (hom_nat q _ m i) (fun x => (nat q _ _ (abvMap U π) hm' hm m i x).symm) (fgt_nat q _ (m + 1) i)
    (hom_nat q _ (m + 1) i)
    (eR i m).2 (eL i m) (eR i (m + 1)) (eL i (m + 1)).1

end LateralTheory.CohomologicalPurity.TubeCut
