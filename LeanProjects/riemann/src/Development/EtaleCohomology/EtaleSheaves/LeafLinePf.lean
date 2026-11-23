import Development.EtaleCohomology.EtaleSheaves.InstCommRingR

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.E.LeafLinePf

theorem det_mulVec_one (A : Type) [CommRing A] (g : GL (Fin 1) A) :
    (g : Matrix (Fin 1) (Fin 1) A).mulVec (fun _ => 1) = ((Matrix.GeneralLinearGroup.det g : Aˣ) : A) • (fun _ => (1 : A)) := by
  funext i
  obtain rfl : i = 0 := Subsingleton.elim _ _
  simp [Matrix.mulVec, dotProduct, Matrix.det_unique]

def e1 (A : Type) [CommRing A] : Um 1 A := ⟨fun _ => 1, by
  rw [Set.range_const]; exact Ideal.span_singleton_one⟩

def secF (A : Type) [CommRing A] : SingleObj (GL (Fin 1) A) ⥤ Um 1 A where
  obj _ := e1 A
  map g := ⟨(g, Matrix.GeneralLinearGroup.det g), det_mulVec_one A g⟩
  map_id _ := Subtype.ext (Prod.ext rfl (map_one _))
  map_comp f g := Subtype.ext (Prod.ext rfl (map_mul _ _ _))

theorem eqToHom_val {A : Type} [CommRing A] {v w : Um 1 A} (h : v = w) : (eqToHom h).1 = 1 := by
  cases h; rfl

theorem comp_val {A : Type} [CommRing A] {u v w : Um 1 A} (a : u ⟶ v) (b : v ⟶ w) : (a ≫ b).1 = b.1 * a.1 := rfl

theorem det_map {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) (g : GL (Fin 1) A) :
    ((Matrix.GeneralLinearGroup.det (Matrix.GeneralLinearGroup.map f g) : Bˣ) : B) = f ((Matrix.GeneralLinearGroup.det g : Aˣ) : A) := by
  simp only [Matrix.GeneralLinearGroup.val_det_apply, Matrix.GeneralLinearGroup.map_apply, RingHom.map_det]
  rfl

def secNat : glCat 1 ⟶ pglCat 1 where
  app A := (secF A).toCatHom
  naturality A B f := by
    apply Cat.Hom.ext
    refine CategoryTheory.Functor.ext (fun _ => Subtype.ext (funext fun _ => (map_one f.hom).symm)) (fun _ _ g => ?_)
    apply Subtype.ext
    erw [comp_val, comp_val, eqToHom_val, eqToHom_val, one_mul, mul_one]
    refine Prod.ext rfl ?_
    ext
    change ((Matrix.GeneralLinearGroup.det (Matrix.GeneralLinearGroup.map f.hom (show GL (Fin 1) A from g)) : (B : Type)ˣ) : (B : Type)) =
      f.hom ((Matrix.GeneralLinearGroup.det (show GL (Fin 1) A from g) : (A : Type)ˣ) : (A : Type))
    exact det_map f.hom _

theorem ofCatMap_comp {C D F : CommRingCat.{0} ⥤ Cat.{0,0}} (α : C ⟶ D) (β : D ⟶ F) :
    ofCatMap α ≫ ofCatMap β = ofCatMap (α ≫ β) := rfl

theorem ofCatMap_id (C : CommRingCat.{0} ⥤ Cat.{0,0}) : ofCatMap (𝟙 C) = 𝟙 _ := rfl

def sec : ofCat (glCat 1) ⟶ PGL 1 := ofCatMap secNat

theorem sec_pr : sec ≫ PGL.pr 1 = 𝟙 (ofCat (glCat 1)) := rfl

theorem single_eqToHom {M : Type} [Monoid M] {x y : SingleObj M} (h : x = y) : (eqToHom h : x ⟶ y) = (1 : M) := by
  cases h; rfl

theorem sec_line : sec ≫ PGL.line 1 = 𝟙 (ofCat (glCat 1)) := by
  rw [sec, PGL.line]
  erw [ofCatMap_comp]
  rw [← ofCatMap_id]
  congr 1
  apply NatTrans.ext
  funext A
  apply Cat.Hom.ext
  refine CategoryTheory.Functor.ext (fun _ => rfl) (fun _ _ g => ?_)
  erw [single_eqToHom]
  change _ = ((1 : GL (Fin 1) A) * (id g : GL (Fin 1) A)) * 1
  rw [one_mul, mul_one]
  change Matrix.GeneralLinearGroup.scalar (Fin 1) (Matrix.GeneralLinearGroup.det (id g : GL (Fin 1) A)) = (id g : GL (Fin 1) A)
  ext i j
  obtain rfl : i = 0 := Subsingleton.elim _ _
  obtain rfl : j = 0 := Subsingleton.elim _ _
  simp [Matrix.GeneralLinearGroup.val_det_apply, Matrix.det_unique]

theorem pull_cast {q : ℕ} {E E' : Spc} (f : E ⟶ E') {n i n' i' : ℤ} (hn : n = n') (hi : i = i') (x : Ht q E' n i) :
    pull _ f _ _ (x.cast hn hi) = Ht.cast (q := q) (E := E) hn hi (pull _ f _ _ x) := by
  subst hn; subst hi; rfl

end LateralTheory.E.LeafLinePf

namespace LateralTheory.E.D2
open LateralTheory.E.LeafLinePf

theorem LeafLine_of (hA : LeafA6nat) : LeafLine := by
  intro q _ P E h L c hc
  obtain ⟨h0, -, heq⟩ := hc
  have hw : 𝟙 E ≫ L = (L ≫ sec) ≫ PGL.pr 1 := by
    rw [Category.assoc, sec_pr, Category.id_comp, Category.comp_id]
  let σ : E ⟶ PB L := pullback.lift (𝟙 E) (L ≫ sec) hw
  have hpr : σ ≫ PB.pr L = 𝟙 E := pullback.lift_fst _ _ _
  have hline : σ ≫ PB.line L = L := by
    rw [PB.line, ← Category.assoc]
    erw [pullback.lift_snd]
    rw [Category.assoc, sec_line, Category.comp_id]
  have h' : Inv q (PB L) := inv_of (PB.pr L) h
  have hm : ∀ j, P.map σ h h' (P.map (PB.pr L) h' h (P.ι h j (c j))) = P.ι h j (c j) := by
    intro j
    rw [P.map_ι, P.map_ι, ← pull_comp, hpr, pull_id]
  have hx : P.map σ h h' (P.deg1 h' (c1 q (PB.line L))) = P.deg1 h (c1 q L) := by
    rw [Collected.deg1, P.map_ι, pull_cast, (hA q).2.2.1 σ (PB.line L) h', hline]
  have := congrArg (P.map σ h h') heq
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, map_add, map_mul, map_pow, map_zero, zero_add, hm, hx,
    map_one, h0] at this
  simp only [one_mul, Nat.sub_zero, Nat.sub_self, pow_one, pow_zero, mul_one] at this
  linear_combination this

end LateralTheory.E.D2
