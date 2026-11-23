import Development.EtaleCohomology.CohomologicalPurity.LeafIndExc

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.CohomologicalPurity.Thom

def Vec (N k : ℕ) (U : Scheme.{0}) : Type :=
  {v : Fin N → Γ(U, ⊤) // ∀ p : U, ∃ i : Fin N, k ≤ i.val ∧ p ∈ U.basicOpen (v i)}

instance (N k : ℕ) (U : Scheme.{0}) : SmallCategory (Vec N k U) where
  Hom v w := {u : (Γ(U, ⊤))ˣ // ∀ i, v.1 i = (u : Γ(U, ⊤)) * w.1 i}
  id v := ⟨1, by simp⟩
  comp f g := ⟨g.1 * f.1, fun i => by rw [f.2 i, g.2 i, Units.val_mul]; ring⟩
  id_comp f := Subtype.ext (mul_one _)
  comp_id f := Subtype.ext (one_mul _)
  assoc f g h := Subtype.ext (mul_assoc _ _ _).symm

def Vec.map (N k : ℕ) {V U : Scheme.{0}} (f : V ⟶ U) : Vec N k U ⥤ Vec N k V where
  obj v := ⟨fun i => f.appTop.hom (v.1 i), fun p => by
    obtain ⟨i, hi, hp⟩ := v.2 (f p)
    exact ⟨i, hi, by rw [← Scheme.preimage_basicOpen_top]; exact hp⟩⟩
  map {v w} u := ⟨Units.map (f.appTop.hom : Γ(U, ⊤) →* Γ(V, ⊤)) u.1, fun i => by
    change f.appTop.hom (v.1 i) = f.appTop.hom _ * f.appTop.hom _
    rw [u.2 i, map_mul]⟩
  map_id v := Subtype.ext (map_one (Units.map (f.appTop.hom : Γ(U, ⊤) →* Γ(V, ⊤))))
  map_comp p q := Subtype.ext (map_mul (Units.map (f.appTop.hom : Γ(U, ⊤) →* Γ(V, ⊤))) _ _)

def vecCat (N k : ℕ) : Scheme.{0}ᵒᵖ ⥤ Cat.{0,0} where
  obj U := Cat.of (Vec N k U.unop)
  map f := (Vec.map N k f.unop).toCatHom
  map_id _ := rfl
  map_comp _ _ := rfl

def nerveMap {C D : Scheme.{0}ᵒᵖ ⥤ Cat.{0,0}} (α : C ⟶ D) :
    ((C ⋙ nerveFunctor).flip : Spc) ⟶ ((D ⋙ nerveFunctor).flip : Spc) :=
  (flipFunctor _ _ _).map (Functor.whiskerRight α nerveFunctor)

def Pj (N k : ℕ) : Spc := (vecCat N k ⋙ nerveFunctor).flip

def Vec.incl (N : ℕ) (U : Scheme.{0}) : Vec N 1 U ⥤ Vec N 0 U where
  obj v := ⟨v.1, fun p => (v.2 p).imp fun _ h => ⟨Nat.zero_le _, h.2⟩⟩
  map u := u

def Vec.tail (d : ℕ) (U : Scheme.{0}) : Vec (d + 1) 1 U ⥤ Vec d 0 U where
  obj v := ⟨fun i => v.1 i.succ, fun p => by
    obtain ⟨i, hi, hp⟩ := v.2 p
    obtain ⟨j, rfl⟩ := Fin.exists_succ_eq.2 (show i ≠ 0 by rintro rfl; simp at hi)
    exact ⟨j, Nat.zero_le _, hp⟩⟩
  map u := ⟨u.1, fun i => u.2 i.succ⟩

def Vec.line (N k : ℕ) (U : Scheme.{0}) : Vec N k U ⥤ SingleObj (GL (Fin 1) Γ(U, ⊤)) where
  obj _ := SingleObj.star _
  map u := Matrix.GeneralLinearGroup.scalar (Fin 1) u.1
  map_id _ := map_one (Matrix.GeneralLinearGroup.scalar (Fin 1))
  map_comp _ _ := map_mul (Matrix.GeneralLinearGroup.scalar (Fin 1)) _ _

def Pj.incl (N : ℕ) : Pj N 1 ⟶ Pj N 0 :=
  nerveMap { app := fun U => (Vec.incl N U.unop).toCatHom, naturality := fun _ _ _ => rfl }

def Pj.tail (d : ℕ) : Pj (d + 1) 1 ⟶ Pj d 0 :=
  nerveMap { app := fun U => (Vec.tail d U.unop).toCatHom, naturality := fun _ _ _ => rfl }

def Pj.line (N k : ℕ) : Pj N k ⟶ ofCat (glCat 1) :=
  nerveMap (D := Scheme.Γ ⋙ glCat 1)
    { app := fun U => (Vec.line N k U.unop).toCatHom
      naturality := fun A B f => by
        apply Cat.Hom.ext
        refine CategoryTheory.Functor.hext (fun _ => rfl) (fun v w p => heq_of_eq ?_)
        change Matrix.GeneralLinearGroup.scalar (Fin 1) (Units.map (f.unop.appTop.hom : _ →* _) p.1) =
          Matrix.GeneralLinearGroup.map f.unop.appTop.hom (Matrix.GeneralLinearGroup.scalar (Fin 1) p.1)
        ext i j
        obtain rfl : i = j := Subsingleton.elim _ _
        simp }

theorem Pj.incl_line (N : ℕ) : Pj.incl N ≫ Pj.line N 0 = Pj.line N 1 := rfl
theorem Pj.tail_line (d : ℕ) : Pj.tail d ≫ Pj.line d 0 = Pj.line (d + 1) 1 := rfl

def Pj.pt {N k : ℕ} {X : Scheme.{0}} (v : Vec N k X) : sch.obj X ⟶ Pj N k where
  app n :=
    { app := fun U => TypeCat.ofHom fun (f : U.unop ⟶ X) =>
        (Functor.const (Fin (n.unop.len + 1))).obj ((Vec.map N k f).obj v)
      naturality := fun U U' g => by
        ext f
        refine CategoryTheory.Functor.hext (fun _ => rfl) (fun _ _ _ => heq_of_eq ?_)
        exact ((Vec.map N k g.unop).map_id ((Vec.map N k f).obj v)).symm }
  naturality n m f := rfl

def vec1 {d : ℕ} {A : Type} [CommRing A] (x : Fin d → A) : Vec (d + 1) 0 (Spec (CommRingCat.of A)) :=
  ⟨fun i => (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom ((Fin.cons 1 x : Fin (d + 1) → A) i), fun p =>
    ⟨0, le_rfl, by simp⟩⟩

abbrev PR (N k : ℕ) (R : Type) [CommRing R] : Spc := Pj N k ⨯ sp R

def hyp (q N k : ℕ) (R : Type) [CommRing R] : Ht q (PR N k R) 2 1 := c1 q (prod.fst ≫ Pj.line N k)

def poly (q N k : ℕ) (R : Type) [CommRing R] (m : ℕ) (n i : ℤ)
    (a : ∀ j : Fin m, Ht q (sp R) (n - 2 * (j : ℕ)) (i - (j : ℕ))) : Ht q (PR N k R) n i :=
  ∑ j : Fin m, ((cup q (pull _ prod.snd _ _ (a j)) (cpow q (hyp q N k R) j)).cast (by ring) (by ring) : Ht q _ n i)

def pr (d : ℕ) (R : Type) [CommRing R] : Arrow Spc :=
  Arrow.mk (prod.map (Pj.incl (d + 1)) (𝟙 _) : PR (d + 1) 1 R ⟶ PR (d + 1) 0 R)

def prMap (d : ℕ) {A B : Type} [CommRing A] [CommRing B] (φ : A →+* B) : pr d B ⟶ pr d A :=
  Arrow.homMk (prod.map (𝟙 _) (spMap φ)) (prod.map (𝟙 _) (spMap φ)) (by simp [pr])

def chart {d : ℕ} {A : Type} [CommRing A] (x : Fin d → A) : sp A ⟶ PR (d + 1) 0 A := prod.lift (Pj.pt (vec1 x)) (𝟙 _)

def IsTau (q d : ℕ) (R : Type) [CommRing R] (τ : Hs q (pr d R) (2 * d) d) : Prop :=
  ∃ a, Hs.fgt q (pr d R) _ _ τ = cpow q (hyp q (d + 1) 0 R) d + poly q (d + 1) 0 R d (2 * d) d a

end LateralTheory.CohomologicalPurity.Thom
