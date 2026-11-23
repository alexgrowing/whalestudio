import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TrivV

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite

namespace GlobalTheory.EtC.PStep
open GlobalTheory.EtC

abbrev P (M : ℕ) (A : Type) [CommRing A] : Spc := pullback (trivV M (sp A)) (PGL.pr M)

abbrev prP (M : ℕ) (A : Type) [CommRing A] : P M A ⟶ sp A := pullback.fst _ _

abbrev lineP (M : ℕ) (A : Type) [CommRing A] : P M A ⟶ ofCat (glCat 1) := pullback.snd _ _ ≫ PGL.line M

theorem comp_trivV (M : ℕ) {E E' : Spc} (f : E ⟶ E') : f ≫ trivV M E' = trivV M E := by
  ext n U x
  rfl

def TU (M : ℕ) (p : ∀ {B : Type} [CommRing B], (Fin M → B) → Prop) (B : Type) [CommRing B] : Type :=
  {v : Um M B // p v.1}

theorem TU.comp_aux {M : ℕ} {B : Type} [CommRing B] (x y z : Fin M → B) (u u' : Bˣ) (h1 : x = (u : B) • y)
    (h2 : y = (u' : B) • z) : x = ((u' * u : Bˣ) : B) • z := by
  subst h1 h2
  rw [smul_smul, Units.val_mul, mul_comm]

instance (M : ℕ) (p : ∀ {B : Type} [CommRing B], (Fin M → B) → Prop) (B : Type) [CommRing B] :
    SmallCategory (TU M p B) where
  Hom v w := {u : Bˣ // v.1.1 = (u : B) • w.1.1}
  id v := ⟨1, by simp⟩
  comp f g := ⟨g.1 * f.1, TU.comp_aux _ _ _ _ _ f.2 g.2⟩
  id_comp f := Subtype.ext (mul_one _)
  comp_id f := Subtype.ext (one_mul _)
  assoc f g h := Subtype.ext (mul_assoc _ _ _).symm

def TU.map (M : ℕ) {p : ∀ {B : Type} [CommRing B], (Fin M → B) → Prop}
    (hp : ∀ {B C : Type} [CommRing B] [CommRing C] (f : B →+* C) (v : Fin M → B), p v → p (f ∘ v))
    {B C : Type} [CommRing B] [CommRing C] (f : B →+* C) : TU M p B ⥤ TU M p C where
  obj v := ⟨(Um.map M f).obj v.1, hp f _ v.2⟩
  map {v w} u := ⟨Units.map (f : B →* C) u.1, by
    funext i
    have h := congrArg f (congrFun u.2 i)
    simp only [Pi.smul_apply, smul_eq_mul, map_mul] at h
    exact h⟩
  map_id v := Subtype.ext (map_one (Units.map (f : B →* C)))
  map_comp u u' := Subtype.ext (map_mul (Units.map (f : B →* C)) _ _)

def tuCat (M : ℕ) (p : ∀ {B : Type} [CommRing B], (Fin M → B) → Prop)
    (hp : ∀ {B C : Type} [CommRing B] [CommRing C] (f : B →+* C) (v : Fin M → B), p v → p (f ∘ v)) :
    CommRingCat.{0} ⥤ Cat.{0,0} where
  obj B := Cat.of (TU M p B)
  map f := (TU.map M hp f.hom).toCatHom
  map_id B := rfl
  map_comp f g := rfl

def TU.toUm (M : ℕ) (p : ∀ {B : Type} [CommRing B], (Fin M → B) → Prop) (B : Type) [CommRing B] :
    TU M p B ⥤ Um M B where
  obj v := v.1
  map {v w} u := ⟨(1, u.1), by simpa using u.2⟩
  map_id v := rfl
  map_comp u u' := Subtype.ext (Prod.ext (mul_one 1).symm rfl)

def tuToPgl (M : ℕ) (p : ∀ {B : Type} [CommRing B], (Fin M → B) → Prop)
    (hp : ∀ {B C : Type} [CommRing B] [CommRing C] (f : B →+* C) (v : Fin M → B), p v → p (f ∘ v)) :
    tuCat M p hp ⟶ pglCat M where
  app B := (TU.toUm M p B).toCatHom
  naturality B C f := by
    apply Cat.Hom.ext
    refine CategoryTheory.Functor.hext (fun _ => rfl) (fun v w u => heq_of_eq ?_)
    exact Subtype.ext (Prod.ext (map_one (Matrix.GeneralLinearGroup.map f.hom)).symm rfl)

theorem tuToPgl_pr (M : ℕ) (p : ∀ {B : Type} [CommRing B], (Fin M → B) → Prop)
    (hp : ∀ {B C : Type} [CommRing B] [CommRing C] (f : B →+* C) (v : Fin M → B), p v → p (f ∘ v)) :
    ofCatMap (tuToPgl M p hp) ≫ PGL.pr M = trivV M (ofCat (tuCat M p hp)) := by
  ext n U x
  exact CategoryTheory.Functor.hext (fun _ => rfl) (fun _ _ _ => HEq.rfl)

def toP {M : ℕ} {C : CommRingCat.{0} ⥤ Cat.{0,0}} (ρ : C ⟶ pglCat M) (hρ : ofCatMap ρ ≫ PGL.pr M = trivV M (ofCat C))
    (A : Type) [CommRing A] : ofCat C ⨯ sp A ⟶ P M A :=
  pullback.lift prod.snd (prod.fst ≫ ofCatMap ρ) (by
    rw [comp_trivV]
    exact ((comp_trivV M (prod.fst : ofCat C ⨯ sp A ⟶ _)).symm.trans (congrArg _ hρ.symm)).trans (Category.assoc _ _ _).symm)

def lastU (N : ℕ) : ∀ {B : Type} [CommRing B], (Fin (N + 1) → B) → Prop := fun v => IsUnit (v (Fin.last N))

theorem lastU_map (N : ℕ) {B C : Type} [CommRing B] [CommRing C] (f : B →+* C) (v : Fin (N + 1) → B) :
    lastU N v → lastU N (f ∘ v) := fun h => h.map f

def headU (N : ℕ) : ∀ {B : Type} [CommRing B], (Fin (N + 1) → B) → Prop :=
  fun v => Ideal.span (Set.range fun k : Fin N => v k.castSucc) = ⊤

theorem headU_map (N : ℕ) {B C : Type} [CommRing B] [CommRing C] (f : B →+* C) (v : Fin (N + 1) → B) :
    headU N v → headU N (f ∘ v) := by
  intro h
  change Ideal.span (Set.range fun k : Fin N => f (v k.castSucc)) = ⊤
  rw [show (fun k : Fin N => f (v k.castSucc)) = f ∘ (fun k : Fin N => v k.castSucc) from rfl, Set.range_comp,
    ← Ideal.map_span, h, Ideal.map_top]

def trivialCondition (M : ℕ) : ∀ {B : Type} [CommRing B], (Fin M → B) → Prop := fun _ => True

theorem allU_map (M : ℕ) {B C : Type} [CommRing B] [CommRing C] (f : B →+* C) (v : Fin M → B) :
    trivialCondition M v → trivialCondition M (f ∘ v) := fun _ => trivial

abbrev W1 (N : ℕ) (A : Type) [CommRing A] : Spc := ofCat (tuCat (N + 1) (lastU N) (lastU_map N)) ⨯ sp A

abbrev W2 (N : ℕ) (A : Type) [CommRing A] : Spc := ofCat (tuCat (N + 1) (headU N) (headU_map N)) ⨯ sp A

def w1 (N : ℕ) (A : Type) [CommRing A] : W1 N A ⟶ P (N + 1) A := toP (tuToPgl _ _ _) (tuToPgl_pr _ _ _) A

def w2 (N : ℕ) (A : Type) [CommRing A] : W2 N A ⟶ P (N + 1) A := toP (tuToPgl _ _ _) (tuToPgl_pr _ _ _) A

def headNat (N : ℕ) : tuCat (N + 1) (headU N) (headU_map N) ⟶ tuCat N (trivialCondition N) (allU_map N) where
  app B := Functor.toCatHom
    { obj := fun v => ⟨⟨fun k => v.1.1 k.castSucc, v.2⟩, trivial⟩
      map := fun {v w} u => ⟨u.1, funext fun k => congrFun u.2 k.castSucc⟩
      map_id := fun _ => rfl
      map_comp := fun _ _ => rfl }
  naturality _ _ _ := rfl

theorem headNat_pr (N : ℕ) : ofCatMap (headNat N ≫ tuToPgl N (trivialCondition N) (allU_map N)) ≫ PGL.pr N =
    trivV N (ofCat (tuCat (N + 1) (headU N) (headU_map N))) := by
  ext n U x
  exact CategoryTheory.Functor.hext (fun _ => rfl) (fun _ _ _ => HEq.rfl)

def r (N : ℕ) (A : Type) [CommRing A] : W2 N A ⟶ P N A := toP _ (headNat_pr N) A

abbrev twoSubspaceIntersection (N : ℕ) (A : Type) [CommRing A] : Spc := pullback (w1 N A) (w2 N A)

def p12 (N : ℕ) (A : Type) [CommRing A] : twoSubspaceIntersection N A ⟶ sp A := pullback.fst _ _ ≫ w1 N A ≫ prP (N + 1) A

abbrev xi (q M : ℕ) (A : Type) [CommRing A] : Ht q (P M A) 2 1 := c1 q (lineP M A)

end GlobalTheory.EtC.PStep

end
