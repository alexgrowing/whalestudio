import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.Subsingleton
import Development.AbelianVarietyTheory.Definitions.Divisors.ToRepFam
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.DrinfeldLevel

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped NumberField

namespace GlobalTheory.DrinLev.HT

open GlobalTheory.UPel.HT GlobalTheory.IwLevel

variable {p : ℕ} [Fact p.Prime]

abbrev powO (D : Datum p) (w : Ideal (𝓞 D.F)) (m : ℕ) : Ideal D.O := (w ^ m).map (algebraMap (𝓞 D.F) D.O)

def IsRankOneIdem (D : Datum p) (w : Ideal (𝓞 D.F)) (m : ℕ) (e : D.O) : Prop :=
  e * e - e ∈ powO D w m ∧ (∀ x : D.O, ∃ c : 𝓞 D.F, e * x * e - algebraMap (𝓞 D.F) D.O c * e ∈ powO D w m) ∧
    e ∉ powO D w 1

variable {D : Datum p} {R : Type} [CommRing R] {b : Base D R} {N : ℕ} {S S' : Scheme.{0}}

def IsEpsTors {s : S ⟶ Sp R} (o : Obj b N s) (w : Ideal (𝓞 D.F)) (m : ℕ) (e : D.O) {T : Over S} (x : T ⟶ o.A) :
    Prop :=
  KilledBy (htAct o) (powO D w m) x ∧ x ≫ o.act.act e = x

structure SubRep (A : Over S) (P : ∀ {T : Over S}, (T ⟶ A) → Prop) where

  Z : Over S

  incl : Z ⟶ A
  mono : Mono incl
  pts : ∀ (T : Over S) (x : T ⟶ A), P x ↔ ∃ y, y ≫ incl = x

def SubRep.unit (A : Over S) [GrpObj A] : SubRep A (fun x => x = 1) where
  Z := 𝟙_ (Over S)
  incl := 1
  mono := ⟨fun g h _ => toUnit_unique g h⟩
  pts T x := ⟨fun h => ⟨toUnit T, by rw [MonObj.comp_one, h]⟩, fun ⟨y, hy⟩ => hy ▸ MonObj.comp_one y⟩

structure HTLevel {s : S ⟶ Sp R} (o : Obj b N s) (w : Ideal (𝓞 D.F)) (m : ℕ) (e : D.O) where

  α : (Fin D.n → 𝓞 D.F ⧸ w ^ m) → (𝟙_ (Over S) ⟶ o.A)
  map_add : ∀ x y, α (x + y) = α x * α y
  map_smul : ∀ (c : 𝓞 D.F) x, α (c • x) = α x ≫ o.act.act (algebraMap (𝓞 D.F) D.O c)
  full : ∃ (G : SubRep o.A (IsEpsTors o w m e)) (β : (Fin D.n → 𝓞 D.F ⧸ w ^ m) → (𝟙_ (Over S) ⟶ G.Z)),
    (∀ x, β x ≫ G.incl = α x) ∧ IsFullSet G.Z β

structure ObjLev (b : Base D R) (N : ℕ) (w : Ideal (𝓞 D.F)) (m : ℕ) (e : D.O) (s : S ⟶ Sp R) where

  obj : Obj b N s

  lev : HTLevel obj w m e

def ObjLevMap {w : Ideal (𝓞 D.F)} {m : ℕ} {e : D.O} {s' : S' ⟶ Sp R} {s : S ⟶ Sp R} (o' : ObjLev b N w m e s')
    (o : ObjLev b N w m e s) (f : S' ⟶ S) : Prop :=
  ∃ φ : ObjMap o'.obj o.obj f, ∀ x, (o'.lev.α x).left ≫ φ.φ = f ≫ (o.lev.α x).left

structure LevRep (b : Base D R) (N : ℕ) (w : Ideal (𝓞 D.F)) (m : ℕ) (e : D.O) where

  X : Scheme.{0}

  s : X ⟶ Sp R

  univ : ObjLev b N w m e s
  rep : ∀ (S : Scheme.{0}) (s' : S ⟶ Sp R) (o : ObjLev b N w m e s'),
    ∃! f : S ⟶ X, f ≫ s = s' ∧ ObjLevMap o univ f

namespace LevRep

variable {w : Ideal (𝓞 D.F)} {m : ℕ} {e : D.O}

def forget (M : LevRep b N w m e) (F₀ : RepFam b N) : M.X ⟶ F₀.X :=
  (F₀.rep M.X M.s M.univ.obj).exists.choose

def Proj (M : LevRep b N w m e) : Prop := IsProjOver M.s

def Regular (M : LevRep b N w m e) : Prop := ∀ x : M.X, IsRegularLocalRing (M.X.presheaf.stalk x)

def FinFlat (M : LevRep b N w m e) (F₀ : RepFam b N) : Prop :=
  IsFinite (M.forget F₀) ∧ Flat (M.forget F₀)

end LevRep

structure LevModel (M₀ : Model b N) (w : Ideal (𝓞 D.F)) (m : ℕ) (e : D.O) extends LevRep b N w m e where
  proj : toLevRep.Proj
  regular : toLevRep.Regular
  finFlat : toLevRep.FinFlat M₀.toRepFam

section Basic₂

example (D : Datum p) (w : Ideal (𝓞 D.F)) (e : D.O) (he : e ∉ powO D w 1) : IsRankOneIdem D w 0 e := by
  have h : powO D w 0 = ⊤ := by
    rw [powO, pow_zero, Ideal.one_eq_top]
    exact (Ideal.eq_top_iff_one _).2 (by simpa using Ideal.mem_map_of_mem (algebraMap (𝓞 D.F) D.O) (Submodule.mem_top (x := (1 : 𝓞 D.F))))
  refine ⟨?_, fun x => ⟨0, ?_⟩, he⟩ <;> simp [h]

example {s : S ⟶ Sp R} (o : Obj b N s) (w : Ideal (𝓞 D.F)) (m : ℕ) (e : D.O) :
    IsEpsTors o w m e (1 : 𝟙_ (Over S) ⟶ o.A) := by
  have := o.act.hom e
  refine ⟨fun a _ => ?_, ?_⟩
  · have := (htAct o).hom a
    exact MonObj.one_comp _
  · exact MonObj.one_comp _

end Basic₂

end GlobalTheory.DrinLev.HT
