import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntEmbCoe
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MonoPullbackOfIsOpenImmersion

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.VB GlobalTheory.LieVB GlobalTheory.IndefiniteRowSideFullHecke.FrobeniusTwistEigen GlobalTheory.CurveRootGeometry

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.TwoSeq

section General

variable {O : Type} [CommRing O] {X T T' S : Scheme.{0}} {A B A' B' : X.Modules}

def sqIso {b : S ⟶ T} {a : T ⟶ X} {c : S ⟶ T'} {a' : T' ⟶ X} (w : b ≫ a = c ≫ a') :
    Scheme.Modules.pullback a ⋙ Scheme.Modules.pullback b ≅ Scheme.Modules.pullback a' ⋙ Scheme.Modules.pullback c :=
  Scheme.Modules.pullbackComp b a ≪≫ Scheme.Modules.pullbackCongr w ≪≫ (Scheme.Modules.pullbackComp c a').symm

structure Datum (α : O →+* End A) (β : O →+* End B) (α' : O →+* End A') (β' : O →+* End B') (r : ℕ) where

  D : X.Modules

  ρ : O →+* End D

  a : A ⟶ D

  b : D ⟶ B

  u : A' ⟶ D

  v : D ⟶ B'
  w₁ : a ≫ b = 0
  w₂ : u ≫ v = 0
  isVB : IsVB D r
  exact₁ : (ShortComplex.mk a b w₁).ShortExact
  exact₂ : (ShortComplex.mk u v w₂).ShortExact
  equiv_a : IsEquivariant α ρ a
  equiv_b : IsEquivariant ρ β b
  equiv_u : IsEquivariant α' ρ u
  equiv_v : IsEquivariant ρ β' v

variable (α : O →+* End A) (β : O →+* End B) (α' : O →+* End A') (β' : O →+* End B') (r : ℕ)

abbrev DatumOn (f : T ⟶ X) : Type 1 := Datum (pullAct α f) (pullAct β f) (pullAct α' f) (pullAct β' f) r

variable {α β α' β' r}

def Agree {a : T ⟶ X} {a' : T' ⟶ X} (d : DatumOn α β α' β' r a) (d' : DatumOn α β α' β' r a') {b : S ⟶ T} {c : S ⟶ T'}
    (w : b ≫ a = c ≫ a') (φ : (Scheme.Modules.pullback b).obj d.D ≅ (Scheme.Modules.pullback c).obj d'.D) : Prop :=
  IsEquivariant (pullAct d.ρ b) (pullAct d'.ρ c) φ.hom ∧
    (Scheme.Modules.pullback b).map d.a ≫ φ.hom = (sqIso w).hom.app A ≫ (Scheme.Modules.pullback c).map d'.a ∧
    φ.hom ≫ (Scheme.Modules.pullback c).map d'.b = (Scheme.Modules.pullback b).map d.b ≫ (sqIso w).hom.app B ∧
    (Scheme.Modules.pullback b).map d.u ≫ φ.hom = (sqIso w).hom.app A' ≫ (Scheme.Modules.pullback c).map d'.u ∧
    φ.hom ≫ (Scheme.Modules.pullback c).map d'.v = (Scheme.Modules.pullback b).map d.v ≫ (sqIso w).hom.app B'

def RestrictsTo (d : Datum α β α' β' r) {a : T ⟶ X} (d' : DatumOn α β α' β' r a)
    (e : (Scheme.Modules.pullback a).obj d.D ≅ d'.D) : Prop :=
  IsEquivariant (pullAct d.ρ a) d'.ρ e.hom ∧
    (Scheme.Modules.pullback a).map d.a ≫ e.hom = d'.a ∧ e.hom ≫ d'.b = (Scheme.Modules.pullback a).map d.b ∧
    (Scheme.Modules.pullback a).map d.u ≫ e.hom = d'.u ∧ e.hom ≫ d'.v = (Scheme.Modules.pullback a).map d.v

def biprodAct (α : O →+* End A) (β : O →+* End B) : O →+* End (A ⊞ B) where
  toFun x := biprod.map (act α x) (act β x)
  map_one' := by
    rw [act, act, map_one, map_one]
    exact biprod.hom_ext _ _ (by simp [End.one_def]) (by simp [End.one_def])
  map_mul' x y := by
    rw [act, act, map_mul, map_mul]
    exact biprod.hom_ext _ _ (by simp [End.mul_def]) (by simp [End.mul_def])
  map_zero' := by
    rw [act, act, map_zero, map_zero]
    change (biprod.map (0 : A ⟶ A) (0 : B ⟶ B) : A ⊞ B ⟶ A ⊞ B) = (0 : A ⊞ B ⟶ A ⊞ B)
    exact biprod.hom_ext _ _ (by simp) (by simp)
  map_add' x y := by
    rw [act, act, map_add, map_add]
    change (biprod.map (act α x + act α y) (act β x + act β y) : A ⊞ B ⟶ A ⊞ B) =
      (biprod.map (act α x) (act β x) + biprod.map (act α y) (act β y) : A ⊞ B ⟶ A ⊞ B)
    exact biprod.hom_ext _ _ (by simp) (by simp)

def Datum.split (α : O →+* End A) (β : O →+* End B) {m n : ℕ} (hA : IsVB A m) (hB : IsVB B n) :
    Datum α β β α (m + n) where
  D := A ⊞ B
  ρ := biprodAct α β
  a := biprod.inl
  b := biprod.snd
  u := biprod.inr
  v := biprod.fst
  w₁ := by simp
  w₂ := by simp
  isVB := hA.biprod hB
  exact₁ := (ShortComplex.Splitting.ofHasBinaryBiproduct A B).shortExact
  exact₂ := (ShortComplex.Splitting.mk (S := ShortComplex.mk (biprod.inr : B ⟶ A ⊞ B) biprod.fst (by simp))
    biprod.snd biprod.inl (by simp) (by simp) (by rw [add_comm]; exact biprod.total)).shortExact
  equiv_a x := by simp [act, biprodAct]
  equiv_b x := by simp [act, biprodAct]
  equiv_u x := by simp [act, biprodAct]
  equiv_v x := by simp [act, biprodAct]

example (X : Scheme.{0}) :
    let σ := scalarAct (GlobalTheory.QCoh.freeModule X (Fin 1)) (RingHom.id Γ(X, ⊤))
    Nonempty (Datum σ σ σ σ 2) :=
  ⟨Datum.split _ _ (isVB_freeModule_fin X 1) (isVB_freeModule_fin X 1)⟩

end General

section Dieu

variable {O : Type} [CommRing O] (q : ℕ) [Fact q.Prime] (k : Type) [Field k] [CharP k q] (c : O →+* O) {C : Scheme.{0}}
  [Algebra k Γ(C, ⊤)] {G : Over C} [GrpObj G] [QuasiSeparated G.hom] (i : OAct O G)

abbrev DieuDatum (g : ℕ) : Type 1 :=
  Datum (omegaAct i) ((lieAct i).comp c) (pullAct ((lieAct i).comp c) (frob C q (natCast_eq_zero C q k)))
    (pullAct (omegaAct i) (frob C q (natCast_eq_zero C q k))) (2 * g)

abbrev DieuDatumOn (g : ℕ) {T : Scheme.{0}} (f : T ⟶ C) : Type 1 :=
  DatumOn (omegaAct i) ((lieAct i).comp c) (pullAct ((lieAct i).comp c) (frob C q (natCast_eq_zero C q k)))
    (pullAct (omegaAct i) (frob C q (natCast_eq_zero C q k))) (2 * g) f

theorem hasDieu_iff : HasDieu q k c i ↔ ∃ g, IsVB (omega G) g ∧ Nonempty (DieuDatum q k c i g) :=
  ⟨fun ⟨D, g, ρ, a, b, u, v, w₁, w₂, h, h₁, h₂, h₃, h₄, h₅, h₆, h₇⟩ =>
      ⟨g, h, ⟨⟨D, ρ, a, b, u, v, w₁, w₂, h₁, h₂, h₃, h₄, h₅, h₆, h₇⟩⟩⟩,
    fun ⟨g, h, ⟨d⟩⟩ => ⟨d.D, g, d.ρ, d.a, d.b, d.u, d.v, d.w₁, d.w₂, h, d.isVB, d.exact₁, d.exact₂, d.equiv_a,
      d.equiv_b, d.equiv_u, d.equiv_v⟩⟩

end Dieu

end GlobalTheory.TwoSeq
