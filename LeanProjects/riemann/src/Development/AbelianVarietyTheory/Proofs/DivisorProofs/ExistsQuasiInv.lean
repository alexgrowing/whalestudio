import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsTjCorrDiagModel

noncomputable section

namespace GlobalTheory.UPel.HT.ES

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT

def IsQuasiInv {Y : Scheme.{0}} {A B : Over Y} [GrpObj A] [GrpObj B] (k : ℕ) (ψ : A ⟶ B) (ψ' : B ⟶ A) : Prop :=
  IsMonHom ψ ∧ IsMonHom ψ' ∧ ψ ≫ ψ' = (𝟙 A) ^ k ∧ ψ' ≫ ψ = (𝟙 B) ^ k

theorem IsQuasiInv.id {Y : Scheme.{0}} (A : Over Y) [GrpObj A] : IsQuasiInv 1 (𝟙 A) (𝟙 A) :=
  ⟨inferInstance, inferInstance, by rw [pow_one, Category.comp_id], by rw [pow_one, Category.comp_id]⟩

def IsAxesTriv {Y : Scheme.{0}} (B : Over Y) [GrpObj B] [IsCommMonObj B] (Q : LB (G2 B).left) : Prop :=
  Q.IsLB ∧ (∃ t : (Q.pull (lift (1 : B ⟶ B) (𝟙 B)).left).Gen, t.IsGen) ∧
    ∃ t : (Q.pull (lift (𝟙 B) (1 : B ⟶ B)).left).Gen, t.IsGen

variable {p : ℕ} [Fact p.Prime] {D : Datum p} {R : Type} [CommRing R] {b : Base D R} {N : ℕ} {Y : Scheme.{0}}
  {s : Y ⟶ Sp R}

theorem isAxesTriv_obj (o : Obj b N s) : IsAxesTriv o.A o.P := ⟨o.isLB, o.rig₁, o.rig₂⟩

def KerStableAt (o : Obj b N s) {B : Over Y} [GrpObj B] (ψ : o.A ⟶ B) {Tb : Scheme.{0}} (t : Tb ⟶ Y) : Prop :=
  ∀ (T : Over Y) (σ : T.left ⟶ Tb), σ ≫ t = T.hom → ∀ g : T ⟶ o.A, g ≫ ψ = 1 →
    ∀ a : D.O, g ≫ o.act.act a ≫ ψ = 1

def PullPolTriv (o : Obj b N s) {B : Over Y} (ψ' : B ⟶ o.A) {T : Over Y} (x : T ⟶ B) : Prop :=
  ∃ τ : (o.P.pull (lift (fst B T ≫ ψ') (snd B T ≫ x ≫ ψ')).left).Gen, τ.IsGen

def PolKerAt (o : Obj b N s) {B : Over Y} [GrpObj B] (ψ' : B ⟶ o.A) (c : ℕ) {Tb : Scheme.{0}} (t : Tb ⟶ Y) : Prop :=
  ∀ (T : Over Y) (σ : T.left ⟶ Tb), σ ≫ t = T.hom → ∀ x : T ⟶ B, x ^ (c ^ 3) = 1 →
    (PullPolTriv o ψ' x ↔ x ^ c = 1)

def TjAt (r : ℤ) (w : Ideal (𝓞 D.F)) (j : ℕ) (o : Obj b N s) {B : Over Y} [GrpObj B] (ψ : o.A ⟶ B)
    {Tb : Scheme.{0}} (t : Tb ⟶ Y) : Prop :=
  ∀ (k : Type) [Field k] [IsAlgClosed k] [CharZero k] (x : Sp k ⟶ Y), (∃ σ : Sp k ⟶ Tb, σ ≫ t = x) →
    (∀ g : Over.mk x ⟶ o.A, g ≫ ψ = 1 → (∃ e : ℕ, KilledBy o (uIdeal D r ^ e) g) → KilledBy o w g) ∧
    Nat.card {g : Over.mk x ⟶ o.A // g ≫ ψ = 1 ∧ KilledBy o w g} = Ideal.absNorm w ^ (D.m * j)

theorem tjAt_id_iff (r : ℤ) (w : Ideal (𝓞 D.F)) (j : ℕ) (o o' : Obj b N s) (ψ : o.A ⟶ o'.A) :
    TjAt r w j o ψ (𝟙 Y) ↔ IsTj r w j o o' ψ :=
  ⟨fun h k _ _ _ x => h k x ⟨x, Category.comp_id x⟩, fun h k _ _ _ x _ => h k x⟩

theorem IsPIsog.kerStableAt {c : ℕ} {o o' : Obj b N s} {ψ : o.A ⟶ o'.A} (h : IsPIsog c o o' ψ)
    {Tb : Scheme.{0}} (t : Tb ⟶ Y) : KerStableAt o ψ t := by
  intro T _ _ g hg a
  haveI := o'.act.hom a
  rw [h.2.2.1, ← Category.assoc, hg, one_comp]

theorem IsPIsog.exists_quasiInv {c : ℕ} {o o' : Obj b N s} {ψ : o.A ⟶ o'.A} (h : IsPIsog c o o' ψ) :
    ∃ ψ' : o'.A ⟶ o.A, IsQuasiInv c ψ ψ' := by
  obtain ⟨-, h1, -, -, -, ψ', h2, h3, h4⟩ := h
  exact ⟨ψ', h1, h2, h3, h4⟩

end GlobalTheory.UPel.HT.ES
