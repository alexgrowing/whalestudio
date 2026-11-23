import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.InjectiveOfSmulMemRange
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.EpsilonPairingZeta

set_option autoImplicit false

noncomputable section

open WittVector Ideal CategoryTheory Opposite

namespace GlobalTheory.PDivLat

open GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta

variable {p : ℕ} [Fact p.Prime] {O : Type} [CommRing O] [Fact ¬IsUnit (p : O)]
  [IsAdicComplete (span {(p : O)}) O]

variable (p O) in

def ghost (n : ℕ) (a : Ainf p O) : O :=
  fontaineTheta O p ((WittVector.frobenius : Ainf p O →+* Ainf p O)^[n] a)

set_option autoImplicit false in
open WittVector Ideal CategoryTheory Opposite in
variable {p : ℕ} [Fact p.Prime] {O : Type} [CommRing O] [Fact ¬IsUnit (p : O)]
  [IsAdicComplete (span {(p : O)}) O] in
theorem _root_.GlobalTheory.PDivLat.ghost_add (n : ℕ) (a b : _root_.GlobalTheory.Sandwich.Ainf p O) :
    _root_.GlobalTheory.PDivLat.ghost p O n (a + b) = _root_.GlobalTheory.PDivLat.ghost p O n a + _root_.GlobalTheory.PDivLat.ghost p O n b := by
  simp only [_root_.GlobalTheory.PDivLat.ghost, iterate_map_add, map_add]

set_option autoImplicit false in
open WittVector Ideal CategoryTheory Opposite in
variable {p : ℕ} [Fact p.Prime] {O : Type} [CommRing O] [Fact ¬IsUnit (p : O)]
  [IsAdicComplete (span {(p : O)}) O] in
theorem _root_.GlobalTheory.PDivLat.ghost_mul (n : ℕ) (a b : _root_.GlobalTheory.Sandwich.Ainf p O) :
    _root_.GlobalTheory.PDivLat.ghost p O n (a * b) = _root_.GlobalTheory.PDivLat.ghost p O n a * _root_.GlobalTheory.PDivLat.ghost p O n b := by
  simp only [_root_.GlobalTheory.PDivLat.ghost, iterate_map_mul, map_mul]

set_option autoImplicit false in
open WittVector Ideal CategoryTheory Opposite in
variable {p : ℕ} [Fact p.Prime] {O : Type} [CommRing O] [Fact ¬IsUnit (p : O)]
  [IsAdicComplete (span {(p : O)}) O] in
theorem _root_.GlobalTheory.PDivLat.ghost_zero (n : ℕ) : _root_.GlobalTheory.PDivLat.ghost p O n 0 = 0 := by
  simp only [_root_.GlobalTheory.PDivLat.ghost, iterate_map_zero, map_zero]

theorem ghost_frobenius (n : ℕ) (a : Ainf p O) :
    ghost p O n (WittVector.frobenius a) = ghost p O (n + 1) a := rfl

abbrev TDual (G : PDivGroup p O) : Type := G.Tate →ₛₗ[ofPadic p O] Ainf p O

def latt (G : PDivGroup p O) : Submodule (Ainf p O) (TDual G) where
  carrier := {y | ∀ n, ∃ x : G.dual.Lie, ∀ t, ghost p O n (y t) = x (hodgeTate G t)}
  zero_mem' n := ⟨0, fun _ => ghost_zero n⟩
  add_mem' {y z} hy hz n := by
    obtain ⟨x, hx⟩ := hy n
    obtain ⟨x', hx'⟩ := hz n
    exact ⟨x + x', fun t => by rw [LinearMap.add_apply, ghost_add, hx, hx', LinearMap.add_apply]⟩
  smul_mem' a y hy n := by
    obtain ⟨x, hx⟩ := hy n
    exact ⟨ghost p O n a • x, fun t => by
      rw [LinearMap.smul_apply, smul_eq_mul, ghost_mul, hx, LinearMap.smul_apply, smul_eq_mul]⟩

def lattMap {G H : PDivGroup p O} (f : G ⟶ H) : latt H →ₗ[Ainf p O] latt G where
  toFun y := ⟨y.1.comp (tateMap G H O f), fun n => by
    obtain ⟨x, hx⟩ := y.2 n
    exact ⟨x ∘ₗ omegaDualMap G H f, fun t => by
      rw [LinearMap.comp_apply, hx, hodgeTate_tateMap, LinearMap.comp_apply]⟩⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

variable (p O) in

def lattFunctor : (PDivGroup p O)ᵒᵖ ⥤ ModuleCat.{0} (Ainf p O) where
  obj G := ModuleCat.of _ (latt G.unop)
  map f := ModuleCat.ofHom (lattMap f.unop)
  map_id _ := rfl
  map_comp _ _ := rfl

def HasDatum [IsDomain O] {ε : PreTilt O p} (hε : IsPrimitiveSystem ε) (G : PDivGroup p O) : Prop :=
  ∃ (D : Datum ε G.height ℤ_[p]) (e : G.Tate ≃ₗ[ℤ_[p]] (Fin G.height → ℤ_[p]))
    (fil : G.dual.omega ≃ₗ[O] D.Fil) (lie : ((Fin G.height → O) ⧸ D.Fil) ≃ₗ[O] G.Lie),
    (∀ t, D.al (toO e t) = (fil (hodgeTate G t) : Fin G.height → O)) ∧
      ∀ (x : G.Lie) (χ : G.dual.Tate), pairingO hε e (bQuot D (lie.symm x)) χ = x (dlog G χ)

def IsConn (G : PDivGroup p O) : Prop := ∀ n, IsLocalRing (G.A n)

def IsConst (G : PDivGroup p O) : Prop :=
  ∀ n, Nonempty (G.A n ≃ₐ[O] (Fin (p ^ (n * G.height)) → O))

def IsSum (G G₁ G₂ : PDivGroup p O) : Prop :=
  ∃ (i₁ : G₁ ⟶ G) (i₂ : G₂ ⟶ G) (q₁ : G ⟶ G₁) (q₂ : G ⟶ G₂), i₁ ≫ q₁ = 𝟙 _ ∧ i₂ ≫ q₂ = 𝟙 _ ∧
    i₁ ≫ q₂ = 0 ∧ i₂ ≫ q₁ = 0 ∧ q₁ ≫ i₁ + q₂ ≫ i₂ = 𝟙 _

end GlobalTheory.PDivLat
