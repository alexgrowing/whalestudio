import Mathlib
import Formalism.LocalRingCardinality.DataAmbForm
import Formalism.LocalRingCardinality.DataKerP

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.PeriodPairingUnitLattice

open Formalism.BasicNotions NumberField

section Generic

variable {LL : Type} [Field LL] [NumberField LL] [StarRing LL] (emb : LL →+* ℂ) (Pl : Rows.Places LL)
  (Λ Λ' : HLat LL) (per : Λ.V → Λ'.V → ℂ)

def Rational : Prop := ∀ x z, ∃ y : LL, emb y = per x z

def IntegralUpTo (n : ℕ) : Prop :=
  ∀ (w : Pl.Pl), ∀ x ∈ locW Pl w Λ.L, ∀ z ∈ locW Pl w Λ'.L, ∀ y : LL, emb y = per x z →
    (n : LL) * y ∈ intW Pl w

def CauchySchwarz : Prop :=
  ∀ (v : InfinitePlace LL) x z, ∀ y : LL, emb y = per x z →
    v y ≤ Formalism.HermitianLatticesTheory.normAt Λ.b Λ.X v x * Formalism.HermitianLatticesTheory.normAt Λ'.b Λ'.X v z

def IsClassSumPairing (n : ℕ) : Prop :=
  Rational emb Λ Λ' per ∧ IntegralUpTo emb Pl Λ Λ' per n ∧ CauchySchwarz emb Λ Λ' per

def Nondegenerate : Prop := (∀ x, (∀ z, per x z = 0) → x = 0) ∧ ∀ z, (∀ x, per x z = 0) → z = 0

theorem IntegralUpTo.of_dvd {n n' : ℕ} (h : IntegralUpTo emb Pl Λ Λ' per n) (hn : n ∣ n') :
    IntegralUpTo emb Pl Λ Λ' per n' := by
  obtain ⟨k, rfl⟩ := hn
  intro w x hx z hz y hy
  have h1 := (intW Pl w).mul_mem (natCast_mem (intW Pl w) k) (h w x hx z hz y hy)
  have e : ((n * k : ℕ) : LL) * y = (k : LL) * ((n : LL) * y) := by push_cast; ring
  rwa [e]

def unitLat (LL : Type) [Field LL] [NumberField LL] [StarRing LL] : HLat LL where
  V := LL
  ι := Unit
  b := Module.Basis.singleton Unit LL
  X := fun _ => 1
  L := LinearMap.range (Algebra.linearMap (𝓞 LL) LL)

example : Rational emb (unitLat LL) (unitLat LL) (fun x z : LL => emb (x * z)) ∧
    CauchySchwarz emb (unitLat LL) (unitLat LL) (fun x z : LL => emb (x * z)) := by
  refine ⟨fun x z => ⟨_, rfl⟩, fun v (x : LL) (z : LL) y hy => ?_⟩
  have hy' : y = x * z := emb.injective hy
  have key : ∀ a : LL, Formalism.HermitianLatticesTheory.normAt (unitLat LL).b (unitLat LL).X v a = v a := by
    intro a
    show Real.sqrt (∑ i : Unit, ‖Matrix.mulVec (1 : Matrix Unit Unit ℂ)⁻¹
      (Formalism.HermitianLatticesTheory.vecAt (Module.Basis.singleton Unit LL) v a) i‖ ^ 2) = v a
    rw [inv_one, Matrix.one_mulVec]
    simp [Formalism.HermitianLatticesTheory.vecAt, InfinitePlace.norm_embedding_eq]
  rw [hy', key, key, map_mul]

end Generic

variable (D : D7)

def per0 (A : AmbForm D (RowSide.sharp D)) (u : D.what₂.Word)
    (x : (D.fm u).ptLat.V) (z : (A.MtH D.what₂.mu0).V) : ℂ :=
  (D.mem u).P.period ((D.fm u).ptEmb x) ((D.eMt u).symm (A.jAmb D.what₂.mu0 z))

def perTw (Tw : TwForms D) (A : AmbForm D (RowSide.sharp D)) (u : D.what₂.Word) (μ : D.what₂.Tup)
    (x : (Tw.fm u μ).ptLat.V) (z : (A.MtH μ).V) : ℂ :=
  (D.PTw u μ).period ((Tw.fm u μ).ptEmb x) ((D.eMtTw u μ).symm (A.jAmb μ z))

def PeriodPairing0 (A : AmbForm D (RowSide.sharp D)) (u : D.what₂.Word) : Prop :=
  IsClassSumPairing D.what₂.embLL D.what₂.places (D.fm u).ptLat (A.MtH D.what₂.mu0) (per0 D A u) (D.mem u).C.DGam

def PeriodPairingAt (Tw : TwForms D) (A : AmbForm D (RowSide.sharp D)) (u : D.what₂.Word) (μ : D.what₂.Tup) : Prop :=
  IsClassSumPairing D.what₂.embLL D.what₂.places (Tw.fm u μ).ptLat (A.MtH μ) (perTw D Tw A u μ) (D.chTw u μ).DGam

def PeriodPairingTw (Tw : TwForms D) (A : AmbForm D (RowSide.sharp D)) (u : D.what₂.Word) : Prop :=
  ∀ μ, DV.Used D μ → μ ≠ D.what₂.mu0 → PeriodPairingAt D Tw A u μ

def PeriodPairing (Tw : TwForms D) (A : AmbForm D (RowSide.sharp D)) (u : D.what₂.Word) : Prop :=
  PeriodPairing0 D A u ∧ PeriodPairingTw D Tw A u

theorem card_stabilizer_dvd₂ (Tw : TwForms D) (u : D.what₂.Word) (μ : D.what₂.Tup) (c : (Tw.fm u μ).clsP) :
    Nat.card ((Tw.fm u μ).stabilizer₂ c) ∣ (D.chTw u μ).DGam :=
  (Subgroup.card_dvd_of_injective _ ((Tw.fm u μ).stabMap_inj c)).trans
    ((D.chTw u μ).dvd_DGam _ le_rfl _)

end GlobalTheory.IndefiniteRowSideFullHecke.PeriodPairingUnitLattice
