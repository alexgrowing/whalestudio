import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.IwahoriDoubleCosets
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivMultiProdOne
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.NotIsGenericDetRepTwo

noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel Matrix GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets

namespace UpperTheory.ConvolutionTheory.Loc

section Alg

variable {E : Type} [Field E] {n : ℕ}

def sg (σ : E ≃+* E) : GL (Fin n) E →* GL (Fin n) E := GeneralLinearGroup.map (σ : E →+* E)

def nrm (σ : E ≃+* E) (q : ℕ) (δ : GL (Fin n) E) : GL (Fin n) E := ((List.range q).map fun i => (sg σ)^[i] δ).prod

example (δ : GL (Fin n) E) (σ : E ≃+* E) : nrm σ 1 δ = δ := by simp [nrm]

example (δ : GL (Fin n) E) (σ : E ≃+* E) : nrm σ 2 δ = δ * sg σ δ := by simp [nrm, List.range_succ]

end Alg

variable {E : Type} [Field E] [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E] {n : ℕ}

def Isom (σ : E ≃+* E) : Prop := ∀ x, valuation E (σ x) = valuation E x

structure Cyc (σ : E ≃+* E) (q : ℕ) : Prop where
  isom : Isom σ
  pos : 0 < q
  ord : ∀ x, σ^[q] x = x

structure Unram (σ : E ≃+* E) (q : ℕ) : Prop extends Cyc σ q where
  res : ∀ j, 0 < j → j < q → ∃ x, valuation E x ≤ 1 ∧ valuation E (σ^[j] x - x) = 1

example : Unram (RingEquiv.refl E) 1 := ⟨⟨fun _ => rfl, one_pos, fun _ => rfl⟩, fun _ h h' => by omega⟩

def ball (n : ℕ) (r : ValueGroupWithZero E) : Set (GL (Fin n) E) :=
  {g | ∀ i j, valuation E ((g : Matrix (Fin n) (Fin n) E) i j - (1 : Matrix (Fin n) (Fin n) E) i j) ≤ r}

example (r : ValueGroupWithZero E) : 1 ∈ ball n r := fun i j => by simp

def Strict (t : Fin n → Eˣ) : Prop := ∀ i j, i < j → valuation E (t i : E) < valuation E (t j : E)

def howeSet (n : ℕ) (ϖ : Eˣ) (a c : ℤ) : Set (GL (Fin n) E) :=
  {g | ∀ i j : Fin n, valuation E ((g : Matrix (Fin n) (Fin n) E) i j - (1 : Matrix (Fin n) (Fin n) E) i j) ≤
    valuation E ((ϖ ^ (a + c * (((i : ℕ) : ℤ) - ((j : ℕ) : ℤ))) : Eˣ) : E)}

example (ϖ : Eˣ) (a c : ℤ) : 1 ∈ howeSet n ϖ a c := fun i j => by simp

variable {V : Type} [AddCommGroup V] [Module ℂ V]

def howeSpace (π : Representation ℂ (GL (Fin n) E) V) (ψ : AddChar E Circle) (S : Set (GL (Fin n) E)) : Submodule ℂ V where
  carrier := {v | ∀ x ∈ S, π x v = (ψ (GlobalTheory.Whittaker.superDiag x) : ℂ) • v}
  add_mem' := by
    intro a b ha hb x hx
    rw [map_add, ha x hx, hb x hx, smul_add]
  zero_mem' := by intro x _; simp
  smul_mem' := by
    intro c v hv x hx
    rw [map_smul, hv x hx, smul_comm]

end UpperTheory.ConvolutionTheory.Loc

end
