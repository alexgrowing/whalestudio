import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.LeibnizDerivatives.GenericProdIff
import GroundTheory.AutomorphicForms.GeometricLemmaCells

noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL

namespace GlobalTheory.CompanionTheory.Rodier

section Pi

variable {α : Type} [Fintype α] {Γ : α → Type} [∀ a, Group (Γ a)]

abbrev piSub (H : ∀ a, Subgroup (Γ a)) : Subgroup (∀ a, Γ a) := Subgroup.pi Set.univ H

def piChar {H : ∀ a, Subgroup (Γ a)} (χ : ∀ a, H a →* ℂˣ) : piSub H →* ℂˣ where
  toFun m := ∏ a, χ a ⟨m.1 a, m.2 a (Set.mem_univ a)⟩
  map_one' := Finset.prod_eq_one fun a _ => map_one (χ a)
  map_mul' x y := by
    rw [← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun a _ => map_mul (χ a) ⟨x.1 a, x.2 a (Set.mem_univ a)⟩ ⟨y.1 a, y.2 a (Set.mem_univ a)⟩

end Pi

variable (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {h N : ℕ} (d : Fin h → ℕ) (hd : ∑ a, d a = N)

abbrev pm (w : Equiv.Perm (Fin N)) : GL (Fin N) k := GroundTheory.Automorphic.permGL k w

def cell (w : Equiv.Perm (Fin N)) : Set (GL (Fin N) k) :=
  {g | ∃ p ∈ parab k (stdBlocks d hd), ∃ n ∈ unipB k (Fin N), g = p * pm k w * n}

def wKey (i : Fin N) : (Fin h)ᵒᵈ ×ₗ Fin N := toLex (OrderDual.toDual (blk (stdBlocks d hd) i), i)

def wOpen : Equiv.Perm (Fin N) := Tuple.sort (wKey d hd)

variable {k}
variable {W : Type} [AddCommGroup W] [Module ℂ W]

def openFns (ρ : Representation ℂ (Levi k fun a => Fin (d a)) W) : Submodule ℂ (IndSp (stdBlocks d hd) ρ) where
  carrier := {f | ∀ g, f.1.1 g ≠ 0 → g ∈ cell k d hd (wOpen d hd)}
  add_mem' := by
    intro a b ha hb g hg
    by_cases h1 : a.1.1 g = 0
    · refine hb g fun h2 => hg ?_
      show a.1.1 g + b.1.1 g = 0
      rw [h1, h2, add_zero]
    · exact ha g h1
  zero_mem' := fun g hg => absurd rfl hg
  smul_mem' := by
    intro c a ha g hg
    refine ha g fun h1 => hg ?_
    show c • a.1.1 g = 0
    rw [h1, smul_zero]

variable (k)

abbrev unipM : Subgroup (Levi k fun a => Fin (d a)) := piSub fun a => unipB k (Fin (d a))

variable {k}

abbrev whitM (ψ : AddChar k Circle) : unipM k d →* ℂˣ := piChar fun a => whitChar ψ (d a)

variable (k)

def unipU : Subgroup (GL (Fin N) k) :=
  unipB k (Fin N) ⊓ (unipRadLower k (stdBlocks d hd)).comap (MulAut.conj (pm k (wOpen d hd))).toMonoidHom

def unipL : Subgroup (GL (Fin N) k) :=
  unipB k (Fin N) ⊓ (leviEmb k (stdBlocks d hd)).range.comap (MulAut.conj (pm k (wOpen d hd))).toMonoidHom

end GlobalTheory.CompanionTheory.Rodier

namespace GlobalTheory.CompanionTheory.Rodier

def smInt {X W : Type} [MeasurableSpace X] [AddCommGroup W] [Module ℂ W] (μ : MeasureTheory.Measure X) (φ : X → W) : W :=
  ∑ᶠ v : W, (((μ (φ ⁻¹' {v})).toReal : ℝ) : ℂ) • v

end GlobalTheory.CompanionTheory.Rodier

end
