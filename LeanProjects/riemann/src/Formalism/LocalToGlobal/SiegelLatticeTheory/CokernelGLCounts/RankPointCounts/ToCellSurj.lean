import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.IdxRatioConjSub

noncomputable section

open scoped Classical

namespace Formalism.L2.SG.Pf.CountAb

variable {G 𝒳 : Type} [Group G] [MulAction G 𝒳]

section

variable (W : 𝒳) (S N' K : Subgroup G) (π : G →* G) (g : G)

structure Data : Prop where
  stab : ∀ x : G, x • W = W ↔ x ∈ S
  mem : ∀ x, π x ∈ S
  id : ∀ s ∈ S, π s = s
  ker : ∀ x, x ∈ N' ↔ π x = 1
  kπ : ∀ k ∈ K, π k ∈ K

def cell (x : G) : G := x * (π x)⁻¹

theorem π_π (hD : Data W S N' K π) (x : G) : π (π x) = π x := hD.id _ (hD.mem x)

theorem cell_mem (hD : Data W S N' K π) (x : G) : cell π x ∈ N' := by
  rw [hD.ker, cell, map_mul, map_inv, π_π W S N' K π hD, mul_inv_cancel]

theorem cell_smul (hD : Data W S N' K π) (x : G) : cell π x • W = x • W := by
  rw [cell, mul_smul, (hD.stab _).mpr (S.inv_mem (hD.mem x))]

def Cells : Set G := {x | x ∈ N' ∧ ∃ k ∈ K, x • W = k • (g • W)}

def cellRel : Setoid (Cells W N' K g) where
  r x y := (y : G) * (x : G)⁻¹ ∈ K ⊓ N'
  iseqv := ⟨fun x => by simp [(K ⊓ N').one_mem], fun {x y} h => by
      have := (K ⊓ N').inv_mem h; simpa [mul_inv_rev] using this,
    fun {x y z} h1 h2 => by
      have := (K ⊓ N').mul_mem h2 h1; simpa [mul_assoc] using this⟩

def Hs : Subgroup G := K ⊓ MulAction.stabilizer G (g • W)

def toCell (hD : Data W S N' K π) (k : K) : Cells W N' K g :=
  ⟨cell π ((k : G) * g), cell_mem W S N' K π hD _, k, k.2, by rw [cell_smul W S N' K π hD, mul_smul]⟩

theorem toCell_surj (hD : Data W S N' K π) : Function.Surjective (toCell W S N' K π g hD) := by
  rintro ⟨c, hcN, k, hk, hc⟩
  refine ⟨⟨k, hk⟩, Subtype.ext ?_⟩
  show cell π (k * g) = c
  have hs : (k * g)⁻¹ * c ∈ S := by
    rw [← hD.stab, mul_smul, hc, ← mul_smul k g W, inv_smul_smul]
  obtain ⟨s, hsS, hc'⟩ : ∃ s ∈ S, c = k * g * s := ⟨_, hs, by group⟩
  have hπc : π c = 1 := (hD.ker c).mp hcN
  have hπ : π (k * g) = s⁻¹ := by
    rw [hc', map_mul, hD.id s hsS] at hπc
    exact eq_inv_of_mul_eq_one_left hπc
  rw [cell, hπ, inv_inv, ← hc']

end

end Formalism.L2.SG.Pf.CountAb
