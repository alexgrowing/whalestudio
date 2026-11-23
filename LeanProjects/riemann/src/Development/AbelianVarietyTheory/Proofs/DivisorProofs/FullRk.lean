import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.RankEqCardIffExistsFrameMatrixFirstColumnBlock
import Development.AbelianVarietyTheory.Definitions.Divisors.HilbertNinetyQuotientHomEqIff

noncomputable section

open GlobalTheory.SplitFlip
open scoped Matrix

namespace GlobalTheory.FullRankCoinv

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

def lact {n d : ℕ} (ν : kˣ →* ℂˣ) (g : GL (Fin n) k) (Ψ : Matrix (Fin n) (Fin d) k → ℂ) :
    Matrix (Fin n) (Fin d) k → ℂ :=
  fun Y => (ν (gdet g) : ℂ) * apow (gdet g) ((d : ℂ) / 2) * Ψ ((g.1)ᵀ * Y)

variable (k) in

def fullRk (n d : ℕ) : Submodule ℂ (Matrix (Fin n) (Fin d) k → ℂ) where
  carrier := {Ψ | Ψ ∈ GlobalTheory.WeilM.SB (Matrix (Fin n) (Fin d) k) ∧ ∀ Y : Matrix (Fin n) (Fin d) k, Y.rank ≠ n → Ψ Y = 0}
  zero_mem' := ⟨Submodule.zero_mem _, fun _ _ => rfl⟩
  add_mem' := fun ha hb => ⟨Submodule.add_mem _ ha.1 hb.1, fun Y hY => by simp [ha.2 Y hY, hb.2 Y hY]⟩
  smul_mem' := fun c _ ha => ⟨Submodule.smul_mem _ c ha.1, fun Y hY => by simp [ha.2 Y hY]⟩

def augRk (n d : ℕ) (ν : kˣ →* ℂˣ) : Submodule ℂ (Matrix (Fin n) (Fin d) k → ℂ) :=
  Submodule.span ℂ {z | ∃ g : GL (Fin n) k, ∃ Ψ ∈ fullRk k n d, z = lact ν g Ψ - Ψ}

variable (k) in

def Y0 (n d : ℕ) : Matrix (Fin n) (Fin d) k := Matrix.of fun i j => if (j : ℕ) = d - n + i then 1 else 0

variable (k) in

def indSp (n d : ℕ) (ν : kˣ →* ℂˣ) : Submodule ℂ (GL (Fin d) k → ℂ) where
  carrier := {f | (∃ U ∈ nhds (1 : GL (Fin d) k), ∀ h, ∀ u ∈ U, f (h * u) = f h) ∧
    ∀ (b h : GL (Fin d) k) (D : GL (Fin n) k), Y0 k n d * b.1 = D.1 * Y0 k n d →
      f (b * h) = (((ν (gdet D))⁻¹ : ℂˣ) : ℂ) * apow (gdet D) (-(d : ℂ) / 2) * f h}
  zero_mem' := ⟨⟨Set.univ, Filter.univ_mem, fun _ _ _ => rfl⟩, fun _ _ _ _ => by simp⟩
  add_mem' := by
    rintro f g ⟨⟨U, hU, hf⟩, hf'⟩ ⟨⟨V, hV, hg⟩, hg'⟩
    refine ⟨⟨U ∩ V, Filter.inter_mem hU hV, fun h u hu => ?_⟩, fun b h D hD => ?_⟩
    · simp [hf h u hu.1, hg h u hu.2]
    · simp [hf' b h D hD, hg' b h D hD, mul_add]
  smul_mem' := by
    rintro c f ⟨⟨U, hU, hf⟩, hf'⟩
    refine ⟨⟨U, hU, fun h u hu => ?_⟩, fun b h D hD => ?_⟩
    · simp [hf h u hu]
    · simp [hf' b h D hD]; ring

end GlobalTheory.FullRankCoinv
