import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.PlacesToAdeles

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil ValuativeRel IsLocalRing
open GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter (compFin ExtUnramAt CharUnramAt)
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FinPl.SrcGl

variable {D : D7}

def CA (A : HSp D) : Submodule ℂ (GA D A → ℂ) where
  carrier := {φ | GlobalTheory.Unf.IsContAut A φ}
  add_mem' {φ ψ} hφ hψ := ⟨fun γ hγ g => by simp [hφ.1 γ hγ g, hψ.1 γ hγ g], hφ.2.add hψ.2⟩
  zero_mem' := ⟨fun _ _ _ => rfl, continuous_const⟩
  smul_mem' c φ hφ := ⟨fun γ hγ g => by simp [hφ.1 γ hγ g], continuous_const.mul hφ.2⟩

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {p : SplitPt D k}
  {n : Type} [Fintype n] [DecidableEq n]

theorem rep_mem_CA {A : HSp D} (α : Frame p A n) (g : GL n k) {φ : GA D A → ℂ} (h : φ ∈ CA A) : α.rep g φ ∈ CA A :=
  ⟨fun γ hγ x => by
    change φ (γ * x * α.gl g) = φ (x * α.gl g)
    rw [mul_assoc, h.1 γ hγ], h.2.comp (continuous_mul_right _)⟩

def caRep {A : HSp D} (α : Frame p A n) : Representation ℂ (GL n k) (CA A) where
  toFun g := (α.rep g).restrict fun _ h => rep_mem_CA α g h
  map_one' := by ext φ x; simp
  map_mul' g h := by ext φ x; simp

@[simp] theorem caRep_apply {A : HSp D} (α : Frame p A n) (g : GL n k) (φ : CA A) :
    ((caRep α g φ : CA A) : GA D A → ℂ) = α.rep g φ := rfl

def blkHom : Matrix n n k →* Matrix (n ⊕ Fin 1) (n ⊕ Fin 1) k where
  toFun x := fromBlocks x 0 0 1
  map_one' := by simp
  map_mul' x y := by simp [fromBlocks_multiply]

def blk : GL n k →* GL (n ⊕ Fin 1) k := Units.map blkHom

@[simp] theorem blk_val (g : GL n k) : (blk g).val = fromBlocks g.val (0 : Matrix n (Fin 1) k) 0 1 := rfl

end GlobalTheory.FinPl.SrcGl
