import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.FaithfulSMulAlgClosure
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemRingOver

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (resG)
open GlobalTheory.Twist (resM resM_resM resM_self resM_smul)
open GlobalTheory.QCoh (freeModule)
open GlobalTheory.VB (isFrame_freeFrame Sub)
open GlobalTheory.PerfdLat (piMap piMap_apply)

namespace GlobalTheory.LatGlue

variable {Y : Scheme.{0}} {h : ℕ}

variable (Y h) in

def coords (W : Y.Opens) : Γ(freeModule Y (Fin h), W) ≃ₗ[Γ(Y, W)] (Fin h → Γ(Y, W)) :=
  ((isFrame_freeFrame Y (Fin h)).basis (le_top : W ≤ ⊤)).equivFun

theorem coords_resM {W W' : Y.Opens} (hle : W' ≤ W) (s : Γ(freeModule Y (Fin h), W)) :
    coords Y h W' (resM _ hle s) = piMap (resG Y hle) (Fin h) (coords Y h W s) :=
  funext fun l => (isFrame_freeFrame Y (Fin h)).repr_resM le_top hle s l

variable {I : Type}

def localSpan (V : I → Y.Opens) (P : ∀ i, Submodule Γ(Y, V i) (Fin h → Γ(Y, V i))) (W : Y.Opens) :
    Submodule Γ(Y, W) (Fin h → Γ(Y, W)) :=
  Submodule.span Γ(Y, W) {v | ∃ (i : I) (hi : W ≤ V i), ∃ u ∈ P i, v = piMap (resG Y hi) (Fin h) u}

variable {V : I → Y.Opens} {P : ∀ i, Submodule Γ(Y, V i) (Fin h → Γ(Y, V i))}

theorem piMap_mem_localSpan {W W' : Y.Opens} (hle : W' ≤ W) {v : Fin h → Γ(Y, W)} (hv : v ∈ localSpan V P W) :
    piMap (resG Y hle) (Fin h) v ∈ localSpan V P W' := by
  induction hv using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨i, hi, u, hu, rfl⟩ := hx
    refine Submodule.subset_span ⟨i, hle.trans hi, u, hu, funext fun l => ?_⟩
    simp only [piMap_apply]
    exact (GlobalTheory.LB.resG_resG hi hle (u l))
  | zero => simp
  | add x y _ _ hx hy => simpa using add_mem hx hy
  | smul a x _ hx =>
    rw [LinearMap.map_smulₛₗ]
    exact Submodule.smul_mem _ _ hx

variable (V P) in

def glueSub : Sub (freeModule Y (Fin h)) where
  sec W :=
    { carrier := {s | ∀ y ∈ W, ∃ (W' : Y.Opens) (hle : W' ≤ W), y ∈ W' ∧
        coords Y h W' (resM _ hle s) ∈ localSpan V P W'}
      zero_mem' := fun y hy => ⟨W, le_rfl, hy, by simp⟩
      add_mem' := fun {s t} hs ht y hy => by
        obtain ⟨W₁, h₁, hy₁, m₁⟩ := hs y hy
        obtain ⟨W₂, h₂, hy₂, m₂⟩ := ht y hy
        refine ⟨W₁ ⊓ W₂, inf_le_left.trans h₁, ⟨hy₁, hy₂⟩, ?_⟩
        have e₁ := coords_resM (inf_le_left : W₁ ⊓ W₂ ≤ W₁) (resM _ h₁ s)
        have e₂ := coords_resM (inf_le_right : W₁ ⊓ W₂ ≤ W₂) (resM _ h₂ t)
        rw [resM_resM] at e₁ e₂
        rw [map_add, map_add, e₁, e₂]
        exact add_mem (piMap_mem_localSpan _ m₁) (piMap_mem_localSpan _ m₂)
      smul_mem' := fun a s hs y hy => by
        obtain ⟨W₁, h₁, hy₁, m₁⟩ := hs y hy
        refine ⟨W₁, h₁, hy₁, ?_⟩
        rw [resM_smul, map_smul]
        exact Submodule.smul_mem _ _ m₁ }
  res_mem {W W'} hle s hs y hy := by
    obtain ⟨W₁, h₁, hy₁, m₁⟩ := hs y (hle hy)
    refine ⟨W₁ ⊓ W', inf_le_right, ⟨hy₁, hy⟩, ?_⟩
    have e₁ := coords_resM (inf_le_left : W₁ ⊓ W' ≤ W₁) (resM _ h₁ s)
    rw [resM_resM] at e₁
    rw [resM_resM, e₁]
    exact piMap_mem_localSpan _ m₁
  mem_of_local {W s} H y hy := by
    obtain ⟨W₁, h₁, hy₁, m₁⟩ := H y hy
    obtain ⟨W₂, h₂, hy₂, m₂⟩ := m₁ y hy₁
    refine ⟨W₂, h₂.trans h₁, hy₂, ?_⟩
    rw [resM_resM] at m₂
    exact m₂

theorem mem_glueSub_sec {W : Y.Opens} {s : Γ(freeModule Y (Fin h), W)} :
    s ∈ (glueSub V P).sec W ↔ ∀ y ∈ W, ∃ (W' : Y.Opens) (hle : W' ≤ W), y ∈ W' ∧
      coords Y h W' (resM _ hle s) ∈ localSpan V P W' := Iff.rfl

end GlobalTheory.LatGlue
