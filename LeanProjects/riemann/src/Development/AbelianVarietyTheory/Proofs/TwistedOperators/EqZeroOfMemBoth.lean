import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.NormalDecomposition.DecompOfNormalStatement

open scoped InnerProductSpace

noncomputable section

namespace GlobalTheory.OntoLinAlg

open Formalism.IndefR.U2

variable {I A B : Type} [NormedAddCommGroup A] [InnerProductSpace ℂ A] [FiniteDimensional ℂ A]
  [NormedAddCommGroup B] [InnerProductSpace ℂ B] [FiniteDimensional ℂ B]

theorem op_mem_ker {θ : A →ₗ[ℂ] B} {op : I → Module.End ℂ A} {opB : I → Module.End ℂ B}
    (hI : Intw θ op opB) (i : I) {k : A} (hk : k ∈ LinearMap.ker θ) : op i k ∈ LinearMap.ker θ := by
  rw [LinearMap.mem_ker] at hk ⊢
  rw [hI, hk, map_zero]

theorem op_mem_orth {θ : A →ₗ[ℂ] B} {op : I → Module.End ℂ A} {opB : I → Module.End ℂ B}
    (hI : Intw θ op opB) (hA : AdjClosed op) (i : I) {v : A} (hv : v ∈ (LinearMap.ker θ)ᗮ) :
    op i v ∈ (LinearMap.ker θ)ᗮ := by
  rw [Submodule.mem_orthogonal] at hv ⊢
  intro u hu
  obtain ⟨i', hi'⟩ := hA i
  rw [← LinearMap.adjoint_inner_left, ← hi']
  exact hv _ (op_mem_ker hI i' hu)

theorem eq_zero_of_mem_both {K : Submodule ℂ A} {z : A} (h1 : z ∈ K) (h2 : z ∈ Kᗮ) : z = 0 := by
  have := (Submodule.mem_orthogonal _ _).mp h2 z h1
  exact inner_self_eq_zero.mp this

theorem ontoParts_of {θ : A →ₗ[ℂ] B} {op : I → Module.End ℂ A} {opB : I → Module.End ℂ B}
    {good : Submodule ℂ A} {goodB : Submodule ℂ B} (Ix : Set (I → ℂ))
    (hI : Intw θ op opB) (hA : AdjClosed op) (hOnto : goodB ≤ LinearMap.range θ)
    (hPr : ∀ y ∈ good, ((LinearMap.ker θ).starProjection y : A) ∈ good)
    (hInj : ∀ (c : I → ℂ) (x y : A), x ∈ eigPart op c → θ x ≠ 0 → y ∈ eigPart op c ⊓ good → θ y = 0 → y = 0) :
    OntoParts (LinearMap.adjoint θ) op opB good goodB Ix := by
  intro c hc y hy
  set K := LinearMap.ker θ with hK
  obtain ⟨w, hw, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hc.2
  obtain ⟨x0, hx0⟩ := hOnto hw.2
  set x := x0 - K.starProjection x0 with hxdef
  have hxo : x ∈ Kᗮ := Submodule.sub_starProjection_mem_orthogonal x0
  have hθx : θ x = w := by
    have : θ (K.starProjection x0) = 0 := LinearMap.mem_ker.mp (Submodule.starProjection_apply_mem K x0)
    rw [hxdef, map_sub, this, sub_zero, hx0]
  have hxe : x ∈ eigPart op c := by
    rw [mem_eigPart]
    intro i
    have hz1 : op i x - c i • x ∈ Kᗮ := Submodule.sub_mem _ (op_mem_orth hI hA i hxo) (Submodule.smul_mem _ _ hxo)
    have hz2 : op i x - c i • x ∈ K := by
      rw [hK, LinearMap.mem_ker, map_sub, map_smul, hI, hθx, (mem_eigPart.mp hw.1) i, sub_self]
    exact sub_eq_zero.mp (eq_zero_of_mem_both hz2 hz1)
  set y1 := K.starProjection y with hy1
  have hy1K : y1 ∈ K := Submodule.starProjection_apply_mem K y
  have hy2 : y - y1 ∈ Kᗮ := Submodule.sub_starProjection_mem_orthogonal y
  have hy1e : y1 ∈ eigPart op c := by
    rw [mem_eigPart]
    intro i
    have hyi := (mem_eigPart.mp hy.1) i
    have e : op i y1 - c i • y1 = -(op i (y - y1) - c i • (y - y1)) := by
      rw [map_sub, smul_sub, hyi]; abel
    have hz1 : op i y1 - c i • y1 ∈ K := Submodule.sub_mem _ (op_mem_ker hI i hy1K) (Submodule.smul_mem _ _ hy1K)
    have hz2 : op i y1 - c i • y1 ∈ Kᗮ := by
      rw [e]
      exact Submodule.neg_mem _ (Submodule.sub_mem _ (op_mem_orth hI hA i hy2) (Submodule.smul_mem _ _ hy2))
    exact sub_eq_zero.mp (eq_zero_of_mem_both hz1 hz2)
  have hy10 : y1 = 0 := hInj c x y1 hxe (by rw [hθx]; exact hw0) ⟨hy1e, hPr y hy.2⟩ (LinearMap.mem_ker.mp hy1K)
  rw [← LinearMap.orthogonal_ker]
  have : y = y - y1 := by rw [hy10, sub_zero]
  rw [this]
  exact hy2

end GlobalTheory.OntoLinAlg
