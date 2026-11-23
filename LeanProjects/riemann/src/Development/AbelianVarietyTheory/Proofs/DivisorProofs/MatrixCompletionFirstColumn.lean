import Mathlib
import Formalism.RealPlaceAnalysis.ThirdArithmeticHolds
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemNilRad
open Matrix GlobalTheory.TorFin

namespace GlobalTheory

open Module

theorem frame_first_column_first_row :
    ∀ (m : ℕ) (v φ : Fin (m + 1) → ℂ), φ ⬝ᵥ v = 1 → ∃ P P' : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ,
      P * P' = 1 ∧ (∀ i, P i 0 = v i) ∧ ∀ j, P' 0 j = φ j := by
  intro m v φ h
  let L : (Fin (m + 1) → ℂ) →ₗ[ℂ] ℂ :=
    { toFun := fun x => φ ⬝ᵥ x
      map_add' := fun x y => dotProduct_add φ x y
      map_smul' := fun c x => by simp [dotProduct_smul] }
  have hL : ∀ x, L x = φ ⬝ᵥ x := fun x => rfl
  have hsurj : LinearMap.range L = ⊤ := by
    rw [LinearMap.range_eq_top]
    intro c
    exact ⟨c • v, by rw [hL, dotProduct_smul, h]; simp⟩
  have hdim : Module.finrank ℂ (LinearMap.ker L) = m := by
    have := LinearMap.finrank_range_add_finrank_ker L
    rw [hsurj, finrank_top, Module.finrank_self, Module.finrank_fin_fun] at this
    omega
  let bN := Module.finBasisOfFinrankEq ℂ (LinearMap.ker L) hdim
  have hli : ∀ (c : ℂ), ∀ x ∈ LinearMap.ker L, c • v + x = 0 → c = 0 := by
    intro c x hx hc
    have := congrArg L hc
    rw [map_add, map_smul, LinearMap.mem_ker.mp hx, hL v, h, map_zero] at this
    simpa using this
  have hsp : ∀ z : Fin (m + 1) → ℂ, ∃ c : ℂ, z + c • v ∈ LinearMap.ker L := by
    intro z
    refine ⟨-(L z), ?_⟩
    rw [LinearMap.mem_ker, map_add, map_smul, hL v, h]
    simp
  let b := Module.Basis.mkFinCons v bN hli hsp
  have hb : ⇑b = Fin.cons v (Subtype.val ∘ bN) := Module.Basis.coe_mkFinCons v bN hli hsp
  let e := Pi.basisFun ℂ (Fin (m + 1))
  have hcoord : b.coord 0 = L := by
    refine b.ext fun i => ?_
    refine Fin.cases ?_ (fun k => ?_) i
    · rw [Basis.coord_apply, Basis.repr_self, hb]
      simp [hL, h]
    · rw [Basis.coord_apply, Basis.repr_self, Finsupp.single_apply]
      have hmem : b k.succ ∈ LinearMap.ker L := by
        rw [hb]; simp
      rw [LinearMap.mem_ker.mp hmem]
      simp [Fin.succ_ne_zero]
  refine ⟨e.toMatrix b, b.toMatrix e, Basis.toMatrix_mul_toMatrix_flip e b, ?_, ?_⟩
  · intro i
    rw [Basis.toMatrix_apply, hb]
    simp [e]
  · intro j
    rw [Basis.toMatrix_apply]
    have := congrArg (fun f : (Fin (m + 1) → ℂ) →ₗ[ℂ] ℂ => f (e j)) hcoord
    simp only [Basis.coord_apply] at this
    rw [this, hL]
    simp [e, dotProduct_single]

end GlobalTheory
