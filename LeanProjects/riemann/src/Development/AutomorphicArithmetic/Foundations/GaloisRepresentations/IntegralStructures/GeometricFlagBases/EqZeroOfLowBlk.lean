import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.FlagBasis

open CategoryTheory Limits AlgebraicGeometry NumberField GlobalTheory.EtC GlobalTheory.Et TensorProduct Polynomial
open GlobalTheory.GalV (HTower Htot hop galV galTot)
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N
open UpperTheory.Gal UpperTheory.Gal.Int.Geo

namespace UpperTheory.Gal.Int.Geo

private def blk (k : Type) [Field k] {d : ℕ} (c : Fin d → ℕ) (i : ℕ) : Submodule k (Fin d → k) where
  carrier := {v | ∀ j, c j ≠ i → v j = 0}
  zero_mem' _ _ := rfl
  add_mem' ha hb j h := by simp [ha j h, hb j h]
  smul_mem' r v hv j h := by simp [hv j h]

theorem grSS_of :
    GrHom → SSOfSum → GrSS := by
  intro _ hSS Γ k _ _ d ρ₀ ρ c hJH hρ
  obtain ⟨hinv, hmax⟩ := hJH
  have key : ∀ (g : Γ) (i : ℕ) (u : Fin d → k), u ∈ blk k c i → ∀ a,
      (↑(ρ g) : Matrix (Fin d) (Fin d) k).mulVec u a =
        if c a = i then (↑(ρ₀ g) : Matrix (Fin d) (Fin d) k).mulVec u a else 0 := by
    intro g i u hu a
    simp only [Matrix.mulVec, dotProduct, hρ]
    split_ifs with h
    · refine Finset.sum_congr rfl fun b _ => ?_
      split_ifs with h'
      · rfl
      · simp [hu b (by omega)]
    · refine Finset.sum_eq_zero fun b _ => ?_
      split_ifs with h'
      · simp [hu b (by omega)]
      · simp
  have hblk : ∀ i, IsInv ρ (blk k c i) := by
    intro i g u hu j hj
    rw [key g i u hu j, if_neg hj]
  have hsup : ⨆ i, blk k c i = ⊤ := by
    rw [eq_top_iff]
    intro v _
    rw [← Finset.univ_sum_single v]
    refine Submodule.sum_mem _ fun j _ => ?_
    refine Submodule.mem_iSup_of_mem (c j) ?_
    intro a ha
    rw [Pi.single_eq_of_ne]
    rintro rfl
    exact ha rfl
  refine hSS Γ k d ρ (fun i => blk k c i) hblk ?_ hsup
  intro i U hU hUle
  have hlow : low k c i ≤ low k c (i + 1) := fun v hv j hj => hv j (by omega)
  have hblkle : blk k c i ≤ low k c (i + 1) := fun v hv j hj => hv j (by omega)
  have hdisj : ∀ v, v ∈ blk k c i → v ∈ low k c i → v = 0 := by
    intro v h1 h2
    funext j
    by_cases h : c j = i
    · exact h2 j h.ge
    · exact h1 j h
  have hU'inv : IsInv ρ₀ (low k c i ⊔ U) := by
    intro g v hv
    obtain ⟨w, hw, u, hu, rfl⟩ := Submodule.mem_sup.mp hv
    rw [Matrix.mulVec_add]
    refine Submodule.add_mem _ (Submodule.mem_sup_left (hinv i g w hw)) ?_
    have huB := hUle hu
    rw [← sub_add_cancel ((↑(ρ₀ g) : Matrix (Fin d) (Fin d) k).mulVec u)
      ((↑(ρ g) : Matrix (Fin d) (Fin d) k).mulVec u)]
    refine Submodule.add_mem _ (Submodule.mem_sup_left ?_) (Submodule.mem_sup_right (hU g u hu))
    intro a ha
    rw [Pi.sub_apply, key g i u huB a]
    split_ifs with h
    · exact sub_self _
    · rw [hinv (i + 1) g u (hblkle huB) a (by omega), sub_zero]
  rcases hmax i _ hU'inv le_sup_left (sup_le hlow (hUle.trans hblkle)) with h | h
  · left
    rw [eq_bot_iff]
    intro v hv
    rw [Submodule.mem_bot]
    have hv' : v ∈ low k c i := by
      rw [← h]
      exact Submodule.mem_sup_right hv
    exact hdisj v (hUle hv) hv'
  · right
    apply le_antisymm hUle
    intro v hv
    have hv' : v ∈ low k c i ⊔ U := by
      rw [h]
      exact hblkle hv
    obtain ⟨w, hw, u, hu, rfl⟩ := Submodule.mem_sup.mp hv'
    have hwB : w ∈ blk k c i := by
      have := Submodule.sub_mem _ hv (hUle hu)
      simpa using this
    rw [hdisj w hwB hw, zero_add]
    exact hu

end UpperTheory.Gal.Int.Geo
