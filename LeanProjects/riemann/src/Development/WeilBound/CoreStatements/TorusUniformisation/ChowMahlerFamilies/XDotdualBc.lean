import Mathlib
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.LieLatticeData
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.AffineHilbertIdealSheafOfQuotientIdealTop
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.LocallyFreeFiniteProjectiveBaseChange
open GlobalTheory.CompanionTheory.Ar.Num

namespace PositivityTheory.Xgn.A_dotdual_bc

variable {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω]

theorem mem_dotDual (R : Subalgebra o Ω) {m : ℕ} (L : AddSubgroup (Fin m → Ω)) (w : Fin m → Ω) :
    w ∈ dotDual R L ↔ ∀ v ∈ L, v ⬝ᵥ w ∈ R := by
  simp only [dotDual, AddSubgroup.mem_iInf, AddSubgroup.mem_comap]
  rfl

theorem dot_bij (m : ℕ) : Function.Bijective (dotProductBilin Ω Ω (m := Fin m) (A := Ω)).flip := by
  have h : ⇑(dotProductBilin Ω Ω (m := Fin m) (A := Ω)).flip = ⇑(dotProductEquiv Ω (Fin m)) := by
    funext w
    ext j
    simp [dotProductBilin, dotProductEquiv]
  rw [h]
  exact (dotProductEquiv Ω (Fin m)).bijective

theorem exists_system (R : Subalgebra o Ω) {m : ℕ} (L : AddSubgroup (Fin m → Ω))
    (h : LocFree R m L) : ∃ (k : ℕ) (v l : Fin k × Fin m → Fin m → Ω), (∀ i, v i ∈ L) ∧
      (∀ i, l i ∈ dotDual R L) ∧ ∀ j j', ∑ i, l i j * v i j' = if j' = j then 1 else 0 := by
  let L' : Submodule R (Fin m → Ω) :=
    { L with smul_mem' := fun a e he => h.1 a a.2 e he }
  obtain ⟨k, φ, v, hφ, hv⟩ := LocFreeProj.exists_dualBasis (L := L') (r := m) h
  refine ⟨k, fun i => v i, fun i j => φ i (Pi.single j 1), fun i => (v i).2, fun i => ?_,
    fun j j' => ?_⟩
  · rw [mem_dotDual]
    intro e he
    have h1 : e ⬝ᵥ (fun j => φ i (Pi.single j 1)) = φ i e := by
      rw [LinearMap.pi_apply_eq_sum_univ (φ i) e, dotProduct]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [smul_eq_mul]
      congr 2
      funext j'
      simp [Pi.single_apply, eq_comm]
    rw [h1]
    exact hφ i e he
  · have := congrFun (hv (Pi.single j 1)) j'
    simpa [Finset.sum_apply, Pi.single_apply] using this

theorem bc_dot {C : Type} [Field C] [Algebra Ω C] {m : ℕ} (a b : Fin m → Ω) :
    bcMap Ω C (Fin m) a ⬝ᵥ bcMap Ω C (Fin m) b = algebraMap Ω C (a ⬝ᵥ b) := by
  simp [dotProduct, bcMap, map_sum]

end PositivityTheory.Xgn.A_dotdual_bc

open PositivityTheory.Xgn.A_dotdual_bc in
theorem PositivityTheory.Xgn.t_dotdual_bc : ∀ {o Ω C : Type} [CommRing o] [Field Ω] [Field C] [Algebra o Ω] [Algebra o C] [Algebra Ω C] [IsScalarTower o Ω C] (R : Subalgebra o Ω) (RC : Subalgebra o C), (∀ a ∈ R, algebraMap Ω C a ∈ RC) → ∀ (m : ℕ) (L : AddSubgroup (Fin m → Ω)), LocFree R m L → LocFree R m (dotDual R L) ∧ dotDual R (dotDual R L) = L ∧ dotDual RC (spanOver RC (bcMap Ω C (Fin m) '' L)) = spanOver RC (bcMap Ω C (Fin m) '' (dotDual R L : AddSubgroup (Fin m → Ω))) := by
  intro o Ω C _ _ _ _ _ _ _ R RC hR m L h
  obtain ⟨h1, h2⟩ := DualLattice.locFree_dual R (dotProductBilin Ω Ω (m := Fin m) (A := Ω))
    (dot_bij m) m L (dotDual R L) h (fun w => mem_dotDual R L w)
  refine ⟨h1, ?_, ?_⟩
  · ext v
    rw [mem_dotDual, h2]
    refine forall₂_congr fun w _ => ?_
    rw [dotProduct_comm]
    rfl
  obtain ⟨k, v, l, hv, hl, hs⟩ := exists_system R L h
  apply le_antisymm
  · intro u hu
    rw [mem_dotDual] at hu
    have key : u = ∑ i, (bcMap Ω C (Fin m) (v i) ⬝ᵥ u) • bcMap Ω C (Fin m) (l i) := by
      funext j
      have h3 : ∀ j', ∑ i, algebraMap Ω C (l i j) * algebraMap Ω C (v i j')
          = if j' = j then 1 else 0 := fun j' => by
        have := congrArg (algebraMap Ω C) (hs j j')
        rw [map_sum] at this
        simp only [map_mul] at this
        rw [this]
        split_ifs <;> simp
      have h4 : ∀ (x : Fin m → Ω) j, bcMap Ω C (Fin m) x j = algebraMap Ω C (x j) := fun _ _ => rfl
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, dotProduct, h4, Finset.sum_mul]
      rw [Finset.sum_comm]
      calc u j = ∑ j', (if j' = j then 1 else 0) * u j' := by simp
        _ = _ := Finset.sum_congr rfl fun j' _ => by
          rw [← h3, Finset.sum_mul]
          exact Finset.sum_congr rfl fun i _ => by ring
    rw [key]
    refine AddSubgroup.sum_mem _ fun i _ => AddSubgroup.subset_closure ?_
    refine ⟨_, hu _ (AddSubgroup.subset_closure ⟨1, RC.one_mem, _, ⟨v i, hv i, rfl⟩, ?_⟩), _,
      ⟨l i, hl i, rfl⟩, rfl⟩
    rw [one_smul]
  · refine (AddSubgroup.closure_le _).2 ?_
    rintro _ ⟨a, ha, _, ⟨w, hw, rfl⟩, rfl⟩
    refine (mem_dotDual _ _ _).2 fun x hx => ?_
    induction hx using AddSubgroup.closure_induction with
    | mem x hx =>
      obtain ⟨b, hb, _, ⟨e, he, rfl⟩, rfl⟩ := hx
      rw [smul_dotProduct, dotProduct_smul, bc_dot, smul_eq_mul, smul_eq_mul]
      exact RC.mul_mem hb (RC.mul_mem ha (hR _ ((mem_dotDual R L w).1 hw e he)))
    | zero => rw [zero_dotProduct]; exact RC.zero_mem
    | add x y _ _ hx hy => rw [add_dotProduct]; exact RC.add_mem hx hy
    | neg x _ hx => rw [neg_dotProduct]; exact RC.neg_mem hx
