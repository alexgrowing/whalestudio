import Mathlib
import CompanionTheory.RealGroups.UnitaryAdmissibility.ArchimedeanUnitaryDual.InhabitedFinite
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.FinrankRangePowConvex
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.CommuteOfMemAdjoin
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.FinrankAdjoinLeAdd

open CompanionTheory.Rg.Fl

namespace GlobalTheory.CompanionTheory.Bernstein

theorem arith_nil (N D D' E m K : ℕ) (hN : 0 < N)
    (h1 : D ≤ (2 * N - 1) * D' + E) (h2 : (2 * N - 1 + 1) * E ≤ m ^ 2)
    (h3 : 4 * N ^ 2 * D' ≤ m ^ 2 + K * m) : N * D ≤ m ^ 2 + K * m := by
  obtain ⟨k, rfl⟩ : ∃ k, N = k + 1 := ⟨N - 1, by omega⟩
  have e1 : 2 * (k + 1) - 1 = 2 * k + 1 := by omega
  have e2 : 2 * (k + 1) - 1 + 1 = 2 * (k + 1) := by omega
  rw [e1] at h1
  rw [e2] at h2
  have h4 : (2 * (k + 1)) * D ≤ (2 * (k + 1)) * ((2 * k + 1) * D') + m ^ 2 := by
    calc (2 * (k + 1)) * D ≤ (2 * (k + 1)) * ((2 * k + 1) * D' + E) :=
          Nat.mul_le_mul_left _ h1
      _ = (2 * (k + 1)) * ((2 * k + 1) * D') + (2 * (k + 1)) * E := by ring
      _ ≤ _ := Nat.add_le_add_left h2 _
  have h5 : (2 * (k + 1)) * ((2 * k + 1) * D') ≤ 4 * (k + 1) ^ 2 * D' := by
    have : (2 * (k + 1)) * ((2 * k + 1) * D') + 2 * (k + 1) * D' = 4 * (k + 1) ^ 2 * D' := by ring
    omega
  have h6 : (2 * (k + 1)) * D ≤ 2 * m ^ 2 + K * m := by omega
  have h7 : 2 * ((k + 1) * D) ≤ 2 * (m ^ 2 + K * m) := by
    have : (2 * (k + 1)) * D = 2 * ((k + 1) * D) := by ring
    have h8 : 2 * (m ^ 2 + K * m) = 2 * m ^ 2 + K * m + K * m := by ring
    omega
  omega

theorem adjoin_shift {V : Type} [AddCommGroup V] [Module ℂ V] {l : ℕ}
    (a : Fin (l + 1) → Module.End ℂ V) (μ : ℂ) :
    Algebra.adjoin ℂ (Set.range (Fin.cons (a 0 - algebraMap ℂ _ μ) (fun i : Fin l => a i.succ) :
      Fin (l + 1) → Module.End ℂ V)) = Algebra.adjoin ℂ (Set.range a) := by
  apply le_antisymm
  · apply Algebra.adjoin_le
    rintro _ ⟨i, rfl⟩
    refine Fin.cases ?_ (fun j => ?_) i
    · simp only [Fin.cons_zero]
      exact Subalgebra.sub_mem _ (Algebra.subset_adjoin ⟨0, rfl⟩) (Subalgebra.algebraMap_mem _ μ)
    · simp only [Fin.cons_succ]
      exact Algebra.subset_adjoin ⟨j.succ, rfl⟩
  · apply Algebra.adjoin_le
    rintro _ ⟨i, rfl⟩
    refine Fin.cases ?_ (fun j => ?_) i
    · have h0 : a 0 - algebraMap ℂ _ μ ∈ Algebra.adjoin ℂ (Set.range (Fin.cons (a 0 - algebraMap ℂ _ μ)
          (fun i : Fin l => a i.succ) : Fin (l + 1) → Module.End ℂ V)) :=
        Algebra.subset_adjoin ⟨0, by simp⟩
      have := Subalgebra.add_mem _ h0 (Subalgebra.algebraMap_mem (Algebra.adjoin ℂ (Set.range (Fin.cons (a 0 - algebraMap ℂ _ μ)
          (fun i : Fin l => a i.succ) : Fin (l + 1) → Module.End ℂ V))) μ)
      simpa using this
    · exact Algebra.subset_adjoin ⟨j.succ, by simp⟩

theorem positionOne_invariantIntegral_exchange_step (l N K : ℕ) (hN : 0 < N)
    (hK : ∀ (V : Type) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
      (a : Fin l → Module.End ℂ V), (∀ i j, Commute (a i) (a j)) →
      4 * N ^ 2 * Module.finrank ℂ (Algebra.adjoin ℂ (Set.range a)) ≤
        Module.finrank ℂ V ^ 2 + K * Module.finrank ℂ V) :
    ∀ (n : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
      (a : Fin (l + 1) → Module.End ℂ V), Module.finrank ℂ V = n → (∀ i j, Commute (a i) (a j)) →
      N * Module.finrank ℂ (Algebra.adjoin ℂ (Set.range a)) ≤
        Module.finrank ℂ V ^ 2 + K * Module.finrank ℂ V := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro V _ _ _ a hn hc
  rcases subsingleton_or_nontrivial V with hV | hV
  · have : Module.finrank ℂ (Algebra.adjoin ℂ (Set.range a)) = 0 :=
      Module.finrank_zero_of_subsingleton
    simp [this]
  obtain ⟨μ, hμ⟩ := Module.End.exists_eigenvalue (a 0)
  obtain ⟨v, hv⟩ := hμ.exists_hasEigenvector
  set s : Module.End ℂ V := a 0 - algebraMap ℂ _ μ with hs
  have hsc : ∀ i, Commute s (a i) := fun i =>
    (hc 0 i).sub_left (Algebra.commutes μ (a i))
  have hsv : s v = 0 := by
    simp [hs, hv.apply_eq_smul, Module.algebraMap_end_apply]
  obtain ⟨k, hcompl, hk⟩ :=
    ((LinearMap.eventually_isCompl_ker_pow_range_pow s).and (Filter.eventually_ge_atTop 1)).exists
  have hkc : ∀ i, Commute (s ^ k) (a i) := fun i => (hsc i).pow_left k
  have h : ∀ i, ∀ w ∈ LinearMap.ker (s ^ k), a i w ∈ LinearMap.ker (s ^ k) := by
    intro i w hw
    rw [LinearMap.mem_ker] at hw ⊢
    have := congrArg (fun f : Module.End ℂ V => f w) (hkc i).eq
    simp only [Module.End.mul_apply] at this
    rw [this, hw, map_zero]
  have h' : ∀ i, ∀ w ∈ LinearMap.range (s ^ k), a i w ∈ LinearMap.range (s ^ k) := by
    rintro i _ ⟨u, rfl⟩
    refine ⟨a i u, ?_⟩
    have := congrArg (fun f : Module.End ℂ V => f u) (hkc i).eq
    simpa only [Module.End.mul_apply] using this
  by_cases hr : LinearMap.range (s ^ k) = ⊥
  ·
    have hnil : IsNilpotent s := ⟨k, LinearMap.range_eq_bot.mp hr⟩
    set b : Fin (l + 1) → Module.End ℂ V := Fin.cons s (fun i : Fin l => a i.succ) with hb
    have hadj : Algebra.adjoin ℂ (Set.range b) = Algebra.adjoin ℂ (Set.range a) :=
      adjoin_shift a μ
    have hb0 : b 0 = s := rfl
    have hbs : ∀ i : Fin l, b i.succ = a i.succ := fun i => rfl
    have hbc : ∀ i j, Commute (b i) (b j) := by
      intro i j
      refine Fin.cases ?_ (fun i' => ?_) i <;> refine Fin.cases ?_ (fun j' => ?_) j
      · exact Commute.refl _
      · rw [hb0, hbs]; exact hsc _
      · rw [hb0, hbs]; exact (hsc _).symm
      · rw [hbs, hbs]; exact hc _ _
    have hmem : ∀ c ∈ Subalgebra.toSubmodule (Algebra.adjoin ℂ (Set.range b)), Commute c s := by
      intro c hcm
      have hle : Algebra.adjoin ℂ (Set.range b) ≤ Subalgebra.centralizer ℂ {s} := by
        apply Algebra.adjoin_le
        rintro _ ⟨i, rfl⟩
        rw [SetLike.mem_coe, Subalgebra.mem_centralizer_iff]
        rintro g rfl
        exact hbc 0 i
      have := hle hcm
      rw [Subalgebra.mem_centralizer_iff] at this
      exact (this s rfl).symm
    have h1 := GlobalTheory.CompanionTheory.CommStep.comm_step V l b hbc (2 * N - 1)
    have h2 := GlobalTheory.CompanionTheory.CommNil.succ_mul_finrank_map_le V s hnil (2 * N - 1) _ hmem
    rw [hb0] at h1
    have h3 := hK V (fun i : Fin l => b i.succ) (fun i j => hbc _ _)
    rw [hadj] at h1 h2
    exact arith_nil N _ _ _ _ K hN h1 h2 h3
  ·
    have hker : LinearMap.ker (s ^ k) ≠ ⊥ := by
      intro hbot
      have hmem : v ∈ LinearMap.ker (s ^ k) := by
        obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
        rw [LinearMap.mem_ker, pow_succ, Module.End.mul_apply, hsv, map_zero]
      rw [hbot, Submodule.mem_bot] at hmem
      exact hv.2 hmem
    have hsum := Submodule.finrank_add_eq_of_isCompl hcompl
    have p1 : Module.finrank ℂ (LinearMap.ker (s ^ k)) ≠ 0 := fun h0 =>
      hker (Submodule.finrank_eq_zero.mp h0)
    have p2 : Module.finrank ℂ (LinearMap.range (s ^ k)) ≠ 0 := fun h0 =>
      hr (Submodule.finrank_eq_zero.mp h0)
    have hres : ∀ (W : Submodule ℂ V) (g : ∀ i, ∀ w ∈ W, a i w ∈ W) (i j : Fin (l + 1)),
        Commute (((a i).restrict (g i) : Module.End ℂ W)) ((a j).restrict (g j)) := by
      intro W g i j
      show ((a i).restrict (g i) : Module.End ℂ W) * (a j).restrict (g j) =
        ((a j).restrict (g j) : Module.End ℂ W) * (a i).restrict (g i)
      refine LinearMap.ext fun w => Subtype.ext ?_
      have := congrArg (fun f : Module.End ℂ V => f w.1) (hc i j).eq
      simpa [Module.End.mul_apply] using this
    have i1 := ih (Module.finrank ℂ (LinearMap.ker (s ^ k))) (by omega) (LinearMap.ker (s ^ k))
      (fun i => ((a i).restrict (h i) : Module.End ℂ (LinearMap.ker (s ^ k)))) rfl (hres _ h)
    have i2 := ih (Module.finrank ℂ (LinearMap.range (s ^ k))) (by omega) (LinearMap.range (s ^ k))
      (fun i => ((a i).restrict (h' i) : Module.End ℂ (LinearMap.range (s ^ k)))) rfl (hres _ h')
    have h3 := GlobalTheory.CompanionTheory.CommSplit.finrank_adjoin_le_add V (l + 1) a _ _ hcompl h h'
    rw [← hsum]
    calc N * Module.finrank ℂ (Algebra.adjoin ℂ (Set.range a))
        ≤ N * (_ + _) := Nat.mul_le_mul_left _ h3
      _ = _ + _ := Nat.mul_add _ _ _
      _ ≤ _ := Nat.add_le_add i1 i2
      _ ≤ _ := by nlinarith [Nat.zero_le (Module.finrank ℂ (LinearMap.ker (s ^ k)) *
            Module.finrank ℂ (LinearMap.range (s ^ k)))]

theorem stComm : StComm := by
  unfold StComm
  intro l
  induction l with
  | zero =>
    intro N
    refine ⟨N, ?_⟩
    intro V _ _ _ a _
    have hr : Set.range a = ∅ := Set.range_eq_empty a
    rw [hr, Algebra.adjoin_empty]
    rcases subsingleton_or_nontrivial V with hV | hV
    · have : Module.finrank ℂ (⊥ : Subalgebra ℂ (Module.End ℂ V)) = 0 :=
        Module.finrank_zero_of_subsingleton
      simp [this]
    · have hpos : 0 < Module.finrank ℂ V := Module.finrank_pos
      rw [Subalgebra.finrank_bot]
      nlinarith
  | succ l ih =>
    intro N
    rcases Nat.eq_zero_or_pos N with rfl | hN
    · exact ⟨0, fun V _ _ _ a _ => by simp⟩
    obtain ⟨K, hK⟩ := ih (4 * N ^ 2)
    exact ⟨K, fun V _ _ _ a hc => positionOne_invariantIntegral_exchange_step l N K hN hK _ V a rfl hc⟩

end GlobalTheory.CompanionTheory.Bernstein
