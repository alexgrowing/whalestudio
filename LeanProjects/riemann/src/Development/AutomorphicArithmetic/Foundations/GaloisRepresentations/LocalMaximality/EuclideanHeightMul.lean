import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalMaximality.LiftFactorization
open KaehlerDifferential GlobalTheory.CechDR GlobalTheory.PD GlobalTheory.WH GlobalTheory.W1 UpperTheory.Gal.productCup_of_system
open scoped TensorProduct

set_option autoImplicit false

noncomputable section

namespace UpperTheory.Gal.productCup_of_system

section SlopeTestRemainingChoices

variable {S E : Type} [CommRing S] [Algebra ℂ S] [AddCommGroup E] [Module ℂ E]
  (act : S →ₐ[ℂ] Module.End ℂ E) (R : Subalgebra ℂ S) (M : Submodule ℂ E)

@[reducible] private def modR (h : Stab act R M) : Module R M where
  smul r m := ⟨act r m, h r r.2 m m.2⟩
  one_smul m := Subtype.ext (by
    change act ((1 : R) : S) (m : E) = m
    simp)
  mul_smul a b m := Subtype.ext (by
    change act ((a * b : R) : S) (m : E) = act a (act b m)
    simp [Module.End.mul_apply])
  smul_zero a := Subtype.ext (by
    change act a ((0 : M) : E) = 0
    simp)
  smul_add a m m' := Subtype.ext (by
    change act a ((m + m' : M) : E) = act a m + act a m'
    simp)
  add_smul a b m := Subtype.ext (by
    change act ((a + b : R) : S) (m : E) = act a m + act b m
    simp)
  zero_smul m := Subtype.ext (by
    change act ((0 : R) : S) (m : E) = 0
    simp)

variable {act R M}

private theorem mem_ofList_iff [Module R M] [IsScalarTower ℂ R M] (hsm : ∀ (a : R) (m : M), ((a • m : M) : E) = act a m)
    {d : ℕ} (f : Fin d → R) (k : ℕ) (x : M) :
    x ∈ (Ideal.ofList ((List.ofFn f).take k) • ⊤ : Submodule R M) ↔
      (x : E) ∈ sm act M ((fun j => (f j : S)) '' {j | j.val < k}) := by
  constructor
  · intro hx
    refine Submodule.smul_induction_on hx ?_ ?_
    · intro a ha n _
      have : ∀ n : M, ((a • n : M) : E) ∈ sm act M ((fun j => (f j : S)) '' {j | j.val < k}) := by
        refine Submodule.span_induction ?_ ?_ ?_ ?_ ha
        · intro b hb n
          obtain ⟨i, hi, rfl⟩ := List.mem_take_iff_getElem.1 hb
          have hi' : i < k := lt_of_lt_of_le hi (min_le_left _ _)
          have hid : i < d := by
            have := lt_of_lt_of_le hi (min_le_right _ _)
            simpa using this
          rw [hsm]
          refine Submodule.mem_iSup_of_mem ((f ⟨i, hid⟩ : S)) (Submodule.mem_iSup_of_mem
            ⟨⟨i, hid⟩, hi', rfl⟩ ?_)
          simpa using ⟨n, n.2, rfl⟩
        · intro n
          simp
        · intro a b _ _ ha hb n
          rw [add_smul]
          simpa using Submodule.add_mem _ (ha n) (hb n)
        · intro a b _ hb n
          rw [smul_eq_mul, mul_comm, mul_smul]
          exact hb (a • n)
      exact this n
    · intro a b ha hb
      simpa using Submodule.add_mem _ ha hb
  · intro hx
    have hle : sm act M ((fun j => (f j : S)) '' {j | j.val < k}) ≤
        ((Ideal.ofList ((List.ofFn f).take k) • ⊤ : Submodule R M).restrictScalars ℂ).map M.subtype := by
      refine iSup₂_le ?_
      rintro _ ⟨j, hj, rfl⟩ _ ⟨m, hm, rfl⟩
      have hmem : f j • (⟨m, hm⟩ : M) ∈ (Ideal.ofList ((List.ofFn f).take k) • ⊤ : Submodule R M) := by
        refine Submodule.smul_mem_smul (Ideal.subset_span ?_) Submodule.mem_top
        refine List.mem_take_iff_getElem.2 ⟨j.val, ?_, by simp⟩
        simpa using hj
      exact Submodule.mem_map.2 ⟨_, (Submodule.restrictScalars_mem ℂ _ _).2 hmem, hsm _ _⟩
    obtain ⟨y, hy, hyx⟩ := Submodule.mem_map.1 (hle hx)
    have hyx' : y = x := Subtype.ext hyx
    rw [← hyx']
    exact (Submodule.restrictScalars_mem ℂ _ _).1 hy

private theorem wd_coe [Module R M] [IsScalarTower ℂ R M]
    (hsm : ∀ (a : R) (m : M), ((a • m : M) : E) = act a m) {κ : Type} [LinearOrder κ] (r : κ → R)
    (c : Finset κ → M) (t : Finset κ) :
    ((wd (fun l => Algebra.lsmul ℂ ℂ M (r l)) c t : M) : E) =
      wd (fun l => act (r l)) (fun s => (c s : E)) t := by
  simp [wd, hsm]

private theorem koszulExact_of_regular (hK : KoszulExactBelowLengthOfWeaklyRegular) {κ : Type} [LinearOrder κ] [Fintype κ] (r : κ → S) {d : ℕ}
    (f : Fin d → S) (hS : Stab act R M) (hr : ∀ l, r l ∈ R) (hReg : Reg act M f)
    (hf : ∀ j, InSp R r (f j)) : KE (kos act M r) d := by
  letI := modR act R M hS
  have hsm : ∀ (a : R) (m : M), ((a • m : M) : E) = act a m := fun _ _ => rfl
  haveI : IsScalarTower ℂ R M := ⟨fun c a m => Subtype.ext (by
    change act ((c • a : R) : S) (m : E) = c • act a m
    simp)⟩
  have hfR : ∀ j, f j ∈ R := by
    intro j
    obtain ⟨a, ha, h⟩ := hf j
    rw [h]
    exact sum_mem fun l _ => R.mul_mem (ha l) (hr l)
  let r' : κ → R := fun l => ⟨r l, hr l⟩
  let f' : Fin d → R := fun j => ⟨f j, hfR j⟩
  have hreg : RingTheory.Sequence.IsWeaklyRegular M (List.ofFn f') := by
    refine ⟨fun i hi => ?_⟩
    have hid : i < d := by simpa using hi
    rw [isSMulRegular_on_quot_iff_lsmul_comap_le]
    intro x hx
    rw [Submodule.mem_comap, LinearMap.lsmul_apply, mem_ofList_iff hsm] at hx
    rw [mem_ofList_iff hsm]
    have hget : (List.ofFn f')[i] = f' ⟨i, hid⟩ := by simp
    rw [hget, hsm] at hx
    exact hReg ⟨i, hid⟩ x x.2 hx
  have hsp : ∀ g ∈ List.ofFn f', InSp (⊤ : Subalgebra ℂ R) r' g := by
    intro g hg
    obtain ⟨j, rfl⟩ := (List.mem_ofFn' _ _).1 hg
    obtain ⟨a, ha, h⟩ := hf j
    refine ⟨fun l => ⟨a l, ha l⟩, fun _ => trivial, Subtype.ext ?_⟩
    simpa [f', r'] using h
  have key := hK d R M κ r' (List.ofFn f') (by simp) hreg hsp
  intro m hm c hc
  obtain ⟨hcC, hcD⟩ := hc
  have hcM : ∀ s, c s ∈ M := by
    intro s
    have : c s ∈ if (s.card : ℤ) = m then M else ⊥ := hcC s (Set.mem_univ s)
    split_ifs at this with h
    · exact this
    · rw [Submodule.mem_bot] at this
      exact this ▸ M.zero_mem
  let c' : Finset κ → M := fun s => ⟨c s, hcM s⟩
  have hc' : c' ∈ (kos (Algebra.lsmul ℂ ℂ M) (⊤ : Submodule ℂ M) r').Z m := by
    constructor
    · intro s _
      have : c s ∈ if (s.card : ℤ) = m then M else ⊥ := hcC s (Set.mem_univ s)
      change c' s ∈ if (s.card : ℤ) = m then (⊤ : Submodule ℂ M) else ⊥
      split_ifs at this ⊢ with h
      · trivial
      · rw [Submodule.mem_bot] at this ⊢
        exact Subtype.ext this
    · refine LinearMap.mem_ker.2 (funext fun t => Subtype.ext ?_)
      have := wd_coe hsm r' c' t
      exact this.trans (congrFun (LinearMap.mem_ker.1 hcD) t)
  obtain ⟨y, hy, hyc⟩ := key m hm hc'
  refine ⟨fun s => (y s : E), ?_, ?_⟩
  · intro s _
    have : y s ∈ if (s.card : ℤ) = m - 1 then (⊤ : Submodule ℂ M) else ⊥ := hy s (Set.mem_univ s)
    change (y s : E) ∈ if (s.card : ℤ) = m - 1 then M else ⊥
    split_ifs at this ⊢ with h
    · exact (y s).2
    · rw [Submodule.mem_bot] at this ⊢
      rw [this]
      rfl
  · funext t
    have h1 := wd_coe hsm r' y t
    have h2 : ((wd (fun l => Algebra.lsmul ℂ ℂ M (r' l)) y t : M) : E) = c t :=
      congrArg (fun z : Finset κ → M => ((z t : M) : E)) hyc
    exact h1.symm.trans h2

end SlopeTestRemainingChoices

end UpperTheory.Gal.productCup_of_system

end

theorem UpperTheory.Gal.productCup_of_system.firstCohomologyBound_of_boundaryBound :
    KoszulExactBelowLengthOfWeaklyRegular → K1 := by
  intro hK S E _ _ _ _ act κ _ _ R M r d f hS hr hReg hf
  exact koszulExact_of_regular hK r f hS hr hReg hf
