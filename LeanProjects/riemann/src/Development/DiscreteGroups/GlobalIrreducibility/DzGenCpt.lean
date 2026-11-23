import Mathlib
import Development.DiscreteGroups.GlobalIrreducibility.DzGenMat

noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel Matrix

namespace DiscreteGroups.sglob.DzType

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {m : ℕ}

theorem exists_scale (X : Finset k) :
    ∃ t : kˣ, valuation k (t : k) ≤ 1 ∧ ∀ x ∈ X, valuation k ((t : k) * x) ≤ 1 := by
  classical
  have hne : ∀ x : k, ¬ valuation k x ≤ 1 → x ≠ 0 := fun x h h0 => h (by simp [h0])
  let f : k → kˣ := fun x => if h : valuation k x ≤ 1 then 1 else (Units.mk0 x (hne x h))⁻¹
  have hf1 : ∀ x, valuation k ((f x : kˣ) : k) ≤ 1 := by
    intro x
    by_cases h : valuation k x ≤ 1
    · simp [f, h]
    · simp only [f, dif_neg h, Units.val_inv_eq_inv_val, Units.val_mk0, map_inv₀]
      push Not at h
      exact inv_le_one_of_one_le₀ h.le
  have hf2 : ∀ x, valuation k ((f x : kˣ) * x) ≤ 1 := by
    intro x
    by_cases h : valuation k x ≤ 1
    · simpa [f, h] using h
    · simp only [f, dif_neg h, Units.val_inv_eq_inv_val, Units.val_mk0]
      rw [inv_mul_cancel₀ (hne x h), map_one]
  refine ⟨∏ x ∈ X, f x, ?_, fun y hy => ?_⟩
  · rw [Units.coe_prod, map_prod]
    exact Finset.prod_le_one' fun x _ => hf1 x
  · rw [Units.coe_prod, ← Finset.mul_prod_erase X (fun x => ((f x : kˣ) : k)) hy, mul_assoc, mul_comm, mul_assoc,
      map_mul]
    have h1 : valuation k (∏ x ∈ X.erase y, ((f x : kˣ) : k)) ≤ 1 := by
      rw [map_prod]; exact Finset.prod_le_one' fun x _ => hf1 x
    calc valuation k (∏ x ∈ X.erase y, ((f x : kˣ) : k)) * valuation k (y * (f y : k))
        ≤ 1 * 1 := by gcongr; rw [mul_comm]; exact hf2 y
      _ = 1 := one_mul 1

theorem isClosed_unipB : IsClosed (unipB k (Fin m) : Set (GL (Fin m) k)) := by
  obtain ⟨_, _⟩ := GlobalTheory.SplitWeil.Model.secondCountable_and_t2_local_field (k := k)
  have hc : ∀ i j : Fin m, Continuous fun g : GL (Fin m) k => (g : Matrix (Fin m) (Fin m) k) i j :=
    fun i j => (Units.continuous_val (M := Matrix (Fin m) (Fin m) k)).matrix_elem i j
  have e : (unipB k (Fin m) : Set (GL (Fin m) k)) =
      (⋂ i : Fin m, ⋂ j : Fin m, {g : GL (Fin m) k | j < i → (g : Matrix (Fin m) (Fin m) k) i j = 0}) ∩
        ⋂ i : Fin m, {g : GL (Fin m) k | (g : Matrix (Fin m) (Fin m) k) i i = 1} := by
    ext g
    simp only [SetLike.mem_coe, mem_unipB, Set.mem_inter_iff, Set.mem_iInter, Set.mem_setOf_eq]
  rw [e]
  refine (isClosed_iInter fun i => isClosed_iInter fun j => ?_).inter (isClosed_iInter fun i => isClosed_eq (hc i i) continuous_const)
  by_cases hji : j < i
  · simpa [hji] using isClosed_eq (hc i j) continuous_const
  · simp [hji]

theorem diag_conj_apply (t : Fin m → kˣ) (g : GL (Fin m) k) (i j : Fin m) :
    ((diagT k (Fin m) t * g * (diagT k (Fin m) t)⁻¹ : GL (Fin m) k) : Matrix (Fin m) (Fin m) k) i j =
      (t i : k) * (g : Matrix (Fin m) (Fin m) k) i j * ((t j)⁻¹ : kˣ) := by
  rw [← map_inv, Units.val_mul, Units.val_mul, val_diagT, val_diagT, Matrix.mul_diagonal, Matrix.diagonal_mul]
  simp

theorem diag_conj_mem_unipB (t : Fin m → kˣ) {g : GL (Fin m) k} (hg : g ∈ unipB k (Fin m)) :
    diagT k (Fin m) t * g * (diagT k (Fin m) t)⁻¹ ∈ unipB k (Fin m) := by
  refine (mem_unipB _).2 ⟨fun i j hij => ?_, fun i => ?_⟩
  · rw [diag_conj_apply, ((mem_unipB _).1 hg).1 i j hij]; simp
  · rw [diag_conj_apply, ((mem_unipB _).1 hg).2 i]; simp

theorem exists_compact_unip (F : Finset (GL (Fin m) k)) (hF : ∀ u ∈ F, u ∈ unipB k (Fin m)) :
    ∃ C : Subgroup (GL (Fin m) k), IsCompact (C : Set (GL (Fin m) k)) ∧ C ≤ unipB k (Fin m) ∧ ∀ u ∈ F, u ∈ C := by
  classical
  obtain ⟨t, ht1, ht⟩ := exists_scale ((F ×ˢ (Finset.univ ×ˢ Finset.univ)).image
    fun x : GL (Fin m) k × Fin m × Fin m => (x.1 : Matrix (Fin m) (Fin m) k) x.2.1 x.2.2)
  let d : GL (Fin m) k := diagT k (Fin m) fun i => t ^ (i : ℕ)
  let C : Subgroup (GL (Fin m) k) := (unipB k (Fin m) ⊓ KO k (Fin m)).map (MulAut.conj d).toMonoidHom
  refine ⟨C, ?_, ?_, fun u hu => ?_⟩
  · rw [Subgroup.coe_map, Subgroup.coe_inf]
    refine (GlobalTheory.SplitFlip.isCompact_KO.inter_left isClosed_unipB).image ?_
    exact (continuous_const.mul continuous_id).mul continuous_const
  · rintro _ ⟨g, hg, rfl⟩
    exact diag_conj_mem_unipB _ hg.1
  · have e : diagT k (Fin m) (fun i => (t ^ (i : ℕ))⁻¹) = d⁻¹ := by rw [← map_inv]; rfl
    have hU : d⁻¹ * u * d ∈ unipB k (Fin m) := by
      have := diag_conj_mem_unipB (fun i => (t ^ (i : ℕ))⁻¹) (hF u hu)
      rwa [e, inv_inv] at this
    have hent : ∀ i j, ((d⁻¹ * u * d : GL (Fin m) k) : Matrix (Fin m) (Fin m) k) i j =
        ((t : k) ^ (i : ℕ))⁻¹ * (u : Matrix (Fin m) (Fin m) k) i j * (t : k) ^ (j : ℕ) := by
      intro i j
      have e2 : d⁻¹ * u * d = diagT k (Fin m) (fun i => (t ^ (i : ℕ))⁻¹) * u *
          (diagT k (Fin m) (fun i => (t ^ (i : ℕ))⁻¹))⁻¹ := by rw [e, inv_inv]
      rw [e2, diag_conj_apply]
      simp
    refine ⟨d⁻¹ * u * d, ⟨hU, mem_KO_of_unip hU fun i j => ?_⟩, ?_⟩
    · rw [hent]
      rcases lt_trichotomy i j with hij | rfl | hij
      · obtain ⟨c, hc⟩ : ∃ c : ℕ, (j : ℕ) = i + (c + 1) := ⟨j - i - 1, by rw [Fin.lt_def] at hij; omega⟩
        have ht0 : (t : k) ^ (i : ℕ) ≠ 0 := pow_ne_zero _ t.ne_zero
        have e3 : ((t : k) ^ (i : ℕ))⁻¹ * (u : Matrix (Fin m) (Fin m) k) i j * (t : k) ^ (j : ℕ) =
            (t : k) ^ c * ((t : k) * (u : Matrix (Fin m) (Fin m) k) i j) := by
          rw [hc, pow_add, pow_succ]
          calc ((t : k) ^ (i : ℕ))⁻¹ * (u : Matrix (Fin m) (Fin m) k) i j * ((t : k) ^ (i : ℕ) * ((t : k) ^ c * t))
              = (((t : k) ^ (i : ℕ))⁻¹ * (t : k) ^ (i : ℕ)) * ((t : k) ^ c * ((t : k) * (u : Matrix (Fin m) (Fin m) k) i j)) := by ring
            _ = _ := by rw [inv_mul_cancel₀ ht0, one_mul]
        rw [e3, map_mul, map_pow]
        exact mul_le_one' (pow_le_one' ht1 c) (ht _ (Finset.mem_image.2 ⟨(u, i, j), by simp [hu], rfl⟩))
      · rw [((mem_unipB _).1 (hF u hu)).2 i, mul_one, inv_mul_cancel₀ (pow_ne_zero _ t.ne_zero), map_one]
      · rw [((mem_unipB _).1 (hF u hu)).1 i j hij]; simp
    · simp [MulAut.conj_apply, d, mul_assoc]

end DiscreteGroups.sglob.DzType
