import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ClassCounting.LemmaKOfSteps

open NumberField IsDedekindDomain UpperTheory.V UpperTheory.V.KL UpperTheory.V.ZK

namespace UpperTheory.V.ZK.SimplicialChains

variable (A : Type) [CommRing A]

private theorem bd_single (G : Type) [Group G] (m : ℕ) (g : Fin (m + 1) → G) (a : A) :
    bd A G m (Finsupp.single g a) = Finsupp.single (fun i => g i.succ) a +
      ∑ j : Fin (m + 1), ((-1 : A) ^ ((j : ℕ) + 1)) • Finsupp.single (Fin.contractNth j (· * ·) g) a := by
  simp only [bd, Finsupp.linearCombination_single, smul_add, Finset.smul_sum, Finsupp.smul_single_one]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finsupp.smul_single, Finsupp.smul_single, smul_eq_mul, smul_eq_mul, mul_comm]

private theorem cm_single {G H : Type} [Group G] [Group H] (f : G →* H) (m : ℕ) (g : Fin m → G) (a : A) :
    cm A f m (Finsupp.single g a) = Finsupp.single (fun i => f (g i)) a := by
  simp [cm]

private theorem bd_eq (G : Type) [Group G] (m : ℕ) (z : Ch A G (m + 1)) :
    bd A G m z = groupHomology.inhomogeneousChains.d (Rep.trivial A G A) m z := by
  induction z using Finsupp.induction_linear with
  | zero => simp
  | add x y hx hy => rw [map_add, hx, hy, map_add]
  | single g a =>
    rw [bd_single, groupHomology.inhomogeneousChains.d_single]
    simp

private theorem bd_bd (G : Type) [Group G] (m : ℕ) (z : Ch A G (m + 2)) :
    bd A G m (bd A G (m + 1) z) = 0 := by
  rw [bd_eq A G (m + 1) z, bd_eq]
  have h := groupHomology.inhomogeneousChains.d_comp_d (Rep.trivial A G A) m
  simpa using LinearMap.congr_fun (congrArg (fun φ => ModuleCat.Hom.hom φ) h) z

private theorem bd_cm (G H : Type) [Group G] [Group H] (f : G →* H) (m : ℕ) (z : Ch A G (m + 1)) :
    bd A H m (cm A f (m + 1) z) = cm A f m (bd A G m z) := by
  induction z using Finsupp.induction_linear with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | single g a =>
    rw [cm_single, bd_single, bd_single, map_add, cm_single, map_sum]
    congr 1
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_smul, cm_single]
    congr 2
    funext l
    simp only [Fin.contractNth]
    split_ifs <;> simp [map_mul]

private theorem cm_prism (G H : Type) [Group G] [Group H] (f : G →* H) (k : G) (m : ℕ) (z : Ch A G m) :
    cm A f (m + 1) (prism A k m z) = prism A (f k) m (cm A f m z) := by
  have key : ∀ (g : Fin m → G) (i : Fin (m + 1)),
      (fun j => f (Fin.insertNth (α := fun _ => G) i k
        (fun j : Fin m => if (j : ℕ) < (i : ℕ) then g j else k⁻¹ * g j * k) j)) =
        Fin.insertNth (α := fun _ => H) i (f k)
          (fun j : Fin m => if (j : ℕ) < (i : ℕ) then f (g j) else (f k)⁻¹ * f (g j) * f k) := by
    intro g i
    funext j
    refine Fin.succAboveCases i ?_ (fun l => ?_) j
    · simp
    · simp only [Fin.insertNth_apply_succAbove]
      split_ifs <;> simp [map_mul]
  induction z using Finsupp.induction_linear with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | single g a =>
    rw [cm_single]
    simp only [prism, Finsupp.linearCombination_single, Finset.smul_sum, map_sum, map_smul, cm_single]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [key g i]

private theorem bd_triv (G : Type) [Group G] [Subsingleton G] (m : ℕ) (a : A) :
    bd A G m (Finsupp.single 1 a) =
      Finsupp.single 1 ((1 + ∑ j ∈ Finset.range (m + 1), (-1 : A) ^ (j + 1)) * a) := by
  rw [bd_single]
  ext x
  simp [Finsupp.finset_sum_apply, Finsupp.single_apply, eq_iff_true_of_subsingleton,
    Fin.sum_univ_eq_sum_range (fun j => (-1 : A) ^ (j + 1) * a), add_mul, Finset.sum_mul]

private theorem coef (m : ℕ) : (1 + ∑ j ∈ Finset.range (m + 1), (-1 : A) ^ (j + 1)) +
    (1 + ∑ j ∈ Finset.range (m + 1 + 1), (-1 : A) ^ (j + 1)) = 1 := by
  induction m with
  | zero => norm_num [Finset.sum_range_succ]
  | succ n ih =>
    rw [Finset.sum_range_succ _ (n + 1 + 1), Finset.sum_range_succ _ (n + 1)]
    rw [Finset.sum_range_succ _ (n + 1)] at ih
    linear_combination ih

private theorem triv (G : Type) [Group G] [Subsingleton G] (m : ℕ) (z : Ch A G (m + 1)) (hz : Cyc z) : Bd z := by
  have hz1 : z = Finsupp.single 1 (z 1) := by
    ext x
    obtain rfl : x = 1 := Subsingleton.elim _ _
    simp
  have h0 : (1 + ∑ j ∈ Finset.range (m + 1), (-1 : A) ^ (j + 1)) * z 1 = 0 := by
    have h := hz
    unfold Cyc at h
    rw [hz1, bd_triv] at h
    simpa using congrArg (fun w => w 1) h
  show z ∈ (bd A G (m + 1)).range
  refine LinearMap.mem_range.mpr ⟨Finsupp.single 1 (z 1), ?_⟩
  rw [bd_triv]
  conv_rhs => rw [hz1]
  congr 1
  linear_combination (z 1) * coef A m - h0

end UpperTheory.V.ZK.SimplicialChains

open UpperTheory.V.ZK.SimplicialChains in
theorem UpperTheory.V.ZK.sChain :
    UpperTheory.V.ZK.SChain := by
  intro A _
  refine ⟨bd_bd A, bd_cm A, fun G H K _ _ _ f g m z => ?_, cm_prism A, triv A⟩
  simp only [cm, Finsupp.lmapDomain_apply]
  rw [← Finsupp.mapDomain_comp]
  rfl
