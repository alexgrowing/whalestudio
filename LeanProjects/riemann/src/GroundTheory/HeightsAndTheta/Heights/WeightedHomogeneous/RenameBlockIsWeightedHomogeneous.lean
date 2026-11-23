import Mathlib
import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.Statements
import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.SectionInjectivityHypothesesProjectiveLine
import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.OneBlockIdealEqComapProjIdeal
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Close

open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Geo (secM sec IsMultiHomog)

noncomputable section

variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ι → ℕ}

theorem weight_coordDeg_apply (d : Coord n →₀ ℕ) (k : ι) :
    Finsupp.weight (coordDeg n) d k = ∑ i, d ⟨k, i⟩ := by
  classical
  rw [Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp), Finset.sum_apply,
    Fintype.sum_sigma]
  rw [Finset.sum_eq_single k]
  · simp [coordDeg]
  · intro b _ hb
    simp [coordDeg, Ne.symm hb]
  · simp

theorem weight_one_eq_sum (d : Coord n →₀ ℕ) :
    Finsupp.weight 1 d = ∑ k, Finsupp.weight (coordDeg n) d k := by
  simp_rw [weight_coordDeg_apply]
  rw [Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp), ← Fintype.sum_sigma]
  simp

omit [Fintype ι] [DecidableEq ι] in

theorem weight_one_fin {r : ℕ} (d : Fin r →₀ ℕ) : Finsupp.weight 1 d = ∑ i, d i := by
  simp [Finsupp.weight_apply, Finsupp.sum_fintype]

omit [Fintype ι] [DecidableEq ι] in

theorem blockInj_injective (k₀ : ι) :
    Function.Injective (fun i : Fin (n k₀ + 1) ↦ (⟨k₀, i⟩ : Coord n)) := fun i j h ↦ by
  simpa using h

theorem isMultiHomog_iff (f : MvPolynomial (Coord n) ℤ) (a : ι → ℕ) :
    IsMultiHomog (ι := fun k ↦ Fin (n k + 1)) f a ↔ IsWeightedHomogeneous (coordDeg n) f a := by
  constructor
  · intro h d hd
    funext k
    rw [weight_coordDeg_apply]
    exact h d (mem_support_iff.mpr hd) k
  · intro h d hd k
    rw [← weight_coordDeg_apply, h (mem_support_iff.mp hd)]

theorem exists_rename_of_block (k₀ : ι) (m : ℕ) (f : MvPolynomial (Coord n) ℤ)
    (hf : IsWeightedHomogeneous (coordDeg n) f (m • Pi.single k₀ 1)) :
    ∃ g : MvPolynomial (Fin (n k₀ + 1)) ℤ, g.IsHomogeneous m ∧
      rename (fun i ↦ (⟨k₀, i⟩ : Coord n)) g = f := by
  obtain ⟨g, rfl⟩ := exists_rename_eq_of_vars_subset_range f _ (blockInj_injective k₀) (by
    rintro ⟨k, i⟩ hv
    obtain ⟨d, hd, hdv⟩ := (mem_vars_iff_mem_support _).mp hv
    have h := congr_fun (hf (mem_support_iff.mp hd)) k
    rw [weight_coordDeg_apply] at h
    by_cases hk : k = k₀
    · subst hk
      exact ⟨i, rfl⟩
    · exfalso
      have h0 : ∑ j, d ⟨k, j⟩ = 0 := by simpa [Pi.single_apply, hk] using h
      exact (Finsupp.mem_support_iff.mp hdv)
        (Finset.sum_eq_zero_iff.mp h0 i (Finset.mem_univ _)))
  refine ⟨g, ?_, rfl⟩
  rw [← IsHomogeneous.rename_isHomogeneous_iff (blockInj_injective k₀)]
  intro d hd
  rw [weight_one_eq_sum, hf hd]
  simp [Pi.single_apply, mul_ite]

theorem rename_block_isWeightedHomogeneous (k₀ : ι) {N : ℕ} {g : MvPolynomial (Fin (n k₀ + 1)) ℤ}
    (hg : g.IsHomogeneous N) :
    IsWeightedHomogeneous (coordDeg n) (rename (fun i ↦ (⟨k₀, i⟩ : Coord n)) g) (N • Pi.single k₀ 1) := by
  classical
  intro d hd
  rw [← mem_support_iff, support_rename_of_injective (blockInj_injective k₀), Finset.mem_image] at hd
  obtain ⟨d', hd', rfl⟩ := hd
  have hN : ∑ i, d' i = N := by rw [← weight_one_fin]; exact hg (mem_support_iff.mp hd')
  funext k
  rw [weight_coordDeg_apply]
  by_cases hk : k = k₀
  · subst hk
    simp only [Finsupp.mapDomain_apply (blockInj_injective k), hN]
    simp
  · have h0 : ∀ i, Finsupp.mapDomain (fun i ↦ (⟨k₀, i⟩ : Coord n)) d' ⟨k, i⟩ = 0 := fun i ↦
      Finsupp.mapDomain_of_notMem_range _ _ (by rintro ⟨j, hj⟩; exact hk (congrArg Sigma.fst hj).symm)
    simp [h0, hk]

theorem isWeightedHomogeneous_unit_iff {r m : ℕ} (f : MvPolynomial (Coord (fun _ : Unit ↦ r)) ℤ) :
    IsWeightedHomogeneous (coordDeg (fun _ : Unit ↦ r)) f (fun _ ↦ m) ↔ f.IsHomogeneous m := by
  have hw : ∀ d : Coord (fun _ : Unit ↦ r) →₀ ℕ,
      Finsupp.weight (coordDeg (fun _ : Unit ↦ r)) d = fun _ ↦ Finsupp.weight 1 d := by
    intro d
    funext u
    rw [weight_one_eq_sum, Fintype.sum_unique]
  constructor
  · intro h d hd
    exact congr_fun ((hw d).symm.trans (h hd)) ()
  · intro h d hd
    rw [hw d, h hd]

theorem forms_of_block (k₀ : ι) (m : ℕ) (f : MvPolynomial (Coord n) ℤ)
    (hf : IsWeightedHomogeneous (coordDeg n) f (m • Pi.single k₀ 1)) :
    ∃ f' : MvPolynomial (Coord (fun _ : Unit ↦ n k₀)) ℤ,
      IsWeightedHomogeneous (coordDeg (fun _ : Unit ↦ n k₀)) f' (fun _ ↦ m) ∧
        rename (Heights.blockIncl k₀) f' = f := by
  obtain ⟨g, hg, rfl⟩ := exists_rename_of_block k₀ m f hf
  refine ⟨rename (blockCoordEquiv (n := n) k₀) g, ?_, ?_⟩
  · rw [isWeightedHomogeneous_unit_iff]
    exact hg.rename_isHomogeneous
  · rw [rename_rename]
    rfl

theorem secM_block (P : ArithVariety n) (k₀ : ι) (N : ℕ) :
    secM (genPt P) (N • Pi.single k₀ 1) =
      (sec ℤ (fun i : Fin (n k₀ + 1) ↦ genPt P ⟨k₀, i⟩) N).toAddSubgroup := by
  unfold secM
  congr 1
  refine le_antisymm (Submodule.span_le.mpr ?_) ?_
  · rintro _ ⟨g, hg, rfl⟩
    rw [isMultiHomog_iff] at hg
    obtain ⟨h, hh, rfl⟩ := exists_rename_of_block k₀ N g hg
    refine Submodule.mem_map.mpr ⟨h, (mem_homogeneousSubmodule N h).mpr hh, ?_⟩
    change aeval _ h = _
    rw [aeval_rename]
    rfl
  · intro x hx
    obtain ⟨h, hh, rfl⟩ := Submodule.mem_map.mp hx
    refine Submodule.subset_span ⟨rename (fun i ↦ (⟨k₀, i⟩ : Coord n)) h, ?_, ?_⟩
    · rw [isMultiHomog_iff]
      exact rename_block_isWeightedHomogeneous k₀ ((mem_homogeneousSubmodule N h).mp hh)
    · rw [aeval_rename]
      rfl

omit [Fintype ι] [DecidableEq ι] in

theorem norm_eval₂_le {r N : ℕ} (f : MvPolynomial (Fin r) ℤ) (hf : f.IsHomogeneous N)
    (w : Fin r → ℂ) :
    ‖eval₂ (Int.castRingHom ℂ) w f‖ ≤
      (∑ d ∈ f.support, ‖Int.castRingHom ℂ (f.coeff d)‖) * l2Norm w ^ N := by
  rw [eval₂_eq', Finset.sum_mul]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun d hd ↦ ?_)
  rw [norm_mul, norm_prod]
  refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
  have hdeg : ∑ i, d i = N := by rw [← weight_one_fin]; exact hf (mem_support_iff.mp hd)
  calc ∏ i, ‖w i ^ d i‖ = ∏ i, ‖w i‖ ^ d i := by simp [norm_pow]
    _ ≤ ∏ i, l2Norm w ^ d i := Finset.prod_le_prod (fun _ _ ↦ by positivity)
        fun i _ ↦ pow_le_pow_left₀ (norm_nonneg _) (norm_le_l2Norm w i) _
    _ = l2Norm w ^ N := by rw [Finset.prod_pow_eq_pow_sum, hdeg]

theorem sSup_eq_of_upperBounds_eq {s t : Set ℝ} (h : upperBounds s = upperBounds t) :
    sSup s = sSup t := by
  rcases s.eq_empty_or_nonempty with rfl | hs
  · have ht : t = ∅ := by
      by_contra ht
      obtain ⟨x, hx⟩ := Set.nonempty_iff_ne_empty.mpr ht
      have hb : x - 1 ∈ upperBounds t := by rw [← h, upperBounds_empty]; trivial
      linarith [hb hx]
    rw [ht]
  · by_cases hb : BddAbove s
    · have ht : t.Nonempty := by
        by_contra ht
        rw [Set.not_nonempty_iff_eq_empty] at ht
        obtain ⟨x, hx⟩ := hs
        have hb' : x - 1 ∈ upperBounds s := by rw [h, ht, upperBounds_empty]; trivial
        linarith [hb' hx]
      have hbt : BddAbove t := by rw [BddAbove, ← h]; exact hb
      have h1 : IsLeast (upperBounds s) (sSup s) := isLUB_csSup hs hb
      have h2 : IsLeast (upperBounds t) (sSup t) := isLUB_csSup ht hbt
      rw [h] at h1
      exact h1.unique h2
    · have hbt : ¬ BddAbove t := by rwa [BddAbove, ← h]
      rw [Real.sSup_of_not_bddAbove hb, Real.sSup_of_not_bddAbove hbt]

theorem upperBounds_eq_of_sSup_eq {s t : Set ℝ} (hs : BddAbove s) (ht : BddAbove t)
    (hne : s.Nonempty ↔ t.Nonempty) (h : sSup s = sSup t) : upperBounds s = upperBounds t := by
  rcases s.eq_empty_or_nonempty with rfl | hs'
  · have : t = ∅ := Set.not_nonempty_iff_eq_empty.mp fun h' ↦ Set.not_nonempty_empty (hne.mpr h')
    rw [this]
  · have ht' := hne.mp hs'
    ext B
    rw [mem_upperBounds, mem_upperBounds, ← csSup_le_iff hs hs', ← csSup_le_iff ht ht', h]

theorem mem_upperBounds_points (P : ArithVariety n) (k₀ : ι) (N : ℕ)
    (f : MvPolynomial (Fin (n k₀ + 1)) ℤ) (B : ℝ) :
    B ∈ upperBounds ((fun z : Cone n ℂ ↦
        ‖eval₂ (Int.castRingHom ℂ) (z k₀) f‖ / (pullFS n k₀).metric z ^ N) '' P.points ℂ) ↔
      ∀ z ∈ P.points ℂ, ‖eval₂ (Int.castRingHom ℂ) (z k₀) f‖ ≤ B * l2Norm (z k₀) ^ N := by
  rw [mem_upperBounds, Set.forall_mem_image]
  refine forall₂_congr fun z hz ↦ ?_
  rw [pullFS_metric_eq_l2Norm, div_le_iff₀ (pow_pos (vectorL2Norm_pos (hz.1 k₀)) N)]

omit [Fintype ι] in

theorem mem_upperBounds_image (P : ArithVariety n) (k₀ : ι) (N : ℕ)
    (f : MvPolynomial (Fin (n k₀ + 1)) ℤ) (B : ℝ) :
    B ∈ upperBounds ((fun w ↦ ‖eval₂ (Int.castRingHom ℂ) w f‖ / l2Norm w ^ N) '' oneBlockPoints P k₀) ↔
      ∀ w ∈ oneBlockPoints P k₀, ‖eval₂ (Int.castRingHom ℂ) w f‖ ≤ B * l2Norm w ^ N := by
  rw [mem_upperBounds, Set.forall_mem_image]
  refine forall₂_congr fun w hw ↦ ?_
  rw [div_le_iff₀ (pow_pos (vectorL2Norm_pos hw.1) N)]

theorem bddAbove_points (P : ArithVariety n) (k₀ : ι) {N : ℕ}
    {f : MvPolynomial (Fin (n k₀ + 1)) ℤ} (hf : f.IsHomogeneous N) :
    BddAbove ((fun z : Cone n ℂ ↦
        ‖eval₂ (Int.castRingHom ℂ) (z k₀) f‖ / (pullFS n k₀).metric z ^ N) '' P.points ℂ) :=
  ⟨_, (mem_upperBounds_points P k₀ N f _).mpr fun z _ ↦ norm_eval₂_le f hf (z k₀)⟩

omit [Fintype ι] in

theorem bddAbove_image (P : ArithVariety n) (k₀ : ι) {N : ℕ}
    {f : MvPolynomial (Fin (n k₀ + 1)) ℤ} (hf : f.IsHomogeneous N) :
    BddAbove ((fun w ↦ ‖eval₂ (Int.castRingHom ℂ) w f‖ / l2Norm w ^ N) '' oneBlockPoints P k₀) :=
  ⟨_, (mem_upperBounds_image P k₀ N f _).mpr fun w _ ↦ norm_eval₂_le f hf w⟩

omit [Fintype ι] in

theorem forall_points_rename (P : ArithVariety n) (k₀ : ι) (N : ℕ)
    (f : MvPolynomial (Fin (n k₀ + 1)) ℤ) (B : ℝ) :
    (∀ z ∈ P.points ℂ, ‖evalCone z (rename (Heights.blockIncl k₀)
        (rename (blockCoordEquiv (n := n) k₀) f))‖ ≤ B * l2Norm (z k₀) ^ N) ↔
      ∀ z ∈ P.points ℂ, ‖eval₂ (Int.castRingHom ℂ) (z k₀) f‖ ≤ B * l2Norm (z k₀) ^ N := by
  refine forall₂_congr fun z _ ↦ ?_
  rw [rename_rename, evalCone, eval₂_rename]
  rfl

omit [Fintype ι] in

theorem forall_conePoints_rename (P : ArithVariety n) (k₀ : ι) (N : ℕ)
    (f : MvPolynomial (Fin (n k₀ + 1)) ℤ) (B : ℝ) :
    (∀ z' ∈ Heights.conePoints (P.projIdeal k₀) ℂ,
        ‖evalCone z' (rename (blockCoordEquiv (n := n) k₀) f)‖ ≤ B * l2Norm (z' ()) ^ N) ↔
      ∀ w ∈ oneBlockPoints P k₀, ‖eval₂ (Int.castRingHom ℂ) w f‖ ≤ B * l2Norm w ^ N := by
  have hev : ∀ z' : Cone (fun _ : Unit ↦ n k₀) ℂ,
      evalCone z' (rename (blockCoordEquiv (n := n) k₀) f) = eval₂ (Int.castRingHom ℂ) (z' ()) f := by
    intro z'
    rw [evalCone, eval₂_rename]
    rfl
  constructor
  · intro h w hw
    have := h _ ((mem_oneBlockPoints_iff P k₀ w).mp hw)
    rwa [hev] at this
  · intro h z' hz'
    have hz : z' = fun _ : Unit ↦ z' () := funext fun u ↦ by cases u; rfl
    rw [hev]
    rw [hz] at hz'
    exact h _ ((mem_oneBlockPoints_iff P k₀ (z' ())).mpr hz')

theorem points_nonempty_iff (hB : IndefiniteRowSideFullHecke.Close.SupNormEquality.Statement) (P : ArithVariety n) (k₀ : ι) :
    (P.points ℂ).Nonempty ↔ (oneBlockPoints P k₀).Nonempty := by
  have h := (hB ι n P k₀).2 0 1 (isHomogeneous_one _ _)
  simp only [eval₂_one, norm_one, pow_zero, div_one] at h
  rcases (P.points ℂ).eq_empty_or_nonempty with h1 | h1 <;>
    rcases (oneBlockPoints P k₀).eq_empty_or_nonempty with h2 | h2
  · simp [h1, h2]
  · rw [h1, h2.image_const, Set.image_empty, Real.sSup_empty, csSup_singleton] at h
    norm_num at h
  · rw [h2, h1.image_const, Set.image_empty, Real.sSup_empty, csSup_singleton] at h
    norm_num at h
  · exact iff_of_true h1 h2

theorem SupNormEquality.equiv : Heights.SupNormEquality.Statement ↔ IndefiniteRowSideFullHecke.Close.SupNormEquality.Statement := by
  constructor
  · intro hA ι _ _ n P k₀
    refine ⟨fun N ↦ secM_block P k₀ N, fun N f hf ↦ sSup_eq_of_upperBounds_eq ?_⟩
    ext B
    rw [mem_upperBounds_points, mem_upperBounds_image, ← forall_points_rename,
      ← forall_conePoints_rename]
    refine (hA ι n P k₀ N).2 _ ?_ B
    rw [isWeightedHomogeneous_unit_iff]
    exact hf.rename_isHomogeneous
  · intro hB ι _ _ n P k₀ m
    refine ⟨forms_of_block k₀ m, fun f' hf' B ↦ ?_⟩
    have hf'eq : f' = rename (blockCoordEquiv (n := n) k₀)
        (rename (blockCoordEquiv (n := n) k₀).symm f') := by
      rw [rename_rename, Equiv.self_comp_symm, rename_id_apply]
    set f := rename (blockCoordEquiv (n := n) k₀).symm f'
    have hf : f.IsHomogeneous m :=
      ((isWeightedHomogeneous_unit_iff f').mp hf').rename_isHomogeneous
    rw [hf'eq, forall_points_rename, forall_conePoints_rename, ← mem_upperBounds_points,
      ← mem_upperBounds_image]
    rw [upperBounds_eq_of_sSup_eq (bddAbove_points P k₀ hf) (bddAbove_image P k₀ hf)
      (by rw [Set.image_nonempty, Set.image_nonempty]; exact points_nonempty_iff hB P k₀)
      ((hB ι n P k₀).2 m f hf)]

end

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Close
