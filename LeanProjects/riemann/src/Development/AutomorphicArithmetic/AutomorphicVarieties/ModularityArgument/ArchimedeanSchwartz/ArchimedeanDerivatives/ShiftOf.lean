import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ArchimedeanSchwartz.ShiftOf

open NumberField MeasureTheory Matrix Polynomial GlobalTheory.CuspRep
open scoped ContDiff

noncomputable section

namespace UpperTheory.V.Z.Inf

variable {K : Type} [Field K] [NumberField K] {n : ℕ}

omit [NumberField K] in
private theorem coord_cases (τ : K →+* ℂ) :
    (∀ z : Cinf K, coord τ z = z (InfinitePlace.mk τ)) ∨
      ∀ z : Cinf K, coord τ z = starRingEnd ℂ (z (InfinitePlace.mk τ)) := by
  unfold coord
  split_ifs
  · exact Or.inl fun _ => rfl
  · exact Or.inr fun _ => rfl

private theorem det_ne_zero {x : Lie K n} (hx : x ∈ invSet K n) (w : InfinitePlace K) :
    (Matrix.of x).det w ≠ 0 := by
  obtain ⟨u, hu⟩ := (Matrix.isUnit_iff_isUnit_det _).1 hx
  have h := congrFun u.mul_inv w
  rw [hu] at h
  exact left_ne_zero_of_mul_eq_one h

private theorem detAt_ne_zero {x : Lie K n} (hx : x ∈ invSet K n) (τ : K →+* ℂ) : detAt τ x ≠ 0 := by
  rcases coord_cases τ with h | h
  · rw [detAt, h]; exact det_ne_zero hx _
  · rw [detAt, h]; exact (_root_.map_ne_zero _).2 (det_ne_zero hx _)

private theorem contDiff_det_at (w : InfinitePlace K) :
    ContDiff ℝ ∞ (fun x : Lie K n => (Matrix.of x).det w) := by
  simp only [Matrix.det_apply', Finset.sum_apply, Pi.mul_apply, Finset.prod_apply, Matrix.of_apply]
  refine ContDiff.sum fun p _ => contDiff_const.mul (contDiff_prod fun i _ => ?_)
  fun_prop

private theorem contDiff_detAt (τ : K →+* ℂ) : ContDiff ℝ ∞ (fun x : Lie K n => detAt τ x) := by
  rcases coord_cases τ with h | h
  · simp only [detAt, h]; exact contDiff_det_at _
  · simp only [detAt, h]; exact Complex.conjCLE.contDiff.comp (contDiff_det_at _)

private theorem nrm_pos {x : Lie K n} (hx : x ∈ invSet K n) : 0 < nrm x :=
  Finset.prod_pos fun w _ => pow_pos (norm_pos_iff.2 (det_ne_zero hx w)) _

private theorem contDiff_nrm : ContDiff ℝ ∞ (fun x : Lie K n => nrm x) :=
  contDiff_prod fun w _ => (contDiff_det_at w).norm_sq ℂ

private theorem contDiffOn_wt (u : ℂ) (e : (K →+* ℂ) → ℕ) : ContDiffOn ℝ ∞ (wt (n := n) u e) (invSet K n) := by
  have h0 : ContDiffOn ℝ ∞ (fun x : Lie K n => Real.log (nrm x)) (invSet K n) :=
    Real.contDiffOn_log.comp contDiff_nrm.contDiffOn (fun x hx => (nrm_pos hx).ne')
  have h1 : ContDiffOn ℝ ∞ (fun x : Lie K n => Complex.exp ((Real.log (nrm x) : ℂ) * u)) (invSet K n) :=
    ((Complex.ofRealCLM.contDiff.comp_contDiffOn h0).mul contDiffOn_const).cexp
  have h2 : ContDiffOn ℝ ∞ (fun x : Lie K n => ((nrm x : ℝ) : ℂ) ^ u) (invSet K n) :=
    h1.congr fun x hx => by
      rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast (nrm_pos hx).ne'), ← Complex.ofReal_log (nrm_pos hx).le]
  exact h2.mul (contDiffOn_prod fun σ _ =>
    ((contDiff_detAt σ).contDiffOn.inv fun x hx => detAt_ne_zero hx σ).pow _)

private theorem prod_coord [IsTotallyComplex K] (z : Cinf K) :
    ∏ σ : K →+* ℂ, coord σ z = ((∏ w, ‖z w‖ ^ 2 : ℝ) : ℂ) := by
  classical
  rw [← Finset.prod_fiberwise Finset.univ InfinitePlace.mk, Complex.ofReal_prod]
  refine Finset.prod_congr rfl fun w _ => ?_
  have hne : w.embedding ≠ ComplexEmbedding.conjugate w.embedding := fun h =>
    InfinitePlace.not_isReal_iff_isComplex.2 (IsTotallyComplex.isComplex w)
      (InfinitePlace.isReal_iff.2 (ComplexEmbedding.isReal_iff.2 h.symm))
  have hf : (Finset.univ.filter fun σ : K →+* ℂ => InfinitePlace.mk σ = w) =
      {w.embedding, ComplexEmbedding.conjugate w.embedding} := by
    ext σ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · intro h
      rcases InfinitePlace.mk_eq_iff.1 (w.mk_embedding.trans h.symm) with h | h
      · exact Or.inl h.symm
      · exact Or.inr h.symm
    · rintro (rfl | rfl)
      · exact w.mk_embedding
      · rw [InfinitePlace.mk_conjugate_eq, w.mk_embedding]
  have h1 : coord w.embedding z = z w := by
    unfold coord
    rw [InfinitePlace.mk_embedding, if_pos rfl]
    rfl
  have h2 : coord (ComplexEmbedding.conjugate w.embedding) z = starRingEnd ℂ (z w) := by
    unfold coord
    rw [InfinitePlace.mk_conjugate_eq, InfinitePlace.mk_embedding, if_neg hne]
    rfl
  rw [hf, Finset.prod_pair hne, h1, h2, Complex.mul_conj, Complex.normSq_eq_norm_sq]

private theorem integral_congr_inv {Ψ : Lie K n → ℂ} (hΨ : tsupport Ψ ⊆ invSet K n) {F G : Lie K n → ℂ}
    (h : ∀ x ∈ invSet K n, F x = G x) : ∫ x, Ψ x * F x = ∫ x, Ψ x * G x := by
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  by_cases hx : x ∈ invSet K n
  · simp only [h x hx]
  · simp only [image_eq_zero_of_notMem_tsupport (fun h' => hx (hΨ h')), zero_mul]

private theorem integral_mul_const_in (Ψ F : Lie K n → ℂ) (c : ℂ) :
    ∫ x, Ψ x * (c * F x) = c * ∫ x, Ψ x * F x := by
  rw [← integral_const_mul]; congr 1; funext x; ring

attribute [local instance] Classical.propDecidable

private theorem wt_succ (u : ℂ) (e : (K →+* ℂ) → ℕ) (τ : K →+* ℂ) (x : Lie K n) :
    wt u (e + Pi.single τ 1) x = wt u e x * (detAt τ x)⁻¹ := by
  simp only [wt, Pi.add_apply, pow_add, Finset.prod_mul_distrib, mul_assoc]
  congr 2
  rw [Finset.prod_eq_single τ (fun σ _ h => by simp [Pi.single_eq_of_ne h]) (by simp)]
  simp

private theorem list_shift [IsTotallyComplex K] (hP : Ptw) (hI : Parts) (φ : Sm K n)
    (m : (K →+* ℂ) → Multiset ℂ) (hm : ∀ τ u, cap τ u φ = ((m τ).map (u + ·)).prod • φ) (g : GA K n) (u : ℂ) :
    ∀ l : List (K →+* ℂ), l.Nodup → ∀ (e : (K →+* ℂ) → ℕ) (Ψ : Lie K n → ℂ), IsTest Ψ →
      IsTest (l.foldr detD Ψ) ∧
      ∫ x, l.foldr detD Ψ x * (chart φ.1 g x * wt u e x) =
        ((-1) ^ n) ^ l.length * (l.map fun τ => ((m τ).map (u - e τ + ((n : ℂ) - 1) / 2 + ·)).prod).prod *
          ∫ x, Ψ x * (chart φ.1 g x * wt u (fun σ => e σ + if σ ∈ l then 1 else 0) x) := by
  intro l
  induction l with
  | nil =>
    intro _ e Ψ hΨ
    exact ⟨hΨ, by simp⟩
  | cons τ l ih =>
    intro hl e Ψ hΨ
    have hτ : τ ∉ l := (List.nodup_cons.1 hl).1
    obtain ⟨hT, hJ⟩ := ih (List.nodup_cons.1 hl).2 (e + Pi.single τ 1) Ψ hΨ
    obtain ⟨hT', hp⟩ := hI K n τ _ hT
    refine ⟨hT', ?_⟩
    have hlow : (fun σ => (e + Pi.single τ 1 : (K →+* ℂ) → ℕ) σ + if σ ∈ l then 1 else 0) =
        fun σ => e σ + if σ ∈ τ :: l then 1 else 0 := by
      funext σ
      by_cases h : σ = τ
      · subst h; simp [hτ]
      · simp [h]
    have hmap : (l.map fun σ => ((m σ).map
          (u - ((e + Pi.single τ 1 : (K →+* ℂ) → ℕ) σ : ℕ) + ((n : ℂ) - 1) / 2 + ·)).prod) =
        l.map fun σ => ((m σ).map (u - e σ + ((n : ℂ) - 1) / 2 + ·)).prod :=
      List.map_congr_left fun σ hσ => by
        rw [Pi.add_apply, Pi.single_eq_of_ne (fun h : σ = τ => hτ (h ▸ hσ)), add_zero]
    have hpt : ∀ x ∈ invSet K n, detD τ (fun y => chart φ.1 g y * wt u e y) x =
        ((m τ).map (u - e τ + ((n : ℂ) - 1) / 2 + ·)).prod * (chart φ.1 g x * wt u (e + Pi.single τ 1) x) :=
      fun x hx => by rw [hP K n τ φ (m τ) (hm τ) g u e x hx, wt_succ, mul_assoc]
    rw [List.foldr_cons, hp _ ((φ.2 g).mul (contDiffOn_wt u e)), integral_congr_inv hT.2.2 hpt,
      integral_mul_const_in, hJ, hlow, hmap, List.map_cons, List.prod_cons, List.length_cons]
    ring

private theorem linPoly_sum {ι : Type} (s : Finset ι) (m : ι → Multiset ℂ) :
    linPoly (∑ i ∈ s, m i) = ∏ i ∈ s, linPoly (m i) := by
  refine Finset.induction_on s (by simp [linPoly]) ?_
  intro a s ha ih
  rw [Finset.sum_insert ha, Finset.prod_insert ha, ← ih]
  simp [linPoly, Multiset.map_add, Multiset.prod_add]

private theorem wt_one [IsTotallyComplex K] (u : ℂ) {x : Lie K n} (hx : x ∈ invSet K n) :
    wt u (fun _ => 1) x = ((nrm x : ℝ) : ℂ) ^ (u - 1) := by
  have h : ∏ σ, detAt σ x = ((nrm x : ℝ) : ℂ) := prod_coord _
  rw [Complex.cpow_sub _ _ (by exact_mod_cast (nrm_pos hx).ne'), Complex.cpow_one, wt, div_eq_mul_inv, ← h,
    ← Finset.prod_inv_distrib]
  simp

end UpperTheory.V.Z.Inf

open UpperTheory.V.Z.Inf in
theorem UpperTheory.V.Z.Inf.shiftOf :
    UpperTheory.V.Z.Inf.ShiftOf := by
  intro hP hI K _ _ _ n
  classical
  refine ⟨((-1) ^ n) ^ (Finset.univ : Finset (K →+* ℂ)).toList.length, by simp, fun φ m hm Φ hΦ => ?_⟩
  have hnd : (Finset.univ : Finset (K →+* ℂ)).toList.Nodup := Finset.nodup_toList _
  refine ⟨(list_shift hP hI φ m hm 1 0 _ hnd 0 Φ hΦ).1, fun g s => ?_⟩
  obtain ⟨_, h⟩ := list_shift hP hI φ m hm g (s + 1 + ((n : ℂ) - 1) / 2 - n) _ hnd 0 Φ hΦ
  have hone : (fun σ : K →+* ℂ => (0 : (K →+* ℂ) → ℕ) σ +
      if σ ∈ (Finset.univ : Finset (K →+* ℂ)).toList then 1 else 0) = fun _ => 1 := by
    funext σ; simp
  have hR : ∀ x ∈ invSet K n, chart φ.1 g x * wt (s + 1 + ((n : ℂ) - 1) / 2 - n) (fun _ => 1) x =
      chart φ.1 g x * ((nrm x : ℝ) : ℂ) ^ (s + ((n : ℂ) - 1) / 2 - n) := fun x hx => by
    rw [wt_one _ hx]; congr 2; ring
  have hL : ∀ x : Lie K n, wt (s + 1 + ((n : ℂ) - 1) / 2 - n) 0 x =
      ((nrm x : ℝ) : ℂ) ^ (s + 1 + ((n : ℂ) - 1) / 2 - n) := fun x => by simp [wt]
  simp only [hL] at h
  rw [hone, integral_congr_inv hΦ.2.2 hR, Finset.prod_map_toList] at h
  simp only [mul_assoc (_ : ℂ) (chart φ.1 g _)]
  rw [detAll, h, linPoly_sum, Polynomial.eval_prod]
  congr 2
  refine Finset.prod_congr rfl fun τ _ => ?_
  rw [linPoly, Polynomial.eval_multiset_prod, Multiset.map_map]
  congr 1
  refine Multiset.map_congr rfl fun z _ => ?_
  simp only [Function.comp_apply, eval_add, eval_X, eval_C, Pi.zero_apply, Nat.cast_zero]
  ring
