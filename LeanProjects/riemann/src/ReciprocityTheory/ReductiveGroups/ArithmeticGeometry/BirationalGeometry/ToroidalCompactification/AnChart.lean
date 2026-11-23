import Mathlib

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.Geo.Tor

open MvPolynomial

theorem hasFDerivAt_eval {I : Type} [Fintype I] [DecidableEq I] (p : MvPolynomial I ℂ) (x : I → ℂ) :
    HasFDerivAt (fun x => eval x p) (∑ i, eval x (pderiv i p) • ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : I => ℂ) i) x := by
  induction p using MvPolynomial.induction_on with
  | C a => simpa using hasFDerivAt_const a x
  | add p q hp hq =>
    refine ((hp.add hq).congr_fderiv ?_).congr_of_eventuallyEq (Filter.Eventually.of_forall fun y => map_add _ _ _)
    simp [add_smul, Finset.sum_add_distrib]
  | mul_X p j hp =>
    refine ((hp.mul (hasFDerivAt_apply (𝕜 := ℂ) j x)).congr_fderiv (ContinuousLinearMap.ext fun v => ?_)).congr_of_eventuallyEq
      (Filter.Eventually.of_forall fun y => by simp)
    simp [pderiv_X, Pi.single_apply, mul_add, Finset.sum_add_distrib, Finset.mul_sum, mul_comm, mul_left_comm, apply_ite, add_comm]

theorem anChart_alg {k A : Type} [Field k] [CommRing A] [Algebra k A] (D : ℕ) [h : Algebra.IsStandardSmoothOfRelativeDimension D k A]
    (σ : k →+* ℂ) (ψ₀ : A →+* ℂ) (h₀ : ψ₀.comp (algebraMap k A) = σ) :
    ∃ (N : ℕ) (g : Fin N → A) (f : Fin D → A) (B : Set (Fin D → ℂ)) (ε : ℝ) (Ψ : (Fin D → ℂ) → (A →+* ℂ)),
      0 < ε ∧ IsOpen B ∧ (∀ b ∈ B, (Ψ b).comp (algebraMap k A) = σ ∧ ∀ i, Ψ b (f i) = b i) ∧
      (∀ a, DifferentiableOn ℂ (fun b => Ψ b a) B) ∧
      ∀ ψ : A →+* ℂ, ψ.comp (algebraMap k A) = σ → (∀ j, ‖ψ (g j) - ψ₀ (g j)‖ < ε) →
        (fun i => ψ (f i)) ∈ B ∧ Ψ (fun i => ψ (f i)) = ψ := by
  classical
  obtain ⟨I, J, _, _, P, hd⟩ := h.out
  have := Fintype.ofFinite I
  have := Fintype.ofFinite J
  have e : Fin D ≃ {i : I // i ∉ Set.range P.map} := (Fintype.equivFinOfCardEq (by
    rw [Fintype.card_subtype_compl, ← hd, Algebra.Presentation.dimension, Nat.card_eq_fintype_card, Nat.card_eq_fintype_card,
      Set.card_range_of_injective P.map_inj])).symm
  let ev := fun (x : I → ℂ) => eval₂Hom σ x
  have pt : ∀ ψ : A →+* ℂ, ψ.comp (algebraMap k A) = σ → ∀ p, ψ (algebraMap P.Ring A p) = ev (fun i => ψ (P.val i)) p := fun ψ hψ p => by
    rw [P.algebraMap_apply, aeval_def, ← coe_eval₂Hom, map_eval₂Hom, hψ]
  let q : I → MvPolynomial I k := fun i => if h : i ∈ Set.range P.map then P.relation h.choose else X i
  have q₁ : ∀ j, q (P.map j) = P.relation j := fun j => (dif_pos ⟨j, rfl⟩).trans
    (congrArg _ (P.map_inj (⟨j, rfl⟩ : P.map j ∈ Set.range P.map).choose_spec))
  have q₂ : ∀ i : {i : I // i ∉ Set.range P.map}, q i = X i.1 := fun i => dif_neg i.2
  let Φ : (I → ℂ) → I → ℂ := fun x i => eval x (map σ (q i))
  have Φe : ∀ x i, Φ x i = ev x (q i) := fun x i => eval_map _ _ _
  let x₀ : I → ℂ := fun i => ψ₀ (P.val i)
  let F : (I → ℂ) →L[ℂ] (I → ℂ) := ContinuousLinearMap.pi fun i =>
    ∑ i', eval x₀ (pderiv i' (map σ (q i))) • ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : I => ℂ) i'
  have hF : HasFDerivAt Φ F x₀ := hasFDerivAt_pi.2 fun i => hasFDerivAt_eval _ _
  have Fv : ∀ v i, F v i = ∑ i', ev x₀ (pderiv i' (q i)) * v i' := fun v i => by
    simp [F, ev, pderiv_map, eval_map]
  have inj : Function.Injective F := (injective_iff_map_eq_zero F).2 fun v hv => by
    have z₁ : ∀ i, i ∉ Set.range P.map → v i = 0 := fun i hi => by
      have := congrFun hv i
      rw [Fv, q₂ ⟨i, hi⟩] at this
      simpa [pderiv_X, Pi.single_apply, apply_ite] using this
    have dt : ((ev x₀).mapMatrix P.jacobiMatrix).det ≠ 0 := by
      rw [← RingHom.map_det, ← pt ψ₀ h₀, ← P.jacobian_eq_jacobiMatrix_det]
      exact (P.jacobian_isUnit.map ψ₀).ne_zero
    have z₂ : (fun j => v (P.map j)) = 0 := Matrix.eq_zero_of_vecMul_eq_zero dt (funext fun j => by
      have := congrFun hv (P.map j)
      rw [Fv, q₁, ← Finset.sum_subset (Finset.subset_univ (Finset.univ.image P.map)) (fun i _ hi => by
        rw [z₁ i (by simpa using hi), mul_zero]), Finset.sum_image fun a _ b _ h => P.map_inj h] at this
      simpa [Matrix.vecMul, dotProduct, P.jacobiMatrix_apply, mul_comm] using this)
    funext i
    by_cases hi : i ∈ Set.range P.map
    · obtain ⟨j, rfl⟩ := hi; exact congrFun z₂ j
    · exact z₁ i hi
  let F' : (I → ℂ) ≃L[ℂ] (I → ℂ) := (LinearEquiv.ofInjectiveEndo F.toLinearMap inj).toContinuousLinearEquiv
  have cd : ContDiffAt ℂ 1 Φ x₀ := contDiffAt_pi.2 fun i =>
    (AnalyticOnNhd.eval_mvPolynomial (map σ (q i)) x₀ trivial).contDiffAt
  let T := cd.toOpenPartialHomeomorph Φ (f' := F') hF one_ne_zero
  let O := T.target ∩ interior {w | ContDiffAt ℂ 1 T.symm w}
  have oO : IsOpen O := T.open_target.inter isOpen_interior
  have mO : Φ x₀ ∈ O := ⟨cd.image_mem_toOpenPartialHomeomorph_target (f' := F') hF one_ne_zero,
    mem_interior_iff_mem_nhds.2 ((cd.to_localInverse (f' := F') hF one_ne_zero).eventually (by simp))⟩
  let em : (Fin D → ℂ) →L[ℂ] (I → ℂ) := ContinuousLinearMap.pi fun i =>
    if h : i ∈ Set.range P.map then 0 else ContinuousLinearMap.proj (e.symm ⟨i, h⟩)
  have m₁ : ∀ b j, em b (P.map j) = 0 := fun b j => by simp [em]
  have m₂ : ∀ b i, em b (e i) = b i := fun b i => by simp only [em, ContinuousLinearMap.pi_apply, dif_neg (e i).2]; simp
  have lf : ∀ x : I → ℂ, (∀ j, ev x (P.relation j) = 0) → ∃ ψ : A →+* ℂ, ∀ p, ψ (algebraMap P.Ring A p) = ev x p := fun x hx =>
    ⟨(algebraMap P.Ring A).liftOfSurjective P.algebraMap_surjective ⟨ev x, by
      show P.ker ≤ _
      rw [← P.span_range_relation_eq_ker, Ideal.span_le]
      rintro _ ⟨j, rfl⟩; exact hx j⟩, fun p => RingHom.liftOfRightInverse_comp_apply _ _ _ _ p⟩
  choose Ψ hΨ using lf
  have rel : ∀ b, em b ∈ O → ∀ j, ev (T.symm (em b)) (P.relation j) = 0 := fun b hb j => by
    rw [← q₁, ← Φe, show Φ (T.symm (em b)) = em b from T.right_inv hb.1, m₁]
  obtain ⟨ε, ε0, hε⟩ := Metric.mem_nhds_iff.1 (Filter.inter_mem (T.open_source.mem_nhds
    (cd.mem_toOpenPartialHomeomorph_source (f' := F') hF one_ne_zero)) (hF.continuousAt.preimage_mem_nhds (oO.mem_nhds mO)))
  let n := Fintype.equivFin I
  refine ⟨_, fun j => P.val (n.symm j), fun i => P.val (e i), em ⁻¹' O, ε, fun b => if h : em b ∈ O then Ψ _ (rel b h) else ψ₀, ε0,
    oO.preimage em.continuous, fun b hb => ?_, fun a => ?_, fun ψ hψ hg => ?_⟩
  · simp only [dif_pos (show em b ∈ O from hb)]
    refine ⟨RingHom.ext fun r => ?_, fun i => ?_⟩
    · rw [RingHom.comp_apply, IsScalarTower.algebraMap_apply k P.Ring A, hΨ]; exact eval₂Hom_C _ _ _
    · rw [show P.val (e i) = algebraMap P.Ring A (X (e i).1) by simp, hΨ, ← q₂, ← Φe,
        show Φ (T.symm (em b)) = em b from T.right_inv hb.1, m₂]
  · obtain ⟨p, rfl⟩ := P.algebraMap_surjective a
    refine DifferentiableOn.congr (f := fun b => eval (T.symm (em b)) (map σ p)) (fun b hb => ?_) fun b hb => ?_
    · have c₁ : ContDiffAt ℂ 1 T.symm (em b) := interior_subset hb.2
      have c₂ : DifferentiableAt ℂ (fun x : I → ℂ => eval x (map σ p)) (T.symm (em b)) := (hasFDerivAt_eval _ _).differentiableAt
      exact (c₂.comp b ((c₁.differentiableAt one_ne_zero).comp b em.differentiableAt)).differentiableWithinAt
    · simp only [dif_pos (show em b ∈ O from hb)]; rw [hΨ, eval_map]; rfl
  · have hx := hε (show (fun i => ψ (P.val i)) ∈ Metric.ball x₀ ε from (dist_pi_lt_iff ε0).2 fun i => by
      simpa [dist_eq_norm] using hg (n i))
    have e₁ : em (fun i => ψ (P.val (e i))) = Φ fun i => ψ (P.val i) := funext fun i => by
      by_cases hi : i ∈ Set.range P.map
      · obtain ⟨j, rfl⟩ := hi
        rw [m₁, Φe, q₁, ← pt ψ hψ, P.algebraMap_apply, P.aeval_val_relation, map_zero]
      · obtain ⟨j, hj⟩ := e.surjective ⟨i, hi⟩
        obtain rfl : (e j).1 = i := congrArg Subtype.val hj
        rw [m₂, Φe, q₂]
        simp only [ev, eval₂Hom_X']
    have mB : em (fun i => ψ (P.val (e i))) ∈ O := by rw [e₁]; exact hx.2
    refine ⟨mB, (dif_pos mB).trans (RingHom.ext fun a => ?_)⟩
    obtain ⟨p, rfl⟩ := P.algebraMap_surjective a
    rw [hΨ, pt ψ hψ, e₁, show T.symm (Φ fun i => ψ (P.val i)) = _ from T.left_inv hx.1]

end ReciprocityTheory.ChartRestriction.G.Geo.Tor
