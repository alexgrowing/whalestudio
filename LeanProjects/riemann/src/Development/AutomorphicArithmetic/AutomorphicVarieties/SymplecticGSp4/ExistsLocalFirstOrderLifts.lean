import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.ExDefs
import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.OnCompSelf

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement

section Alg

variable {B : Type} [CommRing B]

private theorem adj_mul (X Y : M4 B) : adj (X * Y) = adj Y * adj X := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_four, adj_apply, sgn, Fin.rev] <;> ring

private theorem adj_one : adj (1 : M4 B) = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [adj_apply, sgn, Fin.rev]

private theorem gsp_conj {ν : B} {h : (M4 B)ˣ} (h1 : adj (h : M4 B) = (h⁻¹ : (M4 B)ˣ)) {X : M4 B} (hX : IsGSp ν X) :
    IsGSp ν (h * X * (h⁻¹ : (M4 B)ˣ)) := by
  have hinv : adj ((h⁻¹ : (M4 B)ˣ) : M4 B) = h := by
    have e1 : adj ((h⁻¹ : (M4 B)ˣ) : M4 B) * adj (h : M4 B) = 1 := by
      rw [← adj_mul, Units.mul_inv, adj_one]
    rw [h1] at e1
    calc adj ((h⁻¹ : (M4 B)ˣ) : M4 B)
        = adj ((h⁻¹ : (M4 B)ˣ) : M4 B) * (((h⁻¹ : (M4 B)ˣ) : M4 B) * h) := by rw [Units.inv_mul, mul_one]
      _ = h := by rw [← mul_assoc, e1, one_mul]
  unfold IsGSp at hX ⊢
  rw [adj_mul, adj_mul, hinv, h1]
  rw [show (h : M4 B) * (adj X * ((h⁻¹ : (M4 B)ˣ) : M4 B)) * (h * X * ((h⁻¹ : (M4 B)ˣ) : M4 B)) =
      h * (adj X * X) * ((h⁻¹ : (M4 B)ˣ) : M4 B) by simp only [mul_assoc, Units.inv_mul_cancel_left]]
  rw [hX, mul_smul_comm, mul_one, smul_mul_assoc, Units.mul_inv]

private def cj {H : Type} [Group H] (h : (M4 B)ˣ) (r : H →* M4 B) : H →* M4 B where
  toFun g := h * r g * (h⁻¹ : (M4 B)ˣ)
  map_one' := by simp
  map_mul' a b := by simp only [map_mul, mul_assoc, Units.inv_mul_cancel_left]

private theorem cj_apply {H : Type} [Group H] (h : (M4 B)ˣ) (r : H →* M4 B) (g : H) :
    cj h r g = h * r g * (h⁻¹ : (M4 B)ˣ) := rfl

private def cjA (h : (M4 B)ˣ) : M4 B →ₐ[B] M4 B where
  toFun X := h * X * (h⁻¹ : (M4 B)ˣ)
  map_one' := by simp
  map_mul' a b := by simp only [mul_assoc, Units.inv_mul_cancel_left]
  map_zero' := by simp
  map_add' a b := by rw [mul_add, add_mul]
  commutes' a := by simp [Algebra.algebraMap_eq_smul_one]

private theorem prj_cjA_eq_cjA_prj (h : (M4 B)ˣ) (c : Fin 4 → B) (X : M4 B) (i : Fin 4) :
    prj c (cjA h X) i = cjA h (prj c X i) := by
  simp only [prj, Polynomial.aeval_algHom_apply]

private theorem ord_cj {H : Type} [Group H] (h : (M4 B)ˣ) {I : Subgroup H} {ps : Fin 4 → H → B} {s₀ : H}
    {r : H →* M4 B} (hr : Ord I ps s₀ r) : Ord I ps s₀ (cj h r) := by
  have hcj : ∀ g, cj h r g = cjA h (r g) := fun g => rfl
  refine ⟨?_, ?_, ?_⟩
  · rw [hcj]
    show ((h : M4 B) * r s₀ * ((h⁻¹ : (M4 B)ˣ) : M4 B)).charpoly = _
    rw [Matrix.charpoly_mul_comm, ← mul_assoc, Units.inv_mul, one_mul]
    exact hr.charpoly
  · intro g i j hij
    simp only [hcj, prj_cjA_eq_cjA_prj, ← map_mul, hr.stable g i j hij, map_zero]
  · intro s hs i
    have e : cjA h (r s) - ps i s • 1 = cjA h (r s - ps i s • 1) := by
      rw [map_sub, map_smul, map_one]
    simp only [hcj, prj_cjA_eq_cjA_prj, e, ← map_mul, hr.inert s hs i, map_zero]

private def cjL {O : Type} [CommRing O] [IsLocalRing O] [Algebra O B] [IsCO O B] {H : Type} [Group H] [TopologicalSpace H]
    {rb : H →* M4 (ResidueField O)} (h : (M4 B)ˣ) (h1 : (h : M4 B).map (res O B) = 1)
    (h2 : ((h⁻¹ : (M4 B)ˣ) : M4 B).map (res O B) = 1) (r : Lift O rb B) : Lift O rb B where
  hom := cj h r.hom
  cont a b N := (IsLocallyConstant.iff_eventually_eq _).2 fun x => by
    have : ∀ᶠ y in nhds x, ∀ i j, Ideal.Quotient.mk (maximalIdeal B ^ N) (r.hom y i j) =
        Ideal.Quotient.mk (maximalIdeal B ^ N) (r.hom x i j) :=
      Filter.eventually_all.2 fun i => Filter.eventually_all.2 fun j => (r.cont i j N).eventually_eq x
    filter_upwards [this] with y hy
    simp only [cj_apply, Matrix.mul_apply, map_sum, map_mul, hy]
  red g a b := by
    have : (cj h r.hom g).map (res O B) = (r.hom g).map (res O B) := by
      rw [cj_apply, Matrix.map_mul, Matrix.map_mul, h1, h2, one_mul, mul_one]
    exact (congrFun (congrFun this a) b).trans (r.red g a b)

end Alg

section Dual

variable {O : Type} [CommRing O]

private def dU (Y : M4 O) : (M4 (DualNumber O))ˣ :=
  have h : Y.map (TrivSqZeroExt.inr : O → DualNumber O) * Y.map (TrivSqZeroExt.inr : O → DualNumber O) = 0 := by
    refine Matrix.ext fun i j => ?_
    simp only [Matrix.mul_apply, Matrix.map_apply, TrivSqZeroExt.inr_mul_inr, Finset.sum_const_zero, Matrix.zero_apply]
  ⟨1 + Y.map TrivSqZeroExt.inr, 1 - Y.map TrivSqZeroExt.inr, by rw [mul_sub, add_mul, add_mul, h]; simp,
    by rw [mul_add, sub_mul, sub_mul, h]; simp⟩

private theorem dU_val (Y : M4 O) : (dU Y : M4 (DualNumber O)) = 1 + Y.map TrivSqZeroExt.inr := rfl

private theorem dU_inv (Y : M4 O) :
    (((dU Y)⁻¹ : (M4 (DualNumber O))ˣ) : M4 (DualNumber O)) = 1 - Y.map TrivSqZeroExt.inr := rfl

private theorem dU_adj {Y : M4 O} (hY : Y ∈ sp4 O) :
    adj (dU Y : M4 (DualNumber O)) = ((dU Y)⁻¹ : (M4 (DualNumber O))ˣ) := by
  have hY' : adj Y = -Y := hY
  rw [dU_val, dU_inv]
  ext i j
  · rw [adj_apply]
    fin_cases i <;> fin_cases j <;> simp [sgn, Fin.rev, Matrix.one_apply]
  · have hij := congrFun (congrFun hY' i) j
    rw [adj_apply] at hij
    rw [adj_apply]
    simp [Matrix.one_apply]
    rw [zsmul_eq_mul, Int.cast_mul, Matrix.neg_apply] at hij
    have e1 : TrivSqZeroExt.snd (if j = i then ((sgn i : DualNumber O) * (sgn j : DualNumber O)) else 0) = 0 := by
      split_ifs <;> simp
    have e2 : (if i = j then (1 : DualNumber O) else 0).snd = 0 := by
      split_ifs <;> simp
    rw [e1, e2, zero_add, zero_sub, mul_comm, hij]

private theorem map_fst_mul_dualNumber_matrix (A B : M4 (DualNumber O)) :
    (A * B).map TrivSqZeroExt.fst = A.map TrivSqZeroExt.fst * B.map TrivSqZeroExt.fst := by
  ext a b
  simp [Matrix.mul_apply, TrivSqZeroExt.fst_sum]

private theorem map_snd_mul_dualNumber_matrix (A B : M4 (DualNumber O)) :
    (A * B).map TrivSqZeroExt.snd =
      A.map TrivSqZeroExt.fst * B.map TrivSqZeroExt.snd + A.map TrivSqZeroExt.snd * B.map TrivSqZeroExt.fst := by
  ext a b
  simp [Matrix.mul_apply, TrivSqZeroExt.snd_sum, TrivSqZeroExt.snd_mul, Finset.sum_add_distrib, mul_comm]

private theorem dU_conj (Y X : M4 O) (X' : M4 (DualNumber O)) (hX : ∀ a b, X' a b = TrivSqZeroExt.inl (X a b))
    (a b : Fin 4) :
    ((dU Y * X' * ((dU Y)⁻¹ : (M4 (DualNumber O))ˣ) : M4 (DualNumber O)) a b).fst = X a b ∧
      ((dU Y * X' * ((dU Y)⁻¹ : (M4 (DualNumber O))ˣ) : M4 (DualNumber O)) a b).snd = (Y * X - X * Y) a b := by
  have hX' : X' = X.map TrivSqZeroExt.inl := Matrix.ext fun a b => hX a b
  subst hX'
  rw [dU_val, dU_inv]
  have p1 : (1 + Y.map (TrivSqZeroExt.inr : O → DualNumber O)).map TrivSqZeroExt.fst = 1 := by
    ext a b
    by_cases h : a = b <;> simp [Matrix.one_apply, h]
  have p2 : (1 + Y.map (TrivSqZeroExt.inr : O → DualNumber O)).map TrivSqZeroExt.snd = Y := by
    ext a b
    by_cases h : a = b <;> simp [Matrix.one_apply, h]
  have q1 : (1 - Y.map (TrivSqZeroExt.inr : O → DualNumber O)).map TrivSqZeroExt.fst = 1 := by
    ext a b
    by_cases h : a = b <;> simp [Matrix.one_apply, h]
  have q2 : (1 - Y.map (TrivSqZeroExt.inr : O → DualNumber O)).map TrivSqZeroExt.snd = -Y := by
    ext a b
    by_cases h : a = b <;> simp [Matrix.one_apply, h]
  have x1 : (X.map (TrivSqZeroExt.inl : O → DualNumber O)).map TrivSqZeroExt.fst = X := by
    ext a b
    simp
  have x2 : (X.map (TrivSqZeroExt.inl : O → DualNumber O)).map TrivSqZeroExt.snd = 0 := by
    ext a b
    simp
  have F : ((1 + Y.map (TrivSqZeroExt.inr : O → DualNumber O)) * X.map TrivSqZeroExt.inl *
      (1 - Y.map (TrivSqZeroExt.inr : O → DualNumber O))).map TrivSqZeroExt.fst = X := by
    rw [map_fst_mul_dualNumber_matrix, map_fst_mul_dualNumber_matrix, p1, x1, q1, one_mul, mul_one]
  have S : ((1 + Y.map (TrivSqZeroExt.inr : O → DualNumber O)) * X.map TrivSqZeroExt.inl *
      (1 - Y.map (TrivSqZeroExt.inr : O → DualNumber O))).map TrivSqZeroExt.snd = Y * X - X * Y := by
    rw [map_snd_mul_dualNumber_matrix, map_fst_mul_dualNumber_matrix, map_snd_mul_dualNumber_matrix, p1, p2, x1, x2, q1, q2]
    simp only [one_mul, mul_one, mul_zero, zero_add, mul_neg]
    abel
  exact ⟨congrFun (congrFun F a) b, congrFun (congrFun S a) b⟩

private theorem dU_res [IsLocalRing O] [IsCO O (DualNumber O)] (Y : M4 O) :
    (dU Y : M4 (DualNumber O)).map (res O (DualNumber O)) = 1 ∧
      (((dU Y)⁻¹ : (M4 (DualNumber O))ˣ) : M4 (DualNumber O)).map (res O (DualNumber O)) = 1 := by
  have hres : ∀ y : O, res O (DualNumber O) (TrivSqZeroExt.inr y) = 0 := by
    intro y
    have h2 : (res O (DualNumber O) (TrivSqZeroExt.inr y)) ^ 2 = 0 := by
      rw [← map_pow, pow_two]
      simp
    exact (pow_eq_zero_iff two_ne_zero).mp h2
  have hE : (Y.map (TrivSqZeroExt.inr : O → DualNumber O)).map (res O (DualNumber O)) = 0 := by
    ext a b
    simp only [Matrix.map_apply, Matrix.zero_apply, hres]
  constructor
  · rw [dU_val, Matrix.map_add _ (map_add _), Matrix.map_one _ (map_zero _) (map_one _), hE, add_zero]
  · rw [dU_inv, Matrix.map_sub _ (map_sub _), Matrix.map_one _ (map_zero _) (map_one _), hE, sub_zero]

end Dual

private theorem cjL_hom_eq_conj {B : Type} [CommRing B] {O : Type} [CommRing O] [IsLocalRing O] [Algebra O B]
    [IsCO O B] {H : Type} [Group H] [TopologicalSpace H] {rb : H →* M4 (ResidueField O)} (h : (M4 B)ˣ)
    (h1 : (h : M4 B).map (res O B) = 1) (h2 : ((h⁻¹ : (M4 B)ˣ) : M4 B).map (res O B) = 1) (r : Lift O rb B) (g : H) :
    (cjL h h1 h2 r).hom g = h * r.hom g * (h⁻¹ : (M4 B)ˣ) := rfl

theorem UpperTheory.exists_local_first_order_lifts :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} (D : Raw Ω c), D.Good → ∀ Y : D.T → M4 c.O, (∀ v, Y v ∈ sp4 c.O) → ∃ ρ : ∀ v : D.T, Lift c.O (D.rbarAt v) (DualNumber c.O), D.LocEqs ρ ∧ ∀ (v : D.T) (g : D.Gp v) (a b : Fin 4), ((ρ v).hom g a b).fst = D.r0 g a b ∧ ((ρ v).hom g a b).snd = (Y v * D.r0 g - D.r0 g * Y v) a b := by
  intro Ω _ _ _ l _ c D hD Y hY
  obtain ⟨ρ₀, hhom, hpt⟩ := r0pt D hD
  have hL : D.condL (DualNumber c.O) (Lift.map (Algebra.ofId c.O (DualNumber c.O)) (D.loc ρ₀ l)) := by
    obtain ⟨B, _, _, _, _, ρ, hPl, -, y, hy⟩ := hpt.atL
    rw [← hy]
    exact Ex.condL_map D (Algebra.ofId _ _) _ (Ex.condL_map D y ρ hPl)
  have hP : ∀ p ∈ D.Sb,
      D.condP p (DualNumber c.O) (Lift.map (Algebra.ofId c.O (DualNumber c.O)) (D.loc ρ₀ p)) := by
    intro p hp
    obtain ⟨B, _, _, _, _, ρ, hPp, -, y, hy⟩ := hpt.atP p hp
    rw [← hy]
    exact Ex.condP_map D p (Algebra.ofId _ _) _ (Ex.condP_map D p y ρ hPp)
  refine ⟨fun v => cjL (dU (Y v)) (dU_res (Y v)).1 (dU_res (Y v)).2
    (Lift.map (Algebra.ofId c.O (DualNumber c.O)) (D.loc ρ₀ v)), ⟨?_, ?_⟩, ?_⟩
  · exact ⟨fun g => gsp_conj (dU_adj (hY _)) (hL.1 g), ord_cj _ hL.2⟩
  · intro p hp
    refine ⟨fun g => gsp_conj (dU_adj (hY _)) ((hP p hp).1 g), fun g hg => ?_⟩
    show cj _ _ g = 1
    rw [cj_apply, (hP p hp).2 g hg, mul_one, Units.mul_inv]
  · intro v g a b
    have hX : ∀ a b, (Lift.map (Algebra.ofId c.O (DualNumber c.O)) (D.loc ρ₀ v)).hom g a b =
        TrivSqZeroExt.inl (D.r0 g a b) := by
      intro a b
      show algebraMap c.O (DualNumber c.O) (ρ₀.hom g a b) = _
      rw [hhom]
      rfl
    have key := dU_conj (Y v) (D.r0 g) _ hX a b
    simp only [cjL_hom_eq_conj]
    exact key
