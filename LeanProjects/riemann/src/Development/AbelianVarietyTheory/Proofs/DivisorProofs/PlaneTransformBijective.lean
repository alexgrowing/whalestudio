import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.VacGlueIndicator
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRationalDarbouxHermitianTensorAdeles
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.PlaneCo

noncomputable section
namespace GlobalTheory.ThK.PlaneBij

theorem coords_bijective {R A ι κ : Type} [CommRing R] [Ring A] [Algebra R A] [Fintype κ]
    (b : Module.Basis κ R A) : Function.Bijective (fun (s : ι → A) (k : ι × κ) => b.repr (s k.1) k.2) := by
  constructor
  · intro s s' h
    funext i
    apply b.ext_elem
    intro j
    exact congrFun h (i, j)
  · intro g
    refine ⟨fun i => b.equivFun.symm (fun j => g (i, j)), ?_⟩
    funext k
    simp only
    rw [← b.equivFun_apply, LinearEquiv.apply_symm_apply]

theorem pair_bijective {R ι : Type} [CommRing R] [Fintype ι] [DecidableEq ι] (A : Matrix ι ι R) (hA : IsUnit A)
    (f : R → R) (hf : Function.Bijective f) :
    Function.Bijective (fun (t : ι → R) (k : ι) => -∑ m, A k m * f (t m)) := by
  have h1 : Function.Bijective (fun t : ι → R => fun m => f (t m)) := by
    constructor
    · intro t t' h; funext m; exact hf.1 (congrFun h m)
    · intro g; refine ⟨fun m => Function.surjInv hf.2 (g m), ?_⟩; funext m; exact Function.surjInv_eq hf.2 _
  have h2 : Function.Bijective (fun v : ι → R => A *ᵥ v) := by
    obtain ⟨u, rfl⟩ := hA
    refine Function.bijective_iff_has_inverse.2 ⟨fun v => (↑u⁻¹ : Matrix ι ι R) *ᵥ v, fun v => ?_, fun v => ?_⟩
    · simp [Matrix.mulVec_mulVec]
    · simp [Matrix.mulVec_mulVec]
  have h3 : Function.Bijective (fun v : ι → R => -v) := (Equiv.neg _).bijective
  have e : (fun (t : ι → R) (k : ι) => -∑ m, A k m * f (t m)) =
      (fun v : ι → R => -v) ∘ (fun v : ι → R => A *ᵥ v) ∘ (fun t : ι → R => fun m => f (t m)) := by
    funext t k
    simp [Matrix.mulVec, dotProduct]
  rw [e]
  exact h3.comp (h2.comp h1)

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem cA_bijective (σ : E →ₐ[F] E) : Function.Bijective (cA σ) := by
  have hσ : Function.Bijective σ := by
    refine ⟨σ.toRingHom.injective, ?_⟩
    exact (LinearMap.injective_iff_surjective (f := σ.toLinearMap)).1 σ.toRingHom.injective
  let e : E ≃ₐ[F] E := AlgEquiv.ofBijective σ hσ
  have : (cA σ : AE F E → AE F E) = Algebra.TensorProduct.congr (AlgEquiv.refl (R := AF F) (A₁ := AF F)) e := by
    funext x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul a b => simp [cA, e]
    | add x y hx hy => rw [map_add, map_add, hx, hy]
  rw [this]
  exact AlgEquiv.bijective _

theorem planeCoef_inv : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    {n n₁ i₀ i₁ : ℕ} (Y : Spc F E n) (Y₁ : Spc F E n₁) (H : Plane E n n₁), H.IsAdapted σ B Y Y₁ i₀ i₁ → Y.L.IsLattice E →
    planeCoef H * planeMat H = 1 ∧ planeMat H * planeCoef H = 1 := by
  intro F E _ _ _ _ _ σ B n n₁ i₀ i₁ Y Y₁ H hH hL
  have h : n₁ + 2 = n := hH.rank.symm
  set e : Fin n₁ ⊕ Fin 2 ≃ Fin n := finSumFinEquiv.trans (finCongr h) with he
  set Q : Matrix (Fin n) (Fin n) E := (planeMat H).submatrix id e.symm with hQdef
  have hsub : (Y.L : Set (Fin n → E)) ⊆ LinearMap.range Q.mulVecLin := by
    intro z hz
    obtain ⟨s, t, u, -, -, -, rfl⟩ := hH.split z hz
    refine ⟨(Sum.elim u ![s, t]) ∘ e.symm, ?_⟩
    show Q *ᵥ ((Sum.elim u ![s, t]) ∘ e.symm) = s • H.x + H.ι *ᵥ u + t • H.y
    rw [hQdef, Matrix.submatrix_mulVec_equiv]
    funext i
    simp [planeMat, Matrix.mulVec, dotProduct, Fintype.sum_sum_type, Fin.sum_univ_two]
    ring
  have hr : LinearMap.range Q.mulVecLin = ⊤ := by
    rw [eq_top_iff, ← hL.span_eq_top]
    exact Submodule.span_le.2 hsub
  have hQ : IsUnit Q := by
    rw [← Matrix.mulVec_surjective_iff_isUnit]
    intro v
    have hv : v ∈ LinearMap.range Q.mulVecLin := hr ▸ Submodule.mem_top
    obtain ⟨x, hx⟩ := hv
    exact ⟨x, hx⟩
  have hQd : IsUnit Q.det := (Matrix.isUnit_iff_isUnit_det Q).1 hQ
  have hC : planeCoef H = Q⁻¹.submatrix e id := by
    unfold planeCoef
    rw [dif_pos h]
  have hPm : planeMat H = Q.submatrix id e := by
    rw [hQdef]
    ext i k
    simp
  constructor
  · rw [hC, hPm, ← Matrix.submatrix_mul Q⁻¹ Q e id e Function.bijective_id, Matrix.nonsing_inv_mul _ hQd]
    exact Matrix.submatrix_one_equiv e
  · rw [hC, hPm, Matrix.submatrix_mul_equiv, Matrix.mul_nonsing_inv _ hQd]
    exact Matrix.submatrix_one_equiv (Equiv.refl _)

theorem split_bijective : ∀ {R : Type} [CommRing R] {n₁ d₁ : ℕ}, Function.Bijective (fun C : Matrix (Fin n₁ ⊕ Fin 2) (Fin d₁ ⊕ Fin 2) R =>
    ((fun k : Ic d₁ n₁ => C (posS k).1 (posS k).2, fun k : Ic d₁ n₁ => C (posT k).1 (posT k).2), C.submatrix Sum.inl Sum.inl)) := by
  intro R _ n₁ d₁
  constructor
  · intro C C' h
    simp only [Prod.mk.injEq] at h
    obtain ⟨⟨hs, ht⟩, hb⟩ := h
    ext i j
    rcases i with a | i
    · rcases j with c | j
      · exact congrFun (congrFun hb a) c
      · fin_cases j
        · exact congrFun ht (.inr a)
        · exact congrFun hs (.inr a)
    · fin_cases i
      · exact congrFun ht (.inl j)
      · exact congrFun hs (.inl j)
  · rintro ⟨⟨s, t⟩, b⟩
    refine ⟨Matrix.of fun i j => match i, j with
      | .inl a, .inl c => b a c
      | .inl a, .inr j => if j = 0 then t (.inr a) else s (.inr a)
      | .inr i, j => if i = 0 then t (.inl j) else s (.inl j), ?_⟩
    refine Prod.ext (Prod.ext (funext fun k => ?_) (funext fun k => ?_)) ?_
    · rcases k with j | a <;> simp [posS]
    · rcases k with j | a <;> simp [posT]
    · ext a c
      rfl

theorem form_swap {F E : Type} [Field F] [Field E] [Algebra F E] (σ : E →ₐ[F] E) (hσ : ∀ x, σ (σ x) = x) {n : ℕ}
    (J : Matrix (Fin n) (Fin n) E) (c : E) (hJ : ∀ i j, σ (J j i) = c * J i j) (x y : Fin n → E) :
    σ (form σ J x y) = c * form σ J y x := by
  simp only [form, dotProduct, Matrix.mulVec, map_sum, map_mul, hσ, hJ, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem planeGram_apply {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) {m m₁ : ℕ} (J : Matrix (Fin m) (Fin m) E) (H : Plane E m m₁) (i k : Fin m₁ ⊕ Fin 2) :
    planeGram σ J H i k = form σ J (fun r => planeMat H r i) (fun r => planeMat H r k) := by
  simp only [planeGram, form, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, dotProduct, Matrix.mulVec,
    Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => ?_
  ring

theorem planeGram_det_ne_zero {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) {m m₁ : ℕ} (J : Matrix (Fin m) (Fin m) E) (H : Plane E m m₁) (hJ : J.det ≠ 0)
    (h1 : planeCoef H * planeMat H = 1) (h2 : planeMat H * planeCoef H = 1) : (planeGram σ J H).det ≠ 0 := by
  have hJu : IsUnit J.det := isUnit_iff_ne_zero.2 hJ
  have hm : (planeMat H).map σ * (planeCoef H).map σ = 1 := by
    have := Matrix.map_mul (L := planeMat H) (M := planeCoef H) (f := (σ : E →+* E))
    simp only [RingHom.coe_coe] at this
    rw [← this, h2]
    exact Matrix.map_one _ (map_zero _) (map_one _)
  have key : planeGram σ J H * ((planeCoef H).map σ * J⁻¹ * (planeCoef H)ᵀ) = 1 := by
    calc planeGram σ J H * ((planeCoef H).map σ * J⁻¹ * (planeCoef H)ᵀ)
        = (planeMat H)ᵀ * (J * (((planeMat H).map σ * (planeCoef H).map σ) * (J⁻¹ * (planeCoef H)ᵀ))) := by
          simp only [planeGram, Matrix.mul_assoc]
      _ = 1 := by
          rw [hm, Matrix.one_mul, ← Matrix.mul_assoc J, Matrix.mul_nonsing_inv _ hJu, Matrix.one_mul,
            ← Matrix.transpose_mul, h1, Matrix.transpose_one]
  exact isUnit_iff_ne_zero.1 (Matrix.isUnit_det_of_right_inverse key)

theorem planeMat_inl {E : Type} [Field E] {m m₁ : ℕ} (H : Plane E m m₁) (j : Fin m₁) :
    (fun r => planeMat H r (.inl j)) = H.ι *ᵥ Pi.single j 1 := by
  rw [Matrix.mulVec_single_one]
  rfl

theorem plane_mat_inr_zero {E : Type} [Field E] {m m₁ : ℕ} (H : Plane E m m₁) :
    (fun r => planeMat H r (.inr 0)) = H.x := by
  funext r; simp [planeMat]

theorem plane_mat_inr_one {E : Type} [Field E] {m m₁ : ℕ} (H : Plane E m m₁) :
    (fun r => planeMat H r (.inr 1)) = H.y := by
  funext r; simp [planeMat]

theorem pairMat_isUnit : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    {n d n₁ d₁ r s r' s' i₀ i₁ j₀ j₁ : ℕ} (X : Spc F E n) (W : Spc F E d) (X₁ : Spc F E n₁) (W₁ : Spc F E d₁)
    (H : Plane E n n₁) (H' : Plane E d d₁), (∀ x, σ (σ x) = x) → X.IsHerm σ B r s → W.IsSkew σ B r' s' →
    H.IsAdapted σ B X X₁ j₀ j₁ → H'.IsAdapted σ B W W₁ i₀ i₁ → X.J.det ≠ 0 → W.J.det ≠ 0 →
    planeCoef H * planeMat H = 1 → planeMat H * planeCoef H = 1 →
    planeCoef H' * planeMat H' = 1 → planeMat H' * planeCoef H' = 1 →
    IsUnit (Matrix.of fun k m : Ic d₁ n₁ => planeGram σ X.J H (posS k).1 (posT m).1 * planeGram σ W.J H' (posS k).2 (posT m).2) := by
  intro F E _ _ _ _ _ σ B n d n₁ d₁ r s r' s' i₀ i₁ j₀ j₁ X W X₁ W₁ H H' hσ hX hW hH hH' hXd hWd hC hPC hC' hPC'
  have fs : ∀ x y, form σ X.J y x = σ (form σ X.J x y) := fun x y => by
    rw [form_swap σ hσ X.J 1 (fun i j => by rw [one_mul]; exact hX.herm i j), one_mul]
  have fsW : ∀ x y, form σ W.J y x = -σ (form σ W.J x y) := fun x y => by
    rw [form_swap σ hσ W.J (-1) (fun i j => by rw [neg_one_mul]; exact hW.skew i j), neg_one_mul, neg_neg]
  have gX10 : planeGram σ X.J H (.inr 1) (.inr 0) = 1 := by
    rw [planeGram_apply, plane_mat_inr_one, plane_mat_inr_zero, fs, hH.xy, map_one]
  have gX1L : ∀ b, planeGram σ X.J H (.inr 1) (.inl b) = 0 := fun b => by
    rw [planeGram_apply, plane_mat_inr_one, planeMat_inl, fs, (hH.orth _).2, map_zero]
  have gX0L : ∀ b, planeGram σ X.J H (.inr 0) (.inl b) = 0 := fun b => by
    rw [planeGram_apply, plane_mat_inr_zero, planeMat_inl, fs, (hH.orth _).1, map_zero]
  have gXL0 : ∀ a, planeGram σ X.J H (.inl a) (.inr 0) = 0 := fun a => by
    rw [planeGram_apply, planeMat_inl, plane_mat_inr_zero, (hH.orth _).1]
  have gXLL : ∀ a b, planeGram σ X.J H (.inl a) (.inl b) = X₁.J a b := fun a b => by
    rw [← hH.gram]
    rfl
  have gW10 : planeGram σ W.J H' (.inr 1) (.inr 0) = -1 := by
    rw [planeGram_apply, plane_mat_inr_one, plane_mat_inr_zero, fsW, hH'.xy, map_one]
  have hGX := planeGram_det_ne_zero σ X.J H hXd hC hPC
  have hX1 : X₁.J.det ≠ 0 := by
    have hb : planeGram σ X.J H = Matrix.fromBlocks X₁.J (planeGram σ X.J H).toBlocks₁₂ 0
        (planeGram σ X.J H).toBlocks₂₂ := by
      ext i k
      rcases i with a | i <;> rcases k with b | k
      · simp [gXLL]
      · rfl
      · fin_cases i
        · simp [gX0L]
        · simp [gX1L]
      · rfl
    intro h0
    apply hGX
    rw [hb, Matrix.det_fromBlocks_zero₂₁, h0, zero_mul]
  have hMb : (Matrix.of fun k m : Ic d₁ n₁ =>
      planeGram σ X.J H (posS k).1 (posT m).1 * planeGram σ W.J H' (posS k).2 (posT m).2) =
      Matrix.fromBlocks (planeGram σ W.J H') 0 0 (-X₁.J) := by
    ext k m
    rcases k with j | a <;> rcases m with j' | b
    · simp [posS, posT, gX10]
    · simp [posS, posT, gX1L]
    · simp [posS, posT, gXL0]
    · simp [posS, posT, gXLL, gW10]
  rw [hMb, Matrix.isUnit_iff_isUnit_det, Matrix.det_fromBlocks_zero₂₁, isUnit_iff_ne_zero]
  refine mul_ne_zero (planeGram_det_ne_zero σ W.J H' hWd hC' hPC') ?_
  rw [Matrix.det_neg]
  exact mul_ne_zero (pow_ne_zero _ (neg_ne_zero.2 one_ne_zero)) hX1

theorem planeT_bijective : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    {n d n₁ d₁ r s r' s' i₀ i₁ j₀ j₁ : ℕ} (X : Spc F E n) (W : Spc F E d) (X₁ : Spc F E n₁) (W₁ : Spc F E d₁)
    (H : Plane E n n₁) (H' : Plane E d d₁), B.IsGood σ → X.IsHerm σ B r s → W.IsSkew σ B r' s' →
    H.IsAdapted σ B X X₁ j₀ j₁ → H'.IsAdapted σ B W W₁ i₀ i₁ → Function.Bijective (planeT σ X W H H') := by
  intro F E _ _ _ _ _ σ B n d n₁ d₁ r s r' s' i₀ i₁ j₀ j₁ X W X₁ W₁ H H' hB hX hW hH hH'
  obtain ⟨w⟩ : Nonempty (InfinitePlace F) := inferInstance
  have hσ : ∀ x, σ (σ x) = x := fun x => by
    apply ((B.emb w).1 : E →+* ℂ).injective
    rw [hB.cm.2.2.2, hB.cm.2.2.2, star_star]
  have hXd : X.J.det ≠ 0 := fun h0 => by
    apply GlobalTheory.RatDarboux.det_ne_zero_of_isCartan (hX.cartan w)
    have := ((B.emb w).1 : E →+* ℂ).map_det X.J
    rw [h0, map_zero] at this
    exact this.symm
  have hWd : W.J.det ≠ 0 := fun h0 => by
    apply GlobalTheory.RatDarboux.det_ne_zero_of_isCartan (hW.cartan w)
    have := ((B.emb w).1 : E →+* ℂ).map_det W.J
    rw [h0, map_zero] at this
    rw [Matrix.det_smul]
    exact mul_eq_zero_of_right _ this.symm
  have hP := planeCoef_inv σ B X X₁ H hH hX.lat
  have hP' := planeCoef_inv σ B W W₁ H' hH' hW.lat
  have hM := pairMat_isUnit σ B X W X₁ W₁ H H' hσ hX hW hH hH' hXd hWd hP.1 hP.2 hP'.1 hP'.2
  have hm : ∀ {a b c : Type} [Fintype b] (A : Matrix a b E) (C : Matrix b c E), incM F A * incM F C = incM F (A * C) :=
    fun A C => (Matrix.map_mul (f := inclR (F := F) (AF F))).symm
  have h1 : ∀ {a : Type} [Fintype a] [DecidableEq a], incM F (1 : Matrix a a E) = 1 := fun {a} _ _ =>
    Matrix.map_one _ (map_zero _) (map_one _)
  have hc : Function.Bijective (coefLin (F := F) H H') := by
    refine Function.bijective_iff_has_inverse.2 ⟨fun v : Matrix (Fin n₁ ⊕ Fin 2) (Fin d₁ ⊕ Fin 2) (AE F E) =>
      incM F (planeMat H) * v * (incM F (planeMat H'))ᵀ, ?_, ?_⟩
    · intro u
      have e1 : incM F (planeMat H) * incM F (planeCoef H) = 1 := by rw [hm, hP.2, h1]
      have e2 : (incM F (planeCoef H'))ᵀ * (incM F (planeMat H'))ᵀ = 1 := by
        rw [← Matrix.transpose_mul, hm, hP'.2, h1, Matrix.transpose_one]
      show incM F (planeMat H) * (incM F (planeCoef H) * u * (incM F (planeCoef H'))ᵀ) * (incM F (planeMat H'))ᵀ = u
      calc _ = (incM F (planeMat H) * incM F (planeCoef H)) * u *
            ((incM F (planeCoef H'))ᵀ * (incM F (planeMat H'))ᵀ) := by simp only [Matrix.mul_assoc]
        _ = u := by rw [e1, e2, Matrix.one_mul, Matrix.mul_one]
    · intro u
      have e1 : incM F (planeCoef H) * incM F (planeMat H) = 1 := by rw [hm, hP.1, h1]
      have e2 : (incM F (planeMat H'))ᵀ * (incM F (planeCoef H'))ᵀ = 1 := by
        rw [← Matrix.transpose_mul, hm, hP'.1, h1, Matrix.transpose_one]
      show incM F (planeCoef H) * (incM F (planeMat H) * u * (incM F (planeMat H'))ᵀ) * (incM F (planeCoef H'))ᵀ = u
      calc _ = (incM F (planeCoef H) * incM F (planeMat H)) * u *
            ((incM F (planeMat H'))ᵀ * (incM F (planeCoef H'))ᵀ) := by simp only [Matrix.mul_assoc]
        _ = u := by rw [e1, e2, Matrix.one_mul, Matrix.mul_one]
  set A : Matrix (Ic d₁ n₁) (Ic d₁ n₁) (AE F E) := (Matrix.of fun k m : Ic d₁ n₁ =>
    planeGram σ X.J H (posS k).1 (posT m).1 * planeGram σ W.J H' (posS k).2 (posT m).2).map (inclR (F := F) (AF F)) with hA
  have hAu : IsUnit A := by
    rw [Matrix.isUnit_iff_isUnit_det] at hM ⊢
    have := (inclR (F := F) (E := E) (AF F)).map_det (Matrix.of fun k m : Ic d₁ n₁ =>
      planeGram σ X.J H (posS k).1 (posT m).1 * planeGram σ W.J H' (posS k).2 (posT m).2)
    rw [RingHom.mapMatrix_apply] at this
    rw [hA, ← this]
    exact hM.map _
  have h2 := split_bijective (R := AE F E) (n₁ := n₁) (d₁ := d₁)
  have h3 := pair_bijective A hAu (cA σ) (cA_bijective σ)
  have h4 := coords_bijective (ι := Ic d₁ n₁) (bA F E)
  have h4' := coords_bijective (ι := Ic d₁ n₁) (bA' F E)
  have key : ⇑(planeT σ X W H H') =
      (Prod.map (Prod.map (fun (s : Ic d₁ n₁ → AE F E) (k : Kc F E d₁ n₁) => (bA F E).repr (s k.1) k.2)
        (fun (s : Ic d₁ n₁ → AE F E) (k : Kc F E d₁ n₁) => (bA' F E).repr (s k.1) k.2)) id) ∘
      (Prod.map (Prod.map id (fun (t : Ic d₁ n₁ → AE F E) (k : Ic d₁ n₁) => -∑ m, A k m * cA σ (t m))) id) ∘
      (fun C : Matrix (Fin n₁ ⊕ Fin 2) (Fin d₁ ⊕ Fin 2) (AE F E) =>
        ((fun k : Ic d₁ n₁ => C (posS k).1 (posS k).2, fun k : Ic d₁ n₁ => C (posT k).1 (posT k).2),
          C.submatrix Sum.inl Sum.inl)) ∘ ⇑(coefLin (F := F) H H') := by
    funext u
    rfl
  rw [key]
  exact ((h4.prodMap h4').prodMap Function.bijective_id).comp
    (((Function.bijective_id.prodMap h3).prodMap Function.bijective_id).comp (h2.comp hc))

end GlobalTheory.ThK.PlaneBij
