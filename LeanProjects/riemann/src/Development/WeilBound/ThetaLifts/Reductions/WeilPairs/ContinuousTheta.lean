import Mathlib
import Development.WeilBound.ThetaLifts.Reductions.WeilPairs.WeilPairData.ImportsBis
open scoped TensorProduct Matrix BoundedContinuousFunction ContDiff
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.IndefR.DatumF MeasureTheory Matrix GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.RealWeil GlobalTheory.RealWeilF
open Classical

namespace PositivityTheory.ThKW.RealC

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem tmul_split {R : Type} [CommRing R] [Algebra F R] (a : R) (x : E) :
    a ⊗ₜ[F] x = (a ⊗ₜ[F] (1 : E)) * ((1 : R) ⊗ₜ[F] x) := by
  rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]

theorem star_theta_one {σ : E →ₐ[F] E} {τ : E →+* ℂ} (hτ : ∀ x, τ (σ x) = star (τ x))
    {θ : Ainf F ⊗[F] E →+* ℂ} (h : IsInfEmbF τ θ) (a : Ainf F) :
    star (θ (a ⊗ₜ[F] (1 : E))) = θ (a ⊗ₜ[F] (1 : E)) := by
  refine (NumberField.InfiniteAdeleRing.denseRange_algebraMap (K := F)).induction_on
    (p := fun b => star (θ (b ⊗ₜ[F] (1 : E))) = θ (b ⊗ₜ[F] (1 : E))) a (isClosed_eq h.2.star h.2) (fun x => ?_)
  have e : (algebraMap F (Ainf F) x) ⊗ₜ[F] (1 : E) = (1 : Ainf F) ⊗ₜ[F] algebraMap F E x := by
    rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul]
  show star (θ ((algebraMap F (Ainf F) x) ⊗ₜ[F] (1 : E))) = θ ((algebraMap F (Ainf F) x) ⊗ₜ[F] (1 : E))
  rw [e, h.1, ← hτ, σ.commutes]

theorem infPart_tmul (a : AF F) (x : E) : infPartF F E (a ⊗ₜ[F] x) = fstA F a ⊗ₜ[F] x := rfl

theorem theta_inc {τ : E →+* ℂ} {θ : Ainf F ⊗[F] E →+* ℂ} (h : IsInfEmbF τ θ) (x : E) :
    θ (infPartF F E (incAF F E x)) = τ x := by
  have : infPartF F E (incAF F E x) = fstA F 1 ⊗ₜ[F] x := rfl
  rw [this, map_one, h.1]

theorem theta_conj {σ : E →ₐ[F] E} {τ : E →+* ℂ} (hτ : ∀ x, τ (σ x) = star (τ x))
    {θ : Ainf F ⊗[F] E →+* ℂ} (h : IsInfEmbF τ θ) (z : AEF F E) :
    θ (infPartF F E (cAF σ z)) = star (θ (infPartF F E z)) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a x =>
    have e : cAF σ (a ⊗ₜ[F] x) = a ⊗ₜ[F] σ x := rfl
    rw [e, infPart_tmul, infPart_tmul, tmul_split _ (σ x), tmul_split _ x, map_mul, map_mul, h.1, h.1, star_mul',
      star_theta_one hτ h, hτ]
  | add a b ha hb => simp only [map_add, ha, hb, star_add]

theorem continuous_theta {τ : E →+* ℂ} {θ : Ainf F ⊗[F] E →+* ℂ} (h : IsInfEmbF τ θ) :
    Continuous (θ.comp (infPartF F E)) := by
  haveI := isModuleTopology_AE F E
  refine IsModuleTopology.continuous_of_ringHom (R := AF F) _ ?_
  exact h.2.comp (continuous_fst (X := Ainf F) (Y := Af F))

theorem trace_quad {σ : E →ₐ[F] E} (h2 : Module.finrank F E = 2) (hg : IsGalois ℚ E) {ξ : E} (hξ : ξ ≠ 0)
    (hσ : σ ξ = -ξ) (x : E) : algebraMap F E (Algebra.trace F E x) = x + σ x := by
  haveI : FiniteDimensional F E := Module.Finite.of_restrictScalars_finite ℚ F E
  haveI : IsGalois F E := IsGalois.tower_top_of_isGalois ℚ F E
  let s : E ≃ₐ[F] E := AlgEquiv.ofBijective σ σ.bijective
  have hs : (1 : E ≃ₐ[F] E) ≠ s := by
    intro e
    have : ξ = σ ξ := DFunLike.congr_fun e ξ
    rw [hσ] at this
    exact hξ (CharZero.eq_neg_self_iff.1 this)
  have hu : ({1, s} : Finset (E ≃ₐ[F] E)) = Finset.univ := by
    apply Finset.eq_univ_of_card
    rw [Finset.card_pair hs, ← Nat.card_eq_fintype_card, IsGalois.card_aut_eq_finrank, h2]
  rw [trace_eq_sum_automorphisms, ← hu, Finset.sum_pair hs]
  rfl

theorem trace_tens {σ : E →ₐ[F] E} (ht : ∀ x, algebraMap F E (Algebra.trace F E x) = x + σ x) (y : AEF F E) :
    (Algebra.trace (AF F) (AEF F E) y) ⊗ₜ[F] (1 : E) = y + cAF σ y := by
  haveI : FiniteDimensional F E := Module.Finite.of_restrictScalars_finite ℚ F E
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul r x =>
    have h1 : Algebra.trace (AF F) (AF F ⊗[F] E) ((1 : AF F) ⊗ₜ[F] x) = algebraMap F (AF F) (Algebra.trace F E x) := by
      rw [Algebra.trace_apply, Algebra.trace_apply, ← Algebra.baseChange_lmul, LinearMap.trace_baseChange]
    have h2 : r ⊗ₜ[F] x = r • ((1 : AF F) ⊗ₜ[F] x) := by rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    have e : cAF σ (r ⊗ₜ[F] x) = r ⊗ₜ[F] σ x := rfl
    rw [e, ← TensorProduct.tmul_add, ← ht]
    conv_lhs => rw [h2, LinearMap.map_smul, h1, smul_eq_mul, mul_comm, ← Algebra.smul_def, TensorProduct.smul_tmul]
    rw [Algebra.algebraMap_eq_smul_one]
  | add y y' hy hy' => simp only [map_add, TensorProduct.add_tmul, hy, hy']; abel

theorem herm_map {σ : E →ₐ[F] E} {τ : E →+* ℂ} (hτ : ∀ x, τ (σ x) = star (τ x)) {n : ℕ}
    {J : Matrix (Fin n) (Fin n) E} (hJ : IsHermND σ J) : (J.map τ)ᴴ = J.map τ := by
  ext i j
  rw [conjTranspose_apply, map_apply, map_apply, ← hτ, hJ.1]

theorem unit_map {σ : E →ₐ[F] E} (τ : E →+* ℂ) {n : ℕ}
    {J : Matrix (Fin n) (Fin n) E} (hJ : IsHermND σ J) : IsUnit (J.map τ).det := by
  have : (J.map τ).det = τ J.det := (RingHom.map_det τ J).symm
  rw [this]
  exact ((map_ne_zero τ).2 hJ.2).isUnit

theorem inv_map {σ : E →ₐ[F] E} (τ : E →+* ℂ) {n : ℕ}
    {J : Matrix (Fin n) (Fin n) E} (hJ : IsHermND σ J) : (J.map τ)⁻¹ = J⁻¹.map τ := by
  refine inv_eq_right_inv ?_
  rw [← Matrix.map_mul, mul_nonsing_inv _ hJ.2.isUnit, Matrix.map_one _ (map_zero _) (map_one _)]

theorem re_xi {σ : E →ₐ[F] E} {τ : E →+* ℂ} (hτ : ∀ x, τ (σ x) = star (τ x)) {ξ : E} (hσ : σ ξ = -ξ) :
    (τ ξ).re = 0 := by
  have := congrArg Complex.re (hτ ξ)
  rw [hσ, map_neg] at this
  simp at this
  linarith

theorem im_xi {σ : E →ₐ[F] E} {τ : E →+* ℂ} (hτ : ∀ x, τ (σ x) = star (τ x)) {ξ : E} (hξ : ξ ≠ 0) (hσ : σ ξ = -ξ) :
    (τ ξ).im ≠ 0 := fun h => (map_ne_zero τ).2 hξ (Complex.ext (re_xi hτ hσ) h)

theorem compAt_unitary {σ : E →ₐ[F] E} {tau : InfinitePlace F → (E →+* ℂ)} (hτ : ∀ w x, tau w (σ x) = star (tau w x))
    {θ : InfinitePlace F → (Ainf F ⊗[F] E →+* ℂ)} (hθ : IsInfFamF tau θ) {n : ℕ} (J : Matrix (Fin n) (Fin n) E)
    (g : GAF σ J) (w : InfinitePlace F) :
    (compAtF θ w (mtF σ J g))ᴴ * J.map (tau w) * compAtF θ w (mtF σ J g) = J.map (tau w) := by
  have hg : Formalism.UG.cT (cAF σ) (mtF σ J g) * J.map (incAF F E) * mtF σ J g = J.map (incAF F E) := g.2
  have h1 := congrArg (compAtF θ w) hg
  have h2 : compAtF θ w (J.map (incAF F E)) = J.map (tau w) := by
    ext i j
    exact theta_inc (hθ w) _
  have h3 : compAtF θ w (Formalism.UG.cT (cAF σ) (mtF σ J g)) = (compAtF θ w (mtF σ J g))ᴴ := by
    ext i j
    exact theta_conj (hτ w) (hθ w) _
  rw [← h2, ← h3]
  refine Eq.trans ?_ h1
  unfold compAtF
  rw [Matrix.map_mul, Matrix.map_mul]

theorem compAt_mul_inv {σ : E →ₐ[F] E} (θ : InfinitePlace F → (Ainf F ⊗[F] E →+* ℂ)) {n : ℕ}
    (J : Matrix (Fin n) (Fin n) E) (g : GAF σ J) (w : InfinitePlace F) :
    compAtF θ w (mtF σ J g) * compAtF θ w (mtF σ J g⁻¹) = 1 := by
  have : mtF σ J 1 = 1 := by unfold mtF; rw [map_one]; rfl
  unfold compAtF
  rw [← Matrix.map_mul, ← GlobalTheory.WeilPartsF.mtF_mul, mul_inv_cancel, this, Matrix.map_one _ (map_zero _) (map_one _)]

theorem continuous_mt (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) :
    Continuous (mtF σ J) ∧ Continuous fun g : GAF σ J => mtF σ J g⁻¹ := by
  have h : Continuous fun g : GAF σ J => matHomF σ J g := continuous_subtype_val
  refine ⟨Units.continuous_val.comp h, ?_⟩
  have e : (fun g : GAF σ J => mtF σ J g⁻¹) = fun g => ((matHomF σ J g)⁻¹).1 := by
    funext g
    unfold mtF
    rw [map_inv]
  rw [e]
  exact Units.continuous_coe_inv.comp h

end PositivityTheory.ThKW.RealC
