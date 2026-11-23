import Development.WeilBound.CoreStatements.PublishedTheorems.SmoothVectorEstimates.WhittakerVanishingImpliesZero
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CuspRapidDecaySiegelGL

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter BoundedContinuousFunction
open GlobalTheory.CuspGeneric GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.AutomorphicL2Unitary GlobalTheory.UnitaryBC GlobalTheory.DiscSpec GlobalTheory.LFun Formalism.UG Formalism.L2.Host

namespace PositivityTheory.jumpWindows.InverseDerivativeContinuity

section Lin

theorem lin_bound {V W : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    [NormedAddCommGroup W] [NormedSpace ℝ W] (L : V →ₗ[ℝ] W) : ∃ K, 0 ≤ K ∧ ∀ x, ‖L x‖ ≤ K * ‖x‖ :=
  ⟨‖LinearMap.toContinuousLinearMap L‖, norm_nonneg _, fun x => (LinearMap.toContinuousLinearMap L).le_opNorm x⟩

theorem bil_bound {V W : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    [NormedAddCommGroup W] [NormedSpace ℝ W] (B : V →ₗ[ℝ] V →ₗ[ℝ] W) :
    ∃ K, 0 ≤ K ∧ ∀ x y, ‖B x y‖ ≤ K * ‖x‖ * ‖y‖ := by
  let B' : V →ₗ[ℝ] (V →L[ℝ] W) :=
    (LinearMap.toContinuousLinearMap : (V →ₗ[ℝ] W) ≃ₗ[ℝ] (V →L[ℝ] W)).toLinearMap ∘ₗ B
  let T := LinearMap.toContinuousLinearMap B'
  refine ⟨‖T‖, norm_nonneg _, fun x y => ?_⟩
  have e : B x y = T x y := rfl
  rw [e]
  exact ((T x).le_opNorm y).trans (mul_le_mul_of_nonneg_right (T.le_opNorm x) (norm_nonneg _))

end Lin

variable {E : Type} [Field E] [NumberField E] {a : ℕ}

theorem norm_mulL (A B : Lie E a) :
    ‖(toL (Matrix.of A * Matrix.of B) : Lie E a)‖ ≤ a * ‖A‖ * ‖B‖ := by
  have hA : 0 ≤ ‖A‖ := norm_nonneg _
  have hB : 0 ≤ ‖B‖ := norm_nonneg _
  have hC : (0 : ℝ) ≤ a * ‖A‖ * ‖B‖ := mul_nonneg (mul_nonneg (Nat.cast_nonneg a) hA) hB
  have e : (toL (Matrix.of A * Matrix.of B) : Lie E a) = fun i j => ∑ k, A i k * B k j := by
    funext i j
    simp only [toL, Matrix.of_symm_apply, Matrix.mul_apply, Matrix.of_apply]
  rw [e]
  refine (pi_norm_le_iff_of_nonneg hC).2 fun i => (pi_norm_le_iff_of_nonneg hC).2 fun j => ?_
  calc ‖∑ k, A i k * B k j‖ ≤ ∑ k, ‖A i k * B k j‖ := norm_sum_le _ _
    _ ≤ ∑ _k : Fin a, ‖A‖ * ‖B‖ := Finset.sum_le_sum fun k _ => (norm_mul_le _ _).trans
        (mul_le_mul ((norm_le_pi_norm (A i) k).trans (norm_le_pi_norm A i))
          ((norm_le_pi_norm (B k) j).trans (norm_le_pi_norm B k)) (norm_nonneg _) hA)
    _ = a * ‖A‖ * ‖B‖ := by rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_assoc]

def invL (z : Lie E a) : Lie E a := toL (Matrix.of z)⁻¹

theorem invL_one : invL (oneL E a) = oneL E a := by
  simp only [invL, oneL, toL]
  show Matrix.of.symm ((1 : Matrix (Fin a) (Fin a) (Cinf E))⁻¹) = _
  simp

theorem continuousAt_invL : ContinuousAt (invL (E := E) (a := a)) (oneL E a) := by
  have h : ContinuousAt (fun z : Matrix (Fin a) (Fin a) (Cinf E) => z⁻¹) 1 :=
    continuousAt_matrix_inv _ (by
      rw [Matrix.det_one]
      exact NormedRing.inverse_continuousAt (1 : (Cinf E)ˣ))
  exact h

variable [IsTotallyComplex E]

theorem chart_inv (g : GA E a) {x : Lie E a} (hx : x ∈ invSet E a) :
    ∃ h : GA E a, ∀ f : GA E a → ℂ, chart f g x = f h :=
  have hu : IsUnit (Matrix.of x) := hx
  ⟨g * infGL E a hu.unit, fun f => by rw [chart, dif_pos hu]⟩

theorem chart_one (f : GA E a → ℂ) (g : GA E a) : chart f g (oneL E a) = f g := by
  have e := chart_val f g 1
  rw [map_one, mul_one] at e
  exact e

theorem fderiv_chart {f : GA E a → ℂ} (hf : f ∈ Sm E a) (g : GA E a) {x : Lie E a} (hx : x ∈ invSet E a)
    (Y : Lie E a) : fderiv ℝ (chart f g) x Y = chart (lieD (toL ((Matrix.of x)⁻¹ * Matrix.of Y)) f) g x := by
  rw [chart_lieD hf _ g hx]
  congr 1
  symm
  show (toL (Matrix.of x * ((Matrix.of x)⁻¹ * Matrix.of Y)) : Lie E a) = Y
  rw [← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).1 hx), Matrix.one_mul]
  rfl

theorem norm_fderiv_chart_le {f : GA E a → ℂ} (hf : f ∈ Sm E a) {K : ℝ} (hK : 0 ≤ K)
    (hb : ∀ Z h, ‖lieD Z f h‖ ≤ K * ‖Z‖) (g : GA E a) {x : Lie E a} (hx : x ∈ invSet E a) :
    ‖fderiv ℝ (chart f g) x‖ ≤ K * (a * ‖invL x‖) := by
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun Y => ?_
  obtain ⟨h, hh⟩ := chart_inv g hx
  rw [fderiv_chart hf g hx, hh]
  calc _ ≤ K * ‖(toL ((Matrix.of x)⁻¹ * Matrix.of Y) : Lie E a)‖ := hb _ _
    _ ≤ K * (a * ‖invL x‖ * ‖Y‖) := mul_le_mul_of_nonneg_left (norm_mulL (invL x) Y) hK
    _ = _ := by ring

theorem lip {f : GA E a → ℂ} (hf : f ∈ Sm E a) {K Q r : ℝ} (hK : 0 ≤ K)
    (hb : ∀ Z h, ‖lieD Z f h‖ ≤ K * ‖Z‖) (hr : Metric.ball (oneL E a) r ⊆ invSet E a)
    (hQ : ∀ x ∈ Metric.ball (oneL E a) r, ‖invL x‖ ≤ Q) (g : GA E a)
    {x : Lie E a} (hx : x ∈ Metric.ball (oneL E a) r) :
    ‖chart f g x - f g‖ ≤ K * (a * Q) * ‖x - oneL E a‖ := by
  have h0 : oneL E a ∈ Metric.ball (oneL E a) r := Metric.mem_ball_self (lt_of_le_of_lt dist_nonneg hx)
  rw [← chart_one f g]
  exact (convex_ball _ _).norm_image_sub_le_of_norm_fderiv_le
    (fun z hz => (contDiffAt_chart hf g (hr hz)).differentiableAt (by simp))
    (fun z hz => (norm_fderiv_chart_le hf hK hb g (hr hz)).trans
      (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (hQ z hz) (Nat.cast_nonneg _)) hK)) h0 hx

theorem dd_bound {f : GA E a → ℂ} (hf : f ∈ Sm E a) {K K2 Q r : ℝ} (hK : 0 ≤ K) (hK2 : 0 ≤ K2)
    (hb1 : ∀ Z h, ‖lieD Z f h‖ ≤ K * ‖Z‖) (hb2 : ∀ Y Z h, ‖lieD Z (lieD Y f) h‖ ≤ K2 * ‖Y‖ * ‖Z‖)
    (hr : Metric.ball (oneL E a) r ⊆ invSet E a) (hQ : ∀ x ∈ Metric.ball (oneL E a) r, ‖invL x‖ ≤ Q)
    (g : GA E a) {x : Lie E a} (hx : x ∈ Metric.ball (oneL E a) r) :
    ‖fderiv ℝ (chart f g) x - fderiv ℝ (chart f g) (oneL E a)‖ ≤
      K * a * ‖invL x - oneL E a‖ + K2 * a * Q * ‖x - oneL E a‖ := by
  have hQ0 : 0 ≤ Q := (norm_nonneg _).trans (hQ x hx)
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun Y => ?_
  obtain ⟨h, hh⟩ := chart_inv g (hr hx)
  rw [_root_.sub_apply, fderiv_chart hf g (hr hx), hh]
  have e1 : fderiv ℝ (chart f g) (oneL E a) Y = lieD Y f g := rfl
  have e2 : lieD (toL ((Matrix.of x)⁻¹ * Matrix.of Y)) f h - lieD Y f h =
      lieD (toL (Matrix.of (invL x - oneL E a) * Matrix.of Y)) f h := by
    rw [lieD, lieD, lieD, ← map_sub]
    congr 1
    show (toL ((Matrix.of x)⁻¹ * Matrix.of Y) : Lie E a) - toL (Matrix.of Y) =
      toL (((Matrix.of x)⁻¹ - 1) * Matrix.of Y)
    rw [Matrix.sub_mul, Matrix.one_mul]
    rfl
  have e3 : lieD Y f h = chart (lieD Y f) g x := (hh _).symm
  have hl := lip (lieD_mem_Sm Y hf) (by positivity : 0 ≤ K2 * ‖Y‖) (fun Z h => hb2 Y Z h) hr hQ g hx
  rw [e1, show lieD (toL ((Matrix.of x)⁻¹ * Matrix.of Y)) f h - lieD Y f g =
    (lieD (toL ((Matrix.of x)⁻¹ * Matrix.of Y)) f h - lieD Y f h) + (lieD Y f h - lieD Y f g) by ring, e2, e3]
  calc _ ≤ ‖lieD (toL (Matrix.of (invL x - oneL E a) * Matrix.of Y)) f h‖ +
        ‖chart (lieD Y f) g x - lieD Y f g‖ := norm_add_le _ _
    _ ≤ K * (a * ‖invL x - oneL E a‖ * ‖Y‖) + K2 * ‖Y‖ * (a * Q) * ‖x - oneL E a‖ :=
        add_le_add ((hb1 _ _).trans (mul_le_mul_of_nonneg_left (norm_mulL _ _) hK)) hl
    _ = _ := by ring

theorem key_est {f : GA E a → ℂ} (hf : f ∈ Sm E a) {K K2 : ℝ} (hK : 0 ≤ K) (hK2 : 0 ≤ K2)
    (hb1 : ∀ Z h, ‖lieD Z f h‖ ≤ K * ‖Z‖) (hb2 : ∀ Y Z h, ‖lieD Z (lieD Y f) h‖ ≤ K2 * ‖Y‖ * ‖Z‖)
    {c : ℝ} (hc : 0 < c) : ∃ δ > 0, ∀ g, ∀ M ∈ Metric.ball (oneL E a) δ,
      ‖chart f g M - chart f g (oneL E a) - fderiv ℝ (chart f g) (oneL E a) (M - oneL E a)‖ ≤
        c * ‖M - oneL E a‖ := by
  set Q : ℝ := ‖oneL E a‖ + 1 with hQdef
  have ev1 : ∀ᶠ z in 𝓝 (oneL E a), z ∈ invSet E a := isOpen_invSet.mem_nhds isUnit_one
  have ev2 : ∀ᶠ z in 𝓝 (oneL E a), ‖invL z‖ < Q :=
    continuousAt_invL.norm.eventually (Iio_mem_nhds (by show ‖invL (oneL E a)‖ < Q; rw [invL_one]; linarith))
  have hct : ContinuousAt (fun z : Lie E a => K * a * ‖invL z - oneL E a‖ + K2 * a * Q * ‖z - oneL E a‖)
      (oneL E a) :=
    ((continuousAt_invL.sub continuousAt_const).norm.const_mul _).add
      ((continuousAt_id.sub continuousAt_const).norm.const_mul _)
  have ev3 : ∀ᶠ z in 𝓝 (oneL E a), K * a * ‖invL z - oneL E a‖ + K2 * a * Q * ‖z - oneL E a‖ ≤ c :=
    hct.eventually (Iic_mem_nhds (by simp [invL_one, hc]))
  obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff_ball.1 (ev1.and (ev2.and ev3))
  have hr : Metric.ball (oneL E a) δ ⊆ invSet E a := fun z hz => (hball z hz).1
  have hQ : ∀ z ∈ Metric.ball (oneL E a) δ, ‖invL z‖ ≤ Q := fun z hz => (hball z hz).2.1.le
  refine ⟨δ, hδ, fun g M hM => ?_⟩
  exact (convex_ball _ _).norm_image_sub_le_of_norm_fderiv_le'
    (fun z hz => (contDiffAt_chart hf g (hr hz)).differentiableAt (by simp))
    (fun z hz => (dd_bound hf hK hK2 hb1 hb2 hr hQ g hz).trans (hball z hz).2.2)
    (Metric.mem_ball_self hδ) hM

section Forms

theorem bdd (π : CuspSub E a) (hπ : IsNormalised π) (ψ : π.V) : ∃ C : ℝ, ∀ g, ‖ψ.1.1 g‖ ≤ C :=
  GlobalTheory.CompanionTheory.CuspFinGL.cuspFormsBoundedGL.of_invariant (π.cusp _ ψ.2) (hπ _ ψ.2)

def toXB (π : CuspSub E a) (hπ : IsNormalised π) : π.V →ₗ[ℂ] XB E a where
  toFun ψ := BoundedContinuousFunction.ofNormedAddCommGroup ψ.1.1
    (ContAut.continuous_of_isOpen_stab E a ψ.1 (π.cusp _ ψ.2).1.level)
    (Classical.choose (bdd π hπ ψ)) (Classical.choose_spec (bdd π hπ ψ))
  map_add' _ _ := by ext; rfl
  map_smul' _ _ := by ext; rfl

theorem opLie_add (π : CuspSub E a) (Z Z' : Lie E a) (ψ : π.V) :
    π.op (.lie (Z + Z')) ψ = π.op (.lie Z) ψ + π.op (.lie Z') ψ :=
  Subtype.ext (by change lie E a (Z + Z') ψ.1 = lie E a Z ψ.1 + lie E a Z' ψ.1; rw [map_add]; rfl)

theorem opLie_smul (π : CuspSub E a) (c : ℝ) (Z : Lie E a) (ψ : π.V) :
    π.op (.lie (c • Z)) ψ = (c : ℂ) • π.op (.lie Z) ψ :=
  Subtype.ext (Subtype.ext (funext fun g => by
    change lieD (c • Z) ψ.1.1 g = (c : ℂ) * lieD Z ψ.1.1 g
    rw [lieD, lieD, map_smul, Complex.real_smul]))

theorem real_smul_XB (c : ℝ) (f : XB E a) : (c : ℂ) • f = c • f := by
  ext g
  simp [Complex.real_smul]

def dL (π : CuspSub E a) (hπ : IsNormalised π) (ψ : π.V) : Lie E a →ₗ[ℝ] XB E a where
  toFun Z := toXB π hπ (π.op (.lie Z) ψ)
  map_add' Z Z' := by rw [opLie_add, map_add]
  map_smul' c Z := by rw [opLie_smul, map_smul, RingHom.id_apply, real_smul_XB]

def B2 (π : CuspSub E a) (hπ : IsNormalised π) (ψ : π.V) : Lie E a →ₗ[ℝ] Lie E a →ₗ[ℝ] XB E a :=
  LinearMap.mk₂ ℝ (fun Y Z => dL π hπ (π.op (.lie Y) ψ) Z)
    (fun Y Y' Z => by
      show toXB π hπ (π.op (.lie Z) (π.op (.lie (Y + Y')) ψ)) =
        toXB π hπ (π.op (.lie Z) (π.op (.lie Y) ψ)) + toXB π hπ (π.op (.lie Z) (π.op (.lie Y') ψ))
      rw [opLie_add, map_add, map_add])
    (fun c Y Z => by
      show toXB π hπ (π.op (.lie Z) (π.op (.lie (c • Y)) ψ)) = c • toXB π hπ (π.op (.lie Z) (π.op (.lie Y) ψ))
      rw [opLie_smul, map_smul, map_smul, real_smul_XB])
    (fun Y Z Z' => map_add _ _ _)
    (fun c Y Z => map_smul _ _ _)

theorem lev_toXB (π : CuspSub E a) (hπ : IsNormalised π) (ψ : π.V) (S : Finset (Pl E)) :
    Lev S (toXB π hπ ψ) := by
  intro w _
  have ho : IsOpen {k | finRep E a k ψ.1 = ψ.1} := (π.cusp _ ψ.2).1.level
  have h1 : locGL E a w 1 ∈ {k | finRep E a k ψ.1 = ψ.1} := by
    show finRep E a (locGL E a w 1) ψ.1 = ψ.1
    rw [map_one, map_one]
    rfl
  refine Filter.mem_of_superset ((ho.preimage (CuspSub.continuous_locGL w)).mem_nhds h1) fun u hu => ?_
  ext g
  exact congrFun (congrArg Subtype.val hu) g

theorem orb_apply (x : XB E a) (M : Lie E a) (g : GA E a) : orb (repI E a) x M g = chart (⇑x) g M := by
  unfold orb chart
  split_ifs <;> rfl

theorem hasFDerivAt_orb (π : CuspSub E a) (hπ : IsNormalised π) (ψ : π.V) :
    HasFDerivAt (orb (repI E a) (toXB π hπ ψ)) (LinearMap.toContinuousLinearMap (dL π hπ ψ)) (oneL E a) := by
  obtain ⟨K, hK, hK'⟩ := lin_bound (dL π hπ ψ)
  obtain ⟨K2, hK2, hK2'⟩ := bil_bound (B2 π hπ ψ)
  have hb1 : ∀ Z h, ‖lieD Z ψ.1.1 h‖ ≤ K * ‖Z‖ := fun Z h =>
    (norm_coe_le_norm (dL π hπ ψ Z) h).trans (hK' Z)
  have hb2 : ∀ Y Z h, ‖lieD Z (lieD Y ψ.1.1) h‖ ≤ K2 * ‖Y‖ * ‖Z‖ := fun Y Z h =>
    (norm_coe_le_norm (B2 π hπ ψ Y Z) h).trans (hK2' Y Z)
  refine HasFDerivAt.of_isLittleO (Asymptotics.isLittleO_iff.2 fun c hc => ?_)
  obtain ⟨δ, hδ, hM⟩ := key_est ψ.1.2 hK hK2 hb1 hb2 hc
  filter_upwards [Metric.ball_mem_nhds _ hδ] with M hMb
  refine (BoundedContinuousFunction.norm_le (by positivity)).2 fun g => ?_
  have e : (orb (repI E a) (toXB π hπ ψ) M - orb (repI E a) (toXB π hπ ψ) (oneL E a) -
      (LinearMap.toContinuousLinearMap (dL π hπ ψ)) (M - oneL E a)) g =
      chart ψ.1.1 g M - chart ψ.1.1 g (oneL E a) - fderiv ℝ (chart ψ.1.1 g) (oneL E a) (M - oneL E a) := by
    simp only [BoundedContinuousFunction.coe_sub, Pi.sub_apply, orb_apply]
    rfl
  rw [e]
  exact hM g M hMb

end Forms

end PositivityTheory.jumpWindows.InverseDerivativeContinuity

namespace PositivityTheory.jumpWindows

theorem firstGeometricCondition_of_properties : S1 → G1 := by
  intro hS1 E _ _ _ a π hπ φ hφ
  have hP : PolyBd (repI E a) := ⟨1, 0, zero_le_one, fun g x => by
    rw [pow_zero, one_mul, one_mul]
    exact (norm_Rt _ _).le⟩
  have hsm := hS1 (InfinitePlace E) a (XB E a) (repI E a) hP (LinearMap.range (InverseDerivativeContinuity.toXB π hπ))
    (fun v hv => by
      obtain ⟨ψ, rfl⟩ := LinearMap.mem_range.1 hv
      exact ⟨_, InverseDerivativeContinuity.hasFDerivAt_orb π hπ ψ, fun Z => LinearMap.mem_range.2 ⟨π.op (.lie Z) ψ, rfl⟩⟩)
    (InverseDerivativeContinuity.toXB π hπ ⟨φ, hφ⟩) (LinearMap.mem_range.2 ⟨_, rfl⟩)
  exact ⟨InverseDerivativeContinuity.toXB π hπ ⟨φ, hφ⟩, rfl, hsm, InverseDerivativeContinuity.lev_toXB π hπ ⟨φ, hφ⟩⟩

end PositivityTheory.jumpWindows

end
