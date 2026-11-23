import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TensorRepresentations.TraceFormulaB
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TensorRepresentations.TraceFormulaD
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TensorRepresentations.TraceFormulaE
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TensorRepresentations.TraceFormulaG

noncomputable section

open Finset MeasureTheory

namespace ReciprocityTheory.ChartRestriction.DS

section TR

variable {n : ℕ} {G : Type*} [Group G] [MeasurableSpace G] [MeasurableInv G] {μ : Measure G} [μ.IsInvInvariant]

theorem tf_inner_conj_conj (a b : ℂ) :
    inner ℂ (starRingEnd ℂ a) (starRingEnd ℂ b) = starRingEnd ℂ (inner ℂ a b) := by
  simp only [RCLike.inner_apply, map_mul, Complex.conj_conj]

theorem tf_tr_swap (ρ : G → (PiLp 2 (fun _ : Fin n => Lp ℂ 2 μ) →L[ℂ] PiLp 2 (fun _ : Fin n => Lp ℂ 2 μ)))
    (hadj : ∀ g x y, inner ℂ (ρ g x) y = inner ℂ x (ρ g⁻¹ y))
    (J : PiLp 2 (fun _ : Fin n => Lp ℂ 2 μ) →L[ℂ] PiLp 2 (fun _ : Fin n => Lp ℂ 2 μ)) (s : Fin n → ℝ)
    (hJ : ∀ x c, J x c = (s c : ℂ) • x c) (hρJ : ∀ g x, ρ g (J x) = J (ρ g x))
    (HP : Submodule ℂ (PiLp 2 (fun _ : Fin n => Lp ℂ 2 μ))) [HP.HasOrthogonalProjection]
    (hst : ∀ g, ∀ v ∈ HP, ρ g v ∈ HP) (d : ℝ) (u w : Fin n → PiLp 2 (fun _ : Fin n => Lp ℂ 2 μ))
    (hu : ∀ c, u c ∈ HP) (hw : ∀ c, w c = (d : ℂ) • HP.starProjection (J (u c)))
    (hrep : ∀ v ∈ HP, ∀ c, ((v c : Lp ℂ 2 μ) : G → ℂ) =ᵐ[μ] fun g => inner ℂ (w c) (ρ g v))
    (c c' : Fin n) :
    inner ℂ (u c c') (w c c') = starRingEnd ℂ (inner ℂ (u c' c) (w c' c)) := by
  have hJs : ∀ x y, inner ℂ (J x) y = inner ℂ x (J y) := by
    intro x y
    simp only [PiLp.inner_apply, hJ, inner_smul_left, inner_smul_right, Complex.conj_ofReal]
  have hP : ∀ v ∈ HP, HP.starProjection v = v := fun v hv => Submodule.starProjection_eq_self_iff.2 hv
  have hwm : ∀ c, w c ∈ HP := fun c => by
    rw [hw c]; exact HP.smul_mem _ (Submodule.starProjection_apply_mem HP _)
  have k1 : ∀ g a b, inner ℂ (w a) (ρ g⁻¹ (u b)) = starRingEnd ℂ (inner ℂ (w b) (ρ g (u a))) := by
    intro g a b
    rw [inner_conj_symm, hw a, hw b, inner_smul_left, inner_smul_right, Complex.conj_ofReal]
    congr 1
    calc inner ℂ (HP.starProjection (J (u a))) (ρ g⁻¹ (u b))
        = inner ℂ (J (u a)) (HP.starProjection (ρ g⁻¹ (u b))) :=
          Submodule.inner_starProjection_left_eq_right HP _ _
      _ = inner ℂ (J (u a)) (ρ g⁻¹ (u b)) := by rw [hP _ (hst _ _ (hu b))]
      _ = inner ℂ (u a) (ρ g⁻¹ (J (u b))) := by rw [hJs, hρJ]
      _ = inner ℂ (ρ g (u a)) (J (u b)) := (hadj _ _ _).symm
      _ = inner ℂ (HP.starProjection (ρ g (u a))) (J (u b)) := by rw [hP _ (hst _ _ (hu a))]
      _ = inner ℂ (ρ g (u a)) (HP.starProjection (J (u b))) :=
          Submodule.inner_starProjection_left_eq_right HP _ _
  have k2 : ∀ g a b, inner ℂ (w a) (ρ g⁻¹ (w b)) = starRingEnd ℂ (inner ℂ (w b) (ρ g (w a))) := by
    intro g a b
    rw [inner_conj_symm, hadj]
  rw [MeasureTheory.L2.inner_def, MeasureTheory.L2.inner_def, ← integral_conj]
  have e1 : ∫ g, inner ℂ ((u c c' : Lp ℂ 2 μ) g) ((w c c' : Lp ℂ 2 μ) g) ∂μ =
      ∫ g, inner ℂ (inner ℂ (w c') (ρ g (u c))) (inner ℂ (w c') (ρ g (w c))) ∂μ := by
    refine integral_congr_ae ?_
    filter_upwards [hrep _ (hu c) c', hrep _ (hwm c) c'] with g h1 h2
    rw [h1, h2]
  have e2 : ∫ g, starRingEnd ℂ (inner ℂ ((u c' c : Lp ℂ 2 μ) g) ((w c' c : Lp ℂ 2 μ) g)) ∂μ =
      ∫ g, starRingEnd ℂ (inner ℂ (inner ℂ (w c) (ρ g (u c'))) (inner ℂ (w c) (ρ g (w c')))) ∂μ := by
    refine integral_congr_ae ?_
    filter_upwards [hrep _ (hu c') c, hrep _ (hwm c') c] with g h1 h2
    rw [h1, h2]
  rw [e1, e2, ← integral_inv_eq_self _ μ]
  refine integral_congr_ae (Filter.Eventually.of_forall fun g => ?_)
  simp only
  rw [k1, k2, tf_inner_conj_conj]

end TR

section Core

variable {n : ℕ} {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

theorem tf_single_smul_mem {D : Submodule ℂ H} {S : Submodule ℂ D} (c : Fin n) (a : ℂ) {y : D} (hy : y ∈ S) :
    (Pi.single c (a • y) : Fin n → D) ∈ tensSub S := by
  rw [tset_mem]
  intro i
  by_cases h : i = c
  · subst h; simpa using S.smul_mem a hy
  · simp [h]

theorem tf_coe_single {D : Submodule ℂ H} (c : Fin n) (a : ℂ) (y : D) :
    (fun i => (((Pi.single c (a • y) : Fin n → D) i : D) : H)) = Pi.single c (a • (y : H)) := by
  funext i
  by_cases h : i = c
  · subst h; simp
  · simp [h]

theorem tf_coe_single' {D : Submodule ℂ H} (c : Fin n) (y : D) :
    (fun i => (((Pi.single c y : Fin n → D) i : D) : H)) = Pi.single c (y : H) := by
  funext i
  by_cases h : i = c
  · subst h; simp
  · simp [h]

theorem tf_ph_memLp (dual : Bool) {lam : Fin n → ℝ} [CompleteSpace H] {ε : Fin n → Bool}
    {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {D : Submodule ℂ H} {E : Fin n → Fin n → Module.End ℂ D}
    (hσ : IsURepOn (UJset ε) σ) (hD : IsDerivedOn ε σ D E) (hsm : ∀ v : D, IsSmoothVecU ε σ v)
    {V : Submodule ℂ D} (hgap : StdGap ε lam) (hV : IsKIrrHW ε E (lowK ε lam) V)
    (hc : ∀ v ∈ V, casimir E v = (casVal lam : ℂ) • v)
    (hVK : ∀ k ∈ Kset ε, ∀ v ∈ V, ∃ w ∈ V, (w : H) = σ k v)
    (hW : ∀ v ∈ genSub E V, ∀ w ∈ genSub E V, MemLp (fun g : Formalism.REAL.UJ ε =>
      ((Real.sqrt (S7.hs (Formalism.MainNotions.S.umat g)) : ℝ) : ℂ) * inner ℂ ((w : D) : H) (σ (Formalism.MainNotions.S.umat g) ((v : D) : H)))
      2 (Formalism.REAL.muG ε))
    {y : D} (hy : y ∈ genSub E V) {f : Fin n → D} (hf : f ∈ tensSub (genSub E V)) (c : Fin n) :
    MemLp (fun g : Formalism.REAL.UJ ε => coefMap dual σ (Pi.single c (tfSgn ε c • (y : H)))
      (fun d => ((f d : D) : H)) (Formalism.MainNotions.S.umat g)) 2 (Formalism.REAL.muG ε) := by
  have h := ((coef_embed dual hσ hD hsm hgap hV hc hVK hW _ (tf_single_smul_mem c (tfSgn ε c) hy) f hf).1).2 []
  rw [tf_coe_single] at h
  exact h

theorem tfRdiag_tfPh (dual : Bool) {ε : Fin n → Bool} {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)}
    (hσ : IsURepOn (UJset ε) σ) {h : Matrix (Fin n) (Fin n) ℂ} (hh : h ∈ UJset ε) (y : H) (ζ : Fin n → H) :
    tfRdiag ε h (tfPh dual ε σ y ζ) = tfPh dual ε σ y (tensGrp dual σ h ζ) := by
  refine vectorL2_ext fun c => ?_
  rw [tfRdiag_apply, tfPh_apply, tfPh_apply, rightRegular_toL2 ε _ hh]
  refine toL2_congr_of_eq_on_UJset fun x hx => ?_
  simp only [coefMap]
  rw [tf_tensGrp_mul dual hσ hx hh]

theorem tfJ_inner (ε : Fin n → Bool) (x x' : tfL2n ε) : inner ℂ (tfJ ε x) x' = inner ℂ x (tfJ ε x') := by
  simp only [PiLp.inner_apply, tfJ_apply, inner_smul_left, inner_smul_right]
  refine sum_congr rfl fun i _ => ?_
  congr 1
  exact tf_star_sgn ε i

theorem tfFormBH_sub_left (ε : Fin n → Bool) (f f' g : Fin n → H) :
    tfFormBH ε (f - f') g = tfFormBH ε f g - tfFormBH ε f' g := by
  simp only [tfFormBH, Pi.sub_apply, inner_sub_left, mul_sub, sum_sub_distrib]

end Core

end ReciprocityTheory.ChartRestriction.DS
