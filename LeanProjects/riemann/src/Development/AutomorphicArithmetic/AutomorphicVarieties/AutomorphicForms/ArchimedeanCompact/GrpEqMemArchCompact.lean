import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.ArchimedeanCompact.InfEmbGrpEq

noncomputable section

open NumberField Matrix GlobalTheory.CuspRep GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm
open scoped ContDiff Topology

namespace UpperTheory.V.Cm

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ}

variable (E a) in

def archEq : Lie E a ≃L[ℝ] ArchMatrix E a :=
  LinearEquiv.toContinuousLinearEquiv
    ((matEq E a).toLinearEquiv : Lie E a ≃ₗ[ℝ] ArchMatrix E a)

theorem archEq_toL (x : Matrix (Fin a) (Fin a) (Cinf E)) : archEq E a (toL x) = matEq E a x := rfl

theorem archEq_symm_coe (z : archGroup E a) :
    (archEq E a).symm ((z : (ArchMatrix E a)ˣ) : ArchMatrix E a) = toL ((grpEq E a).symm z).val := by
  obtain ⟨y, rfl⟩ := (grpEq E a).surjective z
  rw [MulEquiv.symm_apply_apply, coe_grpEq, ← archEq_toL, ContinuousLinearEquiv.symm_apply_apply]

theorem isArchSmooth_of_mem {φ : GA E a → ℂ} (hφ : φ ∈ Sm E a) : IsArchSmooth φ := by
  intro g
  rw [IsExpLieAlgebra.isSmoothFun_iff]
  intro x
  have hexp : ContDiff ℝ ∞ (NormedSpace.exp : ArchMatrix E a → ArchMatrix E a) :=
    contDiff_iff_contDiffAt.2 fun X => (NormedSpace.exp_analytic (𝕂 := ℝ) X).contDiffAt
  have hc : ContDiff ℝ ∞ fun Y : archLie E a => (archEq E a).symm
      (((x * (isExpLieAlgebra E a).expG Y : archGroup E a) : (ArchMatrix E a)ˣ) : ArchMatrix E a) :=
    (archEq E a).symm.contDiff.comp (contDiff_const.mul (hexp.comp (archLie E a).subtypeL.contDiff))
  have e : (fun Y : archLie E a => archSlice φ g (x * (isExpLieAlgebra E a).expG Y)) = chart φ g ∘ fun Y : archLie E a =>
      (archEq E a).symm (((x * (isExpLieAlgebra E a).expG Y : archGroup E a) : (ArchMatrix E a)ˣ) : ArchMatrix E a) := by
    funext Y
    rw [Function.comp_apply, archEq_symm_coe, chart_val, ← infEmb_grpEq, MulEquiv.apply_symm_apply]
    rfl
  rw [e]
  exact (hφ g).comp_contDiff hc fun Y => by rw [archEq_symm_coe]; exact val_mem_invSet _

private theorem contDiffAt_one {φ : GA E a → ℂ} (hφ : IsArchSmooth φ) (g : GA E a) :
    ContDiffAt ℝ ∞ (chart φ g) (oneL E a) := by
  have h := ((isExpLieAlgebra E a).isSmoothFun_iff).1 (hφ g) 1
  set e := expPartialHomeomorph ℝ (ArchMatrix E a)
  have h1 : archEq E a (oneL E a) = 1 := map_one (matEq E a)
  have hn : e.target ∈ 𝓝 (archEq E a (oneL E a)) := by
    rw [h1]; exact e.open_target.mem_nhds (one_mem_expPartialHomeomorph_target ℝ _)
  have hl : ContDiffAt ℝ ∞ (fun x => subspaceProj (archLie E a) (e.symm (archEq E a x))) (oneL E a) :=
    (subspaceProj (archLie E a)).contDiff.contDiffAt.comp _
      (((contDiffOn_expPartialHomeomorph_symm ℝ _).contDiffAt hn).comp _ (archEq E a).contDiff.contDiffAt)
  refine (h.contDiffAt.comp _ hl).congr_of_eventuallyEq ?_
  filter_upwards [(archEq E a).continuous.continuousAt.preimage_mem_nhds hn,
    isOpen_invSet.mem_nhds (val_mem_invSet (1 : GL (Fin a) (Cinf E)))] with x hx hu
  obtain ⟨u, hu⟩ := hu
  obtain rfl : x = toL u.val := hu.symm
  rw [chart_val, ← infEmb_grpEq]
  simp only [Function.comp_apply, archSlice_apply, one_mul]
  congr 3
  refine Subtype.ext (Units.ext ?_)
  rw [IsExpLieAlgebra.coe_expG, subspaceProj_of_mem Submodule.mem_top]
  exact (e.right_inv hx).symm

theorem mem_Sm_of {φ : GA E a → ℂ} (hφ : IsArchSmooth φ) : φ ∈ Sm E a := by
  intro g x hx
  obtain ⟨u, hu⟩ := hx
  obtain rfl : x = toL u.val := hu.symm
  let L : Lie E a →L[ℝ] Lie E a := LinearMap.toContinuousLinearMap
    (LinearMap.mulLeft ℝ (u⁻¹).val : Matrix (Fin a) (Fin a) (Cinf E) →ₗ[ℝ] Matrix (Fin a) (Fin a) (Cinf E))
  have e1 : L (toL u.val) = oneL E a := u.inv_mul
  have h1 : ContDiffAt ℝ ∞ (chart φ (g * infGL E a u) ∘ L) (toL u.val) :=
    ContDiffAt.comp _ (by rw [e1]; exact contDiffAt_one hφ _) L.contDiff.contDiffAt
  refine (h1.congr_of_eventuallyEq ?_).contDiffWithinAt
  filter_upwards [isOpen_invSet.mem_nhds (val_mem_invSet u)] with x hx
  obtain ⟨v, hv⟩ := hx
  obtain rfl : x = toL v.val := hv.symm
  have e2 : L (toL v.val) = toL (u⁻¹ * v).val := rfl
  rw [Function.comp_apply, e2, chart_val, chart_val, mul_assoc, ← map_mul, mul_inv_cancel_left]

private theorem complex_unitary_iff {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ) :
    (∀ z : Fin n → ℂ, Reduction.euclidNorm (z ᵥ* M) = Reduction.euclidNorm z) ↔ M ∈ unitaryGroup (Fin n) ℂ := by
  refine ⟨fun h => ?_, fun h z => Reduction.euclidNorm_vecMul_unitary h z⟩
  let f : EuclideanSpace ℂ (Fin n) →ₗᵢ[ℂ] EuclideanSpace ℂ (Fin n) :=
    { toLinearMap := (WithLp.linearEquiv 2 ℂ (Fin n → ℂ)).symm.toLinearMap ∘ₗ M.vecMulLinear ∘ₗ
        (WithLp.linearEquiv 2 ℂ (Fin n → ℂ)).toLinearMap
      norm_map' := fun z => by
        rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
        exact h z.ofLp }
  rw [mem_unitaryGroup_iff]
  ext i j
  have := f.inner_map_map (WithLp.toLp 2 (Pi.single j 1)) (WithLp.toLp 2 (Pi.single i 1))
  have e : ∀ k, f (WithLp.toLp 2 (Pi.single k 1)) = WithLp.toLp 2 (M k) := fun k =>
    congrArg (WithLp.toLp 2) (single_one_vecMul k M)
  rw [e, e, PiLp.inner_apply, PiLp.inner_apply] at this
  rw [mul_apply, one_apply]
  simpa [Pi.single_apply, eq_comm] using this

private theorem pi_unitary_iff {ι : Type} {n : ℕ} (M : Matrix (Fin n) (Fin n) (ι → ℂ)) :
    M ∈ unitaryGroup (Fin n) (ι → ℂ) ↔ ∀ w, M.map (fun x => x w) ∈ unitaryGroup (Fin n) ℂ := by
  simp only [mem_unitaryGroup_iff, ← Matrix.ext_iff, funext_iff, mul_apply, one_apply, star_apply, map_apply,
    Finset.sum_apply, Pi.mul_apply, Pi.star_apply, ite_apply, Pi.one_apply, Pi.zero_apply]
  exact ⟨fun h w i j => h i j w, fun h i j w => h w i j⟩

theorem infAt_infGL (y : GL (Fin a) (Cinf E)) (w : InfinitePlace E) (i j : Fin a) :
    (Reduction.infAt w (infGL E a y) : Matrix (Fin a) (Fin a) w.Completion) i j =
      (InfinitePlace.Completion.ringEquivComplexOfIsComplex (IsTotallyComplex.isComplex w)).symm (y.val i j w) :=
  congrFun (infGL_entry y i j) w

theorem finAt_infGL (y : GL (Fin a) (Cinf E)) (v : IsDedekindDomain.HeightOneSpectrum (𝓞 E)) :
    Reduction.finAt v (infGL E a y) = 1 := by
  rw [← infEmb_grpEq]
  show (AdelicGLn.finiteRestrictedEquiv E a (AdelicGLn.prodEquiv E a (infEmb E a (grpEq E a y))).2) v = 1
  rw [prodEquiv_infEmb, map_one]
  rfl

omit [NumberField E] in
private theorem norm_ringEquiv (w : InfinitePlace E) (z : w.Completion) :
    ‖InfinitePlace.Completion.ringEquivComplexOfIsComplex (IsTotallyComplex.isComplex w) z‖ = ‖z‖ :=
  (InfinitePlace.Completion.isometry_extensionEmbedding w).norm_map_of_map_zero (map_zero _) z

theorem grpEq_mem_archCompact (y : GL (Fin a) (Cinf E)) :
    grpEq E a y ∈ archCompact E a ↔ y.val ∈ Matrix.unitaryGroup (Fin a) (Cinf E) := by
  change infEmb E a (grpEq E a y) ∈ Reduction.maxCompact (K := E) (n := a) ↔ _
  rw [infEmb_grpEq, Reduction.mem_maxCompact, and_iff_left fun v => by rw [finAt_infGL]; exact one_mem _,
    pi_unitary_iff]
  refine forall_congr' fun w => ?_
  rw [Reduction.mem_archCompact, ← complex_unitary_iff]
  set ψ := InfinitePlace.Completion.ringEquivComplexOfIsComplex (IsTotallyComplex.isComplex w)
  have hψ : ∀ z, ‖ψ.toRingHom z‖ = ‖z‖ := norm_ringEquiv w
  have e : ∀ z : Fin a → w.Completion,
      (fun j => ψ.toRingHom ((z ᵥ* (Reduction.infAt w (infGL E a y) : Matrix (Fin a) (Fin a) w.Completion)) j)) =
        (fun i => ψ.toRingHom (z i)) ᵥ* y.val.map (fun x => x w) := by
    intro z
    ext j
    simp only [vecMul, dotProduct, map_sum, map_mul, Matrix.map_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [infAt_infGL]
    exact congrArg _ (ψ.apply_symm_apply _)
  constructor
  · intro h z
    have hz : z = fun i => ψ.toRingHom (ψ.symm (z i)) := funext fun i => (ψ.apply_symm_apply _).symm
    rw [hz, ← e, Reduction.euclidNorm_map _ hψ, Reduction.euclidNorm_map _ hψ, h]
  · intro h z
    rw [← Reduction.euclidNorm_map _ hψ, e, h, Reduction.euclidNorm_map _ hψ]

omit [IsTotallyComplex E] in
private theorem norm_le_ht (y : GL (Fin a) (Cinf E)) :
    ‖toL y.val‖ ≤ GlobalTheory.CuspRep.height y ∧ ‖toL (y⁻¹).val‖ ≤ GlobalTheory.CuspRep.height y ∧
      GlobalTheory.CuspRep.height y ≤ 1 + ‖toL y.val‖ + ‖toL (y⁻¹).val‖ := by
  have n1 := norm_nonneg (toL y.val)
  have n2 := norm_nonneg (toL (y⁻¹).val)
  refine ⟨?_, ?_, ?_⟩ <;> first | (unfold GlobalTheory.CuspRep.height; linarith) | fail "height"

private theorem ent (y : GL (Fin a) (Cinf E)) (w : InfinitePlace E) (i j : Fin a) :
    ‖(Reduction.infAt w (infGL E a y) : Matrix (Fin a) (Fin a) w.Completion) i j‖ ≤ ‖toL y.val‖ := by
  rw [infAt_infGL, ← norm_ringEquiv, RingEquiv.apply_symm_apply]
  exact (norm_le_pi_norm (y.val i j) w).trans ((norm_le_pi_norm (toL y.val i) j).trans (norm_le_pi_norm (toL y.val) i))

variable (E a) in

theorem exists_height_le : ∃ N : ℕ, ∀ y : GL (Fin a) (Cinf E),
    AutomorphicForm.height (infGL E a y) ≤ GlobalTheory.CuspRep.height y ^ N := by
  refine ⟨∑ w : InfinitePlace E, w.mult, fun y => ?_⟩
  unfold AutomorphicForm.height
  rw [finprod_eq_one_of_forall_eq_one fun v => by rw [finAt_infGL, locHeight_one], mul_one,
    ← Finset.prod_pow_eq_pow_sum]
  refine Finset.prod_le_prod (fun w _ => (pow_pos (locHeight_pos _) _).le) fun w _ =>
    pow_le_pow_left₀ (locHeight_pos _).le ?_ _
  refine locHeight_le (GlobalTheory.CuspRep.one_le_height y) (fun i j => (ent y w i j).trans (norm_le_ht y).1) fun i j => ?_
  have := ent y⁻¹ w i j
  rw [map_inv, Reduction.infAt_inv] at this
  exact this.trans (norm_le_ht y).2.1

omit [IsTotallyComplex E] in
private theorem loc_le_height (g : GA E a) (w : InfinitePlace E) :
    locHeight (Reduction.infAt w g) ≤ AutomorphicForm.height g := by
  classical
  refine (le_self_pow₀ (one_le_locHeight _) (InfinitePlace.mult_pos (w := w)).ne').trans (le_trans ?_
    (le_mul_of_one_le_right (zero_le_one.trans (one_le_prod_locHeight g)) (one_le_finprod_locHeight g)))
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ w)]
  exact le_mul_of_one_le_right (pow_nonneg (locHeight_pos _).le _) (Finset.prod_induction _ (fun x : ℝ => 1 ≤ x)
    (fun _ _ => one_le_mul_of_one_le_of_one_le) le_rfl fun _ _ => one_le_pow₀ (one_le_locHeight _))

private theorem norm_le_height (g : GA E a) :
    ‖toL (GeneralLinearGroup.map (pInf E) g).val‖ ≤ AutomorphicForm.height g := by
  have h0 : 0 ≤ AutomorphicForm.height g := (height_pos g).le
  refine (pi_norm_le_iff_of_nonneg h0).2 fun i => (pi_norm_le_iff_of_nonneg h0).2 fun j =>
    (pi_norm_le_iff_of_nonneg h0).2 fun w => ?_
  exact (norm_ringEquiv w ((g.val i j).1 w)).le.trans ((norm_apply_le_locHeight _ i j).trans (loc_le_height g w))

theorem height_pInf_le (g : GA E a) :
    GlobalTheory.CuspRep.height (GeneralLinearGroup.map (pInf E) g) ≤ 3 * AutomorphicForm.height g := by
  have h1 := norm_le_height g
  have h2 := norm_le_height g⁻¹
  rw [height_inv, map_inv] at h2
  have h3 := AutomorphicForm.one_le_height g
  linarith [(norm_le_ht (GeneralLinearGroup.map (pInf E) g)).2.2]

end UpperTheory.V.Cm
