import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EisAtMinusRho
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoreConcl
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.LanglandsSquareIntegrable
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ModerateEisensteinHolomorphicDerivative
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoordsSecondKindFormPreservingGroup
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MatrixOneParameterGroupEqExpOfContinuous
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProdOfFnEqSingle
open scoped TensorProduct NNReal Matrix ContDiff
open NumberField MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.EisRes
open GlobalTheory.Doubling (absE)

noncomputable section
namespace GlobalTheory.CircleSmooth

section Banach

open GlobalTheory.ClosedMatGroup

variable {𝔸 : Type} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸]

theorem exists_coords_deriv [FiniteDimensional ℝ 𝔸] {S : Set 𝔸} (hc : IsClosed S)
    (h1 : (1 : 𝔸) ∈ S) (hm : ∀ a ∈ S, ∀ b ∈ S, a * b ∈ S)
    (hi : ∀ Z : 𝔸, NormedSpace.exp Z ∈ S → NormedSpace.exp (-Z) ∈ S) :
    ∃ (d : ℕ) (Z : Fin d → 𝔸) (s : 𝔸 → Fin d → ℝ) (c : 𝔸 →L[ℝ] (Fin d → ℝ)), (∀ i, Z i ∈ lieSub S hc h1 hm) ∧
      s 1 = 0 ∧ HasFDerivAt s c 1 ∧
      ∀ᶠ X in 𝓝 (1 : 𝔸), X ∈ S → X = (List.ofFn fun i => NormedSpace.exp (s X i • Z i)).prod := by
  let _ : NormedAlgebra ℚ 𝔸 := NormedAlgebra.restrictScalars ℚ ℝ 𝔸
  obtain ⟨W, hW⟩ := (lieSub S hc h1 hm).exists_isCompl
  let L := lieSub S hc h1 hm
  let d := Module.finrank ℝ L
  let bL := Module.finBasis ℝ L
  let Z : Fin d → 𝔸 := fun i => (bL i : 𝔸)
  have hZ : ∀ i, ∀ t : ℝ, NormedSpace.exp (t • Z i) ∈ S := fun i t => (bL i).2 t
  let c : 𝔸 →L[ℝ] (Fin d → ℝ) :=
    LinearMap.toContinuousLinearMap (bL.equivFun.toLinearMap ∘ₗ L.projectionOnto W hW)
  let p : 𝔸 →L[ℝ] 𝔸 := LinearMap.toContinuousLinearMap (L.projection W hW)
  have hpc : ∀ z, ∑ i, c z i • Z i = p z := by
    intro z
    show ∑ i, (bL.equivFun (L.projectionOnto W hW z)) i • (bL i : 𝔸) = ((L.projectionOnto W hW z : L) : 𝔸)
    conv_rhs => rw [← bL.sum_equivFun (L.projectionOnto W hW z)]
    rw [Submodule.coe_sum]
    rfl
  have hqW : ∀ z, z - p z ∈ W := fun z => by
    have h := Submodule.projection_add_projection_eq_self hW z
    have e : z - p z = W.projection _ hW.symm z := by
      rw [sub_eq_iff_eq_add']; exact h.symm
    rw [e]; exact Submodule.projection_apply_mem hW.symm z
  let P : 𝔸 → 𝔸 := fun z => (List.ofFn fun i => NormedSpace.exp (c z i • Z i)).prod
  let Φ : 𝔸 → 𝔸 := fun z => P z * NormedSpace.exp (z - p z)
  have hexp : HasStrictFDerivAt NormedSpace.exp (1 : 𝔸 →L[ℝ] 𝔸) (0 : 𝔸) := hasStrictFDerivAt_exp_zero
  have hf : ∀ i, HasStrictFDerivAt (fun z => NormedSpace.exp (c z i • Z i))
      ((1 : 𝔸 →L[ℝ] 𝔸).comp (((ContinuousLinearMap.proj i).comp c).smulRight (Z i))) 0 := fun i =>
    HasStrictFDerivAt.comp (0 : 𝔸) (g := NormedSpace.exp) (by rw [map_zero, Pi.zero_apply, zero_smul]; exact hexp)
      (((ContinuousLinearMap.proj i).comp c).smulRight (Z i)).hasStrictFDerivAt
  have hP := hasStrictFDerivAt_ofFn_prod d (fun i z => NormedSpace.exp (c z i • Z i)) _ 0
    (fun i => by simp) hf
  have h2 : HasStrictFDerivAt (fun z => NormedSpace.exp (z - p z))
      ((1 : 𝔸 →L[ℝ] 𝔸).comp (ContinuousLinearMap.id ℝ 𝔸 - p)) 0 :=
    HasStrictFDerivAt.comp (0 : 𝔸) (f := fun z => z - p z) (by rw [map_zero, sub_zero]; exact hexp)
      (ContinuousLinearMap.id ℝ 𝔸 - p).hasStrictFDerivAt
  have hP0 : P 0 = 1 := by simp [P]
  have h4 : HasStrictFDerivAt Φ ((ContinuousLinearEquiv.refl ℝ 𝔸 : 𝔸 ≃L[ℝ] 𝔸) : 𝔸 →L[ℝ] 𝔸) 0 := by
    refine (hP.mul' h2).congr_fderiv ?_
    ext1 z
    have e1 : (List.ofFn fun i => NormedSpace.exp ((0 : Fin d → ℝ) i • Z i)).prod = 1 := by simp
    simp [e1, hpc]
  have hΦ0 : Φ 0 = 1 := by
    show P 0 * NormedSpace.exp (0 - p 0) = 1
    rw [hP0, map_zero, sub_zero, NormedSpace.exp_zero, one_mul]
  let Ψ := h4.localInverse Φ _ 0
  have hΨ : Tendsto Ψ (𝓝 1) (𝓝 0) := by
    have h := h4.localInverse_tendsto
    rw [hΦ0] at h
    exact h
  have hΨ1 : Ψ 1 = 0 := by
    have h := h4.localInverse_apply_image
    rw [hΦ0] at h
    exact h
  have hΨd : HasFDerivAt Ψ (ContinuousLinearMap.id ℝ 𝔸) 1 := by
    have h := h4.to_localInverse.hasFDerivAt
    rw [hΦ0] at h
    exact h
  have hR : ∀ᶠ X in 𝓝 (1 : 𝔸), Φ (Ψ X) = X := by
    have h := h4.eventually_right_inverse
    rw [hΦ0] at h
    exact h
  have hp0 : Tendsto p (𝓝 0) (𝓝 0) := by simpa using p.continuous.tendsto 0
  have hq0 : Tendsto (fun z => z - p z) (𝓝 0) (𝓝 (0 : 𝔸)) := by
    simpa using (tendsto_id (x := 𝓝 (0 : 𝔸))).sub hp0
  refine ⟨d, Z, fun X => c (Ψ X), c, fun i => (bL i).2, ?_, ?_, ?_⟩
  · simp only [hΨ1, map_zero]
  · exact c.hasFDerivAt.comp 1 hΨd
  · filter_upwards [hR, hΨ.eventually (hq0.eventually (eventually_eq_zero hc h1 hm hi hW.disjoint))]
      with X hX1 hX2 hXS
    obtain ⟨Q, hQ, hQe⟩ := exists_left_inv_ofFn_prod h1 hm d (fun i => c (Ψ X) i • Z i)
      (fun i => by rw [← neg_smul]; exact hZ i _)
    have hE : NormedSpace.exp (Ψ X - p (Ψ X)) = Q * X := by
      conv_rhs => rw [← hX1]
      show _ = Q * ((List.ofFn fun i => NormedSpace.exp (c (Ψ X) i • Z i)).prod * NormedSpace.exp (Ψ X - p (Ψ X)))
      rw [← mul_assoc, hQe, one_mul]
    have hw := hX2 (hqW _) (by rw [hE]; exact hm _ hQ _ hXS)
    calc X = Φ (Ψ X) := hX1.symm
      _ = _ := by
        show (List.ofFn fun i => NormedSpace.exp (c (Ψ X) i • Z i)).prod * NormedSpace.exp (Ψ X - p (Ψ X)) = _
        rw [hw, NormedSpace.exp_zero, mul_one]

omit [CompleteSpace 𝔸] in

theorem contDiff_ofFn_prod {G X : Type} [Group G] [NormedAddCommGroup X] [NormedSpace ℝ X] (φ : G →* 𝔸) :
    ∀ (k : ℕ) (x : Fin k → X → G), (∀ i, ContDiff ℝ ∞ (fun t => φ (x i t)) ∧ ContDiff ℝ ∞ fun t => φ (x i t)⁻¹) →
      ContDiff ℝ ∞ (fun t => φ (List.ofFn fun i => x i t).prod) ∧
        ContDiff ℝ ∞ fun t => φ (List.ofFn fun i => x i t).prod⁻¹ := by
  intro k
  induction k with
  | zero => intro x _; simp only [List.ofFn_zero, List.prod_nil]; exact ⟨contDiff_const, contDiff_const⟩
  | succ k ih =>
    intro x hx
    obtain ⟨h1, h2⟩ := ih (fun i => x i.succ) fun i => hx _
    simp only [List.ofFn_succ, List.prod_cons, mul_inv_rev, map_mul]
    exact ⟨(hx 0).1.mul h1, h2.mul (hx 0).2⟩

end Banach

theorem prod_ofFn_single {M : Type*} [Monoid M] : ∀ {d : ℕ} (g : Fin d → M) (j : Fin d),
    (∀ i, i ≠ j → g i = 1) → (List.ofFn g).prod = g j := by
  first
  | exact @_root_.GlobalTheory.ProductOfFnSingle.prod_ofFn_eq_single
  | exact _root_.GlobalTheory.ProductOfFnSingle.prod_ofFn_eq_single
  | (apply _root_.GlobalTheory.ProductOfFnSingle.prod_ofFn_eq_single <;> assumption)
  | (intros; apply _root_.GlobalTheory.ProductOfFnSingle.prod_ofFn_eq_single <;> assumption)
  | (intros; apply @_root_.GlobalTheory.ProductOfFnSingle.prod_ofFn_eq_single <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.ProductOfFnSingle.prod_ofFn_eq_single ..)

theorem clm_expand {k : ℕ} (L : (Fin k → ℝ) →L[ℝ] ℂ) (v : Fin k → ℝ) :
    L v = ∑ i, (v i : ℂ) * L (Pi.single i 1) := by
  conv_lhs => rw [← Finset.univ_sum_single v, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [show Pi.single i (v i) = v i • (Pi.single i 1 : Fin k → ℝ) by rw [← Pi.single_smul', smul_eq_mul, mul_one],
    map_smul, Complex.real_smul]

theorem hasDerivAt_dir {X Y : Type} [NormedAddCommGroup X] [NormedSpace ℝ X] [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    {Φ : X → Y} {L : X →L[ℝ] Y} {t : X} (h : HasFDerivAt Φ L t) (v : X) :
    HasDerivAt (fun u : ℝ => Φ (t + u • v)) (L v) 0 := by
  have hl : HasDerivAt (fun u : ℝ => t + u • v) v 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const v).const_add t
  exact HasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) h hl (by simp)

theorem contDiff_integral_of_closed {k : ℕ} {Λ ι : Type} [Fintype ι] (nxt : ι → Λ → Λ)
    (φ : Λ → (Fin k → ℝ) → ℝ → ℂ) (a : ι → (Fin k → ℝ) → ((Fin k → ℝ) →L[ℝ] ℂ)) (ha : ∀ j, ContDiff ℝ ∞ (a j))
    (hc : ∀ l x, Continuous (φ l x))
    (hb : ∀ l x₀, ∃ C, ∀ x ∈ Metric.closedBall x₀ 1, ∀ θ, ‖φ l x θ‖ ≤ C)
    (hd : ∀ l x θ, HasFDerivAt (fun x => φ l x θ) (∑ j, φ (nxt j l) x θ • a j x) x) (p q : ℝ) (l : Λ) :
    ContDiff ℝ ∞ fun x => ∫ θ in p..q, φ l x θ := by
  have key : ∀ l x₀, HasFDerivAt (fun x => ∫ θ in p..q, φ l x θ)
      (∑ j, (∫ θ in p..q, φ (nxt j l) x₀ θ) • a j x₀) x₀ := by
    intro l x₀
    choose C hC using fun j => hb (nxt j l) x₀
    choose A hA using fun j => (isCompact_closedBall x₀ 1).exists_bound_of_continuousOn (ha j).continuous.continuousOn
    have hc' : ∀ x, Continuous fun θ => ∑ j, φ (nxt j l) x θ • a j x := fun x =>
      continuous_finset_sum _ fun j _ => (hc _ x).smul continuous_const
    have h := intervalIntegral.hasFDerivAt_integral_of_dominated_of_fderiv_le (μ := volume) (a := p) (b := q)
      (F := φ l) (F' := fun x θ => ∑ j, φ (nxt j l) x θ • a j x) (x₀ := x₀) (bound := fun _ => ∑ j, C j * A j)
      (Metric.closedBall_mem_nhds x₀ one_pos) (Eventually.of_forall fun x => (hc l x).aestronglyMeasurable)
      ((hc l x₀).intervalIntegrable _ _) (hc' x₀).aestronglyMeasurable
      (ae_of_all _ fun θ _ x hx => (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => by
        rw [norm_smul]
        exact mul_le_mul (hC j x hx θ) (hA j x hx) (norm_nonneg _) ((norm_nonneg _).trans (hC j x hx θ))))
      intervalIntegrable_const (ae_of_all _ fun θ _ x _ => hd l x θ)
    rw [intervalIntegral.integral_finset_sum (f := fun j θ => φ (nxt j l) x₀ θ • a j x₀) fun j _ => ((hc _ x₀).smul continuous_const).intervalIntegrable _ _] at h
    simpa only [intervalIntegral.integral_smul_const] using h
  have ind : ∀ m : ℕ, ∀ l, ContDiff ℝ m fun x => ∫ θ in p..q, φ l x θ := by
    intro m
    induction m with
    | zero => intro l; exact contDiff_zero.2 (continuous_iff_continuousAt.2 fun x => (key l x).continuousAt)
    | succ m ih =>
      intro l
      rw [Nat.cast_succ, contDiff_succ_iff_fderiv]
      refine ⟨fun x => (key l x).differentiableAt, by simp, ?_⟩
      rw [show fderiv ℝ (fun x => ∫ θ in p..q, φ l x θ) = fun x₀ => ∑ j, (∫ θ in p..q, φ (nxt j l) x₀ θ) • a j x₀ from
        funext fun x => (key l x).fderiv]
      exact ContDiff.sum fun j _ => (ih _).smul ((ha j).of_le (by exact_mod_cast le_top))
  exact contDiff_infty.2 fun m => ind m l

attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

theorem coords_unitary {m : ℕ} (A : Matrix (Fin m) (Fin m) ℂ) : ∃ (d : ℕ)
    (Z : Fin d → Matrix (Fin m) (Fin m) ℂ) (s : Matrix (Fin m) (Fin m) ℂ → Fin d → ℝ)
    (c : Matrix (Fin m) (Fin m) ℂ →L[ℝ] (Fin d → ℝ)),
    (∀ i, (Z i)ᴴ * A + A * Z i = 0) ∧ s 1 = 0 ∧ HasFDerivAt s c 1 ∧
    ∀ᶠ X in 𝓝 (1 : Matrix (Fin m) (Fin m) ℂ), Xᴴ * A * X = A →
      X = (List.ofFn fun i => NormedSpace.exp (s X i • Z i)).prod := by
  let S := {X : Matrix (Fin m) (Fin m) ℂ | Xᴴ * A * X = A}
  have hc : IsClosed S :=
    isClosed_eq ((continuous_id.matrix_conjTranspose.matrix_mul continuous_const).matrix_mul
      continuous_id) continuous_const
  have h1 : (1 : Matrix (Fin m) (Fin m) ℂ) ∈ S := by simp [S]
  have hm : ∀ a ∈ S, ∀ b ∈ S, a * b ∈ S := by
    intro a ha b hb
    simp only [S, Set.mem_setOf_eq] at ha hb ⊢
    rw [Matrix.conjTranspose_mul]
    calc bᴴ * aᴴ * A * (a * b) = bᴴ * (aᴴ * A * a) * b := by simp only [Matrix.mul_assoc]
      _ = A := by rw [ha, hb]
  have hi : ∀ Z : Matrix (Fin m) (Fin m) ℂ, NormedSpace.exp Z ∈ S → NormedSpace.exp (-Z) ∈ S := by
    intro Z hZ
    simp only [S, Set.mem_setOf_eq] at hZ ⊢
    have hXY : NormedSpace.exp Z * NormedSpace.exp (-Z) = 1 := by
      rw [← Matrix.exp_add_of_commute _ _ (Commute.refl Z).neg_right, add_neg_cancel,
        NormedSpace.exp_zero]
    calc (NormedSpace.exp (-Z))ᴴ * A * NormedSpace.exp (-Z)
        = (NormedSpace.exp (-Z))ᴴ * ((NormedSpace.exp Z)ᴴ * A * NormedSpace.exp Z) * NormedSpace.exp (-Z) := by
          rw [hZ]
      _ = (NormedSpace.exp Z * NormedSpace.exp (-Z))ᴴ * A * (NormedSpace.exp Z * NormedSpace.exp (-Z)) := by
          rw [Matrix.conjTranspose_mul]; simp only [Matrix.mul_assoc]
      _ = A := by rw [hXY]; simp
  have _ : CompleteSpace (Matrix (Fin m) (Fin m) ℂ) := FiniteDimensional.complete ℝ _
  obtain ⟨d, Z, s, c, hZ, hs, hd, hev⟩ := exists_coords_deriv hc h1 hm hi
  exact ⟨d, Z, s, c, fun i => GlobalTheory.ClosedMatGroup.skew_of_exp_smul_mem A (Z i) (hZ i), hs, hd, hev⟩

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E}

open GlobalTheory.Orb (archMat)
open GlobalTheory.UAut (IsSm)

theorem realLine_zero (h : IsCMExt F E σ) {γ : ℝ → GAd σ J} (hγ : IsRealLine σ J γ) : γ 0 = 1 := by
  have := (GlobalTheory.CircleDop.realLine_hom h hγ).1 0 0
  rw [add_zero] at this
  exact mul_eq_left.1 this.symm

theorem exists_lines_curve (h : IsCMExt F E σ) (hJ : IsHermND σ J) (w : InfinitePlace F) (τ : EmbOver E w) :
    ∃ (d : ℕ) (η : Fin d → ℝ → GAd σ J) (c : Matrix (Fin n) (Fin n) ℂ →L[ℝ] (Fin d → ℝ)),
      (∀ i, IsRealLine σ J (η i)) ∧ ∀ f, IsSm σ J f → ∀ (g : GAd σ J) (y : ℝ → GArch σ J w)
        (M : Matrix (Fin n) (Fin n) ℂ), y 0 = 1 → HasDerivAt (fun u => archMat σ J τ (y u)) M 0 →
        HasDerivAt (fun u => f (g * embArch σ J w (y u))) (∑ i, (c M i : ℂ) * lineDer (η i) f g) 0 := by
  set A : Matrix (Fin n) (Fin n) ℂ := J.map τ.1 with hA
  obtain ⟨d, Z, s, c, hZ, hs, hsd, hev⟩ := coords_unitary A
  have hd : IsUnit A.det := by
    rw [hA, ← RingHom.mapMatrix_apply, ← RingHom.map_det]
    exact (IsUnit.mk0 _ hJ.2).map _
  have hx : ∀ (i : Fin d) (t : ℝ), ∃ y : GArch σ J w, archMat σ J τ y = NormedSpace.exp (t • Z i) := by
    intro i t
    obtain ⟨u, hu⟩ := Matrix.isUnit_exp (t • Z i)
    have h1 := GlobalTheory.SmoothForms.exp_mem_UH (X := t • Z i) hd (by
      rw [Matrix.conjTranspose_smul, star_trivial, Matrix.smul_mul, Matrix.mul_smul, ← smul_add, hZ i, smul_zero])
    refine ⟨(archEquiv J h τ).symm ⟨u, show _ * _ * _ = _ from hu ▸ h1⟩, ?_⟩
    rw [GlobalTheory.Orb.archMat_eq_archEquiv J h, MulEquiv.apply_symm_apply]
    exact hu
  choose x hx using hx
  have hS : ∀ g : GArch σ J w, (archMat σ J τ g)ᴴ * A * archMat σ J τ g = A := fun g => (archEquiv J h τ g).2
  have hinj : Function.Injective (archMat σ J τ) := fun a b e =>
    (GlobalTheory.Orb.isEmbedding_archMat J h τ).injective (by
      show (fun i j => archMat σ J τ a i j) = fun i j => archMat σ J τ b i j
      rw [e])
  let η : Fin d → ℝ → GAd σ J := fun i t => embArch σ J w (x i t)
  have hη : ∀ i, IsRealLine σ J (η i) := fun i => ⟨w, τ, Z i, hZ i, fun t => ⟨x i t, rfl, hx i t⟩⟩
  refine ⟨d, η, c, hη, fun f hf g y M hy0 hy => ?_⟩
  have hy1 : archMat σ J τ (y 0) = 1 := by rw [hy0, map_one]
  let Φ : (Fin d → ℝ) → ℂ := fun t => f (g * (List.ofFn fun i => η i (t i)).prod)
  have hΦ : HasFDerivAt Φ (fderiv ℝ Φ 0) 0 := ((hf d η hη g).differentiable (by simp) 0).hasFDerivAt
  have h1 : HasDerivAt (fun u => s (archMat σ J τ (y u))) (c M) 0 :=
    HasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) hsd hy hy1.symm
  have h2 : HasDerivAt (fun u => Φ (s (archMat σ J τ (y u)))) (fderiv ℝ Φ 0 (c M)) 0 :=
    HasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) hΦ h1 (by rw [hy1, hs])
  have h3 : ∀ i, fderiv ℝ Φ 0 (Pi.single i 1) = lineDer (η i) f g := fun i => by
    rw [← (hasDerivAt_dir hΦ (Pi.single i 1)).deriv]
    unfold lineDer
    congr 1
    funext u
    simp only [Φ]
    rw [prod_ofFn_single _ i fun j hj => by simp [Pi.single_eq_of_ne hj, realLine_zero h (hη j)]]
    simp
  rw [clm_expand] at h2
  simp only [h3] at h2
  refine h2.congr_of_eventuallyEq ?_
  have ht : Tendsto (fun u => archMat σ J τ (y u)) (𝓝 0) (𝓝 1) := hy1 ▸ hy.continuousAt.tendsto
  filter_upwards [ht.eventually hev] with u hu
  have e1 : (List.ofFn fun i => η i (s (archMat σ J τ (y u)) i)).prod =
      embArch σ J w (List.ofFn fun i => x i (s (archMat σ J τ (y u)) i)).prod := by
    rw [map_list_prod, List.map_ofFn]; rfl
  simp only [Φ]
  rw [e1]
  congr 3
  apply hinj
  rw [map_list_prod, List.map_ofFn]
  refine (hu (hS _)).trans ?_
  congr 1
  exact List.ofFn_inj.2 (funext fun i => (hx i _).symm)

theorem contDiff_archMat_line (h : IsCMExt F E σ) {γ : ℝ → GAd σ J} (hγ : IsRealLine σ J γ) {w : InfinitePlace F}
    (τ : EmbOver E w) : ContDiff ℝ ∞ fun t => archMat σ J τ (projArch σ J w (γ t)) := by
  obtain ⟨hadd, hc⟩ := GlobalTheory.CircleDop.realLine_hom h hγ
  obtain ⟨Z, hZ⟩ := GlobalTheory.OneParamMatrix.eq_exp_of_continuous_oneParameter
    (fun t => archMat σ J τ (projArch σ J w (γ t)))
    ((GlobalTheory.Orb.continuous_archMat σ J τ).comp ((continuous_projArch σ J w).comp hc))
    (by simp only [realLine_zero h hγ, map_one]) (fun s t => by simp only [hadd, map_mul])
  simp only [hZ]
  have _ : CompleteSpace (Matrix (Fin n) (Fin n) ℂ) := FiniteDimensional.complete ℝ _
  have he : ContDiff ℝ ∞ (NormedSpace.exp : Matrix (Fin n) (Fin n) ℂ → _) :=
    contDiff_iff_contDiffAt.2 fun x => (NormedSpace.exp_analytic (𝕂 := ℝ) x).contDiffAt
  exact he.comp (contDiff_id.smul contDiff_const)

theorem exists_lines_partial (h : IsCMExt F E σ) (hJ : IsHermND σ J) {k : ℕ} {γ : Fin k → ℝ → GAd σ J}
    (hγ : ∀ i, IsRealLine σ J (γ i)) (i : Fin k) :
    ∃ (d : ℕ) (η : Fin d → ℝ → GAd σ J) (b : Fin d → (Fin k → ℝ) → ℝ),
      (∀ a, IsRealLine σ J (η a)) ∧ (∀ a, ContDiff ℝ ∞ (b a)) ∧ ∀ f, IsSm σ J f → ∀ (g : GAd σ J) (t : Fin k → ℝ),
        HasDerivAt (fun u : ℝ => f (g * (List.ofFn fun j => γ j ((t + u • (Pi.single i 1 : Fin k → ℝ)) j)).prod))
          (∑ a, (b a t : ℂ) * lineDer (η a) f (g * (List.ofFn fun j => γ j (t j)).prod)) 0 := by
  obtain ⟨w, τ, Z, -, hw⟩ := hγ i
  obtain ⟨d, η, c, hη, hc⟩ := exists_lines_curve h hJ w τ
  let P : (Fin k → ℝ) → GAd σ J := fun t => (List.ofFn fun j => γ j (t j)).prod
  let φ : GAd σ J →* Matrix (Fin n) (Fin n) ℂ := (archMat σ J τ).comp (projArch σ J w)
  obtain ⟨hm, hm'⟩ := contDiff_ofFn_prod φ k (fun j (t : Fin k → ℝ) => γ j (t j)) fun j =>
    ⟨(contDiff_archMat_line h (hγ j) τ).comp (contDiff_apply ℝ ℝ j), by
      have e : ∀ u, (γ j u)⁻¹ = γ j (-u) := fun u => inv_eq_of_mul_eq_one_right (by
        rw [← (GlobalTheory.CircleDop.realLine_hom h (hγ j)).1, add_neg_cancel, realLine_zero h (hγ j)])
      simp only [e]
      exact (contDiff_archMat_line h (hγ j) τ).comp (contDiff_apply ℝ ℝ j).neg⟩
  let e : Fin k → ℝ := Pi.single i 1
  let M : (Fin k → ℝ) → Matrix (Fin n) (Fin n) ℂ := fun t => φ (P t)⁻¹ * fderiv ℝ (fun t => φ (P t)) t e
  have hM : ContDiff ℝ ∞ M := hm'.mul ((hm.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const)
  refine ⟨d, η, fun a t => c (M t) a, hη, fun a => (contDiff_apply ℝ ℝ a).comp (c.contDiff.comp hM), fun f hf g t => ?_⟩
  have key := hc f hf (g * P t) (fun u => projArch σ J w ((P t)⁻¹ * P (t + u • e))) (M t) (by simp) (by
    have := (hasDerivAt_dir ((hm.differentiable (by simp)) t).hasFDerivAt e).const_mul (φ (P t)⁻¹)
    simp only [← map_mul] at this
    exact this)
  convert key using 3 with u
  have aux : ∀ {H : Type} [Group H] (ψ : GAd σ J →* H), (∀ y, ψ (embArch σ J w y) = 1) →
      ψ ((P t)⁻¹ * P (t + u • e)) = 1 := fun ψ hψ => by
    rw [map_mul, map_inv, inv_mul_eq_one]
    simp only [P, map_list_prod, List.map_ofFn]
    congr 2
    funext j
    by_cases hj : j = i
    · subst hj
      obtain ⟨y1, e1, -⟩ := hw (t j)
      obtain ⟨y2, e2, -⟩ := hw ((t + u • e) j)
      simp only [Function.comp_apply, e1, e2, hψ]
    · simp [e, Pi.single_eq_of_ne hj]
  have e2 : embArch σ J w (projArch σ J w ((P t)⁻¹ * P (t + u • e))) = (P t)⁻¹ * P (t + u • e) := by
    refine GAd_ext σ J (fun v => ?_) fun v => ?_
    · by_cases hv : v = w
      · subst hv; rw [projArch_embArch_self]
      · rw [projArch_embArch_ne σ J hv, aux _ (projArch_embArch_ne σ J hv)]
    · rw [aux (proj σ J v) (by simp)]; simp
  rw [e2, mul_assoc, mul_inv_cancel_left]

theorem exists_lines_fderiv (h : IsCMExt F E σ) (hJ : IsHermND σ J) {k : ℕ} {γ : Fin k → ℝ → GAd σ J}
    (hγ : ∀ i, IsRealLine σ J (γ i)) :
    ∃ (ι : Type) (_ : Fintype ι) (δ : ι → ℝ → GAd σ J) (a : ι → (Fin k → ℝ) → ((Fin k → ℝ) →L[ℝ] ℂ)),
      (∀ j, IsRealLine σ J (δ j)) ∧ (∀ j, ContDiff ℝ ∞ (a j)) ∧ ∀ f, IsSm σ J f → ∀ (g : GAd σ J) (t : Fin k → ℝ),
        HasFDerivAt (fun t : Fin k → ℝ => f (g * (List.ofFn fun i => γ i (t i)).prod))
          (∑ j, lineDer (δ j) f (g * (List.ofFn fun i => γ i (t i)).prod) • a j t) t := by
  choose d η b hη hb hd using exists_lines_partial h hJ hγ
  refine ⟨Σ i, Fin (d i), inferInstance, fun j => η j.1 j.2,
    fun j t => b j.1 j.2 t • (Complex.ofRealCLM.comp (ContinuousLinearMap.proj j.1)), fun j => hη _ _,
    fun j => (hb _ _).smul contDiff_const, fun f hf g t => ?_⟩
  have hD := ((hf k γ hγ g).differentiable (by simp) t).hasFDerivAt
  refine hD.congr_fderiv (Eq.symm (ContinuousLinearMap.ext fun v => ?_))
  rw [clm_expand (fderiv ℝ _ t), ContinuousLinearMap.sum_apply, Fintype.sum_sigma]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [(hasDerivAt_dir hD (Pi.single i 1)).unique (hd i f hf g t), Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  simp
  ring

theorem isSm_circleIntegral : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ →
    ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ (H₀ : ℂ → GAd σ J → ℂ) (s₀ : ℂ) (r : ℝ) (V : Set ℂ),
    IsOpen V → 0 < r → Metric.closedBall s₀ r ⊆ V → (∀ s ∈ V, IsSmoothModerate σ J (H₀ s)) →
    (∀ μ, GlobalTheory.EisLine.IsModerateForm σ J μ → DifferentiableOn ℂ (fun s => μ (H₀ s)) V) → ∀ j : ℤ,
    GlobalTheory.UAut.IsSm σ J fun g => circleIntegral (fun z => (z - s₀) ^ j * H₀ z g) s₀ r := by
  intro F E _ _ _ _ _ σ h n J hJ H₀ s₀ r V hV hr hsub hH hμ j k γ hγ g
  obtain ⟨ι, _, δ, a, hδ, ha, hd⟩ := exists_lines_fderiv h hJ hγ
  have hS : Metric.sphere s₀ r ⊆ V := Metric.sphere_subset_closedBall.trans hsub
  have hmem : ∀ θ, circleMap s₀ r θ ∈ Metric.sphere s₀ r := fun θ => circleMap_mem_sphere s₀ hr.le θ
  let P : (Fin k → ℝ) → GAd σ J := fun t => (List.ofFn fun i => γ i (t i)).prod
  have hP : Continuous P := by
    simp only [P, List.ofFn_eq_map]
    exact continuous_list_prod _ fun i _ => (GlobalTheory.CircleDop.realLine_hom h (hγ i)).2.comp (continuous_apply i)
  let c : ℝ → ℂ := fun θ => deriv (circleMap s₀ r) θ * (circleMap s₀ r θ - s₀) ^ j
  have hc : Continuous c := by
    have h1 : Continuous fun θ => deriv (circleMap s₀ r) θ := by
      simp only [deriv_circleMap]
      exact (continuous_circleMap 0 r).mul continuous_const
    exact h1.mul (((continuous_circleMap s₀ r).sub continuous_const).zpow₀ j fun θ =>
      Or.inl (sub_ne_zero.2 (Metric.ne_of_mem_sphere (hmem θ) hr.ne')))
  have hcb : ∀ θ, ‖c θ‖ = |r| * |r| ^ j := fun θ => by
    simp only [c, deriv_circleMap, norm_mul, norm_zpow, circleMap_sub_center, norm_circleMap_zero, Complex.norm_I,
      mul_one]
  have W := fun l : {l : List (ℝ → GAd σ J) // ∀ γ ∈ l, IsRealLine σ J γ} =>
    GlobalTheory.WeakHolFamily.word_holomorphic_and_uniform F E σ n J H₀ V (Metric.sphere s₀ r) hV
      (isCompact_sphere s₀ r) hS hH hμ l.1 l.2
  have key := contDiff_integral_of_closed (Λ := {l : List (ℝ → GAd σ J) // ∀ γ ∈ l, IsRealLine σ J γ})
    (fun i l => ⟨δ i :: l.1, List.forall_mem_cons.2 ⟨hδ i, l.2⟩⟩)
    (fun l t θ => c θ * l.1.foldr lineDer (H₀ (circleMap s₀ r θ)) (g * P t)) a ha
    (fun l t => hc.mul ((((W l).1 (g * P t)).continuousOn.mono hS).comp_continuous (continuous_circleMap s₀ r) hmem))
    (fun l t₀ => by
      obtain ⟨N, C, hC⟩ := (W l).2
      have hh : Continuous fun t => C * (height σ J (g * P t) : ℝ) ^ N :=
        continuous_const.mul ((NNReal.continuous_coe.comp ((continuous_height_GAd σ J).comp
          (continuous_const.mul hP))).pow N)
      obtain ⟨B, hB⟩ := (isCompact_closedBall t₀ 1).exists_bound_of_continuousOn hh.continuousOn
      refine ⟨|r| * |r| ^ j * B, fun t ht θ => ?_⟩
      rw [norm_mul, hcb]
      exact mul_le_mul_of_nonneg_left ((hC _ (hmem θ) _).trans ((le_abs_self _).trans (hB t ht))) (by positivity))
    (fun l t θ => by
      have h1 := (hd _ (GlobalTheory.WeakHolFamily.smoothLines_foldr (hH _ (hS (hmem θ))).smooth l.1 l.2) g t).const_mul (c θ)
      rw [Finset.smul_sum] at h1
      simp only [smul_smul] at h1
      exact h1)
    0 (2 * Real.pi) ⟨[], by simp⟩
  simp only [c, mul_assoc] at key
  exact key

end GlobalTheory.CircleSmooth
