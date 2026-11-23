import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.SlopeBoundSt
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ArchBetween
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.BdryChart
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.ClopenCondOnto
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
import Development.AbelianVarietyTheory.PublishedTheorems.SemiabelianTori.GeometricallyConnectedSplitTorusAff
import GroundTheory.HeightsAndTheta.Heights.Regularisation.Assembly
import GroundTheory.HeightsAndTheta.Heights.Regularisation.PRiemannExtensionSlices
import GroundTheory.HeightsAndTheta.Heights.Regularisation.PPuncturedExpOrder
import GroundTheory.HeightsAndTheta.Heights.Regularisation.PLogCoverDescent
import Development.AutomorphicSpectrum.Proofs.MetricProofs.ImLowerOnKernel
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.ExistsAdaptedUnimodular
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.SymplecticPolydiscPeriodBasisStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.SiegelLimitImagBoundStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.RiemannFormHermitianLatticeStatement

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

namespace GlobalTheory.CompanionTheory.Ar.RiemannLimit

open GroundTheory.Heights₂.Heights.Regular

def cst {g : ℕ} (u : Fin g → ℤ) : Fin g → ℂ := fun k => (u k : ℂ)

theorem cst_add {g : ℕ} (u v : Fin g → ℤ) : cst (u + v) = cst u + cst v := by
  funext k; simp [cst]

theorem cst_zero {g : ℕ} : cst (0 : Fin g → ℤ) = 0 := by
  funext k; simp [cst]

theorem cst_mulVec {g : ℕ} (B : Matrix (Fin g) (Fin g) ℤ) (v : Fin g → ℤ) :
    B.map (fun x : ℤ => (x : ℂ)) *ᵥ cst v = cst (B *ᵥ v) := by
  funext k; simp [cst, mulVec, dotProduct]

section Coords

variable {g : ℕ} {Λ : Type} [AddCommGroup Λ] (bas : Module.Basis (Fin g ⊕ Fin g) ℤ Λ)

noncomputable def uCo : Λ →ₗ[ℤ] (Fin g → ℤ) := LinearMap.pi fun i => bas.coord (.inl i)

noncomputable def vCo : Λ →ₗ[ℤ] (Fin g → ℤ) := LinearMap.pi fun i => bas.coord (.inr i)

noncomputable def mk (u v : Fin g → ℤ) : Λ :=
  ∑ i, u i • bas (.inl i) + ∑ j, v j • bas (.inr j)

theorem sum_coords (x : Λ) : mk bas (uCo bas x) (vCo bas x) = x := by
  conv_rhs => rw [← bas.sum_repr x]
  rw [Fintype.sum_sum_type]
  simp [mk, uCo, vCo]

theorem uCo_mk (u v : Fin g → ℤ) : uCo bas (mk bas u v) = u := by
  funext i
  simp [uCo, mk, Module.Basis.coord_apply, Finsupp.single_apply]

theorem vCo_mk (u v : Fin g → ℤ) : vCo bas (mk bas u v) = v := by
  funext i
  simp [vCo, mk, Module.Basis.coord_apply, Finsupp.single_apply]

theorem eq_of_coords {x y : Λ} (hu : uCo bas x = uCo bas y) (hv : vCo bas x = vCo bas y) : x = y := by
  rw [← sum_coords bas x, ← sum_coords bas y, hu, hv]

theorem per_coords (P : Λ →+ (Fin g → ℂ)) (τ A : Matrix (Fin g) (Fin g) ℂ) (hτ : τᵀ = τ)
    (ha : ∀ i k, P (bas (.inl i)) k = A i k)
    (hb : ∀ j, P (bas (.inr j)) = ∑ k, τ j k • P (bas (.inl k))) (x : Λ) :
    P x = Aᵀ *ᵥ (cst (uCo bas x) + τ *ᵥ cst (vCo bas x)) := by
  have hx : P x = ∑ i, uCo bas x i • P (bas (.inl i)) + ∑ j, vCo bas x j • P (bas (.inr j)) := by
    conv_lhs => rw [← sum_coords bas x]
    simp [mk, map_sum, map_zsmul]
  rw [hx]
  funext k
  have hsym : ∀ i j, τ i j = τ j i := fun i j => by
    have := congrFun (congrFun hτ j) i
    simpa using this
  simp only [hb, Pi.add_apply, Finset.sum_apply, Pi.smul_apply, mulVec, dotProduct, transpose_apply, cst]
  simp only [ha, zsmul_eq_mul, smul_eq_mul]
  simp only [mul_add, Finset.sum_add_distrib, Finset.mul_sum]
  congr 1
  · exact Finset.sum_congr rfl fun i _ => mul_comm _ _
  · rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [hsym i j]; ring

theorem form_coords (E : LinearMap.BilinForm ℤ Λ)
    (hE : ∀ i j, E (bas (.inl i)) (bas (.inl j)) = 0 ∧ E (bas (.inr i)) (bas (.inr j)) = 0 ∧
      E (bas (.inl i)) (bas (.inr j)) = if i = j then -1 else 0) (halt : ∀ x, E x x = 0) (x y : Λ) :
    E x y = vCo bas x ⬝ᵥ uCo bas y - uCo bas x ⬝ᵥ vCo bas y := by
  have hskew : ∀ x y, E x y = - E y x := by
    intro x y
    have h := halt (x + y)
    simp only [map_add, LinearMap.add_apply, halt] at h
    linarith
  have hba : ∀ i j, E (bas (.inr i)) (bas (.inl j)) = if i = j then 1 else 0 := by
    intro i j
    rw [hskew, (hE j i).2.2]
    by_cases h : i = j
    · simp [h]
    · simp [h, Ne.symm h]
  conv_lhs => rw [← sum_coords bas x, ← sum_coords bas y]
  simp only [mk, map_add, map_sum, map_zsmul, LinearMap.add_apply, LinearMap.sum_apply,
    LinearMap.smul_apply, smul_eq_mul, (hE _ _).1, (hE _ _).2.1, (hE _ _).2.2, hba,
    mul_zero, Finset.sum_const_zero, add_zero, zero_add, mul_ite, mul_one, mul_neg,
    Finset.sum_ite_eq, Finset.mem_univ, if_true, Finset.sum_neg_distrib, dotProduct]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true, mul_one, mul_neg, Finset.sum_neg_distrib]
  rw [sub_eq_add_neg]
  congr 1
  · exact Finset.sum_congr rfl fun _ _ => by ring
  · congr 1
    exact Finset.sum_congr rfl fun _ _ => by ring

end Coords

section
variable {g : ℕ}

theorem tendsto_inv_transpose {X : Type} {f : Filter X} {M : X → Matrix (Fin g) (Fin g) ℂ}
    {M₀ : Matrix (Fin g) (Fin g) ℂ} (h : Tendsto M f (𝓝 M₀)) (h0 : M₀.det ≠ 0) :
    Tendsto (fun x => ((M x)ᵀ)⁻¹) f (𝓝 (M₀ᵀ)⁻¹) := by
  have hd : Tendsto (fun x => ((M x)ᵀ).det) f (𝓝 (M₀ᵀ).det) := by
    have hc : Continuous (fun N : Matrix (Fin g) (Fin g) ℂ => Nᵀ.det) :=
      (continuous_id.matrix_transpose).matrix_det
    exact (hc.tendsto _).comp h
  have ha : Tendsto (fun x => ((M x)ᵀ).adjugate) f (𝓝 (M₀ᵀ).adjugate) := by
    have hc : Continuous (fun N : Matrix (Fin g) (Fin g) ℂ => Nᵀ.adjugate) :=
      (continuous_id.matrix_transpose).matrix_adjugate
    exact (hc.tendsto _).comp h
  have h0' : (M₀ᵀ).det ≠ 0 := by rwa [det_transpose]
  have := (hd.inv₀ h0').smul ha
  simpa [Matrix.inv_def, Ring.inverse_eq_inv'] using this

end

theorem functional_rep {g : ℕ} (φ : (Fin g → ℤ) →+ ℤ) : ∃ p : Fin g → ℤ, ∀ u, φ u = u ⬝ᵥ p := by
  refine ⟨fun i => φ (Pi.single i 1), fun u => ?_⟩
  conv_lhs => rw [← Finset.univ_sum_single u]
  rw [map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  have : (Pi.single i (u i) : Fin g → ℤ) = u i • Pi.single i 1 := by
    funext k
    by_cases h : k = i
    · subst h; simp
    · simp [h]
  rw [this, map_zsmul, smul_eq_mul]

theorem unim : ∀ (g : ℕ) (Bs : Matrix (Fin g) (Fin g) ℤ), Bsᵀ = Bs → ∀ (φ₁ : (Fin g → ℤ) →+ ℤ) (φ₂ : LinearMap.ker Bs.mulVecLin →+ ℤ), (∀ u : Fin g → ℤ, (∀ v : Fin g → ℤ, Bs *ᵥ v = 0 → u ⬝ᵥ v = 0) → φ₁ u = 0) → ∃ p q : Fin g → ℤ, Bs *ᵥ p = 0 ∧ (∀ u, φ₁ u = u ⬝ᵥ p) ∧ ∀ k : LinearMap.ker Bs.mulVecLin, φ₂ k = q ⬝ᵥ (k : Fin g → ℤ) := by
  intro g Bs hT φ₁ φ₂ h
  obtain ⟨p, hp⟩ := functional_rep φ₁
  have hM := GlobalTheory.CompanionTheory.ToricBasis.exists_isCompl_ker Bs.mulVecLin
  obtain ⟨M, hM⟩ := hM
  let π := Submodule.linearProjOfIsCompl _ _ hM.symm
  obtain ⟨q, hq⟩ := functional_rep (φ₂.comp π.toAddMonoidHom)
  refine ⟨p, q, ?_, hp, fun k => ?_⟩
  · funext i
    have h1 : φ₁ (Bs i) = 0 := h _ fun v hv => congrFun hv i
    rw [hp] at h1
    exact h1
  · have h1 := hq (k : Fin g → ℤ)
    have h2 : π (k : Fin g → ℤ) = k := Submodule.linearProjOfIsCompl_apply_left hM.symm k
    simp only [AddMonoidHom.comp_apply, LinearMap.toAddMonoidHom_coe, h2] at h1
    rw [h1, dotProduct_comm]

theorem inv : ∀ (n g : ℕ) (A : (Fin n → ℂ) → Matrix (Fin g) (Fin g) ℂ), ContinuousAt A 0 → (A 0).det ≠ 0 → ∃ ρ K : ℝ, 0 < ρ ∧ 0 ≤ K ∧ ∀ z ∈ Metric.ball (0 : Fin n → ℂ) ρ, (A z).det ≠ 0 ∧ ∀ y : Fin g → ℂ, ∑ i, ‖y i‖ ^ 2 ≤ K * ∑ i, ‖((A z)ᵀ *ᵥ y) i‖ ^ 2 := by
  intro n g A hA h0
  set F0 := ((A 0)ᵀ)⁻¹ with hF0
  have hF : Tendsto (fun z => ((A z)ᵀ)⁻¹) (𝓝 0) (𝓝 F0) := tendsto_inv_transpose hA.tendsto h0
  set M : ℝ := ∑ i, ∑ j, ‖F0 i j‖ + 1 with hMdef
  have hM0 : 0 ≤ M := by positivity
  have hent : ∀ i j, ∀ᶠ z in 𝓝 (0 : Fin n → ℂ), ‖(((A z)ᵀ)⁻¹ : Matrix (Fin g) (Fin g) ℂ) i j‖ ≤ M := by
    intro i j
    have hc : Continuous (fun N : Matrix (Fin g) (Fin g) ℂ => ‖N i j‖) :=
      (continuous_id.matrix_elem i j).norm
    have h1 : ‖F0 i j‖ < M := by
      have h2 : ‖F0 i j‖ ≤ ∑ j, ‖F0 i j‖ :=
        Finset.single_le_sum (f := fun j => ‖F0 i j‖) (fun _ _ => norm_nonneg _) (Finset.mem_univ j)
      have h3 : ∑ j, ‖F0 i j‖ ≤ ∑ i, ∑ j, ‖F0 i j‖ :=
        Finset.single_le_sum (f := fun i => ∑ j, ‖F0 i j‖)
          (fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _) (Finset.mem_univ i)
      simp only [hMdef]; linarith
    exact (((hc.tendsto F0).comp hF).eventually (gt_mem_nhds h1)).mono fun _ h => h.le
  have hdet : ∀ᶠ z in 𝓝 (0 : Fin n → ℂ), (A z).det ≠ 0 := by
    have hc : Continuous (fun N : Matrix (Fin g) (Fin g) ℂ => N.det) := continuous_id.matrix_det
    exact ((hc.tendsto _).comp hA.tendsto).eventually (isOpen_ne.mem_nhds h0)
  have hall := hdet.and (eventually_all.2 fun i => eventually_all.2 fun j => hent i j)
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff_ball.1 hall
  refine ⟨ε, (g : ℝ) * ((g : ℝ) * M ^ 2), hε, by positivity, fun z hz => ⟨(hball z hz).1, fun y => ?_⟩⟩
  obtain ⟨hd, hb⟩ := hball z hz
  set v := (A z)ᵀ *ᵥ y with hv
  have hy : y = ((A z)ᵀ)⁻¹ *ᵥ v := by
    rw [hv, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ (Ne.isUnit (by rwa [det_transpose])),
      Matrix.one_mulVec]
  have hi : ∀ i, ‖y i‖ ^ 2 ≤ (g : ℝ) * M ^ 2 * ∑ j, ‖v j‖ ^ 2 := by
    intro i
    have h1 : ‖y i‖ ≤ ∑ j, M * ‖v j‖ := by
      rw [hy]
      simp only [mulVec, dotProduct]
      refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => ?_)
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_right (hb i j) (norm_nonneg _)
    have h2 : (∑ j, M * ‖v j‖) ^ 2 ≤ (Finset.univ : Finset (Fin g)).card * ∑ j, (M * ‖v j‖) ^ 2 :=
      sq_sum_le_card_mul_sum_sq
    have h3 : ‖y i‖ ^ 2 ≤ (∑ j, M * ‖v j‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h1 2
    refine h3.trans (h2.trans (le_of_eq ?_))
    simp only [Finset.card_univ, Fintype.card_fin, mul_pow, ← Finset.mul_sum]
    ring
  calc ∑ i, ‖y i‖ ^ 2 ≤ ∑ _i : Fin g, (g : ℝ) * M ^ 2 * ∑ j, ‖v j‖ ^ 2 :=
        Finset.sum_le_sum fun i _ => hi i
    _ = (g : ℝ) * ((g : ℝ) * M ^ 2) * ∑ j, ‖v j‖ ^ 2 := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        ring

theorem at_point {n a g : ℕ} {Λ : Type} [AddCommGroup Λ] (L : Flat.LogPeriods n a g Λ)
    (bas : Module.Basis (Fin g ⊕ Fin g) ℤ Λ) (A T0 : (Fin n → ℂ) → Matrix (Fin g) (Fin g) ℂ)
    (B : Fin a → Matrix (Fin g) (Fin g) ℤ) (c K ρ : ℝ) (hc : 0 < c) (hρ0 : 0 < ρ) (hρ : ρ ≤ 1)
    (hE : ∀ i j, L.E (bas (.inl i)) (bas (.inl j)) = 0 ∧ L.E (bas (.inr i)) (bas (.inr j)) = 0 ∧
      L.E (bas (.inl i)) (bas (.inr j)) = if i = j then -1 else 0)
    (hAc : ContinuousOn A (Metric.ball 0 1)) (hTc : ContinuousOn T0 (Metric.ball 0 1))
    (hK : 0 ≤ K)
    (hAinv : ∀ z ∈ Metric.ball (0 : Fin n → ℂ) ρ, (A z).det ≠ 0 ∧
      ∀ y : Fin g → ℂ, ∑ i, ‖y i‖ ^ 2 ≤ K * ∑ i, ‖((A z)ᵀ *ᵥ y) i‖ ^ 2)
    (hB : ∀ j, ((B j).map (fun x : ℤ => (x : ℝ))).PosSemidef)
    (hY : ∀ z ∈ Metric.ball (0 : Fin n → ℂ) ρ, ∀ l : Fin a → ℂ,
      (∀ j, Complex.exp (l j) = z (Fin.castLE L.a_le j)) →
      ((T0 z + ∑ j, (l j / (2 * Real.pi * Complex.I)) • (B j).map (fun x : ℤ => (x : ℂ))).map
        Complex.im - c • (1 : Matrix (Fin g) (Fin g) ℝ)).PosSemidef)
    (hsym : ∀ w ∈ logCover L.a_le, (T0 (expCover a w) + ∑ j, (w (Fin.castLE L.a_le j) /
      (2 * Real.pi * Complex.I)) • (B j).map (fun x : ℤ => (x : ℂ)))ᵀ =
      T0 (expCover a w) + ∑ j, (w (Fin.castLE L.a_le j) /
      (2 * Real.pi * Complex.I)) • (B j).map (fun x : ℤ => (x : ℂ)))
    (hP : ∀ w ∈ logCover L.a_le, ∀ x, L.P w x = (A (expCover a w))ᵀ *ᵥ (cst (uCo bas x) +
      (T0 (expCover a w) + ∑ j, (w (Fin.castLE L.a_le j) / (2 * Real.pi * Complex.I)) •
        (B j).map (fun x : ℤ => (x : ℂ))) *ᵥ cst (vCo bas x)))
    (z : Fin n → ℂ) (hz : z ∈ Metric.ball (0 : Fin n → ℂ) ρ) :
    ∃ (ws : ℕ → Fin n → ℂ) (W : Submodule ℤ Λ) (per : W →+ (Fin g → ℂ)), (∀ m, ws m ∈ logCover L.a_le) ∧ Tendsto (fun m => expCover a (ws m)) atTop (𝓝 z) ∧ (∀ x : W, Tendsto (fun m => L.P (ws m) x) atTop (𝓝 (per x))) ∧ (∀ (x : ℕ → Λ) (p : Fin g → ℂ), Tendsto (fun m => L.P (ws m) (x m)) atTop (𝓝 p) → ∃ x₀ : W, p = per x₀ ∧ ∀ᶠ m in atTop, x m = x₀) ∧ (∀ φ : W →+ ℤ, (∀ x : W, (∀ x' : W, L.E x x' = 0) → φ x = 0) → ∃ x₀ : W, ∀ x : W, φ x = L.E x₀ x) ∧ ∀ Hb : Matrix (Fin g) (Fin g) ℂ, Hb.IsHermitian → (∀ x x' : W, (per x ⬝ᵥ Hb *ᵥ star (per x')).im = L.E x x') → (∀ x : W, (∀ x' : W, L.E x x' = 0) → Hb *ᵥ star (per x) = 0) → ∀ v : Fin g → ℂ, 0 ≤ (v ⬝ᵥ Hb *ᵥ star v).re ∧ (v ⬝ᵥ Hb *ᵥ star v).re ≤ (c⁻¹ * K) * ∑ i, ‖v i‖ ^ 2 ∧ ((v ⬝ᵥ Hb *ᵥ star v).re = 0 → v ∈ Submodule.span ℂ {p | ∃ x : W, (∀ x' : W, L.E x x' = 0) ∧ p = per x}) := by
  classical
  have h2pi : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := Complex.two_pi_I_ne_zero
  have hzk : ∀ k, ‖z k‖ < ρ := fun k =>
    lt_of_le_of_lt (norm_le_pi_norm z k) (by simpa [dist_zero_right] using hz)
  have hzball : z ∈ Metric.ball (0 : Fin n → ℂ) 1 := Metric.ball_subset_ball hρ hz
  set cj : Fin a → Fin n := Fin.castLE L.a_le with hcj
  set l : Fin a → ℂ := fun j => if z (cj j) = 0 then 0 else Complex.log (z (cj j)) with hl
  set Bs : Matrix (Fin g) (Fin g) ℤ := ∑ j, if z (cj j) = 0 then B j else 0 with hBs
  set r : ℕ → ℝ := fun m => ρ⁻¹ + m with hr
  set t : ℕ → ℂ := fun m => ((r m / (2 * Real.pi) : ℝ) : ℂ) * Complex.I with ht
  set ws : ℕ → Fin n → ℂ := fun m k =>
    if k.val < a then (if z k = 0 then -(r m : ℂ) else Complex.log (z k)) else z k with hws
  set σf : (Fin n → ℂ) → Matrix (Fin g) (Fin g) ℂ := fun z' =>
    T0 z' + ∑ j, (l j / (2 * Real.pi * Complex.I)) • (B j).map (fun x : ℤ => (x : ℂ)) with hσf
  have hrpos : ∀ m, 0 < r m := fun m => by
    have : 0 < ρ⁻¹ := inv_pos.2 hρ0
    have h2 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    simp only [hr]; linarith
  have hexpr : ∀ m, Real.exp (-(r m)) < ρ := by
    intro m
    have h1 : r m + 1 ≤ Real.exp (r m) := Real.add_one_le_exp _
    have h3 : ρ⁻¹ ≤ r m := by
      have h2 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
      simp only [hr]; linarith
    rw [Real.exp_neg]
    have h4 : ρ⁻¹ < Real.exp (r m) := by linarith
    exact inv_lt_of_inv_lt₀ hρ0 h4

  have hws_mem : ∀ m, ws m ∈ logCover L.a_le := by
    intro m
    refine ⟨fun i => ?_, fun k hk => ?_⟩
    · have hi : (Fin.castLE L.a_le i).val < a := i.2
      simp only [hws, hi, if_true]
      by_cases h0 : z (Fin.castLE L.a_le i) = 0
      · simp [h0, hrpos m]
      · simp only [h0, if_false, Complex.log_re]
        exact Real.log_neg (norm_pos_iff.2 h0) ((hzk _).trans_le hρ)
    · have hk' : ¬ k.val < a := not_lt.2 hk
      simp only [hws, hk', if_false]
      exact (hzk k).trans_le hρ
  set zs : ℕ → Fin n → ℂ := fun m => expCover a (ws m) with hzs
  have hzs_k : ∀ m k, zs m k = if k.val < a ∧ z k = 0 then ((Real.exp (-(r m)) : ℝ) : ℂ) else z k := by
    intro m k
    simp only [hzs, expCover, hws]
    by_cases hk : k.val < a
    · by_cases h0 : z k = 0
      · simp [hk, h0]
      · simp [hk, h0, Complex.exp_log h0]
    · simp [hk]
  have hzs_ball : ∀ m, zs m ∈ Metric.ball (0 : Fin n → ℂ) ρ := by
    intro m
    rw [mem_ball_zero_iff, pi_norm_lt_iff hρ0]
    intro k
    rw [hzs_k]
    split_ifs
    · rw [Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le]; exact hexpr m
    · exact hzk k
  have hrtop : Tendsto r atTop atTop :=
    tendsto_atTop_add_const_left _ _ tendsto_natCast_atTop_atTop
  have hzs_lim : Tendsto zs atTop (𝓝 z) := by
    rw [tendsto_pi_nhds]
    intro k
    simp only [hzs_k]
    by_cases h : k.val < a ∧ z k = 0
    · simp only [h, and_self, if_true]
      have h1 : Tendsto (fun m => Real.exp (-(r m))) atTop (𝓝 0) :=
        Real.tendsto_exp_atBot.comp (tendsto_neg_atTop_atBot.comp hrtop)
      have h2 := (Complex.continuous_ofReal.tendsto 0).comp h1
      simpa only [Function.comp_def, Complex.ofReal_zero] using h2
    · simp only [h, if_false]
      exact tendsto_const_nhds
  have hlexp : ∀ j, z (cj j) ≠ 0 → Complex.exp (l j) = z (cj j) := by
    intro j hj
    simp only [hl, hj, if_false]
    exact Complex.exp_log hj
  have hl0 : ∀ j, z (cj j) = 0 → l j = 0 := by
    intro j hj
    simp only [hl, hj, if_true]
  have hBsR : Bs.map (fun x : ℤ => (x : ℝ)) =
      ∑ j, if z (cj j) = 0 then (B j).map (fun x : ℤ => (x : ℝ)) else 0 := by
    ext p q
    simp only [hBs, Matrix.map_apply, Matrix.sum_apply]
    push_cast
    refine Finset.sum_congr rfl fun j _ => ?_
    split_ifs <;> simp
  have hBsC : Bs.map (fun x : ℤ => (x : ℂ)) =
      ∑ j, if z (cj j) = 0 then (B j).map (fun x : ℤ => (x : ℂ)) else 0 := by
    ext p q
    simp only [hBs, Matrix.map_apply, Matrix.sum_apply]
    push_cast
    refine Finset.sum_congr rfl fun j _ => ?_
    split_ifs <;> simp
  have hBsPSD : (Bs.map (fun x : ℤ => (x : ℝ))).PosSemidef := by
    rw [hBsR]
    refine posSemidef_sum _ fun j _ => ?_
    split_ifs
    · exact hB j
    · exact PosSemidef.zero
  have hBsT : Bsᵀ = Bs := GlobalTheory.CompanionTheory.ToricBasis.symm_of_posSemidef hBsPSD
  have hker_each : ∀ v : Fin g → ℝ, Bs.map (fun x : ℤ => (x : ℝ)) *ᵥ v = 0 →
      ∀ j, z (cj j) = 0 → (B j).map (fun x : ℤ => (x : ℝ)) *ᵥ v = 0 := by
    intro v hv j hj
    have h0 : v ⬝ᵥ (Bs.map (fun x : ℤ => (x : ℝ)) *ᵥ v) = 0 := by rw [hv]; simp
    rw [hBsR, Matrix.sum_mulVec, dotProduct_sum] at h0
    have hnn : ∀ i ∈ Finset.univ, 0 ≤ v ⬝ᵥ ((if z (cj i) = 0 then
        (B i).map (fun x : ℤ => (x : ℝ)) else 0) *ᵥ v) := by
      intro i _
      split_ifs
      · simpa using (hB i).dotProduct_mulVec_nonneg v
      · simp
    have h1 := (Finset.sum_eq_zero_iff_of_nonneg hnn).1 h0 j (Finset.mem_univ j)
    rw [if_pos hj] at h1
    exact ((hB j).dotProduct_mulVec_zero_iff v).1 (by simpa using h1)
  have htm : ∀ m, (-(r m : ℂ)) / (2 * Real.pi * Complex.I) = t m := by
    intro m
    rw [div_eq_iff h2pi]
    have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    simp only [ht]
    push_cast
    field_simp
    simp
  have hdecomp : ∀ m, T0 (zs m) + ∑ j, (ws m (cj j) / (2 * Real.pi * Complex.I)) •
      (B j).map (fun x : ℤ => (x : ℂ)) = σf (zs m) + t m • Bs.map (fun x : ℤ => (x : ℂ)) := by
    intro m
    simp only [hσf]
    rw [add_assoc, hBsC, Finset.smul_sum, ← Finset.sum_add_distrib]
    congr 1
    refine Finset.sum_congr rfl fun j _ => ?_
    have hj : (cj j).val < a := j.2
    by_cases h : z (cj j) = 0
    · simp only [hws, hj, if_true, h, hl, htm m]
      simp
    · simp only [hws, hj, if_true, h, hl, if_false]
      simp
  have hlower : ∀ v : Fin g → ℝ, Bs.map (fun x : ℤ => (x : ℝ)) *ᵥ v = 0 →
      c * (v ⬝ᵥ v) ≤ v ⬝ᵥ (((σf z).map Complex.im) *ᵥ v) := fun v hv =>
    GlobalTheory.CompanionTheory.ChartBlockLower.im_lower_on_kernel n a g L.a_le (Metric.ball 0 ρ) T0 B c
      Metric.isOpen_ball (hTc.mono (Metric.ball_subset_ball hρ)) hB hc hY z hz l hlexp hl0 v
      (fun j hj => hker_each v hv j hj)
  have hT0lim : Tendsto (fun m => T0 (zs m)) atTop (𝓝 (T0 z)) :=
    ((hTc.continuousAt (Metric.isOpen_ball.mem_nhds hzball)).tendsto).comp hzs_lim
  have hAlim : Tendsto (fun m => A (zs m)) atTop (𝓝 (A z)) :=
    ((hAc.continuousAt (Metric.isOpen_ball.mem_nhds hzball)).tendsto).comp hzs_lim
  have hσlim : Tendsto (fun m => σf (zs m)) atTop (𝓝 (σf z)) :=
    hT0lim.add tendsto_const_nhds
  have hσsym : (σf z)ᵀ = σf z := by
    have each : ∀ m, (σf (zs m))ᵀ = σf (zs m) := by
      intro m
      have h1 := hsym (ws m) (hws_mem m)
      have h2 := hdecomp m
      simp only [hzs] at h2
      rw [h2] at h1
      have h3 : (Bs.map (fun x : ℤ => (x : ℂ)))ᵀ = Bs.map (fun x : ℤ => (x : ℂ)) := by
        rw [← Matrix.transpose_map, hBsT]
      rw [Matrix.transpose_add, Matrix.transpose_smul, h3] at h1
      exact add_right_cancel h1
    have hc1 : Continuous (fun N : Matrix (Fin g) (Fin g) ℂ => Nᵀ) := continuous_id.matrix_transpose
    exact tendsto_nhds_unique ((hc1.tendsto _).comp hσlim)
      (hσlim.congr fun m => (each m).symm)
  have hPm : ∀ m x, L.P (ws m) x = (A (zs m))ᵀ *ᵥ (cst (uCo bas x) +
      (σf (zs m) + t m • Bs.map (fun x : ℤ => (x : ℂ))) *ᵥ cst (vCo bas x)) := by
    intro m x
    rw [← hdecomp m]
    exact hP _ (hws_mem m) x
  set W : Submodule ℤ Λ := LinearMap.ker (Bs.mulVecLin ∘ₗ vCo bas) with hW
  have hWmem : ∀ x, x ∈ W ↔ Bs *ᵥ vCo bas x = 0 := by
    intro x
    simp [hW, LinearMap.mem_ker]
  set perF : Λ → Fin g → ℂ := fun x => (A z)ᵀ *ᵥ (cst (uCo bas x) + σf z *ᵥ cst (vCo bas x)) with hperF
  have hperF_add : ∀ x y, perF (x + y) = perF x + perF y := by
    intro x y
    simp only [hperF, map_add, cst_add, mulVec_add]
    abel_nf
  set per : W →+ (Fin g → ℂ) := AddMonoidHom.mk' (fun x => perF x) (fun x y => hperF_add x y) with hper
  have hper_apply : ∀ x : W, per x = perF x := fun x => rfl
  have hmk : ∀ (u v : Fin g → ℤ), Bs *ᵥ v = 0 → mk bas u v ∈ W := by
    intro u v hv
    rw [hWmem, vCo_mk]; exact hv
  have halt := L.alt
  have hform := form_coords bas L.E hE halt

  have hrad : ∀ u : Fin g → ℤ, (∀ v : Fin g → ℤ, Bs *ᵥ v = 0 → u ⬝ᵥ v = 0) →
      ∀ x' : W, L.E (mk bas u 0) x' = 0 := by
    intro u hu x'
    rw [hform, vCo_mk, uCo_mk, hu _ ((hWmem _).1 x'.2)]
    simp
  refine ⟨ws, W, per, hws_mem, hzs_lim, ?_, ?_, ?_, ?_⟩
  ·
    intro x
    have hx : Bs *ᵥ vCo bas x = 0 := (hWmem _).1 x.2
    have e : ∀ m, L.P (ws m) x = (A (zs m))ᵀ *ᵥ (cst (uCo bas x) + σf (zs m) *ᵥ cst (vCo bas x)) := by
      intro m
      rw [hPm, Matrix.add_mulVec, Matrix.smul_mulVec, cst_mulVec, hx, cst_zero, smul_zero, add_zero]
    have hcts : Continuous (fun p : Matrix (Fin g) (Fin g) ℂ × Matrix (Fin g) (Fin g) ℂ =>
        p.1ᵀ *ᵥ (cst (uCo bas x) + p.2 *ᵥ cst (vCo bas x))) :=
      (continuous_fst.matrix_transpose).matrix_mulVec
        (continuous_const.add (continuous_snd.matrix_mulVec continuous_const))
    have := (hcts.tendsto (A z, σf z)).comp (hAlim.prodMk_nhds hσlim)
    exact this.congr fun m => (e m).symm
  ·
    intro x p hp
    have hdetz : (A z).det ≠ 0 := (hAinv z hz).1
    have hdetm : ∀ m, ((A (zs m))ᵀ).det ≠ 0 := fun m => by
      rw [det_transpose]; exact (hAinv _ (hzs_ball m)).1
    have hinv := tendsto_inv_transpose hAlim hdetz
    have hy := (((continuous_fst.matrix_mulVec continuous_snd :
      Continuous fun q : Matrix (Fin g) (Fin g) ℂ × (Fin g → ℂ) => q.1 *ᵥ q.2)).tendsto
        (((A z)ᵀ)⁻¹, p)).comp (hinv.prodMk_nhds hp)
    have hyeq : ∀ m, ((A (zs m))ᵀ)⁻¹ *ᵥ L.P (ws m) (x m) = cst (uCo bas (x m)) +
        (σf (zs m) + t m • Bs.map (fun x : ℤ => (x : ℂ))) *ᵥ cst (vCo bas (x m)) := by
      intro m
      rw [hPm, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ (Ne.isUnit (hdetm m)), Matrix.one_mulVec]
    have hy' : Tendsto (fun m => (fun k => ((uCo bas (x m) k : ℤ) : ℂ)) +
        (σf (zs m) + t m • Bs.map (fun x : ℤ => (x : ℂ))) *ᵥ (fun k => ((vCo bas (x m) k : ℤ) : ℂ)))
        atTop (𝓝 (((A z)ᵀ)⁻¹ *ᵥ p)) := hy.congr fun m => hyeq m
    have him : Tendsto (fun m => (t m).im) atTop atTop := by
      have h1 : ∀ m, (t m).im = r m / (2 * Real.pi) := fun m => by simp only [ht, Complex.mul_I_im, Complex.ofReal_re]
      simp only [h1]
      exact hrtop.atTop_div_const (by positivity)
    have hYm : ∀ m, ((σf (zs m) + t m • Bs.map (fun x : ℤ => (x : ℂ))).map Complex.im -
        c • (1 : Matrix (Fin g) (Fin g) ℝ)).PosSemidef := by
      intro m
      rw [← hdecomp m]
      refine hY _ (hzs_ball m) (fun j => ws m (cj j)) fun j => ?_
      have hj : (cj j).val < a := j.2
      simp [hzs, expCover, hj]
    obtain ⟨u, v, hv, hyv, hev⟩ := GlobalTheory.T.siegel_limit_imag_bound g Bs (σf z) (fun m => σf (zs m))
      (fun m => σf (zs m) + t m • Bs.map (fun x : ℤ => (x : ℂ))) t c (fun m => uCo bas (x m))
      (fun m => vCo bas (x m)) _ hc hσlim him (fun _ => rfl) hYm hlower hy'
    refine ⟨⟨mk bas u v, hmk u v hv⟩, ?_, ?_⟩
    · rw [hper_apply]
      simp only [hperF, uCo_mk, vCo_mk]
      have : cst u + σf z *ᵥ cst v = ((A z)ᵀ)⁻¹ *ᵥ p := hyv.symm
      rw [this, Matrix.mulVec_mulVec,
        Matrix.mul_nonsing_inv _ (Ne.isUnit (by rw [det_transpose]; exact hdetz)), Matrix.one_mulVec]
    · filter_upwards [hev] with m hm
      refine eq_of_coords bas ?_ ?_
      · rw [hm.1]; exact (uCo_mk bas u v).symm
      · rw [hm.2]; exact (vCo_mk bas u v).symm
  ·
    intro φ hφ
    let i₁ : (Fin g → ℤ) →+ W := AddMonoidHom.mk' (fun u => ⟨mk bas u 0, hmk u 0 (by simp)⟩) (by
      intro u u'
      refine Subtype.ext (eq_of_coords bas ?_ ?_)
      · simp [uCo_mk]
      · simp [vCo_mk])
    let i₂ : LinearMap.ker Bs.mulVecLin →+ W := AddMonoidHom.mk'
      (fun k => ⟨mk bas 0 k, hmk 0 k (by simpa only [Matrix.mulVecLin_apply] using LinearMap.mem_ker.1 k.2)⟩) (by
      intro k k'
      refine Subtype.ext (eq_of_coords bas ?_ ?_)
      · simp [uCo_mk]
      · simp [vCo_mk])
    obtain ⟨p, q, hp, h1, h2⟩ := unim g Bs hBsT (φ.comp i₁) (φ.comp i₂) (fun u hu =>
      hφ _ (fun x' => hrad u hu x'))
    refine ⟨⟨mk bas (-q) p, hmk _ _ hp⟩, fun x => ?_⟩
    have hxs : x = i₁ (uCo bas x) + i₂ ⟨vCo bas x, by simpa using (hWmem _).1 x.2⟩ := by
      refine Subtype.ext (eq_of_coords bas ?_ ?_)
      · simp [i₁, i₂, uCo_mk]
      · simp [i₁, i₂, vCo_mk]
    have e1 := h1 (uCo bas x)
    have e2 := h2 ⟨vCo bas x, by simpa using (hWmem _).1 x.2⟩
    simp only [AddMonoidHom.comp_apply] at e1 e2
    conv_lhs => rw [hxs]
    rw [map_add, e1, e2, hform, vCo_mk, uCo_mk, dotProduct_comm (uCo bas x) p]
    simp
  ·
    intro Hb hHb hIm hKill v
    have hdetz : (A z).det ≠ 0 := (hAinv z hz).1
    have hunit : IsUnit ((A z)ᵀ).det := Ne.isUnit (by rw [det_transpose]; exact hdetz)
    set G : Matrix (Fin g) (Fin g) ℂ := A z * Hb * (A z)ᴴ with hG
    have hGh : G.IsHermitian := Matrix.isHermitian_mul_mul_conjTranspose (A z) hHb
    have hconj : ∀ y y' : Fin g → ℂ, ((A z)ᵀ *ᵥ y) ⬝ᵥ Hb *ᵥ star ((A z)ᵀ *ᵥ y') = y ⬝ᵥ G *ᵥ star y' := by
      intro y y'
      rw [Matrix.mulVec_transpose, Matrix.mulVec_transpose, Matrix.star_vecMul,
        ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
    have hrel : ∀ u u' v v' : Fin g → ℤ, Bs *ᵥ v = 0 → Bs *ᵥ v' = 0 →
        (((fun k => (u k : ℂ)) + σf z *ᵥ (fun k => (v k : ℂ))) ⬝ᵥ G *ᵥ
          star ((fun k => (u' k : ℂ)) + σf z *ᵥ (fun k => (v' k : ℂ)))).im =
          ((v ⬝ᵥ u' - u ⬝ᵥ v' : ℤ) : ℝ) := by
      intro u u' v v' hv hv'
      have h1 := hIm ⟨mk bas u v, hmk u v hv⟩ ⟨mk bas u' v', hmk u' v' hv'⟩
      rw [hper_apply, hper_apply] at h1
      simp only [hperF, uCo_mk, vCo_mk, hconj] at h1
      rw [hform] at h1
      simp only [vCo_mk, uCo_mk] at h1
      exact h1
    have hkerG : ∀ u : Fin g → ℤ, (∀ v : Fin g → ℤ, Bs *ᵥ v = 0 → u ⬝ᵥ v = 0) →
        G *ᵥ (fun k => (u k : ℂ)) = 0 := by
      intro u hu
      have h1 := hKill ⟨mk bas u 0, hmk u 0 (by simp)⟩ (fun x' => hrad u hu x')
      rw [hper_apply] at h1
      simp only [hperF, uCo_mk, vCo_mk, cst_zero, mulVec_zero, add_zero] at h1
      have h2 : star ((A z)ᵀ *ᵥ cst u) = (A z)ᴴ *ᵥ cst u := by
        funext i
        simp [cst, mulVec, dotProduct, Matrix.conjTranspose_apply, map_sum]
      rw [h2] at h1
      rw [hG, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
      have h3 : Hb *ᵥ ((A z)ᴴ *ᵥ (fun k => (u k : ℂ))) = 0 := h1
      rw [h3, mulVec_zero]
    set y : Fin g → ℂ := ((A z)ᵀ)⁻¹ *ᵥ v with hy
    have hvy : (A z)ᵀ *ᵥ y = v := by
      rw [hy, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hunit, Matrix.one_mulVec]
    obtain ⟨f1, f2, f3⟩ := GlobalTheory.T.riemann_form_hermitian_lattice g Bs (σf z) G c hc hBsPSD hσsym hlower hGh hrel hkerG y
    have hval : v ⬝ᵥ Hb *ᵥ star v = y ⬝ᵥ G *ᵥ star y := by
      rw [← hconj, hvy]
    rw [hval]
    refine ⟨f1, ?_, fun h0 => ?_⟩
    · refine f2.trans ?_
      have h1 := (hAinv z hz).2 y
      rw [hvy] at h1
      rw [_root_.mul_assoc]
      exact mul_le_mul_of_nonneg_left h1 (inv_nonneg.2 hc.le)
    · have h1 := f3 h0
      rw [← hvy]
      have h2 := Submodule.mem_map_of_mem (f := ((A z)ᵀ).mulVecLin) h1
      rw [Submodule.map_span] at h2
      refine Submodule.span_mono ?_ h2
      rintro _ ⟨p, ⟨u, hu, rfl⟩, rfl⟩
      refine ⟨⟨mk bas u 0, hmk u 0 (by simp)⟩, fun x' => hrad u hu x', ?_⟩
      rw [hper_apply]
      simp only [hperF, uCo_mk, vCo_mk, cst_zero, mulVec_zero, add_zero]
      rfl

theorem bounded_on_limit_lattice : ∀ (n a g : ℕ) (Λ : Type) [AddCommGroup Λ] (L : Flat.LogPeriods n a g Λ), ∃ ρ C : ℝ, 0 < ρ ∧ ρ ≤ 1 ∧ ∀ z ∈ Metric.ball (0 : Fin n → ℂ) ρ, ∃ (ws : ℕ → Fin n → ℂ) (W : Submodule ℤ Λ) (per : W →+ (Fin g → ℂ)), (∀ m, ws m ∈ GroundTheory.Heights₂.Heights.Regular.logCover L.a_le) ∧ Tendsto (fun m => GroundTheory.Heights₂.Heights.Regular.expCover a (ws m)) atTop (𝓝 z) ∧ (∀ x : W, Tendsto (fun m => L.P (ws m) x) atTop (𝓝 (per x))) ∧ (∀ (x : ℕ → Λ) (p : Fin g → ℂ), Tendsto (fun m => L.P (ws m) (x m)) atTop (𝓝 p) → ∃ x₀ : W, p = per x₀ ∧ ∀ᶠ m in atTop, x m = x₀) ∧ (∀ φ : W →+ ℤ, (∀ x : W, (∀ x' : W, L.E x x' = 0) → φ x = 0) → ∃ x₀ : W, ∀ x : W, φ x = L.E x₀ x) ∧ ∀ Hb : Matrix (Fin g) (Fin g) ℂ, Hb.IsHermitian → (∀ x x' : W, (per x ⬝ᵥ Hb *ᵥ star (per x')).im = L.E x x') → (∀ x : W, (∀ x' : W, L.E x x' = 0) → Hb *ᵥ star (per x) = 0) → ∀ v : Fin g → ℂ, 0 ≤ (v ⬝ᵥ Hb *ᵥ star v).re ∧ (v ⬝ᵥ Hb *ᵥ star v).re ≤ C * ∑ i, ‖v i‖ ^ 2 ∧ ((v ⬝ᵥ Hb *ᵥ star v).re = 0 → v ∈ Submodule.span ℂ {p | ∃ x : W, (∀ x' : W, L.E x x' = 0) ∧ p = per x}) := by
  intro n a g Λ _ L
  obtain ⟨bas, Q, A, T0, hE, hAd, hA0, hT0, hBpsd, hPa, hPb⟩ := GlobalTheory.T.symplectic_polydisc_period_basis n a g Λ L
  obtain ⟨ρ₁, c, C₁, hρ₁, hρ₁1, hc, hb⟩ :=
    (ImTauBounds.cond RiemannExtensionSlices.proof PuncturedExpOrder.proof LogCoverDescent.proof) n a g Q
  have hAc : ContinuousOn A (Metric.ball 0 1) :=
    continuousOn_pi.2 fun i => continuousOn_pi.2 fun j => (hAd i j).continuousOn
  have hTc : ContinuousOn T0 (Metric.ball 0 1) :=
    continuousOn_pi.2 fun i => continuousOn_pi.2 fun j => (hT0.1 i j).continuousOn
  have h0ball : (0 : Fin n → ℂ) ∈ Metric.ball (0 : Fin n → ℂ) 1 := Metric.mem_ball_self one_pos
  obtain ⟨ρ₂, K, hρ₂, hK, hinv⟩ := inv n g A
    (hAc.continuousAt (Metric.isOpen_ball.mem_nhds h0ball)) hA0
  have hτ : ∀ w ∈ logCover L.a_le, Q.τ w = T0 (expCover a w) +
      ∑ j, (w (Fin.castLE L.a_le j) / (2 * Real.pi * Complex.I)) •
        (Q.B j).map (fun x : ℤ => (x : ℂ)) := by
    intro w hw
    have h := hT0.2 w hw
    simp only [PeriodPolydisc.tau0] at h
    rw [← h]
    exact (sub_add_cancel _ _).symm
  set ρ : ℝ := min (min ρ₁ ρ₂) 1 with hρ
  have hρpos : 0 < ρ := lt_min (lt_min hρ₁ hρ₂) one_pos
  have hρ1 : ρ ≤ 1 := min_le_right _ _
  have hρρ₁ : ρ ≤ ρ₁ := (min_le_left _ _).trans (min_le_left _ _)
  have hρρ₂ : ρ ≤ ρ₂ := (min_le_left _ _).trans (min_le_right _ _)
  refine ⟨ρ, c⁻¹ * K, hρpos, hρ1, fun z hz => ?_⟩
  refine at_point L bas A T0 Q.B c K ρ hc hρpos hρ1 hE hAc hTc hK
    (fun z hz => hinv z (Metric.ball_subset_ball hρρ₂ hz)) hBpsd ?_ ?_ ?_ z hz
  · intro z hz l hl
    have hz1 : ∀ k, ‖z k‖ < 1 := fun k =>
      lt_of_le_of_lt (norm_le_pi_norm z k)
        (lt_of_lt_of_le (by simpa [dist_zero_right] using hz) hρ1)
    let w : Fin n → ℂ := fun k => if h : k.val < a then l ⟨k.val, h⟩ else z k
    have hwj : ∀ j : Fin a, w (Fin.castLE L.a_le j) = l j := by
      intro j
      have hj : (Fin.castLE L.a_le j).val < a := j.2
      simp [w, hj]
    have hexp : expCover a w = z := by
      funext k
      by_cases hk : k.val < a
      · have := hl ⟨k.val, hk⟩
        simp only [expCover, hk, if_true, w, dif_pos]
        rw [this]
        rfl
      · simp [expCover, hk, w]
    have hw : w ∈ logCover L.a_le := by
      refine ⟨fun i => ?_, fun k hk => ?_⟩
      · rw [hwj]
        have h1 : ‖Complex.exp (l i)‖ < 1 := by rw [hl i]; exact hz1 _
        rw [Complex.norm_exp] at h1
        exact Real.exp_lt_one_iff.1 h1
      · have hk' : ¬ k.val < a := not_lt.2 hk
        simp only [w, hk', dif_neg, not_false_eq_true]
        exact hz1 k
    have h1 := (hb w hw (by rw [hexp]; exact Metric.ball_subset_closedBall (Metric.ball_subset_ball hρρ₁ hz))).1
    rw [hτ w hw, hexp] at h1
    simp only [hwj] at h1
    exact h1
  · intro w hw
    rw [← hτ w hw]
    exact Q.symm w hw
  · intro w hw x
    rw [← hτ w hw]
    exact per_coords bas (L.P w) (Q.τ w) (A (expCover a w)) (Q.symm w hw) (hPa w hw) (hPb w hw) x

end GlobalTheory.CompanionTheory.Ar.RiemannLimit
