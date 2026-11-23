import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IntFormsSubset
import Development.AbelianVarietyTheory.Definitions.HeightFunctions.XiValIffXiAt
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.CoeSelfDualLatticeInFrameCoordinatesEq
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.ExistsBorelOrthonormalMove
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.EqZeroOfMulEqZero
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.GGConn
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.FourierCoefficientDomain
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LevelCoverComponentReadingsUnitModulusScalarStatement
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj GlobalTheory.CoverRead GlobalTheory.Member GlobalTheory.CompRat GlobalTheory.FinalJoin
open scoped TensorProduct Matrix

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CoverConst

theorem eq_const_mul_of_norm_one : ∀ {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] {ι : Type*} (U : Set V), IsOpen U → IsPreconnected U → ∀ (P₂ P : ι → V → ℂ) (g : V → ℂ), (∀ i, DifferentiableOn ℂ (P₂ i) U) → (∀ i, DifferentiableOn ℂ (P i) U) → (∀ x ∈ U, ‖g x‖ = 1) → (∀ i, ∀ x ∈ U, P₂ i x = g x * P i x) → ∃ u : ℂ, ‖u‖ = 1 ∧ ∀ i, ∀ x ∈ U, P₂ i x = u * P i x := by
  intro V _ _ ι U hU hc P₂ P g hP₂ hP hg1 hg
  by_cases h : ∃ i, ∃ x ∈ U, P i x ≠ 0
  swap
  · push_neg at h
    refine ⟨1, by simp, fun i x hx => ?_⟩
    rw [hg i x hx, h i x hx]
    simp
  obtain ⟨i₀, x₀, hx₀, hne⟩ := h
  have hcont : ContinuousAt (P i₀) x₀ := (hP i₀).continuousOn.continuousAt (hU.mem_nhds hx₀)
  have hnb : ∀ᶠ y in nhds x₀, y ∈ U ∧ P i₀ y ≠ 0 := (hU.eventually_mem hx₀).and (hcont.eventually_ne hne)
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff_ball.1 hnb
  have hx₀b : x₀ ∈ Metric.ball x₀ ε := Metric.mem_ball_self hε
  let q : V → ℂ := fun y => P₂ i₀ y * (P i₀ y)⁻¹
  have hqd : DifferentiableOn ℂ q (Metric.ball x₀ ε) :=
    ((hP₂ i₀).mono (fun y hy => (hball y hy).1)).mul (((hP i₀).mono (fun y hy => (hball y hy).1)).inv
      (fun y hy => (hball y hy).2))
  have hqg : ∀ y ∈ Metric.ball x₀ ε, q y = g y := fun y hy => by
    simp only [q]
    rw [hg i₀ y (hball y hy).1, mul_assoc, mul_inv_cancel₀ (hball y hy).2, mul_one]
  have hmax : IsMaxOn (norm ∘ q) (Metric.ball x₀ ε) x₀ := fun y hy => by
    simp only [Set.mem_setOf_eq, Function.comp_apply]
    rw [hqg y hy, hqg x₀ hx₀b, hg1 _ (hball y hy).1, hg1 _ (hball x₀ hx₀b).1]
  have heq := Complex.eqOn_of_isPreconnected_of_isMaxOn_norm (convex_ball x₀ ε).isPreconnected
    Metric.isOpen_ball hqd hx₀b hmax
  refine ⟨g x₀, hg1 x₀ hx₀, fun i => ?_⟩
  have hzero : ∀ y ∈ U, (fun y => P₂ i y - g x₀ * P i y) y = 0 := by
    refine ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf.eq_zero_of_eventually hU hc ((hP₂ i).sub ((hP i).const_mul (g x₀))) hx₀ ?_
    filter_upwards [Metric.ball_mem_nhds x₀ hε] with y hy
    have e : g y = g x₀ := by
      rw [← hqg y hy, ← hqg x₀ hx₀b]
      exact heq hy
    simp only [Pi.zero_apply]
    rw [hg i y (hball y hy).1, e]
    ring
  intro x hx
  have := hzero x hx
  simp only at this
  exact sub_eq_zero.1 this

theorem psi_and_weight_eq : ∀ (D : D7) (T : CoreJ D), LawsJ T → ∀ j, Formalism.L2.Pj.InR D j → ∀ σ : T.Q.c.F →+* ℂ, GoodEmb T.Q.c σ → ∀ C : Cover T j σ, C.IsUnif → ∀ (k₂ : C.U₂.Comp) (k : (T.U j σ).Comp), (∀ τ : D.host.E →+* ℂ, τ ∈ (C.U₂.X k₂).Ψ ↔ τ ∈ ((T.U j σ).X k).Ψ) ∧ ∀ (a : (D.host.E →+* ℂ) × ℕ → ℕ) (n : ℕ) (τ : D.host.E →+* ℂ) (h₂ : τ ∈ (C.U₂.X k₂).Ψ) (h₁ : τ ∈ ((T.U j σ).X k).Ψ) (i : Fin D.R.r), laU C.U₂ a n k₂ ⟨τ, h₂⟩ i = laU (T.U j σ) a n k ⟨τ, h₁⟩ i := by
  intro D T hL j hj σ hσ C hC k₂ k
  have hU₂ : IsUnf C.U₂ := hC.2.2.2.1
  have hU₁ : IsUnf (T.U j σ) := hL.unf j hj σ hσ
  have hrel : relab C.d.c₂ C.σ₂ = relab T.Q.c σ := by
    funext τ
    ext x
    have e := congrArg (fun φ : T.Q.c.F →+* ℂ => φ (embF T.Q.c τ x)) hC.2.2.1
    simp only [RingHom.comp_apply] at e
    show C.σ₂ (embF C.d.c₂ τ x) = σ (embF T.Q.c τ x)
    rw [← e]
    congr 1
  refine ⟨fun τ => by rw [(hU₂.2.1 k₂).2 τ, (hU₁.2.1 k).2 τ], fun a n τ h₂ h₁ i => ?_⟩
  unfold laU
  rw [(hU₂.2.1 k₂).1, (hU₁.2.1 k).1, hrel]

theorem cover_scalar_const : ∀ (D : D7) (T : CoreJ D), LawsJ T → ∀ j, Formalism.L2.Pj.InR D j → ∀ σ : T.Q.c.F →+* ℂ, GoodEmb T.Q.c σ → ∀ C : Cover T j σ, C.IsUnif → ∀ n : ℕ, ∀ k₂ : C.U₂.Comp, ∃ (k : (T.U j σ).Comp) (γ : GL (Fin D.R.r) D.host.E), (((T.U j σ).X k).Λ : Set (Fin D.R.r → D.host.E)) = (γ : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E).mulVec '' ((C.U₂.X k₂).Λ : Set _) ∧ (∀ v w, herm ((T.U j σ).X k).Gm ((γ : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E).mulVec v) ((γ : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E).mulVec w) = herm (C.U₂.X k₂).Gm v w) ∧ (∀ h, (C.dict₂ h).1 = k₂ → (T.dict j σ h).1 = k) ∧ ∃ u : ℂ, ‖u‖ = 1 ∧ ∀ (x : Frame (C.U₂.X k₂).Ψ D.R.r) (x' : Frame ((T.U j σ).X k).Ψ D.R.r), x ∈ (C.U₂.X k₂).dom → (∀ (τ : D.host.E →+* ℂ) (h₂ : τ ∈ (C.U₂.X k₂).Ψ) (h₁ : τ ∈ ((T.U j σ).X k).Ψ), mat x' ⟨τ, h₁⟩ = (γ : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E).map τ * mat x ⟨τ, h₂⟩) → x' ∈ ((T.U j σ).X k).dom ∧ ∀ (a : (D.host.E →+* ℂ) × ℕ → ℕ), Dom a n → ∀ f ∈ sec (T.Q.Xo j) T.Q.c a n, ∀ f₂ ∈ sec C.d.Xo₂ C.d.c₂ a n, C.IsPull f f₂ → rdU C.U₂ f₂ k₂ x = u * rdU (T.U j σ) f k x' := by
  intro D T hL j hj σ hσ C hC n k₂
  obtain ⟨k, γ, hΛ, hh, hd, hx⟩ := GlobalTheory.T.levelCover_component_readings_unit_modulus_scalar D T hL j hj σ hσ C hC k₂
  obtain ⟨hΨ, hla⟩ := psi_and_weight_eq D T hL j hj σ hσ C hC k₂ k
  refine ⟨k, γ, hΛ, hh, hd, ?_⟩
  have hU₂ : IsUnf C.U₂ := hC.2.2.2.1
  have hU₁ : IsUnf (T.U j σ) := hL.unf j hj σ hσ

  let G : Frame (C.U₂.X k₂).Ψ D.R.r → Frame ((T.U j σ).X k).Ψ D.R.r := fun x τ =>
    ((γ : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E).map τ.1 * mat x ⟨τ.1, (hΨ τ.1).2 τ.2⟩ : Matrix (Fin D.R.r) (Fin D.R.r) ℂ)
  have hGrel : ∀ x (τ : D.host.E →+* ℂ) (h₂ : τ ∈ (C.U₂.X k₂).Ψ) (h₁ : τ ∈ ((T.U j σ).X k).Ψ),
      mat (G x) ⟨τ, h₁⟩ = (γ : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E).map τ * mat x ⟨τ, h₂⟩ := by
    intro x τ h₂ h₁
    rfl
  have hGdom : ∀ x ∈ (C.U₂.X k₂).dom, G x ∈ ((T.U j σ).X k).dom := fun x hx' => (hx x (G x) hx' (hGrel x)).1
  have hGdiff : Differentiable ℂ G := by
    refine differentiable_pi.2 fun τ => differentiable_pi.2 fun a => differentiable_pi.2 fun b => ?_
    simp only [G, mat, Matrix.mul_apply, Matrix.of_apply, Matrix.map_apply]
    fun_prop

  let ι := {p : ((D.host.E →+* ℂ) × ℕ → ℕ) × Rul (T.Q.Xo j) T.Q.c × Rul C.d.Xo₂ C.d.c₂ //
    Dom p.1 n ∧ p.2.1 ∈ sec (T.Q.Xo j) T.Q.c p.1 n ∧ p.2.2 ∈ sec C.d.Xo₂ C.d.c₂ p.1 n ∧ C.IsPull p.2.1 p.2.2}
  let P₂ : ι → Frame (C.U₂.X k₂).Ψ D.R.r → ℂ := fun i => rdU C.U₂ i.1.2.2 k₂
  let P : ι → Frame (C.U₂.X k₂).Ψ D.R.r → ℂ := fun i x => rdU (T.U j σ) i.1.2.1 k (G x)
  have hP₂d : ∀ i, DifferentiableOn ℂ (P₂ i) (C.U₂.X k₂).dom := fun i =>
    (hU₂.2.2.2.2.1 i.1.1 n i.2.1 i.1.2.2 i.2.2.2.1 k₂).1
  have hPd : ∀ i, DifferentiableOn ℂ (P i) (C.U₂.X k₂).dom := fun i =>
    (hU₁.2.2.2.2.1 i.1.1 n i.2.1 i.1.2.1 i.2.2.1 k).1.comp hGdiff.differentiableOn hGdom
  have hg : ∀ x ∈ (C.U₂.X k₂).dom, ∃ c : ℂ, ‖c‖ = 1 ∧ ∀ i : ι, P₂ i x = c * P i x := by
    intro x hxd
    obtain ⟨b, hb, hyd, hyo⟩ := ReciprocityTheory.ChartRestriction.G.PullbackSections.exists_borel_orthonormal_move (C.U₂.X k₂) hxd
    obtain ⟨-, t, -, hmod, hrel⟩ := hx (rmul x b) (G (rmul x b)) hyd (hGrel _)
    have ht1 : ‖t‖ = 1 := hmod (fun τ i => ReciprocityTheory.ChartRestriction.G.PullbackSections.norm_diagonal_minor_one _ hyo τ i)
    refine ⟨t ^ n, by rw [norm_pow, ht1, one_pow], ?_⟩
    rintro ⟨⟨a, f, f₂⟩, hDom, hf, hf₂, hP⟩
    let b₁ : Frame ((T.U j σ).X k).Ψ D.R.r := fun τ => b ⟨τ.1, (hΨ τ.1).2 τ.2⟩
    have hb₁ : b₁ ∈ Bor ((T.U j σ).X k).Ψ D.R.r := fun τ => hb ⟨τ.1, (hΨ τ.1).2 τ.2⟩
    have e1 := hrel n a hDom f hf f₂ hf₂ hP
    have e2 : rdU C.U₂ f₂ k₂ (rmul x b) = bchar (laU C.U₂ a n k₂) b * rdU C.U₂ f₂ k₂ x :=
      (hU₂.2.2.2.2.1 a n hDom f₂ hf₂ k₂).2.1 x hxd b hb
    have e3 : G (rmul x b) = rmul (G x) b₁ := by
      funext τ
      simp only [G, rmul, b₁, mat]
      exact (Matrix.mul_assoc ((γ : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E).map τ.1) (mat x ⟨τ.1, (hΨ τ.1).2 τ.2⟩) (mat b ⟨τ.1, (hΨ τ.1).2 τ.2⟩)).symm
    have e4 : rdU (T.U j σ) f k (rmul (G x) b₁) = bchar (laU (T.U j σ) a n k) b₁ * rdU (T.U j σ) f k (G x) :=
      (hU₁.2.2.2.2.1 a n hDom f hf k).2.1 (G x) (hGdom x hxd) b₁ hb₁
    have e5 : bchar (laU C.U₂ a n k₂) b = bchar (laU (T.U j σ) a n k) b₁ := by
      unfold bchar
      refine Fintype.prod_equiv (Equiv.subtypeEquivRight (fun τ => hΨ τ)) _ _ (fun τ => ?_)
      refine Finset.prod_congr rfl (fun i _ => ?_)
      rw [hla a n τ.1 τ.2 ((hΨ τ.1).1 τ.2) i]
      rfl
    have e6 : bchar (laU C.U₂ a n k₂) b ≠ 0 := by
      unfold bchar
      refine Finset.prod_ne_zero_iff.2 fun τ _ => Finset.prod_ne_zero_iff.2 fun i _ => zpow_ne_zero _ ?_
      have hdet : (mat b τ).det ≠ 0 := (hb τ).1
      rw [Matrix.det_of_upperTriangular (M := mat b τ) (fun a c h => (hb τ).2 a c h)] at hdet
      simpa [mat] using Finset.prod_ne_zero_iff.1 hdet i (Finset.mem_univ _)
    show rdU C.U₂ f₂ k₂ x = t ^ n * rdU (T.U j σ) f k (G x)
    apply mul_left_cancel₀ e6
    rw [← e2, e1, e3, e4, ← e5]
    ring
  classical
  let g : Frame (C.U₂.X k₂).Ψ D.R.r → ℂ := fun x => if h : x ∈ (C.U₂.X k₂).dom then (hg x h).choose else 1
  have hg1 : ∀ x ∈ (C.U₂.X k₂).dom, ‖g x‖ = 1 := fun x h => by
    simp only [g, dif_pos h]; exact (hg x h).choose_spec.1
  have hgr : ∀ i, ∀ x ∈ (C.U₂.X k₂).dom, P₂ i x = g x * P i x := fun i x h => by
    simp only [g, dif_pos h]; exact (hg x h).choose_spec.2 i
  obtain ⟨u, hu1, hu⟩ := eq_const_mul_of_norm_one (C.U₂.X k₂).dom (ReciprocityTheory.ChartRestriction.G.FD.FourierCoefficientDomain.isOpen_dom _)
    (ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.flag_domain_frames_connected D.R.r (C.U₂.X k₂)).isPreconnected P₂ P g hP₂d hPd hg1 hgr
  refine ⟨u, hu1, fun x x' hxd hrel' => ⟨(hx x x' hxd hrel').1, ?_⟩⟩
  have hx' : x' = G x := by
    funext τ
    exact hrel' τ.1 ((hΨ τ.1).2 τ.2) τ.2
  intro a hDom f hf f₂ hf₂ hP
  rw [hx']
  exact hu ⟨(a, f, f₂), hDom, hf, hf₂, hP⟩ x hxd

end GlobalTheory.CoverConst
