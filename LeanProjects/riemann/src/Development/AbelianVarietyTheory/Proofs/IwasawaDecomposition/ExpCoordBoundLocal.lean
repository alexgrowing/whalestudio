import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsIsHodgeFrameIff
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsExponentialChartAtPointStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsContinuousOnFrameDirectionsInverse
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PosDefUniformBoundsNearPointStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsAffineEigenframeNearPointStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExponentialMapOriginIdentityStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EigenframeContinuousFamilyStatement
open AlgebraicGeometry CategoryTheory Limits NumberField Matrix
open ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj GlobalTheory GlobalTheory.CxPts GlobalTheory.Toroidal GlobalTheory.LieMet GlobalTheory.GradedNorm GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Hor
open scoped Topology ComplexOrder
open MonoidalCategory CartesianMonoidalCategory MonObj

set_option autoImplicit false

noncomputable section

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ExpChartMetric

theorem h0_le_exp_coord : ∀ (D : D7) (A : Amb D) (N j : ℕ) (S : Sig A N j) (κ : Lv A) (s : FinalTheorems S κ) (x : ToroidalCompactificationData s) (σ : κ.c.F →+* ℂ) (n g : ℕ) (e : OpenPartialHomeomorph (CxPts (genStr s.T.Z) σ) (Fin n → ℂ)) (ex : ExpMaps s.T.Z σ g), IsExpChart e ex → ∀ y₀ ∈ e.source, ∃ U ∈ 𝓝 y₀, ∃ C : ℝ, 0 ≤ C ∧ ∀ y ∈ U, ∀ (f : EigFrame s.T.Z σ (y.1 ≫ genι s.T.Z)) (W : Letter S.Dw → Fin g → ℂ), Dirs (Z := s.T.Z) ⟨y, f⟩ (fun w => (ex y w).left) W → ∀ (τ : D.host.E →+* ℂ) (v : Fin (S.Dw.mult τ) → ℂ), ‖∑ b, v b • W ⟨τ, b⟩‖ ^ 2 ≤ C * (star v ⬝ᵥ x.gram y f τ *ᵥ v).re ∧ (star v ⬝ᵥ x.gram y f τ *ᵥ v).re ≤ C * ‖∑ b, v b • W ⟨τ, b⟩‖ ^ 2 := by
  intro D A N j S κ s x σ n g e ex he y₀ hy₀
  classical
  obtain ⟨V, φ, F, B, a, hB, hb₀, hBt, ha, hab⟩ := GlobalTheory.T.exists_affine_eigenframe_near_point _ _ _ _ _ _ _ _ _ σ n g e ex he y₀ hy₀
  have hsrc : ∀ b ∈ B, (a b).1 ∈ e.source := fun b hb => (hab b hb).1 ▸ e.map_target (hBt hb)
  obtain ⟨Wm, Wi, hWc, hWic, hWd⟩ :=
    ExpDirs.exists_dirs_continuousOn _ _ _ _ _ _ _ _ _ σ n g e ex he (Fin n → ℂ) B a hB ha hsrc
  have hcont : ContinuousOn (fun b => (a b).1) B :=
    (e.continuousOn_symm.mono hBt).congr fun b hb => (hab b hb).1
  have hK : ∀ τ : D.host.E →+* ℂ, ∃ c C : ℝ, 0 < c ∧ 0 ≤ C ∧ ∀ᶠ b in 𝓝 (e y₀), ∀ u : Fin (S.Dw.mult τ) → ℂ,
      c * ‖u‖ ^ 2 ≤ (star u ⬝ᵥ x.gram (a b).1 (a b).2 τ *ᵥ u).re ∧
        (star u ⬝ᵥ x.gram (a b).1 (a b).2 τ *ᵥ u).re ≤ C * ‖u‖ ^ 2 := fun τ =>
    GlobalTheory.T.posDef_uniform_bounds_near_point _ _ _ (e y₀) ((GlobalTheory.T.eigenframe_continuous_family _ _ _ _ _ _ _ _ _ x σ V φ F _ a B hcont (fun b hb => (hab b hb).2) τ).continuousAt
      (hB.mem_nhds hb₀)) (x.gram_posDef _ τ)
  choose c C hc hC hev using hK
  set A : ℝ := ∑ z, ∑ k, (‖Wm (e y₀) z k‖ + ‖Wi (e y₀) k z‖) + 1 with hA
  have hA0 : 0 ≤ A := by positivity
  have hle : ∀ z k, ‖Wm (e y₀) z k‖ + 1 ≤ A ∧ ‖Wi (e y₀) k z‖ + 1 ≤ A := fun z k => by
    have h1 : ‖Wm (e y₀) z k‖ + ‖Wi (e y₀) k z‖ ≤ ∑ z, ∑ k, (‖Wm (e y₀) z k‖ + ‖Wi (e y₀) k z‖) :=
      (Finset.single_le_sum (f := fun k => ‖Wm (e y₀) z k‖ + ‖Wi (e y₀) k z‖) (fun _ _ => by positivity)
        (Finset.mem_univ k)).trans (Finset.single_le_sum (f := fun z => ∑ k, (‖Wm (e y₀) z k‖ + ‖Wi (e y₀) k z‖))
          (fun _ _ => by positivity) (Finset.mem_univ z))
    constructor <;> linarith [norm_nonneg (Wm (e y₀) z k), norm_nonneg (Wi (e y₀) k z)]
  have hWb : ∀ᶠ b in 𝓝 (e y₀), ∀ z k, ‖Wm b z k‖ ≤ A ∧ ‖Wi b k z‖ ≤ A := by
    have c1 := hWc.continuousAt (hB.mem_nhds hb₀)
    have c2 := hWic.continuousAt (hB.mem_nhds hb₀)
    refine Filter.eventually_all.2 fun z => Filter.eventually_all.2 fun k => ?_
    have d1 : ContinuousAt (fun b => ‖Wm b z k‖) (e y₀) :=
      ((continuous_id.matrix_elem z k).continuousAt.comp c1).norm
    have d2 : ContinuousAt (fun b => ‖Wi b k z‖) (e y₀) :=
      ((continuous_id.matrix_elem k z).continuousAt.comp c2).norm
    filter_upwards [d1.eventually_lt continuousAt_const (lt_add_one ‖Wm (e y₀) z k‖),
      d2.eventually_lt continuousAt_const (lt_add_one ‖Wi (e y₀) k z‖)] with b h1 h2
    exact ⟨h1.le.trans (hle z k).1, h2.le.trans (hle z k).2⟩
  have hP : ∀ᶠ b in 𝓝 (e y₀), b ∈ B ∧ (∀ τ u, c τ * ‖u‖ ^ 2 ≤ (star u ⬝ᵥ x.gram (a b).1 (a b).2 τ *ᵥ u).re ∧
      (star u ⬝ᵥ x.gram (a b).1 (a b).2 τ *ᵥ u).re ≤ C τ * ‖u‖ ^ 2) ∧ ∀ z k, ‖Wm b z k‖ ≤ A ∧ ‖Wi b k z‖ ≤ A :=
    (hB.eventually_mem hb₀).and ((Filter.eventually_all.2 hev).and hWb)
  let T : (D.host.E →+* ℂ) → ℝ := fun τ => ((S.Dw.mult τ : ℝ) * A) ^ 2 / c τ + C τ * ((g : ℝ) * A) ^ 2
  have hT0 : ∀ τ, 0 ≤ T τ := fun τ => add_nonneg (div_nonneg (sq_nonneg _) (hc τ).le) (mul_nonneg (hC τ) (sq_nonneg _))
  have hTle : ∀ τ, T τ ≤ ∑ τ', T τ' := fun τ => Finset.single_le_sum (fun τ' _ => hT0 τ') (Finset.mem_univ τ)
  refine ⟨e.source ∩ e ⁻¹' {b | b ∈ B ∧ (∀ τ u, c τ * ‖u‖ ^ 2 ≤ (star u ⬝ᵥ x.gram (a b).1 (a b).2 τ *ᵥ u).re ∧
      (star u ⬝ᵥ x.gram (a b).1 (a b).2 τ *ᵥ u).re ≤ C τ * ‖u‖ ^ 2) ∧ ∀ z k, ‖Wm b z k‖ ≤ A ∧ ‖Wi b k z‖ ≤ A},
    Filter.inter_mem (e.open_source.mem_nhds hy₀) ((e.continuousAt hy₀).preimage_mem_nhds hP),
    ∑ τ, T τ, Finset.sum_nonneg fun τ _ => hT0 τ, ?_⟩
  rintro y ⟨hy, hbB, hbg, hbW⟩ f W hW τ v
  have hab1 : (a (e y)).1 = y := (hab _ hbB).1.trans (e.left_inv hy)
  have hinv := (hWd _ hbB).2
  obtain ⟨p, hp1, hDp, hgp⟩ : ∃ p : CxFr s.T.Z σ, y = p.1 ∧ Dirs p (fun w => (ex p.1 w).left) (Wm (e y)) ∧
      ∀ u, c τ * ‖u‖ ^ 2 ≤ (star u ⬝ᵥ x.gram p.1 p.2 τ *ᵥ u).re ∧ (star u ⬝ᵥ x.gram p.1 p.2 τ *ᵥ u).re ≤ C τ * ‖u‖ ^ 2 :=
    ⟨a (e y), hab1.symm, (hWd _ hbB).1, hbg τ⟩
  obtain ⟨y₁, F'⟩ := p
  dsimp only at hp1 hDp hgp
  subst hp1
  have e0 : ex y 0 = 1 := by simpa using he.2.2.2.1 _ hy 0 0
  obtain ⟨u, hsum, hq⟩ := GlobalTheory.T.exponential_map_origin_identity _ _ _ _ _ _ _ _ _ x σ g y (fun w => (ex y w).left) (congrArg (·.left) e0)
    (he.2.2.2.2.2 y hy).2 f F' W (Wm (e y)) (fun z => hW z) (fun z => hDp z) τ v
  rw [hsum, hq]
  set X : Fin g → ℂ := ∑ a, u a • Wm (e y) ⟨τ, a⟩ with hX
  have hX1 : ‖X‖ ≤ (S.Dw.mult τ : ℝ) * A * ‖u‖ := by
    calc ‖X‖ ≤ ∑ a, ‖u a • Wm (e y) ⟨τ, a⟩‖ := norm_sum_le _ _
      _ ≤ ∑ _a : Fin (S.Dw.mult τ), ‖u‖ * A := Finset.sum_le_sum fun a _ => by
          rw [norm_smul]
          exact mul_le_mul (norm_le_pi_norm u a) ((pi_norm_le_iff_of_nonneg hA0).2 fun k => (hbW _ k).1)
            (norm_nonneg _) (norm_nonneg _)
      _ = _ := by rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring
  have hu : ∀ a', u a' = ∑ k, X k * Wi (e y) k ⟨τ, a'⟩ := fun a' => by
    have h1 : ∀ a'', ∑ k, Wm (e y) ⟨τ, a''⟩ k * Wi (e y) k ⟨τ, a'⟩ = if a'' = a' then 1 else 0 := fun a'' => by
      have := congrFun (congrFun hinv.1 ⟨τ, a''⟩) ⟨τ, a'⟩
      rw [Matrix.mul_apply, Matrix.one_apply] at this
      rw [this]
      by_cases h : a'' = a' <;> simp [h]
    calc u a' = ∑ a'', u a'' * (if a'' = a' then 1 else 0) := by simp
      _ = ∑ a'', u a'' * ∑ k, Wm (e y) ⟨τ, a''⟩ k * Wi (e y) k ⟨τ, a'⟩ := by simp only [h1]
      _ = ∑ k, X k * Wi (e y) k ⟨τ, a'⟩ := by
          simp only [hX, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum, Finset.sum_mul]
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun a'' _ => ?_
          ring
  have hX2 : ‖u‖ ≤ (g : ℝ) * A * ‖X‖ := by
    refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun a' => ?_
    rw [hu a']
    calc ‖∑ k, X k * Wi (e y) k ⟨τ, a'⟩‖ ≤ ∑ k, ‖X k * Wi (e y) k ⟨τ, a'⟩‖ := norm_sum_le _ _
      _ ≤ ∑ _k : Fin g, ‖X‖ * A := Finset.sum_le_sum fun k _ => by
          rw [norm_mul]
          exact mul_le_mul (norm_le_pi_norm X k) (hbW _ k).2 (norm_nonneg _) (norm_nonneg _)
      _ = _ := by rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring
  obtain ⟨g1, g2⟩ := hgp u
  have hre0 : 0 ≤ (star u ⬝ᵥ x.gram y F' τ *ᵥ u).re := le_trans (by have := hc τ; positivity) g1
  constructor
  · have s1 : ‖X‖ ^ 2 ≤ ((S.Dw.mult τ : ℝ) * A) ^ 2 * ‖u‖ ^ 2 := by
      rw [← mul_pow]; exact pow_le_pow_left₀ (norm_nonneg _) hX1 2
    have s2 : ‖u‖ ^ 2 ≤ (star u ⬝ᵥ x.gram y F' τ *ᵥ u).re / c τ := (le_div_iff₀ (hc τ)).2 (by linarith)
    calc ‖X‖ ^ 2 ≤ ((S.Dw.mult τ : ℝ) * A) ^ 2 * ((star u ⬝ᵥ x.gram y F' τ *ᵥ u).re / c τ) :=
          s1.trans (mul_le_mul_of_nonneg_left s2 (sq_nonneg _))
      _ = ((S.Dw.mult τ : ℝ) * A) ^ 2 / c τ * (star u ⬝ᵥ x.gram y F' τ *ᵥ u).re := by ring
      _ ≤ T τ * (star u ⬝ᵥ x.gram y F' τ *ᵥ u).re :=
          mul_le_mul_of_nonneg_right (le_add_of_nonneg_right (mul_nonneg (hC τ) (sq_nonneg _))) hre0
      _ ≤ (∑ τ', T τ') * (star u ⬝ᵥ x.gram y F' τ *ᵥ u).re := mul_le_mul_of_nonneg_right (hTle τ) hre0
  · have s1 : ‖u‖ ^ 2 ≤ ((g : ℝ) * A) ^ 2 * ‖X‖ ^ 2 := by
      rw [← mul_pow]; exact pow_le_pow_left₀ (norm_nonneg _) hX2 2
    calc (star u ⬝ᵥ x.gram y F' τ *ᵥ u).re ≤ C τ * (((g : ℝ) * A) ^ 2 * ‖X‖ ^ 2) :=
          g2.trans (mul_le_mul_of_nonneg_left s1 (hC τ))
      _ = C τ * ((g : ℝ) * A) ^ 2 * ‖X‖ ^ 2 := by ring
      _ ≤ T τ * ‖X‖ ^ 2 := mul_le_mul_of_nonneg_right (le_add_of_nonneg_left (div_nonneg (sq_nonneg _) (hc τ).le))
          (sq_nonneg _)
      _ ≤ (∑ τ', T τ') * ‖X‖ ^ 2 := mul_le_mul_of_nonneg_right (hTle τ) (sq_nonneg _)

end GlobalTheory.ExpChartMetric
