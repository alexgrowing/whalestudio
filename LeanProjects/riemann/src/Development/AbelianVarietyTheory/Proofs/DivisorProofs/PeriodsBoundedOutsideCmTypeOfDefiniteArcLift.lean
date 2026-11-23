import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MonoSpMapRingOfIntegersAlt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsArcLiftPeriodsTendstoSpan
open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ShFam GlobalTheory.ShFam.BdArc Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (Data Frame Bor rmul lact mat col dmin Wt)

namespace GlobalTheory.ShFam.PerLim

theorem tendsto_of_inv_mulVec_span {α : Type} {l : Filter α} {N n : ℕ} (M : α → Matrix (Fin N) (Fin N) ℂ)
    (u : Fin n → Fin N → ℂ) (L : Fin n → Fin N → ℂ) (hdet : ∀ᶠ w in l, (M w).det ≠ 0)
    (ht : ∀ j, Tendsto (fun w => Matrix.mulVec (M w)⁻¹ (u j)) l (𝓝 (L j)))
    (hs : Submodule.span ℂ (Set.range L) = ⊤) : ∃ L0, Tendsto M l (𝓝 L0) := by
  have hc : ∀ a : Fin N, ∃ c : Fin n → ℂ, ∑ j, c j • L j = Pi.single a 1 := fun a =>
    (Submodule.mem_span_range_iff_exists_fun ℂ).1 (hs ▸ Submodule.mem_top)
  choose c hc using hc
  let W : Matrix (Fin N) (Fin N) ℂ := Matrix.of fun b a => ∑ j, c a j * u j b
  have hR : Tendsto (fun w => (M w)⁻¹ * W) l (𝓝 1) := by
    refine tendsto_pi_nhds.2 fun a' => tendsto_pi_nhds.2 fun a => ?_
    have e : ∀ w, ((M w)⁻¹ * W) a' a = ∑ j, c a j * (Matrix.mulVec (M w)⁻¹ (u j)) a' := by
      intro w
      simp only [Matrix.mul_apply, Matrix.mulVec, dotProduct, W, Matrix.of_apply, Finset.mul_sum]
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun b _ => by ring
    have lim : (1 : Matrix (Fin N) (Fin N) ℂ) a' a = ∑ j, c a j * L j a' := by
      have := congrFun (hc a) a'
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at this
      rw [this, Pi.single_apply, Matrix.one_apply]
    simp only [e]
    rw [lim]
    exact tendsto_finset_sum _ fun j _ => ((ht j).apply_nhds a').const_mul _
  have hRi : Tendsto (fun w => ((M w)⁻¹ * W)⁻¹) l (𝓝 1) := by
    have h0 : ContinuousAt Ring.inverse (1 : Matrix (Fin N) (Fin N) ℂ).det := by
      rw [Matrix.det_one, Ring.inverse_eq_inv']
      exact continuousAt_inv₀ one_ne_zero
    have h1 := ((continuousAt_matrix_inv (1 : Matrix (Fin N) (Fin N) ℂ) h0).tendsto).comp hR
    rw [inv_one] at h1
    exact h1
  have hRd : ∀ᶠ w in l, ((M w)⁻¹ * W).det ≠ 0 := by
    have h1 : Tendsto (fun w => ((M w)⁻¹ * W).det) l (𝓝 (1 : Matrix (Fin N) (Fin N) ℂ).det) :=
      ((Continuous.matrix_det continuous_id).tendsto (1 : Matrix (Fin N) (Fin N) ℂ)).comp hR
    rw [Matrix.det_one] at h1
    exact h1.eventually_ne one_ne_zero
  refine ⟨W, ?_⟩
  have hlim : Tendsto (fun w => W * ((M w)⁻¹ * W)⁻¹) l (𝓝 (W * 1)) :=
    ((continuous_const.matrix_mul continuous_id).tendsto _).comp hRi
  rw [Matrix.mul_one] at hlim
  refine hlim.congr' ?_
  filter_upwards [hdet, hRd] with w h1 h2
  have e1 : M w * ((M w)⁻¹ * W) = W := by
    rw [← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.2 h1), Matrix.one_mul]
  calc W * ((M w)⁻¹ * W)⁻¹ = M w * ((M w)⁻¹ * W) * ((M w)⁻¹ * W)⁻¹ := by rw [e1]
    _ = M w := by rw [Matrix.mul_assoc, Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.2 h2), Matrix.mul_one]

theorem periods_bounded_outside_cmType_of_definite_arc_lift_alt : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Z : Model Xo c β) (σ : c.F →+* ℂ) (N : ℕ) (U : Unf Xo c σ N) (A : Type) [CommRing A] (φ : c.F →+* A) (x : Sp A ⟶ gen Z) (fr : EigFrame Z φ (x ≫ genι Z)) (ψ : ℂ → (A →+* ℂ)) (r : ℝ) (y : ℂ → FrPt Xo c (CAt σ)) (k : U.Comp) (T : ℝ) (M : ℕ) (γ : GL (Fin N) E) (xx : ℂ → Frame (U.X k).Ψ N), GoodEmb c σ → IsUnf U → IsArc Z σ φ x ψ r → (∀ u ∈ Metric.ball (0 : ℂ) r, u ≠ 0 → Matches fr (ψ u) (y u)) → IsOrbit (U.X k) T M γ xx → IsLift U k y T xx → (U.X k).p0 = 0 → ∀ v : Fin N → E, ∃ C : ℝ, ∀ᶠ w in imTop, ∀ (τ : E →+* ℂ) (i : ℕ), τ ∉ (U.X k).Ψ → ‖perFr (U.X k) (xx w) v τ i‖ ≤ C := by
  intro E _ _ _ H Dw l Xo c O _ β Z σ N U A _ φ x fr ψ r y k T M γ xx hσ hU harc hm horb hlift hp0 v
  obtain ⟨n, vv, Lp, Lm, hLp, -, hsp⟩ := GlobalTheory.ShFam.PerLim.exists_periods_tendsto_span E H Dw l Xo c O β Z σ N U A φ x
    fr ψ r y k T M γ xx hσ hU harc hm horb hlift
  have hdom : ∀ᶠ w in imTop, xx w ∈ (U.X k).dom := by
    filter_upwards [(tendsto_comap (f := Complex.im) (x := atTop)).eventually (eventually_gt_atTop T)] with w hw
    exact horb.2.2.2.1 w hw
  have hmat : ∀ τ' : (U.X k).Ψ, ∃ L0, Tendsto (fun w => mat (xx w) τ') imTop (𝓝 L0) := by
    intro τ'
    refine tendsto_of_inv_mulVec_span (fun w => mat (xx w) τ') (fun j => ReciprocityTheory.ChartRestriction.G.FD.Data.emb τ'.1 (vv j))
      (fun j i => Lp j τ' ⟨i, by omega⟩) ?_ ?_ ?_
    · filter_upwards [hdom] with w hw
      exact (hw τ').1
    · intro j
      refine tendsto_pi_nhds.2 fun i => ?_
      have hi : (i : ℕ) < N - (U.X k).p0 := by omega
      refine (hLp j τ' ⟨i, hi⟩).congr fun w => ?_
      unfold perFr
      rw [dif_pos τ'.2, dif_pos (by simp only [hp0]; omega)]
      congr 1
      ext
      simp [hp0]
    · exact span_proj (fun j => Lp j τ') (hsp τ').1 (fun i => ⟨i, by omega⟩)
        (fun a b h => Fin.ext (by simpa using congrArg Fin.val h))
  choose L0 hL0 using hmat
  let F : ℂ → ((U.X k).Ψ → Fin N → ℂ) := fun w τ' a =>
    ReciprocityTheory.ChartRestriction.G.FD.hermC τ'.1 (U.X k).Gm (col (mat (xx w) τ') a) (ReciprocityTheory.ChartRestriction.G.FD.Data.emb τ'.1 v)
  have hF : Tendsto F imTop (𝓝 (fun τ' a =>
      ReciprocityTheory.ChartRestriction.G.FD.hermC τ'.1 (U.X k).Gm (col (L0 τ') a) (ReciprocityTheory.ChartRestriction.G.FD.Data.emb τ'.1 v))) := by
    refine tendsto_pi_nhds.2 fun τ' => tendsto_pi_nhds.2 fun a => ?_
    have hc : Continuous fun Mx : Matrix (Fin N) (Fin N) ℂ =>
        ReciprocityTheory.ChartRestriction.G.FD.hermC τ'.1 (U.X k).Gm (col Mx a) (ReciprocityTheory.ChartRestriction.G.FD.Data.emb τ'.1 v) := by
      unfold ReciprocityTheory.ChartRestriction.G.FD.hermC col
      fun_prop
    exact (hc.tendsto _).comp (hL0 τ')
  refine ⟨‖(fun τ' a =>
      ReciprocityTheory.ChartRestriction.G.FD.hermC τ'.1 (U.X k).Gm (col (L0 τ') a) (ReciprocityTheory.ChartRestriction.G.FD.Data.emb τ'.1 v) :
      (U.X k).Ψ → Fin N → ℂ)‖ + 1, ?_⟩
  filter_upwards [hF.norm.eventually (gt_mem_nhds (lt_add_one _))] with w hw
  intro τ i hτ
  unfold perFr
  rw [dif_neg hτ]
  split_ifs with h' hj
  · exact ((norm_le_pi_norm (F w ⟨_, h'⟩) ⟨_, hj⟩).trans (norm_le_pi_norm (F w) ⟨_, h'⟩)).trans hw.le
  · simp only [norm_zero]; positivity
  · simp only [norm_zero]; positivity

end GlobalTheory.ShFam.PerLim
