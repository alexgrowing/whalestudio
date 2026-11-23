import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SobolevPointwiseBound
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RwAppend
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ChartAndRightWordsSmooth

open MeasureTheory Matrix Finset Filter Topology
open scoped ContDiff ComplexConjugate InnerProductSpace ZeroAtInfty
open PositivityTheory.RgTw (Mat G)
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Fc GlobalTheory.CompanionTheory.PresSobA
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
noncomputable section

namespace GlobalTheory.CompanionTheory.PresSobA.RwCauchy

theorem val_mem_GLs {n : ℕ} (y : G n) : y.val ∈ GLs n :=
  (Matrix.isUnits_det_units y).ne_zero

theorem Rw_sub_on {n : ℕ} {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] {a b : Mat n → V}
    (ha : ContDiffOn ℝ ∞ a (GLs n)) (hb : ContDiffOn ℝ ∞ b (GLs n))
    (w : List (Bool × Fin n × Fin n)) :
    ∀ z ∈ GLs n, Rw w (a - b) z = Rw w a z - Rw w b z := by
  induction w with
  | nil => intro z _; rfl
  | cons p w ih =>
    intro z hz
    have h1 : Rw (p :: w) (a - b) z = Rd (bs p) (Rw w a - Rw w b) z :=
      Rd_congr (f := Rw w (a - b)) (f' := Rw w a - Rw w b) (fun y hy => ih y hy) (bs p) z hz
    rw [h1]
    have hU := isOpen_GLs.mem_nhds hz
    have da : DifferentiableAt ℝ (Rw w a) z :=
      ((GlobalTheory.CompanionTheory.SobGL.Smooth.Rw_contDiffOn' ha w).contDiffAt hU).differentiableAt (by simp)
    have db : DifferentiableAt ℝ (Rw w b) z :=
      ((GlobalTheory.CompanionTheory.SobGL.Smooth.Rw_contDiffOn' hb w).contDiffAt hU).differentiableAt (by simp)
    show fderiv ℝ (Rw w a - Rw w b) z (z * bs p) =
      fderiv ℝ (Rw w a) z (z * bs p) - fderiv ℝ (Rw w b) z (z * bs p)
    have e := (da.hasFDerivAt.sub db.hasFDerivAt).fderiv
    exact DFunLike.congr_fun e (z * bs p)

theorem uniformCauchy : SobG → ∀ (n : ℕ) [MeasurableSpace (G n)] [BorelSpace (G n)] (μ : Measure (G n)) [μ.IsHaarMeasure] (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V] (g : ℕ → Mat n → V) (x : List (Bool × Fin n × Fin n) → Lp V 2 μ), (∀ k, ContDiffOn ℝ ∞ (g k) (GLs n)) → (∀ k w, MemLp (fun y : G n => Rw w (g k) y.val) 2 μ) → (∀ w, Tendsto (fun k => cls μ (Rw w (g k))) atTop (𝓝 (x w))) → ∀ w, UniformCauchySeqOn (fun k => Rw w (g k)) atTop (GLs n) := by
  intro hS n _ _ μ _ V _ _ _ g x hg hm hc w
  obtain ⟨S, C, hC, hsup⟩ := GlobalTheory.CompanionTheory.PresSobA.SupG.sup_sq_bound hS n μ
  have hbound : ∀ k l, ∀ z ∈ GLs n, ‖Rw w (g k) z - Rw w (g l) z‖ ^ 2 ≤
      C * ∑ w' ∈ S, ‖cls μ (Rw (w' ++ w) (g k)) - cls μ (Rw (w' ++ w) (g l))‖ ^ 2 := by
    intro k l z hz
    have sk := GlobalTheory.CompanionTheory.SobGL.Smooth.Rw_contDiffOn' (hg k) w
    have sl := GlobalTheory.CompanionTheory.SobGL.Smooth.Rw_contDiffOn' (hg l) w
    have key : ∀ w', ∀ y ∈ GLs n, Rw w' (Rw w (g k) - Rw w (g l)) y =
        Rw (w' ++ w) (g k) y - Rw (w' ++ w) (g l) y := by
      intro w' y hy
      rw [Rw_sub_on sk sl w' y hy, Rw_append, Rw_append]
    have hcl : ∀ w', MemLp (fun y : G n => Rw w' (Rw w (g k) - Rw w (g l)) y.val) 2 μ ∧
        cls μ (Rw w' (Rw w (g k) - Rw w (g l))) =
          cls μ (Rw (w' ++ w) (g k)) - cls μ (Rw (w' ++ w) (g l)) := by
      intro w'
      refine cls_of_ae μ ?_
      filter_upwards [Lp.coeFn_sub (cls μ (Rw (w' ++ w) (g k))) (cls μ (Rw (w' ++ w) (g l))),
        coe_cls μ (hm k (w' ++ w)), coe_cls μ (hm l (w' ++ w))] with y h1 h2 h3
      rw [h1, Pi.sub_apply, h2, h3, key w' _ (val_mem_GLs y)]
    have := hsup V (Rw w (g k) - Rw w (g l)) (sk.sub sl) (fun w' => (hcl w').1) z hz
    simp only [hcl] at this
    exact this
  rw [Metric.uniformCauchySeqOn_iff]
  intro ε hε
  have hT : Tendsto (fun p : ℕ × ℕ =>
      C * ∑ w' ∈ S, ‖cls μ (Rw (w' ++ w) (g p.1)) - cls μ (Rw (w' ++ w) (g p.2))‖ ^ 2)
      (atTop ×ˢ atTop) (𝓝 0) := by
    have h0 : Tendsto (fun p : ℕ × ℕ =>
        C * ∑ w' ∈ S, ‖cls μ (Rw (w' ++ w) (g p.1)) - cls μ (Rw (w' ++ w) (g p.2))‖ ^ 2)
        (atTop ×ˢ atTop) (𝓝 (C * ∑ w' ∈ S, ‖x (w' ++ w) - x (w' ++ w)‖ ^ 2)) := by
      refine Tendsto.const_mul _ (tendsto_finsetSum _ fun w' _ => ?_)
      exact ((((hc _).comp tendsto_fst).sub ((hc _).comp tendsto_snd)).norm).pow 2
    simpa using h0
  have hev := hT.eventually (gt_mem_nhds (pow_pos hε 2))
  rw [prod_atTop_atTop_eq] at hev
  obtain ⟨N, hN⟩ := eventually_atTop_prod_self'.1 hev
  refine ⟨N, fun k hk l hl z hz => ?_⟩
  rw [dist_eq_norm]
  exact lt_of_pow_lt_pow_left₀ 2 hε.le ((hbound k l z hz).trans_lt (hN k hk l hl))

end GlobalTheory.CompanionTheory.PresSobA.RwCauchy
