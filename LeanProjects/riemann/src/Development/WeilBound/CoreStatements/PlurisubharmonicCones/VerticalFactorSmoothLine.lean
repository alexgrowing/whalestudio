import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.PotentialsBoundedRegSettingEqReference
import GroundTheory.HeightsAndTheta.Heights.Regularisation.BoundedStatements
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterSt
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.PHermExtend
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.PVertFactorPos
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.PVertFactorSmooth
import Development.WeilBound.CoreStatements.PlurisubharmonicCones.ContDiffAtSmoothOnProj
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp
open ReciprocityTheory.AnForm (levi)

namespace LevelTowerAlt

section

variable {K : Type} [Fintype K] {J : K → Type} [∀ k, Fintype (J k)]

theorem eval_conjVec (z : (Σ k, J k) → ℂ) (f : MRing J) :
    MvPolynomial.eval (conjVec z) (MvPolynomial.map (Int.castRingHom ℂ) f) =
      starRingEnd ℂ (MvPolynomial.eval z (MvPolynomial.map (Int.castRingHom ℂ) f)) := by
  induction f using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp [hp, hq]
  | mul_X p i hp => simp [hp, conjVec]

theorem contDiff_conjVec : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun z : (Σ k, J k) → ℂ => conjVec z) :=
  contDiff_pi.2 fun i => Complex.conjCLE.contDiff.comp (contDiff_apply ℝ ℂ i)

theorem conjVec_ne {z : (Σ k, J k) → ℂ} (hz : ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) : ∀ k, ∃ i, conjVec z ⟨k, i⟩ ≠ 0 :=
  fun k => (hz k).imp fun _ hi => (map_ne_zero _).2 hi

noncomputable def symmLine (Z : HermLine J) : HermLine J where
  a := Z.a
  h z := Real.sqrt (Z.h z * Z.h (conjVec z))
  pos z hz := Real.sqrt_pos.2 (mul_pos (Z.pos z hz) (Z.pos _ (conjVec_ne hz)))
  smul c z hc := by
    have h1 : conjVec (fun p : Σ k, J k => c p.1 * z p) =
        fun p : Σ k, J k => (fun k => starRingEnd ℂ (c k)) p.1 * conjVec z p := by
      funext p
      simp [conjVec]
    have h2 := Z.smul (fun k => starRingEnd ℂ (c k)) (conjVec z) fun k => (map_ne_zero _).2 (hc k)
    have hP := prod_norm_zpow_pos hc Z.a
    rw [h1, h2, Z.smul c z hc]
    simp only [Complex.norm_conj]
    rw [_root_.mul_mul_mul_comm, Real.sqrt_mul (mul_self_nonneg _), Real.sqrt_mul_self hP.le]

theorem symmLine_smooth {Z : HermLine J} (hZ : IsSmoothHerm Z) : IsSmoothHerm (symmLine Z) :=
  ContDiffOn.sqrt (ContDiffOn.mul hZ (ContDiffOn.comp hZ contDiff_conjVec.contDiffOn fun _ hz => conjVec_ne hz))
    fun z hz => (mul_pos (Z.pos z hz) (Z.pos _ (conjVec_ne hz))).ne'

theorem symmLine_conj (Z : HermLine J) : IsConjInvariantH (symmLine Z) := by
  intro z
  show Real.sqrt (Z.h (conjVec z) * Z.h (conjVec (conjVec z))) = Real.sqrt (Z.h z * Z.h (conjVec z))
  rw [SncPiece.conj_conj, mul_comm]

end

theorem vertical_factor_smooth_line : ∀ (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (II : IntersectionSystem) (Ψ : Type) [Fintype Ψ] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (W : Ψ → Type) [∀ τ, AddCommGroup (W τ)] [∀ τ, Module Ω (W τ)] (D : ComponentData II Ψ K J Ω W), ∀ p ∈ D.S, (∃ A : HermLine J, A.a = D.vdeg p ∧ IsSmoothHerm A ∧ IsConjInvariantH A ∧ ∀ z ∈ mcPts (mCoordIdeal D.y), A.h z = D.vertFactor p z) ∧ ∀ a, ∀ t ∈ Metric.ball (0 : Fin (Fintype.card Ψ * D.j * (D.N - D.j)) → ℂ) 1, ∃ G : (Fin (Fintype.card Ψ * D.j * (D.N - D.j)) → ℂ) → ℂ, AnalyticAt ℂ G t ∧ ∀ᶠ t' in 𝓝 t, Real.log (D.vertFactor p ((D.chart a).γ t')) = (G t').re := by
  intro K _ J _ II Ψ _ Ω _ _ W _ _ D p hp
  have hpos := VertFactorPos.proof II Ψ K J Ω W D p hp
  have hsm := VertFactorSmooth.proof VertFactorPos.proof II Ψ K J Ω W D p hp
  constructor
  · obtain ⟨Z, hZa, hZs, hZ⟩ := HermExtend.proof K J (mCoordIdeal D.y) (D.vdeg p) (D.vertFactor p) D.arith.2.1.2.1
      hpos hsm.1 hsm.2
    refine ⟨symmLine Z, hZa, symmLine_smooth hZs, symmLine_conj Z, fun z hz => ?_⟩
    have hconj : D.vertFactor p (conjVec z) = D.vertFactor p z := by
      obtain ⟨dG, dH, G, H, hG, hH, hdeg, hrel, hHz⟩ := VertFactorSmooth.exists_forms D hp hz
      rw [VertFactorSmooth.vertFactor_eq D hp (SncPiece.conj_mem hz) hG hH hdeg hrel
          (by rw [eval_conjVec]; exact (map_ne_zero _).2 hHz),
        VertFactorSmooth.vertFactor_eq D hp hz hG hH hdeg hrel hHz, eval_conjVec, eval_conjVec, ← map_div₀,
        Complex.norm_conj]
    show Real.sqrt (Z.h z * Z.h (conjVec z)) = _
    rw [hZ z hz, hZ _ (SncPiece.conj_mem hz), hconj, Real.sqrt_mul_self (hpos z hz).le]
  · intro a t ht
    have hz := (D.chart a).mem t ht
    obtain ⟨dG, dH, G, H, hG, hH, hdeg, hrel, hHz⟩ := VertFactorSmooth.exists_forms D hp hz
    have hγ := (D.chart a).analytic t ht
    have hev : ∀ f : MRing J, AnalyticAt ℂ
        (fun t' => MvPolynomial.eval ((D.chart a).γ t') (MvPolynomial.map (Int.castRingHom ℂ) f)) t := fun f =>
      AnalyticAt.comp (g := fun z => MvPolynomial.eval z (MvPolynomial.map (Int.castRingHom ℂ) f))
        (AnalyticOnNhd.eval_mvPolynomial _ _ (Set.mem_univ _)) hγ
    have h0 := hpos _ hz
    rw [VertFactorSmooth.vertFactor_eq D hp hz hG hH hdeg hrel hHz] at h0
    obtain ⟨L, hL, hLe⟩ := exists_log_re ((hev G).div (hev H) hHz) (norm_pos_iff.1 h0)
    refine ⟨L, hL, ?_⟩
    filter_upwards [hLe, (hev H).continuousAt.eventually_ne hHz, Metric.isOpen_ball.mem_nhds ht] with t' h1 h2 h3
    rw [VertFactorSmooth.vertFactor_eq D hp ((D.chart a).mem t' h3) hG hH hdeg hrel h2]
    exact h1

end LevelTowerAlt
