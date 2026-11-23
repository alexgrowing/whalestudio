import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.CayleyCosetSums.CurveGR
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.ContinuousSecondCayleyBlockMapBis
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.RowsBlocks
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.NormDetFirstBlockCompact
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.RightConn

noncomputable section

open MeasureTheory Matrix Set Filter Topology
open scoped NNReal

namespace PositivityTheory.Rg.Sw.HSt.FarP

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LVs PositivityTheory.Rg.Sw.AbsSt PositivityTheory.Rg.Sw.HSt

variable {m n : ℕ} {e : ℤ} {G : Type} [Group G] [TopologicalSpace G]
  {Pp Γ : Subgroup G} {ι : GR n →* G} {s₀ : ℂ} {Ht : G → ℝ≥0} {f : G → ℂ} {U : Set ℂ} {d : Polynomial ℂ}
  {Ê : ℂ → G → ℂ} {t : ℝ}

def trm (Ht : G → ℝ≥0) (f : G → ℂ) (s₀ z : ℂ) (x : G) : ℂ := ((Ht x : ℝ) : ℂ) ^ (z - s₀) * f x

theorem lift_mR (φ : GR n → ℂ) (y : GR n) : lift φ (mR y) = φ y := by
  unfold lift
  have h : IsUnit (mR y) ∧ InG (mR y) := ⟨y.1.isUnit, y.2⟩
  rw [dif_pos h]
  congr 1
  apply Subtype.ext
  apply Units.ext
  simp [mR]

theorem resG_mR (F : G → ℂ) (g : G) (y : GR n) : resG ι F g (mR y) = F (g * ι y) := lift_mR _ _

theorem termSplit (hS : SecFz) (h : HD m n e G Pp Γ ι s₀ Ht f U d Ê t) (z : ℂ) (x : G) :
    ∃ (y₀ : GR n) (C : ℂ), ∀ y : GR n, trm Ht f s₀ z (x * ι y) = C * fz m e (z - s₀) (mR (y₀ * y)) := by
  obtain ⟨x₀, y₀, S, r, hr, hx, hh⟩ := h.split x
  refine ⟨y₀, ((r : ℝ) : ℂ) ^ (z - s₀) * S, fun y => ?_⟩
  have hxy : x * ι y = x₀ * ι (y₀ * y) := by rw [hx, mul_assoc, ← map_mul]
  unfold trm
  rw [hxy, (hh _).1, (hh _).2, hS n m e (z - s₀) (y₀ * y), Complex.ofReal_mul,
    Complex.mul_cpow_ofReal_nonneg hr.le (Vac.hLoc_nonneg _)]
  ring

theorem fz_mul_k (hS : SecFz) (w : ℂ) (y k : GR n) (hk : k ∈ KR n) :
    fz m e w (mR (y * k)) = fz m e w (mR y) * F0 m 0 e k := by
  obtain ⟨h1, h2⟩ := (mult n m 0 e).1 y k hk
  rw [hS n m e w (y * k), hS n m e w y, h1, h2]
  ring

theorem cosetSum_apply (Φ : G → ℂ) (x : G) :
    GlobalTheory.Eis.cosetSum Pp Γ Φ x = ∑' q : GlobalTheory.Eis.Cosets Pp Γ, Φ (((q.out : Γ) : G) * x) := rfl

theorem klaw (hS : SecFz) (h : HD m n e G Pp Γ ι s₀ Ht f U d Ê t) :
    ∀ z ∈ U, ∀ (g : G) (y k : GR n), k ∈ KR n → Ê z (g * ι (y * k)) = Ê z (g * ι y) * F0 m 0 e k := by
  intro z hz g y k hk
  have hfar : ∀ z' : ℂ, t < z'.re → Ê z' (g * ι (y * k)) = Ê z' (g * ι y) * F0 m 0 e k := by
    intro z' hz'
    rw [(h.far z' hz').2, (h.far z' hz').2, cosetSum_apply, cosetSum_apply, mul_assoc, ← tsum_mul_right]
    congr 1
    refine tsum_congr fun q => ?_
    obtain ⟨y₀, C, hC⟩ := termSplit hS h z' (((q.out : Γ) : G) * g)
    have e1 : ((q.out : Γ) : G) * (g * ι (y * k)) = ((q.out : Γ) : G) * g * ι (y * k) := by rw [mul_assoc]
    have e2 : ((q.out : Γ) : G) * (g * ι y) = ((q.out : Γ) : G) * g * ι y := by rw [mul_assoc]
    change trm Ht f s₀ z' _ = trm Ht f s₀ z' _ * _
    rw [e1, e2, hC, hC, ← mul_assoc y₀ y k, fz_mul_k hS _ _ _ hk]
    ring
  obtain ⟨σ, hσ⟩ := h.hR.1
  have hpre : IsPreconnected U := rightConn U h.hU h.hR
  have hA1 : AnalyticOnNhd ℂ (fun z => Ê z (g * ι (y * k))) U := (h.hol _).analyticOnNhd h.hU
  have hA2 : AnalyticOnNhd ℂ (fun z => Ê z (g * ι y) * F0 m 0 e k) U :=
    ((h.hol _).mul_const _).analyticOnNhd h.hU
  set z₀ : ℂ := ((max σ t + 1 : ℝ) : ℂ)
  have hz₀ : z₀ ∈ U := hσ (by simp [z₀, GlobalTheory.Cont.rightOf]; linarith [le_max_left σ t])
  have hev : (fun z => Ê z (g * ι (y * k))) =ᶠ[𝓝 z₀] fun z => Ê z (g * ι y) * F0 m 0 e k := by
    have ho : IsOpen {z : ℂ | t < z.re} := isOpen_lt continuous_const Complex.continuous_re
    have hm : z₀ ∈ {z : ℂ | t < z.re} := by simp [z₀]; linarith [le_max_right σ t]
    filter_upwards [ho.mem_nhds hm] with z hz using hfar z hz
  exact hA1.eqOn_of_preconnected_of_eventuallyEq hA2 hpre hz₀ hev hz

end PositivityTheory.Rg.Sw.HSt.FarP
