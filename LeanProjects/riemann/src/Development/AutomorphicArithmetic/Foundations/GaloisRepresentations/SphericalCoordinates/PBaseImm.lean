import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.DetOfCharpoly
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCountableCharts

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.PELU Filter Topology
open scoped Matrix
open GlobalTheory.HodgeCoh GlobalTheory.CechDR Polynomial UpperTheory.Gal.W2

namespace UpperTheory.Gal.W2

private theorem chart_at {X : Scheme.{0}} (s : X ⟶ Sp ℂ) (d : ℕ) [SmoothOfRelativeDimension d s]
    (x : GlobalTheory.CxPts s (RingHom.id ℂ)) :
    ∃ (T : Set (Fin d → ℂ)) (y : (Fin d → ℂ) → (Sp ℂ ⟶ X)) (U : X.Opens) (xs : Fin d → Γ(X, U)) (b₀ : Fin d → ℂ),
      IsOpen T ∧ b₀ ∈ T ∧ IsHolTo T y ∧ (∀ b ∈ T, y b ≫ s = spMap (RingHom.id ℂ)) ∧ y b₀ = x.1 ∧
      ⊤ ≤ x.1 ⁻¹ᵁ U ∧ ∀ b ∈ T, ∀ l, valAt' (y b) U (xs l) = b l := by
  obtain ⟨c, hc⟩ : ∃ c : GlobalTheory.AlgChart s (RingHom.id ℂ) d, x ∈ c.e.source :=
    GlobalTheory.AlgChart.exists_mem_source x
  refine ⟨c.finChart.target, fun z => (c.finChart.symm z).1, c.U, c.x, c.finChart x,
    c.finChart.open_target, c.finChart.map_source hc, GlobalTheory.CountableCharts.isHolTo_finChart_symm c,
    fun b _ => (c.finChart.symm b).2, ?_, c.source_subset hc, ?_⟩
  · show (c.finChart.symm (c.finChart x)).1 = x.1
    rw [c.finChart.left_inv hc]
  · intro b hb l
    have hs : c.finChart.symm b ∈ c.e.source := c.finChart.map_target hb
    have := c.finChart_eq_ev hs l
    rw [c.finChart.right_inv hb] at this
    exact this.symm

end UpperTheory.Gal.W2

namespace UpperTheory.Gal.W2

private theorem inj_of_leftInv {d : ℕ} (τ cc : (Fin d → ℂ) → (Fin d → ℂ)) (b₀ : Fin d → ℂ)
    (hτ : DifferentiableAt ℂ τ (cc b₀)) (hcc : DifferentiableAt ℂ cc b₀)
    (h : ∀ᶠ b in 𝓝 b₀, τ (cc b) = b) : Function.Injective (fderiv ℂ τ (cc b₀)) := by
  have hcomp : fderiv ℂ (τ ∘ cc) b₀ = (fderiv ℂ τ (cc b₀)).comp (fderiv ℂ cc b₀) :=
    fderiv_comp b₀ hτ hcc
  have heq : τ ∘ cc =ᶠ[𝓝 b₀] id := h
  have hid : fderiv ℂ (τ ∘ cc) b₀ = ContinuousLinearMap.id ℂ (Fin d → ℂ) := by
    rw [heq.fderiv_eq, fderiv_id]
  have hsurj : Function.Surjective (fderiv ℂ τ (cc b₀)) := by
    intro v
    refine ⟨fderiv ℂ cc b₀ v, ?_⟩
    have := congrArg (fun L : (Fin d → ℂ) →L[ℂ] (Fin d → ℂ) => L v) (hcomp.symm.trans hid)
    simpa using this
  have := LinearMap.injective_iff_surjective (f := (fderiv ℂ τ (cc b₀) : (Fin d → ℂ) →ₗ[ℂ] (Fin d → ℂ)))
  exact this.mpr hsurj

end UpperTheory.Gal.W2

theorem UpperTheory.Gal.W2.baseImm_of :
    UpperTheory.Gal.W2.PerNear → UpperTheory.Gal.W2.PerCoordLoc → UpperTheory.Gal.W2.BaseImm := by
  intro hNear hLoc O _ bar g ρ D X s A _ S d hsm P₀ M₀ hP hH co hco w hw
  haveI := hsm
  set pt : (Fin d → ℂ) → (Sp ℂ ⟶ X) := fun b => S.u (perC P₀ (co b)) with hpt
  have hmemC : ∀ b, co b ∈ Csp bar ρ M₀ := fun b => by
    rw [← hco.2]
    exact LinearMap.mem_range_self co b
  obtain ⟨B, hBo, hB0, hBhol⟩ := hNear O bar g ρ D P₀ M₀ hP hH d co hmemC
  have hpthol : IsHolTo B pt := (S.hol d B _ hBo hBhol).1
  have hpt0 : pt 0 = S.u P₀ := by
    show S.u (perC P₀ (co 0)) = S.u P₀
    rw [map_zero, perC_zero]
  obtain ⟨T, y, U, xs, b₀, hTo, hb₀, hyhol, hyov, hyb₀, hU, hxs⟩ :=
    chart_at s d ⟨S.u P₀, S.ov P₀ hP⟩
  obtain ⟨B', P, hB'o, hb₀B', hB'T, hPhol, hPb₀, hPu⟩ :=
    S.lift d T y hTo hyov hyhol b₀ hb₀ P₀ hP hyb₀
  obtain ⟨c, hcd, hc0, hcev⟩ :=
    hLoc O bar g ρ D P₀ M₀ hP hH d co hco d B' P b₀ hB'o hb₀B' hPhol hPb₀
  have hUpt0 : ⊤ ≤ pt 0 ⁻¹ᵁ U := by
    rw [hpt0]
    exact hU
  have hcompdiff : ∀ l, DifferentiableAt ℂ (fun b => valAt' (pt b) U (xs l)) 0 := fun l =>
    ((hpthol U (xs l)).2 0 ⟨hB0, hUpt0⟩).differentiableAt
      ((hpthol U (xs l)).1.mem_nhds ⟨hB0, hUpt0⟩)
  have hτd : DifferentiableAt ℂ (fun b l => valAt' (pt b) U (xs l)) 0 :=
    differentiableAt_pi.mpr hcompdiff
  have hcB : ∀ᶠ b in 𝓝 b₀, c b ∈ B :=
    hcd.continuousAt.preimage_mem_nhds (by rw [hc0]; exact hBo.mem_nhds hB0)
  have hleft : ∀ᶠ b in 𝓝 b₀, (fun b l => valAt' (pt b) U (xs l)) (c b) = b := by
    filter_upwards [hcev, hcB, hB'o.mem_nhds hb₀B'] with b hb hbB hbB'
    obtain ⟨h, hh⟩ := hb
    have hPer1 : GlobalTheory.PELU.IsPeriod D ρ (P b) := hPhol.1 b hbB'
    have hPer2 : GlobalTheory.PELU.IsPeriod D ρ (perC P₀ (co (c b))) := hBhol.1 (c b) hbB
    have hu : S.u (P b) = pt (c b) := by
      have hl := S.lin _ _ h hPer2 hPer1 hh 0
      have w1 : (S.ex (P b) (h 0)).left ≫ A.hom = S.u (P b) := Over.w _
      have w2 : (S.ex (perC P₀ (co (c b))) 0).left ≫ A.hom = S.u (perC P₀ (co (c b))) := Over.w _
      rw [← w1, hl, w2]
    funext l
    show valAt' (pt (c b)) U (xs l) = b l
    rw [← hu, hPu b hbB']
    exact hxs b (hB'T hbB') l
  have hinj := inj_of_leftInv (fun b l => valAt' (pt b) U (xs l)) c b₀
    (by rw [hc0]; exact hτd) hcd hleft
  rw [hc0] at hinj
  apply hinj
  rw [map_zero, fderiv_pi hcompdiff]
  funext l
  simp only [ContinuousLinearMap.pi_apply, Pi.zero_apply]
  exact hw U (xs l) hUpt0
