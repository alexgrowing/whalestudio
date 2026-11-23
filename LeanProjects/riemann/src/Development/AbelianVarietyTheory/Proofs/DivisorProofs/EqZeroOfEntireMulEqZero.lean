import Development.AbelianVarietyTheory.Definitions.Divisors.IsPolAVSectionInverseImage
import Development.AbelianVarietyTheory.Definitions.Divisors.ToricPeriodBlockIsSymm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoeffTopMonEqZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaCharEntireNeZeroAutomorphyStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.MBModel GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.MBLow.Cl Matrix

noncomputable section

namespace GlobalTheory.MBLow.Cl.FrameAut

theorem eq_zero_of_entire_mul_eq_zero {g : ℕ} {θ D : (Fin g → ℂ) → ℂ} (hθ : Differentiable ℂ θ) (h0 : θ ≠ 0)
    {S : Set (Fin g → ℂ)} (hS : IsOpen S) (hD : ContinuousOn D S) (h : ∀ w ∈ S, θ w * D w = 0)
    {z : Fin g → ℂ} (hz : z ∈ S) : D z = 0 := by
  by_contra hne
  have hc : ContinuousAt D z := hD.continuousAt (hS.mem_nhds hz)
  have he : θ =ᶠ[nhds z] 0 := by
    filter_upwards [hc.eventually_ne hne, hS.mem_nhds hz] with w hw hwS
    exact (mul_eq_zero.1 (h w hwS)).resolve_right hw
  have ha : AnalyticOnNhd ℂ θ Set.univ := SCV.analyticOnNhd_of_differentiable hθ Set.univ
  exact h0 (funext fun w =>
    ha.eqOn_zero_of_preconnected_of_eventuallyEq_zero isPreconnected_univ (Set.mem_univ z) he (Set.mem_univ w))

end GlobalTheory.MBLow.Cl.FrameAut

namespace GlobalTheory.MBLow.Cl

theorem frame_eq_autV_mul : ∀ (g : ℕ) (x : KeyIn ℂ) (hg : x.P.g = g) (u : HolUnif x.P.A x.P.L g) (τ : Matrix (Fin g) (Fin g) ℂ) (a b : Fin g → ℂ) (c : ℂ) (W : Fin g → Fin g → ℂ), NF x hg u τ a b c W → ∀ M N (i : x.P.L.ι) z, ⊤ ≤ (u.ex z).left ⁻¹ᵁ x.P.L.U i → u.fr i z = autV τ a b M N z * u.fr i (z + perV τ M N) := by
  intro g x hg u τ a b c W hNF M N i z hz
  obtain ⟨hs, hp, ha, hb, hc, hΛ, _, hth, _⟩ := hNF
  obtain ⟨hd, ⟨z₀, hz₀⟩, hlaw⟩ := GlobalTheory.T.thetaChar_differentiable_ne_zero_automorphy g τ a b hs hp ha hb
  have hdc : Differentiable ℂ (fun w => c * thetaChar τ a b w) := (differentiable_const c).mul hd
  have h0 : (fun w => c * thetaChar τ a b w) ≠ 0 := fun h => by
    have := congrFun h z₀
    simp only [Pi.zero_apply, mul_eq_zero] at this
    exact this.elim hc hz₀
  have hl : u.ex (perV τ M N) = 1 := (u.ker _).2 ((hΛ _).2 ⟨M, N, rfl⟩)
  have he : ∀ w, u.ex (w + perV τ M N) = u.ex w := fun w => by rw [u.ex_add, hl, _root_.mul_one]
  have hS : IsOpen {w | ⊤ ≤ (u.ex w).left ⁻¹ᵁ x.P.L.U i} := (u.hol _ 0).1
  have htr : ∀ w, ⊤ ≤ (u.ex w).left ⁻¹ᵁ x.P.L.U i → ⊤ ≤ (u.ex (w + perV τ M N)).left ⁻¹ᵁ x.P.L.U i :=
    fun w hw => by rw [he]; exact hw
  have hcf := (u.fr_hol i).continuousOn
  have haut : Continuous (autV τ a b M N) := by
    unfold autV dotProduct
    fun_prop
  have hD : ContinuousOn (fun w => u.fr i w - autV τ a b M N w * u.fr i (w + perV τ M N))
      {w | ⊤ ≤ (u.ex w).left ⁻¹ᵁ x.P.L.U i} :=
    hcf.sub (haut.continuousOn.mul (hcf.comp (continuous_add_const _).continuousOn fun w hw => htr w hw))
  refine sub_eq_zero.1 (FrameAut.eq_zero_of_entire_mul_eq_zero hdc h0 hS hD (fun w hw => ?_) hz)
  have h1 := hth i w hw
  have h2 := hth i _ (htr w hw)
  beta_reduce at h1 h2 ⊢
  rw [he, h1, hlaw] at h2
  linear_combination h2

end GlobalTheory.MBLow.Cl

end
