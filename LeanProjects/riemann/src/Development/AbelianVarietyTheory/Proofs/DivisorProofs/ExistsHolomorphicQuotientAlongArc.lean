import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.CuspIso
import Development.AbelianVarietyTheory.Definitions.Divisors.WellChosen
import Development.AbelianVarietyTheory.Definitions.Divisors.P22
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsLogCanonicalMultipleCanonical
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GeometricallyConnectedOfIsIsoRestrict
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DenseInterior
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrysToDRBijective
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArcZeroZero
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop
open GlobalTheory.AllWt (Psi wtOf cuspOn latOn normOn petOn GoodOn GoodW bergOn framesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp
open Filter Topology
open GlobalTheory.ShFam GlobalTheory.ShFam.BdArc GlobalTheory.Toroidal

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.Vanishing

section ArcQuot

variable {Y : Scheme.{0}} {W : Y.Opens}

theorem arcPt_mem_basicOpen (hW : IsAffineOpen W) (φ : Γ(Y, W) →+* ℂ) (q : Γ(Y, W)) (s : Sp ℂ) :
    (spMap φ ≫ (show Sp Γ(Y, W) ⟶ Y from hW.fromSpec)) s ∈ Y.basicOpen q ↔ φ q ≠ 0 := by
  change (spMap φ) s ∈ hW.fromSpec ⁻¹ᵁ Y.basicOpen q ↔ _
  rw [hW.fromSpec_preimage_basicOpen q]
  haveI := s.isPrime
  have hs : s.asIdeal = ⊥ := Ideal.eq_bot_of_prime _
  change q ∉ (Ideal.comap φ s.asIdeal) ↔ _
  rw [hs]
  simp [Ideal.mem_comap]

theorem evalPt_arcPt (hW : IsAffineOpen W) (φ : Γ(Y, W) →+* ℂ)
    (h : ⊤ ≤ (spMap φ ≫ (show Sp Γ(Y, W) ⟶ Y from hW.fromSpec)) ⁻¹ᵁ W) :
    GlobalTheory.TangentOrigin.evalPt (spMap φ ≫ (show Sp Γ(Y, W) ⟶ Y from hW.fromSpec)) W h = φ := by
  have := GlobalTheory.TangentOrigin.eq_spec_fromSpec hW _ h
  dsimp only [spMap] at this
  rw [cancel_mono] at this
  have := Spec.map_injective this
  exact (congrArg CommRingCat.Hom.hom this).symm

theorem arcPt_top_le (hW : IsAffineOpen W) (φ : Γ(Y, W) →+* ℂ) :
    ⊤ ≤ (spMap φ ≫ (show Sp Γ(Y, W) ⟶ Y from hW.fromSpec)) ⁻¹ᵁ W := by
  rw [Scheme.Hom.comp_preimage]
  change ⊤ ≤ spMap φ ⁻¹ᵁ (hW.fromSpec ⁻¹ᵁ W)
  rw [hW.fromSpec_preimage_self]
  exact le_rfl

theorem exists_punctured_ne_zero {f : ℂ → ℂ} {r : ℝ} (hf : DifferentiableOn ℂ f (Metric.ball 0 r))
    {u₀ : ℂ} (hu₀ : u₀ ∈ Metric.ball (0 : ℂ) r) (h₀ : f u₀ ≠ 0) (hr : 0 < r) :
    ∃ ρ : ℝ, 0 < ρ ∧ ρ ≤ r ∧ ∀ u ∈ Metric.ball (0 : ℂ) ρ, u ≠ 0 → f u ≠ 0 := by
  have ha := hf.analyticOnNhd Metric.isOpen_ball
  have h0 : (0 : ℂ) ∈ Metric.ball (0 : ℂ) r := Metric.mem_ball_self hr
  rcases (ha 0 h0).eventually_eq_zero_or_eventually_ne_zero with hz | hz
  · exact absurd (ha.eqOn_zero_of_preconnected_of_eventuallyEq_zero
      (convex_ball (0 : ℂ) r).isPreconnected h0 hz hu₀) h₀
  · rw [eventually_nhdsWithin_iff, Metric.eventually_nhds_iff_ball] at hz
    obtain ⟨ε, hε, hz⟩ := hz
    refine ⟨min ε r, lt_min hε hr, min_le_right _ _, fun u hu hu0 => hz u ?_ hu0⟩
    exact Metric.ball_subset_ball (min_le_left _ _) hu

end ArcQuot

end GlobalTheory.Vanishing

namespace GlobalTheory.Vanishing

theorem exists_quot_along_arc : ∀ {k : Type} [CommRing k] {Y : Scheme.{0}} {p : Y ⟶ Sp k} {B : LB Y} {O : Y.Opens} (m : H0 p B O) (W : Y.Opens) (hW : IsAffineOpen W) (i : B.ι), W ≤ B.U i → ∀ (ψ : ℂ → (Γ(Y, W) →+* ℂ)) (r : ℝ), IsHolPts ψ r → (∀ u ∈ Metric.ball (0 : ℂ) r, u ≠ 0 → ⊤ ≤ (spMap (ψ u) ≫ (show Sp Γ(Y, W) ⟶ Y from hW.fromSpec)) ⁻¹ᵁ O) → ∃ (ρ : ℝ) (a b : Γ(Y, W)), 0 < ρ ∧ ρ ≤ r ∧ ∀ u ∈ Metric.ball (0 : ℂ) ρ, u ≠ 0 → ψ u b ≠ 0 ∧ ∀ (hO : ⊤ ≤ (spMap (ψ u) ≫ (show Sp Γ(Y, W) ⟶ Y from hW.fromSpec)) ⁻¹ᵁ O) (hi : ⊤ ≤ (spMap (ψ u) ≫ (show Sp Γ(Y, W) ⟶ Y from hW.fromSpec)) ⁻¹ᵁ B.U i), H0.val (spMap (ψ u) ≫ (show Sp Γ(Y, W) ⟶ Y from hW.fromSpec)) i hO hi m * ψ u b = ψ u a := by
  intro k _ Y p B O m W hW i hWi ψ r hψ hout
  obtain ⟨hr, hhol⟩ := hψ
  have hu₀ : ((r / 2 : ℝ) : ℂ) ∈ Metric.ball (0 : ℂ) r := by
    rw [Metric.mem_ball, dist_zero_right, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (half_pos hr)]
    linarith
  have hu₀0 : ((r / 2 : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 (half_pos hr).ne'
  obtain ⟨s⟩ : Nonempty (Sp ℂ) := inferInstance
  have hyO : (spMap (ψ (r / 2 : ℝ)) ≫ (show Sp Γ(Y, W) ⟶ Y from hW.fromSpec)) s ∈ O :=
    hout _ hu₀ hu₀0 (show s ∈ (⊤ : (Sp ℂ).Opens) from trivial)
  have hyW : (spMap (ψ (r / 2 : ℝ)) ≫ (show Sp Γ(Y, W) ⟶ Y from hW.fromSpec)) s ∈ W :=
    arcPt_top_le hW (ψ (r / 2 : ℝ)) (show s ∈ (⊤ : (Sp ℂ).Opens) from trivial)
  obtain ⟨q, hqle, hqy⟩ := hW.exists_basicOpen_le (V := O ⊓ B.U i) ⟨_, hyO, hWi hyW⟩ hyW
  have hq0 : ψ (r / 2 : ℝ) q ≠ 0 := (arcPt_mem_basicOpen hW _ q s).1 hqy
  haveI := hW.isLocalization_basicOpen q
  obtain ⟨n, a, hna⟩ := IsLocalization.Away.surj q (resG Y hqle (m.loc i))
  obtain ⟨ρ, hρ, hρr, hne⟩ := exists_punctured_ne_zero (hhol q) hu₀ hq0 hr
  refine ⟨ρ, a, q ^ n, hρ, hρr, fun u hu hu0 => ?_⟩
  have hqu : ψ u q ≠ 0 := hne u hu hu0
  refine ⟨by rw [map_pow]; exact pow_ne_zero _ hqu, fun hO hi => ?_⟩
  have hD : ⊤ ≤ (spMap (ψ u) ≫ (show Sp Γ(Y, W) ⟶ Y from hW.fromSpec)) ⁻¹ᵁ Y.basicOpen q :=
    fun s _ => (arcPt_mem_basicOpen hW (ψ u) q s).2 hqu
  have hWx := arcPt_top_le hW (ψ u)
  have e := congrArg (GlobalTheory.TangentOrigin.evalPt _ _ hD) hna
  have hres (z : Γ(Y, W)) : GlobalTheory.TangentOrigin.evalPt _ _ hD (algebraMap Γ(Y, W) Γ(Y, Y.basicOpen q) z) = ψ u z := by
    exact (GlobalTheory.TangentOrigin.evalPt_res _ (Y.basicOpen_le q) hWx hD z).trans
      (DFunLike.congr_fun (evalPt_arcPt hW (ψ u) hWx) z)
  rw [map_mul, map_pow, hres, hres] at e
  rw [H0.val_apply, ← GlobalTheory.TangentOrigin.evalPt_res _ hqle _ hD, map_pow, e]

end GlobalTheory.Vanishing
