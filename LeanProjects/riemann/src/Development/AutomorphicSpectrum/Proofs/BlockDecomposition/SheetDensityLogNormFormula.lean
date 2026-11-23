import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RatiosEqOfSameOrbit
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterSheet
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterBridgeB
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry Limits TopologicalSpace MvPolynomial MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.ProjSpace GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt GlobalTheory.Points GlobalTheory.ChartGlue
open GroundTheory.Arith.SchemeCoh GroundTheory.Arith.SchemeCoh.ProjSpace
open GlobalTheory.CompanionTheory.MPDict GlobalTheory.CompanionTheory.MixZ
open ReciprocityTheory.ChartRestriction.G.Geo (mcPts IsMultiHomog SameOrbit segre fibre IsGoodProj IsSheet HermLine IsSmoothHerm sheetDensity maDensity ptsIntegral ptsIntegralAt pot)
open ReciprocityTheory.ChartRestriction.G.AI.I2 (IsRatSectionOn logNormRat)

noncomputable section

namespace GlobalTheory.CompanionTheory.MixZ.ArchEq

section Torus

variable {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)]

theorem eval_torus_of_homog {s : ReciprocityTheory.ChartRestriction.G.Geo.MRing ι} {a : K → ℕ} (hs : IsMultiHomog s a) (c : K → ℂ)
    (u : (Σ k, ι k) → ℂ) :
    eval (fun p => c p.1 * u p) (map (Int.castRingHom ℂ) s) =
      (∏ k, c k ^ a k) * eval u (map (Int.castRingHom ℂ) s) := by
  rw [MvPolynomial.eval_map, MvPolynomial.eval_map, MvPolynomial.eval₂_eq', MvPolynomial.eval₂_eq', Finset.mul_sum]
  refine Finset.sum_congr rfl fun d hd => ?_
  have hprod : ∏ p, (c p.1 * u p) ^ d p = (∏ k, c k ^ a k) * ∏ p, u p ^ d p := by
    simp only [mul_pow, Finset.prod_mul_distrib]
    congr 1
    rw [Fintype.prod_sigma]
    refine Finset.prod_congr rfl fun k _ => ?_
    show ∏ i, c k ^ d ⟨k, i⟩ = c k ^ a k
    rw [Finset.prod_pow_eq_pow_sum, hs d hd k]
  rw [hprod]
  ring

private theorem ratio_cancel {a b F G H : ℝ} (ha : a ≠ 0) (hb : b ≠ 0) :
    a * F / (b * G) / (a / b * H) = F / G / H := by
  by_cases hG : G = 0
  · simp [hG]
  by_cases hH : H = 0
  · simp [hH]
  field_simp

theorem logNormRat_torus {P : Ideal (ReciprocityTheory.ChartRestriction.G.Geo.MRing ι)} {A : HermLine ι} {f g : ReciprocityTheory.ChartRestriction.G.Geo.MRing ι}
    (h : IsRatSectionOn P A f g) {c : K → ℂ} (hc : ∀ k, c k ≠ 0) (z : (Σ k, ι k) → ℂ) :
    logNormRat A f g (fun p => c p.1 * z p) = logNormRat A f g z := by
  obtain ⟨α, β, hf, hg, -, -, hd⟩ := h
  have hne : ∀ (a : K → ℕ), ‖∏ k, c k ^ a k‖ ≠ 0 := fun a =>
    norm_ne_zero_iff.2 (Finset.prod_ne_zero_iff.2 fun k _ => pow_ne_zero _ (hc k))
  have hab : ∏ k, ‖c k‖ ^ A.a k = ‖∏ k, c k ^ α k‖ / ‖∏ k, c k ^ β k‖ := by
    rw [norm_prod, norm_prod, ← Finset.prod_div_distrib]
    refine Finset.prod_congr rfl fun k _ => ?_
    rw [← hd k, zpow_sub₀ (norm_ne_zero_iff.2 (hc k)), norm_pow, norm_pow, zpow_natCast, zpow_natCast]
  unfold logNormRat
  rw [eval_torus_of_homog hf, eval_torus_of_homog hg, A.smul c z hc, norm_mul, norm_mul, hab,
    ratio_cancel (hne α) (hne β)]

end Torus

theorem sheetDensity_eq_of_isSheet : ∀ (m : ℕ) (n : Fin (m + 1) → ℕ) (P : Ideal (Pol n)) (D : ℕ) (Ψ : GlobalTheory.CompanionTheory.MixZ.ArchEq.LinProj n D)
    (B A : HermLine (Bk n)) (f g : Pol n), ReciprocityTheory.ChartRestriction.G.Geo.IsArithVar P (D + 1) → IsGoodProj P Ψ → IsSmoothHerm B →
    IsRatSectionOn P A f g → ∀ᵐ v : Fin D → ℂ, ∀ w γ, IsSheet P Ψ v w γ →
      sheetDensity P Ψ (pot fun _ : Fin D => B) (logNormRat A f g) v w =
        logNormRat A f g (γ v) * maDensity (fun _ y' => Real.log (B.h (γ y'))) v := by
  intro m n P D Ψ B A f g hP hΨ hB hA
  let A' : HermLine (Bk n) := ReciprocityTheory.ChartRestriction.G.AI.I2.constLine 1
  have hA1 : ∀ z, ReciprocityTheory.ChartRestriction.G.Geo.logNorm A' 1 z = 1 := fun z => by
    simp [ReciprocityTheory.ChartRestriction.G.Geo.logNorm, A', ReciprocityTheory.ChartRestriction.G.AI.I2.constLine, HermLine.ofWeight, Real.exp_neg]
  have hAs : IsSmoothHerm A' := contDiffOn_const
  have hs : ReciprocityTheory.ChartRestriction.G.Geo.IsSectionOn P A' 1 := by
    refine ⟨0, fun k => by simp [A', ReciprocityTheory.ChartRestriction.G.AI.I2.constLine, HermLine.ofWeight], fun d hd k => ?_, fun h => ?_⟩
    · rw [MvPolynomial.support_one, Finset.mem_singleton] at hd
      subst hd
      simp
    · exact hP.2.1.1.ne_top ((Ideal.eq_top_iff_one P).mpr h)
  filter_upwards [ReciprocityTheory.ChartRestriction.G.Geo.sheetIndep (Fin (m + 1)) (Bk n) P D Ψ (fun _ => B) A' 1 hP hΨ (fun _ => hB) hAs hs]
    with v hind w γ hγ
  have hex : ∃ γ, IsSheet P Ψ v w γ := ⟨γ, hγ⟩
  have hc := hex.choose_spec
  have h1 := hind w _ γ hc hγ
  simp only [hA1, one_mul] at h1
  have hval : logNormRat A f g (hex.choose v) = logNormRat A f g (γ v) := by
    obtain ⟨c, hcne, hcz⟩ := ReciprocityTheory.ChartRestriction.G.Geo.sameOrbit_of_segre hγ.2.self_of_nhds.2.1.1 1 one_ne_zero
      (by rw [one_smul, hc.1, hγ.1])
    rw [hcz]
    exact logNormRat_torus hA hcne _
  unfold sheetDensity
  rw [dif_pos hex, hval]
  exact congrArg (logNormRat A f g (γ v) * ·) h1

end GlobalTheory.CompanionTheory.MixZ.ArchEq
