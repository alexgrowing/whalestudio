import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SemiposAtOfPositive
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Definitions.Divisors.NefFibOfIsNef
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolynomialNumeratorLinearExtensionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GreenPotentialSmoothPullbackStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DegreeComparisonRootMetricsStatement
import Development.AbelianVarietyTheory.Definitions.Divisors.ChernOn
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ArTopTrue
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ScaleZeroComp
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsKitWithKitWith
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O
open scoped ENNReal Classical
open MvPolynomial Formalism.DegreeFormula Formalism.BasicNotions.DV Formalism.MainNotions.WeightThresholdDefs Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M GlobalTheory.FlagPoly GlobalTheory.FlagAr
open GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.TrueGeo AlgebraicGeometry CategoryTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.ArInt GlobalTheory.Cartier GlobalTheory.CxPts

set_option maxHeartbeats 800000

namespace GlobalTheory.DegreeOnObjects

theorem eq_sum_single {τ : Type} [Fintype τ] [DecidableEq τ] {n : ℕ} (u : τ → Fin n → ℝ) :
    u = ∑ x : τ × Fin n, u x.1 x.2 • (Pi.single x.1 (Pi.single x.2 (1 : ℝ)) : τ → Fin n → ℝ) := by
  funext t i
  rw [Finset.sum_apply, Finset.sum_apply, Fintype.sum_eq_single (t, i)]
  · simp
  · rintro ⟨t', i'⟩ hne
    simp only [Pi.smul_apply, smul_eq_mul]
    by_cases ht : t = t'
    · subst ht
      have hi : i ≠ i' := fun h => hne (by rw [h])
      simp [hi]
    · simp [ht]

theorem tieDeg_onObj : Hypotheses2 → HypothesesH → OnObj fun _ _ _ T _ _ => TieDeg T := by
  intro hP hH D O hO _ A T H h B hB R hR u
  have hO' := hO
  obtain ⟨xa, P, hx⟩ := hO'
  have hR2 : (2 : ℝ) ≤ R := by
    have := Real.add_one_le_exp (2 : ℝ)
    linarith
  change (arIn O.s O.Φ O.met.hm).arDeg (setB O.Y B) R (linRoot u ^ (dimY O.Y + 1)) = _
  rw [ArIn.arDeg]
  erw [LinearMap.sum_apply]
  refine Finset.sum_congr rfl fun c _ => ?_
  have hm : O.met.hm = metsOf xa O.Φ := hx.hm_eq
  set S := FlagAr.setB O.Y B with hS
  set w : D.what₂.Tau × Fin O.N → Sym D.host.E →₀ ℤ :=
    fun x => rootSym O.S.Dw (ArIn.ind S) (some R) (DV.tauEmb D x.1) x.2 with hw
  have hsupp : ∀ x, ∀ a ∈ (w x).support, {q | a.1 q = true}.Finite ∧ a.2.1 = some R := by
    intro x a ha
    have e : a.1 = ArIn.ind S ∧ a.2.1 = some R := by
      simp only [hw, rootSym] at ha
      split_ifs at ha <;>
      · have := Finsupp.support_single_subset ha
        rw [Finset.mem_singleton] at this
        subst this
        exact ⟨rfl, rfl⟩
    refine ⟨?_, e.2⟩
    rw [e.1]
    simpa [ArIn.ind] using S.finite_toSet
  obtain ⟨-, hfam⟩ := GlobalTheory.ArTopTrue.arTop_true hP.p4 hH.deg GlobalTheory.ShFam.Pad.HTBound.htBound D O.A O.N O.j O.S O.κ O.s xa O.Φ
    c R hR2
  obtain ⟨M, L, m, Ψ, hI, hΨ, hnum⟩ := hfam (D.what₂.Tau × Fin O.N) w hsupp
  rw [O.dim_eq c] at hnum
  have hhom : (linRoot u ^ (dimY O.Y + 1)).IsHomogeneous (dimY O.Y + 1) := by
    have h1 : (linRoot u).IsHomogeneous 1 := by
      unfold linRoot
      refine MvPolynomial.IsHomogeneous.neg ?_
      exact MvPolynomial.IsHomogeneous.sum _ _ _ fun i _ => MvPolynomial.isHomogeneous_C_mul_X _ _
    simpa using h1.pow (dimY O.Y + 1)
  have hL : (numL ((arIn O.s O.Φ O.met.hm).num c) (dimFl D.what₂.Tau O.N + 1) ∘ₗ
      (MvPolynomial.rename fun x => (arIn O.s O.Φ O.met.hm).root (ArIn.ind S) R x c).toLinearMap)
        (linRoot u ^ (dimY O.Y + 1)) =
      Ψ (linRoot u ^ (dimY O.Y + 1)) / (((m : ℕ) : ℝ) ^ (dimY O.Y + 1) * (Module.finrank ℚ D.what₂.LL : ℝ)) := by
    rw [show arIn O.s O.Φ O.met.hm = arIn O.s O.Φ (metsOf xa O.Φ) by rw [hm]]
    exact GlobalTheory.T.polynomial_numerator_linear_extension _ _ w Ψ _ (fun μ hμ => hnum μ hμ) _ hhom
  set W := h.mdl S c with hWdef
  obtain ⟨ε, π, hd⟩ := W.V.exists_isDown (h.man c)
  have hs := GlobalTheory.T.green_potential_smooth_pullback hP hH D O hO A T H h c R hR2 u W.V ε π hd
  have har : IsArithVar W.V.p (dimY O.Y) := by
    have := W.V.ar
    rwa [O.dim_eq c] at this
  obtain ⟨Φ, hΦ⟩ := ((hP.p4.arExists _ _ W.V.p (dimY O.Y) har).2 _
    (fun o : Option (Option (D.what₂.Tau × Fin O.N)) => o.elim (fnB ((T.M c).pull ε π ((2 : ℝ) • (T.F c).phR R u)) hs.2.1 hs.2.2) (W.gens S))).1
  have hN := h.num B hB c ε π hd ((T.F c).phR R u) hs.1 hs.2.1 hs.2.2 Φ hΦ
    (fun o : Option (Option (D.what₂.Tau × Fin O.N)) => o.elim 1 fun o' => o'.elim 0 fun x => u x.1 x.2)
  have hI' : ∀ x, (adlOf (O.Φ.C c) (O.met.hm c) (rootSym O.S.Dw (ArIn.ind S) (some R) (DV.tauEmb D x.1) x.2)).Induced
      M (L x) m 0 := by
    rw [hm]; exact hI
  have h3 := GlobalTheory.T.degree_comparison_root_metrics hP hH D O hO A T H h B hB R hR c u M L m Ψ hI' hΨ ε π hd hs.2.1 hs.2.2 Φ hΦ
  rw [hL]
  refine h3.trans ?_
  rw [hN, mul_div_cancel_left₀ _ W.V.ν_pos.ne']
  unfold Real0.fR
  congr 1
  simp only [Option.elim, one_smul, zero_smul, add_zero, Fintype.sum_option, Real0.gen]
  congr 1
  rw [zero_add]
  have e := eq_sum_single (τ := D.what₂.Tau) (n := O.N) u
  conv_rhs => rw [e]
  erw [map_sum]
  exact Finset.sum_congr rfl fun x _ => (LinearMap.map_smul _ _ _).symm

end GlobalTheory.DegreeOnObjects
