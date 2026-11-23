import Mathlib
import Development.AutomorphicArithmetic.CMTraceForms.Places
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.IntegralChartDepthLeResidueCharTwoStatement
import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.ExistsIntegralChartIntegralFramedPoint
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.StarRingExtOfStar
import Formalism.LocalToGlobal.ProjectiveLattices.CrudeVal
import Development.AbelianVarietyTheory.Definitions.Jets.TwoPlaces
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.ConnectionKillsSeries
open AlgebraicGeometry CategoryTheory NumberField IsDedekindDomain IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open GlobalTheory.CharDepth TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CharDepth

theorem ramOverZ_pos_place {K : Type} [Field K] [NumberField K] (la : HeightOneSpectrum (𝓞 K)) :
    0 < ramOverZ la := by
  have h := Crude.crv_vLa_char la
  rw [Crude.crv_vLa_natCast_eq] at h
  have h0 : ((resCharOf la : ℕ) : 𝓞 K) ≠ 0 := by exact_mod_cast (Crude.resCharOf_prime la).ne_zero
  have h1 : la.intValuation ((resCharOf la : ℕ) : 𝓞 K) < 1 :=
    (la.intValuation_lt_one_iff_mem _).2 (Crude.crv_char_mem la)
  have h2 : WithZero.log (la.intValuation ((resCharOf la : ℕ) : 𝓞 K)) < 0 := by
    have := (WithZero.log_lt_log (la.intValuation_ne_zero _ h0) one_ne_zero).2 h1
    simpa using this
  omega

theorem vV_eq_zero_of_isUnit (T : CDVR) {x : T.V} (hx : IsUnit x) : vV T.V (algebraMap T.V T.Fr x) = 0 := by
  have h : valV T.V (algebraMap T.V T.Fr x) = 1 := by
    unfold valV
    rw [HeightOneSpectrum.valuation_of_algebraMap, HeightOneSpectrum.intValuation_eq_one_iff]
    intro hm
    exact (IsLocalRing.mem_maximalIdeal _).1 hm hx
  simp [vV, h]

theorem nuW_le_two : ∀ (p : ℕ) [Fact p.Prime], AvFSt p → HTFSt p → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 E)], (∀ a : 𝓞 E, star a = H.bar a) → ∀ (f : ℕ) (vd : ℝ), 0 ≤ vd → UpperTheory.Depth.SplitAt H.d p → UpperTheory.Depth.SplitPlaces p H f vd → ∀ (la : HeightOneSpectrum (𝓞 c.F)), resCharOf la = p → ∀ (k n : ℕ) (a : (E →+* ℂ) × ℕ → ℕ), DomW Dw a → Fintype.card (Lt1 Dw) ≤ n → ∀ Ap : ℝ, 0 ≤ Ap → (∀ τ, InPsi H τ → (a (τ, 0) : ℝ) ≤ Ap) → (open Classical in nuW Xo c la k a n ≤ (((ramOverZ la : ℝ) * ((f : ℝ) * Dw.q * (1 + vd / 2) * Ap + Dw.q * ∑ τ ∈ Finset.univ.filter (fun τ => ¬ InPsi H τ), (a (τ, 0) : ℝ)) : ℝ) : EReal)) := by
  intro p _ hA hH E _ _ _ H Dw l Xo c inst hst f vd hvd hsp hT la hla k n a ha hn Ap hAp hle
  obtain rfl : inst = H.starRing := GlobalTheory.PowGerm.starSt E H inst hst
  letI := H.starRing
  have hE : IntChartEx Xo c := (GlobalTheory.IntChartExists.intChart_exists E H Dw l Xo c).2.1 hst
  refine max_le ?_ ?_
  · rw [EReal.coe_nonneg]
    positivity
  refine iSup_le fun T => iSup_le fun io => iSup_le fun e => iSup_le fun ho => iSup_le fun y => iSup_le fun hy => ?_
  obtain ⟨C⟩ := hE T io y hy
  have hv : vV T.V ((p : ℕ) : T.Fr) = (e : ℤ) * (ramOverZ la : ℤ) := by
    rw [← map_natCast io, ho.2, ← hla, Crude.crv_vLa_char]
  have he : 0 < e := ho.1
  have hnu : ¬ IsUnit ((p : ℕ) : T.V) := by
    intro hu
    have h0 := vV_eq_zero_of_isUnit T hu
    rw [map_natCast, hv] at h0
    have := ramOverZ_pos_place la
    have : (0 : ℤ) < (e : ℤ) * (ramOverZ la : ℤ) := by positivity
    omega
  refine (iInf_le _ C).trans ((GlobalTheory.T.integralChartDepth_le_residueChar_two p hA hH E H Dw l Xo c T io y C hy hnu hsp f vd hvd hT e k n a he ha hn Ap hAp hle).trans (le_of_eq ?_))
  have he' : (e : ℝ) ≠ 0 := by exact_mod_cast he.ne'
  rw [hv, Int.cast_mul, Int.cast_natCast, Int.cast_natCast, mul_div_cancel_left₀ _ he']

end GlobalTheory.CharDepth
