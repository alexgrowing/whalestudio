import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HtValOnSubset
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlatDegreeStatementOfDegreeTheorem
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrameCoord
import Development.AbelianVarietyTheory.Definitions.Divisors.VolMeasureOfAdd
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.NonemptyUnitAt
import Development.AbelianVarietyTheory.Definitions.Divisors.TorusExt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StepIdeal
import Development.AutomorphicArithmetic.DivisorFrames.TangentVectorsReductionPrime
import Development.AbelianVarietyTheory.Definitions.Divisors.IsLocalRingTrivSqZeroExt
import Development.AbelianVarietyTheory.Definitions.CMLattices.IntegralOf
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsCompleteDVRCompletionIntegralIffStatement
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.LowerTriIsUnitDet
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsAlgebraicOfNormConst
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HostIntegerCharacterCompConjEqConjEmbedding
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRamificationCompleteDVRValuationEqMulStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlatLineWeightCharacterTriangularFrameChangeStatement
import Development.AbelianVarietyTheory.Proofs.HeightProofs.MemRangeOfValVLeOne
open AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G.Semi NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.FlatDegreeCompare

theorem UpperTheory.archimedean_section_valuation_bound :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (x : ℝ), Laws U x → ∀ (Z : Comp Xo c) (τ : Psi H) (s : ArchSec U x Z (flatWt Dw τ)) (ρ : HeightOneSpectrum (𝓞 c.F) → ℝ), (∀ la, ∀ w ∈ valOn Z la, w s.sig = (ρ la : EReal)) → ∀ (K : Type) [Field K] [NumberField K] [Algebra c.F K] (y : FrPt Xo c K), LiesOn Z y → ∀ (t₀ : SAB H (Sp K)) (m1 : SABMap t₀ Xo.univ.t y.x) (v : Fin (Dw.mult τ.1) → (epsR K ⟶ t₀.G)) (v' : Fin (Dw.mult (conjEmb τ.1)) → (epsR K ⟶ t₀.G)), (∀ i, (v i).left ≫ m1.φ = y.u τ.1 i) → (∀ i, (v' i).left ≫ m1.φ = y.u (conjEmb τ.1) i) → Indep v → Indep v' → ∀ (π : HeightOneSpectrum (𝓞 K) → HeightOneSpectrum (𝓞 c.F)) (ε : HeightOneSpectrum (𝓞 K) → ℕ), (∀ 𝔓 (z : c.F), 𝔓.valuation K (algebraMap c.F K z) = (π 𝔓).valuation c.F z ^ ε 𝔓) → ∀ (𝔓 : HeightOneSpectrum (𝓞 K)), HasModel t₀ 𝔓 → ∀ (a a' : ℝ), EigenvectorLieDegree.IsLocOrd t₀.G v 𝔓 a → EigenvectorLieDegree.IsLocOrd t₀.G v' 𝔓 a' → (ε 𝔓 : ℝ) * ρ (π 𝔓) = (vAdd 𝔓 (evR Xo c s.sig y) : ℝ) + (a - a') := by
  intro E _ _ _ H Dw l Xo c r U x hL Z τ s ρ hρ K _ _ _ y hyZ t₀ m1 v v' hv1 hv1' hI hI' π ε hπε 𝔓 hM a a' ha ha'
  have hε : 0 < ε 𝔓 := by
    rcases Nat.eq_zero_or_pos (ε 𝔓) with h | h
    · have h0 := hπε 𝔓 0
      rw [h, pow_zero, map_zero, map_zero] at h0
      exact absurd h0 zero_ne_one
    · exact h
  obtain ⟨T, iK, hFin, hT⟩ := GlobalTheory.T.exists_completeDVR_completion_integral_iff K 𝔓
  obtain ⟨e, he, hv⟩ := GlobalTheory.T.exists_ramification_completeDVR_valuation_eq_mul K 𝔓 T iK hT
  letI := (iK.comp (algebraMap c.F K)).toAlgebra
  let φ : K →ₐ[c.F] T.Fr := { iK with commutes' := fun _ => rfl }
  obtain ⟨yT, hyT⟩ := GlobalTheory.FlagTan.exists_frMap φ y
  obtain ⟨y', td, hbor, hint0⟩ := GlobalTheory.RealisationValues.Proportional.exists_integral_change
    (GlobalTheory.T.evaluation_laws_generic_frames_atlas_hold E H Dw l Xo c).1 (GlobalTheory.T.exists_global_model_goodLevel_all_primes E H Dw l Xo c hL.pos hL.good hL.lev).1
    (valV T.V (K' := T.Fr)).valuationSubring yT
  have hint : Formalism.L2.Pj.Integral T (iK.comp (algebraMap c.F K)) y' :=
    hint0 T _ (AlgHom.id _ _) (fun x hx => GlobalTheory.RealisationValues.Proportional.mem_range_of_valV_le_one hx) y'
      (ReciprocityTheory.ChartRestriction.G.PullbackSections.frMap_refl y')
  have hA := UpperTheory.tangent_vectors_reduction_prime E H Dw l Xo c K y t₀ m1 τ.1 v hv1 𝔓 T iK e he hv yT hyT td y' hbor hint
  have hB := UpperTheory.tangent_vectors_reduction_prime E H Dw l Xo c K y t₀ m1 (conjEmb τ.1) v' hv1' 𝔓 T iK e he hv yT hyT td y' hbor hint
  obtain ⟨g, hg⟩ := exists_gen hI hM
  obtain ⟨g', hg'⟩ := exists_gen hI' hM
  have hAa := (eq_of_locOrd hI hg ha).trans (eq_of_locOrd hI hg hA).symm
  have hBa := (eq_of_locOrd hI' hg' ha').trans (eq_of_locOrd hI' hg' hB).symm
  obtain ⟨C, -, -, hchg⟩ := ((GlobalTheory.Frames.frBor_calculus E H Dw l Xo c T.Fr yT y' y').1 td).1 hbor
  have hover : OverLa (π 𝔓) T.V (iK.comp (algebraMap c.F K)) (e * ε 𝔓) := by
    refine ⟨Nat.mul_pos he hε, fun z => ?_⟩
    rw [RingHom.comp_apply, hv, vAdd, hπε, vLa]
    by_cases hz : z = 0
    · subst hz; simp
    · have hz' : (π 𝔓).valuation c.F z ≠ 0 := by simpa using hz
      rw [WithZero.log_pow]
      push_cast; ring
  let yI : IntFr Xo c T (iK.comp (algebraMap c.F K)) := ⟨y', GlobalTheory.FlagTan.fromTest_of_isLocalRing y', hint⟩
  have hyTZ : LiesOn Z yT := GlobalTheory.FlatLine.liesOn_frMap hyT hyZ
  have hlies : LiesOn Z y' := by
    have e1 : ptF y' = ptF yT := by
      unfold ptF
      congr 1
      exact hchg.1
    intro p
    rw [e1]
    exact hyTZ p
  have hmem : (fun f => nval T.V (e * ε 𝔓) (evI yI f)) ∈ valOn Z (π 𝔓) :=
    ⟨PtV.mk (π 𝔓) hover yI ⟨hFin, hlies⟩ () trivial, rfl⟩
  have hval := hρ (π 𝔓) _ hmem
  have hev1 := GlobalTheory.FlagTan.evR_frBor s.sig_mem hbor
  have hev2 : evR Xo c s.sig yT = φ (evR Xo c s.sig y) := GlobalTheory.FlagTan.evR_frMap s.sig_mem.1 hyT
  have hS4 := GlobalTheory.T.flatLineWeight_character_triangular_frameChange E H Dw τ T.Fr td
  have hφ : ∀ z, φ z = iK z := fun _ => rfl
  have hD : ∀ σ, (∏ i : Fin (Dw.mult σ), (td (some ⟨σ, i⟩) : T.Fr)) ≠ 0 := fun σ =>
    Finset.prod_ne_zero_iff.2 fun i _ => (td _).ne_zero
  have hprod : evR Xo c s.sig y' * (∏ i : Fin (Dw.mult τ.1), (td (some ⟨τ.1, i⟩) : T.Fr)) =
      (∏ i : Fin (Dw.mult (conjEmb τ.1)), (td (some ⟨conjEmb τ.1, i⟩) : T.Fr)) * iK (evR Xo c s.sig y) := by
    rw [hev1, hev2, hφ, ← hS4]
    ring
  have hval' : nval T.V (e * ε 𝔓) (evR Xo c s.sig y') = (ρ (π 𝔓) : EReal) := hval
  have hy'0 : evR Xo c s.sig y' ≠ 0 := by
    intro h0
    rw [h0, nval_zero] at hval'
    exact EReal.coe_ne_top _ hval'.symm
  have ha0 : iK (evR Xo c s.sig y) ≠ 0 := by
    intro h0
    rw [h0, mul_zero] at hprod
    exact mul_ne_zero hy'0 (hD _) hprod
  have hZ := congrArg (vV T.V) hprod
  rw [vV_mul hy'0 (hD _), vV_mul (hD _) ha0, hv] at hZ
  rw [nval_of_ne hy'0, EReal.coe_eq_coe_iff] at hval'
  have he' : (e : ℝ) ≠ 0 := by exact_mod_cast he.ne'
  have hε' : (ε 𝔓 : ℝ) ≠ 0 := by exact_mod_cast hε.ne'
  have hZ' := congrArg (Int.cast : ℤ → ℝ) hZ
  push_cast at hZ'
  rw [← hval', hAa, hBa, eq_sub_of_add_eq hZ']
  push_cast
  field_simp
  ring
