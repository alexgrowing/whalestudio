import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MultihomogeneousIdeals.ExistsUniqueStatement
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.HeckeSectionsIsotropicCommutatorPairingPower
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterNamed
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.KleimanNefness.KleimanSt
import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.ArithIntersectionDivisorSupportStatement
import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.ArithIntersectionSectionRecursionStatement
import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.ChartLatticePowerSectionStatement
import Development.WeilBound.CoreStatements.FlagImmersions.ExistsSmooth

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology GlobalTheory.CompanionTheory.Ar.Top

theorem RootFieldNumerics.intersection_section_log_integral : ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH.KleimanNefFStatement → (∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)], ReciprocityTheory.ChartRestriction.G.AI.I1.ExistsUniqueStatement ℚ ι) → ReciprocityTheory.ChartRestriction.G.Geo.DivSuppArithStatement → ∀ II : IntersectionSystem, IsFullIntersectionSystem II → ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] (y : (Σ k, ι k) → Ω) (e : ℕ) (L : Fin e → HermLine ι) (A : HermLine ι) (s : Ω), IsArithVar (mCoordIdeal y) (e + 2) → Birational y → (∀ j, IsSmoothHerm (L j)) → IsSmoothHerm A → s ≠ 0 → s ∈ chartLatNm y A.a 1 → (∀ j W', IsArithVar W' 2 → mCoordIdeal y ≤ W' → 0 ≤ geomDeg W' (L j) 1) → 0 ≤ ptsIntegral (mCoordIdeal y) (fun j z => Real.log (((Fin.snoc L A : Fin (e + 1) → HermLine ι) j).h z)) (fun _ => 1) := by
  intro hK hEU hDiv II hII K _ ι _ Ω _ y e L A s hV hB hL hA hs hsA hgeo
  have hW : ∀ W : Ideal (MRing ι), IsArithVar W (e + 1) → mCoordIdeal y ≤ W →
      0 ≤ ptsIntegral W (fun j z => Real.log ((L j).h z)) (fun _ => 1) := by
    intro W hW hle
    exact GlobalTheory.T.ptsIntegral_log_nonneg hK hEU hDiv II hII K ι W e L hW hL
      (fun j W' hW' hle' => hgeo j W' hW' (le_trans hle hle'))
  obtain ⟨b, c, hc0, hc⟩ := GlobalTheory.T.chart_lattice_power_section K ι Ω y (e + 2) A.a s hV hB hsA
  obtain ⟨B, hBs, hBa⟩ := RootFieldNumerics.EffN.exists_smooth (ι := ι) b
  have key : ∀ n : ℕ, 0 ≤ ptsIntegral (mCoordIdeal y)
      (fun j z => Real.log (((Fin.snoc L B : Fin (e + 1) → HermLine ι) j).h z)) (fun _ => 1)
      + (n : ℝ) * ptsIntegral (mCoordIdeal y)
      (fun j z => Real.log (((Fin.snoc L A : Fin (e + 1) → HermLine ι) j).h z)) (fun _ => 1) := by
    intro n
    obtain ⟨C, hCs, hCa⟩ := RootFieldNumerics.EffN.exists_smooth (ι := ι) (b + n • A.a)
    have hCa' : C.a = B.a + (n : ℤ) • A.a := by rw [hCa, hBa, natCast_zsmul]
    have hmem : c * s ^ n ∈ chartLat y C.a 1 := by rw [hCa]; exact hc n
    have h0 := GlobalTheory.T.arith_intersection_section_recursion II hII hDiv K ι Ω y e L C (c * s ^ n) hV hB hL hCs
      (mul_ne_zero hc0 (pow_ne_zero _ hs)) hmem hW
    rw [RootFieldNumerics.EffN.last_lin II hII (mCoordIdeal y) e hV L A B C (n : ℤ) hL hA hBs hCs hCa'] at h0
    simpa using h0
  set PB := ptsIntegral (mCoordIdeal y)
    (fun j z => Real.log (((Fin.snoc L B : Fin (e + 1) → HermLine ι) j).h z)) (fun _ => 1)
  set PA := ptsIntegral (mCoordIdeal y)
    (fun j z => Real.log (((Fin.snoc L A : Fin (e + 1) → HermLine ι) j).h z)) (fun _ => 1)
  by_contra hneg
  push_neg at hneg
  have hpos : 0 < -PA := by linarith
  obtain ⟨n, hn⟩ := exists_nat_gt (PB / -PA)
  have h1 := (div_lt_iff₀ hpos).mp hn
  have h2 := key n
  have h3 : (n : ℝ) * -PA = -((n : ℝ) * PA) := by ring
  linarith
