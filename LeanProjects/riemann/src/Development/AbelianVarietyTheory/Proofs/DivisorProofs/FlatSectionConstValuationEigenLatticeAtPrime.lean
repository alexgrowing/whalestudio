import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrameCoord
import Development.AbelianVarietyTheory.Definitions.Divisors.IsLocalRingTrivSqZeroExt
import Development.AbelianVarietyTheory.Definitions.CMLattices.IntegralOf
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsCompleteDVRCompletionIntegralIffStatement
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.LowerTriIsUnitDet
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsAlgebraicOfNormConst
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HostIntegerCharacterCompConjEqConjEmbedding
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRamificationCompleteDVRValuationEqMulStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DetValuationsSumZeroSameLocalLatticeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlatLineWeightCharacterTriangularFrameChangeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TriangularFrameChangeBasechangeIntegralAtCompletStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralFrameSpanCompletedEigenLatticeStatement

open AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G.Semi NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore

namespace GlobalTheory.PtDeg

theorem rho_eq_vAdd_at_prime : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (x : ℝ), Laws U x → ∀ (Z : Comp Xo c) (τ : Psi H) (s : ArchSec U x Z (flatWt Dw τ)) (ρ : HeightOneSpectrum (𝓞 c.F) → ℝ), (∀ la, ∀ w ∈ valOn Z la, w s.sig = (ρ la : EReal)) → ∀ (K : Type) [Field K] [NumberField K] [Algebra c.F K] (y : FrPt Xo c K), LiesOn Z y → ∀ (B : GlobalTheory.CM.PAT H (Sp (𝓞 K))) (t₀ : SAB H (Sp K)) (m1 : SABMap t₀ Xo.univ.t y.x) (m2 : SABMap t₀ B.t (spMap (algebraMap (𝓞 K) K))) (F : GlobalTheory.CM.GenFib B.pol) (t : 𝓞 E →+* 𝓞 K), (∀ a, ((t a : 𝓞 K) : K) = algebraMap c.F K (embK c τ.1 a)) → ∀ (π : HeightOneSpectrum (𝓞 K) → HeightOneSpectrum (𝓞 c.F)) (ε : HeightOneSpectrum (𝓞 K) → ℕ), (∀ 𝔓 (z : c.F), 𝔓.valuation K (algebraMap c.F K z) = (π 𝔓).valuation c.F z ^ ε 𝔓) → ∀ (u : Fin (Dw.mult τ.1) → Fin F.P₀.g → K) (u' : Fin (Dw.mult (conjEmb τ.1)) → Fin F.P₀.g → K), GlobalTheory.PtDeg.FrameCoord y m1 m2 F τ.1 u → GlobalTheory.PtDeg.FrameCoord y m1 m2 F (conjEmb τ.1) u' → ∀ (𝔓 : HeightOneSpectrum (𝓞 K)) (b : Fin (Dw.mult τ.1) → Fin F.P₀.g → K) (M : Matrix (Fin (Dw.mult τ.1)) (Fin (Dw.mult τ.1)) K) (b' : Fin (Dw.mult (conjEmb τ.1)) → Fin F.P₀.g → K) (M' : Matrix (Fin (Dw.mult (conjEmb τ.1))) (Fin (Dw.mult (conjEmb τ.1))) K), GlobalTheory.PtDeg.LocBasis 𝔓 (F.eigLat B.t.act t) b → (∀ i, u i = ∑ j, M i j • b j) → GlobalTheory.PtDeg.LocBasis 𝔓 (F.eigLat B.t.act (t.comp (H.bar : 𝓞 E →+* 𝓞 E))) b' → (∀ i, u' i = ∑ j, M' i j • b' j) → (ε 𝔓 : ℝ) * ρ (π 𝔓) = (vAdd 𝔓 (evR Xo c s.sig y) : ℝ) + (vAdd 𝔓 M.det : ℝ) - (vAdd 𝔓 M'.det : ℝ) := by
  intro E _ _ _ H Dw l Xo c r U x hL Z τ s ρ hρ K _ _ _ y hyZ B t₀ m1 m2 F t ht π ε hπε u u' hu hu' 𝔓 b M b' M' hb hM hb' hM'
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
  obtain ⟨ρV, hρV, G, t', n, n', m1', m2', h1, h2, C, td, y', hlow, hdiag, hchg, hlie, hint⟩ :=
    GlobalTheory.T.triangular_frameChange_basechange_integral_at_completion E H Dw l Xo c K y B t₀ m1 m2 𝔓 T iK hT yT hyT
  have hbor : FrBor td yT y' :=
    ((GlobalTheory.Frames.frBor_calculus E H Dw l Xo c T.Fr yT y' y').1 td).2 ⟨C, hlow, hdiag, hchg⟩
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
  have hct := GlobalTheory.ConjHostChar.conj_char E H Dw l Xo c τ K t ht
  obtain ⟨hA1, hA2⟩ := GlobalTheory.T.integralFrame_span_completed_eigenLattice E H Dw l Xo c K y B t₀ m1 m2 F τ.1 t ht u hu 𝔓 T iK hT ρV hρV yT hyT G t' n n'
    m1' m2' h1 h2 C (td none) y' hchg hlie
  obtain ⟨hB1, hB2⟩ := GlobalTheory.T.integralFrame_span_completed_eigenLattice E H Dw l Xo c K y B t₀ m1 m2 F (conjEmb τ.1) (t.comp (H.bar : 𝓞 E →+* 𝓞 E)) hct u' hu'
    𝔓 T iK hT ρV hρV yT hyT G t' n n' m1' m2' h1 h2 C (td none) y' hchg hlie
  obtain ⟨-, hCdet, hvC⟩ := GlobalTheory.T.det_valuations_sum_zero_same_local_lattice K 𝔓 T iK hT F.P₀.g _ _ b hb M u hM (C τ.1) hA1 hA2
  obtain ⟨-, -, hvC'⟩ := GlobalTheory.T.det_valuations_sum_zero_same_local_lattice K 𝔓 T iK hT F.P₀.g _ _ b' hb' M' u' hM' (C (conjEmb τ.1)) hB1 hB2
  have hdet : ∀ σ, (C σ).det = ∏ i, (td (some ⟨σ, i⟩) : T.Fr) := fun σ => by
    rw [Matrix.det_of_lowerTriangular (C σ) (fun i j hij => hlow σ i j hij)]
    exact Finset.prod_congr rfl fun i _ => hdiag σ i
  have hφ : ∀ z, φ z = iK z := fun _ => rfl
  have hprod : evR Xo c s.sig y' * (C τ.1).det = (C (conjEmb τ.1)).det * iK (evR Xo c s.sig y) := by
    rw [hev1, hev2, hdet, hdet, hφ, ← hS4]
    ring
  have hval' : nval T.V (e * ε 𝔓) (evR Xo c s.sig y') = (ρ (π 𝔓) : EReal) := hval
  have hy'0 : evR Xo c s.sig y' ≠ 0 := by
    intro h0
    rw [h0, nval_zero] at hval'
    exact EReal.coe_ne_top _ hval'.symm
  have ha0 : iK (evR Xo c s.sig y) ≠ 0 := by
    intro h0
    rw [h0, mul_zero] at hprod
    exact mul_ne_zero hy'0 hCdet hprod
  have hC'0 : (C (conjEmb τ.1)).det ≠ 0 := by
    intro h0
    rw [h0, zero_mul] at hprod
    exact mul_ne_zero hy'0 hCdet hprod
  have hZ := congrArg (vV T.V) hprod
  rw [vV_mul hy'0 hCdet, vV_mul hC'0 ha0, hv] at hZ
  rw [hv] at hvC hvC'
  rw [nval_of_ne hy'0, EReal.coe_eq_coe_iff] at hval'
  have hvy : (vV T.V (evR Xo c s.sig y') : ℝ) = e * ((vAdd 𝔓 (evR Xo c s.sig y) : ℝ) + (vAdd 𝔓 M.det : ℝ) - (vAdd 𝔓 M'.det : ℝ)) := by
    have : vV T.V (evR Xo c s.sig y') = e * (vAdd 𝔓 (evR Xo c s.sig y) + vAdd 𝔓 M.det - vAdd 𝔓 M'.det) := by linarith
    rw [this]; push_cast; ring
  rw [← hval', hvy]
  have he' : (e : ℝ) ≠ 0 := by exact_mod_cast he.ne'
  have hε' : (ε 𝔓 : ℝ) ≠ 0 := by exact_mod_cast hε.ne'
  push_cast
  field_simp

end GlobalTheory.PtDeg
