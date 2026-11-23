import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IdealPeriodLatticeOfCurveDatum
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.InducedTypeThetaGenusOnePermutes
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PowerSeriesSupNormMulPadicComplex
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicComplexIntegralBoundedSeriesLaws
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CoeffNormLeOneOfIsogenySeriesIdentitiesStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExpMvNegLogMvMul
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.TaylorSeriesInParameterRescaleOfAlgebraic
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SigmaStarSquareQuotientInModelParameterStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IntSerOfIsWq
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.EvenThetaTwoTorsionBasicProperties
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsogenyFibresEvenThetaSigmaStarSquareQuotientStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.AlgebraicTaylorTorsionTranslateEvenThetaStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.EvenThetaTranslateSqEqSigmaStarStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.EvenThetaDoubleTranslateMulStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsTraceOneEvenNormUnitAtTwoStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IntegralJAndAlgebraicData
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CmThetaTaylorCoeffAlgebraicAndConjugate
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CmThetaTorsionTranslateIntegralSeriesStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CmThetaPointsIntegralNormConjugateLawsStatement
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Formalism.PairingDivisors.StatementH
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.OddThetaFunctionExistenceUniqueness
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DifferentiableSqTh
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.EvenTheta
open scoped BigOperators

noncomputable section
namespace GlobalTheory.EvenTheta

section General
variable {p : ℕ} [Fact p.Prime]

theorem lamC_coe (lam : Qbar →+* ℂ_[p]) {x : ℂ} (hx : x ∈ Qbar) : lamC lam x = lam ⟨x, hx⟩ := dif_pos hx

theorem lamC_mul (lam : Qbar →+* ℂ_[p]) {x y : ℂ} (hx : x ∈ Qbar) (hy : y ∈ Qbar) :
    lamC lam (x * y) = lamC lam x * lamC lam y := by
  rw [lamC_coe lam hx, lamC_coe lam hy, lamC_coe lam (mul_mem hx hy), ← map_mul]; rfl

theorem lamC_sub (lam : Qbar →+* ℂ_[p]) {x y : ℂ} (hx : x ∈ Qbar) (hy : y ∈ Qbar) :
    lamC lam (x - y) = lamC lam x - lamC lam y := by
  rw [lamC_coe lam hx, lamC_coe lam hy, lamC_coe lam (sub_mem hx hy), ← map_sub]; rfl

theorem lamC_one (lam : Qbar →+* ℂ_[p]) : lamC lam 1 = 1 := by
  rw [lamC_coe lam (one_mem _)]; exact map_one lam

theorem lamC_neg_one (lam : Qbar →+* ℂ_[p]) : lamC lam (-1) = -1 := by
  rw [lamC_coe lam (neg_mem (one_mem _)), ← map_one lam, ← map_neg]; rfl

theorem lamC_inj (lam : Qbar →+* ℂ_[p]) {x y : ℂ} (hx : x ∈ Qbar) (hy : y ∈ Qbar)
    (h : lamC lam x = lamC lam y) : x = y := by
  rw [lamC_coe lam hx, lamC_coe lam hy] at h
  exact congrArg Subtype.val (lam.injective h)

theorem xAt_inj (g : GL3Theta.G1 p) {v w : ℂ} (hv : wpF g.abelian₂ v ∈ Qbar) (hw : wpF g.abelian₂ w ∈ Qbar)
    (h : xAt g v = xAt g w) : wpF g.abelian₂ v = wpF g.abelian₂ w := by
  refine lamC_inj g.lam hv hw ?_
  have := mul_left_cancel₀ (pow_ne_zero 2 (Units.ne_zero _)) h
  linear_combination this

theorem IntSer.bdd {f : PowerSeries ℂ_[p]} (h : IntSer f) : BddSer f := ⟨1, h⟩

theorem IntSer.mul {f g : PowerSeries ℂ_[p]} (hf : IntSer f) (hg : IntSer g) : IntSer (f * g) :=
  ((GlobalTheory.EvenTheta.SerRing.series_ring_laws p).1 f g hf hg).2.2
theorem IntSer.add {f g : PowerSeries ℂ_[p]} (hf : IntSer f) (hg : IntSer g) : IntSer (f + g) :=
  ((GlobalTheory.EvenTheta.SerRing.series_ring_laws p).1 f g hf hg).1
theorem IntSer.sub {f g : PowerSeries ℂ_[p]} (hf : IntSer f) (hg : IntSer g) : IntSer (f - g) :=
  ((GlobalTheory.EvenTheta.SerRing.series_ring_laws p).1 f g hf hg).2.1
theorem BddSer.mul {f g : PowerSeries ℂ_[p]} (hf : BddSer f) (hg : BddSer g) : BddSer (f * g) :=
  ((GlobalTheory.EvenTheta.SerRing.series_ring_laws p).2.1 f g hf hg).2.2
theorem BddSer.add {f g : PowerSeries ℂ_[p]} (hf : BddSer f) (hg : BddSer g) : BddSer (f + g) :=
  ((GlobalTheory.EvenTheta.SerRing.series_ring_laws p).2.1 f g hf hg).1
theorem bdd_C (c : ℂ_[p]) : BddSer (PowerSeries.C c) := ((GlobalTheory.EvenTheta.SerRing.series_ring_laws p).2.2.1 c).1
theorem int_C {c : ℂ_[p]} (h : ‖c‖ ≤ 1) : IntSer (PowerSeries.C c) := ((GlobalTheory.EvenTheta.SerRing.series_ring_laws p).2.2.1 c).2 h
theorem int_X : IntSer (PowerSeries.X : PowerSeries ℂ_[p]) := (GlobalTheory.EvenTheta.SerRing.series_ring_laws p).2.2.2.1
theorem IntSer.inv {f : PowerSeries ℂ_[p]} (hf : IntSer f) (h : ‖PowerSeries.constantCoeff f‖ = 1) :
    IntSer f⁻¹ := (GlobalTheory.EvenTheta.SerRing.series_ring_laws p).2.2.2.2.1 f hf h
theorem IntSer.sq {f : PowerSeries ℂ_[p]} (hf : IntSer f) : IntSer (f ^ 2) := by
  rw [_root_.sq]; exact hf.mul hf
theorem intSer_iff {f : PowerSeries ℂ_[p]} : IntegralMv f ↔ IntSer f := by
  constructor
  · intro h n; exact h (Finsupp.single () n)
  · intro h n
    have := h (n ())
    rwa [PowerSeries.coeff_def (s := n) rfl] at this

theorem int_of_sq {f : PowerSeries ℂ_[p]} (hb : BddSer f) (h : IntSer (f ^ 2)) : IntSer f := by
  intro n
  have := GlobalTheory.EvenTheta.sup_norm_mul_padicComplex p f f 1 hb hb (by rw [← _root_.sq]; exact h) n n
  nlinarith [norm_nonneg (PowerSeries.coeff n f)]

theorem int_line {e : PowerSeries ℂ_[p]} {x : ℂ_[p]} (he : IntSer e) :
    IntSer (lineSer e x) ↔ ‖x‖ ≤ 1 := by
  constructor
  · intro h
    have := he.sub h 2
    simpa [lineSer, PowerSeries.coeff_X_pow] using this
  · intro h
    exact he.sub ((int_C h).mul int_X.sq)

variable (g : GL3Theta.G1 p)

theorem atU_mul {F G : ℂ → ℂ} (hF : AlgEnt F) (hG : AlgEnt G) :
    AlgEnt (fun z => F z * G z) ∧ g.atU (fun z => F z * G z) = g.atU F * g.atU G :=
  ((GlobalTheory.SerTransport.transport p g).1 F G hF hG).1
theorem atU_add {F G : ℂ → ℂ} (hF : AlgEnt F) (hG : AlgEnt G) :
    AlgEnt (fun z => F z + G z) ∧ g.atU (fun z => F z + G z) = g.atU F + g.atU G :=
  ((GlobalTheory.SerTransport.transport p g).1 F G hF hG).2
theorem atU_smul {c : ℂ} (hc : c ∈ Qbar) {F : ℂ → ℂ} (hF : AlgEnt F) :
    AlgEnt (fun z => c * F z) ∧ g.atU (fun z => c * F z) = PowerSeries.C (lamC g.lam c) * g.atU F := by
  obtain ⟨h1, h2⟩ := (GlobalTheory.SerTransport.transport p g).2.1 c hc
  rw [← h2]
  exact atU_mul g h1 hF
theorem atU_sq {F : ℂ → ℂ} (hF : AlgEnt F) :
    AlgEnt (fun z => F z ^ 2) ∧ g.atU (fun z => F z ^ 2) = g.atU F ^ 2 := by
  simp only [_root_.sq]
  exact atU_mul g hF hF
theorem atU_prod {ι : Type} (s : Finset ι) {F : ι → ℂ → ℂ} (hF : ∀ i, AlgEnt (F i)) :
    AlgEnt (fun z => ∏ i ∈ s, F i z) ∧ g.atU (fun z => ∏ i ∈ s, F i z) = ∏ i ∈ s, g.atU (F i) := by
  induction s using Finset.induction_on with
  | empty =>
    obtain ⟨h1, h2⟩ := (GlobalTheory.SerTransport.transport p g).2.1 1 (one_mem _)
    simp only [Finset.prod_empty]
    exact ⟨h1, by rw [h2, lamC_one, map_one]⟩
  | insert a s ha ih =>
    simp only [Finset.prod_insert ha]
    rw [← ih.2]
    exact atU_mul g (hF a) ih.1

end General

theorem thetaTranslation_zero (Λ : AddSubgroup ℂ) (F : ℂ → ℂ) : U1 Λ 0 F = F := by
  funext z; simp [U1]

section Two
variable {g : GL3Theta.G1 2} {t₀ : ℂ} (hok : g.Ok) (hlat : IsLat g.abelian₂) (hdisc : TaylorLogMetric.discr g.abelian₂ = 1)
  (h2 : g2 g.abelian₂ ∈ Qbar) (h3 : g3 g.abelian₂ ∈ Qbar)
  (hwp : ∀ t, InRationalLattice g.abelian₂ t → t ∉ g.abelian₂ → wpF g.abelian₂ t ∈ Qbar)
  (halg : ∀ x, InRationalLattice g.abelian₂ x → AlgEnt (U1 g.abelian₂ x (sgStar g.abelian₂)))
  (hnm : t₀ ∉ g.abelian₂) (htwo : 2 * t₀ ∈ g.abelian₂)

theorem rational_lattice_point_zero (Λ : AddSubgroup ℂ) : InRationalLattice Λ 0 := ⟨1, one_pos, by simp⟩

include halg in
theorem alg_sg : AlgEnt (sgStar g.abelian₂) := by
  have := halg 0 (rational_lattice_point_zero _)
  rwa [thetaTranslation_zero] at this

include hlat halg hnm htwo in
theorem alg_th : AlgEnt (GL3Theta.th0 g.abelian₂ t₀) := by
  have := (GlobalTheory.T.algebraicTaylor_torsionTranslate_evenTheta g.abelian₂ hlat halg t₀ hnm htwo 0 (rational_lattice_point_zero _)).1
  rwa [thetaTranslation_zero] at this

include hok hlat h2 h3 hwp halg in
theorem atU_sqTh {v : ℂ} (hv : v ∉ g.abelian₂) (hq : InRationalLattice g.abelian₂ v) :
    AlgEnt (sqTh g.abelian₂ v) ∧
      g.atU (sqTh g.abelian₂ v) = ePhi1 g.lam g.abelian₂ g.C g.wq ^ 2 * lineSer g.wq⁻¹ (xAt g v) :=
  GlobalTheory.T.sigmaStarSquareQuotient_in_model_parameter 2 g hok.2.1 hlat h2 h3 (alg_sg halg) v hv (hwp v hq hv)

include hok hlat h2 h3 hwp halg hnm htwo in
theorem atU_th_sq : PowerSeries.constantCoeff (g.atU (GL3Theta.th0 g.abelian₂ t₀)) = 1 ∧
    g.atU (GL3Theta.th0 g.abelian₂ t₀) ^ 2 = ePhi1 g.lam g.abelian₂ g.C g.wq ^ 2 * lineSer g.wq⁻¹ (xAt g t₀) := by
  obtain ⟨-, h0, -, hsq, -⟩ := GlobalTheory.EvenTheta.evenThetaTwoTorsion_basic_properties g.abelian₂ hlat t₀ hnm htwo
  have ha := alg_th hlat halg hnm htwo
  refine ⟨by rw [((GlobalTheory.SerTransport.transport 2 g).2.2.1 _ ha).2, h0, lamC_one], ?_⟩
  rw [← (atU_sq g ha).2, ← (atU_sqTh hok hlat h2 h3 hwp halg hnm ⟨2, two_pos, by exact_mod_cast htwo⟩).2]
  exact congrArg _ (funext hsq)

include hok hlat hdisc h2 h3 hwp halg hnm htwo in

theorem int_th {β : ℂ} {k : ℕ} (hβ : β ∈ Qbar) (hn : ‖lamC g.lam β‖ = 1)
    (hst : ∀ ω ∈ g.abelian₂, β * ω ∈ g.abelian₂) (htr : β + starRingEnd ℂ β = 1)
    (hN : β * starRingEnd ℂ β = ((2 * k : ℕ) : ℂ)) (hb1 : β * t₀ ∉ g.abelian₂) (hb2 : (1 - β) * t₀ ∉ g.abelian₂)
    (hint : IntegralMv (g.mulBy (lamC g.lam β) (GL3Theta.Xv ()) : MvPowerSeries Unit ℂ_[2])) :
    IntSer (g.atU (GL3Theta.th0 g.abelian₂ t₀)) ∧ ‖xAt g t₀‖ ≤ 1 := by
  obtain ⟨Q, Q', hQ, hQ', e1, e2, hne, ⟨j0, hj0⟩, ⟨j1, hj1⟩, h01⟩ :=
    GlobalTheory.T.isogeny_fibres_even_theta_sigmaStarSquareQuotient g.abelian₂ hlat β t₀ k hst htr hN htwo hb1 hb2
  obtain ⟨h, hh, hh0, hh1, hsub⟩ := (GlobalTheory.SerTransport.transport 2 g).2.2.2 hok β hβ
  obtain ⟨-, hw, hw0, hE, -⟩ := GlobalTheory.EvenTheta.DatumBasic.datum_basic 2 g hok hlat h2 h3 hdisc
  obtain ⟨hf0, hf2⟩ := atU_th_sq hok hlat h2 h3 hwp halg hnm htwo
  have hq0 : InRationalLattice g.abelian₂ t₀ := ⟨2, two_pos, by exact_mod_cast htwo⟩
  have hq1 : InRationalLattice g.abelian₂ (β * t₀) := ⟨2, two_pos, by
    have := hst _ htwo
    rwa [show β * (2 * t₀) = ((2 : ℕ) : ℂ) * (β * t₀) by push_cast; ring] at this⟩
  have hd := fun v hv hq => atU_sqTh (v := v) hok hlat h2 h3 hwp halg hv hq
  have hxe : ∀ v w, wpF g.abelian₂ v = wpF g.abelian₂ w → xAt g v = xAt g w := fun v w h => by
    simp only [xAt, h]
  refine GlobalTheory.T.coeffNormLeOne_of_isogeny_series_identities 2 k g.wq⁻¹ h (ePhi1 g.lam g.abelian₂ g.C g.wq ^ 2) _ (xAt g t₀) (xAt g (β * t₀))
    (fun i => xAt g (Q i)) (fun j => xAt g (Q' j)) hw hw0 (intSer_iff.1 (hh ▸ hint)) hh0 (hh1 ▸ hn) ?_
    (by rw [map_pow, hE, one_pow]) hf0 hf2 ?_ ?_ ?_ ⟨j0, hxe _ _ hj0⟩ ⟨j1, hxe _ _ hj1⟩ ?_
  · rw [Nat.cast_mul, norm_mul]
    have h1 : ‖((2 : ℕ) : ℂ_[2])‖ < 1 := by
      rw [← map_natCast (algebraMap ℚ_[2] ℂ_[2]), norm_algebraMap']
      exact Padic.norm_p_lt_one
    have h4 : ‖(k : ℂ_[2])‖ ≤ 1 := IsUltrametricDist.norm_natCast_le_one _ _
    nlinarith [norm_nonneg ((2 : ℕ) : ℂ_[2]), norm_nonneg (k : ℂ_[2])]
  · rw [← (hsub _ (alg_th hlat halg hnm htwo)).2, funext e1,
      (atU_prod g Finset.univ fun i => (hd _ (hQ i).1 (hQ i).2).1).2,
      Finset.prod_congr rfl fun i _ => (hd _ (hQ i).1 (hQ i).2).2, Finset.prod_mul_distrib]
    simp
  · rw [← (hd _ hb1 hq1).2, ← (hsub _ (hd _ hb1 hq1).1).2, funext e2,
      (atU_prod g Finset.univ fun i => (hd _ (hQ' i).1 (hQ' i).2).1).2,
      Finset.prod_congr rfl fun i _ => (hd _ (hQ' i).1 (hQ' i).2).2, Finset.prod_mul_distrib]
    simp
  · exact fun i j h => hne i j (xAt_inj g (hwp _ (hQ i).2 (hQ i).1) (hwp _ (hQ' j).2 (hQ' j).1) h)
  · exact fun h => h01 (xAt_inj g (hwp _ hq0 hnm) (hwp _ hq1 hb1) h)

theorem tors_laQ {Λ : AddSubgroup ℂ} {t : ℂ} (h : GL3Theta.Tors1 2 Λ t) : InRationalLattice Λ t :=
  let ⟨_, n, hn, _, h⟩ := h; ⟨n, hn, h⟩

theorem tors_neg {Λ : AddSubgroup ℂ} {t : ℂ} (h : GL3Theta.Tors1 2 Λ t) : GL3Theta.Tors1 2 Λ (-t) := by
  obtain ⟨h0, n, hn, hc, h⟩ := h
  exact ⟨by simpa using h0, n, hn, hc, by simpa using h⟩

theorem tors_two {Λ : AddSubgroup ℂ} {t : ℂ} (h : GL3Theta.Tors1 2 Λ t) : GL3Theta.Tors1 2 Λ (2 * t) := by
  obtain ⟨h0, n, hn, hc, h⟩ := h
  obtain ⟨m, rfl⟩ : Odd n := by simpa using hc
  refine ⟨fun h' => h0 ?_, _, hn, hc, ?_⟩
  · have := sub_mem h (nsmul_mem h' m)
    convert this using 1
    simp only [nsmul_eq_mul]; push_cast; ring
  · have := add_mem h h
    convert this using 1
    ring

theorem tors_half {Λ : AddSubgroup ℂ} {t : ℂ} (h : GL3Theta.Tors1 2 Λ t) :
    ∃ s ω, GL3Theta.Tors1 2 Λ s ∧ ω ∈ Λ ∧ 2 * s = t + ω := by
  obtain ⟨h0, n, hn, hc, h⟩ := h
  obtain ⟨m, rfl⟩ : Odd n := by simpa using hc
  have e : 2 * (((m : ℂ) + 1) * t) = t + ((2 * m + 1 : ℕ) : ℂ) * t := by push_cast; ring
  refine ⟨(m + 1) * t, _, ⟨fun h' => h0 ?_, _, hn, hc, ?_⟩, h, e⟩
  · have := sub_mem (add_mem h' h') h
    convert this using 1
    push_cast; ring
  · have := nsmul_mem h (m + 1)
    convert this using 1
    simp only [nsmul_eq_mul]; push_cast; ring

variable (htr : ∀ t : ℂ, GL3Theta.Tors1 2 g.abelian₂ t →
      IntegralMv ((ePhi1 g.lam g.abelian₂ g.C g.wq)⁻¹ * g.atU (U1 g.abelian₂ t (sgStar g.abelian₂))) ∧
      ‖PowerSeries.constantCoeff (g.atU (U1 g.abelian₂ t (sgStar g.abelian₂)))‖ = 1)

include hok hlat hdisc h2 h3 halg htr in
theorem exists_tau {t : ℂ} (ht : GL3Theta.Tors1 2 g.abelian₂ t) : ∃ τ : PowerSeries ℂ_[2], IntSer τ ∧
    ‖PowerSeries.constantCoeff τ‖ = 1 ∧ U1 g.abelian₂ t (sgStar g.abelian₂) 0 ∈ Qbar ∧
    ‖lamC g.lam (U1 g.abelian₂ t (sgStar g.abelian₂) 0)‖ = 1 ∧
    g.atU (U1 g.abelian₂ t (sgStar g.abelian₂)) = ePhi1 g.lam g.abelian₂ g.C g.wq * τ := by
  obtain ⟨-, -, -, hE, -⟩ := GlobalTheory.EvenTheta.DatumBasic.datum_basic 2 g hok hlat h2 h3 hdisc
  obtain ⟨a, b⟩ := htr t ht
  obtain ⟨c, d⟩ := (GlobalTheory.SerTransport.transport 2 g).2.2.1 _ (halg t (tors_laQ ht))
  refine ⟨_, intSer_iff.1 a, ?_, c, d ▸ b, ?_⟩
  · rw [map_mul, PowerSeries.constantCoeff_inv, hE, inv_one, one_mul, b]
  · rw [← mul_assoc, PowerSeries.mul_inv_cancel _ (by rw [hE]; exact one_ne_zero), one_mul]

include hok hlat hdisc h2 h3 hwp halg htr in

theorem norm_xAt_tors {t : ℂ} (ht : GL3Theta.Tors1 2 g.abelian₂ t) : ‖xAt g t‖ ≤ 1 := by
  obtain ⟨-, hw, -, hE, -⟩ := GlobalTheory.EvenTheta.DatumBasic.datum_basic 2 g hok hlat h2 h3 hdisc
  obtain ⟨τ, a1, -, a3, a4, a5⟩ := exists_tau hok hlat hdisc h2 h3 halg htr ht
  obtain ⟨τ', b1, -, b3, b4, b5⟩ := exists_tau hok hlat hdisc h2 h3 halg htr (tors_neg ht)
  obtain ⟨c1, c2⟩ := atU_sqTh hok hlat h2 h3 hwp halg ht.1 (tors_laQ ht)
  have e := (atU_smul g (mul_mem a3 b3) c1).2
  rw [funext (hlat.sqTh_mul ht.1), (atU_mul g (halg _ (tors_laQ ht)) (halg _ (tors_laQ (tors_neg ht)))).2,
    a5, b5, c2, lamC_mul _ a3 b3] at e
  set c := lamC g.lam (U1 g.abelian₂ t (sgStar g.abelian₂) 0) * lamC g.lam (U1 g.abelian₂ (-t) (sgStar g.abelian₂) 0) with hc
  have hc1 : ‖c‖ = 1 := by rw [hc, norm_mul, a4, b4, one_mul]
  have hc0 : c ≠ 0 := by intro h; rw [h, norm_zero] at hc1; exact zero_ne_one hc1
  have hE0 : ePhi1 g.lam g.abelian₂ g.C g.wq ≠ 0 := by intro h; rw [h, map_zero] at hE; exact zero_ne_one hE
  have e2 : lineSer g.wq⁻¹ (xAt g t) = PowerSeries.C c⁻¹ * (τ * τ') := by
    have hcc : PowerSeries.C c⁻¹ * PowerSeries.C c = 1 := by rw [← map_mul, inv_mul_cancel₀ hc0, map_one]
    refine mul_left_cancel₀ (pow_ne_zero 2 hE0) ?_
    linear_combination (-PowerSeries.C c⁻¹) * e -
      (ePhi1 g.lam g.abelian₂ g.C g.wq ^ 2 * lineSer g.wq⁻¹ (xAt g t)) * hcc
  rw [← int_line hw, e2]
  exact (int_C (by rw [norm_inv, hc1, inv_one])).mul (a1.mul b1)

variable (hf : IntSer (g.atU (GL3Theta.th0 g.abelian₂ t₀))) (hx : ‖xAt g t₀‖ ≤ 1)

include hok hlat hdisc h2 h3 hwp halg hnm htwo hf hx in
theorem int_E_sq : IntSer (ePhi1 g.lam g.abelian₂ g.C g.wq ^ 2) := by
  obtain ⟨-, hw, hw0, hE, -⟩ := GlobalTheory.EvenTheta.DatumBasic.datum_basic 2 g hok hlat h2 h3 hdisc
  obtain ⟨hf0, hf2⟩ := atU_th_sq hok hlat h2 h3 hwp halg hnm htwo
  have h0 : PowerSeries.constantCoeff (lineSer g.wq⁻¹ (xAt g t₀)) = 1 := by
    simp only [lineSer, map_sub, map_mul, map_pow, PowerSeries.constantCoeff_X, hw0]; simp
  have := hf.sq.mul (((int_line hw).2 hx).inv (by rw [h0, norm_one]))
  rwa [hf2, mul_assoc, PowerSeries.mul_inv_cancel _ (by rw [h0]; exact one_ne_zero), mul_one] at this

include hok hlat hdisc h2 h3 hwp halg hnm htwo htr hx in

theorem transl_sq {t : ℂ} (ht : GL3Theta.Tors1 2 g.abelian₂ t) : ∃ H : PowerSeries ℂ_[2], IntSer H ∧
    (‖PowerSeries.coeff 0 H‖ = 1 ∨ ‖PowerSeries.coeff 1 H‖ = 1) ∧
    g.atU (U1 g.abelian₂ t (GL3Theta.th0 g.abelian₂ t₀)) ^ 2 = ePhi1 g.lam g.abelian₂ g.C g.wq ^ 2 * H := by
  obtain ⟨hε, hw, -, hE, hσ⟩ := GlobalTheory.EvenTheta.DatumBasic.datum_basic 2 g hok hlat h2 h3 hdisc
  obtain ⟨τ, a1, a2, a3, a4, a5⟩ := exists_tau hok hlat hdisc h2 h3 halg htr ht
  obtain ⟨τ', b1, b2, -, -, b5⟩ := exists_tau hok hlat hdisc h2 h3 halg htr (tors_two ht)
  have hq0 : InRationalLattice g.abelian₂ t₀ := ⟨2, two_pos, by exact_mod_cast htwo⟩
  have w1 := hwp _ (tors_laQ ht) ht.1
  have w0 := hwp _ hq0 hnm
  have hA := (GlobalTheory.T.algebraicTaylor_torsionTranslate_evenTheta g.abelian₂ hlat halg t₀ hnm htwo t (tors_laQ ht)).1
  have hs1 := halg _ (tors_laQ ht)
  have hs2 := halg _ (tors_laQ (tors_two ht))
  have hs0 := alg_sg halg
  have e := (atU_smul g (mul_mem a3 a3) (atU_sq g hA).1).2
  have id1 : (fun z => U1 g.abelian₂ t (sgStar g.abelian₂) 0 * U1 g.abelian₂ t (sgStar g.abelian₂) 0 *
      U1 g.abelian₂ t (GL3Theta.th0 g.abelian₂ t₀) z ^ 2) = fun z =>
      (-1) * (U1 g.abelian₂ (2 * t) (sgStar g.abelian₂) z * sgStar g.abelian₂ z) +
      ((wpF g.abelian₂ t - wpF g.abelian₂ t₀) * (U1 g.abelian₂ t (sgStar g.abelian₂) 0 * U1 g.abelian₂ t (sgStar g.abelian₂) 0)) *
        U1 g.abelian₂ t (sgStar g.abelian₂) z ^ 2 := by
    funext z
    linear_combination GlobalTheory.T.U1_sq_mul_U1_th0_sq_eq_sgStar g.abelian₂ hlat t₀ hnm htwo t ht.1 z
  have m1 := atU_smul g (neg_mem (one_mem _)) (atU_mul g hs2 hs0).1
  have m2 := atU_smul g (mul_mem (sub_mem w1 w0) (mul_mem a3 a3)) (atU_sq g hs1).1
  rw [id1, (atU_add g m1.1 m2.1).2, m1.2, m2.2, (atU_mul g hs2 hs0).2, (atU_sq g hs1).2, (atU_sq g hA).2,
    a5, b5, hσ, lamC_neg_one, lamC_mul _ (sub_mem w1 w0) (mul_mem a3 a3), lamC_mul _ a3 a3] at e
  set c := lamC g.lam (U1 g.abelian₂ t (sgStar g.abelian₂) 0) with hc
  set ε := ((g.C.u⁻¹ : ℂ_[2]ˣ) : ℂ_[2]) with hεd
  set κ := lamC g.lam (wpF g.abelian₂ t - wpF g.abelian₂ t₀) with hκ
  have hκ1 : ‖κ‖ ≤ 1 := by
    have e1 : ε ^ 2 * κ = xAt g t - xAt g t₀ := by
      rw [hκ, lamC_sub _ w1 w0, xAt, xAt]; ring
    have e2 : ‖xAt g t - xAt g t₀‖ ≤ 1 := by
      rw [sub_eq_add_neg]
      refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ (by rwa [norm_neg]))
      exact norm_xAt_tors hok hlat hdisc h2 h3 hwp halg htr ht
    rwa [← e1, norm_mul, norm_pow, hε, one_pow, one_mul] at e2
  have hc0 : c ≠ 0 := by intro h; rw [h, norm_zero] at a4; exact zero_ne_one a4
  set μ := -(c * c)⁻¹ * ε with hμ
  have hμ1 : ‖μ‖ = 1 := by simp [hμ, a4, hε]
  refine ⟨PowerSeries.C μ * (PowerSeries.X * τ') + PowerSeries.C κ * τ ^ 2,
    ((int_C hμ1.le).mul (int_X.mul b1)).add ((int_C hκ1).mul a1.sq), ?_, ?_⟩
  · rcases hκ1.eq_or_lt with h | h
    · left
      simp [h, a2]
    · right
      have n1 : ‖μ * PowerSeries.constantCoeff τ'‖ = 1 := by rw [norm_mul, hμ1, b2, one_mul]
      have n2 : ‖κ * PowerSeries.coeff 1 (τ ^ 2)‖ < 1 := by
        rw [norm_mul]
        nlinarith [a1.sq 1, norm_nonneg κ, norm_nonneg (PowerSeries.coeff 1 (τ ^ 2))]
      rw [map_add, PowerSeries.coeff_C_mul, PowerSeries.coeff_C_mul, PowerSeries.coeff_succ_X_mul,
        PowerSeries.coeff_zero_eq_constantCoeff_apply,
        IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm (by rw [n1]; exact n2.ne'), n1]
      exact max_eq_left n2.le
  · have hcc : PowerSeries.C (c * c)⁻¹ * PowerSeries.C (c * c) = 1 := by
      rw [← map_mul, inv_mul_cancel₀ (mul_ne_zero hc0 hc0), map_one]
    rw [hμ]
    simp only [map_mul, map_neg, map_one] at e hcc ⊢
    linear_combination (-PowerSeries.C (c * c)⁻¹) * e -
      (g.atU (U1 g.abelian₂ t (GL3Theta.th0 g.abelian₂ t₀)) ^ 2 -
        PowerSeries.C κ * ePhi1 g.lam g.abelian₂ g.C g.wq ^ 2 * τ ^ 2) * hcc

include hok hlat hdisc h2 h3 hwp halg hnm htwo htr hf hx in

theorem transl_bdd {t : ℂ} (ht : GL3Theta.Tors1 2 g.abelian₂ t) :
    BddSer (g.atU (U1 g.abelian₂ t (GL3Theta.th0 g.abelian₂ t₀))) := by
  obtain ⟨s, ω, hs, hω, e2⟩ := tors_half ht
  obtain ⟨hA, hsh⟩ := GlobalTheory.T.algebraicTaylor_torsionTranslate_evenTheta g.abelian₂ hlat halg t₀ hnm htwo t (tors_laQ ht)
  obtain ⟨κ, hκ, hκ0, hκe⟩ := hsh ω hω
  rw [← e2] at hκe
  have hAs := (GlobalTheory.T.algebraicTaylor_torsionTranslate_evenTheta g.abelian₂ hlat halg t₀ hnm htwo s (tors_laQ hs)).1
  have hA2 := (GlobalTheory.T.algebraicTaylor_torsionTranslate_evenTheta g.abelian₂ hlat halg t₀ hnm htwo _ (tors_laQ (tors_two hs))).1
  have hA0 := alg_th hlat halg hnm htwo
  have hs1 := halg _ (tors_laQ hs)
  obtain ⟨τ, a1, -, a3, a4, a5⟩ := exists_tau hok hlat hdisc h2 h3 halg htr hs
  obtain ⟨H, b1, -, b2⟩ := transl_sq hok hlat hdisc h2 h3 hwp halg hnm htwo htr hx hs
  have hE2 := int_E_sq hok hlat hdisc h2 h3 hwp halg hnm htwo hf hx
  obtain ⟨hf0, -⟩ := atU_th_sq hok hlat h2 h3 hwp halg hnm htwo
  have q1 := ((GlobalTheory.SerTransport.transport 2 g).2.2.1 _ hAs).1
  have q2 := ((GlobalTheory.SerTransport.transport 2 g).2.2.1 _ hA2).1
  have hc0 : U1 g.abelian₂ s (sgStar g.abelian₂) 0 ≠ 0 := by
    intro h
    rw [h, lamC_coe _ (zero_mem _)] at a4
    exact zero_ne_one ((norm_zero.symm.trans (congrArg norm (map_zero g.lam).symm)).trans a4)
  obtain ⟨c₁, c₂, hc1, hc2, hid⟩ : ∃ c₁ c₂ : ℂ, c₁ ∈ Qbar ∧ c₂ ∈ Qbar ∧ (fun z =>
      U1 g.abelian₂ t (GL3Theta.th0 g.abelian₂ t₀) z * GL3Theta.th0 g.abelian₂ t₀ z) = fun z =>
      c₁ * U1 g.abelian₂ s (GL3Theta.th0 g.abelian₂ t₀) z ^ 2 + c₂ * U1 g.abelian₂ s (sgStar g.abelian₂) z ^ 2 := by
    refine ⟨U1 g.abelian₂ s (GL3Theta.th0 g.abelian₂ t₀) 0 ^ 2 / κ, (U1 g.abelian₂ (2 * s) (GL3Theta.th0 g.abelian₂ t₀) 0 -
      U1 g.abelian₂ s (GL3Theta.th0 g.abelian₂ t₀) 0 ^ 4) / (U1 g.abelian₂ s (sgStar g.abelian₂) 0 ^ 2 * κ),
      div_mem (pow_mem q1 _) hκ, div_mem (sub_mem q2 (pow_mem q1 _)) (mul_mem (pow_mem a3 _) hκ),
      funext fun z => ?_⟩
    have := GlobalTheory.T.U1_two_mul_th0_mul_th0_eq g.abelian₂ hlat t₀ hnm htwo s hs.1 z
    rw [hκe z] at this
    field_simp
    linear_combination this
  have e := (atU_mul g hA hA0).2
  have m1 := atU_smul g hc1 (atU_sq g hAs).1
  have m2 := atU_smul g hc2 (atU_sq g hs1).1
  rw [hid, (atU_add g m1.1 m2.1).2, m1.2, m2.2, (atU_sq g hAs).2, (atU_sq g hs1).2, a5, b2, mul_pow] at e
  have hb := (((bdd_C (lamC g.lam c₁)).mul (hE2.mul b1).bdd).add
    ((bdd_C (lamC g.lam c₂)).mul (hE2.mul a1.sq).bdd)).mul (hf.inv (by rw [hf0, norm_one])).bdd
  rwa [e, mul_assoc, PowerSeries.mul_inv_cancel _ (by rw [hf0]; exact one_ne_zero), mul_one] at hb

include hok hlat hdisc h2 h3 hwp halg hnm htwo htr hf hx in

theorem transl_int {t : ℂ} (ht : GL3Theta.Tors1 2 g.abelian₂ t) :
    IntSer (g.atU (U1 g.abelian₂ t (GL3Theta.th0 g.abelian₂ t₀))) ∧
      ¬ ∃ ρ : ℝ, ρ < 1 ∧ ∀ n, ‖PowerSeries.coeff n (g.atU (U1 g.abelian₂ t (GL3Theta.th0 g.abelian₂ t₀)))‖ ≤ ρ := by
  obtain ⟨-, -, -, hE, -⟩ := GlobalTheory.EvenTheta.DatumBasic.datum_basic 2 g hok hlat h2 h3 hdisc
  obtain ⟨H, b1, b3, b2⟩ := transl_sq hok hlat hdisc h2 h3 hwp halg hnm htwo htr hx ht
  have hE2 := int_E_sq hok hlat hdisc h2 h3 hwp halg hnm htwo hf hx
  have hi := int_of_sq (transl_bdd hok hlat hdisc h2 h3 hwp halg hnm htwo htr hf hx ht)
    (by rw [b2]; exact hE2.mul b1)
  refine ⟨hi, ?_⟩
  rintro ⟨ρ, hρ, h⟩
  have h0 : PowerSeries.constantCoeff (ePhi1 g.lam g.abelian₂ g.C g.wq ^ 2) = 1 := by rw [map_pow, hE, one_pow]
  have k1 := (GlobalTheory.EvenTheta.SerRing.series_ring_laws 2).2.2.2.2.2.2 _ _ _ _ hi h
  have k2 := (GlobalTheory.EvenTheta.SerRing.series_ring_laws 2).2.2.2.2.2.2 _ _ _ _ (hE2.inv (by rw [h0, norm_one])) k1
  rw [← _root_.sq, b2, ← mul_assoc, PowerSeries.inv_mul_cancel _ (by rw [h0]; exact one_ne_zero),
    one_mul] at k2
  rcases b3 with b | b
  · linarith [k2 0]
  · linarith [k2 1]

end Two

theorem atTwo : ∀ D : D7, GL3Theta.atTwo D := by
  intro D cc δ g hg t₀ ht₀
  have htr := GlobalTheory.T.cm_theta_torsion_translate_integral_series D 2 cc δ g hg
  have hend := (GlobalTheory.T.cmThetaPoints_integral_norm_conjugate_laws D).1 2 cc δ g hg
  obtain ⟨hcc, -, hδ, hΛ, hok⟩ := hg
  have hcrv : Crv D cc δ := ⟨hcc, hδ⟩
  have hG := (GlobalTheory.InducedType.induced_type D).1
  obtain ⟨hlat, -, hdisc, -, hst⟩ := GlobalTheory.CurveLattice.lattice_of_curve D hG cc δ hcrv
  obtain ⟨⟨-, h2, h3⟩, hwp⟩ := (GlobalTheory.CurveAlgebraic.integral_j_and_algebraic_data D hG).2 cc δ hcrv
  have huse := (GlobalTheory.ThetaConj.cmTheta_taylorCoeff_algebraic_and_conjugate D cc δ hcrv).1
  simp only [tor0] at h2 h3
  rw [← hΛ] at hlat hdisc hst h2 h3 hwp huse
  obtain ⟨a, β, k, ha, hβ, hn, htrc, hN, hb⟩ := GlobalTheory.T.exists_traceOne_evenNorm_unit_at_two D g.lam
  obtain ⟨hb1, hb2⟩ := hb _ _ ht₀
  have hst' : ∀ ω ∈ g.abelian₂, β * ω ∈ g.abelian₂ := fun ω hω => ha ▸ hst a ω hω
  have hnm : t₀ ∉ g.abelian₂ := fun h => hb1 (hst' _ h)
  have hlat' : IsLat g.abelian₂ := hlat
  have halg : ∀ x, InRationalLattice g.abelian₂ x → AlgEnt (U1 g.abelian₂ x (sgStar g.abelian₂)) := fun x hx => ⟨by
    have := hlat'.differentiable
    unfold U1
    fun_prop, huse x hx⟩
  have hwp' : ∀ t, InRationalLattice g.abelian₂ t → t ∉ g.abelian₂ → wpF g.abelian₂ t ∈ Qbar := fun t h h' => (hwp t h h').1
  have hint := hend _ (subset_closure ⟨a, rfl⟩)
  simp only [GL3Theta.tauK, ha] at hint
  obtain ⟨hf, hx⟩ := int_th hok hlat' hdisc h2 h3 hwp' halg hnm ht₀.1 hβ hn hst' htrc hN hb1 hb2 hint
  obtain ⟨hf0, -⟩ := atU_th_sq hok hlat' h2 h3 hwp' halg hnm ht₀.1
  refine ⟨?_, fun t ht => ?_⟩
  · obtain ⟨e1, e2⟩ := GlobalTheory.ExpLogMv.expMv_neg_logMv_mul 2 Unit (g.atU (GL3Theta.th0 g.abelian₂ t₀)) hf0
    refine ⟨by rw [sub_zero, map_neg, e1, neg_zero], ?_⟩
    rw [sub_zero]
    have e3 : (expMv (-GL3Theta.logMv (g.atU (GL3Theta.th0 g.abelian₂ t₀))) : PowerSeries ℂ_[2]) =
        (g.atU (GL3Theta.th0 g.abelian₂ t₀))⁻¹ :=
      (PowerSeries.eq_inv_iff_mul_eq_one (by rw [hf0]; exact one_ne_zero)).2 e2
    exact intSer_iff.2 (e3 ▸ hf.inv (by rw [hf0, norm_one]))
  · obtain ⟨k1, k2⟩ := transl_int hok hlat' hdisc h2 h3 hwp' halg hnm ht₀.1 htr hf hx ht
    exact ⟨intSer_iff.2 k1, k2⟩

end GlobalTheory.EvenTheta
