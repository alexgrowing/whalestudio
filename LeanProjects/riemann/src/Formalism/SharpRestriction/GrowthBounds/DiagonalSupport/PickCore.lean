import Formalism.SharpRestriction.GrowthBounds.DiagonalSupport.PickVal

noncomputable section

open MvPolynomial Finset Classical

namespace Formalism.MainNotions.Proposition5Numerics

open Formalism.MainNotions.G Formalism.GradedWeylDivisibility Formalism.MainNotions.SourceCleaning Formalism.MainNotions.Pf14 Formalism.MainNotions.PlaneGramData Formalism.MainNotions.TestSideCounting Formalism.MainNotions.TestSideWords Formalism.MainNotions.G.GLWeightTheory

theorem gram_exponent_arithmetic (VC VP VN VU M0 T n1 nn Dno Dn q1 q2 q3 c2 : ℝ) (h1 : q3 ≤ q2 + VP / 2) (h2 : q2 + c2 = q1)
    (h3 : c2 = VU / 2) (h4 : q1 ≤ VN / 2) (h5 : M0 = VC + VP + VN) (h6 : M0 ≤ T)
    (h7 : Dno + (n1 - VP) / 2 + (nn - VN) / 2 ≤ Dn) :
    VC + (nn / 2 + Dno - VU / 2) + VU + q3 ≤ T - n1 / 2 + Dn := by
  linarith

theorem thL_arith (a b c : ℝ) (h1 : 3 / 8 * a < b / 2) (h2 : b / 2 ≤ c) : 0 < c - 3 / 8 * a := by
  linarith

theorem fact_arith (a b c d : ℤ) (h : a = b + c + d + 0 + 0) : a = b + c + d := by
  omega

theorem pick_core (p : ℕ) [hpF : Fact p.Prime] {n' r K m : ℕ} [NeZero n'] [NeZero r] [NeZero K] (O : Type) [CommRing O]
    [IsDomain O] [IsDiscreteValuationRing O] (S : UniformizedDVR p O) (w : O) (hw2 : w ^ 2 = (p : O))
    (hk : m + 1 = r + K) (Fr : Frames n' r) (deg : Fin n' → ℕ) (Y : ℝ) (N₁ G' cP : ℕ)
    (d : Fin n' → ℕ) (Dn : ℝ) {J : ℕ} [NeZero J] (Dt : SignedChainData p O r J) (dPl dNo : TL J Dt.nL r → ℕ)
    (ka : ZMod J → ℕ → Fin K → ℤ) (rho : TL J Dt.nL r × Fin (r + K) → ℕ)
    (hTP : SignedChainDegreeCondition p O Fr deg Y N₁ G' cP Dt dPl ka) (hBlk : BlockOK Fr p Dt.nL d rho dPl dNo)
    (hDig : DigFacts Fr p O hk Dt.nL d)
    (hgnU : ∀ bn : TL J Dt.nL r × Fin K →₀ ℕ, gamNo Fr p Dt.nL rho bn ≠ 0 ∧ padicValRat p (gamNo Fr p Dt.nL rho bn) = 0)
    (hgpU : ∀ bp : TL J Dt.nL r × Fin r →₀ ℕ, gamPl Fr p Dt.nL rho bp ≠ 0 ∧ padicValRat p (gamPl Fr p Dt.nL rho bp) = 0)
    (hgaeq : ∀ al, algebraMap O (KK O) (Dt.ga al) = ((gamPl Fr p Dt.nL rho al : ℚ) : KK O))
    (e : Module.End (KK O) (MvPolynomial (TL J Dt.nL r × Fin K) (KK O))) (hJPOK : JPOK p O Dt dNo ka e)
    (hNo : NoAt (K := K) p O Fr cP Dt) (hSz : SizeAt (K := K) p Fr Dt.nL d Dn)
    (G : MvPolynomial (TV n' (m + 1)) (KK O)) (hdeg : HasMultideg G d) (hGint : CoefGe p G 0)
    (hMem : MemAt p O hk Fr deg Y N₁ G' cP G)
    (mo0 : TV n' (m + 1) →₀ ℕ) (hmo0 : vK p (G.coeff mo0) = 0) (hmo0d : ∀ s, multideg mo0 s = d s)
    (bp0 : TL J Dt.nL r × Fin r →₀ ℕ) (bn0 : TL J Dt.nL r × Fin K →₀ ℕ)
    (hcoef : ((levImg Fr p hk Dt.nL rho dPl dNo G).coeff bp0).coeff bn0 = G.coeff mo0)
    (hdp : ∀ x, multideg bp0 x = dPl x) (hdn : ∀ x, multideg bn0 x = dNo x)
    (hfact : ((expFact mo0 : ℕ) : ℚ) = ((cstOf Fr p Dt.nL rho dPl dNo : ℕ) : ℚ) *
        ((expFact bp0 : ℕ) : ℚ) * ((expFact bn0 : ℕ) : ℚ) * gamPl Fr p Dt.nL rho bp0 * gamNo Fr p Dt.nL rho bn0)
    (hvle : vBB (O := O) p (e ((levImg Fr p hk Dt.nL rho dPl dNo G).coeff bp0)) ≤
      vBB (O := O) p ((levImg Fr p hk Dt.nL rho dPl dNo G).coeff bp0)) :
    PickAt p O hk Fr deg Y N₁ G' cP d (kapFl p (m + 1) d) Dn G := by
  have hp := hpF.out
  have : CharZero (KK O) := dvr_fraction_field_char_zero hp S
  have hy : (levImg Fr p hk Dt.nL rho dPl dNo G).coeff bp0 ∈ Pol (KK O) K dNo := (hDig G hdeg).2.1 rho dPl dNo bp0

  have hy1 : vBB (O := O) p ((levImg Fr p hk Dt.nL rho dPl dNo G).coeff bp0) ≤ (((padicValNat p (expFact bn0) : ℚ) / 2 : ℚ) : WithTop ℚ) := by
    have := vBB_le_coeff (p := p) ((levImg Fr p hk Dt.nL rho dPl dNo G).coeff bp0) bn0
    rwa [hcoef, hmo0, zero_add] at this
  obtain ⟨q1, hq1, hq1le⟩ := WithTop.le_coe_iff.1 (le_trans hvle hy1)
  obtain ⟨nu, hnus, hnu⟩ := vBB_attained (p := p) (e ((levImg Fr p hk Dt.nL rho dPl dNo G).coeff bp0)) (by rw [hq1]; exact WithTop.coe_ne_top)
  rw [hq1] at hnu
  obtain ⟨q2, c2, hq2, hc2, hq2c⟩ := WithTop.add_eq_coe.1 hnu.symm
  have hc2' : c2 = (padicValNat p (expFact nu) : ℚ) / 2 := by exact_mod_cast hc2
  obtain ⟨Pc, hPc⟩ : ∃ Pc, Pc = planeCoeff nu (oneT e (levImg Fr p hk Dt.nL rho dPl dNo G)) := ⟨_, rfl⟩
  have hPc0 : Pc.coeff bp0 = (e ((levImg Fr p hk Dt.nL rho dPl dNo G).coeff bp0)).coeff nu := by rw [hPc, coeff_planeCoeff, coeff_oneT]
  have hPc1 : vBB (O := O) p Pc ≤ ((q2 + (padicValNat p (expFact bp0) : ℚ) / 2 : ℚ) : WithTop ℚ) := by
    have := vBB_le_coeff (p := p) Pc bp0
    rwa [hPc0, ← hq2, ← WithTop.coe_add] at this
  obtain ⟨q3, hq3, hq3le⟩ := WithTop.le_coe_iff.1 hPc1
  obtain ⟨m3, hm3s, hm3⟩ := vBB_attained (p := p) Pc (by rw [hq3]; exact WithTop.coe_ne_top)
  obtain ⟨z, hzdef⟩ : ∃ z, z = Pc.coeff m3 * (algebraMap O (KK O) w) ^ (padicValNat p (expFact m3)) := ⟨_, rfl⟩
  have hz : vK p z = (q3 : WithTop ℚ) := by
    rw [hzdef, valuation_mul_alt, vK_w_pow hp S w hw2, ← hm3, hq3]
  have hz0 : z ≠ 0 := by
    rintro rfl
    rw [valuation_zero_alt] at hz
    exact WithTop.top_ne_coe hz
  have hvF2 : vBB (O := O) p (z⁻¹ • Pc) = 0 := by
    rw [vBB_smul _ (inv_ne_zero hz0), vK_inv z q3 hz, hq3, ← WithTop.coe_add]
    simp
  have hey : e ((levImg Fr p hk Dt.nL rho dPl dNo G).coeff bp0) ∈ Pol (KK O) K dNo := (hJPOK.2.2.1 _ hy).1
  have hnud : ∀ x, multideg nu x = dNo x := ((mem_restrictSupport_iff (KK O)).1 hey) hnus
  have hmonpol : (monomial nu (1 : KK O)) ∈ Pol (KK O) K dNo := by
    rw [Pol, mem_restrictSupport_iff]
    intro mo hmo
    have : mo = nu := by
      rw [Finset.mem_coe, mem_support_iff, coeff_monomial] at hmo
      by_contra h
      exact hmo (if_neg fun h' => h h'.symm)
    rw [this]
    exact hnud
  obtain ⟨N0, cY, hNT, hcY, hNerr⟩ := hNo dNo ka rho e nu hBlk.1 hJPOK hnud
  have hXX : Dt.XX (z⁻¹ • Pc) := by
    rw [hPc]
    exact XX_smul _ z⁻¹ (hMem J Dt dPl dNo ka hTP.1 rho e hJPOK.1 nu)
  refine ⟨J, inferInstance, Dt, dPl, dNo, ka, rho, z⁻¹ • Pc, N0,
    ((cstOf Fr p Dt.nL rho dPl dNo : ℕ) : KK O) * cY * ((expFact nu : ℕ) : KK O) * z, hTP, hBlk, hXX, hvF2, hNT, ?_, ?_⟩
  · have hE : ∀ {τ : Type} (al : τ →₀ ℕ), expFact al ≠ 0 := by
      intro τ al
      unfold expFact Finsupp.prod
      exact Finset.prod_ne_zero_iff.2 fun _ _ => Nat.factorial_ne_zero _
    have hcst0 : cstOf Fr p Dt.nL rho dPl dNo ≠ 0 := by
      unfold cstOf
      exact Nat.mul_ne_zero (Finset.prod_ne_zero_iff.2 fun _ _ => Nat.factorial_ne_zero _)
        (Finset.prod_ne_zero_iff.2 fun _ _ => pow_ne_zero _ (Nat.factorial_ne_zero _))
    have l1 : leQ (vK p ((cstOf Fr p Dt.nL rho dPl dNo : ℕ) : KK O)) (padicValNat p (cstOf Fr p Dt.nL rho dPl dNo) : ℝ) :=
      ⟨_, valuation_natCast_padicVal hp S _ hcst0, by push_cast; exact le_rfl⟩
    have l3 : leQ (vK p ((expFact nu : ℕ) : KK O)) (padicValNat p (expFact nu) : ℝ) :=
      ⟨_, valuation_natCast_padicVal hp S _ (hE nu), by push_cast; exact le_rfl⟩
    have l4 : leQ (vK p z) (q3 : ℝ) := ⟨q3, hz, le_rfl⟩
    refine leQ_mono ?_ (leQ_mul _ _ (leQ_mul _ _ (leQ_mul _ _ l1 hcY) l3) l4)
    have hfactV : (padicValNat p (expFact mo0) : ℤ) = (padicValNat p (cstOf Fr p Dt.nL rho dPl dNo) : ℤ) +
        padicValNat p (expFact bp0) + padicValNat p (expFact bn0) := by
      have ha : ((cstOf Fr p Dt.nL rho dPl dNo : ℕ) : ℚ) ≠ 0 := by exact_mod_cast hcst0
      have hb : ((expFact bp0 : ℕ) : ℚ) ≠ 0 := by exact_mod_cast hE bp0
      have hc : ((expFact bn0 : ℕ) : ℚ) ≠ 0 := by exact_mod_cast hE bn0
      have h := congrArg (padicValRat p) hfact
      rw [padicValRat.mul (mul_ne_zero (mul_ne_zero (mul_ne_zero ha hb) hc) (hgpU bp0).1) (hgnU bn0).1,
        padicValRat.mul (mul_ne_zero (mul_ne_zero ha hb) hc) (hgpU bp0).1,
        padicValRat.mul (mul_ne_zero ha hb) hc, padicValRat.mul ha hb, (hgnU bn0).2, (hgpU bp0).2,
        padicValRat.of_nat, padicValRat.of_nat, padicValRat.of_nat, padicValRat.of_nat] at h
      exact fact_arith _ _ _ _ h
    have hfactR : (padicValNat p (expFact mo0) : ℝ) = (padicValNat p (cstOf Fr p Dt.nL rho dPl dNo) : ℝ) +
        padicValNat p (expFact bp0) + padicValNat p (expFact bn0) := by exact_mod_cast hfactV
    have hM0 : (padicValNat p (expFact mo0) : ℝ) ≤ twiceValuationFactorialProduct p d := by
      unfold twiceValuationFactorialProduct
      exact_mod_cast padicVal_expFact_le p d mo0 hmo0d
    have hS := hSz rho dPl dNo hBlk bp0 bn0 hdp hdn
    have hn0 : Dt.n0 = (padicValNat p (∏ x, (dPl x).factorial) : ℝ) / 2 := by
      unfold SignedChainData.n0
      rw [hTP.1.2.2.2.1]
    have r1 : (q3 : ℝ) ≤ (q2 : ℝ) + (padicValNat p (expFact bp0) : ℝ) / 2 := by
      have h : ((q3 : ℚ) : ℝ) ≤ ((q2 + (padicValNat p (expFact bp0) : ℚ) / 2 : ℚ) : ℝ) := Rat.cast_le.2 hq3le
      push_cast at h
      exact h
    have r2 : (q2 : ℝ) + (c2 : ℝ) = (q1 : ℝ) := by exact_mod_cast hq2c
    have r3 : (c2 : ℝ) = (padicValNat p (expFact nu) : ℝ) / 2 := by rw [hc2']; push_cast; ring
    have r4 : (q1 : ℝ) ≤ (padicValNat p (expFact bn0) : ℝ) / 2 := by
      have h : ((q1 : ℚ) : ℝ) ≤ (((padicValNat p (expFact bn0) : ℚ) / 2 : ℚ) : ℝ) := Rat.cast_le.2 hq1le
      push_cast at h
      exact h
    rw [hn0]
    exact gram_exponent_arithmetic _ _ _ _ _ _ _ _ _ _ _ _ _ _ r1 r2 r3 r4 hfactR hM0 hS
  · intro A hA hAint
    have hex := value_exact Fr p O hk Dt.nL d hDig G hdeg rho dPl dNo hBlk.1
      (fun bn => by exact_mod_cast (hgnU bn).1) e hJPOK.2.1 nu cY (hJPOK.2.2.1 _ hmonpol).1 A hA
    have hBf : Dt.Bform (z⁻¹ • Pc) A =
        z⁻¹ * fock Pc (diagK (fun bp => ((gamPl Fr p Dt.nL rho bp : ℚ) : KK O)) A) := by
      have h1 : (fun bp => ((gamPl Fr p Dt.nL rho bp : ℚ) : KK O)) = fun bp => algebraMap O (KK O) (Dt.ga bp) :=
        funext fun bp => (hgaeq bp).symm
      rw [h1, ← fock_smul_left]
      rfl
    obtain ⟨Nex, hNex⟩ : ∃ Nex, Nex = diagK (fun bn => ((gamNo Fr p Dt.nL rho bn : ℚ) : KK O)⁻¹)
      (cY • e (monomial nu 1)) := ⟨_, rfl⟩
    rw [← hNex] at hex
    have hNerr' : CoefGe p (N0 - Nex) cP := by rw [hNex]; exact hNerr
    have hsub : fock G (asm Fr p O hk Dt.nL rho A N0) -
        ((cstOf Fr p Dt.nL rho dPl dNo : ℕ) : KK O) * cY * ((expFact nu : ℕ) : KK O) * z *
          Dt.Bform (z⁻¹ • Pc) A = fock G (asm Fr p O hk Dt.nL rho A (N0 - Nex)) := by
      have h2 : asm Fr p O hk Dt.nL rho A N0 =
          asm Fr p O hk Dt.nL rho A Nex + asm Fr p O hk Dt.nL rho A (N0 - Nex) := by
        rw [← asm_add_right]
        congr 1
        ring
      have h3 : z * z⁻¹ = 1 := mul_inv_cancel₀ hz0
      rw [h2, fock_add_right, hex, hBf, ← hPc]
      linear_combination (-(((cstOf Fr p Dt.nL rho dPl dNo : ℕ) : KK O) * cY * ((expFact nu : ℕ) : KK O) *
        fock Pc (diagK (fun bp => ((gamPl Fr p Dt.nL rho bp : ℚ) : KK O)) A))) * h3
    have hfin := geQ_fock S d G _ hdeg hGint (asm_coefGe' Fr p O hk Dt.nL rho hAint hNerr')
    rw [← hsub] at hfin
    exact hfin

end Formalism.MainNotions.Proposition5Numerics
