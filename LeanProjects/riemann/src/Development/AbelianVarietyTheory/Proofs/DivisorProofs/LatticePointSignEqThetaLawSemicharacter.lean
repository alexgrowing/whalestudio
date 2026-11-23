import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusHermitianFormScaledCoordinateEq
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IdealPeriodLatticeOfCurveDatum
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsSemicharacterCompletedSelfDualLattice
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RationalPointFinitePartIsotropicPairing
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSelfDualLatticeSemicharacterVacuumStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StdCharFiniteAdeleRationalEqExpTraceStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CmTraceEqAddStarStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RationalHomHermitianTraceFormSelfEqFrameNormSumStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField Matrix MvPolynomial
open GlobalTheory.SignedHC GlobalTheory.ChiGrid Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.FunObj
attribute [local instance] Formalism.BasicNotions.Host.cmStar

open scoped TensorProduct

noncomputable section

namespace GlobalTheory.ThetaSignLat

variable {D : D7}

theorem semichar_value : ∀ {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)), IsStdChar D ψ (-1) → IsSelfDualC S ΛS → IsSelfDualC T ΛT → ∀ b : 𝓞 D.host.E, (b : D.host.E) + star (b : D.host.E) = 1 → ∃ χ : WO S T → ℂ, IsLatVac (heisO ψ S T) (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True) χ ∧ ∀ l ∈ latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) (fun _ => True), χ l = ψ (symplOH S T (l.map fun z => incA D (b : D.host.E) * z) l) := GlobalTheory.T.exists_selfDualLattice_semicharacter_vacuum

theorem psi_fin_rat : ∀ {D : D7} (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ q : D.host.F, ψ (pairA D.host.F 0 (algebraMap D.host.F (Af D.host.F) q)) = Complex.exp (2 * Real.pi * Complex.I * ∑ τ, tauE D τ (q : D.host.E)) := GlobalTheory.T.stdChar_finiteAdele_rational_eq_exp_trace

theorem trace_eq_add_star : ∀ {D : D7} (x : D.host.E), ((Algebra.trace D.host.F D.host.E x : D.host.F) : D.host.E) = x + star x := GlobalTheory.T.cmTrace_eq_add_star

theorem hRat_frame : ∀ {D : D7} (S T : HSp D) (frS : GL (Fin S.rank) D.host.E) (frT : GL (Fin T.rank) D.host.E), Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) frS.1 * S.gram * frS.1 = 1 → Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) frT.1 * T.gram * frT.1 = 1 → ∀ v : Matrix (Fin T.rank) (Fin S.rank) D.host.E, GlobalTheory.LatVac.hRat S T v v = ∑ a, ∑ b, star (((frT⁻¹ : GL (Fin T.rank) D.host.E).1 * v * frS.1) a b) * ((frT⁻¹ : GL (Fin T.rank) D.host.E).1 * v * frS.1) a b := GlobalTheory.T.rationalHomHermitianTraceForm_self_eq_frame_normSum

theorem sign_of_exp (t : ℝ)
    (h : Complex.exp (-(Real.pi : ℂ) * Complex.I * t) = 1 ∨ Complex.exp (-(Real.pi : ℂ) * Complex.I * t) = -1) :
    (-1 : ℂ) ^ (round t) = Complex.exp (-(Real.pi : ℂ) * Complex.I * t) := by
  have h2 : Complex.exp (2 * (-(Real.pi : ℂ) * Complex.I * t)) = 1 := by
    rw [show (2 : ℂ) = ((2 : ℕ) : ℂ) by norm_num, Complex.exp_nat_mul]
    rcases h with h | h <;> rw [h] <;> norm_num
  obtain ⟨n, hn⟩ := Complex.exp_eq_one_iff.1 h2
  have hπ : (2 * (Real.pi : ℂ) * Complex.I) ≠ 0 := by
    have : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    simp [this, Complex.I_ne_zero]
  have h3 : (2 * (Real.pi : ℂ) * Complex.I) * ((t : ℂ) + n) = 0 := by linear_combination (-1 : ℂ) * hn
  have h4 : (t : ℂ) = -((n : ℤ) : ℂ) := by
    have := (mul_eq_zero.1 h3).resolve_left hπ
    linear_combination this
  have ht : t = ((-n : ℤ) : ℝ) := by
    push_cast
    exact_mod_cast h4
  rw [ht, round_intCast]
  have e1 : (-1 : ℂ) ^ (-n) = (-1) ^ n := by rw [_root_.zpow_neg, ← _root_.inv_zpow, inv_neg, inv_one]
  have e2 : -(Real.pi : ℂ) * Complex.I * (((-n : ℤ) : ℝ) : ℂ) = n * ((Real.pi : ℂ) * Complex.I) := by
    push_cast; ring
  rw [e1, e2, Complex.exp_int_mul, Complex.exp_pi_mul_I]

theorem host_facts (D : D7) : (Ideal.absNorm D.host.ccK : D.host.E) ≠ 0 ∧ D.host.sqrtMinusD ≠ 0 ∧
    D.host.xi0 * D.host.sqrtMinusD = -1 / (Ideal.absNorm D.host.ccK : D.host.E) ∧ star D.host.xi0 = -D.host.xi0 := by
  obtain ⟨-, hN1, -⟩ := ReciprocityTheory.ChartRestriction.G.PullbackSections.PfModelDataX.xiR_facts D
  have hN : Ideal.absNorm D.host.ccK ≠ 0 := by
    intro h0; rw [h0, Nat.cast_zero] at hN1; linarith
  have hN0 : (Ideal.absNorm D.host.ccK : D.host.E) ≠ 0 := by exact_mod_cast hN
  have hsq := D.host.sqd_sq
  have hs0 : D.host.sqrtMinusD ≠ 0 := by
    intro h0
    have hd0 : D.host.d ≠ 0 := by
      intro h; have := D.host.hyp.2.2.2.1; rw [h] at this; norm_num at this
    have e : (D.host.d : D.host.E) = 0 := by
      have h' : D.host.sqrtMinusD ^ 2 = -(D.host.d : D.host.E) := hsq
      rw [h0] at h'
      linear_combination h'
    exact hd0 (by exact_mod_cast e)
  refine ⟨hN0, hs0, ?_, ?_⟩
  · show -1 / ((Ideal.absNorm D.host.ccK : D.host.E) * D.host.sqrtMinusD) * D.host.sqrtMinusD = _
    field_simp
  · show star (-1 / ((Ideal.absNorm D.host.ccK : D.host.E) * D.host.sqrtMinusD)) =
      -(-1 / ((Ideal.absNorm D.host.ccK : D.host.E) * D.host.sqrtMinusD))
    rw [star_div₀, star_neg, star_one, star_mul', star_natCast, GlobalTheory.FockCompare.RealChart.star_sqrtMinusD]
    field_simp

theorem trace_val (n b : D.host.E) (hns : star n = n) (hbv : b = (1 + D.host.sqrtMinusD) / 2) :
    ((1 / 2 * Algebra.trace D.host.F D.host.E (D.host.xi0 * (b * n)) : D.host.F) : D.host.E) =
      -n / (2 * (Ideal.absNorm D.host.ccK : D.host.E)) := by
  obtain ⟨hN0, hs0, hxs, hxstar⟩ := host_facts D
  have h2s : star (2 : D.host.E) = 2 := by
    have := star_natCast (R := D.host.E) 2
    exact_mod_cast this
  have hbs : star b = 1 - b := by
    rw [hbv, star_div₀, star_add, star_one, h2s, GlobalTheory.FockCompare.RealChart.star_sqrtMinusD]
    ring
  have htr : ((Algebra.trace D.host.F D.host.E (D.host.xi0 * (b * n)) : D.host.F) : D.host.E) =
      -n / (Ideal.absNorm D.host.ccK : D.host.E) := by
    rw [GlobalTheory.ThetaSignLat.trace_eq_add_star, star_mul', star_mul', hxstar, hbs, hns]
    have e : D.host.xi0 * (b * n) + -D.host.xi0 * ((1 - b) * n) =
        (D.host.xi0 * D.host.sqrtMinusD) * n := by rw [hbv]; ring
    rw [e, hxs]; ring
  have hc : ((1 / 2 * Algebra.trace D.host.F D.host.E (D.host.xi0 * (b * n)) : D.host.F) : D.host.E) =
      ((1 / 2 : D.host.F) : D.host.E) * ((Algebra.trace D.host.F D.host.E (D.host.xi0 * (b * n)) : D.host.F) : D.host.E) := rfl
  have h12 : ((1 / 2 : D.host.F) : D.host.E) = 1 / 2 := by
    rw [show ((1 / 2 : D.host.F) : D.host.E) = D.host.F.subtype (1 / 2) from rfl, map_div₀, map_one, map_ofNat]
  rw [hc, h12, htr]
  field_simp

theorem hRat_smul_left (S T : HSp D) (c : D.host.E) (M N : Matrix (Fin T.rank) (Fin S.rank) D.host.E) :
    GlobalTheory.LatVac.hRat S T (Matrix.of fun i j => c * M i j) N = c * GlobalTheory.LatVac.hRat S T M N := by
  unfold GlobalTheory.LatVac.hRat
  simp only [Finset.mul_sum, Matrix.of_apply]
  refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ =>
    Finset.sum_congr rfl fun _ _ => by ring

theorem hRat_neg_neg (S T : HSp D) (M : Matrix (Fin T.rank) (Fin S.rank) D.host.E) :
    GlobalTheory.LatVac.hRat S T (-M) (-M) = GlobalTheory.LatVac.hRat S T M M := by
  unfold GlobalTheory.LatVac.hRat
  simp only [Matrix.neg_apply, star_neg]
  refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ =>
    Finset.sum_congr rfl fun _ _ => by ring

theorem coord_entry (S T : HSp D) (frS : GL (Fin S.rank) D.host.E) (frT : GL (Fin T.rank) D.host.E)
    (v : Matrix (Fin T.rank) (Fin S.rank) D.host.E) (τ : D.what₂.Tau) :
    (GlobalTheory.FockPos.frAt frT τ)⁻¹ * Matrix.of (GlobalTheory.VacUnique.infRat S T v τ) * GlobalTheory.FockPos.frAt frS τ =
      ((frT⁻¹ : GL (Fin T.rank) D.host.E).1 * v * frS.1).map (tauE D τ) := by
  have hinv : (GlobalTheory.FockPos.frAt frT τ)⁻¹ = (frT⁻¹ : GL (Fin T.rank) D.host.E).1.map (tauE D τ) := by
    refine Matrix.inv_eq_left_inv ?_
    rw [GlobalTheory.FockPos.frAt, ← Matrix.map_mul, Units.inv_mul]
    exact Matrix.map_one _ (map_zero _) (map_one _)
  rw [hinv, Matrix.map_mul, Matrix.map_mul]
  rfl

theorem sign_eq_alpha : ∀ {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (frS : GL (Fin S.rank) D.host.E) (frT : GL (Fin T.rank) D.host.E), Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) frS.1 * S.gram * frS.1 = 1 → Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) frT.1 * T.gram * frT.1 = 1 → IsStdChar D ψ (-1) → ∀ δ : ℂ, δ ≠ 0 → ∀ v : Matrix (Fin T.rank) (Fin S.rank) D.host.E, GlobalTheory.VacUnique.finRat S T v ∈ latO S T (colLat frS : Set (Fin S.rank → D.host.E)) (colLat frT : Set (Fin T.rank → D.host.E)) (fun _ => True) → ∀ ε : ℂ, (∀ g : WO S T → ℂ, IsLatVac (heisO ψ S T) (latO S T (colLat frS : Set (Fin S.rank → D.host.E)) (colLat frT : Set (Fin T.rank → D.host.E)) (fun _ => True)) g → heisO ψ S T (GlobalTheory.VacUnique.finRat S T (-v)) g = ε • g) → ψ (-symplOH S T (ratW T S v) (GlobalTheory.VacUnique.finRat S T (-v))) * ε = Formalism.MainNotions.TaylorLogMetric.al D (Formalism.MainNotions.TaylorLogMetric.tor0 D D.host.ccK δ) (δ • (fun τ a b => ((GlobalTheory.FockPos.frAt frT τ)⁻¹ * Matrix.of (GlobalTheory.VacUnique.infRat S T v τ) * GlobalTheory.FockPos.frAt frS τ) a b)) := by
  intro D ψ S T frS frT hS hT hψ δ hδ v hv ε hε
  set L := latO S T (colLat frS : Set (Fin S.rank → D.host.E)) (colLat frT : Set (Fin T.rank → D.host.E))
    (fun _ => True) with hL
  have hSd := GlobalTheory.FunObj.VecEx.isSelfDualC_colLat S frS hS
  have hTd := GlobalTheory.FunObj.VecEx.isSelfDualC_colLat T frT hT
  set u : WO S T := GlobalTheory.VacUnique.finRat S T (-v) with hu
  have huL : u ∈ L := by
    rw [hu, map_neg]; exact L.neg_mem hv

  have hsq := D.host.sqd_sq
  let b : 𝓞 D.host.E := ⟨(1 + D.host.sqrtMinusD) / 2,
    GlobalTheory.NormSum.isIntegral_half_one_add D.host.d D.host.hyp.2.2.2.1 _ hsq⟩
  have hbv : (b : D.host.E) = (1 + D.host.sqrtMinusD) / 2 := rfl
  have h2s : star (2 : D.host.E) = 2 := by
    have := star_natCast (R := D.host.E) 2
    exact_mod_cast this
  have hbs : star (b : D.host.E) = 1 - (b : D.host.E) := by
    rw [hbv, star_div₀, star_add, star_one, h2s, GlobalTheory.FockCompare.RealChart.star_sqrtMinusD]
    ring
  have hb : (b : D.host.E) + star (b : D.host.E) = 1 := by rw [hbs]; ring
  obtain ⟨χ, hχ, hval⟩ := GlobalTheory.ThetaSignLat.semichar_value ψ S T (colLat frS) (colLat frT) hψ hSd hTd b hb
  obtain ⟨f1, -, f3, -⟩ := GlobalTheory.T.homSymplecticHalfForm_algebraic_laws_continuous D S T
  have hz : ∀ w : WO S T, symplOH S T 0 w = 0 := fun w => by
    have := f1 0 0 w
    rw [add_zero] at this
    exact left_eq_add.1 this
  have e1 : ∀ g : WO S T → ℂ, heisO ψ S T u g 0 = g u := fun g => by
    show ψ (symplOH S T 0 u) * g (0 + u) = g u
    rw [hz, AddChar.map_zero_eq_one, one_mul, zero_add]
  have e0 : χ 0 = 1 := by
    rw [hval 0 (zero_mem _)]
    have : ((0 : WO S T).map fun z => incA D (b : D.host.E) * z) = 0 := by
      funext i j; exact mul_zero _
    rw [this, f3, AddChar.map_zero_eq_one]
  have hεu : ε = χ u := by
    have := congrFun (hε χ hχ) 0
    rw [e1] at this
    rw [this, Pi.smul_apply, e0, smul_eq_mul, mul_one]
  have hpm : ε = 1 ∨ ε = -1 := by
    obtain ⟨ε', h1, h2⟩ := (GlobalTheory.T.self_dual_lattice_pairing_dual D ψ S T (colLat frS) (colLat frT) hψ hSd hTd).2.2 χ hχ u huL
    have := congrFun (h2 χ hχ) 0
    rw [e1, Pi.smul_apply, e0, smul_eq_mul, mul_one] at this
    rw [hεu, this]; exact h1

  set Y : Matrix (Fin T.rank) (Fin S.rank) D.host.E := (frT⁻¹ : GL (Fin T.rank) D.host.E).1 * v * frS.1 with hY
  set n : D.host.E := ∑ a, ∑ b, star (Y a b) * Y a b with hn
  have hns : star n = n := by
    rw [hn, star_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [star_sum]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [star_mul', star_star, mul_comm]
  have hmap : (u.map fun z => incA D (b : D.host.E) * z) =
      GlobalTheory.LatVac.finTens 1 (Matrix.of fun i j => (b : D.host.E) * (-v) i j) := by
    funext i j
    show ((1 : AF D.host.F) ⊗ₜ[D.host.F] (b : D.host.E)) * (pairA D.host.F 0 1 ⊗ₜ[D.host.F] ((-v) i j)) =
      pairA D.host.F 0 1 ⊗ₜ[D.host.F] ((b : D.host.E) * (-v) i j)
    rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul]
  have hu' : u = GlobalTheory.LatVac.finTens 1 (-v) := rfl
  have hs : symplOH S T (u.map fun z => incA D (b : D.host.E) * z) u = pairA D.host.F 0
      (algebraMap D.host.F (Af D.host.F) (1 / 2 * Algebra.trace D.host.F D.host.E (D.host.xi0 * ((b : D.host.E) * n)))) := by
    rw [hmap, hu', symplOH, GlobalTheory.LatVac.symplO_finTens, hRat_smul_left, hRat_neg_neg,
      GlobalTheory.ThetaSignLat.hRat_frame S T frS frT hS hT v]
    refine Prod.ext (mul_zero _) ?_
    show algebraMap D.host.F (Af D.host.F) (1 / 2) * (1 * 1 * _) = _
    rw [one_mul, one_mul, ← RingHom.map_mul]
    rfl

  have hq := trace_val n (b : D.host.E) hns hbv
  have hχu : χ u = Complex.exp (2 * Real.pi * Complex.I * ∑ τ, tauE D τ
      ((1 / 2 * Algebra.trace D.host.F D.host.E (D.host.xi0 * ((b : D.host.E) * n)) : D.host.F) : D.host.E)) := by
    rw [hval u huL, hs, GlobalTheory.ThetaSignLat.psi_fin_rat ψ hψ]
  obtain ⟨c, hc⟩ : ∃ c : ℂ, c = ∑ τ, tauE D τ n := ⟨_, rfl⟩
  have hsumq : ∑ τ, tauE D τ
      ((1 / 2 * Algebra.trace D.host.F D.host.E (D.host.xi0 * ((b : D.host.E) * n)) : D.host.F) : D.host.E) =
        -c / (2 * (Ideal.absNorm D.host.ccK : ℂ)) := by
    have : ∀ τ, tauE D τ
        ((1 / 2 * Algebra.trace D.host.F D.host.E (D.host.xi0 * ((b : D.host.E) * n)) : D.host.F) : D.host.E) =
          -(tauE D τ n) / (2 * (Ideal.absNorm D.host.ccK : ℂ)) := fun τ => by
      rw [hq, map_div₀, map_neg, map_mul, map_natCast, map_ofNat]
    rw [Finset.sum_congr rfl fun τ _ => this τ, ← Finset.sum_div, Finset.sum_neg_distrib, hc]
  have hcre : ((c.re : ℝ) : ℂ) = c := by
    have : starRingEnd ℂ c = c := by
      rw [hc, map_sum]
      refine Finset.sum_congr rfl fun τ _ => ?_
      rw [← GlobalTheory.FockCompare.tauE_star, hns]
    exact Complex.conj_eq_iff_re.1 this
  obtain ⟨hxi, hN1, hd1⟩ := ReciprocityTheory.ChartRestriction.G.PullbackSections.PfModelDataX.xiR_facts D
  have hNC : (Ideal.absNorm D.host.ccK : ℂ) ≠ 0 := by
    have : Ideal.absNorm D.host.ccK ≠ 0 := by
      intro h0; rw [h0, Nat.cast_zero] at hN1; linarith
    exact_mod_cast this
  have hNR : (Ideal.absNorm D.host.ccK : ℝ) ≠ 0 := by linarith
  have hdR : Real.sqrt D.host.d ≠ 0 := by linarith
  have hεt : ε = Complex.exp (-(Real.pi : ℂ) * Complex.I * ((c.re / Ideal.absNorm D.host.ccK : ℝ) : ℂ)) := by
    rw [hεu, hχu, hsumq]
    congr 1
    push_cast
    rw [hcre]
    field_simp
  have hX : (fun τ a b => ((GlobalTheory.FockPos.frAt frT τ)⁻¹ * Matrix.of (GlobalTheory.VacUnique.infRat S T v τ) *
      GlobalTheory.FockPos.frAt frS τ) a b) = fun τ a b => tauE D τ (Y a b) := by
    funext τ a b
    rw [coord_entry]
    rfl
  have hsum : (∑ τ, ∑ a, ∑ b, tauE D τ (Y a b) * starRingEnd ℂ (tauE D τ (Y a b))) = c := by
    rw [hc]
    refine Finset.sum_congr rfl fun τ _ => ?_
    rw [hn, map_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [map_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [map_mul, GlobalTheory.FockCompare.tauE_star, mul_comm]
  have h0 := GlobalTheory.RatFinIso.symplOH_ratW_finRat_neg S T v
  rw [← hu] at h0
  rw [h0, neg_zero, AddChar.map_zero_eq_one, one_mul, hX, Formalism.MainNotions.TaylorLogMetric.al, GlobalTheory.ThetaLawOF.torusHermitianForm_scaled_coordinate_eq hδ, hsum]
  have hre : Real.sqrt D.host.d / 2 * (2 * ((Formalism.L2.Pj.xiR D : ℝ) : ℂ) * c).re = c.re / Ideal.absNorm D.host.ccK := by
    rw [show (2 * ((Formalism.L2.Pj.xiR D : ℝ) : ℂ) * c) = ((2 * Formalism.L2.Pj.xiR D : ℝ) : ℂ) * c by push_cast; ring,
      Complex.re_ofReal_mul, hxi]
    field_simp
  rw [hre, hεt]
  exact (GlobalTheory.ThetaSignLat.sign_of_exp _ (by rw [← hεt]; exact hpm)).symm

end GlobalTheory.ThetaSignLat
