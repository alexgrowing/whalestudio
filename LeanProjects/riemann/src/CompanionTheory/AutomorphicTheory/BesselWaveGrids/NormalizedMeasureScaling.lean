import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.TBBTie
import Formalism.SharpRestriction.CuspSpanNormBounds.FrobeniusCoefficientMemLp.AmpBig
import Formalism.SharpRestriction.CuspSpanNormBounds.BridgeLemma3
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutLemB
import CompanionTheory.AutomorphicTheory.PieriRules.PieriDegreeBounds.BesselNormSqEqBigCellNormSqAltImports

noncomputable section

namespace CompanionTheory.WaveGrid.Ties

open MeasureTheory Formalism.BasicNotions Formalism.QuantumDeterminants Formalism.MainNotions.S Formalism.MainNotions.S.ThB Formalism.L2.SG.Pf.BesselExpansion Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open scoped ENNReal

section energy

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] {k r : ℕ}

theorem norm_JF_eq (Bs : B.RealPlaceData k r Wp Wq) (F : B.Mat k r → (Wq →L[ℂ] Wp)) (d : Fin (r + 1) → ℂ)
    (hd : ∀ a, d a ≠ 0) {γ γ' : B.Mat k r} (hγ : γ ∈ B.GV k r) (hγ' : γ' ∈ B.GV k r)
    (hZ : Zhat k r Bs.z Bs.z' γ = D.ptMatN (PBJ.bigPt d) (r + 1))
    (hZ' : Zhat k r Bs.z Bs.z' γ' = D.ptMatN (PBJ.bigPt d) (r + 1)) (hpos : 0 < Gf k r Bs.z Bs.z' γ) :
    ‖B.hsVec (B.JF Bs F γ)‖ = ‖B.hsVec (B.JF Bs F γ')‖ := by
  have hl : D.IsLocPt (PBJ.bigPt d) (r + 1) := PBJ.Dens.isLocPt_bigPt d hd
  have hpos' : 0 < Gf k r Bs.z Bs.z' γ' := by
    rw [← ptG_spec k r _ _ (PBJ.bigPt d) _ hl hZ', ptG_spec k r _ _ (PBJ.bigPt d) _ hl hZ]
    exact hpos
  obtain ⟨s, hs, s', hs', hγs⟩ := fibre_orbit_description k r Bs.z Bs.z'
    ⟨Bs.k_pos, Dx2.VV.std_vector_z Bs, Dx2.VV.std_vector_z_prime Bs⟩ _ hγ _ hγ' hpos (hZ.trans hZ'.symm)
  obtain ⟨hA, hhA, nA, hnA, hfA, rfl⟩ := Dx2.VV.stabilizer_decomp_unitary_mul_unipotent (Dx2.VV.std_vector_z Bs) hs
  obtain ⟨hB, hhB, nB, hnB, hfB, rfl⟩ := Dx2.VV.stabilizer_decomp_unitary_mul_unipotent (Dx2.VV.std_vector_z_prime Bs) hs'
  have hlaw := Dx2.VV.orbJ_pt Bs (PBJ.bigPt d) hl hγ hZ hpos hhA hnA hfA hhB hnB hfB F
  rw [← hγs] at hlaw
  have hw : (hl.2 ▸ D.ptPerm (PBJ.bigPt d) : Equiv.Perm (Fin (r + 1))) = 1 :=
    PBM.cast_perm_eq_one _ _ (PBM.ptPerm_bigPt d hd)
  obtain ⟨hmono, hnz⟩ := Dx2.VV.ptMatN_monoP' (PBJ.bigPt d) (r + 1) hl.2 hl.1
  rw [hw] at hmono hlaw
  rw [PBM.orbJ_one_eq Bs hγ' hpos' hnz (hZ'.trans hmono) F, PBM.orbJ_one_eq Bs hγ hpos hnz (hZ.trans hmono) F] at hlaw
  rw [← hlaw, CutBP.hsVec_norm_CinL Bs hhA hhB]

theorem normSq_sec (hk : 2 ≤ k) (Bs : B.RealPlaceData k r Wp Wq) (F : B.Mat k r → (Wq →L[ℂ] Wp))
    (μsec : ℂ → Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) (hsec : IsSection k r Bs.z Bs.z' μsec) :
    B.normSq Bs F = jNormSq k r (Tz k r Bs.z) (Tz k r Bs.z')
      fun q => Real.sqrt (hsNormSq (B.JF Bs F (bigCell k r q.1 (μsec q.2)))) := by
  unfold B.normSq jNormSq
  refine lintegral_congr fun q => ?_
  by_cases hw0 : bcWeight k r (Tz k r Bs.z) (Tz k r Bs.z') q = 0
  · rw [hw0, zero_mul, zero_mul]
  obtain ⟨hc, hζ⟩ := Formalism.MainNotions.S.Pv.LemmaJ.bcWeight_ne hk hw0
  have hζ0 : q.2 ≠ 0 := by
    intro h
    rw [h, map_zero] at hζ
    exact absurd (mul_pos Bs.T_pos Bs.T'_pos) (not_lt.2 hζ.le)
  obtain ⟨d, hd1, hd2⟩ : ∃ d : Fin (r + 1) → ℂ, (fun i : Fin r => d i.castSucc) = q.1 ∧ d (Fin.last r) = q.2 :=
    ⟨Fin.snoc q.1 q.2, by funext i; simp, by simp⟩
  have hd : ∀ a, d a ≠ 0 := fun a => by
    refine Fin.lastCases ?_ (fun i => ?_) a
    · rw [hd2]; exact hζ0
    · rw [congrFun hd1 i]; exact hc i
  have hZ := PBM.zhat_bigCell_pt Bs d (by rw [hd2]; exact hζ)
  have hZ' := PBM.zhat_bigCell_pt { Bs with μsec := μsec, sec := hsec } d (by rw [hd2]; exact hζ)
  rw [hd1, hd2] at hZ hZ'
  have e := norm_JF_eq Bs F d hd (bigCellMem k r _ _ hc (Bs.sec.2 _ hζ).1) (bigCellMem k r _ _ hc (hsec.2 _ hζ).1) hZ hZ'
    (Formalism.MainNotions.S.Pv.LemmaJ.Gf_big Bs.z_mem Bs.z'_mem Bs.sec q.1 hc q.2 hζ)
  congr 2
  rw [Real.norm_eq_abs, sq_abs, Real.sq_sqrt (Formalism.MainNotions.BesselShellMomentBounds.hsNormSq_nonneg _), Formalism.MainNotions.BesselShellMomentBounds.hsNormSq_eq]
  change ‖B.hsVec (B.JF Bs F (bigCell k r q.1 (Bs.μsec q.2)))‖ ^ 2 = _
  rw [e, PiLp.norm_sq_eq_of_L2]
  rfl

end energy

theorem energy_identity : EnergyTie := by
  intro k r L f μsec u u' p _ hc _ _ htie _ _ hsec
  obtain ⟨hz, hz', hπ, hπ', hW, hN, hW'⟩ := htie
  have e : TBB.jN2 p f = jNorm2 L f μsec := by
    refine (GlobalTheory.T.jN2_eq_normSq_base (parOfL L u u') L.Wp L.Wq p f).trans ?_
    have h := normSq_sec (k := k) (r := r) p.hl.2.2 p.T.base f μsec (by
      have e1 : (p.T.base.z : Fin (2 * r + k + 1) → ℂ) = L.z := hz
      have e2 : (p.T.base.z' : Fin (2 * r + k + 1) → ℂ) = L.z' := hz'
      exact e1 ▸ e2 ▸ hsec)
    refine h.trans ?_
    unfold jNorm2 LocBessel.J B.JF
    rw [hc]
    simp only [hz, hz', hπ, hπ', hW, hN, hW']
  rw [e]
  refine le_mul_of_one_le_left' ?_
  rw [ENNReal.one_le_ofReal]
  exact one_le_pow₀ (by linarith [Real.pi_gt_three])

section scale

variable {k r : ℕ}

@[reducible] def withN (L : LocBessel k r) (κ : ℝ≥0∞) : LocBessel k r := { L with κN := κ }

theorem pairMeas_smul (L : LocBessel k r) (κ s : ℝ≥0∞) (h : L.μN = s • (withN L κ).μN) :
    pairMeas L = (s * s) • pairMeas (withN L κ) := by
  have i1 : SFinite (withN L κ).μN := Formalism.MainNotions.FrameBoundFromBesselTorus.sFinite_haarLie _ _
  have i2 : SigmaFinite L.μW := L.hμW.1.1
  have i3 : SigmaFinite L.μW' := L.hμW'.1.1
  unfold pairMeas
  rw [h]
  change (L.μW.prod (s • (withN L κ).μN)).prod (L.μW'.prod (s • (withN L κ).μN)) =
    (s * s) • (L.μW.prod (withN L κ).μN).prod (L.μW'.prod (withN L κ).μN)
  rw [Measure.prod_smul_right, Measure.prod_smul_right, Measure.prod_smul_right, Measure.prod_smul_left, smul_smul]

theorem orbSq_le (L : LocBessel k r) (κ s : ℝ≥0∞) (hs0 : s ≠ 0) (hs : s ≠ ⊤)
    (h : pairMeas L = s • pairMeas (withN L κ)) (f : Mx k r → (L.Wq →L[ℂ] L.Wp)) (γ : Point ℂ (r + 1)) :
    orbSq L f γ ≤ ENNReal.ofReal (s.toReal ^ 2) * orbSq (withN L κ) f γ := by
  unfold orbSq
  refine iSup_le fun g => iSup_le fun μR => iSup_le fun ν => iSup_le fun hc => ?_
  have hq : IsOrbQuot (withN L κ) g μR (s⁻¹ • ν) := by
    intro φ hφ
    have e := hc.2.2.2 φ hφ
    rw [h, lintegral_smul_measure] at e
    rw [lintegral_smul_measure, ← e, smul_eq_mul, smul_eq_mul, ← mul_assoc, ENNReal.inv_mul_cancel hs0 hs, one_mul]
  have e : OrbInt L f g ν = ((s.toReal : ℝ) : ℂ) • OrbInt (withN L κ) f g (s⁻¹ • ν) := by
    have e1 : ν = s • (s⁻¹ • ν) := by rw [smul_smul, ENNReal.mul_inv_cancel hs0 hs, one_smul]
    unfold OrbInt
    conv_lhs => rw [e1, integral_smul_measure]
    rw [Complex.coe_smul]
    rfl
  rw [e, Formalism.MainNotions.BesselShellMomentBounds.hsNormSq_smul, Complex.norm_real, Real.norm_eq_abs, sq_abs, ENNReal.ofReal_mul (by positivity)]
  refine mul_le_mul' le_rfl ?_
  exact le_iSup_of_le g (le_iSup_of_le μR (le_iSup_of_le (s⁻¹ • ν) (le_iSup_of_le ⟨hc.1, hc.2.1, hc.2.2.1, hq⟩ le_rfl)))

theorem jNorm2_eq (L : LocBessel k r) (κ s : ℝ≥0∞) (h : pairMeas L = s • pairMeas (withN L κ))
    (f : Mx k r → (L.Wq →L[ℂ] L.Wp)) (μsec : ℂ → Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) :
    jNorm2 L f μsec = ENNReal.ofReal (s.toReal ^ 2) * jNorm2 (withN L κ) f μsec := by
  have hJ : ∀ g, L.J f g = ((s.toReal : ℝ) : ℂ) • (withN L κ).J f g := fun g => by
    change ∫ x, besselIntg L f g x ∂(pairMeas L) = _ • ∫ x, besselIntg L f g x ∂(pairMeas (withN L κ))
    rw [h, integral_smul_measure, Complex.coe_smul]
  rw [Formalism.MainNotions.BesselShellMomentBounds.jNorm2_eq, Formalism.MainNotions.BesselShellMomentBounds.jNorm2_eq, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine lintegral_congr fun q => ?_
  rw [← ENNReal.ofReal_mul (by positivity)]
  congr 1
  unfold Formalism.MainNotions.BesselShellMomentBounds.dens
  rw [hJ, Formalism.MainNotions.BesselShellMomentBounds.hsNormSq_smul, Complex.norm_real, Real.norm_eq_abs, sq_abs]
  change _ = _ * (bcWeight k r (Tz k r L.z) (Tz k r L.z') q * _)
  ring

end scale

end CompanionTheory.WaveGrid.Ties
