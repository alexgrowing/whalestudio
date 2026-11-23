import Mathlib
import Formalism.SharpRestriction.CuspSpanNormBounds.NormalizedLocalScale
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.OrbitalSquareEqHilbertSchmidtNormalisedVector
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.StabilizerMeasureNormalisationSymm
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.NormalFormFlagZeroMiddleInverseMinorOrthogonal
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsIsQuotMeas
import Formalism.HermitianCurvature.HermitianCurvatureProofs.SettingConstruction
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CellRep

noncomputable section

open MeasureTheory Matrix Formalism.BasicNotions Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp GlobalTheory.ThA.OrbSq
open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Dx2
open scoped ENNReal

namespace GlobalTheory.Amp.RootQuot

variable {k r : ℕ}

theorem exists_setting (hk : 1 ≤ k) {z z' : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z) (hz' : inWb k r z')
    (hT : 0 < Tz k r z) (hT' : 0 < Tz k r z') : ∃ Bs : B.RealPlaceData k r ℂ ℂ, Bs.z = z ∧ Bs.z' = z' := by
  obtain ⟨μG, hG⟩ := unitary_group_haar_exists k r
  obtain ⟨μN, hN⟩ := unipotent_haar_exists k r
  obtain ⟨μW, hW⟩ := weyl_haar_exists k r z hz hT
  obtain ⟨μW', hW'⟩ := weyl_haar_exists k r z' hz' hT'
  obtain ⟨μsec, hs⟩ := SettingConstruction.sectionExists k r z z' hk hz hz' hT hT'
  obtain ⟨χ, hχ1, hχ2, hχ3⟩ := character_exists_alt
  exact ⟨⟨z, z', fun _ => 1, fun _ => 1, μG, μW, μN, μW', μsec, χ, hk, hz, hz', hT, hT',
    ⟨rfl, fun _ _ _ _ => rfl⟩, ⟨rfl, fun _ _ _ _ => rfl⟩, fun _ _ _ => rfl, fun _ _ _ => rfl,
    continuousOn_const, continuousOn_const, hG, hW, hN, hW', hs, hχ1, hχ2, hχ3⟩, rfl, rfl⟩

theorem perm_invol (p : C.LPt) (n : ℕ) (h : D.ptSize p = n) (a : Fin n) :
    (h ▸ D.ptPerm p : Equiv.Perm (Fin n)) ((h ▸ D.ptPerm p : Equiv.Perm (Fin n)) a) = a := by
  subst h
  exact Dx1.ptPerm_invol p a

theorem zhat_inv_mono {z z' : Fin (2 * r + k + 1) → ℂ} (p : Point ℂ (r + 1)) {g : Mat k r} (hg : g ∈ GG k r)
    (hZ : ZhatO k r z z' g = ptMat p) :
    ∃ d : Fin (r + 1) → ℂ, (∀ a, d a ≠ 0) ∧ Zhat k r z' z g⁻¹ = C2.monoP (permOf p) d := by
  obtain ⟨hw, hd⟩ := VV.ptMatN_monoP' (sw p.1) (r + 1) (isLocPt_sw p).2 (isLocPt_sw p).1
  rw [ptMat_sw, ← hZ] at hw
  generalize (Eq.rec (motive := fun x _ => Fin x → ℂ) (D.ptDiag (sw p.1)) (isLocPt_sw p).2) = d at hw hd
  have hi : ∀ a, permOf p (permOf p a) = a := perm_invol _ _ _
  refine ⟨fun a => star ((-1) ^ (r - (permOf p a).val) * d (permOf p a)), fun a => ?_, ?_⟩
  · exact star_ne_zero.2 (mul_ne_zero (pow_ne_zero _ (by norm_num)) (hd _))
  · rw [NfMid.zhat_inv z z' hg]
    ext i a
    have h1 : (-1 : ℂ) ^ (r - i.val) * Zhat k r z z' g a i = if a = permOf p i then d i else 0 :=
      congrFun (congrFun hw a) i
    have h2 : Zhat k r z z' g a i = (-1 : ℂ) ^ (r - i.val) * if a = permOf p i then d i else 0 := by
      rw [← h1, ← mul_assoc, ← pow_add, ← two_mul, pow_mul]
      norm_num
    rw [conjTranspose_apply, h2]
    show _ = if i = permOf p a then _ else 0
    by_cases h : a = permOf p i
    · subst h
      rw [if_pos rfl, if_pos (hi i).symm, hi]
    · rw [if_neg h, if_neg (fun e => h (by rw [e, hi])), mul_zero, star_zero]

theorem gf_inv (z z' : Fin (2 * r + k + 1) → ℂ) {g : Mat k r} (hg : g ∈ GG k r) :
    Gf k r z' z g⁻¹ = Gf k r z z' g := by
  unfold Gf
  simp only [Complex.normSq_eq_norm_sq, NfMid.dmin_inv z z' hg]
  ring

theorem exists_root_haar (hk : 1 ≤ k) {z z' : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z) (hz' : inWb k r z')
    (hT : 0 < Tz k r z) (hT' : 0 < Tz k r z') (p : Point ℂ (r + 1)) {g : Mat k r} (hg : g ∈ GG k r)
    (hZ : ZhatO k r z z' g = ptMat p) (hG0 : Gf k r z z' g ≠ 0) :
    ∃ μ : Measure (Mt k r), IsHaarOn (Rset k r g) μ ∧ IsUnimod (Rset k r g) μ ∧
      μ.map (rootCoords k r z' p) = volume := by
  obtain ⟨Bs, rfl, rfl⟩ := exists_setting hk hz' hz hT' hT
  obtain ⟨d, hd, hZw⟩ := zhat_inv_mono p hg hZ
  have hu := isUnit_det_of_mem_GG hg
  have hgi : g⁻¹ ∈ B.GV k r := isClosedSub_GG.2.2.2.2 _ hg
  have hpos : 0 < Gf k r Bs.z Bs.z' g⁻¹ := by
    rw [gf_inv _ _ hg]
    exact lt_of_le_of_ne (gNonneg k r _ _ hz hz' hT hT' g hg) hG0.symm
  have hG : Rad.Good Bs g⁻¹ (permOf p) d :=
    ⟨Rad.exists_rho Bs hgi hpos hd hZw, Rad.u_inj Bs hgi hpos hd hZw, fun ρ hρ => Rad.u_lstg Bs hgi hpos hd hZw hρ⟩
  have hm := Rad.rhoF_meas Bs hgi hd hG
  have hH := Rad.haar_good Bs hgi hd hG
  have hI := haar_measure_inversion k r _ _ (OrbJ.closedR (Matrix.isUnit_nonsing_inv_det g hu)) hH
  have hset : C6.Rset g⁻¹ = Rset k r g := by
    ext x
    simp only [C6.Rset, Formalism.MainNotions.S.Rset, Set.mem_setOf_eq, Matrix.nonsing_inv_nonsing_inv _ hu]
  rw [hset] at hH
  have hmu : D.muR Bs g⁻¹ (permOf p) = (volume : Measure (C2.Lstidx (permOf p) → ℂ)).map
      (fun x => (Matrix.of.symm (Rad.rhoF Bs g⁻¹ (permOf p) x) : Mt k r)) := rfl
  have hphi : ∀ x : Mt k r, Rad.phi0 Bs (permOf p) x = cjE (rootEquiv p) (rootCoords k r Bs.z p x) := by
    intro x
    funext q
    rw [cjE_apply]
    have hq : q.1.2.val < r := by have h1 := q.2.1; have h2 := q.1.1.isLt; rw [Fin.lt_def] at h1; omega
    show star (C2.uMap k r Bs.z (Matrix.of x) q.1.2 q.1.1) = star (flagMat k r Bs.z (Matrix.of x) q.1.2 q.1.1)
    unfold C2.uMap flagMat
    rw [dif_pos hq, dif_pos hq]
    exact congrArg star (DF.herm_es _ _)
  have hrc : rootCoords k r Bs.z p = (cjE (rootEquiv p)).symm ∘ Rad.phi0 Bs (permOf p) := by
    funext x; simp [hphi x]
  have hrm : Measurable (rootCoords k r Bs.z p) := by
    rw [hrc]; exact (cjE (rootEquiv p)).symm.measurable.comp (Rad.continuous_radial_phi Bs).measurable
  refine ⟨D.muR Bs g⁻¹ (permOf p), ⟨OrbJ.sigmaF hH, hH.ne_zero, hH.conc, hH.left⟩, ⟨hH.right, hI⟩, ?_⟩
  rw [hmu, Measure.map_map hrm hm]
  have : rootCoords k r Bs.z p ∘ (fun x => (Matrix.of.symm (Rad.rhoF Bs g⁻¹ (permOf p) x) : Mt k r)) =
      (cjE (rootEquiv p)).symm := by
    funext x
    rw [hrc]
    simp only [Function.comp]
    rw [Rad.coordMap_hermRep_leftInverse Bs hgi hd hG]
  rw [this, (cjE_mp _).symm.map_eq]

theorem scale_pos (D : D7) : 0 < 2 * D.host.ka / gg D / (2 * Real.pi) := by
  have h1 : 0 < D.host.ka := by
    unfold Formalism.BasicNotions.Host.ka Formalism.BasicNotions.Host.v Formalism.BasicNotions.Host.rdE
    have h : (0 : ℝ) < |(NumberField.discr D.host.E : ℝ)| :=
      abs_pos.2 (by exact_mod_cast NumberField.discr_ne_zero D.host.E)
    have := Real.rpow_pos_of_pos h ((1 : ℝ) / (Module.finrank ℚ D.host.E : ℝ))
    positivity
  have h2 : 0 < gg D := by
    unfold gg
    have a := (D.host.g_prime 0).pos
    have b := (D.host.g_prime 1).pos
    positivity
  positivity

theorem exists_rMeas : ∀ (D : D7) (W : LocW D.R.k D.R.rS) (γ : MatKR D.R.k D.R.rS) (p : Point ℂ (D.R.rS + 1)), inWb D.R.k D.R.rS W.z → inWb D.R.k D.R.rS W.z' → 0 < Tz D.R.k D.R.rS W.z → 0 < Tz D.R.k D.R.rS W.z' → IsHaarOn (UH (Hpk D.R.k D.R.rS)) W.μG → RelPt D W.z W.z' γ p → ∃ ν, RMeas D W γ 1 ν := by
  rintro D W γ p hz hz' hT hT' hG ⟨hγ, hC, hG0⟩
  have hk : 1 ≤ D.R.k := by have := D.R.m_add_three_le_k; omega
  obtain ⟨n, hn, n', hn', g, hg, rfl, hZ⟩ := GlobalTheory.CellRep.cell_rep _ _ W.z W.z' γ p hz hz' hT hT' hγ hC
  rw [gInv _ _ W.z W.z' hz hz' n ⟨1, (isClosedSub_UWset W.z).2.2.1, n, hn, (Matrix.one_mul _).symm⟩
    n' ⟨1, (isClosedSub_UWset W.z').2.2.1, n', hn', (Matrix.one_mul _).symm⟩] at hG0
  obtain ⟨μ, h1, h2, h3⟩ := exists_root_haar hk hz hz' hT hT' p hg hZ hG0
  obtain ⟨n1, -, -, -, n5⟩ := isClosedSub_Nset (k := D.R.k) (r := D.R.rS)
  obtain ⟨d1, d2⟩ := StabMeas.haar_smul h1 h2 (pow_pos (scale_pos D) (rootPat p).card)
  obtain ⟨e1, e2⟩ := StabMeas.haar_conj (isUnit_det_of_mem_GG (n1 (n5 _ hn'))) (StabMeas.conj_mem_Rset hn hn' g) d1 d2
  obtain ⟨ν, hν⟩ := GlobalTheory.SgQuot.exists_isQuotMeas _ _ _ W.μG _ (StabMeas.isClosedSub_Rset hγ) hG e1 e2
  refine ⟨ν, p, _, ⟨n, hn, n', hn', g, rfl, hZ, _, d1.2.2.1, ?_, rfl⟩, ?_⟩
  · rw [Measure.map_smul, h3]
  · have e : (fun x : Mt D.R.k D.R.rS => fun i j => (n'⁻¹ * Matrix.of x * n') i j) = conjM n'⁻¹ := by
      funext x
      unfold conjM
      rw [Matrix.nonsing_inv_nonsing_inv _ (isUnit_det_of_mem_GG (n1 hn'))]
    rw [ENNReal.ofReal_one, one_smul, e]
    exact hν

end GlobalTheory.Amp.RootQuot
