import Formalism.HermitianCurvature.HermitianCurvatureProofs.OpLEqZeroOfEventually
import Formalism.FormalDegreeBessel.FormalDegreeRatio.GroupFactorizationHolds
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CompactGroupHaarExists
import Formalism.HermitianCurvature.HermitianCurvatureProofs.OppositeWeylSubgroupClosed
import Formalism.HermitianCurvature.HermitianCurvatureProofs.RegularisedPairingViaPhase
import Formalism.HermitianCurvature.HermitianCurvatureProofs.TheoremPIntegralOfPlaces

open Matrix MeasureTheory Filter Topology

noncomputable section

namespace Formalism.FourierDecayAlt.P5.HerC

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.P5 Formalism.FourierDecayAlt.P5.HerA Formalism.FourierDecayAlt.P5.HerB

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

section Minors

variable {k r : ℕ}

def pc (c : Fin r → ℂ) : ℂ := ∏ a : Fin r with a.val < (Fin.last r).val, c a

theorem pc_continuous : Continuous (pc (r := r)) := by
  unfold pc
  exact continuous_finset_prod _ fun a _ => continuous_apply a

theorem pc_ne_zero {c : Fin r → ℂ} (hc : c ∈ OmX r) : pc c ≠ 0 := Finset.prod_ne_zero_iff.2 fun a _ => hc a

theorem dmin_wCell {z z' : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z) (hz' : inWb k r z') {c : Fin r → ℂ}
    (hc : c ∈ OmX r) {g : Mx k r} (hg : g ∈ Glev k r (Fin.last r)) :
    Dmin k r z z' (wCell k r (Fin.last r) c * g) ⟨r, by omega⟩ = pc c ∧
      Dmin k r z z' (wCell k r (Fin.last r) c * g) (Fin.last (r + 1)) = zetaL k r z z' (Fin.last r) g * pc c := by
  obtain ⟨μ, _, rfl⟩ := (Formalism.FourierDecayAlt.P.TwoByOneBlock.UWb_iff g).1 (Formalism.FourierDecayAlt.P5.Rad.glev_last_uwb hg)
  have e : wCell k r (Fin.last r) c * Formalism.FourierDecayAlt.B2.embWb k r μ = bigCell k r c μ := by
    rw [Formalism.FourierDecayAlt.P5.Rad.wCell_last_eq, ← (Formalism.FourierDecayAlt.P.bruhat_big_cell_factorization k r c μ).1]
  rw [e]
  have hmin := big_cell_minors_holds k r z z' c μ hz hz'
  have hζ : herm (Hpk k r) (bigCell k r c μ *ᵥ z') z = zetaL k r z z' (Fin.last r) (Formalism.FourierDecayAlt.B2.embWb k r μ) := by
    rw [Formalism.FourierDecayAlt.P5.Rad.zetaL_last, ← Formalism.FourierDecayAlt.P.TwoByOneBlock.jV_wbPart hz', Formalism.FourierDecayAlt.P.BigCellHermitian.bigCell_mulVec_jV,
      Formalism.FourierDecayAlt.P.TwoByOneBlock.emb_mulVec_jV]
  have hr : Dmin k r z z' (bigCell k r c μ) ⟨r, by omega⟩ = pc c := hmin.1 (Fin.last r)
  refine ⟨hr, ?_⟩
  have hzeta := hmin.2.2 hc
  rw [hζ] at hzeta
  unfold Formalism.QuantumDeterminants.zeta at hzeta
  rw [hr] at hzeta
  have h2 := div_mul_cancel₀ (Dmin k r z z' (bigCell k r c μ) (Fin.last (r + 1))) (pc_ne_zero hc)
  rw [hzeta] at h2
  exact h2.symm

end Minors

theorem jfCptLocAll : JFCptLocAll := by
  intro Wp Wq _ _ _ _ _ _ P z z' π π' D F Φ _hP hz hz' hπ hπ' hF hΦ
  subst hz hz' hπ hπ'
  obtain ⟨⟨_, ε, hε, hG⟩, hC⟩ := hF
  have hW := Formalism.FourierDecayAlt.P.weyl_subgroup_closed P.k P.r
  have hN := Formalism.FourierDecayAlt.P.unipotent_radical_closed P.k P.r
  have hGV := Formalism.FourierDecayAlt.P.unitary_group_closed P.k P.r
  have := Formalism.FourierDecayAlt.P.B5.haar_sigmaFinite D.haarW
  have := Formalism.FourierDecayAlt.P.B5.haar_sigmaFinite D.haarN
  have := Formalism.FourierDecayAlt.P.B5.haar_sigmaFinite D.haarW'

  have hcont : Continuous (fun h : Mx P.k P.r => Dmin P.k P.r D.z D.z' h (Fin.last (P.r + 1))) :=
    (Formalism.FourierDecayAlt.P.JCx1.contDiff_Dmin D.z D.z' (Fin.last (P.r + 1))).continuous
  obtain ⟨R0, hR0⟩ := hC.isCompact.exists_bound_of_continuousOn hcont.continuousOn

  have hae : ∀ᵐ (p : (Mt P.k P.r × Mt P.k P.r) × (Mt P.k P.r × Mt P.k P.r)) ∂((D.μW.prod D.μN).prod (D.μW'.prod D.μN)),
      (Matrix.of p.1.1 ∈ UWset P.k P.r D.z ∧ Matrix.of p.1.2 ∈ Formalism.QuantumDeterminants.Nset P.k P.r) ∧
        (Matrix.of p.2.1 ∈ UWset P.k P.r D.z' ∧ Matrix.of p.2.2 ∈ Formalism.QuantumDeterminants.Nset P.k P.r) := by
    have hw : ∀ᵐ (a : Mt P.k P.r) ∂D.μW, Matrix.of a ∈ UWset P.k P.r D.z :=
      (measure_eq_zero_iff_ae_notMem.1 D.haarW.conc).mono fun a ha => not_not.1 ha
    have hn : ∀ᵐ (a : Mt P.k P.r) ∂D.μN, Matrix.of a ∈ Formalism.QuantumDeterminants.Nset P.k P.r :=
      (measure_eq_zero_iff_ae_notMem.1 D.haarN.conc).mono fun a ha => not_not.1 ha
    have hw' : ∀ᵐ (a : Mt P.k P.r) ∂D.μW', Matrix.of a ∈ UWset P.k P.r D.z' :=
      (measure_eq_zero_iff_ae_notMem.1 D.haarW'.conc).mono fun a ha => not_not.1 ha
    have h1 : ∀ᵐ (q : Mt P.k P.r × Mt P.k P.r) ∂(D.μW.prod D.μN), Matrix.of q.1 ∈ UWset P.k P.r D.z ∧ Matrix.of q.2 ∈ Formalism.QuantumDeterminants.Nset P.k P.r :=
      (Measure.quasiMeasurePreserving_fst.ae hw).and (Measure.quasiMeasurePreserving_snd.ae hn)
    have h2 : ∀ᵐ (q : Mt P.k P.r × Mt P.k P.r) ∂(D.μW'.prod D.μN), Matrix.of q.1 ∈ UWset P.k P.r D.z' ∧ Matrix.of q.2 ∈ Formalism.QuantumDeterminants.Nset P.k P.r :=
      (Measure.quasiMeasurePreserving_fst.ae hw').and (Measure.quasiMeasurePreserving_snd.ae hn)
    exact (Measure.quasiMeasurePreserving_fst.ae h1).and (Measure.quasiMeasurePreserving_snd.ae h2)
  intro c hc
  set p0 : ℝ := ‖pc c‖ with hp0
  have hp0pos : 0 < p0 := norm_pos_iff.2 (pc_ne_zero hc)
  set U : Set (Fin P.r → ℂ) := {c' | p0 / 2 < ‖pc c'‖ ∧ ‖pc c'‖ < 2 * p0} with hU
  have hUo : IsOpen U :=
    (isOpen_lt continuous_const (continuous_norm.comp pc_continuous)).inter
      (isOpen_lt (continuous_norm.comp pc_continuous) continuous_const)
  have hcU : c ∈ U := ⟨by linarith, by linarith⟩
  set e' : ℝ := ε / (2 * p0) ^ 2 with he'
  set R' : ℝ := R0 / (p0 / 2) with hR'
  have he'pos : 0 < e' := div_pos hε (by positivity)
  refine ⟨U, hUo, hcU, {g | g ∈ Glev P.k P.r (Fin.last P.r) ∧ e' ≤ GGl P.k P.r D.z D.z' g ∧
      ‖zetaL P.k P.r D.z D.z' (Fin.last P.r) g‖ ≤ R'},
    isCompact_zeta_le D.z D.z' D.z_mem D.z'_mem D.T_pos D.T'_pos e' R', fun g hg => lt_of_lt_of_le he'pos hg.2.1, ?_⟩
  intro c' hc' g hg hgK
  by_cases hd : (c', g) ∈ DomR P.k P.r D.z D.z'
  swap
  · exact radSp_zero_off Φ (x := (c', g)) hd
  rw [hΦ (c', g) hd]
  unfold resG
  have hc'O : c' ∈ OmX P.r := hd.1
  set x : Mx P.k P.r := wCell P.k P.r (Fin.last P.r) c' * g with hx
  obtain ⟨hDr, hDl⟩ := dmin_wCell D.z_mem D.z'_mem hc'O hg
  rw [← hx] at hDr hDl
  have hxG : x ∈ B.GV P.k P.r := hGV.mul_mem _ (Formalism.FourierDecayAlt.P.Qx3.wlist_glev hc'O _).1 _ hg.1

  have hF0 : ∀ y ∈ B.GV P.k P.r, Dmin P.k P.r D.z D.z' y ⟨P.r, by omega⟩ = pc c' →
      Dmin P.k P.r D.z D.z' y (Fin.last (P.r + 1)) = zetaL P.k P.r D.z D.z' (Fin.last P.r) g * pc c' → F y = 0 := by
    intro y hy hyr hyl
    by_contra hFy
    apply hgK
    have hsupp : y ∈ tsupport F := subset_tsupport F hFy
    have hb := hR0 y hsupp
    have hGy := hG y hy hFy
    rw [hyl] at hb
    have hGy' : Gf P.k P.r D.z D.z' y = Complex.normSq (pc c') * GGl P.k P.r D.z D.z' g := by
      unfold Formalism.QuantumDeterminants.Gf GGl
      rw [hyr, hyl, Complex.normSq_mul]
      ring
    have hpc1 : p0 / 2 < ‖pc c'‖ := hc'.1
    have hpc2 : ‖pc c'‖ < 2 * p0 := hc'.2
    have hpcpos : 0 < ‖pc c'‖ := by linarith
    have hns : Complex.normSq (pc c') = ‖pc c'‖ ^ 2 := by rw [Complex.sq_norm]
    refine ⟨hg, ?_, ?_⟩
    ·
      have hGG : ε ≤ ‖pc c'‖ ^ 2 * GGl P.k P.r D.z D.z' g := by rw [← hns, ← hGy']; exact hGy
      have hGGpos : 0 < GGl P.k P.r D.z D.z' g := hd.2.2
      have hsq : ‖pc c'‖ ^ 2 ≤ (2 * p0) ^ 2 := by nlinarith
      rw [he', div_le_iff₀ (by positivity)]
      nlinarith
    ·
      rw [norm_mul] at hb
      have hz0 : 0 ≤ ‖zetaL P.k P.r D.z D.z' (Fin.last P.r) g‖ := norm_nonneg _
      have hR0nn : 0 ≤ R0 := le_trans (by positivity) hb
      rw [hR', le_div_iff₀ (by positivity)]
      nlinarith
  have hJ0 : B.JF D F x = 0 := by
    unfold B.JF besselJ
    refine integral_eq_zero_of_ae (hae.mono fun p hp => ?_)
    obtain ⟨⟨ha, hn⟩, ⟨ha', hn'⟩⟩ := hp
    set a := Matrix.of p.1.1
    set n := Matrix.of p.1.2
    set a' := Matrix.of p.2.1
    set n' := Matrix.of p.2.2
    have hainv : a⁻¹ ∈ UWset P.k P.r D.z := (hW D.z).inv_mem _ ha
    have hninv : n⁻¹ ∈ Formalism.QuantumDeterminants.Nset P.k P.r := hN.inv_mem _ hn
    have hs1 : a⁻¹ * n⁻¹ ∈ Formalism.QuantumDeterminants.Sset P.k P.r D.z := ⟨a⁻¹, hainv, n⁻¹, hninv, rfl⟩
    have hs2 : n' ∈ Formalism.QuantumDeterminants.Sset P.k P.r D.z' := ⟨1, (hW D.z').one_mem, n', hn', (one_mul _).symm⟩
    have hs3 : (1 : Mx P.k P.r) ∈ Formalism.QuantumDeterminants.Sset P.k P.r D.z := ⟨1, (hW D.z).one_mem, 1, hN.one_mem, (mul_one _).symm⟩
    have hs4 : a' ∈ Formalism.QuantumDeterminants.Sset P.k P.r D.z' := ⟨a', ha', 1, hN.one_mem, (mul_one _).symm⟩
    have hinvD : ∀ l, Dmin P.k P.r D.z D.z' (a⁻¹ * n⁻¹ * x * n' * a') l = Dmin P.k P.r D.z D.z' x l := by
      intro l
      have e1 := diagonal_inverse_holds P.k P.r D.z D.z' D.z_mem D.z'_mem 1 hs3 a' hs4 (a⁻¹ * n⁻¹ * x * n') l
      rw [one_mul] at e1
      rw [e1]
      exact diagonal_inverse_holds P.k P.r D.z D.z' D.z_mem D.z'_mem _ hs1 n' hs2 x l
    have hyG : a⁻¹ * n⁻¹ * x * n' * a' ∈ B.GV P.k P.r :=
      hGV.mul_mem _ (hGV.mul_mem _ (hGV.mul_mem _ (hGV.mul_mem _ hainv.1 _ hninv.1) _ hxG) _ hn'.1) _ ha'.1
    have hFy : F (a⁻¹ * n⁻¹ * x * n' * a') = 0 :=
      hF0 _ hyG (by rw [hinvD]; exact hDr) (by rw [hinvD]; exact hDl)
    have hxy : (Matrix.of p.1.1)⁻¹ * (Matrix.of p.1.2)⁻¹ * x * Matrix.of p.2.2 * Matrix.of p.2.1 =
        a⁻¹ * n⁻¹ * x * n' * a' := rfl
    simp only [hxy, hFy, ContinuousLinearMap.comp_zero, ContinuousLinearMap.zero_comp, smul_zero, Pi.zero_apply]
  rw [hJ0, smul_zero]

theorem herCptTopAll : HerCptTopAll := herCptTopAll_of_jf jfCptLocAll

theorem thmPActualCpt_of_stepForm (hSF : StepFormCptAll) : ThmPActualCpt := thmPActualCpt_of_jf jfCptLocAll hSF

end Formalism.FourierDecayAlt.P5.HerC
