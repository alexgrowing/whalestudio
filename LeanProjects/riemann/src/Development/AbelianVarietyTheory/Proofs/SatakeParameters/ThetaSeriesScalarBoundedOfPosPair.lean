import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsUnifAt
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SiteSystemRanksEqDatumRanks
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ChiAlgUnitInert
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.DeterminantIdealNormOneAndCharUnitarySmulStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SystemWeightsEqShiftedCharacterExponentsStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.NormLambdaCharacterNormOneIdeleEqPPowStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LatticeTuplePointDetNormOneOrderEqNegLengthStatement
import Formalism.LocalToGlobal.InertKernelTheory.InertCoprimeLemmas.MInvFdOfCharts
import Formalism.LocalToGlobal.InertKernelTheory.InertCoprimeLemmas.LocalModelLatticesAdmissibleSmall
import Formalism.LocalToGlobal.GlobalTheory.GL3.IsIntegralOfMemQbar
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.DIV Formalism.UG Formalism.L2.Ker Formalism.L2.G.Pend Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert GlobalTheory.TwV GlobalTheory.TwV.Xc TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.L2.KerInert.ScalM (qbar_zpow_mem lamC_mul_mem lamC_inv_mem lamC_zpow_mem)

noncomputable section

namespace GlobalTheory.TwV.Xc

set_option maxHeartbeats 4000000 in

theorem scal_of_pos_pair : Sites (fun {D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X} [Fact (D.what₂.places.resChar w).Prime] {std t J} S =>
    S.Pos → S.Pair → S.Scal) := by
  intro D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X _ std t J S hD hS hPos hPair
  obtain ⟨hmm, -, -, -⟩ := GlobalTheory.TwV.DelB.sysS_ranks S
  obtain ⟨hp5, -, hIn, -, -, -, hχ, -, -⟩ := S.curve
  have hp2 : D.what₂.places.resChar w ≠ 2 := by omega
  intro j hj L0 hL0 La' hLa'
  have hj' : j < D.R.m := hmm ▸ hj
  have hL0lat : ((sysS H X std).Pj j).IsLatTup L0.2 := Formalism.L2.G.Pend.repOf_lat _ S.hfin j L0 hL0
  obtain ⟨hAdm, -, -, -, -, -, -, -⟩ := hPair j hj L0 La' hL0lat hLa'
  obtain ⟨hN, hN', hsd, hsd'⟩ := hAdm
  obtain ⟨ha, -, hu⟩ := chi_alg_unit_inert D _ S.lam t.χ hχ hp2 hIn _ (GlobalTheory.T.determinantIdeal_normOne_char_unitary_smul D t.χ hχ _ _ hN hsd).1
  obtain ⟨ha', -, hu'⟩ := chi_alg_unit_inert D _ S.lam t.χ hχ hp2 hIn _ (GlobalTheory.T.determinantIdeal_normOne_char_unitary_smul D t.χ hχ _ _ hN' hsd').1
  obtain ⟨hU0, hord0⟩ := GlobalTheory.T.lattice_det_mem_U1_and_ordA_eq_neg_len S hD hS j hj'.le L0 hL0lat
  obtain ⟨hU1, hord1⟩ := GlobalTheory.T.lattice_det_mem_U1_and_ordA_eq_neg_len S hD hS (j + 1) hj' La' hLa'
  have hfill := GlobalTheory.T.systemWeights_eq_shifted_character_exponents S hD hS j hj' La'.1
  have hm1 := S.law.mu_alg j hj' _ hU1
  have hm0 := S.law.mu_alg j hj' _ hU0
  have hn1 := GlobalTheory.T.norm_lambdaCharacter_normOne_idele_eq_p_pow S hD hS hPos j hj' hfill _ hU1
  have hn0 := GlobalTheory.T.norm_lambdaCharacter_normOne_idele_eq_p_pow S hD hS hPos j hj' hfill _ hU0

  have hcf : Base.chiFac t.χ _ _ ((J.fd std).kerN j L0) ((J.fd std).kerN (j + 1) La') ∈ TaylorLogMetric.Qbar := by
    unfold Base.chiFac
    exact TaylorLogMetric.Qbar.mul_mem (qbar_zpow_mem ha _) (qbar_zpow_mem ha' _)
  have hcfn : ‖TaylorLogMetric.lamC S.lam (Base.chiFac t.χ _ _ ((J.fd std).kerN j L0) ((J.fd std).kerN (j + 1) La'))‖ = 1 := by
    unfold Base.chiFac
    rw [lamC_mul_mem S.lam (qbar_zpow_mem ha _) (qbar_zpow_mem ha' _), lamC_zpow_mem S.lam ha,
      lamC_zpow_mem S.lam ha', norm_mul, norm_zpow, norm_zpow, hu, hu', one_zpow, one_zpow, mul_one]
  have hmr : S.muT (j + 1) ((J.fd std).dt (j + 1) La') * (S.muT (j + 1) ((J.fd std).dt j L0))⁻¹ ∈ TaylorLogMetric.Qbar :=
    TaylorLogMetric.Qbar.mul_mem hm1 (TaylorLogMetric.Qbar.inv_mem hm0)
  refine ⟨?_, ?_⟩
  · unfold KG.scalG
    exact TaylorLogMetric.Qbar.mul_mem (TaylorLogMetric.Qbar.mul_mem (TaylorLogMetric.Qbar.mul_mem hmr (TaylorLogMetric.Qbar.inv_mem hcf)) (qbar_zpow_mem ha _))
      (qbar_zpow_mem ha' _)
  have hexp : TaylorLogMetric.lamC S.lam (KG.scalG (J.fd std) t.χ S.muT j L0 La') =
      TaylorLogMetric.lamC S.lam (S.muT (j + 1) ((J.fd std).dt (j + 1) La') * (S.muT (j + 1) ((J.fd std).dt j L0))⁻¹) *
        (TaylorLogMetric.lamC S.lam (Base.chiFac t.χ _ _ ((J.fd std).kerN j L0) ((J.fd std).kerN (j + 1) La')))⁻¹ *
        TaylorLogMetric.lamC S.lam (t.χ (TaylorLogMetric.detId D (StandardLatticesGL3.stdL D _) ((J.fd std).kerN j L0))) ^ (-(((j * ((sysS H X std).t + 1) / 2 : ℕ) : ℤ))) *
        TaylorLogMetric.lamC S.lam (t.χ (TaylorLogMetric.detId D (StandardLatticesGL3.stdL D _) ((J.fd std).kerN (j + 1) La'))) ^ ((((j + 1) * ((sysS H X std).t + 1) / 2 : ℕ) : ℤ)) := by
    unfold KG.scalG
    rw [lamC_mul_mem S.lam (TaylorLogMetric.Qbar.mul_mem (TaylorLogMetric.Qbar.mul_mem hmr (TaylorLogMetric.Qbar.inv_mem hcf)) (qbar_zpow_mem ha _))
        (qbar_zpow_mem ha' _),
      lamC_mul_mem S.lam (TaylorLogMetric.Qbar.mul_mem hmr (TaylorLogMetric.Qbar.inv_mem hcf)) (qbar_zpow_mem ha _),
      lamC_mul_mem S.lam hmr (TaylorLogMetric.Qbar.inv_mem hcf), lamC_inv_mem S.lam hcf, lamC_zpow_mem S.lam ha, lamC_zpow_mem S.lam ha']
  have hp0 : ‖((D.what₂.places.resChar w : ℕ) : ℂ_[D.what₂.places.resChar w])‖ ≠ 0 := by
    rw [norm_ne_zero_iff]
    exact_mod_cast (Fact.out : (D.what₂.places.resChar w).Prime).ne_zero
  have hB' : ‖((D.what₂.places.resChar w : ℕ) : ℂ_[D.what₂.places.resChar w]) ^ KG.expG (sysS H X std) j L0 La' *
      TaylorLogMetric.lamC S.lam (S.muT (j + 1) ((J.fd std).dt (j + 1) La') * (S.muT (j + 1) ((J.fd std).dt j L0))⁻¹)‖ = 1 := by
    rw [lamC_mul_mem S.lam hm1 (TaylorLogMetric.Qbar.inv_mem hm0), lamC_inv_mem S.lam hm0, norm_mul, norm_mul, norm_inv, norm_zpow,
      hn1, hn0, ← zpow_neg, ← mul_assoc, ← zpow_add₀ hp0, ← zpow_add₀ hp0]
    convert zpow_zero (‖((D.what₂.places.resChar w : ℕ) : ℂ_[D.what₂.places.resChar w])‖) using 2
    simp only [hord1, hord0, KG.expG, ← Finset.sum_neg_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_eq_zero fun v _ => by ring
  rw [hexp]
  calc ‖((D.what₂.places.resChar w : ℕ) : ℂ_[D.what₂.places.resChar w]) ^ KG.expG (sysS H X std) j L0 La' *
        (TaylorLogMetric.lamC S.lam (S.muT (j + 1) ((J.fd std).dt (j + 1) La') * (S.muT (j + 1) ((J.fd std).dt j L0))⁻¹) *
          (TaylorLogMetric.lamC S.lam (Base.chiFac t.χ _ _ ((J.fd std).kerN j L0) ((J.fd std).kerN (j + 1) La')))⁻¹ *
          TaylorLogMetric.lamC S.lam (t.χ (TaylorLogMetric.detId D (StandardLatticesGL3.stdL D _) ((J.fd std).kerN j L0))) ^ (-(((j * ((sysS H X std).t + 1) / 2 : ℕ) : ℤ))) *
          TaylorLogMetric.lamC S.lam (t.χ (TaylorLogMetric.detId D (StandardLatticesGL3.stdL D _) ((J.fd std).kerN (j + 1) La'))) ^ ((((j + 1) * ((sysS H X std).t + 1) / 2 : ℕ) : ℤ)))‖
      = ‖((D.what₂.places.resChar w : ℕ) : ℂ_[D.what₂.places.resChar w]) ^ KG.expG (sysS H X std) j L0 La' *
          TaylorLogMetric.lamC S.lam (S.muT (j + 1) ((J.fd std).dt (j + 1) La') * (S.muT (j + 1) ((J.fd std).dt j L0))⁻¹)‖ := by
        rw [← mul_assoc, ← mul_assoc, ← mul_assoc, norm_mul, norm_mul, norm_mul, norm_inv, norm_zpow, norm_zpow, hcfn, hu, hu',
          one_zpow, one_zpow, inv_one, mul_one, mul_one, mul_one]
    _ = 1 := hB'
    _ ≤ 1 := le_rfl

end GlobalTheory.TwV.Xc
