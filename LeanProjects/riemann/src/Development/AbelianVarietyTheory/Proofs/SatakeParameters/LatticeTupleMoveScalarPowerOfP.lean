import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsUnifAt
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.KernelLatticeMovedLatticeTupleStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.CharDeterminantIdealUnitarySmulSelfDual
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.EigenvalueArithmeticElementAtSiteStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SystemWeightsEqShiftedCharacterExponentsStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ToMatrixCoMulSymm
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.DetUnitaryAdelicPointGramStepNormOne
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SiteSystemRanksEqDatumRanks
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.DIV Formalism.UG Formalism.L2.Ker Formalism.L2.G.Pend Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert GlobalTheory.TwV GlobalTheory.TwV.Xc TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section

namespace GlobalTheory.TwV.Xc.MoveScal

theorem embLL_mem' (D : D7) (z : D.what₂.LL) : D.what₂.embLL z ∈ TaylorLogMetric.Qbar := by
  rw [mem_algebraicClosure_iff']
  exact (Algebra.IsIntegral.isIntegral z).map D.what₂.embLL.toRatAlgHom

theorem embT_mem' (D : D7) (τ : D.what₂.Tau) (x : D.host.E) : TaylorLogMetric.embT D τ x ∈ TaylorLogMetric.Qbar := by
  rw [mem_algebraicClosure_iff']
  exact (Algebra.IsIntegral.isIntegral x).map (TaylorLogMetric.embT D τ).toRatAlgHom

theorem lamC_mul' {p : ℕ} [Fact p.Prime] (lam : TaylorLogMetric.Qbar →+* ℂ_[p]) {x y : ℂ} (hx : x ∈ TaylorLogMetric.Qbar) (hy : y ∈ TaylorLogMetric.Qbar) :
    TaylorLogMetric.lamC lam (x * y) = TaylorLogMetric.lamC lam x * TaylorLogMetric.lamC lam y := by
  rw [Formalism.L2.Ker.lamC_of_mem lam (mul_mem hx hy), Formalism.L2.Ker.lamC_of_mem lam hx, Formalism.L2.Ker.lamC_of_mem lam hy, ← map_mul]
  rfl

theorem lamC_ne' {p : ℕ} [Fact p.Prime] (lam : TaylorLogMetric.Qbar →+* ℂ_[p]) {x : ℂ} (hx : x ∈ TaylorLogMetric.Qbar) (h0 : x ≠ 0) :
    TaylorLogMetric.lamC lam x ≠ 0 := by
  rw [Formalism.L2.Ker.lamC_of_mem lam hx]
  exact (map_ne_zero lam).2 fun h => h0 (congrArg Subtype.val h)

theorem scal_core {Mp Mg ML Mk χk P x y : ℂ} (e1 e1' e2 n2 : ℤ) (hMg : Mg ≠ 0) (hMk : Mk ≠ 0) (hχ : χk ≠ 0)
    (hP : P ≠ 0) :
    Mp * (Mg * ML * Mk)⁻¹ * (P⁻¹ * x) ^ (-e1) * y ^ e1' * ((P⁻¹ * x) ^ e2 * y ^ (-n2))⁻¹ * (Mk * χk⁻¹) *
        (χk * Mg * P ^ (-(e1 + e2))) =
      Mp * ML⁻¹ * x ^ (-e1) * y ^ e1' * (x ^ e2 * y ^ (-n2))⁻¹ := by
  rw [mul_zpow, mul_zpow, inv_zpow', inv_zpow', neg_neg, zpow_neg P (e1 + e2), zpow_add₀ hP, zpow_neg P e2]
  have hA : P ^ e1 ≠ 0 := zpow_ne_zero _ hP
  have hB : P ^ e2 ≠ 0 := zpow_ne_zero _ hP
  generalize P ^ e1 = A at hA ⊢
  generalize P ^ e2 = B at hB ⊢
  generalize x ^ (-e1) = X1
  generalize x ^ e2 = X2
  generalize y ^ e1' = Y1
  generalize y ^ (-n2) = Y2
  field_simp

end GlobalTheory.TwV.Xc.MoveScal

open GlobalTheory.TwV.Xc.MoveScal in
set_option maxHeartbeats 4000000 in

theorem GlobalTheory.TwV.Xc.moveBy_scal : Sites (fun {D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X} [Fact (D.what₂.places.resChar w).Prime] {std t J} S => S.Pos → S.Pair → ∀ j (hj : j < D.R.m) (c : (sysS H X std).Lv.comp j) (La : ((sysS H X std).Pj j).Tup) (γ : ((sysS H X std).Lv.lev j c).Γ) (g : GL (Fin (D.R.N j)) D.host.E) (κ : ((J.St j hj.le).K (J.chart std j hj.le (c, La))).lev.U) (hr : ((sysS H X std).Pj j).m + 1 = D.R.N j), ((sysS H X std).Pj j).IsLatTup La → MoveBy std J j hj.le c La γ g κ → ∀ La' : (sysS H X std).Lt (j + 1), ((sysS H X std).Pj (j + 1)).IsLatTup La'.2 → letI := wittFractionAlgebraCp (D.what₂.places.resChar w); letI := algKfC S.E.toCEmb; GlobalTheory.TwU.pPow (sysS H X std) j (c, (((sysS H X std).Lv.lev j c).smul γ La)) La' * TaylorLogMetric.lamC S.lam (GlobalTheory.TwU.scal0 (sysS H X std) (J.fd std) t.χ S.muT j (c, (((sysS H X std).Lv.lev j c).smul γ La)) La' * (Base.chiFac t.χ _ _ ((J.fd std).kerN j (c, (((sysS H X std).Lv.lev j c).smul γ La))) ((J.fd std).kerN (j + 1) La'))⁻¹ * (S.muT (j + 1) (Matrix.GeneralLinearGroup.det κ.1) * (((((J.St j hj.le).K (J.chart std j hj.le (c, La))).lev.chi κ : ℂˣ) : ℂ))⁻¹)) = (kapG (sysS H X std) ℂ_[D.what₂.places.resChar w] j c γ)⁻¹ * (GlobalTheory.TwU.pPow (sysS H X std) j (c, La) La' * TaylorLogMetric.lamC S.lam (GlobalTheory.TwU.scal0 (sysS H X std) (J.fd std) t.χ S.muT j (c, La) La' * (Base.chiFac t.χ _ _ ((J.fd std).kerN j (c, La)) ((J.fd std).kerN (j + 1) La'))⁻¹))) := by
  intro D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X _ std t J S hD hSp hPos hPair j hj c La γ g κ hr hLa hMove La' hLa'
  have hγL : ((sysS H X std).Pj j).IsLatTup (((sysS H X std).Lv.lev j c).smul γ La) :=
    (Formalism.MainNotions.FormalGroupSystem.Pf.latTup_smul _ _ γ La).2 hLa
  have hjm : j < (sysS H X std).mm := by rw [(GlobalTheory.TwV.DelB.sysS_ranks S).1]; exact hj
  obtain ⟨hA1, -, -, -, hs1, hf1, -, -⟩ := hPair j hjm (c, La) La' hLa hLa'
  have hker := GlobalTheory.T.kernelLattice_movedLatticeTuple S hD hSp j hj c La γ g κ hr hLa hMove
  obtain ⟨hMgA, hkap⟩ := GlobalTheory.T.eigenvalue_arithmeticElement_at_site S hD hSp hPos j hj c La γ g κ hr hLa hMove (GlobalTheory.T.systemWeights_eq_shifted_character_exponents S hD hSp j hj La'.1)
  obtain ⟨hgU, hpt, -, r, hr_eq, -⟩ := hMove
  have hE := (GlobalTheory.TwV.Xc.eMat_unitary_det D.host.E (D.sp.cm.sig : D.host.E →+* D.host.E) (fun x => rfl) _ _ hr
    (gramN D j hj.le) (J.A.crd j hj.le) (J.pins.crd_orth j hj.le)).2 g hgU
  have hchi := GlobalTheory.ChiMove.chi_detId_smulLat D t.χ t.χ_ok ⟨_, hA1.2.2.1⟩ _ hE.1
  rw [hE.2] at hchi
  have hD1 := (hD j hj.le (c, La) hLa).2.2.2
  have hD2 := (hD j hj.le (c, ((sysS H X std).Lv.lev j c).smul γ La) hγL).2.2.2
  have hUL : (J.fd std).dt j (c, La) ∈ U1 (sigD D) := hD1 ▸ det_unitary_adelic_point_gram_step_norm_one D j hj.le _
  have hUk : Matrix.GeneralLinearGroup.det κ.1 ∈ U1 (sigD D) :=
    det_unitary_adelic_point_gram_step_norm_one D j hj.le ⟨κ.1, ((((J.St j hj.le).K _).lev.U_eq κ.1).1 κ.2).1⟩
  have hUγ : (J.fd std).dt j (c, ((sysS H X std).Lv.lev j c).smul γ La) ∈ U1 (sigD D) :=
    hD2 ▸ det_unitary_adelic_point_gram_step_norm_one D j hj.le _
  have hUg : Matrix.GeneralLinearGroup.det (GlobalTheory.TwU.ratA D.host.F g) ∈ U1 (sigD D) := by
    have e : Matrix.GeneralLinearGroup.det (GlobalTheory.TwU.ratA D.host.F g) =
        (J.fd std).dt j (c, ((sysS H X std).Lv.lev j c).smul γ La) * (Matrix.GeneralLinearGroup.det κ.1)⁻¹ *
          ((J.fd std).dt j (c, La))⁻¹ := by
      rw [hD2, hD1, hpt, map_mul, map_mul, mul_inv_cancel_right, mul_inv_cancel_right]
    rw [e]
    exact mul_mem (mul_mem hUγ (inv_mem hUk)) (inv_mem hUL)

  have hmm := S.law.mu_mul j hj
  have hMdt : S.muT (j + 1) ((J.fd std).dt j (c, (((sysS H X std).Lv.lev j c).smul γ La))) = S.muT (j + 1) (Matrix.GeneralLinearGroup.det (GlobalTheory.TwU.ratA D.host.F g)) *
      S.muT (j + 1) ((J.fd std).dt j (c, La)) * S.muT (j + 1) (Matrix.GeneralLinearGroup.det κ.1) := by
    rw [hD2, hpt, map_mul, map_mul, ← hD1, hmm.2 _ (mul_mem hUg hUL) _ hUk, hmm.2 _ hUg _ hUL]
  have hMg := S.law.mu_ne hj hUg
  have hMk := S.law.mu_ne hj hUk
  have hχ : ((((J.St j hj.le).K (J.chart std j hj.le (c, La))).lev.chi κ : ℂˣ) : ℂ) ≠ 0 := Units.ne_zero _
  have hP : (∏ τ : D.what₂.Tau, TaylorLogMetric.embT D τ g.1.det) ≠ 0 := Finset.prod_ne_zero_iff.2 fun τ _ => (map_ne_zero _).2 (Units.ne_zero (Matrix.GeneralLinearGroup.det g))
  have hcore : GlobalTheory.TwU.scal0 (sysS H X std) (J.fd std) t.χ S.muT j (c, (((sysS H X std).Lv.lev j c).smul γ La)) La' * (Base.chiFac t.χ _ _ ((J.fd std).kerN j (c, (((sysS H X std).Lv.lev j c).smul γ La))) ((J.fd std).kerN (j + 1) La'))⁻¹ * (S.muT (j + 1) (Matrix.GeneralLinearGroup.det κ.1) * (((((J.St j hj.le).K (J.chart std j hj.le (c, La))).lev.chi κ : ℂˣ) : ℂ))⁻¹) * (((((J.St j hj.le).K (J.chart std j hj.le (c, La))).lev.chi κ : ℂˣ) : ℂ) * S.muT (j + 1) (Matrix.GeneralLinearGroup.det (GlobalTheory.TwU.ratA D.host.F g)) * (∏ τ : D.what₂.Tau, TaylorLogMetric.embT D τ g.1.det) ^ (-(((j * ((sysS H X std).t + 1) / 2 : ℕ) : ℤ) + (((((sysS H X std).Pj (j + 1)).m + 1) / 2 : ℕ) : ℤ)))) =
      GlobalTheory.TwU.scal0 (sysS H X std) (J.fd std) t.χ S.muT j (c, La) La' * (Base.chiFac t.χ _ _ ((J.fd std).kerN j (c, La)) ((J.fd std).kerN (j + 1) La'))⁻¹ := by
    simp only [GlobalTheory.TwU.scal0, Base.chiFac]
    rw [hker, hchi, hMdt]
    exact scal_core _ _ _ _ hMg hMk hχ hP
  have hbQ : (((((J.St j hj.le).K (J.chart std j hj.le (c, La))).lev.chi κ : ℂˣ) : ℂ) * S.muT (j + 1) (Matrix.GeneralLinearGroup.det (GlobalTheory.TwU.ratA D.host.F g)) * (∏ τ : D.what₂.Tau, TaylorLogMetric.embT D τ g.1.det) ^ (-(((j * ((sysS H X std).t + 1) / 2 : ℕ) : ℤ) + (((((sysS H X std).Pj (j + 1)).m + 1) / 2 : ℕ) : ℤ)))) ∈ TaylorLogMetric.Qbar :=
    mul_mem (mul_mem (hr_eq ▸ embLL_mem' D r) hMgA) (zpow_mem (prod_mem fun τ _ => embT_mem' D τ _) _)
  have hb0 : (((((J.St j hj.le).K (J.chart std j hj.le (c, La))).lev.chi κ : ℂˣ) : ℂ) * S.muT (j + 1) (Matrix.GeneralLinearGroup.det (GlobalTheory.TwU.ratA D.host.F g)) * (∏ τ : D.what₂.Tau, TaylorLogMetric.embT D τ g.1.det) ^ (-(((j * ((sysS H X std).t + 1) / 2 : ℕ) : ℤ) + (((((sysS H X std).Pj (j + 1)).m + 1) / 2 : ℕ) : ℤ)))) ≠ 0 := mul_ne_zero (mul_ne_zero hχ hMg) (zpow_ne_zero _ hP)
  have hALQ : GlobalTheory.TwU.scal0 (sysS H X std) (J.fd std) t.χ S.muT j (c, La) La' * (Base.chiFac t.χ _ _ ((J.fd std).kerN j (c, La)) ((J.fd std).kerN (j + 1) La'))⁻¹ ∈ TaylorLogMetric.Qbar := mul_mem hs1 (inv_mem hf1)
  have hAγQ : GlobalTheory.TwU.scal0 (sysS H X std) (J.fd std) t.χ S.muT j (c, (((sysS H X std).Lv.lev j c).smul γ La)) La' * (Base.chiFac t.χ _ _ ((J.fd std).kerN j (c, (((sysS H X std).Lv.lev j c).smul γ La))) ((J.fd std).kerN (j + 1) La'))⁻¹ * (S.muT (j + 1) (Matrix.GeneralLinearGroup.det κ.1) * (((((J.St j hj.le).K (J.chart std j hj.le (c, La))).lev.chi κ : ℂˣ) : ℂ))⁻¹) ∈ TaylorLogMetric.Qbar := by
    rw [← mul_inv_cancel_right₀ hb0 (GlobalTheory.TwU.scal0 (sysS H X std) (J.fd std) t.χ S.muT j (c, (((sysS H X std).Lv.lev j c).smul γ La)) La' * (Base.chiFac t.χ _ _ ((J.fd std).kerN j (c, (((sysS H X std).Lv.lev j c).smul γ La))) ((J.fd std).kerN (j + 1) La'))⁻¹ * (S.muT (j + 1) (Matrix.GeneralLinearGroup.det κ.1) * (((((J.St j hj.le).K (J.chart std j hj.le (c, La))).lev.chi κ : ℂˣ) : ℂ))⁻¹)), hcore]
    exact mul_mem hALQ (inv_mem hbQ)
  have hp0 : ((D.what₂.places.resChar w : ℕ) : ℂ_[D.what₂.places.resChar w]) ≠ 0 :=
    Nat.cast_ne_zero.2 (Fact.out : (D.what₂.places.resChar w).Prime).ne_zero
  have hpp : GlobalTheory.TwU.pPow (sysS H X std) j (c, La) La' = GlobalTheory.TwU.pPow (sysS H X std) j (c, (((sysS H X std).Lv.lev j c).smul γ La)) La' * ((D.what₂.places.resChar w : ℕ) : ℂ_[D.what₂.places.resChar w]) ^ (∑ v : (sysS H X std).Pl, (sysS H X std).vm v (j + 1) * (len (sysS H X std) v j (((sysS H X std).Lv.lev j c).smul γ La) - len (sysS H X std) v j La)) := by
    unfold GlobalTheory.TwU.pPow
    rw [← zpow_add₀ hp0, ← Finset.sum_add_distrib]
    congr 1
    refine Finset.sum_congr rfl fun v _ => ?_
    dsimp only
    ring
  have hq0 : ((D.what₂.places.resChar w : ℕ) : ℂ_[D.what₂.places.resChar w]) ^ (∑ v : (sysS H X std).Pl, (sysS H X std).vm v (j + 1) * (len (sysS H X std) v j (((sysS H X std).Lv.lev j c).smul γ La) - len (sysS H X std) v j La)) ≠ 0 := zpow_ne_zero _ hp0
  have hl0 := lamC_ne' S.lam hbQ hb0
  rw [hkap, hpp, ← hcore, lamC_mul' S.lam hAγQ hbQ]
  field_simp

end
