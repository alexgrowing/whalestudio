import Development.AbelianVarietyTheory.Proofs.SatakeParameters.EquivFrameBTheta
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.RkLe
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.UnitaryBlockMatricesReadInPlaceFieldStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.RealPlaceBlockWeightLastEntryConsecutiveLevelsStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.RealisingPolynomialBlockwiseHomogeneousStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LinearChoiceEqRealisingPolynomialStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.FramePolynomialsWeightRealisedNextLevelStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ModelPartitionSizeExtensionFirstLastRowsStatement
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelProjection Formalism.L2.KerInert.QuadraticBaseChangeGL3 Formalism.L2.KerInert.SecondKernelDifference Formalism.L2.KerInert.SecondKernelHermitian GlobalTheory.TwV.DelA
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TwV.DelA

theorem zpow_toNat_div' {K : Type} [Field K] (x : K) (hx : x ≠ 0) (e : ℤ) :
    x ^ e.toNat * (x ^ (-e).toNat)⁻¹ = x ^ e := by
  rw [← zpow_natCast, ← zpow_natCast, ← zpow_neg, ← zpow_add₀ hx]
  congr 1
  omega

theorem blk_scal_odd {K : Type} [Field K] (c δ : K) (hc : c ≠ 0) (hδ : δ ≠ 0) (N : ℕ) (hN : 1 ≤ N) (cM sz : ℤ)
    (h0 : 0 ≤ (N : ℤ) * cM - sz) :
    ((c * δ⁻¹) ^ (N - 1)) ^ ((N : ℤ) * cM - sz).toNat *
      ((δ⁻¹) ^ (cM - sz).toNat * ((c * δ⁻¹) ^ N) ^ (cM - (N : ℤ) * cM + sz).toNat) *
      ((δ⁻¹) ^ (-(cM - sz)).toNat * ((c * δ⁻¹) ^ N) ^ (-(cM - (N : ℤ) * cM + sz)).toNat)⁻¹ =
    c ^ sz * δ ^ (-cM) := by
  have hκ : c * δ⁻¹ ≠ 0 := mul_ne_zero hc (inv_ne_zero hδ)
  have hd : δ⁻¹ ≠ 0 := inv_ne_zero hδ
  have hκN : (c * δ⁻¹) ^ N ≠ 0 := pow_ne_zero _ hκ
  have e1 : ((c * δ⁻¹) ^ (N - 1)) ^ ((N : ℤ) * cM - sz).toNat = (c * δ⁻¹) ^ (((N : ℤ) - 1) * ((N : ℤ) * cM - sz)) := by
    rw [← pow_mul, ← zpow_natCast]
    congr 1
    push_cast [Int.toNat_of_nonneg h0, Nat.cast_sub hN]
    ring
  calc _ = ((c * δ⁻¹) ^ (N - 1)) ^ ((N : ℤ) * cM - sz).toNat *
        ((δ⁻¹) ^ (cM - sz).toNat * ((δ⁻¹) ^ (-(cM - sz)).toNat)⁻¹) *
        (((c * δ⁻¹) ^ N) ^ (cM - (N : ℤ) * cM + sz).toNat * (((c * δ⁻¹) ^ N) ^ (-(cM - (N : ℤ) * cM + sz)).toNat)⁻¹) := by
          ring
    _ = (c * δ⁻¹) ^ (((N : ℤ) - 1) * ((N : ℤ) * cM - sz)) * (δ⁻¹) ^ (cM - sz) *
        (c * δ⁻¹) ^ ((N : ℤ) * (cM - (N : ℤ) * cM + sz)) := by
          rw [zpow_toNat_div' _ hd, zpow_toNat_div' _ hκN, e1, ← zpow_natCast (c * δ⁻¹) N, ← zpow_mul]
    _ = c ^ (((N : ℤ) - 1) * ((N : ℤ) * cM - sz) + (N : ℤ) * (cM - (N : ℤ) * cM + sz)) *
        δ ^ (-(((N : ℤ) - 1) * ((N : ℤ) * cM - sz)) + -(cM - sz) + -((N : ℤ) * (cM - (N : ℤ) * cM + sz))) := by
          rw [mul_zpow, mul_zpow, inv_zpow', inv_zpow', inv_zpow', zpow_add₀ hc, zpow_add₀ hδ, zpow_add₀ hδ]
          ring
    _ = _ := by
          congr 2 <;> ring

set_option maxHeartbeats 1000000 in

theorem scal_tauV : ∀ {p : ℕ} [Fact p.Prime] (X : Sys p) (D : D7) (pos : (Σ v : X.Pl, Fin (X.G.P.n' v)) ≃ D.what₂.Tau) (Kc : Type) [Field Kc] [Algebra (Formalism.MainNotions.FormalGroupSystem.K0 p) Kc] [Algebra X.G.Kf Kc] (ι : ℂ →+* Kc) (ρ : ∀ v : X.Pl, D.host.E →+* X.G.P.Qq v), PosTie X D pos Kc ι ρ → ∀ (fd : FData X D) (c : Kc), c ≠ 0 → ∀ (j : ℕ) (hN : RankTie X D j) (La' : X.Lt (j + 1)) (M : GL (Fin (D.R.N (j + 1))) D.host.E), StdU D M → FrIs fd ρ (j + 1) La' (rkT X D hN) M → ∀ (ν : D.what₂.Tau → Fin (D.R.N j) → ℕ), NuIs X D pos j ν → GlobalTheory.FrameB.sS X Kc j (GlobalTheory.FrameB.kV Kc fd c j La') * GlobalTheory.FrameB.kN X Kc j (GlobalTheory.FrameB.wV Kc fd c j La') (GlobalTheory.FrameB.kV Kc fd c j La') * (GlobalTheory.FrameB.kD X Kc j (GlobalTheory.FrameB.wV Kc fd c j La') (GlobalTheory.FrameB.kV Kc fd c j La'))⁻¹ = ∏ τ, if IsOddPos (pos.symm τ).2 then c ^ szT X D pos j τ * ι (embT D τ (M : Matrix (Fin (D.R.N (j + 1))) (Fin (D.R.N (j + 1))) D.host.E).det) ^ cT1 X D pos j τ else 1 := by
  intro p _ X D pos Kc _ _ _ ι ρ hT fd c hc j hN La' M hU hFr ν hν
  obtain ⟨-, hsz, -, hle, -⟩ := GlobalTheory.T.modelPartition_size_extension_firstLast_rows X D pos j hN ν hν
  have hN1 : 1 ≤ NN X.G.P.m X.t j := by unfold NN; omega

  have hdet : ∀ (v : X.Pl) (s : Fin (X.G.P.n' v)), (GlobalTheory.FrameB.mk Kc fd j La' v s).det =
      Formalism.L2.G.Pend.tw X Kc v s (ρ v (M : Matrix (Fin (D.R.N (j + 1))) (Fin (D.R.N (j + 1))) D.host.E).det) := by
    intro v s
    unfold GlobalTheory.FrameB.mk
    rw [det_mAt, hFr v, Matrix.det_submatrix_equiv_self, RingHom.map_det (ρ v)]
    rfl
  have hdet0 : ∀ (v : X.Pl) (s : Fin (X.G.P.n' v)), (GlobalTheory.FrameB.mk Kc fd j La' v s).det ≠ 0 := by
    intro v s
    rw [hdet]
    exact (((M.isUnit.map (Matrix.detMonoidHom))).map (ρ v)).map (Formalism.L2.G.Pend.tw X Kc v s) |>.ne_zero

  have hbd : ∀ b : (Σ v : X.Pl, Fin (X.G.P.n' v)),
      0 ≤ (NN X.G.P.m X.t j : ℤ) * cMu X j b.1 b.2 - szMu X j b.1 b.2 := by
    intro b
    have h1 : szMu X j b.1 b.2 = szT X D pos j (pos b) := by
      show _ = szMu X j (pos.symm (pos b)).1 (pos.symm (pos b)).2; rw [Equiv.symm_apply_apply]
    have h2 : cMu X j b.1 b.2 = cT1 X D pos j (pos b) := by
      show _ = cMu X j (pos.symm (pos b)).1 (pos.symm (pos b)).2; rw [Equiv.symm_apply_apply]
    rw [h1, h2, hsz, ← hN.1]
    have : ∑ r : Fin (D.R.N j), (ν (pos b) r : ℤ) ≤ ∑ _r : Fin (D.R.N j), cT1 X D pos j (pos b) := by
      refine Finset.sum_le_sum fun r _ => ?_
      have := hle (pos b) (Fin.castLE (rk_le X D hN) r)
      simpa [extNu] using this
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at this
    linarith
  have hkN : GlobalTheory.FrameB.kN X Kc j (GlobalTheory.FrameB.wV Kc fd c j La') (GlobalTheory.FrameB.kV Kc fd c j La') =
      ∏ b : (Σ v : X.Pl, Fin (X.G.P.n' v)), if IsOddPos b.2 then
        ((GlobalTheory.FrameB.wV Kc fd c j La' b.1 b.2).det⁻¹) ^ (exY X j b.1 b.2).toNat *
          (GlobalTheory.FrameB.kV Kc fd c j La' b.1 b.2 ^ NN X.G.P.m X.t j) ^ (exT X j b.1 b.2).toNat else 1 := by
    unfold GlobalTheory.FrameB.kN
    rw [Fintype.prod_sigma]
  have hkD : GlobalTheory.FrameB.kD X Kc j (GlobalTheory.FrameB.wV Kc fd c j La') (GlobalTheory.FrameB.kV Kc fd c j La') =
      ∏ b : (Σ v : X.Pl, Fin (X.G.P.n' v)), if IsOddPos b.2 then
        ((GlobalTheory.FrameB.wV Kc fd c j La' b.1 b.2).det⁻¹) ^ (-exY X j b.1 b.2).toNat *
          (GlobalTheory.FrameB.kV Kc fd c j La' b.1 b.2 ^ NN X.G.P.m X.t j) ^ (-exT X j b.1 b.2).toNat else 1 := by
    unfold GlobalTheory.FrameB.kD
    rw [Fintype.prod_sigma]
  rw [← Fintype.prod_equiv pos _ _ (fun _ => rfl), hkN, hkD, GlobalTheory.FrameB.sS, ← Finset.prod_inv_distrib,
    ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun b _ => ?_
  beta_reduce
  rw [Equiv.symm_apply_apply]
  by_cases ho : IsOddPos b.2
  · simp only [if_pos ho]
    have hw : GlobalTheory.FrameB.wV Kc fd c j La' b.1 b.2 = GlobalTheory.FrameB.mk Kc fd j La' b.1 b.2 := by
      unfold GlobalTheory.FrameB.wV; rw [if_pos ho]
    have hk : GlobalTheory.FrameB.kV Kc fd c j La' b.1 b.2 = c * (GlobalTheory.FrameB.mk Kc fd j La' b.1 b.2).det⁻¹ := by
      unfold GlobalTheory.FrameB.kV; rw [if_pos ho]
    rw [hw, hk, exY, exT, blk_scal_odd c _ hc (hdet0 b.1 b.2) _ hN1 _ _ (hbd b)]
    have h1 : szMu X j b.1 b.2 = szT X D pos j (pos b) := by
      show _ = szMu X j (pos.symm (pos b)).1 (pos.symm (pos b)).2; rw [Equiv.symm_apply_apply]
    have h2 : cMu X j b.1 b.2 = cT1 X D pos j (pos b) := by
      show _ = cMu X j (pos.symm (pos b)).1 (pos.symm (pos b)).2; rw [Equiv.symm_apply_apply]
    have h3 := (GlobalTheory.T.unitaryBlockMatrices_read_in_placeField X D pos Kc ι ρ hT M hU b.1 b.2).2
    rw [if_pos ho] at h3
    rw [h1, h2, hdet, h3, ← zpow_mul]
    congr 2
    ring
  · simp only [if_neg ho]
    simp

end GlobalTheory.TwV.DelA
