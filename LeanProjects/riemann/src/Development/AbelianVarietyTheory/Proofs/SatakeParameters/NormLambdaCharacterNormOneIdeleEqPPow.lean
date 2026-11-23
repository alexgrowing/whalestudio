import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsUnifAt
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsPowNormOneIdeleEqPrincipalMulIntegralUnit
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.PhiAMemRange
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.NormLamCTypeNormOne
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SumAltSignRange
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.MtFiniteOrder
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.StepCharacterLawsNormOneIdelesOfKernelChain
import Formalism.LocalToGlobal.PairingIndexBounds.OrthogonalChartLevels.ChartPosEqOfIw
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.DIV Formalism.UG Formalism.L2.Ker Formalism.L2.G.Pend Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert GlobalTheory.TwV GlobalTheory.TwV.Xc TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.TwV.Xc

set_option maxHeartbeats 4000000 in

theorem lambdaCharacter_norm_eq_p_pow_of_pos : Sites (fun {D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X} [Fact (D.what₂.places.resChar w).Prime] {std t J} S => S.Pos → ∀ j (hj : j < D.R.m), FillAt (hT := hT) (H := H) (X := X) std j hj → ∀ x ∈ U1 (sigD D), ‖TaylorLogMetric.lamC S.lam (S.muT (j + 1) x)‖ = ‖((D.what₂.places.resChar w : ℕ) : ℂ_[D.what₂.places.resChar w])‖ ^ (∑ v : (sysS H X std).Pl, (sysS H X std).vm v (j + 1) * ordA (A0 J) v x)) := by
  intro D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X _ std t J S _hD hSpl hPos j hj hFill x hx
  have hsc : ∀ y, sigD D y = D.host.conj y := fun y => bridge_star_holds D.R D.host y
  have hσ : ∀ a, sigD D (sigD D a) = a := fun a => by rw [hsc a]; exact Formalism.L2.PairingIndexBounds.F.sigD_conj D a
  obtain ⟨m, z, k, hm, hz, hkU, hkI, hxm⟩ := exists_pow_normOne_idele_eq_principal_mul_integralUnit _ _ (sigD D) hσ x hx
  have hz' : (z : D.host.E) * D.host.conj (z : D.host.E) = 1 := by rw [← hsc]; exact hz
  have hzU := GlobalTheory.TwV.MuLawPf.rationalIdele_mem_normOne_of_norm_eq_one z hz'
  have hmul := S.law.mu_mul j hj
  have hpow : ∀ n : ℕ, S.muT (j + 1) (x ^ n) = S.muT (j + 1) x ^ n := by
    intro n
    induction n with
    | zero => rw [pow_zero, pow_zero, hmul.1]
    | succ n ih => rw [pow_succ, pow_succ, hmul.2 _ (pow_mem hx n) _ hx, ih]
  have hsplit : S.muT (j + 1) x ^ m = S.muT (j + 1) (ratId D.host.F D.host.E z) * S.muT (j + 1) k := by
    rw [← hpow, hxm, hmul.2 _ hzU _ hkU]
  obtain ⟨e, he, hrat⟩ := S.law.mu_rat j hj

  obtain ⟨y, hy⟩ := GlobalTheory.TwV.MuLawPf.exists_unitaryOne_det_eq_normOneIdele hkU
  obtain ⟨n, hn, hroot⟩ := GlobalTheory.TieFinOrd.mt_finite_order J.A J.dtU J.a J.pins J.tie j hj y (by rw [hy]; exact hkI)
  have hkroot : S.muT (j + 1) k ^ n = 1 := by
    rw [← hy, S.law.mu_read j hj y, ← Units.val_pow_eq_pow_val, hroot, Units.val_one]

  have ha := S.law.mu_alg j hj x hx
  have hb := S.law.mu_alg j hj _ hzU
  have hc := S.law.mu_alg j hj k hkU
  have hlamC : ∀ (a : ℂ) (h : a ∈ TaylorLogMetric.Qbar), TaylorLogMetric.lamC S.lam a = S.lam ⟨a, h⟩ := fun a h => by
    unfold TaylorLogMetric.lamC; rw [dif_pos h]
  have eQ : (⟨S.muT (j + 1) x, ha⟩ : TaylorLogMetric.Qbar) ^ m = ⟨_, hb⟩ * ⟨_, hc⟩ := Subtype.ext (by push_cast; exact hsplit)
  have eQk : (⟨S.muT (j + 1) k, hc⟩ : TaylorLogMetric.Qbar) ^ n = 1 := Subtype.ext (by push_cast; exact hkroot)
  have hnormk : ‖S.lam ⟨_, hc⟩‖ = 1 := by
    have h1 := congrArg (fun q => ‖S.lam q‖) eQk
    simp only [map_pow, norm_pow, map_one, norm_one] at h1
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) hn.ne').1 h1
  have hnorm_m : ‖TaylorLogMetric.lamC S.lam (S.muT (j + 1) x)‖ ^ m = ‖TaylorLogMetric.lamC S.lam (S.muT (j + 1) (ratId D.host.F D.host.E z))‖ := by
    have h1 := congrArg (fun q => ‖S.lam q‖) eQ
    simp only [map_pow, norm_pow, map_mul, norm_mul, hnormk, mul_one] at h1
    rw [hlamC _ ha, hlamC _ hb]
    exact h1
  have hratN := GlobalTheory.TwU.RatNorm.norm_lamC_type_normOne D _ (sysS H X std) S.E.toCEmb (hT.gat_pos u w hg) S.lam (J.rho std) hPos e (z : D.host.E) hz'
  rw [← hrat z hz'] at hratN

  have hvm : ∀ v : (sysS H X std).Pl, (sysS H X std).vm v (j + 1) = ∑ s : Fin ((sysS H X std).G.P.n' v), (if IsOddPos s then -1 else 1) * e (hT.gat_pos u w hg ⟨v, s⟩) := by
    intro v
    refine vm_shift_cancels _ (sysS H X std) v (j + 1) (fun s => e (hT.gat_pos u w hg ⟨v, s⟩))
      (((j * ((sysS H X std).t + 1) / 2 : ℕ) : ℤ) + (((((sysS H X std).Pj (j + 1)).m + 1) / 2 : ℕ) : ℤ)) (fun s => ?_)
    rw [hFill e he v s, sub_sub]

  have hord : ∀ v : (sysS H X std).Pl, (m : ℤ) * ordA (A0 J) v x = ordP ((sysS H X std).G.P.W v) (D.what₂.places.resChar w) (J.rho std v (z : D.host.E)) := by
    intro v
    obtain ⟨hadd, hint, hratO, -⟩ := OrdA.ordA_props _ _ _ _ _ (A0 J) J.one.int hSpl.1 v
    have hp : ∀ n : ℕ, ordA (A0 J) v (x ^ n) = n * ordA (A0 J) v x := by
      intro n
      induction n with
      | zero =>
        have h1 := hadd 1 1
        rw [mul_one] at h1
        rw [pow_zero, Nat.cast_zero, zero_mul]
        linarith
      | succ n ih => rw [pow_succ, hadd, ih]; push_cast; ring
    rw [← hp, hxm, hadd, hratO, hint k hkI, add_zero]
  rw [← pow_left_inj₀ (norm_nonneg _) (zpow_nonneg (norm_nonneg _) _) hm.ne', hnorm_m, hratN, ← zpow_natCast, ← zpow_mul]
  congr 1
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun v _ => ?_
  rw [hvm v, ← hord v]
  ring

end GlobalTheory.TwV.Xc

end
