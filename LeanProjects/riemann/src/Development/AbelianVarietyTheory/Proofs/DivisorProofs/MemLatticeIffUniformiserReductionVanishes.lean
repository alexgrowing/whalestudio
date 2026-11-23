import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NabBaseChange
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemCompletedPairLatticeIffFrameMatrixIntegralOnHStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemHatIffOfSelfDual
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FinPartMulIncAMem
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR
open Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open GlobalTheory.ConjTwist GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.OnTies GlobalTheory.OnCmp GlobalTheory.BaseCmp
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Classical
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000
namespace GlobalTheory.DilKer

open GlobalTheory.StdFrames (cpt)

theorem frMapO_dil {D : D7} (i : Fin D.R.m) (βS : GL (Fin (Vc D i).rank) (EAf D)) (βT : GL (Fin (Wc D i).rank) (EAf D))
    (a : D.host.E) (z : WO (Vc D i) (Wc D i)) :
    frMapO (Vc D i) (Wc D i) βS βT (dil i a z) = eToEAf D a • frMapO (Vc D i) (Wc D i) βS βT z := by
  have h : (dil i a z).map (toEAf D) = eToEAf D a • z.map (toEAf D) := by
    ext k l
    simp only [dil, Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, RingHom.map_mul, GlobalTheory.IdemIntegral.toEAf_incA]
  simp only [frMapO, h, Matrix.mul_smul, Matrix.smul_mul]

theorem isHalf_dil {D : D7} (i : Fin D.R.m) (e : AE D) (a : D.host.E) {z : WO (Vc D i) (Wc D i)} (hz : IsHalf e z) :
    IsHalf e (dil i a z) := fun k l => by
  simp only [dil, Matrix.map_apply]
  rw [mul_left_comm, hz k l]

theorem frMapO_half {D : D7} (i : Fin D.R.m) (βS : GL (Fin (Vc D i).rank) (EAf D)) (βT : GL (Fin (Wc D i).rank) (EAf D))
    {e : AE D} {z : WO (Vc D i) (Wc D i)} (hz : IsHalf e z) (k l) :
    toEAf D e * frMapO (Vc D i) (Wc D i) βS βT z k l = frMapO (Vc D i) (Wc D i) βS βT z k l := by
  have h : z.map (toEAf D) = toEAf D e • z.map (toEAf D) := by
    ext a b
    simp only [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, ← RingHom.map_mul, hz a b]
  have h2 : frMapO (Vc D i) (Wc D i) βS βT z = toEAf D e • frMapO (Vc D i) (Wc D i) βS βT z := by
    conv_lhs => rw [frMapO, h]
    simp only [frMapO, Matrix.mul_smul, Matrix.smul_mul]
  conv_rhs => rw [h2]
  rfl

theorem val_cpt_eToEAf {D : D7} (PP : Pl D.host.E) (x : D.host.E) :
    Valued.v (cpt PP (eToEAf D x)) = PP.valuation D.host.E x := by
  have : eToEAf D x = GlobalTheory.IndefiniteRowSideFullHecke.FlatSpaceComponents.inc D x := rfl
  rw [this, GlobalTheory.AdIsom.cpt_inc, Formalism.UG.P.levelaf_valued_algebraMap]

theorem mem_int_of_mul {D : D7} {Q : Finset (Pl D.host.E)} {e : AE D} (he : IsIdemSum e Q) {ϖ : 𝓞 D.host.E}
    (hϖ : ∀ PP ∈ Q, ϖ ∈ PP.asIdeal ∧ ϖ ∉ PP.asIdeal ^ 2) {m : EAf D} (hm : toEAf D e * m = m)
    (hy : eToEAf D (ϖ : D.host.E) * m ∈ Formalism.L2.Herm.intAf D.host.F D.host.E)
    (hr : ∀ PP ∈ Q, Valued.v (cpt PP (eToEAf D (ϖ : D.host.E) * m)) < 1) :
    m ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := by
  obtain ⟨⟨es, hes, rfl⟩, -⟩ := he
  refine (GlobalTheory.AdIsom.mem_OA m).2 fun P => ?_
  by_cases hP : P ∈ Q
  · have h1 := hr P hP
    rw [RingHom.map_mul, Valuation.map_mul, val_cpt_eToEAf, GlobalTheory.HeckeDetChar.val_unif (hϖ P hP).1 (hϖ P hP).2] at h1
    by_cases h0 : Valued.v (cpt P m) = 0
    · rw [h0]; exact zero_le'
    obtain ⟨k, hk⟩ : ∃ k : ℤ, Valued.v (cpt P m) = WithZero.exp k := ⟨_, (WithZero.exp_log h0).symm⟩
    rw [hk] at h1 ⊢
    rw [← WithZero.exp_add, ← WithZero.exp_zero, WithZero.exp_lt_exp] at h1
    rw [← WithZero.exp_zero, WithZero.exp_le_exp]
    omega
  · have h0 : cpt P (toEAf D (∑ PP ∈ Q, es PP)) = 0 := by
      rw [map_sum, map_sum]
      exact Finset.sum_eq_zero fun PP hPP => (GlobalTheory.StdFrames.cpt_of_isIdemAt (hes PP hPP)).2 P fun h => hP (h ▸ hPP)
    have := congrArg (cpt P) hm
    rw [RingHom.map_mul, h0, zero_mul] at this
    rw [← this, Valuation.map_zero]
    exact zero_le'

theorem mem_localLattice_iff_redM : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Hk3.Core R F → QGuard R → ∀ (i : Fin D.R.m), VStd D i → ∀ (Q : Finset (Pl D.host.E)), (∃ t, Q ⊆ R.Q t) → ∀ eQ : AE D, IsIdemSum eQ Q → ∀ ϖ : 𝓞 D.host.E, ϖ ≠ 0 → (∀ PP ∈ Q, ϖ ∈ PP.asIdeal ∧ ϖ ∉ PP.asIdeal ^ 2) → ∀ z : WO (Vc D i) (Wc D i), IsHalf eQ z → dil i (ϖ : D.host.E) z ∈ lattice₂ R i → (z ∈ lattice₂ R i ↔ ∀ PP ∈ Q, redM PP (frMapO (Vc D i) (Wc D i) (R.βV i) (R.βW i) (dil i (ϖ : D.host.E) z)) = 0) := by
  intro D G _ _ Pl0 T0 A Ks _ _ _ R F hC hG i hV Q hQ eQ he ϖ hϖ0 hϖ z hz hϖz
  have hI := GlobalTheory.T.mem_completedPairLattice_iff_frameMatrix_integral_on_half D G Pl0 T0 A Ks R F hC hG i hV Q hQ eQ he
  rw [frMapO_dil]
  constructor
  · intro hzL PP hPP
    have hM := (hI z hz).2 hzL
    ext k l
    have hϖi : eToEAf D (ϖ : D.host.E) ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := by
      rw [← GlobalTheory.IdemIntegral.toEAf_incA]
      exact GlobalTheory.IdemIntegral.toEAf_mem_of_finPart (GlobalTheory.SplitIndex.finPart_incA_mem ϖ)
    have hint : eToEAf D (ϖ : D.host.E) * frMapO (Vc D i) (Wc D i) (R.βV i) (R.βW i) z k l ∈
        Formalism.L2.Herm.intAf D.host.F D.host.E := mul_mem hϖi (hM k l)
    simp only [redM, Matrix.smul_apply, smul_eq_mul, Matrix.zero_apply, dif_pos hint]
    refine (GlobalTheory.AdIsom.resS_eq_zero_iff_cpt PP ⟨_, hint⟩).2 ?_
    change Valued.v (cpt PP (eToEAf D (ϖ : D.host.E) * _)) < 1
    rw [RingHom.map_mul, Valuation.map_mul, val_cpt_eToEAf, GlobalTheory.HeckeDetChar.val_unif (hϖ PP hPP).1 (hϖ PP hPP).2]
    calc WithZero.exp (-1 : ℤ) * Valued.v (cpt PP (frMapO (Vc D i) (Wc D i) (R.βV i) (R.βW i) z k l))
        ≤ WithZero.exp (-1 : ℤ) * 1 := by gcongr; exact (GlobalTheory.AdIsom.mem_OA _).1 (hM k l) PP
      _ < 1 := by rw [mul_one, ← WithZero.exp_zero, WithZero.exp_lt_exp]; omega
  · intro hred
    have hN := (hI _ (isHalf_dil i eQ _ hz)).2 hϖz
    rw [frMapO_dil] at hN
    have hN' : ∀ k l, eToEAf D (ϖ : D.host.E) * frMapO (Vc D i) (Wc D i) (R.βV i) (R.βW i) z k l ∈
        Formalism.L2.Herm.intAf D.host.F D.host.E := fun k l => hN k l
    refine (hI z hz).1 fun k l => mem_int_of_mul he hϖ (frMapO_half i _ _ hz k l) (hN' k l) fun PP hPP => ?_
    have h1 := congrFun (congrFun (hred PP hPP) k) l
    simp only [redM, Matrix.smul_apply, smul_eq_mul, Matrix.zero_apply, dif_pos (hN' k l)] at h1
    exact (GlobalTheory.AdIsom.resS_eq_zero_iff_cpt PP ⟨_, hN' k l⟩).1 h1

end GlobalTheory.DilKer
