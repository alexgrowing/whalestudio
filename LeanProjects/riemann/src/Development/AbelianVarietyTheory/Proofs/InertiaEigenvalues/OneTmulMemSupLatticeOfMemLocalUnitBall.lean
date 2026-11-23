import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.SmulMemRatForms
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ValCCuspOfSmul
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsCdvrReadingInCpOfFiniteResidue
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralCuspFormsFullLattice
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SupLatticeLocalisationOfUnitBall
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT Formalism.L2.Pj GlobalTheory.GeoTie
open scoped TensorProduct

set_option autoImplicit false
noncomputable section
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

namespace GlobalTheory.GeoTie

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section BallSup

variable {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 I0 T1 : Type}
  {A3 : FamIn3 D.what₂.LL Γ Pl0 I0 (List ℕ) T1 D.R.m} {T0 : CoreJ D} [Algebra T0.Q.c.F D.what₂.LL]
  {Rl : RealDat3 D A3 T0.Q.c.F} {cG : Formalism.L2.DIV.G0 Rl.Pg D.R.r ≃* G0g D.nd} {S : NX.RatDat D.ntw} (YS : NX.NExpRealS Rl cG S)
  {κ : ∀ j : Fin D.R.m, WeightFamilies.Wt D ((j : ℕ) + 1)} {v₀ : ∀ (j : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (Rl.MW j σ).Vec}
  (fw : FWTie T0 Rl.toRealDat κ v₀) {i : D.ntw.Tw} (iC : FractionRing (D.ntw.O i) →+* ℂ_[D.ntw.l i]) (b : Bool)
  (j : Fin D.R.m)

theorem nrm_le_one_of_mem_locBall {f : NX.FmK S ((j : ℕ) + 1)} (hf : f ∈ locBall YS fw iC b j)
    (y : (Rl.FW j).Pt (placeC YS iC b)) :
    (Rl.FW j).nrm (placeC YS iC b) y (fw.e j (cuspOf YS fw j f)) ≤ 1 := by
  rw [fw.nrm_eq, Core.nrmM_le_one_iff]
  obtain ⟨q, hq⟩ := (fw.pt j (placeC YS iC b) y).2
  rcases q with ⟨qv, T, io, e, ho, y', hy', eta, heta, rfl⟩
  obtain ⟨k, hk⟩ := ReadExist.exists_isReading (D.ntw.l i) T0.Q.c.F (embC YS iC b) T io e ho hy'
  obtain ⟨z, hz⟩ := PtC.exists_of_reading hk y' hy'
  have h1 := hf z
  rw [hz _ _ _ (cuspOf_mem_sec YS fw j f)] at h1
  obtain ⟨a, ha⟩ := (hk.int _).1 h1
  rw [← hq]
  change 0 ≤ nval T.V e (evI y' _)
  by_cases hx : evI y' (cuspOf YS fw j f : T0.R ((j : ℕ) + 1)) = 0
  · rw [hx, nval_zero]; exact le_top
  · rw [nval_of_ne hx]
    exact EReal.coe_nonneg.2 (div_nonneg (Int.cast_nonneg
      ((GlobalTheory.CompleteValExt.exists_algebraMap_eq_iff _).1 ⟨a, ha⟩)) (Nat.cast_nonneg _))

theorem one_tmul_mem_Bsup_of_mem_locBall
    (hiC : ∀ x, ‖iC x‖ ≤ 1 ↔ x ∈ (algebraMap (D.ntw.O i) (FractionRing (D.ntw.O i))).range)
    (f : NX.FmK S ((j : ℕ) + 1)) (hf : f ∈ locBall YS fw iC b j) :
    (show NX.Fm S i ((j : ℕ) + 1) b from (1 : NX.KB S i b) ⊗ₜ[S.Ks] f) ∈ NX.Bsup S i ((j : ℕ) + 1) b := by
  obtain ⟨s, hs, hsM⟩ := GlobalTheory.supLattice_localisation_of_unitBall D.what₂.LL T0.Q.c.F _ _ _ (Rl.FW j)
    (GlobalTheory.GoodLat.Obj.mkFull_of_tie fw j).2 (placeC YS iC b) (fw.e j (cuspOf YS fw j f))
    (nrm_le_one_of_mem_locBall YS fw iC b j hf)
  rw [e_cuspOf] at hsM
  set c : S.Ks := (YS.fi j).eK.symm (s : T0.Q.c.F) with hcdef
  have hc : (YS.fi j).e (c • (show ↥(S.A ((j : ℕ) + 1)).WK from f).1) = s • (YS.fi j).e (show ↥(S.A ((j : ℕ) + 1)).WK from f).1 := by
    rw [← algebraMap_smul D.what₂.LL c, LinearEquiv.map_smul, ← (YS.fi j).eK_LL c, hcdef, RingEquiv.apply_symm_apply,
      algebraMap_smul]
    exact (algebraMap_smul T0.Q.c.F s _)
  have hcM : c • (show ↥(S.A ((j : ℕ) + 1)).WK from f).1 ∈ (S.A ((j : ℕ) + 1)).MK := by
    rw [(YS.fi j).mkK, hc]; exact hsM

  have hgen : (show NX.Fm S i ((j : ℕ) + 1) b from (1 : NX.KB S i b) ⊗ₜ[S.Ks] (c • f)) ∈ NX.Bsup S i ((j : ℕ) + 1) b :=
    Submodule.subset_span ⟨c • f, hcM, rfl⟩
  have heK : eKs YS c = (s : T0.Q.c.F) := by
    apply (algebraMap T0.Q.c.F D.what₂.LL).injective
    rw [eKs_LL, ← (YS.fi j).eK_LL c, hcdef, RingEquiv.apply_symm_apply]
  obtain ⟨x, hx⟩ : ∃ x : FractionRing (D.ntw.O i), x = NX.ιK S i b c := ⟨_, rfl⟩
  have hn1 : ‖iC x‖ = 1 := by
    rw [hx]
    change ‖embS S iC b c‖ = 1
    rw [← embC_eKs YS iC b, heK]
    refine le_antisymm (norm_int_le_one _ s) (not_lt.1 fun h => hs ?_)
    exact (mem_placeAt _ s).2 h
  have hne : x ≠ 0 := fun h => by
    rw [h, map_zero, norm_zero] at hn1; exact zero_ne_one hn1
  obtain ⟨u, hu⟩ := (hiC x⁻¹).1 (by rw [map_inv₀, norm_inv, hn1, inv_one])
  have key : (show NX.Fm S i ((j : ℕ) + 1) b from (1 : NX.KB S i b) ⊗ₜ[S.Ks] f) =
      u • (show NX.Fm S i ((j : ℕ) + 1) b from (1 : NX.KB S i b) ⊗ₜ[S.Ks] (c • f)) := by
    rw [← algebraMap_smul (FractionRing (D.ntw.O i)) u, hu]
    have h1 : (c • (1 : NX.KB S i b)) = (show NX.KB S i b from x) := by
      rw [Algebra.smul_def, mul_one, hx]; rfl
    change (1 : NX.KB S i b) ⊗ₜ[S.Ks] f =
      (show NX.KB S i b from x⁻¹) • ((1 : NX.KB S i b) ⊗ₜ[S.Ks] (c • f) : NX.KB S i b ⊗[S.Ks] NX.FmK S ((j : ℕ) + 1))
    rw [← TensorProduct.smul_tmul, h1, TensorProduct.smul_tmul', smul_eq_mul]
    congr 1
    exact (inv_mul_cancel₀ hne).symm
  rw [key]
  exact Submodule.smul_mem _ u hgen

end BallSup

theorem one_tmul_mem_Bsup : ∀ (D : D7) (Γ : Type) [Group Γ] [Fintype Γ] (Pl0 I0 T1 : Type) (A3 : FamIn3 D.what₂.LL Γ Pl0 I0 (List ℕ) T1 D.R.m) (T0 : CoreJ D) [Algebra T0.Q.c.F D.what₂.LL] (Rl : RealDat3 D A3 T0.Q.c.F) (cG : Formalism.L2.DIV.G0 Rl.Pg D.R.r ≃* G0g D.nd) (S : NX.RatDat D.ntw) (YS : NX.NExpRealS Rl cG S) (κ : ∀ j : Fin D.R.m, WeightFamilies.Wt D ((j : ℕ) + 1)) (v₀ : ∀ (j : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (Rl.MW j σ).Vec) (fw : FWTie T0 Rl.toRealDat κ v₀) (i : D.ntw.Tw) (iC : FractionRing (D.ntw.O i) →+* ℂ_[D.ntw.l i]), (∀ x, ‖iC x‖ ≤ 1 ↔ x ∈ (algebraMap (D.ntw.O i) (FractionRing (D.ntw.O i))).range) → ∀ (b : Bool) (j : Fin D.R.m), ∀ f ∈ locBall YS fw iC b j, (show NX.Fm S i ((j : ℕ) + 1) b from (1 : NX.KB S i b) ⊗ₜ[S.Ks] f) ∈ NX.Bsup S i ((j : ℕ) + 1) b := by
  intro D Γ _ _ Pl0 I0 T1 A3 T0 _ Rl cG S YS κ v₀ fw i iC hiC b j f hf
  exact one_tmul_mem_Bsup_of_mem_locBall YS fw iC b j hiC f hf

end GlobalTheory.GeoTie
