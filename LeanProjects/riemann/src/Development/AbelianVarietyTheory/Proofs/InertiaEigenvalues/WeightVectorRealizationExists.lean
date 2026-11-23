import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.SmulMemRatForms
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ValCCuspOfSmul
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralCuspFormsFullLattice
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ImportsFurther

set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT Formalism.L2.Pj GlobalTheory.GeoTie
open scoped TensorProduct
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

namespace GlobalTheory.GeoTie

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem exists_intMul_mem_MK {LL Ks WL G : Type} [Field LL] [NumberField LL] [Field Ks]
    [NumberField Ks] [Algebra Ks LL] [AddCommGroup WL] [Module LL WL] [Module Ks WL] [IsScalarTower Ks LL WL]
    [Module (𝓞 Ks) WL] [IsScalarTower (𝓞 Ks) Ks WL] {W : (LL →+* ℂ) → Type} [∀ σ, NormedAddCommGroup (W σ)]
    [∀ σ, InnerProductSpace ℂ (W σ)] [Group G] (Φ : Formalism.IndefR.Arith.FormsL LL Ks WL W G)
    (hspan : Submodule.span Ks (Φ.MK : Set WL) = Φ.WK) (x : WL) (hx : x ∈ Φ.WK) :
    ∃ a : 𝓞 Ks, a ≠ 0 ∧ a • x ∈ Φ.MK := by
  first
  | exact @_root_.GlobalTheory.ScalarMultipleMembership.main
  | exact _root_.GlobalTheory.ScalarMultipleMembership.main
  | (apply _root_.GlobalTheory.ScalarMultipleMembership.main <;> assumption)
  | (intros; apply _root_.GlobalTheory.ScalarMultipleMembership.main <;> assumption)
  | (intros; apply @_root_.GlobalTheory.ScalarMultipleMembership.main <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.ScalarMultipleMembership.main ..)

theorem exists_smul_mem_locBall : ∀ (D : D7) (Γ : Type) [Group Γ] [Fintype Γ] (Pl0 I0 T1 : Type) (A3 : FamIn3 D.what₂.LL Γ Pl0 I0 (List ℕ) T1 D.R.m) (T0 : CoreJ D) [Algebra T0.Q.c.F D.what₂.LL] (Rl : RealDat3 D A3 T0.Q.c.F) (cG : Formalism.L2.DIV.G0 Rl.Pg D.R.r ≃* G0g D.nd) (S : NX.RatDat D.ntw) (YS : NX.NExpRealS Rl cG S) (κ : ∀ j : Fin D.R.m, WeightFamilies.Wt D ((j : ℕ) + 1)) (v₀ : ∀ (j : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (Rl.MW j σ).Vec) (fw : FWTie T0 Rl.toRealDat κ v₀) (i : D.ntw.Tw) (iC : FractionRing (D.ntw.O i) →+* ℂ_[D.ntw.l i]), (∀ x, ‖iC x‖ ≤ 1 ↔ x ∈ (algebraMap (D.ntw.O i) (FractionRing (D.ntw.O i))).range) → ∀ (b : Bool) (j : Fin D.R.m), (∀ f : NX.FmK S ((j : ℕ) + 1), (show ↥(S.A ((j : ℕ) + 1)).WK from f).1 ∈ (S.A ((j : ℕ) + 1)).MK → f ∈ locBall YS fw iC b j) → (∀ f : NX.FmK S ((j : ℕ) + 1), ∃ c : S.Ks, c ≠ 0 ∧ c • f ∈ locBall YS fw iC b j) := by
  intro D Γ _ _ Pl0 I0 T1 A3 T0 _ Rl cG S YS κ v₀ fw i iC _ b j hball f
  have hfull := GlobalTheory.GoodLat.Obj.mkFull_of_tie fw j
  have hwk : (YS.fi j).e (show ↥(S.A ((j : ℕ) + 1)).WK from f).1 ∈ (Rl.FW j).WK :=
    ((YS.fi j).wk _).1 (show ↥(S.A ((j : ℕ) + 1)).WK from f).2
  obtain ⟨a, ha, hamk⟩ := exists_intMul_mem_MK (Rl.FW j) hfull.2 _ hwk
  refine ⟨(YS.fi j).eK.symm (a : T0.Q.c.F), ?_, hball _ ?_⟩
  · intro h
    apply ha
    have : ((a : T0.Q.c.F)) = 0 := by
      have := congrArg (YS.fi j).eK h
      simpa using this
    exact_mod_cast this
  · rw [(YS.fi j).mkK]
    have h1 : ((show ↥(S.A ((j : ℕ) + 1)).WK from (YS.fi j).eK.symm (a : T0.Q.c.F) • f)).1 =
        (YS.fi j).eK.symm (a : T0.Q.c.F) • (show ↥(S.A ((j : ℕ) + 1)).WK from f).1 := rfl
    rw [h1, ← algebraMap_smul D.what₂.LL, map_smul, ← (YS.fi j).eK_LL, RingEquiv.apply_symm_apply, algebraMap_smul,
      algebraMap_smul]
    exact hamk

end GlobalTheory.GeoTie
