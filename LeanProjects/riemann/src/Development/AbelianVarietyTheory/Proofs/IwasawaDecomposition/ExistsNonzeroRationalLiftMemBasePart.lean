import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StableIffCarrierEq
import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinRepApply
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3

namespace GlobalTheory.RatLift

theorem exists_rat_lift_mem_part : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) (cG : G0 R.Pg D.R.r ≃* G0g D.nd), Inputs D → Pins R F cG → Holds R F → GlobalTheory.CuspMult.MultEq R.toRealDat → (∀ χ ∈ A3.A.X, chiIdem χ * lvlIdem F.P0 F.ψ0 ≠ 0) → ∀ p, R.EEp3 p ≠ ⊥ → ∀ i, (R.toCx3 F).Wp i p ⊓ LinearMap.range ((R.toCx3 F).w0C false i) ≠ ⊥ → ∃ x : Fin ((lv (F.fc (R.toCx3 F).zs) false).dZ i A3.A.μ0) → D.what₂.LL, (R.toCx3 F).tC F.cr false i A3.A.μ0 (cpt A3.A.v0.embedding x) ∈ (R.toCx3 F).Wp i p ∧ x ≠ 0 := by
  intro D G _ _ Pl0 I0 T A3 Ks _ _ _ R F cG _ hP hH _ _ p _ i hB
  have hRw := complex_data_conditions_base_level_of_primitive_links hH.ok hH.sep hP.char hH.prim
  have hk : (R.toCx3 F).KForm false := hRw.kForm
  have he : (R.toCx3 F).EWnorm false := hRw.ewNorm
  have hn : 0 < (R.toCx3 F).nP false := hRw.h4pos.2.2 false
  have h5 : (R.toCx3 F).H5 F.cr false := hRw.lifts0.1
  have hr : (R.toCx3 F).RATth F.cr false := hRw.ratTh
  have h3W : (R.toCx3 F).H3W F.cr false := hRw.liftHyp0.h3W
  have ht : (lv (F.fc (R.toCx3 F).zs) false).Types := hRw.types0
  have hK : ∀ y, y ∈ ⨆ q, (R.toCx3 F).WpK false i q := fun y => CxData.liftsK ht hk he hn h5 hr h3W i y
  have hc0 : cpt A3.A.v0.embedding (0 : Fin ((R.toCx3 F).dW false i) → D.what₂.LL) = 0 := by
    funext l; simp [cpt]
  have hWpK : (R.toCx3 F).WpK false i p ≠ ⊥ := by
    intro h0
    apply hB
    rw [eq_bot_iff]
    intro w hw
    let M : Submodule ℂ ((R.toCx3 F).W i) :=
      ⨆ q, ⨆ (_ : q ≠ p), (R.toCx3 F).Wp i q ⊓ LinearMap.range ((R.toCx3 F).w0C false i)
    have hrat : ∀ y, (R.toCx3 F).w0C false i (cpt A3.A.v0.embedding y) ∈ M := by
      intro y
      refine Submodule.iSup_induction _ (motive := fun y => (R.toCx3 F).w0C false i (cpt A3.A.v0.embedding y) ∈ M)
        (hK y) ?_ ?_ ?_
      · intro q z hz
        by_cases hq : q = p
        · subst hq
          rw [h0] at hz
          rw [(Submodule.mem_bot _).1 hz, hc0, map_zero]
          exact M.zero_mem
        · exact (le_iSup₂ (f := fun q (_ : q ≠ p) => (R.toCx3 F).Wp i q ⊓ LinearMap.range ((R.toCx3 F).w0C false i)) q hq)
            ⟨hz, ⟨_, rfl⟩⟩
      · rw [hc0, map_zero]
        exact M.zero_mem
      · intro a c ha hc
        have : cpt A3.A.v0.embedding (a + c) = cpt A3.A.v0.embedding a + cpt A3.A.v0.embedding c := by
          funext l; simp [cpt]
        rw [this, map_add]
        exact M.add_mem ha hc
    have hrange : LinearMap.range ((R.toCx3 F).w0C false i) ≤ M := by
      rw [LinearMap.range_eq_map, ← (Pi.basisFun ℂ (Fin ((R.toCx3 F).dW false i))).span_eq, Submodule.map_span,
        Submodule.span_le]
      rintro _ ⟨_, ⟨k, rfl⟩, rfl⟩
      have : (Pi.basisFun ℂ (Fin ((R.toCx3 F).dW false i)) k) =
          cpt A3.A.v0.embedding (Pi.single k (1 : D.what₂.LL)) := by
        funext l
        simp only [Pi.basisFun_apply, cpt, Pi.single_apply]
        split_ifs <;> simp
      rw [this]
      exact hrat _
    have hperp : M ≤ (ℂ ∙ w)ᗮ := by
      refine iSup₂_le fun q hq => ?_
      intro v hv
      rw [Submodule.mem_orthogonal_singleton_iff_inner_right]
      exact (hH.prim.sumW i).1 p q (Ne.symm hq) w hw v hv
    have hww := hperp (hrange hw.2)
    rw [Submodule.mem_orthogonal_singleton_iff_inner_right] at hww
    exact (Submodule.mem_bot ℂ).2 (inner_self_eq_zero.1 hww)
  obtain ⟨y, hy, hy0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hWpK
  obtain ⟨x, rfl⟩ := ((R.toCx3 F).liftMat_bij F.cr false hk he hn h5 hr i A3.A.μ0).2 y
  refine ⟨x, ?_, ?_⟩
  · have hy' : (R.toCx3 F).w0C false i (cpt A3.fam3.base3.v0.embedding
        ((R.toCx3 F).liftMat F.cr false i A3.A.μ0 *ᵥ x)) ∈ (R.toCx3 F).Wp i p := hy
    rw [(R.toCx3 F).key_lift F.cr false h5 hr i A3.A.μ0 x] at hy'
    exact hy'
  · rintro rfl
    exact hy0 (Matrix.mulVec_zero _)

end GlobalTheory.RatLift
