import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.FWExist
open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.EvalInj

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}

theorem evAt_injective_of_ne {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks)
    (hm : R.models_HW) (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ) (v : (R.MW i σ).Vec)
    (hv : ∀ τ, (v τ : (R.MW i σ).H τ) ≠ 0) : Function.Injective (evAt R i σ v) := by
  intro x y hxy
  have h0 : (R.HW i σ).e (x - y) v = 0 := by
    rw [map_sub]
    show (R.HW i σ).e x v - (R.HW i σ).e y v = 0
    exact sub_eq_zero.2 hxy
  have hip : ipM (R.MW i σ) (R.νW i) (R.fdW i) ((R.HW i σ).e (x - y)) ((R.HW i σ).e (x - y)) = 0 := by
    by_cases h : ∃ c, IsMultIP (R.MW i σ) (R.νW i) (R.fdW i) ((R.HW i σ).e (x - y)) ((R.HW i σ).e (x - y)) c
    · have h1 := (ipM_spec _ _ _ _ _ h v v).2
      rw [h0] at h1
      simp only [Pi.zero_apply, mul_zero, integral_zero] at h1
      rcases mul_eq_zero.1 h1.symm with h2 | h2
      · exact h2
      · obtain ⟨τ, -, hτ⟩ := Finset.prod_eq_zero_iff.1 h2
        exact absurd (inner_self_eq_zero.1 hτ) (hv τ)
    · unfold ipM
      rw [dif_neg h]
  have h3 := (hm i σ).2.2 (x - y) (x - y)
  unfold ipAt at h3
  rw [hip, mul_zero] at h3
  exact sub_eq_zero.1 (inner_self_eq_zero.1 h3)

variable (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F)

noncomputable def junkModel {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) :
    RealDat D A Ks :=
  { R with
    HW := fun _ _ => ⟨ℂ, 0⟩
    gW := fun _ _ => 1
    thG := fun _ _ => 0
    FW := fun i =>
      { WK := (R.FW i).WK, Pt := (R.FW i).Pt, nrm := (R.FW i).nrm, nrm_nonneg := (R.FW i).nrm_nonneg,
        nrm_zero := (R.FW i).nrm_zero, nrm_add := (R.FW i).nrm_add, nrm_smul := (R.FW i).nrm_smul,
        towKs := (R.FW i).towKs, ρ := (R.FW i).ρ, chi := (R.FW i).chi, j := fun _ => 0 } }

end GlobalTheory.EvalInj
