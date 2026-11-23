import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.FWExist
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FiniteGroupActsUnitarilyHilbertMultiplicityModelStatement

open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory

theorem gW_norm_eq : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks), R.models_HW → R.models_gW → R.models_νW → ∀ i σ g x, ‖R.gW i σ g x‖ = ‖x‖ := by
  intro D G _ _ Pl0 T0 A Ks _ _ _ R hH hg hν i σ g x
  unfold RealDat.models_HW at hH
  unfold RealDat.models_gW at hg
  unfold RealDat.models_νW at hν
  obtain ⟨hinj, hrange, hip⟩ := hH i σ
  unfold ipAt at hip
  have hfd := hν i
  unfold IsMeasFD at hfd
  have hHaar : (R.νW i).IsHaarMeasure := by
    have h := hfd.1
    unfold IsMeasLev IsMeasLevW at h
    exact h.1
  let u : (R.HW i σ).H ≃ₗ[ℂ] (R.HW i σ).H :=
    LinearEquiv.ofLinear (R.gW i σ g) (R.gW i σ g⁻¹) (by ext y; simp) (by ext y; simp)
  have hmem : ∀ y, (R.HW i σ).e y ∈ R.Wall i σ := fun y => by
    rw [← hrange]
    exact LinearMap.mem_range_self _ y
  exact _root_.GlobalTheory.T.norm_eq_of_actG0_intertwining_isometric_embedding R.θ (R.MW i σ) (R.βW i) (R.datWp i R.triv) _ _ (R.HW i σ).H (R.HW i σ).e _
    (R.νW i) (R.fdW i) hip hinj hmem hHaar hfd.2 (R.eG g) u
    (fun y v => congrArg (fun T => T v) (hg i σ g y)) x

end GlobalTheory
