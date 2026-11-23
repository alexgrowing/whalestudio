import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.FWExist
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FiniteGroupActsUnitarilyHilbertMultiplicityModelStatement

open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory

theorem norm_gE_rows : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks), R.models_HE → R.models_gE → R.models_ν0 → ∀ g x, ‖R.gE g x‖ = ‖x‖ := by
  intro D G _ _ Pl0 T0 A Ks _ _ _ R hE hg h0 g x
  unfold RealDat.models_HE RealDat.models_gE RealDat.models_ν0 at *
  obtain ⟨hinj, hrange, hip⟩ := hE
  obtain ⟨hm, hfd⟩ := h0
  obtain ⟨hHaar, -⟩ := hm

  let u : R.HE.H ≃ₗ[ℂ] R.HE.H :=
    LinearEquiv.ofLinear (R.gE g) (R.gE g⁻¹)
      (by
        ext y
        show R.gE g (R.gE g⁻¹ y) = y
        rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply])
      (by
        ext y
        show R.gE g⁻¹ (R.gE g y) = y
        rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply])

  have hmem : ∀ y, R.HE.e y ∈ Mult R.θ (R.MY 0) (levS _ (R.βY 0) (R.dat0 R.triv))
      (levChi _ (R.βY 0) (R.dat0 R.triv)) := by
    intro y
    have hy : R.HE.e y ∈ LinearMap.range R.HE.e := ⟨y, rfl⟩
    rw [hrange] at hy
    exact (Submodule.mem_inf.mp hy).1

  have hact : ∀ y v, R.HE.e (u y) v = actG0 (Yc D 0) (R.βY 0) (R.dat0 R.triv) (R.eG g) (R.HE.e y v) := by
    intro y v
    show R.HE.e (R.gE g y) v = _
    rw [hg]
    rfl
  exact GlobalTheory.T.norm_eq_of_actG0_intertwining_isometric_embedding R.θ (R.MY 0) (R.βY 0) (R.dat0 R.triv) (levS _ (R.βY 0) (R.dat0 R.triv))
    (levChi _ (R.βY 0) (R.dat0 R.triv)) R.HE.H R.HE.e 1 R.ν0 R.fd0
    (fun y z => by rw [one_mul]; exact hip y z) hinj hmem hHaar hfd (R.eG g) u hact x

end GlobalTheory
