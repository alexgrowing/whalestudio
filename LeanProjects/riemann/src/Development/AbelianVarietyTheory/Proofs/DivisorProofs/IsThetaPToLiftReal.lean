import Formalism.LocalToGlobal.IndefiniteReal.ThetaFireRow
open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.IndefR
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped TensorProduct

namespace GlobalTheory.ThetaPRead

theorem isThetaP_restrict {G' H' S' Si Tau Y ι : Type} [MeasurableSpace H'] [AddCommGroup Si] [Module ℂ Si]
    [AddCommGroup Tau] [Module ℂ Tau] [AddCommGroup Y] [Module ℂ Y]
    {M : ι → Type} [∀ ρ, AddCommGroup (M ρ)] [∀ ρ, Module ℂ (M ρ)] (low : ∀ ρ, Submodule ℂ (M ρ))
    {ν : Measure H'} {𝓕 : Set H'} {th : G' → H' → S' → ℂ} {pt : Si → S'}
    {io : (⨂[ℂ] ρ, low ρ) →ₗ[ℂ] Tau →ₗ[ℂ] Si} (L : Y →ₗ[ℂ] (H' → Tau)) (hL : Function.Injective L)
    (S : Submodule ℂ (H' → Tau)) (U : Y →ₗ[ℂ] MultilinearMap ℂ M (G' → ℂ))
    (h : ∃ thP, Lift.IsThetaP ν 𝓕 th pt io (LinearMap.range L) thP ∧
      ∀ x (v : ∀ ρ, low ρ), U x (fun ρ => v ρ) = thP (L.rangeRestrict x) (PiTensorProduct.tprod ℂ v)) :
    Lift.IsThetaP ν 𝓕 th pt io (LinearMap.range L ⊓ S)
      (LinearMap.lcomp ℂ (G' → ℂ) (PiTensorProduct.map fun ρ => (low ρ).subtype) ∘ₗ
        (PiTensorProduct.lift : MultilinearMap ℂ M (G' → ℂ) ≃ₗ[ℂ] _).toLinearMap ∘ₗ U ∘ₗ
        (LinearEquiv.ofInjective L hL).symm.toLinearMap ∘ₗ Submodule.inclusion inf_le_left) := by
  obtain ⟨thP, hP, hv⟩ := h
  have key : ∀ f : ↥(LinearMap.range L ⊓ S),
      (LinearMap.lcomp ℂ (G' → ℂ) (PiTensorProduct.map fun ρ => (low ρ).subtype) ∘ₗ
        (PiTensorProduct.lift : MultilinearMap ℂ M (G' → ℂ) ≃ₗ[ℂ] _).toLinearMap ∘ₗ U ∘ₗ
        (LinearEquiv.ofInjective L hL).symm.toLinearMap ∘ₗ Submodule.inclusion inf_le_left) f =
        thP (Submodule.inclusion inf_le_left f) := by
    intro f
    set x := (LinearEquiv.ofInjective L hL).symm (Submodule.inclusion inf_le_left f) with hx
    have h1 : L.rangeRestrict x = Submodule.inclusion inf_le_left f := by
      have := LinearEquiv.apply_symm_apply (LinearEquiv.ofInjective L hL) (Submodule.inclusion inf_le_left f)
      rw [← hx] at this
      rw [← this]
      rfl
    apply PiTensorProduct.ext
    apply MultilinearMap.ext
    intro v
    simp only [LinearMap.compMultilinearMap_apply, LinearMap.coe_comp, Function.comp_apply,
      LinearMap.lcomp_apply, LinearEquiv.coe_coe, PiTensorProduct.map_tprod, Submodule.coe_subtype,
      PiTensorProduct.lift.tprod]
    rw [← hx, hv x v, h1]
  refine ⟨fun f e g => ?_, fun f e g => ?_⟩
  · exact hP.integ (Submodule.inclusion inf_le_left f) e g
  · rw [key f]
    exact hP.eq _ e g

theorem isThetaP_toLiftReal : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks), ∀ (F : Face D A) (tupT : D.what₂.Tup → T) (hm : 0 < D.R.m) (hTop : RecTie.TopMultH R) (hinj : ∀ i t, Function.Injective (R.extV i t)), R.thP_thF → ∀ μ i, Lift.IsThetaP ((RecTie.toLiftReal R F tupT hm hTop hinj).measV μ i) ((RecTie.toLiftReal R F tupT hm hTop hinj).fdV μ i) ((RecTie.toLiftReal R F tupT hm hTop hinj).thW μ i) ((RecTie.toLiftReal R F tupT hm hTop hinj).ptW μ i) ((RecTie.toLiftReal R F tupT hm hTop hinj).ioK i) ((RecTie.toLiftReal R F tupT hm hTop hinj).Amt μ i) ((RecTie.toLiftReal R F tupT hm hTop hinj).thC μ i) := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F tupT hm hTop hinj h μ i
  exact isThetaP_restrict _ _ _ _ _ (h i (tupT μ))

end GlobalTheory.ThetaPRead
