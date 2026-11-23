import Development.AutomorphicArithmetic.Foundations.Convolution.CentreSplitting.DefsTw
import Development.AutomorphicArithmetic.Foundations.Convolution.CentreSplitting.ExSummand
import Development.AutomorphicArithmetic.Foundations.Convolution.CentreSplitting.TwCls
import Development.AutomorphicArithmetic.Foundations.Convolution.CentreSplitting.TwUnitary
import Development.AutomorphicArithmetic.Foundations.Convolution.CentreSplitting.GalCentral

open MeasureTheory NumberField IsDedekindDomain
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum
open GlobalTheory.CuspRep (CuspSub GA Af Ad finGL locGL)
open UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.Dp UpperTheory.V

private theorem map_closure {H : Type} [NormedAddCommGroup H] [NormedSpace ℂ H] [CompleteSpace H] (U : H →L[ℂ] H)
    (hU : ∀ v, ‖U v‖ = ‖v‖) (A V : Submodule ℂ H) :
    V = A.topologicalClosure ↔ V.map U.toLinearMap = (A.map U.toLinearMap).topologicalClosure := by
  have hi : Isometry U := AddMonoidHomClass.isometry_of_norm U hU
  have e : (A.map U.toLinearMap).topologicalClosure = A.topologicalClosure.map U.toLinearMap := SetLike.coe_injective (by
    rw [Submodule.topologicalClosure_coe, Submodule.map_coe, Submodule.map_coe, Submodule.topologicalClosure_coe]
    exact hi.isClosedEmbedding.closure_image_eq _)
  rw [e]
  exact (Submodule.map_injective_of_injective (f := U.toLinearMap) hi.injective).eq_iff.symm

theorem UpperTheory.ConvolutionTheory.Dp.conjCarries :
    UpperTheory.ConvolutionTheory.Dp.ConjCarries := by
  intro E _ _ _ n μ _ θ σ s hs hθ π π' V' hsp
  set m : GA E n →* GA E n := Matrix.GeneralLinearGroup.map s.toRingHom with hm
  have hsurj : Function.Surjective m := fun g => ⟨Matrix.GeneralLinearGroup.map s.symm.toRingHom g, by
    ext i j : 2
    exact s.apply_symm_apply _⟩
  have hcen : ∀ t, m (centralSection E n t) = centralSection E n t := (galCentral E n σ s hs).2
  have hmem : ∀ (ρ : CuspSub E n) (f : GA E n → ℂ), f ∈ (UpperTheory.CBC.Cusp.cx ρ).space ↔ ∃ φ ∈ Cm.carrier ρ, f = φ.1 := fun ρ f => by
    constructor
    · rintro ⟨φ, hφ, rfl⟩
      rw [← Cm.map_carrier] at hφ
      obtain ⟨ψ, hψ, rfl⟩ := hφ
      exact ⟨ψ, hψ, rfl⟩
    · rintro ⟨φ, hφ, rfl⟩
      exact ⟨_, hφ, rfl⟩
  have h1 : ∀ ψ ∈ Cm.carrier π', ∃ φ ∈ Cm.carrier π, ∀ g, ψ.1 g = φ.1 (m g) := fun ψ hψ => by
    have h := (hmem π' _).2 ⟨ψ, hψ, rfl⟩
    rw [hsp] at h
    obtain ⟨f, hf, e⟩ := h
    obtain ⟨φ, hφ, rfl⟩ := (hmem π f).1 hf
    exact ⟨φ, hφ, fun g => (congrFun e g).symm⟩
  have h2 : ∀ φ ∈ Cm.carrier π, ∃ ψ ∈ Cm.carrier π', ∀ g, ψ.1 g = φ.1 (m g) := fun φ hφ => by
    have h : (fun g => φ.1 (m g)) ∈ (UpperTheory.CBC.Cusp.cx π').space := by
      rw [hsp]
      exact ⟨φ.1, (hmem π _).2 ⟨φ, hφ, rfl⟩, rfl⟩
    obtain ⟨ψ, hψ, e⟩ := (hmem π' _).1 h
    exact ⟨ψ, hψ, fun g => (congrFun e g).symm⟩
  have hc : Cm.carrier π' ≤ centralCuspForms E n ↔ Cm.carrier π ≤ centralCuspForms E n := by
    constructor
    · intro h φ hφ t x
      obtain ⟨ψ, hψ, e⟩ := h2 φ hφ
      obtain ⟨y, rfl⟩ := hsurj x
      have h3 := h hψ t y
      rwa [e, e, map_mul, hcen] at h3
    · intro h ψ hψ t x
      obtain ⟨φ, hφ, e⟩ := h1 ψ hψ
      have h3 := h hφ t (m x)
      show ψ.1 (centralSection E n t * x) = ψ.1 x
      rw [e, e, map_mul, hcen]
      exact h3
  rw [exSummand E n μ π' V', exSummand E n μ π, hc]
  refine and_congr_right fun h => ?_
  have hU : ∀ φ ∈ Cm.carrier π, ∀ ψ ∈ Cm.carrier π', (∀ g, ψ.1 g = φ.1 (m g)) → θ.U (clsL μ ψ) = clsL μ φ := fun φ hφ ψ hψ e =>
    (twCls E n μ θ φ (h hφ) ψ (hc.2 h hψ)).2 fun x => (e x).trans (congrArg φ.1 (hθ x).symm)
  have e : (Cm.carrier π).map (clsL μ) = ((Cm.carrier π').map (clsL μ)).map θ.U.toLinearMap := by
    refine le_antisymm (Submodule.map_le_iff_le_comap.2 fun φ hφ => ?_)
      (Submodule.map_le_iff_le_comap.2 (Submodule.map_le_iff_le_comap.2 fun ψ hψ => ?_))
    · obtain ⟨ψ, hψ, e⟩ := h2 φ hφ
      exact Submodule.mem_map.2 ⟨_, Submodule.mem_map_of_mem hψ, hU φ hφ ψ hψ e⟩
    · obtain ⟨φ, hφ, e⟩ := h1 ψ hψ
      exact Submodule.mem_map.2 ⟨φ, hφ, (hU φ hφ ψ hψ e).symm⟩
  rw [e]
  exact map_closure θ.U (twUnitary E n μ θ).1 _ _
