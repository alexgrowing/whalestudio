import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Brauer
import PositivityTheory.AutomorphicForms.PublishedInputs.RealGaloisRepresentations.IwahoriSphericalTransfer.FinrankAdjoinSqrtNegOne
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.RealTransport.RealTransport
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.LocIsotypic
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Langlands
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitModelToPlaceModel
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ValuationLtOneIffTendsto
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published UpperTheory.V.Af.Bc GlobalTheory.RealGal
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.CompletionIso

open ValuativeRel

section Val

variable {k k' : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  [Field k'] [ValuativeRel k'] [TopologicalSpace k'] [IsNonarchimedeanLocalField k']

theorem valuation_le_one_of_map (f : k ≃+* k') (hf : Continuous f) {x : k}
    (hx : valuation k' (f x) ≤ 1) : valuation k x ≤ 1 := by
  by_contra h
  rw [not_le] at h
  have hx0 : x ≠ 0 := by rintro rfl; simp at h
  have h1 : valuation k x⁻¹ < 1 := by rw [map_inv₀]; exact inv_lt_one_of_one_lt₀ h
  have h2 := GlobalTheory.TypeRec.TwistInert.valuation_lt_one_map f.toRingHom hf h1
  have hfx : f x ≠ 0 := (map_ne_zero f).2 hx0
  have hw : 0 < valuation k' (f x) := by rw [zero_lt_iff]; exact (Valuation.ne_zero_iff _).2 hfx
  simp only [RingEquiv.toRingHom_eq_coe, RingHom.coe_coe, map_inv₀] at h2
  exact absurd ((inv_lt_one₀ hw).1 h2) (not_lt.2 hx)

theorem valuation_lt_one_of_map (f : k ≃+* k') (hf : Continuous f) {x : k}
    (hx : valuation k' (f x) < 1) : valuation k x < 1 := by
  by_contra h
  rw [not_lt] at h
  have hx0 : x ≠ 0 := by rintro rfl; simp at h
  have h1 : x⁻¹ ∈ 𝒪[k] := by
    rw [Valuation.mem_integer_iff, map_inv₀]; exact inv_le_one_of_one_le₀ h
  have h2 := GlobalTheory.LastCompare.map_mem_integer f.toMonoidHom hf h1
  rw [Valuation.mem_integer_iff] at h2
  have hfx : f x ≠ 0 := (map_ne_zero f).2 hx0
  have hw : 0 < valuation k' (f x) := by rw [zero_lt_iff]; exact (Valuation.ne_zero_iff _).2 hfx
  have h3 : valuation k' (f x⁻¹) ≤ 1 := h2
  rw [map_inv₀, map_inv₀] at h3
  exact absurd hx (not_lt.2 ((inv_le_one₀ hw).1 h3))

variable (f : k ≃+* k') (hf : Continuous f) {n : Type} [Fintype n] [DecidableEq n]

theorem map_map_symm (h : GL n k') :
    Matrix.GeneralLinearGroup.map f.toRingHom (Matrix.GeneralLinearGroup.map f.symm.toRingHom h) = h := by
  ext a b
  simp

include hf in

theorem map_symm_mem_KO {h : GL n k'} (hh : h ∈ GlobalTheory.SplitWeil.KO k' n) :
    Matrix.GeneralLinearGroup.map f.symm.toRingHom h ∈ GlobalTheory.SplitWeil.KO k n := by
  obtain ⟨h0, rfl⟩ := hh
  let j : 𝒪[k'] →+* 𝒪[k] := (f.symm.toRingHom.comp (algebraMap 𝒪[k'] k')).codRestrict 𝒪[k] (fun y => by
      show valuation k (f.symm (y : k')) ≤ 1
      apply valuation_le_one_of_map f hf
      rw [RingEquiv.apply_symm_apply]
      exact y.2)
  refine ⟨Matrix.GeneralLinearGroup.map j h0, ?_⟩
  ext a b
  simp [j] <;> rfl

include hf in

theorem map_symm_mem_iwahori [LinearOrder n] {h : GL n k'} (hh : h ∈ GlobalTheory.SmGL.iwahori k' n) :
    Matrix.GeneralLinearGroup.map f.symm.toRingHom h ∈ GlobalTheory.SmGL.iwahori k n := by
  rw [GlobalTheory.SmGL.mem_iwahori] at hh ⊢
  refine ⟨map_symm_mem_KO f hf hh.1, fun a b hab => ?_⟩
  apply valuation_lt_one_of_map f hf
  have := hh.2 a b hab
  simpa using this

end Val

theorem fixed_ne_bot_transfer {G G' V V' : Type} [Group G] [Group G'] [AddCommGroup V] [Module ℂ V]
    [AddCommGroup V'] [Module ℂ V'] (ρ : Representation ℂ G V) (ρ' : Representation ℂ G' V') (φ : G →* G')
    (ψ : G' → G) (hψ : ∀ g, φ (ψ g) = g) (e : V ≃ₗ[ℂ] V') (he : ∀ g x, e (ρ g x) = ρ' (φ g) (e x))
    (H : Subgroup G) (H' : Subgroup G') (hH : ∀ h ∈ H', ψ h ∈ H) :
    GlobalTheory.PRep.fixed ρ H ≠ ⊥ → GlobalTheory.PRep.fixed ρ' H' ≠ ⊥ := by
  intro hne
  obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  have hx' : ∀ h : H, ρ (h : G) x = (((1 : H →* ℂˣ) h : ℂˣ) : ℂ) • x := hx
  refine (Submodule.ne_bot_iff _).2 ⟨e x, ?_, by simpa using hx0⟩
  show ∀ h : H', ρ' (h : G') (e x) = (((1 : H' →* ℂˣ) h : ℂˣ) : ℂ) • e x
  intro h
  have h1 := hx' ⟨ψ h, hH h h.2⟩
  simp only [MonoidHom.one_apply, Units.val_one, one_smul] at h1 ⊢
  rw [← hψ h, ← he, h1]

theorem iwahori_spherical_transfer : ∀ (F K : Type) [Field F] [NumberField F] [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 F)) (w : HeightOneSpectrum (𝓞 K)) (i : v.adicCompletion F ≃+* w.adicCompletion K), Continuous i → ∀ (a : ℕ) (σ : SmIrr (GL (Fin a) (v.adicCompletion F))) (σ' : SmIrr (GL (Fin a) (w.adicCompletion K))) (e : σ.V ≃ₗ[ℂ] σ'.V), (∀ g x, e (σ.ρ g x) = σ'.ρ (Matrix.GeneralLinearGroup.map i.toRingHom g) (e x)) → (GlobalTheory.PRep.fixed σ.ρ (GlobalTheory.SmGL.iwahori (v.adicCompletion F) (Fin a)) ≠ ⊥ → GlobalTheory.PRep.fixed σ'.ρ (GlobalTheory.SmGL.iwahori (w.adicCompletion K) (Fin a)) ≠ ⊥) ∧ (GlobalTheory.SmGL.IsSpherical σ.ρ → GlobalTheory.SmGL.IsSpherical σ'.ρ) := by
  intro F K _ _ _ _ v w i hi a σ σ' e he
  exact ⟨fixed_ne_bot_transfer σ.ρ σ'.ρ (Matrix.GeneralLinearGroup.map i.toRingHom)
      (Matrix.GeneralLinearGroup.map i.symm.toRingHom) (map_map_symm i) e he _ _
      (fun h hh => map_symm_mem_iwahori i hi hh),
    fixed_ne_bot_transfer σ.ρ σ'.ρ (Matrix.GeneralLinearGroup.map i.toRingHom)
      (Matrix.GeneralLinearGroup.map i.symm.toRingHom) (map_map_symm i) e he _ _
      (fun h hh => map_symm_mem_KO i hi hh)⟩

end GlobalTheory.CompletionIso
