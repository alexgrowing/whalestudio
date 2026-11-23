import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.InvariantsGenerators
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.JSmul
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdmissibleQuotientKerIffFullLattices
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsTopDataOfSlotHyps
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdmissibleClassesPropsOfFlatCoefficient
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdmissibleOfSurjective
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdmissibleStd
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CrystallineSumsTwistsCharactersExpectedJumps
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsIntegralCyclotomicChar
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FinrankDcrisLetterDeRhamComponentEqDim
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DvrComplete
open GlobalTheory.AdmLoc GlobalTheory.TopSteps Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions
set_option synthInstance.maxHeartbeats 400000
open ReciprocityTheory.Def (Z1 B1 H1)
open TensorProduct

namespace GlobalTheory.TransportCoef

open Formalism.MainNotions.N (twistRep coefRep)
open ReciprocityTheory.Def (d0 d1 C1)

variable {O G : Type} [CommRing O] [Group G] {M M' : Type} [AddCommGroup M] [Module O M] [AddCommGroup M']
  [Module O M']

theorem rTensor_coefRep (W : Representation O G M) (W' : Representation O G M') (e : M →ₗ[O] M')
    (he : ∀ g x, e (W g x) = W' g (e x)) (X : Type) [AddCommGroup X] [Module O X] (g : G) (y : M ⊗[O] X) :
    LinearMap.rTensor X e (coefRep W X g y) = coefRep W' X g (LinearMap.rTensor X e y) := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul m x => rw [coefRep_tmul, LinearMap.rTensor_tmul, LinearMap.rTensor_tmul, coefRep_tmul, he]
  | add a b ha hb => rw [map_add, map_add, ha, hb, map_add, map_add]

theorem twist_intertwine (W : Representation O G M) (W' : Representation O G M') (e : M →ₗ[O] M')
    (he : ∀ g x, e (W g x) = W' g (e x)) (χ : G →* Oˣ) (g : G) (x : M) :
    e (twistRep W χ g x) = twistRep W' χ g (e x) := by
  rw [twistRep_apply, twistRep_apply, map_smul, he]

variable [TopologicalSpace G]

section General

variable {P P' : Type} [AddCommGroup P] [Module O P] [AddCommGroup P'] [Module O P']
  (π : Representation O G P) (π' : Representation O G P') (F : P →ₗ[O] P')
  (hF : ∀ g y, F (π g y) = π' g (F y))
include hF

theorem mem_Z1_comp {z : G → P} (hz : z ∈ Z1 π ⊤) : (fun g => F (z g)) ∈ Z1 π' ⊤ := by
  rw [Z1, Submodule.mem_inf] at hz ⊢
  obtain ⟨h1, h2⟩ := hz
  refine ⟨⟨h1.1.comp F, fun _ => Submodule.mem_top⟩, ?_⟩
  rw [LinearMap.mem_ker] at h2 ⊢
  funext x
  have := congrFun h2 x
  simp only [d1, LinearMap.coe_mk, AddHom.coe_mk, Pi.zero_apply] at this ⊢
  rw [← hF, ← map_sub, ← map_add, this, map_zero]

theorem cob_comp {z : G → P} (S : Set G) (b : P) (hb : ∀ g ∈ S, z g = π g b - b) :
    ∀ g ∈ S, F (z g) = π' g (F b) - F b := by
  intro g hg
  rw [hb g hg, map_sub, hF]

theorem mem_B1_comp {z : G → P} (hz : z ∈ B1 π ⊤) : (fun g => F (z g)) ∈ B1 π' ⊤ := by
  rw [ReciprocityTheory.Def.B1, Submodule.mem_map] at hz ⊢
  obtain ⟨b, -, rfl⟩ := hz
  refine ⟨F b, Submodule.mem_top, ?_⟩
  funext g
  simp only [d0, LinearMap.coe_mk, AddHom.coe_mk]
  rw [map_sub, hF]

end General

end GlobalTheory.TransportCoef

namespace GlobalTheory.TransportCoef
open Formalism.MainNotions.N (twistRep coefRep)

theorem transport {O G : Type} [CommRing O] [Group G] [TopologicalSpace G] {M M' : Type} [AddCommGroup M]
    [Module O M] [AddCommGroup M'] [Module O M'] (W : Representation O G M) (W' : Representation O G M')
    (e : M ≃ₗ[O] M') (he : ∀ g x, e (W g x) = W' g (e x)) :
    ∀ (χ : G →* Oˣ) (X : Type) [AddCommGroup X] [Module O X] (z : G → M ⊗[O] X) (z' : G → M' ⊗[O] X),
      (∀ g, z' g = LinearEquiv.rTensor X e (z g)) →
      (z ∈ Z1 (twCoef W χ X) ⊤ ↔ z' ∈ Z1 (twCoef W' χ X) ⊤) ∧
      (∀ (hz : z ∈ Z1 (twCoef W χ X) ⊤) (hz' : z' ∈ Z1 (twCoef W' χ X) ⊤) {c : O} (hc : ∀ x : X, c • x = 0),
        ∃ f : ((M ⊗[O] X) × (O ⧸ Ideal.span {c})) ≃ₗ[O] ((M' ⊗[O] X) × (O ⧸ Ideal.span {c})),
          ∀ g x, f (Ea W χ hc ⟨z, hz⟩ g x) = Ea W' χ hc ⟨z', hz'⟩ g (f x)) ∧
      (z ∈ B1 (twCoef W χ X) ⊤ ↔ z' ∈ B1 (twCoef W' χ X) ⊤) ∧
      ∀ I : Subgroup G, (∃ b, ∀ g ∈ I, z g = twCoef W χ X g b - b) ↔
        (∃ b', ∀ g ∈ I, z' g = twCoef W' χ X g b' - b') := by
  intro χ X _ _ z z' hzz
  have he' : ∀ g x, e.symm (W' g x) = W g (e.symm x) := fun g x => by
    apply e.injective
    rw [he, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]
  let E := LinearEquiv.rTensor X e
  have hE : ∀ y, E y = LinearMap.rTensor X (e : M →ₗ[O] M') y := fun _ => rfl
  have hEs : ∀ y, E.symm y = LinearMap.rTensor X (e.symm : M' →ₗ[O] M) y := by
    intro y
    apply E.injective
    rw [LinearEquiv.apply_symm_apply, hE, ← LinearMap.comp_apply, ← LinearMap.rTensor_comp]
    simp
  have key : ∀ g y, (E : M ⊗[O] X →ₗ[O] M' ⊗[O] X) (twCoef W χ X g y) = twCoef W' χ X g (E y) := fun g y =>
    rTensor_coefRep (twistRep W χ⁻¹) (twistRep W' χ⁻¹) (e : M →ₗ[O] M')
      (twist_intertwine W W' (e : M →ₗ[O] M') he χ⁻¹) X g y
  have keys : ∀ g y, (E.symm : M' ⊗[O] X →ₗ[O] M ⊗[O] X) (twCoef W' χ X g y) = twCoef W χ X g (E.symm y) :=
    fun g y => by
      show E.symm _ = _
      rw [hEs, hEs]
      exact rTensor_coefRep (twistRep W' χ⁻¹) (twistRep W χ⁻¹) (e.symm : M' →ₗ[O] M)
        (twist_intertwine W' W (e.symm : M' →ₗ[O] M) he' χ⁻¹) X g y
  have keyc : ∀ g y, E (coefRep W X g y) = coefRep W' X g (E y) := fun g y =>
    rTensor_coefRep W W' (e : M →ₗ[O] M') he X g y
  have hz'f : z' = fun g => (E : M ⊗[O] X →ₗ[O] M' ⊗[O] X) (z g) := funext hzz
  have hzf : z = fun g => (E.symm : M' ⊗[O] X →ₗ[O] M ⊗[O] X) (z' g) := by
    funext g; show z g = E.symm (z' g); rw [hzz, LinearEquiv.symm_apply_apply]
  refine ⟨⟨fun hz => ?_, fun hz' => ?_⟩, ?_, ⟨fun hz => ?_, fun hz' => ?_⟩, fun I => ⟨?_, ?_⟩⟩
  · rw [hz'f]; exact mem_Z1_comp _ _ _ key hz
  · rw [hzf]; exact mem_Z1_comp _ _ _ keys hz'
  · intro hz hz' c hc
    refine ⟨E.prodCongr (LinearEquiv.refl O _), fun g x => ?_⟩
    obtain ⟨m, q⟩ := x
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective q
    rw [LinearEquiv.prodCongr_apply, Ea_apply, LinearEquiv.prodCongr_apply, LinearEquiv.refl_apply,
      LinearEquiv.refl_apply, Ea_apply]
    simp only [Prod.mk.injEq, and_true]
    rw [map_add, map_smul, keyc, hzz]
  · rw [hz'f]; exact mem_B1_comp _ _ _ key hz
  · rw [hzf]; exact mem_B1_comp _ _ _ keys hz'
  · rintro ⟨b, hb⟩
    refine ⟨E b, fun g hg => ?_⟩
    rw [hzz]
    exact cob_comp _ _ _ key (I : Set G) b hb g hg
  · rintro ⟨b, hb⟩
    refine ⟨E.symm b, fun g hg => ?_⟩
    rw [hzf]
    exact cob_comp _ _ _ keys (I : Set G) b hb g hg

end GlobalTheory.TransportCoef
