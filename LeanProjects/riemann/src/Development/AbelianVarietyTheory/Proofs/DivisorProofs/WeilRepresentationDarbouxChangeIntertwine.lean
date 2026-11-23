import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.DblActId
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RealisedOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchroedingerPreservesAdelicSchwartz
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProductFunctionOnSumCoordsMemAdelicSchwartzSpace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjMemAdelicSchwartzSpaceNumberFieldOfMem
open scoped TensorProduct NNReal ENNReal Matrix Classical
open NumberField MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.TowU

noncomputable section

namespace GlobalTheory.TowU

section Dbl

variable {R : Type} [CommRing R] [Invertible (2 : R)] {E : Type} [CommRing E] [Algebra R E] {c : E →ₐ[R] E}
  {α β : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] {ξ : E} {JA : Matrix α α E} {JB : Matrix β β E}
  {κ κ' : Type} [Fintype κ] [Fintype κ']

end Dbl

section Adelic

variable {F : Type} [Field F] [NumberField F]

theorem adm_of_eqOn_schA {κ : Type} [Fintype κ] {l l' : ((κ → AF F) → ℂ) →ₗ[ℂ] ℂ}
    (h : ∀ φ ∈ schA F κ, l φ = l' φ) (hl : l ∈ (adeleClass F).adm κ) : l' ∈ (adeleClass F).adm κ := by
  intro g hg
  obtain ⟨T, hT⟩ := hl g hg
  exact ⟨T, fun f => (h _ (Submodule.subset_span ⟨f, g, hg, rfl⟩)).symm.trans (hT f)⟩

variable {ψ : AddChar (AF F) ℂ} {W : Type} [AddCommGroup W] [Module (AF F) W] {B : W → W → AF F}
  {κ κ' : Type} [Fintype κ] [Fintype κ'] {d : Darboux B κ} {d' : Darboux B κ'}
  {s : (κ → AF F) × (κ → AF F) → (κ' → AF F) × (κ' → AF F)}
  {S : ((κ → AF F) → ℂ) →ₗ[ℂ] ((κ' → AF F) → ℂ)} {S' : ((κ' → AF F) → ℂ) →ₗ[ℂ] ((κ → AF F) → ℂ)}

theorem IsOp.rho_eq (hs : ∀ w, s (d.e w) = d'.e w) (hS : IsOp ψ s S S') (w : W) {φ : (κ → AF F) → ℂ}
    (hφ : φ ∈ schA F κ) : S (d.rho ψ w φ) = d'.rho ψ w (S φ) := by
  simp only [Darboux.rho]
  rw [hS.Heisenberg₂ _ _ hφ, hs]

theorem isUSplitting_of_isOp (hψ : IsStd ψ) (hs : ∀ w, s (d.e w) = d'.e w) (hS : IsOp ψ s S S')
    {G : Type} [Group G] [TopologicalSpace G] {act : G → W → W}
    {om : G →* Module.End ℂ ((κ → AF F) → ℂ)} {om' : G →* Module.End ℂ ((κ' → AF F) → ℂ)}
    (hom : ∀ g, ∀ φ ∈ schA F κ', om' g φ = S (om g (S' φ)))
    (h : IsUSplitting (adeleClass F) ψ d act om) : IsUSplitting (adeleClass F) ψ d' act om' := by
  have hmem : ∀ (κ₀ : Type) [Fintype κ₀] (p : (κ₀ → AF F) × (κ₀ → AF F)) (φ : (κ₀ → AF F) → ℂ),
      φ ∈ schA F κ₀ → schr ψ p φ ∈ schA F κ₀ := fun κ₀ _ p φ hφ =>
    GlobalTheory.SchrKeepsSchA.schr_mem_schA F ψ hψ κ₀ p φ hφ
  have hrho' : ∀ w, ∀ φ ∈ schA F κ', S' (d'.rho ψ w φ) = d.rho ψ w (S' φ) := fun w φ hφ => by
    have h1 := IsOp.rho_eq hs hS w (hS.pres' φ hφ)
    rw [hS.right φ hφ] at h1
    have hm : d.rho ψ w (S' φ) ∈ schA F κ := hmem _ _ _ (hS.pres' φ hφ)
    rw [← h1, hS.left _ hm]
  refine ⟨⟨fun g φ hφ => ?_, fun g w φ hφ => ?_, fun g l hl => ?_⟩, fun μ' hμ' g φ hφ => ?_, fun l hl φ hφ => ?_⟩
  · rw [hom g φ hφ]
    exact hS.pres _ (h.pres g _ (hS.pres' φ hφ))
  · have hw : d'.rho ψ w φ ∈ schA F κ' := hmem _ _ _ hφ
    rw [hom g _ hw, hrho' w φ hφ, h.impl g w _ (hS.pres' φ hφ),
      IsOp.rho_eq hs hS _ (h.pres g _ (hS.pres' φ hφ)), hom g φ hφ]
  · have h2 := hS.adm' _ (h.adm g _ (hS.adm l hl))
    refine adm_of_eqOn_schA (fun φ hφ => ?_) h2
    simp only [LinearMap.coe_comp, Function.comp_apply]
    rw [hom g φ hφ]
  · letI : MeasurableSpace (κ → AF F) := borel _
    haveI : BorelSpace (κ → AF F) := ⟨rfl⟩
    obtain ⟨c, -, -, hc⟩ := hS.norm Measure.addHaar μ' inferInstance hμ'
    rw [hom g φ hφ, hc _ (h.pres g _ (hS.pres' φ hφ)), h.unit Measure.addHaar inferInstance g _ (hS.pres' φ hφ),
      ← hc _ (hS.pres' φ hφ), hS.right φ hφ]
  · refine (h.cont (l ∘ₗ S) (hS.adm l hl) (S' φ) (hS.pres' φ hφ)).congr fun g => ?_
    simp only [LinearMap.coe_comp, Function.comp_apply]
    rw [hom g φ hφ]

theorem siegelRule_of_isOp {E' : Type} [CommRing E'] [Algebra (AF F) E'] {c : E' →ₐ[AF F] E'} {α β : Type} [Fintype α]
    [DecidableEq α] [Fintype β] [DecidableEq β] {ξ : E'} {JA : Matrix α α E'} {JB : Matrix β β E'}
    {d : Darboux (symp c ξ JA JB) κ} {d' : Darboux (symp c ξ JA JB) κ'} (hs : ∀ w, s (d.e w) = d'.e w)
    (hS : IsOp ψ s S S') {χ : E'ˣ →* Circle} {ν : Type} [Fintype ν] [DecidableEq ν] {Cy : Matrix β ν E'}
    {om : UG c JB →* Module.End ℂ ((κ → AF F) → ℂ)} {om' : UG c JB →* Module.End ℂ ((κ' → AF F) → ℂ)}
    (hom : ∀ g, ∀ φ ∈ schA F κ', om' g φ = S (om g (S' φ)))
    (h : SiegelRule c (adeleClass F) ψ ξ JA JB d χ Cy om) : SiegelRule c (adeleClass F) ψ ξ JA JB d' χ Cy om' := by
  intro l hl hinv p t hpt φ hφ
  have key := h (l ∘ₗ S) (hS.adm l hl) (fun z φ' hφ' => by
    simp only [LinearMap.coe_comp, Function.comp_apply]
    rw [IsOp.rho_eq hs hS _ hφ']
    exact hinv z _ (hS.pres _ hφ')) p t hpt (S' φ) (hS.pres' φ hφ)
  simp only [LinearMap.coe_comp, Function.comp_apply, hS.right φ hφ] at key
  rw [hom p φ hφ]
  exact key

end Adelic

end GlobalTheory.TowU

end
