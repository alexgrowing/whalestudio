import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GEquivIntL
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial Formalism.UG GlobalTheory.SatInd

noncomputable section

namespace GlobalTheory.SatInd

section HeckeTransport

theorem hecke_comp_of_inverse {G G' : Type} [Group G] [Group G'] (φ : G →* G') (ψ : G' →* G)
    (hψφ : ∀ y, ψ (φ y) = y) {K : Subgroup G} {K' : Subgroup G'} (hφK : ∀ a ∈ K, φ a ∈ K')
    (hψK : ∀ a ∈ K', ψ a ∈ K) (h' : G' → ℂ) (hh : h' ∈ Formalism.UG.Hecke ℂ K') :
    (fun y => h' (φ y)) ∈ Formalism.UG.Hecke ℂ K := by
  classical
  have hh' : Formalism.UG.IsBiInv K' h' ∧ Formalism.UG.FinDosetSupp K' h' := hh
  obtain ⟨hbi, S', hS'⟩ := hh'
  show Formalism.UG.IsBiInv K (fun y => h' (φ y)) ∧ Formalism.UG.FinDosetSupp K (fun y => h' (φ y))
  refine ⟨fun a b y => ?_, S'.image ψ, fun y hy => ?_⟩
  · show h' (φ ((a : G) * y * b)) = h' (φ y)
    rw [map_mul, map_mul]
    exact hbi ⟨φ a, hφK a a.2⟩ ⟨φ b, hφK b b.2⟩ (φ y)
  · obtain ⟨s, hs, a, b, e⟩ := hS' (φ y) hy
    refine ⟨ψ s, Finset.mem_image_of_mem _ hs, ⟨ψ a, hψK a a.2⟩, ⟨ψ b, hψK b b.2⟩, ?_⟩
    show y = ψ a * ψ s * ψ b
    rw [← map_mul, ← map_mul, ← e, hψφ]

end HeckeTransport

section KUTransport

variable {K : Type} [Field K] [Valued K (WithZero (Multiplicative ℤ))]

theorem guMap_mem_KU (g : K ≃+* K) {σ σ' : K →+* K} (hg : ∀ x, g (σ x) = σ' (g x))
    (hint : ∀ x, x ∈ intL K → g x ∈ intL K) (n : ℕ) (a : GU σ n) (ha : a ∈ KU σ n) :
    guMap g hg n a ∈ KU σ' n := by
  simp only [KU, Subgroup.mem_subgroupOf, intPts, Subgroup.mem_inf, MonoidHom.mem_range] at ha ⊢
  obtain ⟨-, b, hb⟩ := ha
  refine ⟨(guMap g hg n a).2, ?_⟩
  let gi : intL K →+* intL K :=
    ((g : K →+* K).comp (intL K).subtype).codRestrict (intL K) (fun x => hint x x.2)
  refine ⟨bc (n := Fin n) gi b, ?_⟩
  apply Units.ext
  ext i j
  have hij := congrArg (fun u : GL (Fin n) K => (u : Matrix (Fin n) (Fin n) K) i j) hb
  simp only [bc, Units.coe_map, MonoidHom.coe_coe, RingHom.mapMatrix_apply, Matrix.map_apply] at hij ⊢
  rw [guMap_val, Matrix.map_apply, ← hij]
  rfl

theorem guMap_symm_guMap (g : K ≃+* K) {σ σ' : K →+* K} (hg : ∀ x, g (σ x) = σ' (g x))
    (hg' : ∀ x, g.symm (σ' x) = σ (g.symm x)) (n : ℕ) (y : GU σ n) :
    guMap g.symm hg' n (guMap g hg n y) = y := by
  apply Subtype.ext
  apply Units.ext
  ext i j
  rw [guMap_val, guMap_val]
  simp

theorem guMap_hecke_comap : ∀ {K : Type} [Field K] [Valued K (WithZero (Multiplicative ℤ))] (g : K ≃+* K) {σ σ' : K →+* K} (hg : ∀ x, g (σ x) = σ' (g x)), (∀ x, x ∈ intL K ↔ g x ∈ intL K) → ∀ (n : ℕ) (h' : GU σ' n → ℂ), h' ∈ Hecke ℂ (KU σ' n) → (fun y => h' (guMap g hg n y)) ∈ Hecke ℂ (KU σ n) := by
  intro K _ _ g σ σ' hg hint n h' hh
  have hg' : ∀ x, g.symm (σ' x) = σ (g.symm x) := by
    intro x
    apply g.injective
    rw [RingEquiv.apply_symm_apply, hg, RingEquiv.apply_symm_apply]
  have hint' : ∀ x, x ∈ intL K → g.symm x ∈ intL K := by
    intro x hx
    rw [hint (g.symm x), RingEquiv.apply_symm_apply]
    exact hx
  exact hecke_comp_of_inverse (guMap g hg n) (guMap g.symm hg' n) (guMap_symm_guMap g hg hg' n)
    (fun a ha => guMap_mem_KU g hg (fun x => (hint x).1) n a ha)
    (fun a ha => guMap_mem_KU g.symm hg' hint' n a ha) h' hh

end KUTransport

end GlobalTheory.SatInd
