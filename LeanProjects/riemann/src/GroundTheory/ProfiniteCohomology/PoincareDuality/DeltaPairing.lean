import Mathlib
import GroundTheory.ProfiniteCohomology.CupProducts.ExistsCocycleMapFEqD
import GroundTheory.ProfiniteCohomology.CupProducts.Pairing
set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

open CategoryTheory MonoidalCategory groupCohomology GroundTheory.GroupCoh

universe u

variable {k G : Type u} [CommRing k] [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

variable {S T : ShortComplex (Rep.{u} k G)} [IsDiscreteRep S.X₁] [IsDiscreteRep S.X₂]
  [IsDiscreteRep S.X₃] [IsDiscreteRep T.X₁] [IsDiscreteRep T.X₂] [IsDiscreteRep T.X₃]
  {C : Rep.{u} k G} [IsDiscreteRep C]
  (μ₁ : S.X₁ ⊗ T.X₃ ⟶ C) (μ₂ : S.X₂ ⊗ T.X₂ ⟶ C) (μ₃ : S.X₃ ⊗ T.X₁ ⟶ C)

omit [TopologicalSpace G] [IsTopologicalGroup G] [IsDiscreteRep S.X₁] [IsDiscreteRep S.X₂] [IsDiscreteRep S.X₃] [IsDiscreteRep T.X₁]
  [IsDiscreteRep T.X₂] [IsDiscreteRep T.X₃] [IsDiscreteRep C] in

theorem cupCochain_pairing_left (h₁₂ : (S.f ⊗ₘ 𝟙 T.X₂) ≫ μ₂ = (𝟙 S.X₁ ⊗ₘ T.g) ≫ μ₁)
    {p q n : ℕ} (h : p + q = n) (a : (Fin p → G) → S.X₁) (b : (Fin q → G) → T.X₂)
    (σ : Fin n → G) :
    μ₂.hom (cupCochain h (fun τ => S.f.hom (a τ)) b σ) =
      μ₁.hom (cupCochain h a (fun τ => T.g.hom (b τ)) σ) := by
  have e := congrArg (fun φ : S.X₁ ⊗ T.X₂ ⟶ C => φ.hom (cupCochain h a b σ)) h₁₂
  simp only [Rep.hom_comp, Representation.IntertwiningMap.comp_apply] at e
  rw [tensorHom_cupCochain, tensorHom_cupCochain] at e
  exact e

omit [TopologicalSpace G] [IsTopologicalGroup G] [IsDiscreteRep S.X₁] [IsDiscreteRep S.X₂] [IsDiscreteRep S.X₃] [IsDiscreteRep T.X₁]
  [IsDiscreteRep T.X₂] [IsDiscreteRep T.X₃] [IsDiscreteRep C] in

theorem cupCochain_pairing_right (h₂₃ : (𝟙 S.X₂ ⊗ₘ T.f) ≫ μ₂ = (S.g ⊗ₘ 𝟙 T.X₁) ≫ μ₃)
    {p q n : ℕ} (h : p + q = n) (a : (Fin p → G) → S.X₂) (b : (Fin q → G) → T.X₁)
    (σ : Fin n → G) :
    μ₂.hom (cupCochain h a (fun τ => T.f.hom (b τ)) σ) =
      μ₃.hom (cupCochain h (fun τ => S.g.hom (a τ)) b σ) := by
  have e := congrArg (fun φ : S.X₂ ⊗ T.X₁ ⟶ C => φ.hom (cupCochain h a b σ)) h₂₃
  simp only [Rep.hom_comp, Representation.IntertwiningMap.comp_apply] at e
  rw [tensorHom_cupCochain, tensorHom_cupCochain] at e
  exact e

theorem cupPairing_δ_add_cupPairing_δ (h₁₂ : (S.f ⊗ₘ 𝟙 T.X₂) ≫ μ₂ = (𝟙 S.X₁ ⊗ₘ T.g) ≫ μ₁)
    (h₂₃ : (𝟙 S.X₂ ⊗ₘ T.f) ≫ μ₂ = (S.g ⊗ₘ 𝟙 T.X₁) ≫ μ₃) (hS : S.ShortExact) (hT : T.ShortExact)
    {p p' q q' n : ℕ} (hp : p + 1 = p') (hq : q + 1 = q') (h₁ : p' + q = n) (h₃ : p + q' = n)
    (x : cohomology S.X₃ p) (y : cohomology T.X₃ q) :
    cupPairing μ₁ h₁ (δ hS p p' hp x) y + (-1 : k) ^ p • cupPairing μ₃ h₃ x (δ hT q q' hq y) =
      0 := by
  subst hp hq
  obtain rfl : n = p + q + 1 := by omega
  obtain ⟨x₃, rfl⟩ := cohomologyπ_surjective S.X₃ p x
  obtain ⟨y₃, rfl⟩ := cohomologyπ_surjective T.X₃ q y
  have := hS.epi_g
  have := hT.epi_g
  obtain ⟨x₂, hx₂⟩ := (ModuleCat.epi_iff_surjective ((cochainsMap S.g).f p)).1 inferInstance
    (cocycleι S.X₃ p x₃)
  obtain ⟨x₁, hx₁⟩ := exists_cocycle_map_f_eq_d hS (p + 1) x₃ x₂ hx₂
  obtain ⟨y₂, hy₂⟩ := (ModuleCat.epi_iff_surjective ((cochainsMap T.g).f q)).1 inferInstance
    (cocycleι T.X₃ q y₃)
  obtain ⟨y₁, hy₁⟩ := exists_cocycle_map_f_eq_d hT (q + 1) y₃ y₂ hy₂
  have hx₂' : (fun σ => S.g.hom (cochainOf S.X₂ x₂ σ)) = cochainOf S.X₃ (cocycleι S.X₃ p x₃) :=
    congrArg (cochainOf S.X₃) hx₂
  have hx₁' : (fun σ => S.f.hom (cochainOf S.X₁ (cocycleι S.X₁ (p + 1) x₁) σ)) =
      (inhomogeneousCochains.d S.X₂ p).hom (cochainOf S.X₂ x₂) :=
    (congrArg (cochainOf S.X₂) hx₁).trans (cochainOf_d x₂)
  have hy₂' : (fun σ => T.g.hom (cochainOf T.X₂ y₂ σ)) = cochainOf T.X₃ (cocycleι T.X₃ q y₃) :=
    congrArg (cochainOf T.X₃) hy₂
  have hy₁' : (fun σ => T.f.hom (cochainOf T.X₁ (cocycleι T.X₁ (q + 1) y₁) σ)) =
      (inhomogeneousCochains.d T.X₂ q).hom (cochainOf T.X₂ y₂) :=
    (congrArg (cochainOf T.X₂) hy₁).trans (cochainOf_d y₂)
  rw [δ_cohomologyπ_of_lift hS rfl x₃ x₂ hx₂ x₁ hx₁, δ_cohomologyπ_of_lift hT rfl y₃ y₂ hy₂ y₁ hy₁,
    cupPairing_cohomologyπ, cupPairing_cohomologyπ, ← map_smul, ← map_add]
  have key : HomologicalComplex.cyclesMap (cochainsMap μ₁) (p + q + 1) (cupCocycles h₁ x₁ y₃) +
      (-1 : k) ^ p • HomologicalComplex.cyclesMap (cochainsMap μ₃) (p + q + 1)
        (cupCocycles h₃ x₃ y₁) =
      (cochainsComplex C).toCycles (p + q) (p + q + 1)
        ((cochainsMap μ₂).f (p + q) (cupLocallyConstant rfl x₂ y₂)) := by
    apply cocycleι_injective
    apply cochainOf_injective
    have hcomm := ConcreteCategory.congr_hom ((cochainsMap μ₂).comm (p + q) (p + q + 1))
      (cupLocallyConstant rfl x₂ y₂)
    rw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply] at hcomm
    rw [map_add, map_smul, cochainOf_add, cochainOf_smul, cochainOf_cocycleι_cyclesMap,
      cochainOf_cocycleι_cyclesMap, cocycleι_cupCocycles, cocycleι_cupCocycles,
      cochainOf_cocycleι_toCycles, ← cochainOf_d, hcomm, cochainOf_cochainsMap_f, cochainOf_d]
    simp only [cochainOf_cupLocallyConstant]
    rw [d_cupCochain, ← hx₁', ← hy₁']
    funext σ
    rw [Pi.add_apply, Pi.smul_apply, Pi.add_apply, Pi.smul_apply, map_add, map_smul,
      cupCochain_pairing_left μ₁ μ₂ h₁₂, cupCochain_pairing_right μ₂ μ₃ h₂₃, hx₂', hy₂']
  rw [key, cohomologyπ_toCycles]

theorem cupPairing_δ_eq (h₁₂ : (S.f ⊗ₘ 𝟙 T.X₂) ≫ μ₂ = (𝟙 S.X₁ ⊗ₘ T.g) ≫ μ₁)
    (h₂₃ : (𝟙 S.X₂ ⊗ₘ T.f) ≫ μ₂ = (S.g ⊗ₘ 𝟙 T.X₁) ≫ μ₃) (hS : S.ShortExact) (hT : T.ShortExact)
    {p p' q q' n : ℕ} (hp : p + 1 = p') (hq : q + 1 = q') (h₁ : p' + q = n) (h₃ : p + q' = n)
    (x : cohomology S.X₃ p) (y : cohomology T.X₃ q) :
    cupPairing μ₁ h₁ (δ hS p p' hp x) y =
      (-1 : k) ^ (p + 1) • cupPairing μ₃ h₃ x (δ hT q q' hq y) := by
  rw [eq_neg_of_add_eq_zero_left
    (cupPairing_δ_add_cupPairing_δ μ₁ μ₂ μ₃ h₁₂ h₂₃ hS hT hp hq h₁ h₃ x y), pow_succ, mul_neg_one,
    neg_smul]

end GroundTheory.ProfCoh
