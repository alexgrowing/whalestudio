import Mathlib
import GroundTheory.ProfiniteCohomology.PoincarePairs.Natural
import GroundTheory.ProfiniteCohomology.PoincarePairs
import GroundTheory.ProfiniteCohomology.CompactSupportCohomology.CompactCupEqCompactCupRight
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.ProfCoh

open CategoryTheory MonoidalCategory GroundTheory.GroupCoh

universe u

attribute [local instance 2000] Rep.hV2

section CompactCupNatural

variable {k G : Type u} [CommRing k] [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {ι : Type u} {H : ι → Type u} [∀ v, Group (H v)] [∀ v, TopologicalSpace (H v)]
  [∀ v, IsTopologicalGroup (H v)] (φ : ∀ v, H v →ₜ* G)
  {A A' B C C' : Rep.{u} k G} [IsDiscreteRep A] [IsDiscreteRep A'] [IsDiscreteRep B] [IsDiscreteRep C]
  [IsDiscreteRep C'] {Aᵥ A'ᵥ Cᵥ C'ᵥ : ∀ v, Rep.{u} k (H v)} [∀ v, IsDiscreteRep (Aᵥ v)]
  [∀ v, IsDiscreteRep (A'ᵥ v)] [∀ v, IsDiscreteRep (Cᵥ v)] [∀ v, IsDiscreteRep (C'ᵥ v)]
  {a : ∀ v, Rep.res (φ v).toMonoidHom A ⟶ Aᵥ v} {a' : ∀ v, Rep.res (φ v).toMonoidHom A' ⟶ A'ᵥ v}
  {c : ∀ v, Rep.res (φ v).toMonoidHom C ⟶ Cᵥ v} {c' : ∀ v, Rep.res (φ v).toMonoidHom C' ⟶ C'ᵥ v}

theorem compactCohomologyMap_compactCup (μ : A ⊗ B ⟶ C) (μᵥ : ∀ v, Aᵥ v ⊗ Rep.res (φ v).toMonoidHom B ⟶ Cᵥ v)
    (hμ : ∀ v, (Rep.resFunctor (φ v).toMonoidHom).map μ ≫ c v =
      resTensorHom (φ v).toMonoidHom (a v) (𝟙 _) ≫ μᵥ v)
    (g : C ⟶ C') (gᵥ : ∀ v, Cᵥ v ⟶ C'ᵥ v)
    (hg : ∀ v, c v ≫ gᵥ v = (Rep.resFunctor (φ v).toMonoidHom).map g ≫ c' v)
    (hμ' : ∀ v, (Rep.resFunctor (φ v).toMonoidHom).map (μ ≫ g) ≫ c' v =
      resTensorHom (φ v).toMonoidHom (a v) (𝟙 _) ≫ (μᵥ v ≫ gᵥ v))
    {r s n : ℕ} (h : r + s = n) (x : compactCohomology φ A Aᵥ a r) (y : cohomology B s) :
    (compactCohomologyMap φ g gᵥ hg n).hom (compactCup φ μ μᵥ hμ h x y) =
      compactCup φ (μ ≫ g) (fun v => μᵥ v ≫ gᵥ v) hμ' h x y := by
  refine LeibnizPairing.homologyMap_homology (compactCupLeibniz φ μ μᵥ hμ)
    (compactCupLeibniz φ (μ ≫ g) (fun v => μᵥ v ≫ gᵥ v) hμ') (compactCochainsMap φ g gᵥ hg) ?_ h x y
  intro r s n h p z
  revert p
  intro (p : (cochainsComplex A).X r × shiftNegOneX (piComplex fun v => cochainsComplex (Aᵥ v)) r)
  obtain ⟨x0, b⟩ := p
  refine Prod.ext ?_ ?_
  · apply cochainOf_injective
    rfl
  · cases r with
    | zero =>
      cases n with
      | zero => rfl
      | succ m =>
        change ((piMap fun v => cochainsMap (gᵥ v)).f m).hom 0 = 0
        exact map_zero _
    | succ r =>
      cases n with
      | zero => rfl
      | succ m =>
        revert b
        intro (b : (piComplex fun v => cochainsComplex (Aᵥ v)).X r)
        refine funext fun v => ?_
        apply cochainOf_injective
        rfl

theorem compactCup_compactCohomologyMap (g : A ⟶ A') (gᵥ : ∀ v, Aᵥ v ⟶ A'ᵥ v)
    (hg : ∀ v, a v ≫ gᵥ v = (Rep.resFunctor (φ v).toMonoidHom).map g ≫ a' v)
    (μ' : A' ⊗ B ⟶ C) (μ'ᵥ : ∀ v, A'ᵥ v ⊗ Rep.res (φ v).toMonoidHom B ⟶ Cᵥ v)
    (hμ' : ∀ v, (Rep.resFunctor (φ v).toMonoidHom).map μ' ≫ c v =
      resTensorHom (φ v).toMonoidHom (a' v) (𝟙 _) ≫ μ'ᵥ v)
    (hμ : ∀ v, (Rep.resFunctor (φ v).toMonoidHom).map ((g ⊗ₘ 𝟙 B) ≫ μ') ≫ c v =
      resTensorHom (φ v).toMonoidHom (a v) (𝟙 _) ≫ ((gᵥ v ⊗ₘ 𝟙 _) ≫ μ'ᵥ v))
    {r s n : ℕ} (h : r + s = n) (x : compactCohomology φ A Aᵥ a r) (y : cohomology B s) :
    compactCup φ μ' μ'ᵥ hμ' h ((compactCohomologyMap φ g gᵥ hg r).hom x) y =
      compactCup φ ((g ⊗ₘ 𝟙 B) ≫ μ') (fun v => (gᵥ v ⊗ₘ 𝟙 _) ≫ μ'ᵥ v) hμ h x y := by
  have e := LeibnizPairing.homology_homologyMap
    (compactCupLeibniz φ ((g ⊗ₘ 𝟙 B) ≫ μ') (fun v => (gᵥ v ⊗ₘ 𝟙 _) ≫ μ'ᵥ v) hμ)
    (compactCupLeibniz φ μ' μ'ᵥ hμ') (compactCochainsMap φ g gᵥ hg) (𝟙 (cochainsComplex B)) ?_ h x y
  · rw [HomologicalComplex.homologyMap_id] at e
    exact e.symm
  intro r s n h p z
  revert p
  intro (p : (cochainsComplex A).X r × shiftNegOneX (piComplex fun v => cochainsComplex (Aᵥ v)) r)
  obtain ⟨x0, b⟩ := p
  refine Prod.ext ?_ ?_
  · apply cochainOf_injective
    funext σ
    exact cupCochain_tensorHom_eq' ((g ⊗ₘ 𝟙 B) ≫ μ') μ' g rfl h (cochainOf _ x0) (cochainOf _ z) σ
  · cases r with
    | zero => rfl
    | succ r =>
      cases n with
      | zero => rfl
      | succ m =>
        revert b
        intro (b : (piComplex fun v => cochainsComplex (Aᵥ v)).X r)
        refine funext fun v => ?_
        apply cochainOf_injective
        funext σ
        exact cupCochain_tensorHom_eq' ((gᵥ v ⊗ₘ 𝟙 _) ≫ μ'ᵥ v) (μ'ᵥ v) (gᵥ v) rfl (show r + s = m by omega)
          (cochainOf _ (b v)) (fun τ => cochainOf B z (⇑(φ v).toMonoidHom ∘ τ)) σ

end CompactCupNatural

end GroundTheory.ProfCoh
