import Mathlib
import GroundTheory.ProfiniteCohomology.RealPlaces.DevissageDefs
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.ProfCoh

open CategoryTheory MonoidalCategory Limits GroundTheory.GroupCoh

universe u

attribute [local instance 2000] Rep.hV2

section CupNatural

variable {k G : Type u} [CommRing k] [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {ι : Type u} {H : ι → Type u} [∀ v, Group (H v)] [∀ v, TopologicalSpace (H v)]
  [∀ v, IsTopologicalGroup (H v)] (φ : ∀ v, H v →ₜ* G)
  {κ : Type u} {F : κ → Type u} [∀ w, Group (F w)] [∀ w, TopologicalSpace (F w)]
  [∀ w, IsTopologicalGroup (F w)] [∀ w, Fintype (F w)] (ψ : ∀ w, F w →ₜ* G)
  {A A' B B' C : Rep.{u} k G} [IsDiscreteRep A] [IsDiscreteRep A'] [IsDiscreteRep B]
  [IsDiscreteRep B'] [IsDiscreteRep C]

noncomputable abbrev tateCompactCupResLeibniz (μ : A ⊗ B ⟶ C) :
    LeibnizPairing (tateCompactCochains φ ψ A (fun v => Rep.res (φ v).toMonoidHom A) (fun _ => 𝟙 _)
        (fun w => Rep.res (ψ w).toMonoidHom A) (fun _ => 𝟙 _)) (cochainsComplex B)
      (tateCompactCochains φ ψ C (fun v => Rep.res (φ v).toMonoidHom C) (fun _ => 𝟙 _)
        (fun w => Rep.res (ψ w).toMonoidHom C) (fun _ => 𝟙 _)) :=
  tateCompactCupLeibniz φ ψ μ (fun v => (Rep.resFunctor (φ v).toMonoidHom).map μ)
    (fun w => (Rep.resFunctor (ψ w).toMonoidHom).map μ)
    (fun v => resFunctor_map_comp_id (φ v).toMonoidHom μ)
    (fun w => resFunctor_map_comp_id (ψ w).toMonoidHom μ)

theorem tateCompactCupRes_eq_homology (μ : A ⊗ B ⟶ C) {r s n : ℕ} (h : r + s = n) :
    tateCompactCupRes φ ψ μ h = (tateCompactCupResLeibniz φ ψ μ).homology h :=
  rfl

theorem tateCompactCupResLeibniz_naturality (μ : A ⊗ B ⟶ C) (μ' : A' ⊗ B' ⟶ C) (g : A' ⟶ A)
    (f : B ⟶ B') (hμ : (g ⊗ₘ 𝟙 B) ≫ μ = (𝟙 A' ⊗ₘ f) ≫ μ') {r s n : ℕ} (h : r + s = n)
    (p : (tateCompactCochains φ ψ A' (fun v => Rep.res (φ v).toMonoidHom A') (fun _ => 𝟙 _)
      (fun w => Rep.res (ψ w).toMonoidHom A') (fun _ => 𝟙 _)).X r)
    (z : (cochainsComplex B).X s) :
    (tateCompactCupResLeibniz φ ψ μ).μ h (((tateCompactCochainsResMap φ ψ g).f r).hom p) z =
      (tateCompactCupResLeibniz φ ψ μ').μ h p (((cochainsMap f).f s).hom z) := by
  revert p
  intro (p : (tateGlobalComplex A' fun w => Rep.res (ψ w).toMonoidHom A').X r ×
    shiftNegOneX (tateLocalComplex (fun v => Rep.res (φ v).toMonoidHom A')
      fun w => Rep.res (ψ w).toMonoidHom A') r)
  obtain ⟨⟨x0, e⟩, b⟩ := p
  refine Prod.ext (Prod.ext ?_ ?_) ?_
  · apply cochainOf_injective
    funext σ
    exact (cupCochain_naturality μ μ' g f hμ h (cochainOf _ x0) (cochainOf _ z) σ).symm
  · rcases r with _ | r
    · rcases s with _ | s
      · obtain rfl : n = 0 := by omega
        funext w
        exact congrArg (fun φ' => Rep.Hom.hom φ' ((e w ⊗ₜ[k] cochainOf B z (fun i => i.elim0) :
          (Rep.res (ψ w).toMonoidHom A' ⊗ Rep.res (ψ w).toMonoidHom B : Rep k (F w)))))
          (resFunctor_map_naturality (ψ w).toMonoidHom μ μ' g f hμ)
      · rfl
    · rfl
  · rcases r with _ | r
    · rcases s with _ | t
      · obtain rfl : n = 0 := by omega
        exact Subsingleton.elim (α := PUnit) _ _
      · obtain rfl : n = t + 1 := by omega
        change (0 : (tateLocalComplex (fun v => Rep.res (φ v).toMonoidHom C)
              fun w => Rep.res (ψ w).toMonoidHom C).X t) +
            tateCupHomotopyL ψ (fun w => (Rep.resFunctor (ψ w).toMonoidHom).map μ)
              (Cᵥ := fun v => Rep.res (φ v).toMonoidHom C) (rfl : t + 1 = t + 1)
              ((piRepHom fun w => (Rep.resFunctor (ψ w).toMonoidHom).map g).hom e) z =
          (0 : (tateLocalComplex (fun v => Rep.res (φ v).toMonoidHom C)
              fun w => Rep.res (ψ w).toMonoidHom C).X t) +
            tateCupHomotopyL ψ (fun w => (Rep.resFunctor (ψ w).toMonoidHom).map μ')
              (Cᵥ := fun v => Rep.res (φ v).toMonoidHom C) (rfl : t + 1 = t + 1) e
              (((cochainsMap f).f (t + 1)).hom z)
        erw [tateCupHomotopyL_apply, tateCupHomotopyL_apply]
        refine congrArg _ (Prod.ext rfl (funext fun w => congrArg Neg.neg ?_))
        have key := normHomotopy_compat_left ((Rep.resFunctor (ψ w).toMonoidHom).map μ')
          ((Rep.resFunctor (ψ w).toMonoidHom).map μ) ((Rep.resFunctor (ψ w).toMonoidHom).map g)
          ((Rep.resFunctor (ψ w).toMonoidHom).map f)
          (resFunctor_map_naturality (ψ w).toMonoidHom μ μ' g f hμ) (rfl : t + 1 = t + 1) (e w)
          (((localRes ψ B (fun w => Rep.res (ψ w).toMonoidHom B) fun _ => 𝟙 _).f (t + 1)).hom z w)
        exact key
    · obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨r + s, by omega⟩
      change (tateLocalCup φ ψ (fun v => (Rep.resFunctor (φ v).toMonoidHom).map μ)
            (fun w => (Rep.resFunctor (ψ w).toMonoidHom).map μ)).μ (show r + s = m by omega)
            ((tateLocalMap (fun v => (Rep.resFunctor (φ v).toMonoidHom).map g)
              fun w => (Rep.resFunctor (ψ w).toMonoidHom).map g).f r |>.hom b)
            (((tateLocalResB φ ψ B).f s).hom z) + 0 =
          (tateLocalCup φ ψ (fun v => (Rep.resFunctor (φ v).toMonoidHom).map μ')
            (fun w => (Rep.resFunctor (ψ w).toMonoidHom).map μ')).μ (show r + s = m by omega) b
            (((tateLocalResB φ ψ B').f s).hom (((cochainsMap f).f s).hom z)) + 0
      rw [add_zero, add_zero]
      refine Prod.ext (funext fun v => ?_) (funext fun w => ?_)
      · apply cochainOf_injective
        funext σ
        exact (cupCochain_naturality ((Rep.resFunctor (φ v).toMonoidHom).map μ)
          ((Rep.resFunctor (φ v).toMonoidHom).map μ') ((Rep.resFunctor (φ v).toMonoidHom).map g)
          ((Rep.resFunctor (φ v).toMonoidHom).map f)
          (resFunctor_map_naturality (φ v).toMonoidHom μ μ' g f hμ) (show r + s = m by omega)
          (cochainOf _ (b.1 v)) (fun τ => cochainOf B z (⇑(φ v).toMonoidHom ∘ τ)) σ).symm
      · apply cochainOf_injective
        funext σ
        exact (cupCochain_naturality ((Rep.resFunctor (ψ w).toMonoidHom).map μ)
          ((Rep.resFunctor (ψ w).toMonoidHom).map μ') ((Rep.resFunctor (ψ w).toMonoidHom).map g)
          ((Rep.resFunctor (ψ w).toMonoidHom).map f)
          (resFunctor_map_naturality (ψ w).toMonoidHom μ μ' g f hμ) (show r + s = m by omega)
          (cochainOf _ (b.2 w)) (fun τ => cochainOf B z (⇑(ψ w).toMonoidHom ∘ τ)) σ).symm

theorem tateCompactCupRes_tateCompactCohomologyResMap (μ : A ⊗ B ⟶ C) (μ' : A' ⊗ B' ⟶ C)
    (g : A' ⟶ A) (f : B ⟶ B') (hμ : (g ⊗ₘ 𝟙 B) ≫ μ = (𝟙 A' ⊗ₘ f) ≫ μ') {r s n : ℕ}
    (h : r + s = n) (y : tateCompactCohomologyRes φ ψ A' r) (x : cohomology B s) :
    tateCompactCupRes φ ψ μ h ((tateCompactCohomologyResMap φ ψ g r).hom y) x =
      tateCompactCupRes φ ψ μ' h y ((cohomologyMap f s).hom x) := by
  rw [tateCompactCupRes_eq_homology, tateCompactCupRes_eq_homology]
  exact (LeibnizPairing.homology_homologyMap (tateCompactCupResLeibniz φ ψ μ')
    (tateCompactCupResLeibniz φ ψ μ) (tateCompactCochainsResMap φ ψ g) (cochainsMap f)
    (fun h p z => (tateCompactCupResLeibniz_naturality φ ψ μ μ' g f hμ h p z).symm) h y x).symm

end CupNatural

section DualityNatural

variable {k G : Type u} [CommRing k] [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {ι : Type u} {H : ι → Type u} [∀ v, Group (H v)] [∀ v, TopologicalSpace (H v)]
  [∀ v, IsTopologicalGroup (H v)] (φ : ∀ v, H v →ₜ* G)
  {κ : Type u} {F : κ → Type u} [∀ w, Group (F w)] [∀ w, TopologicalSpace (F w)]
  [∀ w, IsTopologicalGroup (F w)] [∀ w, Fintype (F w)] (ψ : ∀ w, F w →ₜ* G)
  (D : Rep.{u} k G) [IsDiscreteRep D] {n m r s : ℕ} (h : r + s = m)
  (t : tateCompactCohomologyRes φ ψ D m →+ ZMod n)

theorem tateCompactDualityMap_cohomologyMap {A B : Rep.{u} k G} [IsDiscreteRep A] [IsDiscreteRep B]
    [IsDiscreteRep (dualRep D A)] [IsDiscreteRep (dualRep D B)] (f : A ⟶ B)
    (x : cohomology A r) (y : tateCompactCohomologyRes φ ψ (dualRep D B) s) :
    tateCompactDualityMap φ ψ D h t B ((cohomologyMap f r).hom x) y =
      tateCompactDualityMap φ ψ D h t A x ((tateCompactCohomologyResMap φ ψ (dualMap D f) s).hom y) := by
  rw [tateCompactDualityMap_apply, tateCompactDualityMap_apply,
    tateCompactCupRes_tateCompactCohomologyResMap φ ψ (dualEvalPairing D A) (dualEvalPairing D B)
      (dualMap D f) f (tensorHom_dualEvalPairing D f)]

theorem bijective_tateCompactDualityMap_of_sum {J : Type*} [Fintype J] (X : J → Rep.{u} k G)
    [∀ j, IsDiscreteRep (X j)] [∀ j, IsDiscreteRep (dualRep D (X j))] (P : Rep.{u} k G)
    [IsDiscreteRep P] [IsDiscreteRep (dualRep D P)] (i : ∀ j, X j ⟶ P) (p : ∀ j, P ⟶ X j)
    (hsum : ∑ j, p j ≫ i j = 𝟙 P)
    (hX : ∀ j, Function.Bijective (tateCompactDualityMap φ ψ D h t (X j))) :
    Function.Bijective (tateCompactDualityMap φ ψ D h t P) := by
  have hdecomp : ∀ x : cohomology P r,
      x = ∑ j, (cohomologyMap (i j) r).hom ((cohomologyMap (p j) r).hom x) := by
    intro x
    have e := congrArg (fun φ => (cohomologyMap φ r).hom x) hsum
    simp only [cohomologyMap_finsetSum, cohomologyMap_id, cohomologyMap_comp, ModuleCat.hom_sum,
      LinearMap.sum_apply, ModuleCat.hom_comp, LinearMap.comp_apply,
      ModuleCat.hom_id, LinearMap.id_apply] at e
    exact e.symm
  have hdual : ∀ y : tateCompactCohomologyRes φ ψ (dualRep D P) s,
      ∑ j, (tateCompactCohomologyResMap φ ψ (dualMap D (p j)) s).hom
        ((tateCompactCohomologyResMap φ ψ (dualMap D (i j)) s).hom y) = y := by
    intro y
    have e := congrArg (fun F => (tateCompactCohomologyResMap φ ψ (dualMap D F) s).hom y) hsum
    simp only [dualMap_finsetSum, dualMap_comp, tateCompactCohomologyResMap_finsetSum, dualMap_id,
      tateCompactCohomologyResMap_id, tateCompactCohomologyResMap_comp, ModuleCat.hom_sum,
      LinearMap.sum_apply, ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_id,
      LinearMap.id_apply] at e
    exact e
  constructor
  · rw [injective_iff_map_eq_zero]
    intro x hx
    have hj : ∀ j, (cohomologyMap (p j) r).hom x = 0 := by
      intro j
      apply (hX j).1
      rw [map_zero]
      ext y
      rw [AddMonoidHom.zero_apply, tateCompactDualityMap_cohomologyMap, hx, AddMonoidHom.zero_apply]
    rw [hdecomp x]
    simp [hj]
  · intro χ
    choose a ha using fun j => (hX j).2
      (χ.comp (tateCompactCohomologyResMap φ ψ (dualMap D (p j)) s).hom.toAddMonoidHom)
    refine ⟨∑ j, (cohomologyMap (i j) r).hom (a j), ?_⟩
    ext y
    rw [map_sum, AddMonoidHom.finsetSum_apply]
    conv_rhs => rw [← hdual y, map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [tateCompactDualityMap_cohomologyMap, ha j]
    rfl

theorem bijective_tateCompactDualityMap_biproduct {J : Type} [Fintype J] (X : J → Rep.{u} k G)
    [∀ j, IsDiscreteRep (X j)] [∀ j, Finite (X j)]
    (hX : ∀ j, Function.Bijective (tateCompactDualityMap φ ψ D h t (X j))) :
    Function.Bijective (tateCompactDualityMap φ ψ D h t (⨁ X)) :=
  bijective_tateCompactDualityMap_of_sum φ ψ D h t X (⨁ X) (biproduct.ι X) (biproduct.π X)
    (biproduct.total (f := X)) hX

end DualityNatural

section Sign

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {ι : Type u} {H : ι → Type u} [∀ v, Group (H v)] [∀ v, TopologicalSpace (H v)]
  [∀ v, IsTopologicalGroup (H v)] (φ : ∀ v, H v →ₜ* G)
  {κ : Type u} {F : κ → Type u} [∀ w, Group (F w)] [∀ w, TopologicalSpace (F w)]
  [∀ w, IsTopologicalGroup (F w)] [∀ w, Fintype (F w)] (ψ : ∀ w, F w →ₜ* G)
  (D : Rep.{u} (ULift.{u} ℤ) G) [IsDiscreteRep D] {N : ℕ}
  {S : ShortComplex (Rep.{u} (ULift.{u} ℤ) G)} [IsDiscreteRep S.X₁] [IsDiscreteRep S.X₂]
  [IsDiscreteRep S.X₃] [Finite S.X₁] [Finite S.X₂] [Finite S.X₃]

theorem tateCompactDualityMap_δ {n : ℕ} (t : tateCompactCohomologyRes φ ψ D (n + 1) →+ ZMod N)
    (hS : S.ShortExact) (hT : (dualShortComplex D S).ShortExact) {r s : ℕ}
    (h₁ : r + 1 + s = n + 1) (h₀ : r + (s + 1) = n + 1) (q : cohomology S.X₃ r)
    (y : tateCompactCohomologyRes φ ψ (dualRep D S.X₁) s) :
    tateCompactDualityMap φ ψ D h₁ t S.X₁ ((δ hS r (r + 1) rfl).hom q) y =
      (-(-1 : ℤ) ^ s) • tateCompactDualityMap φ ψ D h₀ t S.X₃ q ((tateCompactδRes φ ψ hT s).hom y) := by
  have key := tateCompactCup_tateCompactδ_add_tateCompactCup_δ φ ψ
    (SAᵥ := fun v => (dualShortComplex D S).map (Rep.resFunctor (φ v).toMonoidHom))
    (fun _ => 𝟙 _)
    (SAᵣ := fun w => (dualShortComplex D S).map (Rep.resFunctor (ψ w).toMonoidHom))
    (fun _ => 𝟙 _) (C := D) (Cᵥ := fun v => Rep.res (φ v).toMonoidHom D) (c := fun _ => 𝟙 _)
    (Cᵣ := fun w => Rep.res (ψ w).toMonoidHom D) (cr := fun _ => 𝟙 _)
    (dualEvalPairing D S.X₃) (dualEvalPairing D S.X₂) (dualEvalPairing D S.X₁)
    (fun v => (Rep.resFunctor (φ v).toMonoidHom).map (dualEvalPairing D S.X₃))
    (fun v => (Rep.resFunctor (φ v).toMonoidHom).map (dualEvalPairing D S.X₂))
    (fun v => (Rep.resFunctor (φ v).toMonoidHom).map (dualEvalPairing D S.X₁))
    (fun w => (Rep.resFunctor (ψ w).toMonoidHom).map (dualEvalPairing D S.X₃))
    (fun w => (Rep.resFunctor (ψ w).toMonoidHom).map (dualEvalPairing D S.X₂))
    (fun w => (Rep.resFunctor (ψ w).toMonoidHom).map (dualEvalPairing D S.X₁))
    (fun v => resFunctor_map_comp_id (φ v).toMonoidHom _)
    (fun v => resFunctor_map_comp_id (φ v).toMonoidHom _)
    (fun v => resFunctor_map_comp_id (φ v).toMonoidHom _)
    (fun w => resFunctor_map_comp_id (ψ w).toMonoidHom _)
    (fun w => resFunctor_map_comp_id (ψ w).toMonoidHom _)
    (fun w => resFunctor_map_comp_id (ψ w).toMonoidHom _)
    (tensorHom_dualEvalPairing D S.g) (tensorHom_dualEvalPairing D S.f).symm
    (fun v => resFunctor_map_naturality (φ v).toMonoidHom _ _ _ _ (tensorHom_dualEvalPairing D S.g))
    (fun v => (resFunctor_map_naturality (φ v).toMonoidHom _ _ _ _
      (tensorHom_dualEvalPairing D S.f)).symm)
    (fun w => resFunctor_map_naturality (ψ w).toMonoidHom _ _ _ _ (tensorHom_dualEvalPairing D S.g))
    (fun w => (resFunctor_map_naturality (ψ w).toMonoidHom _ _ _ _
      (tensorHom_dualEvalPairing D S.f)).symm)
    hT (fun v => (Rep.shortExact_res (φ v).toMonoidHom).2 hT)
    (fun w => (Rep.shortExact_res (ψ w).toMonoidHom).2 hT) hS
    (show s + 1 + r = n + 1 by omega) (show s + (r + 1) = n + 1 by omega) y q
  rw [tateCompactDualityMap_apply, tateCompactDualityMap_apply]
  exact map_eq_of_add_neg_one_pow_smul_eq_zero t s key

end Sign

end GroundTheory.ProfCoh
