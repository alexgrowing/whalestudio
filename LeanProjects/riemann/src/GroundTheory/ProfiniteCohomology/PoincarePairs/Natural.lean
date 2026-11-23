import Mathlib
import GroundTheory.ProfiniteCohomology.PoincarePairs.IsDiscreteRepResHomCoindRes
import GroundTheory.ProfiniteCohomology.PoincareDuality.Devissage
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.ProfCoh

open CategoryTheory MonoidalCategory Limits GroundTheory.GroupCoh

universe u

attribute [local instance 2000] Rep.hV2

section LeibnizNatural

variable {k : Type u} [CommRing k] {M M' N N' P : CochainComplex (ModuleCat.{u} k) ℕ}

theorem LeibnizPairing.homology_homologyMap (μ₁ : LeibnizPairing M N P)
    (μ₂ : LeibnizPairing M' N' P) (f : M ⟶ M') (g : N' ⟶ N)
    (hfg : ∀ {r s n : ℕ} (h : r + s = n) (x : M.X r) (y : N'.X s),
      μ₁.μ h x ((g.f s).hom y) = μ₂.μ h ((f.f r).hom x) y)
    {r s n : ℕ} (h : r + s = n) (x : M.homology r) (y : N'.homology s) :
    μ₁.homology h x ((HomologicalComplex.homologyMap g s).hom y) =
      μ₂.homology h ((HomologicalComplex.homologyMap f r).hom x) y := by
  obtain ⟨x, rfl⟩ := homologyπ_hom_surjective M r x
  obtain ⟨y, rfl⟩ := homologyπ_hom_surjective N' s y
  rw [hom_apply_hom_apply_eq_of_comp_eq (HomologicalComplex.homologyπ_naturality g s) y,
    hom_apply_hom_apply_eq_of_comp_eq (HomologicalComplex.homologyπ_naturality f r) x,
    LeibnizPairing.homology_homologyπ, LeibnizPairing.homology_homologyπ]
  congr 1
  apply iCycles_hom_injective
  rw [LeibnizPairing.iCycles_cycles, LeibnizPairing.iCycles_cycles, iCycles_cyclesMap_apply,
    iCycles_cyclesMap_apply]
  exact hfg h _ _

end LeibnizNatural

section ResMap

variable {k G : Type u} [CommRing k] [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {ι : Type u} {Hv : ι → Type u} [∀ v, Group (Hv v)] [∀ v, TopologicalSpace (Hv v)]
  [∀ v, IsTopologicalGroup (Hv v)] (φ : ∀ v, Hv v →ₜ* G)

noncomputable abbrev compactCochainsResMap {A B : Rep.{u} k G} [IsDiscreteRep A] [IsDiscreteRep B]
    (g : A ⟶ B) :
    compactCochains φ A (fun v => Rep.res (φ v).toMonoidHom A) (fun _ => 𝟙 _) ⟶
      compactCochains φ B (fun v => Rep.res (φ v).toMonoidHom B) (fun _ => 𝟙 _) :=
  compactCochainsMap φ (Aᵥ := fun v => Rep.res (φ v).toMonoidHom A)
    (Bᵥ := fun v => Rep.res (φ v).toMonoidHom B) g
    (fun v => (Rep.resFunctor (φ v).toMonoidHom).map g)
    (fun _ => (Category.id_comp _).trans (Category.comp_id _).symm)

noncomputable abbrev compactCohomologyResMap {A B : Rep.{u} k G} [IsDiscreteRep A]
    [IsDiscreteRep B] (g : A ⟶ B) (n : ℕ) :
    compactCohomologyRes φ A n ⟶ compactCohomologyRes φ B n :=
  HomologicalComplex.homologyMap (compactCochainsResMap φ g) n

variable {A B C : Rep.{u} k G} [IsDiscreteRep A] [IsDiscreteRep B] [IsDiscreteRep C]

theorem compactCochainsResMap_add (g₁ g₂ : A ⟶ B) :
    compactCochainsResMap φ (g₁ + g₂) = compactCochainsResMap φ g₁ + compactCochainsResMap φ g₂ := by
  ext n : 1
  refine ModuleCat.hom_ext (LinearMap.ext fun (p : (cochainsComplex A).X n ×
    shiftNegOneX (piComplex fun v => cochainsComplex (Rep.res (φ v).toMonoidHom A)) n) =>
      Prod.ext ?_ ?_)
  · exact congrArg (fun F => (F.f n).hom p.1) (cochainsMap_add g₁ g₂)
  · cases n with
    | zero => rfl
    | succ n =>
      refine funext fun v => ?_
      exact congrArg (fun F => (F.f n).hom (p.2 v)) (cochainsMap_add
        ((Rep.resFunctor (φ v).toMonoidHom).map g₁) ((Rep.resFunctor (φ v).toMonoidHom).map g₂))

theorem compactCochainsResMap_zero :
    compactCochainsResMap φ (0 : A ⟶ B) = 0 := by
  ext n : 1
  refine ModuleCat.hom_ext (LinearMap.ext fun (p : (cochainsComplex A).X n ×
    shiftNegOneX (piComplex fun v => cochainsComplex (Rep.res (φ v).toMonoidHom A)) n) =>
      Prod.ext ?_ ?_)
  · exact congrArg (fun F => (F.f n).hom p.1) (cochainsMap_zero (A := A) (B := B))
  · cases n with
    | zero => rfl
    | succ n =>
      refine funext fun v => ?_
      exact congrArg (fun F => (F.f n).hom (p.2 v))
        (cochainsMap_zero (A := Rep.res (φ v).toMonoidHom A) (B := Rep.res (φ v).toMonoidHom B))

theorem compactCochainsResMap_id : compactCochainsResMap φ (𝟙 A) = 𝟙 _ := by
  ext n : 1
  refine ModuleCat.hom_ext (LinearMap.ext fun (p : (cochainsComplex A).X n ×
    shiftNegOneX (piComplex fun v => cochainsComplex (Rep.res (φ v).toMonoidHom A)) n) =>
      Prod.ext rfl ?_)
  cases n with
  | zero => rfl
  | succ n => rfl

theorem compactCochainsResMap_comp (g : A ⟶ B) (g' : B ⟶ C) :
    compactCochainsResMap φ (g ≫ g') = compactCochainsResMap φ g ≫ compactCochainsResMap φ g' := by
  ext n : 1
  refine ModuleCat.hom_ext (LinearMap.ext fun (p : (cochainsComplex A).X n ×
    shiftNegOneX (piComplex fun v => cochainsComplex (Rep.res (φ v).toMonoidHom A)) n) =>
      Prod.ext rfl ?_)
  cases n with
  | zero => rfl
  | succ n => rfl

theorem compactCohomologyResMap_add (g₁ g₂ : A ⟶ B) (n : ℕ) :
    compactCohomologyResMap φ (g₁ + g₂) n =
      compactCohomologyResMap φ g₁ n + compactCohomologyResMap φ g₂ n := by
  rw [compactCohomologyResMap, compactCochainsResMap_add, HomologicalComplex.homologyMap_add]
  rfl

theorem compactCohomologyResMap_zero (n : ℕ) : compactCohomologyResMap φ (0 : A ⟶ B) n = 0 := by
  rw [compactCohomologyResMap, compactCochainsResMap_zero, HomologicalComplex.homologyMap_zero]
  rfl

theorem compactCohomologyResMap_id (n : ℕ) : compactCohomologyResMap φ (𝟙 A) n = 𝟙 _ := by
  rw [compactCohomologyResMap, compactCochainsResMap_id, HomologicalComplex.homologyMap_id]
  rfl

theorem compactCohomologyResMap_comp (g : A ⟶ B) (g' : B ⟶ C) (n : ℕ) :
    compactCohomologyResMap φ (g ≫ g') n =
      compactCohomologyResMap φ g n ≫ compactCohomologyResMap φ g' n := by
  rw [compactCohomologyResMap, compactCochainsResMap_comp, HomologicalComplex.homologyMap_comp]
  rfl

theorem compactCohomologyResMap_finsetSum {J : Type*} (s : Finset J) (f : J → (A ⟶ B)) (m : ℕ) :
    compactCohomologyResMap φ (∑ j ∈ s, f j) m = ∑ j ∈ s, compactCohomologyResMap φ (f j) m := by
  classical
  induction s using Finset.induction with
  | empty => simp [compactCohomologyResMap_zero]
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, compactCohomologyResMap_add, ih]

theorem nsmul_compactCohomologyRes_eq_zero {m : ℕ} (hm : ∀ a : A, m • a = 0) (n : ℕ)
    (x : compactCohomologyRes φ A n) : m • x = 0 := by
  have h0 : (∑ _j ∈ Finset.range m, 𝟙 A) = 0 := by
    rw [Finset.sum_const, Finset.card_range]
    ext a
    exact hm a
  have e : (compactCohomologyResMap φ (∑ _j ∈ Finset.range m, 𝟙 A) n).hom x =
      (compactCohomologyResMap φ (0 : A ⟶ A) n).hom x := by rw [h0]
  rw [compactCohomologyResMap_finsetSum, compactCohomologyResMap_zero] at e
  simp only [compactCohomologyResMap_id, Finset.sum_const, Finset.card_range] at e
  simpa using e

end ResMap

section CupNatural

variable {k G : Type u} [CommRing k] [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {ι : Type u} {Hv : ι → Type u} [∀ v, Group (Hv v)] [∀ v, TopologicalSpace (Hv v)]
  [∀ v, IsTopologicalGroup (Hv v)] (φ : ∀ v, Hv v →ₜ* G)

omit [TopologicalSpace G] [IsTopologicalGroup G] in

theorem cupCochain_naturality {X X' Y Y' Z : Rep.{u} k G} (ν : X ⊗ Y ⟶ Z) (ν' : X' ⊗ Y' ⟶ Z)
    (α : X' ⟶ X) (β : Y ⟶ Y') (hν : (α ⊗ₘ 𝟙 Y) ≫ ν = (𝟙 X' ⊗ₘ β) ≫ ν') {r s n : ℕ}
    (h : r + s = n) (F : (Fin r → G) → X') (E : (Fin s → G) → Y) (σ : Fin n → G) :
    ν'.hom (cupCochain h F (fun τ => β.hom (E τ)) σ) =
      ν.hom (cupCochain h (fun τ => α.hom (F τ)) E σ) :=
  (cupCochain_tensorHom_eq ((α ⊗ₘ 𝟙 Y) ≫ ν) ν' β hν h F E σ).symm.trans
    (cupCochain_tensorHom_eq' _ ν α rfl h F E σ)

omit [TopologicalSpace G] [IsTopologicalGroup G] in

theorem resFunctor_map_naturality {K : Type u} [Group K] (ψ : K →* G)
    {X X' Y Y' Z : Rep.{u} k G} (ν : X ⊗ Y ⟶ Z) (ν' : X' ⊗ Y' ⟶ Z) (α : X' ⟶ X) (β : Y ⟶ Y')
    (hν : (α ⊗ₘ 𝟙 Y) ≫ ν = (𝟙 X' ⊗ₘ β) ≫ ν') :
    ((Rep.resFunctor ψ).map α ⊗ₘ 𝟙 (Rep.res ψ Y)) ≫ (Rep.resFunctor ψ).map ν =
      (𝟙 (Rep.res ψ X') ⊗ₘ (Rep.resFunctor ψ).map β) ≫ (Rep.resFunctor ψ).map ν' := by
  refine Rep.Hom.ext (Representation.IntertwiningMap.ext (LinearMap.ext fun x => ?_))
  induction x using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul a b => exact congrArg (fun F => F.hom (a ⊗ₜ[k] b : (X' ⊗ Y : Rep k G))) hν
  | add x y hx hy => simp only [map_add, hx, hy]

variable {A A' B B' C : Rep.{u} k G} [IsDiscreteRep A] [IsDiscreteRep A'] [IsDiscreteRep B]
  [IsDiscreteRep B'] [IsDiscreteRep C]

noncomputable abbrev compactCupResLeibniz (μ : A ⊗ B ⟶ C) :
    LeibnizPairing (compactCochains φ A (fun v => Rep.res (φ v).toMonoidHom A) (fun _ => 𝟙 _))
      (cochainsComplex B)
      (compactCochains φ C (fun v => Rep.res (φ v).toMonoidHom C) (fun _ => 𝟙 _)) :=
  compactCupLeibniz φ μ (fun v => (Rep.resFunctor (φ v).toMonoidHom).map μ)
    (fun v => resFunctor_map_comp_id (φ v).toMonoidHom μ)

theorem compactCupRes_eq_homology (μ : A ⊗ B ⟶ C) {r s n : ℕ} (h : r + s = n) :
    compactCupRes φ μ h = (compactCupResLeibniz φ μ).homology h :=
  rfl

theorem compactCupRes_compactCohomologyResMap (μ : A ⊗ B ⟶ C) (μ' : A' ⊗ B' ⟶ C) (g : A' ⟶ A)
    (f : B ⟶ B') (hμ : (g ⊗ₘ 𝟙 B) ≫ μ = (𝟙 A' ⊗ₘ f) ≫ μ') {r s n : ℕ} (h : r + s = n)
    (y : compactCohomologyRes φ A' r) (x : cohomology B s) :
    compactCupRes φ μ h ((compactCohomologyResMap φ g r).hom y) x =
      compactCupRes φ μ' h y ((cohomologyMap f s).hom x) := by
  rw [compactCupRes_eq_homology, compactCupRes_eq_homology]
  refine (LeibnizPairing.homology_homologyMap (compactCupResLeibniz φ μ')
    (compactCupResLeibniz φ μ) (compactCochainsResMap φ g) (cochainsMap f) ?_ h y x).symm
  intro r s n h p z
  revert p
  intro (p : (cochainsComplex A').X r ×
    shiftNegOneX (piComplex fun v => cochainsComplex (Rep.res (φ v).toMonoidHom A')) r)
  obtain ⟨x0, b⟩ := p
  refine Prod.ext ?_ ?_
  · apply cochainOf_injective
    funext σ
    exact cupCochain_naturality μ μ' g f hμ h (cochainOf _ x0) (cochainOf _ z) σ
  · cases r with
    | zero => rfl
    | succ r =>
      cases n with
      | zero => rfl
      | succ m =>
        revert b
        intro (b : (piComplex fun v => cochainsComplex (Rep.res (φ v).toMonoidHom A')).X r)
        refine funext fun v => ?_
        apply cochainOf_injective
        funext σ
        exact cupCochain_naturality ((Rep.resFunctor (φ v).toMonoidHom).map μ)
          ((Rep.resFunctor (φ v).toMonoidHom).map μ') ((Rep.resFunctor (φ v).toMonoidHom).map g)
          ((Rep.resFunctor (φ v).toMonoidHom).map f)
          (resFunctor_map_naturality (φ v).toMonoidHom μ μ' g f hμ) (show r + s = m by omega)
          (cochainOf _ (b v)) (fun τ => cochainOf B z (⇑(φ v).toMonoidHom ∘ τ)) σ

end CupNatural

section DualityNatural

variable {k G : Type u} [CommRing k] [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {ι : Type u} {Hv : ι → Type u} [∀ v, Group (Hv v)] [∀ v, TopologicalSpace (Hv v)]
  [∀ v, IsTopologicalGroup (Hv v)] (φ : ∀ v, Hv v →ₜ* G) (D : Rep.{u} k G) [IsDiscreteRep D]
  {n m r s : ℕ} (h : r + s = m) (t : compactCohomologyRes φ D m →+ ZMod n)

omit [TopologicalSpace G] [IsTopologicalGroup G] in

theorem tensorHom_dualEvalPairing {A B : Rep.{u} k G} (f : A ⟶ B) :
    (dualMap D f ⊗ₘ 𝟙 A) ≫ dualEvalPairing D A = (𝟙 (dualRep D B) ⊗ₘ f) ≫ dualEvalPairing D B := by
  refine Rep.Hom.ext (Representation.IntertwiningMap.ext (LinearMap.ext fun x => ?_))
  induction x using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul a b => rfl
  | add x y hx hy => simp only [map_add, hx, hy]

theorem compactDualityMap_cohomologyMap {A B : Rep.{u} k G} [IsDiscreteRep A] [IsDiscreteRep B]
    [IsDiscreteRep (dualRep D A)] [IsDiscreteRep (dualRep D B)] (f : A ⟶ B)
    (x : cohomology A r) (y : compactCohomologyRes φ (dualRep D B) s) :
    compactDualityMap φ D h t B ((cohomologyMap f r).hom x) y =
      compactDualityMap φ D h t A x ((compactCohomologyResMap φ (dualMap D f) s).hom y) := by
  rw [compactDualityMap_apply, compactDualityMap_apply,
    compactCupRes_compactCohomologyResMap φ (dualEvalPairing D A) (dualEvalPairing D B)
      (dualMap D f) f (tensorHom_dualEvalPairing D f)]

theorem bijective_compactDualityMap_of_sum {J : Type*} [Fintype J] (X : J → Rep.{u} k G)
    [∀ j, IsDiscreteRep (X j)] [∀ j, IsDiscreteRep (dualRep D (X j))] (P : Rep.{u} k G)
    [IsDiscreteRep P] [IsDiscreteRep (dualRep D P)] (i : ∀ j, X j ⟶ P) (p : ∀ j, P ⟶ X j)
    (hsum : ∑ j, p j ≫ i j = 𝟙 P)
    (hX : ∀ j, Function.Bijective (compactDualityMap φ D h t (X j))) :
    Function.Bijective (compactDualityMap φ D h t P) := by
  have hdecomp : ∀ x : cohomology P r,
      x = ∑ j, (cohomologyMap (i j) r).hom ((cohomologyMap (p j) r).hom x) := by
    intro x
    have e := congrArg (fun φ => (cohomologyMap φ r).hom x) hsum
    simp only [cohomologyMap_finsetSum, cohomologyMap_id, cohomologyMap_comp, ModuleCat.hom_sum,
      LinearMap.sum_apply, ModuleCat.hom_comp, LinearMap.comp_apply,
      ModuleCat.hom_id, LinearMap.id_apply] at e
    exact e.symm
  have hdual : ∀ y : compactCohomologyRes φ (dualRep D P) s,
      ∑ j, (compactCohomologyResMap φ (dualMap D (p j)) s).hom
        ((compactCohomologyResMap φ (dualMap D (i j)) s).hom y) = y := by
    intro y
    have e := congrArg (fun F => (compactCohomologyResMap φ (dualMap D F) s).hom y) hsum
    simp only [dualMap_finsetSum, dualMap_comp, compactCohomologyResMap_finsetSum, dualMap_id,
      compactCohomologyResMap_id, compactCohomologyResMap_comp, ModuleCat.hom_sum,
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
      rw [AddMonoidHom.zero_apply, compactDualityMap_cohomologyMap, hx, AddMonoidHom.zero_apply]
    rw [hdecomp x]
    simp [hj]
  · intro χ
    choose a ha using fun j => (hX j).2
      (χ.comp (compactCohomologyResMap φ (dualMap D (p j)) s).hom.toAddMonoidHom)
    refine ⟨∑ j, (cohomologyMap (i j) r).hom (a j), ?_⟩
    ext y
    rw [map_sum, AddMonoidHom.finsetSum_apply]
    conv_rhs => rw [← hdual y, map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [compactDualityMap_cohomologyMap, ha j]
    rfl

theorem bijective_compactDualityMap_biproduct {J : Type} [Fintype J] (X : J → Rep.{u} k G)
    [∀ j, IsDiscreteRep (X j)] [∀ j, Finite (X j)]
    (hX : ∀ j, Function.Bijective (compactDualityMap φ D h t (X j))) :
    Function.Bijective (compactDualityMap φ D h t (⨁ X)) :=
  bijective_compactDualityMap_of_sum φ D h t X (⨁ X) (biproduct.ι X) (biproduct.π X)
    (biproduct.total (f := X)) hX

end DualityNatural

end GroundTheory.ProfCoh
