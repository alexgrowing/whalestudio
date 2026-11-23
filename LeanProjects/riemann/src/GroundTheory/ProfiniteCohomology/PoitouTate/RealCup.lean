import Mathlib
import GroundTheory.ProfiniteCohomology.PoitouTate.RealAbstract
import GroundTheory.ProfiniteCohomology.RealPlaces.Induced
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.ProfCoh

open CategoryTheory MonoidalCategory

universe u

section LeibnizNatural

variable {k : Type u} [CommRing k] {M M' N P P' : CochainComplex (ModuleCat.{u} k) ℕ}

theorem LeibnizPairing.homologyMap_homology_of_comm (μ₁ : LeibnizPairing M N P)
    (μ₂ : LeibnizPairing M' N P') (f : M ⟶ M') (ψ : P ⟶ P')
    (hfψ : ∀ {r s n : ℕ} (h : r + s = n) (x : M.X r) (y : N.X s),
      (ψ.f n).hom (μ₁.μ h x y) = μ₂.μ h ((f.f r).hom x) y)
    {r s n : ℕ} (h : r + s = n) (x : M.homology r) (y : N.homology s) :
    (HomologicalComplex.homologyMap ψ n).hom (μ₁.homology h x y) =
      μ₂.homology h ((HomologicalComplex.homologyMap f r).hom x) y := by
  obtain ⟨x, rfl⟩ := homologyπ_hom_surjective M r x
  obtain ⟨y, rfl⟩ := homologyπ_hom_surjective N s y
  rw [hom_apply_hom_apply_eq_of_comp_eq (HomologicalComplex.homologyπ_naturality f r) x,
    LeibnizPairing.homology_homologyπ, LeibnizPairing.homology_homologyπ, homologyMap_homologyπ_apply]
  congr 1
  apply iCycles_hom_injective
  rw [LeibnizPairing.iCycles_cycles, iCycles_cyclesMap_apply, LeibnizPairing.iCycles_cycles,
    iCycles_cyclesMap_apply]
  exact hfψ h _ _

end LeibnizNatural

section Forget

variable {k G : Type u} [CommRing k] [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {ι : Type u} {H : ι → Type u} [∀ v, Group (H v)] [∀ v, TopologicalSpace (H v)]
  [∀ v, IsTopologicalGroup (H v)] (φ : ∀ v, H v →ₜ* G)
  {κ : Type u} {F : κ → Type u} [∀ w, Group (F w)] [∀ w, TopologicalSpace (F w)]
  [∀ w, IsTopologicalGroup (F w)] [∀ w, Fintype (F w)] (ψ : ∀ w, F w →ₜ* G)
  {A B C : Rep.{u} k G} [IsDiscreteRep A] [IsDiscreteRep B] [IsDiscreteRep C]

noncomputable abbrev tateForgetRes (A : Rep.{u} k G) [IsDiscreteRep A] :=
  tateForgetCochains φ ψ A (fun v => Rep.res (φ v).toMonoidHom A) (fun _ => 𝟙 _)
    (fun w => Rep.res (ψ w).toMonoidHom A) (fun _ => 𝟙 _)

theorem tateForgetRes_cup (μ : A ⊗ B ⟶ C) {r s n : ℕ} (h : r + s = n)
    (p : (tateCompactCochains φ ψ A (fun v => Rep.res (φ v).toMonoidHom A) (fun _ => 𝟙 _)
      (fun w => Rep.res (ψ w).toMonoidHom A) (fun _ => 𝟙 _)).X r) (z : (cochainsComplex B).X s) :
    ((tateForgetRes φ ψ C).f n).hom ((tateCompactCupResLeibniz φ ψ μ).μ h p z) =
      (compactCupLeibniz φ μ (fun v => (Rep.resFunctor (φ v).toMonoidHom).map μ)
        (fun v => resFunctor_map_comp_id (φ v).toMonoidHom μ)).μ h (((tateForgetRes φ ψ A).f r).hom p) z := by
  revert p
  intro (p : (tateGlobalComplex A fun w => Rep.res (ψ w).toMonoidHom A).X r ×
    shiftNegOneX (tateLocalComplex (fun v => Rep.res (φ v).toMonoidHom A)
      fun w => Rep.res (ψ w).toMonoidHom A) r)
  obtain ⟨⟨x, e⟩, b⟩ := p
  refine Prod.ext rfl ?_
  rcases r with _ | r
  · rcases n with _ | n
    · rfl
    · change (prodFst _ _ |>.f n).hom (0 + tateCupHomotopyL ψ
          (fun w => (Rep.resFunctor (ψ w).toMonoidHom).map μ)
          (Cᵥ := fun v => Rep.res (φ v).toMonoidHom C) (by omega) e z) = 0
      rw [zero_add]
      erw [tateCupHomotopyL_apply]
      rfl
  · rcases n with _ | n
    · omega
    · change (prodFst _ _ |>.f n).hom ((tateLocalCup φ ψ (fun v => (Rep.resFunctor (φ v).toMonoidHom).map μ)
          (fun w => (Rep.resFunctor (ψ w).toMonoidHom).map μ)).μ (show r + s = n by omega) b
          (((tateLocalResB φ ψ B).f s).hom z) + 0) = _
      rw [add_zero]
      rfl

theorem tateForget_tateCompactCupRes (μ : A ⊗ B ⟶ C) {r s n : ℕ} (h : r + s = n)
    (x : tateCompactCohomologyRes φ ψ A r) (z : cohomology B s) :
    (tateForget φ ψ C (fun v => Rep.res (φ v).toMonoidHom C) (fun _ => 𝟙 _)
        (fun w => Rep.res (ψ w).toMonoidHom C) (fun _ => 𝟙 _) n).hom (tateCompactCupRes φ ψ μ h x z) =
      compactCupRes φ μ h ((tateForget φ ψ A (fun v => Rep.res (φ v).toMonoidHom A) (fun _ => 𝟙 _)
        (fun w => Rep.res (ψ w).toMonoidHom A) (fun _ => 𝟙 _) r).hom x) z :=
  LeibnizPairing.homologyMap_homology_of_comm _ _ _ _ (fun h p z => tateForgetRes_cup φ ψ μ h p z) h x z

end Forget

section Target

variable {k G : Type u} [CommRing k] [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {ι : Type u} {H : ι → Type u} [∀ v, Group (H v)] [∀ v, TopologicalSpace (H v)]
  [∀ v, IsTopologicalGroup (H v)] (φ : ∀ v, H v →ₜ* G)
  {κ : Type u} {F : κ → Type u} [∀ w, Group (F w)] [∀ w, TopologicalSpace (F w)]
  [∀ w, IsTopologicalGroup (F w)] [∀ w, Fintype (F w)] (ψ : ∀ w, F w →ₜ* G)
  {A B C C' : Rep.{u} k G} [IsDiscreteRep A] [IsDiscreteRep B] [IsDiscreteRep C] [IsDiscreteRep C']

omit [IsTopologicalGroup G] in

theorem cochainsMap_normHomotopy {F' : Type u} [Group F'] [TopologicalSpace F'] [IsTopologicalGroup F'] [Fintype F'] {X Y Z Z' : Rep.{u} k F'}
    [IsDiscreteRep Y] [IsDiscreteRep Z] [IsDiscreteRep Z'] (μ : X ⊗ Y ⟶ Z) (g : Z ⟶ Z')
    {s m : ℕ} (h : s = m + 1) (e : X) (y : (cochainsComplex Y).X s) :
    ((cochainsMap g).f m).hom (normHomotopy μ h e y) = normHomotopy (μ ≫ g) h e y := by
  apply cochainOf_injective
  funext σ
  rw [cochainOf_normHomotopy]
  change g.hom (cochainOf Z (normHomotopy μ h e y) σ) = _
  rw [cochainOf_normHomotopy]
  change g.hom (∑ a : F', Z.ρ a (μ.hom _)) = ∑ a : F', Z'.ρ a (g.hom (μ.hom _))
  rw [map_sum]
  exact Finset.sum_congr rfl fun a _ => Rep.hom_comm_apply g a _

set_option maxHeartbeats 1600000 in

theorem tateCompactCochainsResMap_cup (μ : A ⊗ B ⟶ C) (g : C ⟶ C') {r s n : ℕ} (h : r + s = n)
    (p : (tateCompactCochains φ ψ A (fun v => Rep.res (φ v).toMonoidHom A) (fun _ => 𝟙 _)
      (fun w => Rep.res (ψ w).toMonoidHom A) (fun _ => 𝟙 _)).X r) (z : (cochainsComplex B).X s) :
    ((tateCompactCochainsResMap φ ψ g).f n).hom ((tateCompactCupResLeibniz φ ψ μ).μ h p z) =
      (tateCompactCupResLeibniz φ ψ (μ ≫ g)).μ h p z := by
  revert p
  intro (p : (tateGlobalComplex A fun w => Rep.res (ψ w).toMonoidHom A).X r ×
    shiftNegOneX (tateLocalComplex (fun v => Rep.res (φ v).toMonoidHom A)
      fun w => Rep.res (ψ w).toMonoidHom A) r)
  obtain ⟨⟨x, e⟩, b⟩ := p
  refine Prod.ext (Prod.ext ?_ ?_) ?_
  · apply cochainOf_injective
    rfl
  · rcases r with _ | r
    · rcases s with _ | s
      · obtain rfl : n = 0 := by omega
        rfl
      · obtain rfl : n = s + 1 := by omega
        exact Subsingleton.elim _ _
    · obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨r + s, by omega⟩
      exact Subsingleton.elim _ _
  · rcases r with _ | r
    · rcases s with _ | t
      · obtain rfl : n = 0 := by omega
        exact Subsingleton.elim (α := PUnit) _ _
      · obtain rfl : n = t + 1 := by omega
        change ((tateLocalMap (fun v => (Rep.resFunctor (φ v).toMonoidHom).map g)
            (fun w => (Rep.resFunctor (ψ w).toMonoidHom).map g)).f t).hom
            ((0 : (tateLocalComplex (fun v => Rep.res (φ v).toMonoidHom C)
              fun w => Rep.res (ψ w).toMonoidHom C).X t) +
            tateCupHomotopyL ψ (fun w => (Rep.resFunctor (ψ w).toMonoidHom).map μ)
              (Cᵥ := fun v => Rep.res (φ v).toMonoidHom C) (rfl : t + 1 = t + 1) e z) =
          (0 : (tateLocalComplex (fun v => Rep.res (φ v).toMonoidHom C')
              fun w => Rep.res (ψ w).toMonoidHom C').X t) +
            tateCupHomotopyL ψ (fun w => (Rep.resFunctor (ψ w).toMonoidHom).map (μ ≫ g))
              (Cᵥ := fun v => Rep.res (φ v).toMonoidHom C') (rfl : t + 1 = t + 1) e z
        rw [zero_add, zero_add]
        erw [tateCupHomotopyL_apply, tateCupHomotopyL_apply]
        refine Prod.ext ?_ (funext fun w => ?_)
        · change ((piMap fun v => cochainsMap ((Rep.resFunctor (φ v).toMonoidHom).map g)).f t).hom 0 = 0
          exact map_zero _
        change ((cochainsMap ((Rep.resFunctor (ψ w).toMonoidHom).map g)).f t).hom
          (-(tateNormHomotopy ψ (fun w => (Rep.resFunctor (ψ w).toMonoidHom).map μ) rfl e z w)) =
            -(tateNormHomotopy ψ (fun w => (Rep.resFunctor (ψ w).toMonoidHom).map (μ ≫ g)) rfl e z w)
        rw [map_neg]
        exact congrArg Neg.neg (cochainsMap_normHomotopy _ _ _ _ _)
    · obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨r + s, by omega⟩
      change ((tateLocalMap (fun v => (Rep.resFunctor (φ v).toMonoidHom).map g)
            (fun w => (Rep.resFunctor (ψ w).toMonoidHom).map g)).f m).hom
          ((tateLocalCup φ ψ (fun v => (Rep.resFunctor (φ v).toMonoidHom).map μ)
            (fun w => (Rep.resFunctor (ψ w).toMonoidHom).map μ)).μ (show r + s = m by omega) b
            (((tateLocalResB φ ψ B).f s).hom z) + 0) =
          (tateLocalCup φ ψ (fun v => (Rep.resFunctor (φ v).toMonoidHom).map (μ ≫ g))
            (fun w => (Rep.resFunctor (ψ w).toMonoidHom).map (μ ≫ g))).μ (show r + s = m by omega) b
            (((tateLocalResB φ ψ B).f s).hom z) + 0
      rw [add_zero, add_zero]
      refine Prod.ext (funext fun v => ?_) (funext fun w => ?_)
      · apply cochainOf_injective
        rfl
      · apply cochainOf_injective
        rfl

theorem tateCompactCohomologyResMap_tateCompactCupRes (μ : A ⊗ B ⟶ C) (g : C ⟶ C') {r s n : ℕ}
    (h : r + s = n) (x : tateCompactCohomologyRes φ ψ A r) (z : cohomology B s) :
    (tateCompactCohomologyResMap φ ψ g n).hom (tateCompactCupRes φ ψ μ h x z) =
      tateCompactCupRes φ ψ (μ ≫ g) h x z := by
  have e := LeibnizPairing.homologyMap_homology_of_comm (tateCompactCupResLeibniz φ ψ μ)
    (tateCompactCupResLeibniz φ ψ (μ ≫ g)) (𝟙 _) (tateCompactCochainsResMap φ ψ g)
    (fun h p z => tateCompactCochainsResMap_cup φ ψ μ g h p z) h x z
  rw [HomologicalComplex.homologyMap_id] at e
  exact e

end Target

end GroundTheory.ProfCoh
