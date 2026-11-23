import Mathlib
import GroundTheory.ProfiniteCohomology.RealPlaces.LocalCohomologyIsoHomologyMapNormCochains
set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

open CategoryTheory Limits

universe u

variable {k G : Type u} [CommRing k] [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {ι : Type u} {H : ι → Type u} [∀ v, Group (H v)] [∀ v, TopologicalSpace (H v)]
  [∀ v, IsTopologicalGroup (H v)] (φ : ∀ v, H v →ₜ* G)
  {κ : Type u} {F : κ → Type u} [∀ w, Group (F w)] [∀ w, TopologicalSpace (F w)]
  [∀ w, IsTopologicalGroup (F w)] [∀ w, Fintype (F w)] (ψ : ∀ w, F w →ₜ* G)
  (A : Rep.{u} k G) [IsDiscreteRep A] (Aᵥ : ∀ v, Rep.{u} k (H v))
  [∀ v, IsDiscreteRep (Aᵥ v)] (a : ∀ v, Rep.res (φ v).toMonoidHom A ⟶ Aᵥ v)
  (Aᵣ : ∀ w, Rep.{u} k (F w)) [∀ w, IsDiscreteRep (Aᵣ w)]
  (ar : ∀ w, Rep.res (ψ w).toMonoidHom A ⟶ Aᵣ w)

noncomputable def tateForgetCochains :
    tateCompactCochains φ ψ A Aᵥ a Aᵣ ar ⟶ compactCochains φ A Aᵥ a :=
  mappingCoconeNat.map (prodFst _ _) (prodFst _ _) (tateCompactRes_prodFst φ ψ A Aᵥ a Aᵣ ar)

noncomputable def tateForget (n : ℕ) :
    tateCompactCohomology φ ψ A Aᵥ a Aᵣ ar n ⟶ compactCohomology φ A Aᵥ a n :=
  HomologicalComplex.homologyMap (tateForgetCochains φ ψ A Aᵥ a Aᵣ ar) n

@[reassoc (attr := simp)]
theorem tateForget_compactToGlobal (n : ℕ) :
    tateForget φ ψ A Aᵥ a Aᵣ ar n ≫ compactToGlobal φ A Aᵥ a n = tateToGlobal φ ψ A Aᵥ a Aᵣ ar n := by
  exact (HomologicalComplex.homologyMap_comp _ _ n).symm.trans
    (congrArg (fun f => HomologicalComplex.homologyMap f n) (mappingCoconeNat.map_fst _ _ _))

noncomputable def tateLocalFst (n : ℕ) :
    ModuleCat.of k ((∀ v, cohomology (Aᵥ v) n) × (∀ w, cohomology (Aᵣ w) n)) ⟶
      ModuleCat.of k (∀ v, cohomology (Aᵥ v) n) :=
  ModuleCat.ofHom (LinearMap.fst k _ _)

omit [∀ w, Fintype (F w)] in
theorem tateLocalCohomologyIso_inv_homologyMap_prodFst (n : ℕ) :
    (tateLocalCohomologyIso Aᵥ Aᵣ n).inv ≫ HomologicalComplex.homologyMap (prodFst _ _) n =
      tateLocalFst Aᵥ Aᵣ n ≫ (localCohomologyIso Aᵥ n).inv := by
  refine ModuleCat.hom_ext (LinearMap.ext fun p => ?_)
  have hp := hom_apply_hom_apply_of_comp_eq (Iso.inv_hom_id (tateLocalCohomologyIso Aᵥ Aᵣ n)) p
  rw [tateLocalCohomologyIso_hom_apply] at hp
  have h1 := congrArg Prod.fst hp
  change (localCohomologyIso Aᵥ n).hom.hom _ = p.1 at h1
  change (HomologicalComplex.homologyMap (prodFst _ _) n).hom
      ((tateLocalCohomologyIso Aᵥ Aᵣ n).inv.hom p) = (localCohomologyIso Aᵥ n).inv.hom p.1
  rw [← h1]
  exact (hom_apply_hom_apply_of_comp_eq (Iso.hom_inv_id (localCohomologyIso Aᵥ n)) _).symm

@[reassoc]
theorem tateLocalToCompact_tateForget (n : ℕ) :
    tateLocalToCompact φ ψ A Aᵥ a Aᵣ ar n ≫ tateForget φ ψ A Aᵥ a Aᵣ ar (n + 1) =
      tateLocalFst Aᵥ Aᵣ n ≫ localToCompact φ A Aᵥ a n := by
  exact (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·)
    (mappingCoconeNat.homologyδ_naturality _ _ _ n)).trans ((Category.assoc _ _ _).symm.trans
      ((congrArg (· ≫ _) (tateLocalCohomologyIso_inv_homologyMap_prodFst Aᵥ Aᵣ n)).trans
        (Category.assoc _ _ _))))

end GroundTheory.ProfCoh
