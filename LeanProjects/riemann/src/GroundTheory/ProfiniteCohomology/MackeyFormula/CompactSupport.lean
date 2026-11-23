import Mathlib
import GroundTheory.ProfiniteCohomology.MackeyFormula.Homotopy
import GroundTheory.ProfiniteCohomology.MackeyFormula.ConeHomotopy
import GroundTheory.ProfiniteCohomology.CompactSupportCohomology.HomologyMapPiLiftPiHomologyIsoHom
set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

open CategoryTheory HomologicalComplex

universe u

section PiHomotopy

variable {k : Type u} [CommRing k] {J : Type u} {M : CochainComplex (ModuleCat.{u} k) ℕ}
  {K : J → CochainComplex (ModuleCat.{u} k) ℕ}

noncomputable def piLiftHomotopy {g g' : ∀ j, M ⟶ K j} (h : ∀ j, Homotopy (g j) (g' j)) :
    Homotopy (piLift g) (piLift g') where
  hom a b := ModuleCat.ofHom (LinearMap.pi fun j => ((h j).hom a b).hom)
  zero a b hab := ModuleCat.hom_ext (LinearMap.ext fun x => funext fun j => by
    change ((h j).hom a b).hom x = 0
    rw [(h j).zero a b hab]
    rfl)
  comm a := by
    refine ModuleCat.hom_ext (LinearMap.ext fun x => funext fun j => ?_)
    have e := congrArg (fun ψ => ψ.hom x) ((h j).comm a)
    change ((g j).f a).hom x = ((h j).hom ((ComplexShape.up ℕ).next a) a).hom
        ((M.d a ((ComplexShape.up ℕ).next a)).hom x) +
      ((K j).d ((ComplexShape.up ℕ).prev a) a).hom
        (((h j).hom a ((ComplexShape.up ℕ).prev a)).hom x) + ((g' j).f a).hom x at e
    change ((g j).f a).hom x = ((h j).hom ((ComplexShape.up ℕ).next a) a).hom
        ((M.d a ((ComplexShape.up ℕ).next a)).hom x) +
      ((piComplex K).d ((ComplexShape.up ℕ).prev a) a).hom
        (fun j' => ((h j').hom a ((ComplexShape.up ℕ).prev a)).hom x) j + ((g' j).f a).hom x
    erw [piComplex_d_hom_apply']
    exact e

end PiHomotopy

variable {k G : Type u} [CommRing k] [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] {ι : Type u} {Hv : ι → Type u} [∀ v, Group (Hv v)]
  [∀ v, TopologicalSpace (Hv v)] [∀ v, IsTopologicalGroup (Hv v)] [∀ v, CompactSpace (Hv v)]
  (V : OpenSubgroup G) (φ : ∀ v, Hv v →ₜ* G) (N : Rep.{u} k (V : Subgroup G)) [IsDiscreteRep N]

abbrev MackeyIndex : Type u :=
  Σ v : ι, MackeyDoubleCoset (V : Subgroup G) (φ v).toMonoidHom

noncomputable abbrev mackeyGroup (p : MackeyIndex V φ) : Type u :=
  mackeySubgroup (V : Subgroup G) (φ p.1).toMonoidHom p.2.out

noncomputable def mackeyFamily (p : MackeyIndex V φ) : mackeyGroup V φ p →ₜ* (V : Subgroup G) :=
  mackeyConjₜ V (φ p.1) p.2.out

noncomputable abbrev mackeyCoeff (p : MackeyIndex V φ) : Rep.{u} k (mackeyGroup V φ p) :=
  mackeyRep (V : Subgroup G) (φ p.1).toMonoidHom N p.2.out

noncomputable def mackeyLocalMap :
    piComplex (fun v => cochainsComplex (Rep.res (φ v).toMonoidHom
        (Rep.coind (V : Subgroup G).subtype N))) ⟶
      piComplex (fun p : MackeyIndex V φ => cochainsComplex (mackeyCoeff V φ N p)) :=
  piLift fun p => piProj _ p.1 ≫ mackeyCochainsMap V (φ p.1) N p.2.out

noncomputable def mackeyLocalHomotopy :
    Homotopy (localRes φ (Rep.coind (V : Subgroup G).subtype N)
        (fun v => Rep.res (φ v).toMonoidHom (Rep.coind (V : Subgroup G).subtype N)) (fun _ => 𝟙 _) ≫
          mackeyLocalMap V φ N)
      (shapiroCochains V N ≫ localRes (mackeyFamily V φ) N (mackeyCoeff V φ N) (fun _ => 𝟙 _)) := by
  refine (Homotopy.ofEq ?_).trans ((piLiftHomotopy fun p =>
    (mackeyHomotopy V (φ p.1) N p.2.out).symm).trans (Homotopy.ofEq ?_))
  · exact HomologicalComplex.hom_ext _ _ fun _ => ModuleCat.hom_ext (LinearMap.ext fun _ => rfl)
  · exact HomologicalComplex.hom_ext _ _ fun _ => ModuleCat.hom_ext (LinearMap.ext fun _ => rfl)

noncomputable def mackeyCompactMap :
    compactCochains φ (Rep.coind (V : Subgroup G).subtype N)
        (fun v => Rep.res (φ v).toMonoidHom (Rep.coind (V : Subgroup G).subtype N)) (fun _ => 𝟙 _) ⟶
      compactCochains (mackeyFamily V φ) N (mackeyCoeff V φ N) (fun _ => 𝟙 _) :=
  mappingCoconeNat.mapOfHomotopy (mackeyLocalHomotopy V φ N)

theorem isIso_homologyMap_shapiroCochains (n : ℕ) :
    IsIso (homologyMap (shapiroCochains V N) n) := by
  rw [homologyMap_shapiroCochains]
  exact isIso_shapiroMap' V N n

theorem isIso_homologyMap_mackeyLocalMap (n : ℕ) : IsIso (homologyMap (mackeyLocalMap V φ N) n) := by
  have hS := piHomologyToPi_bijective (fun v => cochainsComplex (Rep.res (φ v).toMonoidHom
    (Rep.coind (V : Subgroup G).subtype N))) n
  have hT := piHomologyToPi_bijective
    (fun p : MackeyIndex V φ => cochainsComplex (mackeyCoeff V φ N p)) n

  have key : ∀ x (p : MackeyIndex V φ),
      (piHomologyToPi _ n).hom ((homologyMap (mackeyLocalMap V φ N) n).hom x) p =
        (mackeyCohomologyMap V (φ p.1) N p.2.out n).hom ((piHomologyToPi _ n).hom x p.1) := by
    intro x p
    rw [piHomologyToPi_hom_apply, piHomologyToPi_hom_apply, ← homologyMap_mackeyCochainsMap,
      hom_apply_hom_apply_of_comp_eq (homologyMap_comp _ _ n).symm x]
    erw [mackeyLocalMap, piLift_piProj, homologyMap_comp]
    rfl
  have hM := fun v => mackeyCohomology_bijective V (φ v) N n
  have hbij : Function.Bijective (homologyMap (mackeyLocalMap V φ N) n).hom := by
    refine ⟨fun x x' hx => hS.1 (funext fun v => (hM v).1 (funext fun d => ?_)), fun z => ?_⟩
    · have := congrArg (fun w => (piHomologyToPi _ n).hom w ⟨v, d⟩) hx
      simp only [key] at this
      exact this
    · choose c hc using fun v => (hM v).2 fun d => (piHomologyToPi _ n).hom z ⟨v, d⟩
      obtain ⟨x, hx⟩ := hS.2 c
      refine ⟨x, hT.1 (funext fun p => ?_)⟩
      rw [key, hx]
      exact congrFun (hc p.1) p.2
  exact @isIso_of_mono_of_epi _ _ _ _ _ _ ((ModuleCat.mono_iff_injective _).2 hbij.1)
    ((ModuleCat.epi_iff_surjective _).2 hbij.2)

theorem isIso_homologyMap_mackeyCompactMap (n : ℕ) :
    IsIso (homologyMap (mackeyCompactMap V φ N) n) :=
  mappingCoconeNat.isIso_homologyMap_mapOfHomotopy _
    (isIso_homologyMap_shapiroCochains V N) (isIso_homologyMap_mackeyLocalMap V φ N) n

noncomputable def mackeyCompactCohomologyIso (n : ℕ) :
    compactCohomologyRes φ (Rep.coind (V : Subgroup G).subtype N) n ≅
      compactCohomology (mackeyFamily V φ) N (mackeyCoeff V φ N) (fun _ => 𝟙 _) n :=
  @asIso _ _ _ _ (homologyMap (mackeyCompactMap V φ N) n)
    (isIso_homologyMap_mackeyCompactMap V φ N n)

end GroundTheory.ProfCoh
