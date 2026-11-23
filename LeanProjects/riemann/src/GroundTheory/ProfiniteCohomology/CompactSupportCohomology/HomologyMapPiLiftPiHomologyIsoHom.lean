import Mathlib
import GroundTheory.ProfiniteCohomology.CompactSupportCohomology.HomApplyHomApplyEqOfCompEq
import GroundTheory.ProfiniteCohomology.FilteredHomology
set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

open CategoryTheory Limits

universe u

variable {k : Type u} [CommRing k]

section Pi

variable {ι : Type u} (K : ι → CochainComplex (ModuleCat.{u} k) ℕ)

theorem piComplex_d_hom_apply' (i j : ℕ) (x : (piComplex K).X i) (v : ι) :
    ((piComplex K).d i j).hom x v = ((K v).d i j).hom (x v) := by
  by_cases h : i + 1 = j
  · subst h
    exact piComplex_d_hom_apply K i x v
  · rw [(piComplex K).shape i j h, (K v).shape i j h]
    rfl

noncomputable def piProj (v : ι) : piComplex K ⟶ K v :=
  CochainComplex.ofHom (fun _ => ModuleCat.ofHom (LinearMap.proj v)) fun n =>
    ModuleCat.hom_ext (LinearMap.ext fun x => (piComplex_d_hom_apply K n x v).symm)

theorem piProj_f_hom_apply (v : ι) (n : ℕ) (x : (piComplex K).X n) :
    ((piProj K v).f n).hom x = x v :=
  rfl

@[reassoc (attr := simp)]
theorem piLift_piProj {M : CochainComplex (ModuleCat.{u} k) ℕ} (g : ∀ v, M ⟶ K v) (v : ι) :
    piLift g ≫ piProj K v = g v :=
  HomologicalComplex.hom_ext _ _ fun _ => ModuleCat.hom_ext (LinearMap.ext fun _ => rfl)

noncomputable def piHomologyToPi (n : ℕ) :
    (piComplex K).homology n ⟶ ModuleCat.of k (∀ v, (K v).homology n) :=
  ModuleCat.ofHom (LinearMap.pi fun v => (HomologicalComplex.homologyMap (piProj K v) n).hom)

theorem piHomologyToPi_hom_apply (n : ℕ) (h : (piComplex K).homology n) (v : ι) :
    (piHomologyToPi K n).hom h v = (HomologicalComplex.homologyMap (piProj K v) n).hom h :=
  rfl

theorem piHomologyToPi_bijective (n : ℕ) : Function.Bijective (piHomologyToPi K n).hom := by
  constructor
  · rw [injective_iff_map_eq_zero]
    intro h hh
    obtain ⟨c, rfl⟩ := (ModuleCat.epi_iff_surjective ((piComplex K).homologyπ n)).1 inferInstance h
    have hv : ∀ v, ∃ y : (K v).X ((ComplexShape.up ℕ).prev n),
        ((K v).d _ n).hom y =
          ((K v).iCycles n).hom ((HomologicalComplex.cyclesMap (piProj K v) n).hom c) := by
      intro v
      refine (homologyπ_eq_zero_iff _ _).1 ?_
      rw [← homologyMap_homologyπ_apply]
      exact congrFun hh v
    choose y hy using hv
    refine (homologyπ_eq_zero_iff _ c).2 ⟨show (piComplex K).X _ from y, funext fun v => ?_⟩
    rw [piComplex_d_hom_apply', hy v, iCycles_cyclesMap_apply]
    rfl
  · intro h
    have hv : ∀ v, ∃ c : (K v).cycles n, ((K v).homologyπ n).hom c = h v :=
      fun v => (ModuleCat.epi_iff_surjective ((K v).homologyπ n)).1 inferInstance (h v)
    choose c hc using hv
    obtain ⟨c', hc'⟩ := exists_iCycles_eq (K := piComplex K)
      (show (piComplex K).X n from fun v => ((K v).iCycles n).hom (c v)) (by
        rw [CochainComplex.next]
        funext v
        rw [piComplex_d_hom_apply]
        exact iCycles_d_apply _ n (n + 1) (c v))
    refine ⟨((piComplex K).homologyπ n).hom c', funext fun v => ?_⟩
    rw [piHomologyToPi_hom_apply, homologyMap_homologyπ_apply, ← hc v]
    congr 1
    apply (ModuleCat.mono_iff_injective ((K v).iCycles n)).1 inferInstance
    rw [iCycles_cyclesMap_apply, hc']
    rfl

noncomputable def piHomologyIso (n : ℕ) :
    (piComplex K).homology n ≅ ModuleCat.of k (∀ v, (K v).homology n) :=
  (LinearEquiv.ofBijective (piHomologyToPi K n).hom (piHomologyToPi_bijective K n)).toModuleIso

theorem piHomologyIso_hom_apply (n : ℕ) (h : (piComplex K).homology n) (v : ι) :
    (piHomologyIso K n).hom.hom h v = (HomologicalComplex.homologyMap (piProj K v) n).hom h :=
  rfl

theorem homologyMap_piLift_piHomologyIso_hom {M : CochainComplex (ModuleCat.{u} k) ℕ}
    (g : ∀ v, M ⟶ K v) (n : ℕ) :
    HomologicalComplex.homologyMap (piLift g) n ≫ (piHomologyIso K n).hom =
      ModuleCat.ofHom (LinearMap.pi fun v => (HomologicalComplex.homologyMap (g v) n).hom) := by
  refine ModuleCat.hom_ext (LinearMap.ext fun h => funext fun v => ?_)
  change (HomologicalComplex.homologyMap (piProj K v) n).hom
    ((HomologicalComplex.homologyMap (piLift g) n).hom h) = _
  rw [hom_apply_hom_apply_of_comp_eq (HomologicalComplex.homologyMap_comp _ _ n).symm h,
    piLift_piProj]
  rfl

end Pi

end GroundTheory.ProfCoh
