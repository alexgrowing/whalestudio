import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.IsTheta
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.BcDefs
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Polynomial GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.UnitaryBC UpperTheory.V UpperTheory.V.Hi
open UpperTheory.V.W (Plc)
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

private theorem exists_root (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] {m : ℕ} (hm : 0 < m)
    (d : Ideles E) (hd : pFin E (d : Ad E) = 1) : ∃ y : Ideles E, y ^ m = d := by
  have h : ∀ w : InfinitePlace E, ∃ y : w.Completion, y ^ m = (d : Ad E).1 w := fun w => by
    let e := InfinitePlace.Completion.ringEquivComplexOfIsComplex (IsTotallyComplex.isComplex w)
    obtain ⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq (e ((d : Ad E).1 w)) hm
    exact ⟨e.symm z, e.injective (by rw [map_pow, e.apply_symm_apply, hz])⟩
  choose y hy using h
  let Y : Ad E := ((y : InfiniteAdeleRing E), (1 : Af E))
  have hY : Y ^ m = (d : Ad E) := Prod.ext (funext hy) ((one_pow m).trans hd.symm)
  have hu : IsUnit Y := (isUnit_pow_iff hm.ne').1 (hY ▸ d.isUnit)
  exact ⟨hu.unit, Units.ext (by rw [Units.val_pow_eq_pow_val, hu.unit_spec, hY])⟩

theorem UpperTheory.detCharacter_ker_open_trivial_rational_archimedean :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (ν : HChar E) (m : ℕ), 0 < m → ν.OrderDvd m → IsOpen (((chiDet n ν).comp (UA E n).subtype).ker : Set (UA E n)) ∧ (∀ g ∈ ratU E n, chiDet n ν (g : UA E n) = 1) ∧ ∀ g ∈ infU E n, chiDet n ν (g : UA E n) = 1 := by
  intro E _ _ _ n ν m hm h
  have h1 : ∀ x, ν.1 x ^ m = 1 := fun x => congrArg (fun ξ : HChar E => ξ.1 x) h
  refine ⟨isOpen_ker_of_pow _ ?_ hm fun g => h1 _, ?_, ?_⟩
  · exact ν.2.1.comp (Matrix.GeneralLinearGroup.continuous_det.comp continuous_subtype_val)
  · intro g hg
    obtain ⟨γ, hγ⟩ := Subgroup.mem_subgroupOf.1 hg
    rw [← hγ, chiDet_ratGL]
  · intro g hg
    have hg' : Matrix.GeneralLinearGroup.map (pFin E) (g : GA E n) = 1 := hg
    obtain ⟨y, hy⟩ := exists_root E hm (Matrix.GeneralLinearGroup.det (g : GA E n)) (by
      rw [← GlobalTheory.CuspRep.det_map, hg']; simp)
    change ν.1 (Matrix.GeneralLinearGroup.det (g : GA E n)) = 1
    rw [← hy, map_pow, h1]
