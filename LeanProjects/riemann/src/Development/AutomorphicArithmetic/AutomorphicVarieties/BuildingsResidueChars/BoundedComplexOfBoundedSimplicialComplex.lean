import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TupleActions.InstMulActionTup
import Development.AutomorphicArithmetic.AutomorphicVarieties.ConvexNerveComplexes.SxExact
import Development.AutomorphicArithmetic.AutomorphicVarieties.HermiteNormalForms.ColsMinSmul
import Development.AutomorphicArithmetic.AutomorphicVarieties.HermiteNormalForms.Stabfin

open NumberField UpperTheory.V UpperTheory.V.Af.BA

private noncomputable def cxK (L : Type) [Field L] [NumberField L] (N : ℕ) : Cx (KT.Gm L N) (KT.Vx L N) where
  S := ConeExtensionAcyclic.simp (KT.qc L N) (KT.Psd L N)
  comp := fun f t ht => by
    obtain ⟨y, hy, h⟩ := ht
    exact ⟨y, hy, fun j => h (f j)⟩
  smul := fun g t ht => KT.smul_mem_simp g ht

theorem UpperTheory.bounded_complex_of_bounded_simplicial_complex :
    UpperTheory.V.Af.BA.BddCx → UpperTheory.V.Af.BA.BddComplex := by
  intro H L _ _ _ N
  refine H (KT.Gm L N) (KT.Vx L N) (cxK L N) (fun m => ConeExtensionAcyclic.sx_exact L N m) (fun p => ?_) (fun t => ?_)
  · haveI : Finite (MulAction.orbitRel.Quotient (KT.Gm L N) ((cxK L N).Tup p)) := (KT.orb L N p).1
    refine ⟨Set.range (fun c : MulAction.orbitRel.Quotient (KT.Gm L N) ((cxK L N).Tup p) => Quotient.out c),
      Set.finite_range _, fun x => ?_⟩
    obtain ⟨g, hg⟩ := MulAction.orbitRel_apply.1
      (Quotient.exact (Quotient.out_eq (Quotient.mk (MulAction.orbitRel (KT.Gm L N) ((cxK L N).Tup p)) x)))
    exact ⟨g, _, hg.symm⟩
  · haveI := KT.stabfin L N (t.1 0)
    refine Finite.of_injective (fun g : MulAction.stabilizer (KT.Gm L N) t =>
      (⟨g.1, congrFun (congrArg Subtype.val g.2) 0⟩ : MulAction.stabilizer (KT.Gm L N) (t.1 0))) fun g k e => ?_
    exact Subtype.ext (Subtype.mk.inj e)
