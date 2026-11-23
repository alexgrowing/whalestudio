import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SeparatingAlgebras.BlockBoundAlt
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.DefU
open UpperTheory.Gal.Gen

theorem UpperTheory.Gal.Gen.kerOpen_pf :
    UpperTheory.Gal.Gen.PowNhds → UpperTheory.Gal.Gen.KerOpen := by
  intro hP E _ _ w a J hJ A _ _ θ
  have hN : Nat.card A ≠ 0 := Nat.card_pos.ne'
  have hV := hP E w a (Nat.card A) hN (J : Set (GL (Fin a) (w.adicCompletion E)))
    (hJ.mem_nhds J.one_mem)
  refine ⟨interior ((fun x => x ^ Nat.card A) '' (J : Set (GL (Fin a) (w.adicCompletion E)))),
    isOpen_interior, mem_interior_iff_mem_nhds.2 hV, ?_⟩
  intro x hx
  obtain ⟨y, hy, hxy⟩ := interior_subset hx
  have hx' : x = (⟨y, hy⟩ : J) ^ Nat.card A := Subtype.ext (by simpa using hxy.symm)
  rw [hx', map_pow, pow_card_eq_one']
