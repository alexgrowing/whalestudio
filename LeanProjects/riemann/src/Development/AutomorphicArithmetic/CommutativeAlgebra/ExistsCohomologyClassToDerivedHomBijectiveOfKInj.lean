import Mathlib
import Development.AutomorphicArithmetic.CommutativeAlgebra.EtaleCohomology.CompLeft
import Development.AutomorphicArithmetic.CommutativeAlgebra.ExtFreeEtaleSheafYoneda

open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC CochainComplex CochainComplex.HomComplex
open LateralTheory.E.EtaleTopologySheaves LateralTheory.E.LeafGhostCut UpperTheory.Et.Loc

theorem UpperTheory.exists_cohomologyClass_to_derivedHom_bijective_of_kInjective :
    ∀ (q : ℕ) (B : Scheme.{0}) (I : Cx (ZMod q)), ∃ l : ∀ (C : B.Etale ⥤ Cx (ZMod q)) (h : ∀ n, Presheaf.IsSheaf (EtTop B) (TP C I n)) (U : B.Etale) (n : ℤ), CohomologyClass (C.obj U) I n → ((OU B q).obj U ⟶ (CategoryTheory.shiftFunctor _ n).obj (DerivedCategory.Q.obj (TC C I h))), (∀ C h, (TC C I h).IsKInjective → ∀ U n, Function.Bijective (l C h U n)) ∧ (∀ C h (U U' : B.Etale) (a : U' ⟶ U) n x, l C h U' n (cpre (Cocycle.ofHom (C.map a)) I n n (zero_add n) x) = (OU B q).map a ≫ l C h U n x) ∧ ∀ (C C' : B.Etale ⥤ Cx (ZMod q)) h h' (φ : C' ⟶ C) U n x, l C' h' U n (cpre (Cocycle.ofHom (φ.app U)) I n n (zero_add n) x) = l C h U n x ≫ (CategoryTheory.shiftFunctor _ n).map (DerivedCategory.Q.map (TM φ I h h')) := by
  intro q B I
  obtain ⟨y, hwd, hK, hU, hT⟩ := UpperTheory.ext_free_etale_sheaf_yoneda B q
  have cz : ∀ (C : B.Etale ⥤ Cx (ZMod q)) (h : ∀ n, Presheaf.IsSheaf (EtTop B) (TP C I n)) (U : B.Etale) (n : ℤ)
      (z : Cocycle (C.obj U) I n), dS (TC C I h) n (n + 1) U (z : Cochain (C.obj U) I n) = 0 :=
    fun C h U n z => Cocycle.δ_eq_zero z (n + 1)
  have wd : ∀ (C : B.Etale ⥤ Cx (ZMod q)) (h : ∀ n, Presheaf.IsSheaf (EtTop B) (TP C I n)) (U : B.Etale) (n : ℤ)
      (z z' : Cocycle (C.obj U) I n), CohomologyClass.mk z = CohomologyClass.mk z' →
      y (TC C I h) U n (z : Cochain (C.obj U) I n) (cz C h U n z) =
        y (TC C I h) U n (z' : Cochain (C.obj U) I n) (cz C h U n z') := by
    intro C h U n z z' hzz
    apply hwd
    have h0 : CohomologyClass.mk (z - z') = 0 := by
      rw [CohomologyClass.mk_sub, hzz, sub_self]
    rw [CohomologyClass.mk_eq_zero_iff, mem_coboundaries_iff _ (n - 1) (by omega)] at h0
    obtain ⟨β, hβ⟩ := h0
    exact ⟨β, hβ⟩
  have lmk : ∀ (C : B.Etale ⥤ Cx (ZMod q)) (h : ∀ n, Presheaf.IsSheaf (EtTop B) (TP C I n)) (U : B.Etale) (n : ℤ)
      (z : Cocycle (C.obj U) I n),
      y (TC C I h) U n ((CohomologyClass.mk_surjective (CohomologyClass.mk z)).choose : Cochain (C.obj U) I n)
        (cz C h U n _) = y (TC C I h) U n (z : Cochain (C.obj U) I n) (cz C h U n z) :=
    fun C h U n z => wd C h U n _ _ (CohomologyClass.mk_surjective _).choose_spec
  refine ⟨fun C h U n x => y (TC C I h) U n ((CohomologyClass.mk_surjective x).choose : Cochain (C.obj U) I n)
    (cz C h U n _), ?_, ?_, ?_⟩
  · intro C h hKI U n
    constructor
    · intro x x' hxx
      obtain ⟨z, rfl⟩ := CohomologyClass.mk_surjective x
      obtain ⟨z', rfl⟩ := CohomologyClass.mk_surjective x'
      dsimp only at hxx
      rw [lmk, lmk] at hxx
      obtain ⟨b, hb⟩ := (hK (TC C I h) hKI U n).1 _ _ _ _ hxx
      rw [← sub_eq_zero, ← CohomologyClass.mk_sub, CohomologyClass.mk_eq_zero_iff,
        mem_coboundaries_iff _ (n - 1) (by omega)]
      exact ⟨b, hb⟩
    · intro x
      obtain ⟨s, hs, hsx⟩ := (hK (TC C I h) hKI U n).2 x
      refine ⟨CohomologyClass.mk (Cocycle.mk s (n + 1) rfl hs), ?_⟩
      dsimp only
      rw [lmk]
      exact hsx
  · intro C h U U' a n x
    obtain ⟨z, rfl⟩ := CohomologyClass.mk_surjective x
    dsimp only
    rw [cpre_mk, lmk, lmk]
    exact hU (TC C I h) U U' a n (z : Cochain (C.obj U) I n) (cz C h U n z) _
  · intro C C' h h' φ U n x
    obtain ⟨z, rfl⟩ := CohomologyClass.mk_surjective x
    dsimp only
    rw [cpre_mk, lmk, lmk]
    exact hT (TC C I h) (TC C' I h') (TM φ I h h') U n (z : Cochain (C.obj U) I n) (cz C h U n z) _
