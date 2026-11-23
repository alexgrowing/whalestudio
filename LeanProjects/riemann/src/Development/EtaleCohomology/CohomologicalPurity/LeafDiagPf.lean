import Development.EtaleCohomology.CohomologicalPurity.LeafHensCutDef

noncomputable section
open CategoryTheory Limits

namespace LateralTheory.CohomologicalPurity.Hz.DiagPf

variable {A : Type} [CommRing A] (I : Ideal A)

structure Obj where
  n : ℕ
  K : Ideal (MvPolynomial (Fin n) A)
  good : Good (algebraMap A (MvPolynomial (Fin n) A ⧸ K)) I

variable {I}

abbrev Obj.Q (X : Obj I) : Type := MvPolynomial (Fin X.n) A ⧸ X.K

abbrev Obj.s (X : Obj I) : A →+* X.Q := algebraMap A X.Q

instance : SmallCategory (Obj I) where
  Hom X Y := {f : X.Q →+* Y.Q // f.comp X.s = Y.s}
  id X := ⟨RingHom.id _, RingHom.id_comp _⟩
  comp f g := ⟨g.1.comp f.1, by rw [RingHom.comp_assoc, f.2, g.2]⟩
  id_comp f := Subtype.ext (RingHom.comp_id _)
  comp_id f := Subtype.ext (RingHom.id_comp _)
  assoc f g h := Subtype.ext (RingHom.comp_assoc _ _ _).symm

def DF : Obj I ⥤ CommRingCat.{0} where
  obj X := CommRingCat.of X.Q
  map f := CommRingCat.ofHom f.1
  map_id _ := rfl
  map_comp _ _ := rfl

theorem key (hC : LeafComp) {T : Type} [CommRing T] (φ : A →+* T) (h : Good φ I) :
    ∃ (X : Obj I) (ρ : T →+* X.Q), ρ.comp φ = X.s := by
  let _ := φ.toAlgebra
  have : Algebra.Etale A T := h.etale
  obtain ⟨n, f, hf⟩ := Algebra.FiniteType.iff_quotient_mvPolynomial''.1 (inferInstance : Algebra.FiniteType A T)
  let e0 := Ideal.quotientKerAlgEquivOfSurjective hf
  have hcomp : (e0.symm : T →+* MvPolynomial (Fin n) A ⧸ RingHom.ker f).comp φ =
      algebraMap A (MvPolynomial (Fin n) A ⧸ RingHom.ker f) := by
    have := AlgHom.comp_algebraMap (e0.symm : T →ₐ[A] MvPolynomial (Fin n) A ⧸ RingHom.ker f)
    rw [← RingHom.algebraMap_toAlgebra φ]
    exact this
  have hg : Good (algebraMap A (MvPolynomial (Fin n) A ⧸ RingHom.ker f)) I := by
    rw [← hcomp]
    exact hC.2 _ _ _ _ _ _ h (hC.1 _ _ e0.symm.toRingEquiv _)
  exact ⟨⟨n, RingHom.ker f, hg⟩, e0.symm, hcomp⟩

theorem diag_nonempty (hC : LeafComp) (hS : LeafSup) (hQ : LeafCoeq) (A : Type) [CommRing A] (I : Ideal A) :
    Nonempty (Diag A I) := by
  have hf : IsFiltered (Obj I) :=
    { cocone_objs := fun X Y => by
        obtain ⟨T, _, u, u', huu, hg⟩ := hS _ _ _ X.s Y.s I X.good Y.good
        obtain ⟨Z, ρ, hρ⟩ := key hC _ hg
        refine ⟨Z, ⟨ρ.comp u, by rw [RingHom.comp_assoc, hρ]⟩, ⟨ρ.comp u', ?_⟩, trivial⟩
        rw [RingHom.comp_assoc, ← huu, hρ]
      cocone_maps := fun X Y f g => by
        obtain ⟨T, _, w, hw, hg⟩ := hQ _ _ _ X.s Y.s I f.1 g.1 X.good Y.good f.2 g.2
        obtain ⟨Z, ρ, hρ⟩ := key hC _ hg
        refine ⟨Z, ⟨ρ.comp w, by rw [RingHom.comp_assoc, hρ]⟩, Subtype.ext ?_⟩
        change (ρ.comp w).comp f.1 = (ρ.comp w).comp g.1
        rw [RingHom.comp_assoc, RingHom.comp_assoc, hw]
      nonempty := by
        obtain ⟨Z, _, _⟩ := key hC (RingHom.id A) (hC.1 A A (RingEquiv.refl A) I)
        exact ⟨Z⟩ }
  refine ⟨@Diag.mk A _ I (Obj I) _ hf DF (fun X => X.s) (fun e => e.2) (fun X => X.good) ?_⟩
  intro j S _ ψ hψ
  have hg : Good (ψ.comp j.s) I := hC.2 _ _ _ _ _ _ j.good hψ
  obtain ⟨Z, ρ, hρ⟩ := key hC _ hg
  exact ⟨Z, ⟨ρ.comp ψ, hρ⟩, ρ, rfl⟩

end LateralTheory.CohomologicalPurity.Hz.DiagPf

namespace LateralTheory.CohomologicalPurity.Hz

theorem LeafDiag_of (hC : LeafComp) (hS : LeafSup) (hQ : LeafCoeq) : LeafDiag :=
  fun A _ I => DiagPf.diag_nonempty hC hS hQ A I

end LateralTheory.CohomologicalPurity.Hz
