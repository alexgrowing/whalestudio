import Development.EtaleCohomology.EtaleSheaves.CechFiltPf

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC CochainComplex CochainComplex.HomComplex

namespace LateralTheory.E.ShiftLvlPf

universe u v

section General

variable {C : Type u} [Category.{v} C] [Abelian C]

def coneIso {A B A' B' : CochainComplex C ℤ} (φ : A ⟶ B) (ψ : A' ⟶ B') (e₁ : A ≅ A') (e₂ : B ≅ B')
    (h : φ ≫ e₂.hom = e₁.hom ≫ ψ) : mappingCone φ ≅ mappingCone ψ where
  hom := mappingCone.map φ ψ e₁.hom e₂.hom h
  inv := mappingCone.map ψ φ e₁.inv e₂.inv
    (by rw [Iso.comp_inv_eq, Category.assoc, h, Iso.inv_hom_id_assoc])
  hom_inv_id := by
    rw [← mappingCone.map_comp]
    simp only [Iso.hom_inv_id]
    exact mappingCone.map_id φ
  inv_hom_id := by
    rw [← mappingCone.map_comp]
    simp only [Iso.inv_hom_id]
    exact mappingCone.map_id ψ

theorem sub_of_iso {K K' : CochainComplex C ℤ} (L : CochainComplex C ℤ) (n : ℤ) (e : K ≅ K')
    (h : Subsingleton (CohomologyClass K' L n)) : Subsingleton (CohomologyClass K L n) := by
  rw [(CohomologyClass.homAddEquiv (K := K) (L := L) (n := n)).toEquiv.subsingleton_congr]
  rw [(CohomologyClass.homAddEquiv (K := K') (L := L) (n := n)).toEquiv.subsingleton_congr] at h
  exact @Equiv.subsingleton _ _ ((((HomotopyCategory.quotient C (ComplexShape.up ℤ)).mapIso e).homCongr (Iso.refl ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).obj (L⟦n⟧))))) h

theorem sub_of_shift {A0 Ap : CochainComplex C ℤ} (I : CochainComplex C ℤ) (p n : ℤ) (e : Ap ≅ A0⟦p⟧)
    (h : Subsingleton (CohomologyClass A0 I (n - p))) : Subsingleton (CohomologyClass Ap I n) := by
  rw [(CohomologyClass.homAddEquiv (K := Ap) (L := I) (n := n)).toEquiv.subsingleton_congr]
  rw [(CohomologyClass.homAddEquiv (K := A0) (L := I) (n := n - p)).toEquiv.subsingleton_congr] at h
  let Q := HomotopyCategory.quotient C (ComplexShape.up ℤ)
  let α : (Q.obj A0)⟦p⟧ ≅ Q.obj Ap := ((Q.commShiftIso p).app A0).symm ≪≫ Q.mapIso e.symm
  let β : (Q.obj (I⟦n - p⟧))⟦p⟧ ≅ Q.obj (I⟦n⟧) :=
    ((Q.commShiftIso p).app _).symm ≪≫ Q.mapIso ((CategoryTheory.shiftFunctorAdd' (CochainComplex C ℤ) (n - p) p n (by omega)).app I).symm
  have e1 := (Functor.FullyFaithful.ofFullyFaithful (CategoryTheory.shiftFunctor (HomotopyCategory C (ComplexShape.up ℤ)) p)).homEquiv
    (X := Q.obj A0) (Y := Q.obj (I⟦n - p⟧))
  exact @Equiv.subsingleton _ _ (e1.trans (α.homCongr β)).symm h

def singleConeIso {X Y : C} (f : X ⟶ Y) (p : ℤ) :
    mappingCone ((HomologicalComplex.single C (ComplexShape.up ℤ) (-p)).map f) ≅
      (mappingCone ((HomologicalComplex.single C (ComplexShape.up ℤ) 0).map f))⟦p⟧ :=
  let σ := (CochainComplex.singleFunctors C).shiftIso p (-p) 0 (by omega)
  coneIso _ _ (σ.app X).symm (σ.app Y).symm (σ.inv.naturality f) ≪≫
    (mappingCone.shiftIso ((HomologicalComplex.single C (ComplexShape.up ℤ) 0).map f) p).symm

end General

theorem chains_f_comm (R : Type) [CommRing R] {E₀ E : Spc} (g : E₀ ⟶ E) (p : ℕ) :
    ((chains R).map g).f (-(p : ℤ)) ≫ (chainsXIso R E p).hom =
      (chainsXIso R E₀ p).hom ≫ (free R).map (g.app (op (SimplexCategory.mk p))) := by
  unfold chains chainsXIso
  rw [Functor.comp_map]
  show (HomologicalComplex.extendMap ((chainsN R).map g) ComplexShape.embeddingDownNat).f (ComplexShape.embeddingDownNat.f p) ≫
      (HomologicalComplex.extendXIso ((chainsN R).obj E) ComplexShape.embeddingDownNat (i := p) rfl).hom =
    (HomologicalComplex.extendXIso ((chainsN R).obj E₀) ComplexShape.embeddingDownNat (i := p) rfl).hom ≫ _
  rw [HomologicalComplex.extendMap_f _ _ (i := p) rfl]
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  congr 1

theorem ShiftLvl_of : LateralTheory.E.CechFiltPf.ShiftLvl := by
  intro R _ F E₀ E g p n h
  have h1 := sub_of_shift (res R F) (p : ℤ) n
    (singleConeIso ((free R).map (g.app (op (SimplexCategory.mk p)))) (p : ℤ)) h
  refine sub_of_iso (res R F) n ?_ h1
  exact coneIso _ _ ((HomologicalComplex.single (Shv R) (ComplexShape.up ℤ) (-(p : ℤ))).mapIso (chainsXIso R E₀ p))
    ((HomologicalComplex.single (Shv R) (ComplexShape.up ℤ) (-(p : ℤ))).mapIso (chainsXIso R E p))
    (by simp only [Functor.mapIso_hom, ← Functor.map_comp, chains_f_comm])

end LateralTheory.E.ShiftLvlPf
