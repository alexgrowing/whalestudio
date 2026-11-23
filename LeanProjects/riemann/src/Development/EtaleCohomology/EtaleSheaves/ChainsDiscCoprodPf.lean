import Development.EtaleCohomology.EtaleSheaves.CoprodPf

noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC

namespace LateralTheory.E.ChainsDiscCoprodPf

variable (R : Type) [CommRing R]

theorem chains_disc_f {P Q : PSh} (f : P ⟶ Q) (n : ℕ) :
    ((chains R).map (disc.map f)).f (-(n : ℤ)) =
      (chainsXIso R (disc.obj P) n).hom ≫ (free R).map f ≫ (chainsXIso R (disc.obj Q) n).inv := by
  dsimp only [chains, chainsXIso, Functor.comp_map]
  erw [HomologicalComplex.extendMap_f _ ComplexShape.embeddingDownNat (i := n) rfl]
  rfl

theorem isZero_chains_X (E : Spc) (i : ℤ) (hi : ∀ n : ℕ, -(n : ℤ) ≠ i) :
    IsZero (((chains R).obj E).X i) :=
  HomologicalComplex.isZero_extend_X _ ComplexShape.embeddingDownNat i (fun n => hi n)

theorem cofan_of_isos {C : Type*} [Category C] {ι : Type} {A A' : ι → C} {B B' : C}
    (a : ∀ j, A' j ≅ A j) (b : B' ≅ B) (f : ∀ j, A j ⟶ B) (f' : ∀ j, A' j ⟶ B')
    (hf : ∀ j, f' j = (a j).hom ≫ f j ≫ b.inv) (hc : IsColimit (Cofan.mk B f)) :
    Nonempty (IsColimit (Cofan.mk B' f')) := by
  refine ⟨Cofan.IsColimit.mk _ (fun s => b.hom ≫ hc.desc (Cofan.mk s.pt fun j => (a j).inv ≫ s.inj j)) ?_ ?_⟩
  · intro s j
    have := hc.fac (Cofan.mk s.pt fun j => (a j).inv ≫ s.inj j) ⟨j⟩
    simp only [Cofan.mk_ι_app] at this
    change f' j ≫ _ = _
    simp only [hf, Category.assoc, Iso.inv_hom_id_assoc, this, Iso.hom_inv_id_assoc]
  · intro s m hm
    rw [← Iso.inv_comp_eq]
    refine hc.uniq (Cofan.mk s.pt fun j => (a j).inv ≫ s.inj j) _ ?_
    rintro ⟨j⟩
    change f j ≫ b.inv ≫ m = (a j).inv ≫ s.inj j
    rw [← hm j]
    change f j ≫ b.inv ≫ m = (a j).inv ≫ f' j ≫ m
    simp only [hf, Category.assoc, Iso.inv_hom_id_assoc]

theorem cofan_of_zero {C : Type*} [Category C] [HasZeroMorphisms C] {ι : Type} {A : ι → C} {B : C}
    (hA : ∀ j, IsZero (A j)) (hB : IsZero B) (f : ∀ j, A j ⟶ B) :
    Nonempty (IsColimit (Cofan.mk B f)) :=
  ⟨Cofan.IsColimit.mk _ (fun _ => 0) (fun _ j => (hA j).eq_of_src _ _) (fun _ _ _ => hB.eq_of_src _ _)⟩

theorem degColimit {ι : Type} (P : ι → PSh) (Q : PSh) (p : ∀ j, P j ⟶ Q)
    (hc : IsColimit (Cofan.mk ((free R).obj Q) fun j => (free R).map (p j))) (i : ℤ) :
    Nonempty (IsColimit ((HomologicalComplex.eval _ _ i).mapCocone
      (Cofan.mk ((chains R).obj (disc.obj Q)) fun j => (chains R).map (disc.map (p j))))) := by
  rw [(isColimitMapCoconeCofanMkEquiv _ _ _).nonempty_congr]
  by_cases h : 0 < i
  · have h' : ∀ n : ℕ, -(n : ℤ) ≠ i := fun n => by omega
    exact cofan_of_zero (fun j => isZero_chains_X R _ i h') (isZero_chains_X R _ i h') _
  · have hi : i = -(((-i).toNat : ℕ) : ℤ) := by omega
    rw [hi]
    generalize (-i).toNat = n
    exact cofan_of_isos (fun j => chainsXIso R (disc.obj (P j)) n) (chainsXIso R (disc.obj Q) n)
      (fun j => (free R).map (p j)) _ (fun j => chains_disc_f R (p j) n) hc

theorem ChainsDiscCoprod_of : LateralTheory.E.CoprodPf.ChainsDiscCoprod := by
  intro R _ ι P Q p ⟨hc⟩
  exact ⟨HomologicalComplex.isColimitOfEval _ _ (fun i => (degColimit R P Q p hc i).some)⟩

end LateralTheory.E.ChainsDiscCoprodPf
