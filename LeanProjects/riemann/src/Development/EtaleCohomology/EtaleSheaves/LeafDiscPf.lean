import Development.EtaleCohomology.EtaleSheaves.LeafLevelPf

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex GlobalTheory.EtC HomologicalComplex CochainComplex.HomComplex
namespace LateralTheory.E.LeafDiscPf
variable (R : Type) [CommRing R]

theorem pullK_comp {K L M : Cx R} (f : K ⟶ L) (g : L ⟶ M) (F : Shv R) (n : ℤ) (x : HK R M F n) :
    HK.pull R (f ≫ g) F n x = HK.pull R f F n (HK.pull R g F n x) := by
  obtain ⟨x, rfl⟩ := x.mk_surjective
  refine congrArg CohomologyClass.mk (Cocycle.ext ?_)
  simp [HK.pull, HK.pre, cpre, zcomp, Cochain.ofHom_comp]

theorem pullK_id {K : Cx R} (F : Shv R) (n : ℤ) (x : HK R K F n) : HK.pull R (𝟙 K) F n x = x := by
  obtain ⟨x, rfl⟩ := x.mk_surjective
  refine congrArg CohomologyClass.mk (Cocycle.ext ?_)
  simp [HK.pull, HK.pre, cpre, zcomp]

abbrev Ch (P : PSh) : Cx R := (chains R).obj (disc.obj P)

abbrev S0 (P : PSh) : Cx R := (HomologicalComplex.single (Shv R) (ComplexShape.up ℤ) 0).obj ((free R).obj P)

def e0 (P : PSh) : (Ch R P).X 0 ≅ (free R).obj P := chainsXIso R (disc.obj P) 0

theorem chainsMap_degreeZero {E E' : Spc} (h : E ⟶ E') : ((chains R).map h).f 0 =
    (chainsXIso R E 0).hom ≫ (free R).map (h.app (op (SimplexCategory.mk 0))) ≫ (chainsXIso R E' 0).inv := by
  exact HomologicalComplex.extendMap_f ((chainsN R).map h) ComplexShape.embeddingDownNat (i := 0) rfl

def ι (P : PSh) : S0 R P ⟶ Ch R P :=
  mkHomFromSingle (e0 R P).inv (by
    rintro k rfl
    apply IsZero.eq_of_tgt
    exact HomologicalComplex.isZero_extend_X _ _ _ (fun i => by
      change -(i:ℤ) ≠ 1; omega))

theorem d_zero (P : PSh) : (Ch R P).d (-1) 0 = 0 := by
  have h1 : (ComplexShape.embeddingDownNat).f 1 = (-1 : ℤ) := rfl
  have h0 : (ComplexShape.embeddingDownNat).f 0 = (0 : ℤ) := rfl
  change (((chainsN R).obj (disc.obj P)).extend _).d (-1) 0 = 0
  rw [HomologicalComplex.extend_d_eq _ _ h1 h0]
  have : ((chainsN R).obj (disc.obj P)).d 1 0 = 0 := by
    change (AlgebraicTopology.AlternatingFaceMapComplex.obj _).d (0+1) 0 = 0
    rw [AlgebraicTopology.AlternatingFaceMapComplex.obj_d_eq]
    rw [Fin.sum_univ_two]
    simp only [Fin.val_zero, Fin.val_one, Fin.isValue, pow_zero, pow_one, one_smul, neg_smul, one_zsmul, neg_one_zsmul]
    exact add_neg_cancel _
  rw [this]; simp

def π (P : PSh) : Ch R P ⟶ S0 R P :=
  mkHomToSingle (e0 R P).hom (by
    intro i hi
    obtain rfl : i = -1 := by simp at hi; omega
    rw [d_zero]; simp)

theorem retr (P : PSh) : ι R P ≫ π R P = 𝟙 _ := by
  apply HomologicalComplex.from_single_hom_ext
  simp [ι, π, mkHomFromSingle_f, mkHomToSingle_f]

theorem natι {P Q : PSh} (g : P ⟶ Q) :
    (HomologicalComplex.single (Shv R) (ComplexShape.up ℤ) 0).map ((free R).map g) ≫ ι R Q =
      ι R P ≫ (chains R).map (disc.map g) := by
  apply HomologicalComplex.from_single_hom_ext
  simp [ι, e0, mkHomFromSingle_f, chainsMap_degreeZero, single_map_f_self]

theorem natπ {P Q : PSh} (g : P ⟶ Q) :
    (chains R).map (disc.map g) ≫ π R Q =
      π R P ≫ (HomologicalComplex.single (Shv R) (ComplexShape.up ℤ) 0).map ((free R).map g) := by
  apply HomologicalComplex.to_single_hom_ext
  simp [π, e0, mkHomToSingle_f, chainsMap_degreeZero, single_map_f_self]

end LateralTheory.E.LeafDiscPf
open LateralTheory.E.LeafDiscPf in
theorem LateralTheory.E.LeafDiscPf.LeafDisc_of : LateralTheory.E.LeafLevelPf.LeafDisc := by
  intro R _ F P Q g n hs
  let a := mappingCone.map _ _ (ι R P) (ι R Q) (natι R g)
  let b := mappingCone.map _ _ (π R P) (π R Q) (natπ R g)
  have hab : a ≫ b = 𝟙 _ := by
    simp only [a, b, ← mappingCone.map_comp, retr, mappingCone.map_id]
  refine ⟨fun x y => ?_⟩
  have hx := pullK_comp R a b F n x
  have hy := pullK_comp R a b F n y
  rw [hab, pullK_id] at hx hy
  rw [hx, hy, Subsingleton.elim (HK.pull R b F n x) (HK.pull R b F n y)]
