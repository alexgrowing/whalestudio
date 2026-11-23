import Development.EtaleCohomology.EtaleSheaves.CechFiltPf

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC CochainComplex CochainComplex.HomComplex

namespace LateralTheory.E.DiscLvlPf

variable (R : Type) [CommRing R]

def e0 (E : Spc) : ((chains R).obj E).X 0 ≅ (free R).obj (E.obj (op (SimplexCategory.mk 0))) :=
  ((chainsN R).obj E).extendXIso ComplexShape.embeddingDownNat (i := 0) rfl

theorem etale_discrete_chains_degree_zero_iso_free_naturality {E E' : Spc} (g : E ⟶ E') :
    ((chains R).map g).f 0 ≫ (e0 R E').hom = (e0 R E).hom ≫ (free R).map (g.app (op (SimplexCategory.mk 0))) := by
  have : ((chains R).map g).f 0 = (e0 R E).hom ≫ ((chainsN R).map g).f 0 ≫ (e0 R E').inv :=
    HomologicalComplex.extendMap_f (φ := (chainsN R).map g) (e := ComplexShape.embeddingDownNat) (i := 0) (i' := 0) rfl
  rw [this]
  erw [Category.assoc, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rfl

theorem d_zero (P : PSh) : ((chains R).obj (disc.obj P)).d (-1) 0 = 0 := by
  change (HomologicalComplex.extend ((chainsN R).obj (disc.obj P)) ComplexShape.embeddingDownNat).d (-1) 0 = 0
  rw [HomologicalComplex.extend_d_eq (K := (chainsN R).obj (disc.obj P)) (e := ComplexShape.embeddingDownNat) (i' := -1) (j' := 0) (i := 1) (j := 0) rfl rfl]
  have : ((chainsN R).obj (disc.obj P)).d 1 0 = 0 := by
    change (AlgebraicTopology.AlternatingFaceMapComplex.obj (((SimplicialObject.whiskering _ _).obj (free R)).obj (disc.obj P))).d (0 + 1) 0 = 0
    have h01 : (((SimplicialObject.whiskering _ _).obj (free R)).obj (disc.obj P)).δ (0 : Fin 2) =
      (((SimplicialObject.whiskering _ _).obj (free R)).obj (disc.obj P)).δ (1 : Fin 2) := rfl
    rw [AlgebraicTopology.AlternatingFaceMapComplex.obj_d_eq, Fin.sum_univ_two, h01]
    simp only [Fin.val_zero, Fin.val_one, pow_zero, pow_one, one_zsmul, neg_one_zsmul, add_neg_cancel]
  rw [this, zero_comp, comp_zero]

def e0d (P : PSh) : ((chains R).obj (disc.obj P)).X 0 ≅ (free R).obj P := e0 R (disc.obj P)

@[reassoc]
theorem etale_discrete_simplicial_chains_degree_zero_iso_naturality {P Q : PSh} (h : P ⟶ Q) :
    ((chains R).map (disc.map h)).f 0 ≫ (e0d R Q).hom = (e0d R P).hom ≫ (free R).map h :=
  etale_discrete_chains_degree_zero_iso_free_naturality R (disc.map h)

def pr (P : PSh) : (chains R).obj (disc.obj P) ⟶ (HomologicalComplex.single (Shv R) (ComplexShape.up ℤ) 0).obj ((free R).obj P) :=
  HomologicalComplex.mkHomToSingle (e0d R P).hom (fun i hi => by
    have hi' : i = -1 := by simp at hi; omega
    subst hi'
    rw [d_zero, zero_comp])

def sec (P : PSh) : (HomologicalComplex.single (Shv R) (ComplexShape.up ℤ) 0).obj ((free R).obj P) ⟶ (chains R).obj (disc.obj P) :=
  HomologicalComplex.mkHomFromSingle (e0d R P).inv (fun k hk =>
    (LateralTheory.E.CechFiltPf.chains_isZero R (disc.obj P) k (by simp at hk; omega)).eq_of_tgt _ _)

theorem sec_pr (P : PSh) : sec R P ≫ pr R P = 𝟙 _ := by
  ext
  simp [sec, pr]

theorem pr_comm {P Q : PSh} (h : P ⟶ Q) :
    (chains R).map (disc.map h) ≫ pr R Q = pr R P ≫ (HomologicalComplex.single (Shv R) (ComplexShape.up ℤ) 0).map ((free R).map h) := by
  ext
  simp [pr, etale_discrete_simplicial_chains_degree_zero_iso_naturality_assoc, HomologicalComplex.single_map_f_self]

theorem sec_comm {P Q : PSh} (h : P ⟶ Q) :
    (HomologicalComplex.single (Shv R) (ComplexShape.up ℤ) 0).map ((free R).map h) ≫ sec R Q = sec R P ≫ (chains R).map (disc.map h) := by
  apply HomologicalComplex.from_single_hom_ext
  simp only [HomologicalComplex.comp_f, sec, HomologicalComplex.mkHomFromSingle_f, HomologicalComplex.single_map_f_self,
    Category.assoc, Iso.inv_hom_id_assoc]
  congr 1
  rw [Iso.eq_inv_comp, ← etale_discrete_simplicial_chains_degree_zero_iso_naturality_assoc, Iso.hom_inv_id, Category.comp_id]

theorem cone_map_congr {K₁ L₁ K₂ L₂ : Cx R} (φ₁ : K₁ ⟶ L₁) (φ₂ : K₂ ⟶ L₂) {a a' : K₁ ⟶ K₂} {b b' : L₁ ⟶ L₂}
    (c : φ₁ ≫ b = a ≫ φ₂) (c' : φ₁ ≫ b' = a' ≫ φ₂) (ha : a = a') (hb : b = b') :
    mappingCone.map φ₁ φ₂ a b c = mappingCone.map φ₁ φ₂ a' b' c' := by
  subst ha hb; rfl

theorem pull_comp' {K L M : Cx R} (f : K ⟶ L) (g : L ⟶ M) (F : Shv R) (n : ℤ) (x : HK R M F n) :
    HK.pull R (f ≫ g) F n x = HK.pull R f F n (HK.pull R g F n x) := by
  obtain ⟨x, rfl⟩ := x.mk_surjective
  refine congrArg CohomologyClass.mk (Cocycle.ext ?_)
  simp [zcomp, Cochain.ofHom_comp]

theorem pull_id' (K : Cx R) (F : Shv R) (n : ℤ) (x : HK R K F n) : HK.pull R (𝟙 K) F n x = x := by
  obtain ⟨x, rfl⟩ := x.mk_surjective
  refine congrArg CohomologyClass.mk (Cocycle.ext ?_)
  simp [zcomp]

end LateralTheory.E.DiscLvlPf

open LateralTheory.E.DiscLvlPf in
theorem LateralTheory.E.DiscLvlPf.DiscLvl_of : LateralTheory.E.CechFiltPf.DiscLvl := by
  intro R _ F P Q h m hs
  let φ₁ := (chains R).map (disc.map h)
  let φ₂ := (HomologicalComplex.single (Shv R) (ComplexShape.up ℤ) 0).map ((free R).map h)
  let Pm := mappingCone.map φ₁ φ₂ (pr R P) (pr R Q) (pr_comm R h)
  let Sm := mappingCone.map φ₂ φ₁ (sec R P) (sec R Q) (sec_comm R h)
  have hSP : Sm ≫ Pm = 𝟙 _ := by
    rw [← mappingCone.map_comp]
    rw [cone_map_congr R φ₂ φ₂ _ (by rw [Category.id_comp, Category.comp_id]) (sec_pr R P) (sec_pr R Q)]
    exact mappingCone.map_id φ₂
  have : Subsingleton (HK R (mappingCone φ₁) F m) := hs
  refine Function.Injective.subsingleton (f := HK.pull R Pm F m) ?_
  intro x y hxy
  have := congrArg (HK.pull R Sm F m) hxy
  rwa [← pull_comp', ← pull_comp', hSP, pull_id', pull_id'] at this
