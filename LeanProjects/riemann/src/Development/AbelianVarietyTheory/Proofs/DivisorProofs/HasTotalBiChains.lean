import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpanRangeMulVecLe

noncomputable section
open CategoryTheory Limits Opposite AlgebraicTopology

namespace GlobalTheory.EZ

abbrev BOp : Type := Free ℤ (SimplexCategoryᵒᵖ × SimplexCategoryᵒᵖ)

def bo (n m : ℕ) : BOp := Free.of ℤ (op (SimplexCategory.mk n), op (SimplexCategory.mk m))

def bop {n m p q : ℕ} (α : SimplexCategory.mk p ⟶ SimplexCategory.mk n)
    (β : SimplexCategory.mk q ⟶ SimplexCategory.mk m) : bo n m ⟶ bo p q :=
  Finsupp.single (show (op (SimplexCategory.mk n), op (SimplexCategory.mk m)) ⟶
    (op (SimplexCategory.mk p), op (SimplexCategory.mk q)) from (α.op, β.op)) 1

def clampHom (n m : ℕ) (f : ℕ → ℕ) (hf : Monotone f) : SimplexCategory.mk m ⟶ SimplexCategory.mk n :=
  SimplexCategory.mkHom ⟨fun j => ⟨min n (f j), Nat.lt_succ_of_le (min_le_left _ _)⟩,
    fun i j h => by
      change min n (f i) ≤ min n (f j)
      exact min_le_min_left n (hf (show (i : ℕ) ≤ j from h))⟩

def faceFun (i : ℕ) (j : ℕ) : ℕ := if j < i then j else j + 1

theorem faceFun_mono (i : ℕ) : Monotone (faceFun i) := by
  intro a b h
  unfold faceFun
  split_ifs <;> omega

def fc (n m i : ℕ) : SimplexCategory.mk m ⟶ SimplexCategory.mk n := clampHom n m (faceFun i) (faceFun_mono i)

def idc (n m : ℕ) : SimplexCategory.mk m ⟶ SimplexCategory.mk n := clampHom n m id monotone_id

def backc (n a b : ℕ) : SimplexCategory.mk b ⟶ SimplexCategory.mk n :=
  clampHom n b (a + ·) (fun _ _ h => Nat.add_le_add_left h a)

def dH (a b a' b' : ℕ) : bo a b ⟶ bo a' b' :=
  if a = a' + 1 ∧ b = b' then ∑ i ∈ Finset.range (a + 1), ((-1 : ℤ) ^ i) • bop (fc a a' i) (idc b b') else 0

def dV (a b a' b' : ℕ) : bo a b ⟶ bo a' b' :=
  if a = a' ∧ b = b' + 1 then ∑ j ∈ Finset.range (b + 1), ((-1 : ℤ) ^ j) • bop (idc a a') (fc b b' j) else 0

def dT (a b a' b' : ℕ) : bo a b ⟶ bo a' b' := dH a b a' b' + ((-1 : ℤ) ^ a) • dV a b a' b'

def dD (n m : ℕ) : bo n n ⟶ bo m m :=
  if n = m + 1 then ∑ i ∈ Finset.range (n + 1), ((-1 : ℤ) ^ i) • bop (fc n m i) (fc n m i) else 0

def awO (n a b : ℕ) : bo n n ⟶ bo a b := if a + b = n then bop (idc n a) (backc n a b) else 0

def idO (a b a' b' : ℕ) : bo a b ⟶ bo a' b' := if a = a' ∧ b = b' then bop (idc a a') (idc b b') else 0

section Ev

variable {C : Type*} [Category* C] [Preadditive C]

set_option backward.isDefEq.respectTransparency false in

def ev (Y : SimplicialObject (SimplicialObject C)) : BOp ⥤ C where
  obj X := (Functor.uncurry.obj Y).obj X
  map {_ _} f := f.sum fun f' (r : ℤ) => r • (Functor.uncurry.obj Y).map f'
  map_id := by
    dsimp +instances [CategoryTheory.categoryFree]
    simp
  map_comp {X Y' Z} f g := by
    induction f using Finsupp.induction_linear with
    | zero => simp
    | add f₁ f₂ w₁ w₂ =>
      rw [Preadditive.add_comp]
      rw [Finsupp.sum_add_index', Finsupp.sum_add_index']
      · simp only [w₁, w₂, Preadditive.add_comp]
      · intros; rw [zero_smul]
      · intros; simp only [add_smul]
      · intros; rw [zero_smul]
      · intros; simp only [add_smul]
    | single f' r =>
      induction g using Finsupp.induction_linear with
      | zero => simp
      | add f₁ f₂ w₁ w₂ =>
        rw [Preadditive.comp_add]
        rw [Finsupp.sum_add_index', Finsupp.sum_add_index']
        · simp only [w₁, w₂, Preadditive.comp_add]
        · intros; rw [zero_smul]
        · intros; simp only [add_smul]
        · intros; rw [zero_smul]
        · intros; simp only [add_smul]
      | single g' s =>
        rw [Free.single_comp_single _ _ f' g' r s]
        simp only [Finsupp.sum_single_index, zero_smul, Functor.map_comp, Preadditive.zsmul_comp,
          Preadditive.comp_zsmul, smul_smul, mul_comm]

set_option backward.isDefEq.respectTransparency false in
theorem ev_map_bop (Y : SimplicialObject (SimplicialObject C)) {n m p q : ℕ}
    (α : SimplexCategory.mk p ⟶ SimplexCategory.mk n) (β : SimplexCategory.mk q ⟶ SimplexCategory.mk m) :
    (ev Y).map (bop α β) =
      (Y.map α.op).app (op (SimplexCategory.mk m)) ≫ (Y.obj (op (SimplexCategory.mk p))).map β.op := by
  simp [ev, bop]
  rfl

set_option backward.isDefEq.respectTransparency false in
instance (Y : SimplicialObject (SimplicialObject C)) : (ev Y).Additive where
  map_add {X Z f g} := by
    dsimp [ev]
    rw [Finsupp.sum_add_index'] <;> simp [add_smul]

end Ev

section Cx

variable {C : Type*} [Category* C] [Preadditive C]

def diag : SimplicialObject (SimplicialObject C) ⥤ SimplicialObject C :=
  Functor.uncurry ⋙ (Functor.whiskeringLeft _ _ C).obj (Functor.diag SimplexCategoryᵒᵖ)

def diagCx (Y : SimplicialObject (SimplicialObject C)) : ChainComplex C ℕ :=
  (alternatingFaceMapComplex C).obj (diag.obj Y)

def dbl (Y : SimplicialObject (SimplicialObject C)) :
    HomologicalComplex₂ C (ComplexShape.down ℕ) (ComplexShape.down ℕ) :=
  (alternatingFaceMapComplex (ChainComplex C ℕ)).obj
    (((SimplicialObject.whiskering _ _).obj (alternatingFaceMapComplex C)).obj Y)

variable [HasFiniteCoproducts C]

instance hasTotal_down (K : HomologicalComplex₂ C (ComplexShape.down ℕ) (ComplexShape.down ℕ)) :
    K.HasTotal (ComplexShape.down ℕ) := fun n => by
  haveI : Finite ((ComplexShape.π (ComplexShape.down ℕ) (ComplexShape.down ℕ) (ComplexShape.down ℕ)) ⁻¹' {n}) := by
    refine Set.Finite.to_subtype ((Set.finite_Iic n).prod (Set.finite_Iic n) |>.subset ?_)
    rintro ⟨a, b⟩ h
    simp only [Set.mem_preimage, Set.mem_singleton_iff, ComplexShape.π_def] at h
    simp only [Set.mem_prod, Set.mem_Iic]
    omega
  infer_instance

def tot (Y : SimplicialObject (SimplicialObject C)) : ChainComplex C ℕ := (dbl Y).total (ComplexShape.down ℕ)

def awF (Y : SimplicialObject (SimplicialObject C)) (n : ℕ) : (diagCx Y).X n ⟶ (tot Y).X n :=
  ∑ a : Fin (n + 1), (ev Y).map (awO n a (n - a)) ≫
    (dbl Y).ιTotal (ComplexShape.down ℕ) a (n - a) n (by simp only [ComplexShape.π_def] ; omega)

end Cx

section Sheaves

open GlobalTheory.EtC

variable (R : Type) [CommRing R]

def freeBi : SimplicialObject Spc ⥤ SimplicialObject (SimplicialObject (Shv R)) :=
  (SimplicialObject.whiskering _ _).obj ((SimplicialObject.whiskering _ _).obj (free R))

def dblF : SimplicialObject (SimplicialObject (Shv R)) ⥤
    HomologicalComplex₂ (Shv R) (ComplexShape.down ℕ) (ComplexShape.down ℕ) :=
  (SimplicialObject.whiskering _ _).obj (alternatingFaceMapComplex (Shv R)) ⋙
    alternatingFaceMapComplex (ChainComplex (Shv R) ℕ)

def biChainsF : SimplicialObject Spc ⥤ HomologicalComplex₂ (Shv R) (ComplexShape.up ℤ) (ComplexShape.up ℤ) :=
  freeBi R ⋙ dblF R ⋙
    (ComplexShape.embeddingDownNat.extendFunctor (Shv R)).mapHomologicalComplex (ComplexShape.down ℕ) ⋙
    ComplexShape.embeddingDownNat.extendFunctor (CochainComplex (Shv R) ℤ)

abbrev biChains (X : SimplicialObject Spc) : HomologicalComplex₂ (Shv R) (ComplexShape.up ℤ) (ComplexShape.up ℤ) :=
  (biChainsF R).obj X

instance hasTotal_biChains (X : SimplicialObject Spc) : (biChains R X).HasTotal (ComplexShape.up ℤ) := fun _ => by
  haveI : HasColimitsOfSize.{0, 0} (ModuleCat.{1} (ULift.{1} R)) := inferInstance
  haveI : HasColimitsOfSize.{0, 0} (Shv R) := inferInstanceAs (HasColimitsOfSize.{0, 0} (Sheaf _ _))
  haveI h := this
  exact @HasColimitsOfShape.has_colimit _ _ _ _ (HasColimitsOfSize.has_colimits_of_shape _) _

abbrev totChains (X : SimplicialObject Spc) : Cx R := (biChains R X).total (ComplexShape.up ℤ)

def biChainsXIso (X : SimplicialObject Spc) (a b : ℕ) :
    ((biChains R X).X (-(a : ℤ))).X (-(b : ℤ)) ≅
      (free R).obj ((X.obj (op (SimplexCategory.mk a))).obj (op (SimplexCategory.mk b))) :=
  (HomologicalComplex.eval _ _ (-(b : ℤ))).mapIso
      (HomologicalComplex.extendXIso _ ComplexShape.embeddingDownNat (i := a) rfl) ≪≫
    HomologicalComplex.extendXIso _ ComplexShape.embeddingDownNat (i := b) rfl

def awP (X : SimplicialObject Spc) (n a b : ℕ) :
    (bidiag.obj X).obj (op (SimplexCategory.mk n)) ⟶ (X.obj (op (SimplexCategory.mk a))).obj (op (SimplexCategory.mk b)) :=
  (X.map (idc n a).op).app (op (SimplexCategory.mk n)) ≫ (X.obj (op (SimplexCategory.mk a))).map (backc n a b).op

def awZ (X : SimplicialObject Spc) (n : ℕ) :
    ((chains R).obj (bidiag.obj X)).X (-(n : ℤ)) ⟶ (totChains R X).X (-(n : ℤ)) :=
  (chainsXIso R (bidiag.obj X) n).hom ≫
    ∑ a : Fin (n + 1), (free R).map (awP X n a (n - a)) ≫ (biChainsXIso R X a (n - a)).inv ≫
      (biChains R X).ιTotal (ComplexShape.up ℤ) (-(a : ℤ)) (-((n - a : ℕ) : ℤ)) (-(n : ℤ))
        (by simp only [ComplexShape.π_def]; omega)

end Sheaves

end GlobalTheory.EZ
