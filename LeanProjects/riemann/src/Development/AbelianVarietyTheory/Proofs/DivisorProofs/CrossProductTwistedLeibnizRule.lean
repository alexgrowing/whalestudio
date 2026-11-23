import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CrossTZeroRight
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullAwChainsBijective
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BijectiveTotalOfColumns
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC GlobalTheory.EtC.CupSpec GlobalTheory.EZ GlobalTheory.PBFc

noncomputable section

namespace GlobalTheory.PBFc
variable {R : Type} [CommRing R]
set_option backward.isDefEq.respectTransparency false in
theorem biChains_dh (X : SimplicialObject Spc) (a b : ℕ) :
    (biChainsXIso R X (a + 1) b).inv ≫ ((biChains R X).d (-((a + 1 : ℕ) : ℤ)) (-(a : ℤ))).f (-(b : ℤ)) =
      (∑ i : Fin (a + 2), (-1 : ℤ) ^ (i : ℕ) • (free R).map ((X.δ i).app (op (SimplexCategory.mk b)))) ≫
        (biChainsXIso R X a b).inv := by
  let D := (dblF R).obj ((freeBi R).obj X)
  let M := ((ComplexShape.embeddingDownNat.extendFunctor (Shv R)).mapHomologicalComplex (ComplexShape.down ℕ)).obj D
  have h1 : (biChains R X).d (-((a + 1 : ℕ) : ℤ)) (-(a : ℤ)) =
      (M.extendXIso ComplexShape.embeddingDownNat (i := a + 1) rfl).hom ≫ M.d (a + 1) a ≫
        (M.extendXIso ComplexShape.embeddingDownNat (i := a) rfl).inv :=
    HomologicalComplex.extend_d_eq M ComplexShape.embeddingDownNat rfl rfl
  have h2 : ∀ p : ℕ, (biChainsXIso R X p b).inv =
      @CategoryStruct.comp _ _ _ ((M.X p).X (-(b : ℤ))) _
        ((D.X p).extendXIso ComplexShape.embeddingDownNat (i := b) rfl).inv
        ((M.extendXIso ComplexShape.embeddingDownNat (i := p) rfl).inv.f (-(b : ℤ))) := fun p => rfl
  have h3 : (M.d (a + 1) a).f (-(b : ℤ)) = ((D.X (a+1)).extendXIso ComplexShape.embeddingDownNat (i := b) rfl).hom ≫
      (D.d (a + 1) a).f b ≫ ((D.X a).extendXIso ComplexShape.embeddingDownNat (i := b) rfl).inv :=
    HomologicalComplex.extendMap_f _ ComplexShape.embeddingDownNat (i := b) rfl
  have key : (M.extendXIso ComplexShape.embeddingDownNat (i := a + 1) rfl).inv.f (-(b : ℤ)) ≫
      (M.extendXIso ComplexShape.embeddingDownNat (i := a + 1) rfl).hom.f (-(b : ℤ)) = 𝟙 _ := by
    rw [← HomologicalComplex.comp_f, Iso.inv_hom_id, HomologicalComplex.id_f]
  rw [h1, h2, h2, HomologicalComplex.comp_f, HomologicalComplex.comp_f, Category.assoc, reassoc_of% key, h3,
    Category.assoc, Iso.inv_hom_id_assoc]
  simp only [← Category.assoc]
  congr 2
  rw [show D.d (a + 1) a = ∑ i : Fin (a + 2), (-1 : ℤ) ^ (i : ℕ) •
      (((SimplicialObject.whiskering _ _).obj (AlgebraicTopology.alternatingFaceMapComplex (Shv R))).obj ((freeBi R).obj X)).δ i
    from AlgebraicTopology.alternatingFaceMapComplex_obj_d _ a]
  rw [← HomologicalComplex.eval_map, Functor.map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Functor.map_zsmul]
  rfl

set_option backward.isDefEq.respectTransparency false in
theorem biChains_dv (X : SimplicialObject Spc) (a b : ℕ) :
    (biChainsXIso R X a (b + 1)).inv ≫ ((biChains R X).X (-(a : ℤ))).d (-((b + 1 : ℕ) : ℤ)) (-(b : ℤ)) =
      (∑ j : Fin (b + 2), (-1 : ℤ) ^ (j : ℕ) • (free R).map ((X.obj (op (SimplexCategory.mk a))).δ j)) ≫
        (biChainsXIso R X a b).inv := by
  let D := (dblF R).obj ((freeBi R).obj X)
  let M := ((ComplexShape.embeddingDownNat.extendFunctor (Shv R)).mapHomologicalComplex (ComplexShape.down ℕ)).obj D
  have h2 : ∀ q : ℕ, (biChainsXIso R X a q).inv =
      @CategoryStruct.comp _ _ _ ((M.X a).X (-(q : ℤ))) _
        ((D.X a).extendXIso ComplexShape.embeddingDownNat (i := q) rfl).inv
        ((M.extendXIso ComplexShape.embeddingDownNat (i := a) rfl).inv.f (-(q : ℤ))) := fun q => rfl
  have h3 : (M.X a).d (-((b + 1 : ℕ) : ℤ)) (-(b : ℤ)) =
      ((D.X a).extendXIso ComplexShape.embeddingDownNat (i := b + 1) rfl).hom ≫ (D.X a).d (b + 1) b ≫
        ((D.X a).extendXIso ComplexShape.embeddingDownNat (i := b) rfl).inv :=
    HomologicalComplex.extend_d_eq _ ComplexShape.embeddingDownNat rfl rfl
  have hc : (M.extendXIso ComplexShape.embeddingDownNat (i := a) rfl).inv.f (-((b + 1 : ℕ) : ℤ)) ≫
      ((biChains R X).X (-(a : ℤ))).d (-((b + 1 : ℕ) : ℤ)) (-(b : ℤ)) =
      (M.X a).d (-((b + 1 : ℕ) : ℤ)) (-(b : ℤ)) ≫ (M.extendXIso ComplexShape.embeddingDownNat (i := a) rfl).inv.f (-(b : ℤ)) :=
    HomologicalComplex.Hom.comm _ _ _
  rw [h2, h2, Category.assoc, hc, h3, Category.assoc, Category.assoc,
    Iso.inv_hom_id_assoc]
  simp only [← Category.assoc]
  congr 2
  rw [show (D.X a).d (b + 1) b = ∑ j : Fin (b + 2), (-1 : ℤ) ^ (j : ℕ) • ((freeBi R).obj X |>.obj (op (SimplexCategory.mk a))).δ j
    from AlgebraicTopology.alternatingFaceMapComplex_obj_d _ b]
  rfl

section Faces
variable {X : SimplicialObject Spc}

def BSx.hface {a b : ℕ} {U : Scheme.{0}} (y : BSx X (a + 1) b U) (i : Fin (a + 2)) : BSx X a b U :=
  ((X.δ i).app (op (SimplexCategory.mk b))).app (op U) y

def BSx.vface {a b : ℕ} {U : Scheme.{0}} (y : BSx X a (b + 1) U) (j : Fin (b + 2)) : BSx X a b U :=
  ((X.obj (op (SimplexCategory.mk a))).δ j).app (op U) y

variable {K : Cx R} {k : ℤ}

def evD (γ : Cochain (totChains R X) K k) (t : ℤ) (a b : ℕ) (U : Scheme.{0}) (y : BSx X a b U) : Sec (K.X t) U :=
  if h : -((a + b : ℕ) : ℤ) + k = t then evT γ a b t h U y else 0

theorem evD_eq (γ : Cochain (totChains R X) K k) (t : ℤ) (a b : ℕ) (h : -((a + b : ℕ) : ℤ) + k = t) (U : Scheme.{0})
    (y : BSx X a b U) : evD γ t a b U y = evT γ a b t h U y := dif_pos h

def hB (γ : Cochain (totChains R X) K k) (t : ℤ) : ∀ (a b : ℕ) (U : Scheme.{0}), BSx X a b U → Sec (K.X t) U
  | 0, _, _, _ => 0
  | a + 1, b, U, y => ∑ i : Fin (a + 2), (-1 : ℤ) ^ (i : ℕ) • evD γ t a b U (y.hface i)

def vB (γ : Cochain (totChains R X) K k) (t : ℤ) : ∀ (a b : ℕ) (U : Scheme.{0}), BSx X a b U → Sec (K.X t) U
  | _, 0, _, _ => 0
  | a, b + 1, U, y => ∑ j : Fin (b + 2), (-1 : ℤ) ^ (j : ℕ) • evD γ t a b U (y.vface j)

end Faces

theorem ιTotal_v_congr {X : SimplicialObject Spc} {K : Cx R} {k : ℤ} (γ : Cochain (totChains R X) K k) (i₁ i₂ p p' t : ℤ)
    (hp : p = p') (h : ComplexShape.π (ComplexShape.up ℤ) (ComplexShape.up ℤ) (ComplexShape.up ℤ) ⟨i₁, i₂⟩ = p)
    (h' : ComplexShape.π (ComplexShape.up ℤ) (ComplexShape.up ℤ) (ComplexShape.up ℤ) ⟨i₁, i₂⟩ = p')
    (hv : p + k = t) (hv' : p' + k = t) :
    (biChains R X).ιTotal (ComplexShape.up ℤ) i₁ i₂ p h ≫ γ.v p t hv =
      (biChains R X).ιTotal (ComplexShape.up ℤ) i₁ i₂ p' h' ≫ γ.v p' t hv' := by
  subst hp
  rfl

theorem evT_dh {X : SimplicialObject Spc} {K : Cx R} {k : ℤ} (γ : Cochain (totChains R X) K k) (a b : ℕ) (p t : ℤ)
    (hp : -((a + b : ℕ) : ℤ) + 1 = p) (hv : p + k = t) (U : Scheme.{0}) (y : BSx X a b U) :
    Sec.map ((biChainsXIso R X a b).inv ≫ (biChains R X).d₁ (ComplexShape.up ℤ) (-(a : ℤ)) (-(b : ℤ)) p ≫ γ.v p t hv)
      (freeGen R _ U y) = hB γ t a b U y := by
  cases a with
  | zero =>
    rw [HomologicalComplex₂.d₁_eq _ _ (show (ComplexShape.up ℤ).Rel (-((0 : ℕ) : ℤ)) 1 from by simp) (-(b : ℤ)) p
      (by simp only [ComplexShape.π_def]; omega),
      (biChains_isZero X 1 (-(b : ℤ)) (Or.inl one_pos)).eq_of_tgt (HomologicalComplex.Hom.f _ _) 0]
    simp only [zero_comp, smul_zero, comp_zero]
    exact map_zero (mapHom _ _ (freeGen R _ U y))
  | succ a =>
    rw [HomologicalComplex₂.d₁_eq _ _ (show (ComplexShape.up ℤ).Rel (-((a + 1 : ℕ) : ℤ)) (-(a : ℤ)) from by simp <;> omega)
      (-(b : ℤ)) p (by simp only [ComplexShape.π_def]; omega)]
    show _ = ∑ i : Fin (a + 2), (-1 : ℤ) ^ (i : ℕ) • evD γ t a b U (y.hface i)
    rw [show (ComplexShape.up ℤ).ε₁ (ComplexShape.up ℤ) (ComplexShape.up ℤ) (-((a + 1 : ℕ) : ℤ), -(b : ℤ)) = 1 from rfl,
      one_smul, Category.assoc, ← Category.assoc _ (HomologicalComplex.Hom.f _ _), biChains_dh, Category.assoc,
      Preadditive.sum_comp]
    refine (map_sum (mapHom _ (K.X t) (freeGen R _ U y)) _ _).trans (Finset.sum_congr rfl fun i _ => ?_)
    rw [Preadditive.zsmul_comp, map_zsmul]
    congr 1
    change Sec.map (_ ≫ _ ≫ γ.v p t hv) (Sec.map ((free R).map _) (freeGen R _ U y)) = _
    rw [freeGen_map, evD_eq γ t a b (by omega)]
    unfold evT
    rw [ιTotal_v_congr γ _ _ p (-((a + b : ℕ) : ℤ)) t (by omega) _ (by simp only [ComplexShape.π_def]; omega) hv]
    rfl

theorem evT_dv {X : SimplicialObject Spc} {K : Cx R} {k : ℤ} (γ : Cochain (totChains R X) K k) (a b : ℕ) (p t : ℤ)
    (hp : -((a + b : ℕ) : ℤ) + 1 = p) (hv : p + k = t) (U : Scheme.{0}) (y : BSx X a b U) :
    Sec.map ((biChainsXIso R X a b).inv ≫ (biChains R X).d₂ (ComplexShape.up ℤ) (-(a : ℤ)) (-(b : ℤ)) p ≫ γ.v p t hv)
      (freeGen R _ U y) = (a : ℤ).negOnePow • vB γ t a b U y := by
  cases b with
  | zero =>
    rw [HomologicalComplex₂.d₂_eq _ _ _ (show (ComplexShape.up ℤ).Rel (-((0 : ℕ) : ℤ)) 1 from by simp) p
      (by simp only [ComplexShape.π_def]; omega),
      (biChains_isZero X (-(a : ℤ)) 1 (Or.inr one_pos)).eq_of_tgt (HomologicalComplex.d _ _ _) 0]
    simp only [zero_comp, smul_zero, comp_zero]
    exact (map_zero (mapHom _ _ (freeGen R _ U y))).trans (smul_zero _).symm
  | succ b =>
    show _ = (a : ℤ).negOnePow • ∑ j : Fin (b + 2), (-1 : ℤ) ^ (j : ℕ) • evD γ t a b U (y.vface j)
    rw [HomologicalComplex₂.d₂_eq _ _ _ (show (ComplexShape.up ℤ).Rel (-((b + 1 : ℕ) : ℤ)) (-(b : ℤ)) from by simp <;> omega)
      p (by simp only [ComplexShape.π_def]; omega),
      show (ComplexShape.up ℤ).ε₂ (ComplexShape.up ℤ) (ComplexShape.up ℤ) (-(a : ℤ), -((b + 1 : ℕ) : ℤ)) = (a : ℤ).negOnePow
        by simp,
      Units.smul_def, Preadditive.zsmul_comp, Preadditive.comp_zsmul]
    refine (map_zsmul (mapHom _ (K.X t) (freeGen R _ U y)) _ _).trans ?_
    rw [Units.smul_def]
    congr 1
    rw [Category.assoc, ← Category.assoc _ (HomologicalComplex.d _ _ _), biChains_dv, Category.assoc, Preadditive.sum_comp]
    refine (map_sum (mapHom _ (K.X t) (freeGen R _ U y)) _ _).trans (Finset.sum_congr rfl fun j _ => ?_)
    rw [Preadditive.zsmul_comp, map_zsmul]
    congr 1
    change Sec.map (_ ≫ _ ≫ γ.v p t hv) (Sec.map ((free R).map _) (freeGen R _ U y)) = _
    rw [freeGen_map, evD_eq γ t a b (by omega)]
    unfold evT
    rw [ιTotal_v_congr γ _ _ p (-((a + b : ℕ) : ℤ)) t (by omega) _ (by simp only [ComplexShape.π_def]; omega) hv]
    rfl

theorem evT_δ {X : SimplicialObject Spc} {K : Cx R} {k k' : ℤ} (hk : k + 1 = k') (γ : Cochain (totChains R X) K k)
    (a b : ℕ) (s t : ℤ) (hs : -((a + b : ℕ) : ℤ) + k = s) (ht : -((a + b : ℕ) : ℤ) + k' = t) (U : Scheme.{0})
    (y : BSx X a b U) :
    evT (δ k k' γ) a b t ht U y = Sec.map (K.d s t) (evT γ a b s hs U y) +
      k'.negOnePow • (hB γ t a b U y + (a : ℤ).negOnePow • vB γ t a b U y) := by
  rw [evT, δ_v k k' hk γ _ t ht s (-((a + b : ℕ) : ℤ) + 1) (by omega) rfl, Preadditive.comp_add, Preadditive.comp_add]
  refine (map_add (mapHom _ (K.X t) (freeGen R _ U y)) _ _).trans (congrArg₂ (· + ·) ?_ ?_)
  · simp only [← Category.assoc]
    rfl
  · rw [Units.smul_def, Preadditive.comp_zsmul, Preadditive.comp_zsmul]
    refine (map_zsmul (mapHom _ (K.X t) (freeGen R _ U y)) _ _).trans ?_
    rw [Units.smul_def]
    congr 1
    rw [HomologicalComplex₂.total_d, Preadditive.add_comp, Preadditive.comp_add, ← Category.assoc, HomologicalComplex₂.ι_D₁,
      HomologicalComplex₂.ι_D₂_assoc, Preadditive.comp_add]
    refine (map_add (mapHom _ (K.X t) (freeGen R _ U y)) _ _).trans (congrArg₂ (· + ·) ?_ ?_)
    · exact evT_dh γ a b _ t rfl _ U y
    · exact evT_dv γ a b _ t rfl _ U y

section Cross2
variable {E : Spc} {N : ℕ} (V : E ⟶ ofCat (glCat N)) {B : Spc} (ℓ : twX E V ⟶ (Functor.const SimplexCategoryᵒᵖ).obj B)

theorem vertS_hface {a b : ℕ} {U : Scheme.{0}} (y : BSx (twX E V) (a + 1) b U) (i : Fin (a + 2)) :
    vertS V ℓ (y.hface i) = vertS V ℓ y := by
  have h := ℓ.naturality (SimplexCategory.δ i).op
  exact ConcreteCategory.congr_hom (NatTrans.congr_app (NatTrans.congr_app h (op (SimplexCategory.mk b))) (op U)) y

theorem vertS_vface {a b : ℕ} {U : Scheme.{0}} (y : BSx (twX E V) a (b + 1) U) (j : Fin (b + 2)) :
    vertS V ℓ (y.vface j) = (vertS V ℓ y).face j :=
  ConcreteCategory.congr_hom (NatTrans.congr_app ((ℓ.app (op (SimplexCategory.mk a))).naturality
    (SimplexCategory.δ j).op) (op U)) y

end Cross2

section Two
variable {E B : Spc} {U : Scheme.{0}} {I J K : Cx R} (μ : Pair I J K) {n m : ℤ}

def bisimplexFunctionBoundaryFirst {A : Type*} [AddCommGroup A] (φ : ∀ p r : ℕ, Sx E p U → Sx B r U → A) : ∀ p r : ℕ, Sx E p U → Sx B r U → A
  | 0, _, _, _ => 0
  | p + 1, r, x, v => ∑ i : Fin (p + 2), (-1 : ℤ) ^ (i : ℕ) • φ p r (x.face i) v

def bisimplexFunctionBoundarySecond {A : Type*} [AddCommGroup A] (φ : ∀ p r : ℕ, Sx E p U → Sx B r U → A) : ∀ p r : ℕ, Sx E p U → Sx B r U → A
  | _, 0, _, _ => 0
  | p, r + 1, x, v => ∑ j : Fin (r + 2), (-1 : ℤ) ^ (j : ℕ) • φ p r x (v.face j)

def xv (α : Cochain ((chains R).obj E) I n) (z : Cochain ((chains R).obj B) J m) (w : ℤ) (p r : ℕ) (x : Sx E p U)
    (v : Sx B r U) : Sec (K.X w) U :=
  if h : (-(p : ℤ) + n) + (-(r : ℤ) + m) = w then μ.mul U _ _ w h (ev α p _ rfl U x) (ev z r _ rfl U v) else 0

theorem xv_eq (α : Cochain ((chains R).obj E) I n) (z : Cochain ((chains R).obj B) J m) (w : ℤ) (p r : ℕ) (x : Sx E p U)
    (v : Sx B r U) (s t : ℤ) (hs : -(p : ℤ) + n = s) (ht : -(r : ℤ) + m = t) (h : s + t = w) :
    xv μ α z w p r x v = μ.mul U s t w h (ev α p s hs U x) (ev z r t ht U v) := by
  subst hs ht
  exact dif_pos h

theorem xv_δ_left {n₁ : ℤ} (hn : n + 1 = n₁) (α : Cochain ((chains R).obj E) I n) (z : Cochain ((chains R).obj B) J m)
    (w : ℤ) (p r : ℕ) (x : Sx E p U) (v : Sx B r U) (s s' t : ℤ) (hs : -(p : ℤ) + n = s) (hs' : s + 1 = s')
    (ht : -(r : ℤ) + m = t) (h : s' + t = w) :
    μ.mul U s' t w h (Sec.map (I.d s s') (ev α p s hs U x)) (ev z r t ht U v) =
      xv μ (δ n n₁ α) z w p r x v - sg n₁ • bisimplexFunctionBoundaryFirst (xv μ α z w) p r x v := by
  rw [xv_eq μ _ z w p r x v s' t (by omega) ht h]
  cases p with
  | zero => rw [ev_δ_zero hn α U s s' hs, bisimplexFunctionBoundaryFirst, smul_zero, sub_zero]
  | succ p =>
    rw [ev_δ_succ hn α U p s s' hs, bisimplexFunctionBoundaryFirst, map_add, LinearMap.add_apply, sg_smul, map_zsmul, LinearMap.smul_apply, map_sum,
      LinearMap.sum_apply, eq_sub_iff_add_eq]
    refine congrArg₂ (· + ·) rfl (congrArg _ (Finset.sum_congr rfl fun i _ => ?_))
    rw [map_zsmul, LinearMap.smul_apply, xv_eq μ α z w p r _ v s' t (by omega) ht h]

theorem xv_δ_right {m₁ : ℤ} (hm : m + 1 = m₁) (α : Cochain ((chains R).obj E) I n) (z : Cochain ((chains R).obj B) J m)
    (w : ℤ) (p r : ℕ) (x : Sx E p U) (v : Sx B r U) (s t t' : ℤ) (hs : -(p : ℤ) + n = s)
    (ht : -(r : ℤ) + m = t) (ht' : t + 1 = t') (h : s + t' = w) :
    μ.mul U s t' w h (ev α p s hs U x) (Sec.map (J.d t t') (ev z r t ht U v)) =
      xv μ α (δ m m₁ z) w p r x v - sg m₁ • bisimplexFunctionBoundarySecond (xv μ α z w) p r x v := by
  rw [xv_eq μ α _ w p r x v s t' hs (by omega) h]
  cases r with
  | zero => rw [ev_δ_zero hm z U t t' ht, bisimplexFunctionBoundarySecond, smul_zero, sub_zero]
  | succ r =>
    rw [ev_δ_succ hm z U r t t' ht, bisimplexFunctionBoundarySecond, map_add, sg_smul, map_zsmul, map_sum, eq_sub_iff_add_eq]
    refine congrArg₂ (· + ·) rfl (congrArg _ (Finset.sum_congr rfl fun i _ => ?_))
    rw [map_zsmul, xv_eq μ α z w p r x _ s t' hs (by omega) h]

theorem d_xv {n₁ m₁ : ℤ} (hn : n + 1 = n₁) (hm : m + 1 = m₁) (α : Cochain ((chains R).obj E) I n)
    (z : Cochain ((chains R).obj B) J m) (w w' : ℤ) (hw : w + 1 = w') (p r : ℕ) (x : Sx E p U) (v : Sx B r U)
    (h : (-(p : ℤ) + n) + (-(r : ℤ) + m) = w) :
    Sec.map (K.d w w') (xv μ α z w p r x v) =
      (xv μ (δ n n₁ α) z w' p r x v - sg n₁ • bisimplexFunctionBoundaryFirst (xv μ α z w') p r x v) +
        sg (-(p : ℤ) + n) • (xv μ α (δ m m₁ z) w' p r x v - sg m₁ • bisimplexFunctionBoundarySecond (xv μ α z w') p r x v) := by
  subst hw
  rw [xv_eq μ α z w p r x v _ _ rfl rfl h, μ.leibniz, xv_δ_left μ hn α z _ p r x v _ _ _ rfl rfl rfl,
    xv_δ_right μ hm α z _ p r x v _ _ _ rfl rfl rfl, sg_smul]

end Two

theorem evT_usmul {X : SimplicialObject Spc} {L : Cx R} {t : ℤ} (c : ℤˣ) (γ : Cochain (totChains R X) L t) (a b : ℕ) (s : ℤ)
    (h : -((a + b : ℕ) : ℤ) + t = s) (U : Scheme.{0}) (y : BSx X a b U) :
    evT (c • γ) a b s h U y = c • evT γ a b s h U y := by
  unfold evT
  rw [Units.smul_def, Units.smul_def, Cochain.smul_v, Preadditive.comp_zsmul, Preadditive.comp_zsmul]
  exact map_zsmul (mapHom _ _ (freeGen R _ U y)) _ _

section Cross3
variable {E : Spc} {N : ℕ} (V : E ⟶ ofCat (glCat N)) {B : Spc} (ℓ : twX E V ⟶ (Functor.const SimplexCategoryᵒᵖ).obj B)
  {I J K : Cx R} (μ : Pair I J K) {n m k : ℤ} (hk : n + m = k) (α : Cochain ((chains R).obj E) I n)
  (z : Cochain ((chains R).obj B) J m)

theorem evT_crossT_xv (a b : ℕ) (w : ℤ) (h : -((a + b : ℕ) : ℤ) + k = w) (U : Scheme.{0}) (y : BSx (twX E V) a b U) :
    evT (crossT V ℓ μ hk α z) a b w h U y = sg (m * a) • xv μ α z w a b (baseS V y) (vertS V ℓ y) := by
  rw [evT_crossT, xv_eq μ α z w a b _ _ _ _ rfl rfl (by push_cast at h; omega), sg_smul]

theorem evD_crossT (w : ℤ) (a b : ℕ) (U : Scheme.{0}) (y : BSx (twX E V) a b U) :
    evD (crossT V ℓ μ hk α z) w a b U y = sg (m * a) • xv μ α z w a b (baseS V y) (vertS V ℓ y) := by
  by_cases h : -((a + b : ℕ) : ℤ) + k = w
  · rw [evD_eq _ _ _ _ h, evT_crossT_xv]
  · rw [evD, dif_neg h, xv, dif_neg (by push_cast at h; omega), smul_zero]

theorem hB_crossT (w : ℤ) (a b : ℕ) (U : Scheme.{0}) (y : BSx (twX E V) a b U) :
    hB (crossT V ℓ μ hk α z) w a b U y = sg (m * a + m) • bisimplexFunctionBoundaryFirst (xv μ α z w) a b (baseS V y) (vertS V ℓ y) := by
  cases a with
  | zero => rw [hB, bisimplexFunctionBoundaryFirst, smul_zero]
  | succ a =>
    rw [hB, bisimplexFunctionBoundaryFirst, Finset.smul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [evD_crossT, vertS_hface, smul_comm]
    congr 1
    rw [show m * ((a + 1 : ℕ) : ℤ) + m = m * a + (m + m) by push_cast; ring, sg_add, sg_add, sg_sq, mul_one]

theorem vB_crossT (w : ℤ) (a b : ℕ) (U : Scheme.{0}) (y : BSx (twX E V) a b U) :
    vB (crossT V ℓ μ hk α z) w a b U y = sg (m * a) • bisimplexFunctionBoundarySecond (xv μ α z w) a b (baseS V y) (vertS V ℓ y) := by
  cases b with
  | zero => rw [vB, bisimplexFunctionBoundarySecond, smul_zero]
  | succ b =>
    rw [vB, bisimplexFunctionBoundarySecond, Finset.smul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [evD_crossT, vertS_vface, smul_comm]
    rfl

end Cross3

theorem crossT_leibniz {E : Spc} {N : ℕ} (V : E ⟶ ofCat (glCat N)) {B : Spc}
    (ℓ : twX E V ⟶ (Functor.const SimplexCategoryᵒᵖ).obj B) {I J K : Cx R} (μ : Pair I J K) {n m k n' m' k' : ℤ}
    (hk : n + m = k) (hn : n + 1 = n') (hm : m + 1 = m') (hk' : k + 1 = k') (hk₁ : n' + m = k') (hk₂ : n + m' = k')
    (α : Cochain ((chains R).obj E) I n) (z : Cochain ((chains R).obj B) J m) :
    δ k k' (crossT V ℓ μ hk α z) = crossT V ℓ μ hk₁ (δ n n' α) z + n.negOnePow • crossT V ℓ μ hk₂ α (δ m m' z) := by
  refine evT_ext _ _ fun a b t ht U y => ?_
  rw [evT_add, evT_usmul, evT_δ hk' _ a b (-((a + b : ℕ) : ℤ) + k) t rfl ht U y, evT_crossT_xv, evT_crossT_xv,
    evT_crossT_xv, hB_crossT, vB_crossT]
  have hd := d_xv μ hn hm α z (-((a + b : ℕ) : ℤ) + k) t (by omega) a b (baseS V y) (vertS V ℓ y) (by push_cast; omega)
  rw [Sec.map] at hd
  rw [Sec.map, map_zsmul, hd]
  clear hd
  subst hn hm hk hk'
  have e1 : sg ((m + 1) * (a : ℤ)) = sg (m * a) * sg a := by rw [add_mul, one_mul, sg_add]
  rw [e1]
  simp only [sg_smul, sg_add, sg_neg, sg_one]
  have q1 := sg_sq m
  have q2 := sg_sq n
  have q3 := sg_sq (a : ℤ)
  have q4 := sg_sq (m * (a : ℤ))
  generalize sg m = σm at *
  generalize sg n = σn at *
  generalize sg (a : ℤ) = σa at *
  generalize sg (m * (a : ℤ)) = σ at *
  match_scalars <;> first | ring1 | linear_combination (-(σ * σn)) * q1 | linear_combination (σ * σn) * q1

end GlobalTheory.PBFc

end
