import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PairTAdjTLeft
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HodgeTateKernelAtPoint
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqZeroOfForallDual

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.EigenSplit GlobalTheory.CompHt GlobalTheory.CM GlobalTheory.TorusTateLie
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PointMap

section General

variable {p : ℕ} [Fact p.Prime] {C : Type} [Field C] {v : Valuation C ℝ≥0} {O : Type} [CommRing O]
  [Algebra O C] {Λ : Type} [CommRing Λ] [StarRing Λ] {P P' : Point p v O Λ}
  (α : P.A.A ⟶ P'.A.A) [IsMonHom α]

theorem mapT_actT (h : ∀ a, P.oA.act a ≫ α = α ≫ P'.oA.act a) (a : Λ) (t : P.T) :
    mapT P P' α (P.actT a t) = P'.actT a (mapT P P' α t) := Tate.ext fun n => by
  change (t.lev n ≫ P.oA.act a) ≫ α = (t.lev n ≫ α) ≫ P'.oA.act a
  rw [Category.assoc, Category.assoc, h]

section Lattices

variable [Algebra ℤ_[p] C]

theorem isEquivariant_mapV (h : ∀ a, P.oA.act a ≫ α = α ≫ P'.oA.act a) :
    IsEquivariant P.actV P'.actV (mapV P P' α) := fun a x => by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul c t => exact congrArg (c ⊗ₜ ·) (mapT_actT α h a t)

theorem mapV_mem_eigV (h : ∀ a, P.oA.act a ≫ α = α ≫ P'.oA.act a) (τ : Λ →+* O) {x : P.V}
    (hx : x ∈ P.eigV τ) : mapV P P' α x ∈ P'.eigV τ :=
  mem_eigenSub.2 fun b => by rw [← isEquivariant_mapV α h, mem_eigenSub.1 hx b, map_smul]

variable [Algebra ℤ_[p] O] [IsScalarTower ℤ_[p] O C]

theorem mapV_mem_latT {x : P.V} (hx : x ∈ P.latT) : mapV P P' α x ∈ P'.latT := by
  obtain ⟨x, rfl⟩ := hx
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add a b ha hb => rw [map_add, map_add]; exact Submodule.add_mem _ ha hb
  | tmul c t => exact ⟨c ⊗ₜ mapT P P' α t, by rw [Point.inclT_tmul, Point.inclT_tmul]; rfl⟩

theorem mapV_mem_latTSub (h : ∀ a, P.oA.act a ≫ α = α ≫ P'.oA.act a) (τ : Λ →+* O) {x : P.V}
    (hx : x ∈ P.latTSub τ) : mapV P P' α x ∈ P'.latTSub τ :=
  ⟨mapV_mem_latT α hx.1, mapV_mem_eigV α h τ hx.2⟩

end Lattices

variable [IsAlgClosed C] [CharZero C]

theorem pairV_mapV [Algebra ℤ_[p] C] (x : P.V) (y : P'.V) :
    P'.pairV (mapV P P' α x) y = P.pairV x (adjV P P' α y) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x x' hx hx' => simp only [map_add, LinearMap.add_apply, hx, hx']
  | tmul c s =>
    induction y using TensorProduct.induction_on with
    | zero => simp
    | add y y' hy hy' => simp only [map_add, hy, hy']
    | tmul d t => exact congrArg (· • (c * d)) (pairT_mapT P P' α s t)

theorem weil_adjT (he : P'.eps = P.eps) (t : P'.T) {n : ℕ} {z : ChTor.Pts P.A.A} (hz : z ^ p ^ n = 1) :
    weil P'.A (p ^ n) (z ≫ α) (t.lev n) = weil P.A (p ^ n) z ((adjT P P' α t).lev n) := by
  obtain ⟨s, rfl⟩ := (tate_free_of_card p _ _ P.card_torsion).2.1 n z hz
  rw [← pow_pairT P.A P.eps, ← pairT_mapT, ← he, pow_pairT, lev_mapT]

variable [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O]
  (β : P.Gt ⟶ P'.Gt) [IsMonHom β] (he : P'.eps = P.eps) (hβ : ∀ x, P'.toA (x ≫ β) = P.toA x ≫ α)

include he hβ

theorem weilChar_adjT (t : P'.T) (n : ℕ) : (P.weilChar (adjT P P' α t)).χ n =
    ExtensionTorsion.torsionHom β (p ^ n) ≫ (P'.weilChar t).χ n := P.char_ext fun w => by
  rw [← Category.assoc, P.isWeilChar_weilChar, P'.isWeilChar_weilChar, Category.assoc,
    ExtensionTorsion.torsionHom_ι, ← Category.assoc, hβ, weil_adjT α he t (P.toA_pow w)]

variable [Algebra ℤ_[p] O]

theorem al₀_adjT (t : P'.T) (x : LieG P.Gt) :
    (P.al₀ (adjT P P' α t)).1 x = (P'.al₀ t).1 (lieMap β x) := by
  refine HodgeTateImage.eq_of_forall (p := p) fun n => ?_
  have hR := HodgeTateImage.pow_quot (O := O) (p := p) n
  have h1 := isAl_dlogTv (P.weilChar (adjT P P' α t)) n _ hR x _ (HodgeTateImage.lift_ι hR x)
  have h2 := isAl_dlogTv (P'.weilChar t) n _ hR (lieMap β x)
    (HodgeTateImage.lift hR x ≫ ExtensionTorsion.torsionHom β (p ^ n)) (by
      rw [Category.assoc, ExtensionTorsion.torsionHom_ι, ← Category.assoc, HodgeTateImage.lift_ι]
      exact Category.assoc _ _ _)
  rw [Category.assoc, ← weilChar_adjT α β he hβ, h1] at h2
  change algebraMap O _ ((dlogTv (P.weilChar (adjT P P' α t))).1 x) =
    algebraMap O _ ((dlogTv (P'.weilChar t)).1 (lieMap β x))
  simpa [Algebra.algebraMap_eq_smul_one] using congrArg TrivSqZeroExt.snd h2

variable [Algebra ℤ_[p] C] [IsScalarTower ℤ_[p] O C]

theorem mapV_bLie (x : LieG P.Gt) : mapV P P' α (P.bLie x) = P'.bLie (lieMap β x) :=
  P'.eq_of_pairV fun t => by
    rw [pairV_mapV, adjV_tmul, Point.pairV_bLie, Point.pairV_bLie, al₀_adjT α β he hβ]

theorem mapV_mem_wRec (h : ∀ a, P.oGt.act a ≫ β = β ≫ P'.oGt.act a) (τ : Λ →+* O) {x : P.V}
    (hx : x ∈ P.wRec τ) : mapV P P' α x ∈ P'.wRec τ := by
  obtain ⟨y, rfl⟩ := hx
  refine ⟨⟨lieMap β y.1, fun a => Subtype.ext ?_⟩, (mapV_bLie α β he hβ y.1).symm⟩
  have h1 : y.1.1 ≫ P.oGt.act a = ptMap (dualScale (τ a)) ≫ y.1.1 := congrArg Subtype.val (y.2 a)
  change (y.1.1 ≫ β) ≫ P'.oGt.act a = ptMap (dualScale (τ a)) ≫ y.1.1 ≫ β
  rw [Category.assoc, ← h, ← Category.assoc, h1, Category.assoc]

end General

section Good

variable {Λ : Type} [CommRing Λ] [StarRing Λ] {p : ℕ} [Fact p.Prime] {C : Type} [Field C]
  {v : Valuation C ℝ≥0} {O : Type} [CommRing O] [Algebra O C] (hv : v.Integers O) (ε : Eps p C) {R : Type}
  [CommRing R] (j : R →+* O) {B B' B'' : Out.PolAV (Sp R)} (o : B.OAct Λ) (o' : B'.OAct Λ) (o'' : B''.OAct Λ)

theorem homO_act {f : B.A ⟶ B'.A} (h : ∀ a, o.act a ≫ f = f ≫ o'.act a) (a : Λ) :
    (goodPoint hv ε j B o).oGt.act a ≫ homO hv ε j o o' f =
      homO hv ε j o o' f ≫ (goodPoint hv ε j B' o').oGt.act a := by
  rw [goodPoint_oGt, goodPoint_oGt]
  exact ((Over.pullback _).map_comp _ _).symm.trans ((congrArg _ (h a)).trans ((Over.pullback _).map_comp _ _))

theorem homC_comp (f : B.A ⟶ B'.A) (g : B'.A ⟶ B''.A) :
    homC hv ε j o o'' (f ≫ g) = homC hv ε j o o' f ≫ homC hv ε j o' o'' g :=
  (congrArg _ ((Over.pullback _).map_comp _ _)).trans ((Over.pullback _).map_comp _ _)

theorem homC_act {f : B.A ⟶ B'.A} (h : ∀ a, o.act a ≫ f = f ≫ o'.act a) (a : Λ) :
    (goodPoint hv ε j B o).oA.act a ≫ homC hv ε j o o' f =
      homC hv ε j o o' f ≫ (goodPoint hv ε j B' o').oA.act a := by
  rw [goodPoint_oA, goodPoint_oA]
  exact (homC_comp hv ε j o o o' _ f).symm.trans ((congrArg _ (h a)).trans (homC_comp hv ε j o o' o' f _))

theorem homT_act (a : Λ) [IsMonHom (o.act a)] : homT hv ε j o o (o.act a) = (goodPoint hv ε j B o).actT a :=
  LinearMap.ext fun t => Tate.ext fun n => congrArg (t.lev n ≫ ·) (goodPoint_oA hv ε j o a).symm

theorem homT_id : homT hv ε j o o (𝟙 B.A) = LinearMap.id :=
  LinearMap.ext fun t => Tate.ext fun n =>
    (congrArg (t.lev n ≫ ·) ((congrArg _ ((Over.pullback _).map_id _)).trans ((Over.pullback _).map_id _))).trans
      (Category.comp_id _)

section Linear

variable {f : B.A ⟶ B'.A} [IsMonHom f]

theorem homT_actT (h : ∀ a, o.act a ≫ f = f ≫ o'.act a) (a : Λ) (t : (goodPoint hv ε j B o).T) :
    homT hv ε j o o' f ((goodPoint hv ε j B o).actT a t) = (goodPoint hv ε j B' o').actT a (homT hv ε j o o' f t) :=
  mapT_actT (P := goodPoint hv ε j B o) (P' := goodPoint hv ε j B' o') _ (homC_act hv ε j o o' h) a t

variable [Algebra ℤ_[p] C]

variable [Algebra ℤ_[p] O] [IsScalarTower ℤ_[p] O C]

theorem homV_mem_latTSub (h : ∀ a, o.act a ≫ f = f ≫ o'.act a) (τ : Λ →+* O) {x : (goodPoint hv ε j B o).V}
    (hx : x ∈ (goodPoint hv ε j B o).latTSub τ) : homV hv ε j o o' f x ∈ (goodPoint hv ε j B' o').latTSub τ :=
  mapV_mem_latTSub (P := goodPoint hv ε j B o) (P' := goodPoint hv ε j B' o') _ (homC_act hv ε j o o' h) τ hx

end Linear

variable [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O]

theorem toG_goodPoint (x : specO O O ⟶ (goodPoint hv ε j B o).Gt) : (goodPoint hv ε j B o).toG x = x :=
  (goodPoint hv ε j B o).hom_ext_red fun m => (goodPoint hv ε j B o).red_toG x m

theorem toA_homO (f : B.A ⟶ B'.A) (x : specO O O ⟶ (goodPoint hv ε j B o).Gt) :
    (goodPoint hv ε j B' o').toA (x ≫ homO hv ε j o o' f) = (goodPoint hv ε j B o).toA x ≫ homC hv ε j o o' f := by
  have h1 := ((goodPoint hv ε j B o).eq_toA_iff x _).1 rfl
  have h2 : (homC hv ε j o o' f).left ≫ (goodPoint hv ε j B' o').gen =
      (goodPoint hv ε j B o).gen ≫ (homO hv ε j o o' f).left := pullback.lift_fst _ _ _
  rw [toG_goodPoint] at h1
  symm
  rw [Point.eq_toA_iff, toG_goodPoint, Over.comp_left, Category.assoc, h2]
  exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ (homO hv ε j o o' f).left) h1).trans (Category.assoc _ _ _))

variable [IsAlgClosed C] [CharZero C] [Algebra ℤ_[p] O] [Algebra ℤ_[p] C] [IsScalarTower ℤ_[p] O C]

theorem homV_bLie (f : B.A ⟶ B'.A) [IsMonHom f] (x : LieG (goodPoint hv ε j B o).Gt) :
    homV hv ε j o o' f ((goodPoint hv ε j B o).bLie x) = (goodPoint hv ε j B' o').bLie (homLie hv ε j o o' f x) :=
  mapV_bLie _ (homO hv ε j o o' f) rfl (toA_homO hv ε j o o' f) x

variable {f : B.A ⟶ B'.A} [IsMonHom f]

omit [Algebra ℤ_[p] C] [IsScalarTower ℤ_[p] O C] in

theorem al₀_adjT_homC (t : (goodPoint hv ε j B' o').T) (x : LieG (goodPoint hv ε j B o).Gt) :
    ((goodPoint hv ε j B o).al₀ (adjT _ _ (homC hv ε j o o' f) t)).1 x = ((goodPoint hv ε j B' o').al₀ t).1 (homLie hv ε j o o' f x) :=
  al₀_adjT (P := goodPoint hv ε j B o) (P' := goodPoint hv ε j B' o') _ (homO hv ε j o o' f) rfl (toA_homO hv ε j o o' f) t x

theorem homV_mem_wRec (h : ∀ a, o.act a ≫ f = f ≫ o'.act a) (τ : Λ →+* O) {x : (goodPoint hv ε j B o).V}
    (hx : x ∈ (goodPoint hv ε j B o).wRec τ) : homV hv ε j o o' f x ∈ (goodPoint hv ε j B' o').wRec τ :=
  mapV_mem_wRec (P := goodPoint hv ε j B o) (P' := goodPoint hv ε j B' o') _ (homO hv ε j o o' f) rfl (toA_homO hv ε j o o' f)
    (homO_act hv ε j o o' h) τ hx

end Good

section Triples

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {K : Type} [Field K] {ℓ : ℕ} [Fact ℓ.Prime]
  {C : Type} [Field C] {v : Valuation C ℝ≥0} {O : Type} [CommRing O] [Algebra O C] (hv : v.Integers O)
  (ε : Eps ℓ C) (i : K →+* C) {T T' : PAT H (Sp (𝓞 K))} {f g : T.t.G ⟶ T'.t.G}
  (hf : Serre.IsLinearHom T.t.act T'.t.act f) (hg : Serre.IsLinearHom T.t.act T'.t.act g)

theorem patT_actT : letI := H.starRing
    ∀ a t, patT hv ε i hf ((patPoint hv ε i T).actT a t) = (patPoint hv ε i T').actT a (patT hv ε i hf t) :=
  letI := H.starRing
  haveI : IsMonHom (C := Over (Sp (𝓞 K))) (M := T.pol.A) (N := T'.pol.A) f := hf.isMonHom
  homT_actT (B := T.pol) (B' := T'.pol) hv ε (embO hv i) (patAct T) (patAct T') hf.comm

variable [Algebra ℤ_[ℓ] C]

variable [Algebra ℤ_[ℓ] O] [IsScalarTower ℤ_[ℓ] O C]

theorem patV_mem_latTSub (τ : 𝓞 E →+* O) : letI := H.starRing
    ∀ x ∈ (patPoint hv ε i T).latTSub τ, patV hv ε i hf x ∈ (patPoint hv ε i T').latTSub τ :=
  letI := H.starRing
  haveI : IsMonHom (C := Over (Sp (𝓞 K))) (M := T.pol.A) (N := T'.pol.A) f := hf.isMonHom
  fun _ => homV_mem_latTSub (B := T.pol) (B' := T'.pol) hv ε (embO hv i) (patAct T) (patAct T') hf.comm τ

variable [Fact ¬IsUnit (ℓ : O)] [IsAdicComplete (Ideal.span {(ℓ : O)}) O] [IsAlgClosed C] [CharZero C]

theorem patV_bLie : letI := H.starRing
    ∀ x, patV hv ε i hf ((patPoint hv ε i T).bLie x) = (patPoint hv ε i T').bLie (patLie hv ε i hf x) :=
  letI := H.starRing
  haveI : IsMonHom (C := Over (Sp (𝓞 K))) (M := T.pol.A) (N := T'.pol.A) f := hf.isMonHom
  homV_bLie (B := T.pol) (B' := T'.pol) hv ε (embO hv i) (patAct T) (patAct T') f

theorem patV_mem_wRec (τ : 𝓞 E →+* O) : letI := H.starRing
    ∀ x ∈ (patPoint hv ε i T).wRec τ, patV hv ε i hf x ∈ (patPoint hv ε i T').wRec τ :=
  letI := H.starRing
  haveI : IsMonHom (C := Over (Sp (𝓞 K))) (M := T.pol.A) (N := T'.pol.A) f := hf.isMonHom
  fun _ => homV_mem_wRec (B := T.pol) (B' := T'.pol) hv ε (embO hv i) (patAct T) (patAct T') hf.comm τ

end Triples

example {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {K : Type} [Field K] [NumberField K]
    {ρ : 𝓞 K} {σ₁ : K →+* ℂ} {p q : ℕ} (X : CMObj H K ρ σ₁ p q) (ℓ : ℕ) [Fact ℓ.Prime] (ε : Eps ℓ ℂ_[ℓ])
    (i : K →+* ℂ_[ℓ]) (k : Fin p ⊕ Fin q) :
    letI := H.starRing; letI := algPadicInt ℓ; letI := algPadicField ℓ; haveI := towerPadic ℓ; haveI := factPadic ℓ
    haveI := PadicComplexHost.isAdicComplete ℓ
    ∀ x, phiV (PadicComplexInt.integers ℓ) ε i X k ((pointA (PadicComplexInt.integers ℓ) ε i X k.isLeft).bLie x) =
      (pointB (PadicComplexInt.integers ℓ) ε i X).bLie (phiLie (PadicComplexInt.integers ℓ) ε i X k x) := by
  letI := H.starRing; letI := algPadicInt ℓ; letI := algPadicField ℓ; haveI := towerPadic ℓ; haveI := factPadic ℓ
  haveI := PadicComplexHost.isAdicComplete ℓ
  exact patV_bLie (PadicComplexInt.integers ℓ) ε i (X.lin k)

end GlobalTheory.PointMap
