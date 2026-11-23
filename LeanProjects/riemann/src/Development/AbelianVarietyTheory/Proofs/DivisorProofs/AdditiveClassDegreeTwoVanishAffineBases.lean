import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsThickId
import Development.AbelianVarietyTheory.Definitions.Divisors.SameIdIff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CohomologyRestrictBasisExtendedBijective
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechPairRestrictBaseChangeBijectiveStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.Obs GlobalTheory.LBLift
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.PrimBasis

variable {R : Type} [CommRing R] (R₁ : Type) [CommRing R₁] [Algebra R R₁]
variable {X X' : Scheme.{0}} {D T : Type} [Category.{0} D] [Category.{0} T]

def pairFun (φ : X' ⟶ X) (G : D ⥤ AffOp X) (H : T ⥤ AffOp X') (K : T ⥤ D)
    (le : ∀ t, (H.obj t).unop.1 ≤ φ ⁻¹ᵁ (G.obj (K.obj t)).unop.1) : T ⥤ (Pair φ)ᵒᵖ where
  obj t := Opposite.op ⟨((H.obj t).unop, (G.obj (K.obj t)).unop), le t⟩
  map {t t'} a := (homOfLE (show (⟨((H.obj t').unop, (G.obj (K.obj t')).unop), le t'⟩ : Pair φ) ≤
      ⟨((H.obj t).unop, (G.obj (K.obj t)).unop), le t⟩ from
    ⟨leOfHom (H.map a).unop, leOfHom (G.map (K.map a)).unop⟩)).op
  map_id _ := Subsingleton.elim _ _
  map_comp _ _ := Subsingleton.elim _ _

def pairTo {R' : Type} [CommRing R'] (φ : X' ⟶ X) (s' : X' ⟶ Sp R') (G : D ⥤ AffOp X) (H : T ⥤ AffOp X')
    (K : T ⥤ D) (le : ∀ t, (H.obj t).unop.1 ≤ φ ⁻¹ᵁ (G.obj (K.obj t)).unop.1) :
    CoefMap (RingHom.id R') (OPair φ s') (H ⋙ OAff s') where
  G := pairFun φ G H K le
  α _ := RingHom.id _
  naturality _ _ := rfl
  smul _ _ _ := rfl

end GlobalTheory.PrimBasis

namespace GlobalTheory.PrimBasis

variable {R : Type} [CommRing R] (R₁ : Type) [CommRing R₁] [Algebra R R₁]
variable {X X' : Scheme.{0}} {D T : Type} [Category.{0} D] [Category.{0} T]

theorem pairTo_pairRes (φ : X' ⟶ X) (s' : X' ⟶ Sp R) (G : D ⥤ AffOp X) (H : T ⥤ AffOp X') (K : T ⥤ D)
    (le : ∀ t, (H.obj t).unop.1 ≤ φ ⁻¹ᵁ (G.obj (K.obj t)).unop.1) (c : H2 (ext R₁ (OAff s'))) :
    (extMap R₁ (pairTo φ s' G H K le)).pull2 ((extMap R₁ (pairRes φ s')).pull2 c) =
      (extMap R₁ (CoefMap.restrict (OAff s') H)).pull2 c := by
  rw [← CoefMap.pullCohomologyTwo_comp]
  refine CoefMap.pullCohomologyTwo_eq_of_natTrans _ _ (𝟙 H) (fun t b ↦ ?_) c
  erw [mp_id]
  induction b using TensorProduct.induction_on with
  | zero => exact (map_zero _).trans (map_zero _).symm
  | tmul x y => rfl
  | add x y hx hy => exact (map_add _ x y).trans ((congrArg₂ (· + ·) hx hy).trans (map_add _ x y).symm)

theorem pairTo_pairPull {φ : X' ⟶ X} {s : X ⟶ Sp R} {s' : X' ⟶ Sp R} (w : φ ≫ s = s' ≫ spMap (RingHom.id R))
    (G : D ⥤ AffOp X) (H : T ⥤ AffOp X') (K : T ⥤ D)
    (le : ∀ t, (H.obj t).unop.1 ≤ φ ⁻¹ᵁ (G.obj (K.obj t)).unop.1) (c : H2 (ext R₁ (OAff s))) :
    (extMap R₁ (pairTo φ s' G H K le)).pull2 ((extMap R₁ (pairPull w)).pull2 c) =
      (extMap R₁ (pullMap w G H K le)).pull2 ((extMap R₁ (CoefMap.restrict (OAff s) G)).pull2 c) := by
  rw [← CoefMap.pullCohomologyTwo_comp, ← CoefMap.pullCohomologyTwo_comp]
  refine CoefMap.pullCohomologyTwo_eq_of_natTrans _ _ (𝟙 (K ⋙ G)) (fun t b ↦ ?_) c
  erw [mp_id]
  induction b using TensorProduct.induction_on with
  | zero => exact (map_zero _).trans (map_zero _).symm
  | tmul x y => rfl
  | add x y hx hy => exact (map_add _ x y).trans ((congrArg₂ (· + ·) hx hy).trans (map_add _ x y).symm)

end GlobalTheory.PrimBasis

namespace GlobalTheory.PrimBasis

variable {R : Type} [CommRing R] (R₁ : Type) [CommRing R₁] [Algebra R R₁]
variable {X X' : Scheme.{0}} {D T : Type} [Category.{0} D] [Category.{0} T]

theorem pairTo_injective (φ : X' ⟶ X) (s' : X' ⟶ Sp R) (G : D ⥤ AffOp X) (H : T ⥤ AffOp X') (K : T ⥤ D)
    (le : ∀ t, (H.obj t).unop.1 ≤ φ ⁻¹ᵁ (G.obj (K.obj t)).unop.1)
    (hr : Function.Surjective (extMap R₁ (pairRes φ s')).pull2)
    (hH : Function.Injective (extMap R₁ (CoefMap.restrict (OAff s') H)).pull2) :
    Function.Injective (extMap R₁ (pairTo φ s' G H K le)).pull2 := by
  intro x y e
  obtain ⟨x, rfl⟩ := hr x
  obtain ⟨y, rfl⟩ := hr y
  rw [pairTo_pairRes, pairTo_pairRes] at e
  rw [hH e]

end GlobalTheory.PrimBasis

open GlobalTheory.PrimBasis in

theorem GlobalTheory.Obs.additiveClassDegreeTwo_vanish_affineBases : PrimitiveExtendedDegTwoVanish → ∀ (R R₁ : Type) [CommRing R] [CommRing R₁] [Algebra R R₁] (q : R₁ →ₐ[R] R), (∀ y y', q y = 0 → q y' = 0 → y * y' = 0) → ∀ (A : Over (Sp R)) [GrpObj A] (g : ℕ), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom → ∀ (D T : Type) [Category.{0} D] [Category.{0} T] [Quiver.IsThin D] [Quiver.IsThin T] (G : D ⥤ AffOp A.left) (H : T ⥤ AffOp (A ⊗ A).left) (K₀ K₁ K₂ : T ⥤ D) (le₀ : ∀ t, (H.obj t).unop.1 ≤ (μ[A]).left ⁻¹ᵁ (G.obj (K₀.obj t)).unop.1) (le₁ : ∀ t, (H.obj t).unop.1 ≤ (fst A A).left ⁻¹ᵁ (G.obj (K₁.obj t)).unop.1) (le₂ : ∀ t, (H.obj t).unop.1 ≤ (snd A A).left ⁻¹ᵁ (G.obj (K₂.obj t)).unop.1), IsBasis G → IsBasis H → ∀ c : GlobalTheory.CatCoh.H2 (GlobalTheory.Obs.ext R₁ (G ⋙ OAff A.hom)), (extMap R₁ (pullMap (overW μ[A]) G H K₀ le₀)).pull2 c = (extMap R₁ (pullMap (overW (fst A A)) G H K₁ le₁)).pull2 c + (extMap R₁ (pullMap (overW (snd A A)) G H K₂ le₂)).pull2 c → c = 0 := by
  intro hP R R₁ _ _ _ q hq A _ g hA hg D T _ _ _ _ G H K₀ K₁ K₂ le₀ le₁ le₂ hGb hHb c hc
  have hG := (GlobalTheory.Obs.BasisExt.restrict_ext_bijective R R₁ A.left A.hom D G hGb.cover hGb.dir).2
  have hH := (GlobalTheory.Obs.BasisExt.restrict_ext_bijective R R₁ (A ⊗ A).left (A ⊗ A).hom T H hHb.cover hHb.dir).2
  have hr : ∀ φ : (A ⊗ A).left ⟶ A.left, Function.Bijective (extMap R₁ (pairRes φ (A ⊗ A).hom)).pull2 :=
    fun φ ↦ (GlobalTheory.T.cechPairRestrict_baseChange_bijective R R₁ A.left (A ⊗ A).left (A ⊗ A).hom φ).1.2
  obtain ⟨c', rfl⟩ := hG.2 c
  obtain ⟨c₁, hc₁⟩ := (hr (fst A A).left).2 ((extMap R₁ (pairPull (overW (fst A A)))).pull2 c')
  obtain ⟨c₂, hc₂⟩ := (hr (snd A A).left).2 ((extMap R₁ (pairPull (overW (snd A A)))).pull2 c')
  suffices h : c' = 0 by rw [h, map_zero]
  refine hP R R₁ q hq A g hA hg c' c₁ c₂ ?_ hc₁.symm hc₂.symm
  refine pairTo_injective R₁ _ _ G H K₀ le₀ (hr _).2 hH.1 ?_
  rw [pairTo_pairPull, pairTo_pairRes, map_add, hc, ← pairTo_pairPull R₁ (overW (fst A A)) G H K₁ le₁,
    ← pairTo_pairPull R₁ (overW (snd A A)) G H K₂ le₂, ← hc₁, ← hc₂, pairTo_pairRes, pairTo_pairRes]
