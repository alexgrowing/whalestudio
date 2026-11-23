import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.AxesVanishingStructureSheafDegOne
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq
import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
import Development.AbelianVarietyTheory.Definitions.Uniformization.ExistsInKNeOne
import Development.AbelianVarietyTheory.PublishedTheorems.RelativeAmpleness.RelAmpleAndKTrivIff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteAffineCoverInfClosed
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAffineOpenProductSectionsIsoStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorAlgebraProductDiagramCompatStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechPullOneBijectiveLatticeCoverStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.AbLaw GlobalTheory.CatCoh GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.Kunneth

section Pairs

variable {R R' : Type} [CommRing R] [CommRing R'] {X X' : Scheme.{0}} {s : X ⟶ Sp R}
  {s' : X' ⟶ Sp R'} {σ : R →+* R'} {φ : X' ⟶ X}
  {C : Type} [Category.{0} C] (A : C ⥤ AffOp X') (B : C ⥤ AffOp X)
  (hle : ∀ T, (A.obj T).unop.1 ≤ φ ⁻¹ᵁ (B.obj T).unop.1)

def toPair : C ⥤ (Pair φ)ᵒᵖ where
  obj T := Opposite.op ⟨((A.obj T).unop, (B.obj T).unop), hle T⟩
  map {T T'} a := (homOfLE (Subtype.coe_le_coe.1
    (Prod.mk_le_mk.2 ⟨leOfHom (A.map a).unop, leOfHom (B.map a).unop⟩) :
      (⟨((A.obj T').unop, (B.obj T').unop), hle T'⟩ : Pair φ) ≤ ⟨((A.obj T).unop, (B.obj T).unop), hle T⟩)).op
  map_id _ := Quiver.Hom.unop_inj (Subsingleton.elim _ _)
  map_comp _ _ := Quiver.Hom.unop_inj (Subsingleton.elim _ _)

theorem restrict_pullHO1 (h : φ ≫ s = s' ≫ spMap σ) (c : HO1 s) :
    (CoefMap.restrict (OAff s') A).pull1 (pullHO1 h c) =
      ((pairPull h).comp (CoefMap.restrict (OPair φ s') (toPair A B hle))).pull1 c := by
  rw [CoefMap.pullCohomologyOne_comp, (isPullO_pullHO1 h c : (pairPull h).pull1 c = (pairRes φ s').pull1 (pullHO1 h c))]
  exact CoefMap.pullCohomologyOne_comp (pairRes φ s') (CoefMap.restrict (OPair φ s') (toPair A B hle)) (pullHO1 h c)

end Pairs

end GlobalTheory.Kunneth

namespace GlobalTheory.Kunneth

def prodFun {J J' : Type} [Preorder J] [Preorder J'] {Z : Scheme.{0}} (W : J × J' → Z.affineOpens)
    (hW : Monotone W) : Jᵒᵖ × J'ᵒᵖ ⥤ AffOp Z where
  obj T := Opposite.op (W (T.1.unop, T.2.unop))
  map a := (homOfLE (hW (Prod.mk_le_mk.2 ⟨leOfHom a.1.unop, leOfHom a.2.unop⟩))).op
  map_id _ := Quiver.Hom.unop_inj (Subsingleton.elim _ _)
  map_comp _ _ := Quiver.Hom.unop_inj (Subsingleton.elim _ _)

theorem cup_tmul_injective : ∀ (K : Type) [Field K] (X Y : Over (Sp K)), IsSeparated X.hom → QuasiCompact X.hom →
    IsSeparated Y.hom → QuasiCompact Y.hom → ∀ (n : ℕ) (x : Fin n → HO1 X.hom) (y : Fin n → HO1 Y.hom),
    ∑ i, cup (OAff (X ⊗ Y).hom) (pO1 (fst X Y) (x i)) (pO1 (snd X Y) (y i)) = 0 →
    ∑ i, x i ⊗ₜ[K] y i = 0 := by
  intro K _ X Y hXs hXq hYs hYq n x y hsum
  obtain ⟨J, _, _, U, hU, hUi, hUc⟩ := GlobalTheory.exists_finite_affine_cover_infClosed K X.left X.hom hXs hXq
  obtain ⟨J', _, _, V, hV, hVi, hVc⟩ := GlobalTheory.exists_finite_affine_cover_infClosed K Y.left Y.hom hYs hYq
  choose Wf h1 h2 i1 i2 hWe hi1 hi2 hbij using fun p : J × J' ↦ GlobalTheory.T.exists_affine_open_product_sections_iso K X Y (U p.1) (V p.2)
  have hWm : Monotone Wf := fun p q hpq ↦ by
    show (Wf p).1 ≤ (Wf q).1
    rw [hWe p, hWe q]
    exact inf_le_inf (Scheme.Hom.preimage_mono _ (hU hpq.1)) (Scheme.Hom.preimage_mono _ (hV hpq.2))
  haveI : Finite J'ᵒᵖ := Finite.of_equiv J' Opposite.equivToOpposite
  let Ψ := prodFun Wf hWm
  let F := hU.functor.op ⋙ OAff X.hom
  let G := hV.functor.op ⋙ OAff Y.hom
  let E := Ψ ⋙ OAff (X ⊗ Y).hom
  let B₁ : Jᵒᵖ × J'ᵒᵖ ⥤ AffOp X.left := CategoryTheory.Prod.fst Jᵒᵖ J'ᵒᵖ ⋙ hU.functor.op
  let B₂ : Jᵒᵖ × J'ᵒᵖ ⥤ AffOp Y.left := CategoryTheory.Prod.snd Jᵒᵖ J'ᵒᵖ ⋙ hV.functor.op
  have hle₁ : ∀ T, (Ψ.obj T).unop.1 ≤ (fst X Y).left ⁻¹ᵁ (B₁.obj T).unop.1 := fun T ↦ h1 (T.1.unop, T.2.unop)
  have hle₂ : ∀ T, (Ψ.obj T).unop.1 ≤ (snd X Y).left ⁻¹ᵁ (B₂.obj T).unop.1 := fun T ↦ h2 (T.1.unop, T.2.unop)
  let m₁ := (pairPull (ovw (fst X Y))).comp (CoefMap.restrict (OPair (fst X Y).left (X ⊗ Y).hom) (toPair Ψ B₁ hle₁))
  let m₂ := (pairPull (ovw (snd X Y))).comp (CoefMap.restrict (OPair (snd X Y).left (X ⊗ Y).hom) (toPair Ψ B₂ hle₂))
  let j₁ : ∀ T : Jᵒᵖ × J'ᵒᵖ, F.obj T.1 →ₐ[K] E.obj T := fun T ↦ i1 (T.1.unop, T.2.unop)
  let j₂ : ∀ T : Jᵒᵖ × J'ᵒᵖ, G.obj T.2 →ₐ[K] E.obj T := fun T ↦ i2 (T.1.unop, T.2.unop)
  have nat₁ : ∀ (T T' : Jᵒᵖ × J'ᵒᵖ) (a : T ⟶ T') (b : F.obj T.1), j₁ T' (mp F a.1 b) = mp E a (j₁ T b) := by
    intro T T' a b
    refine (hi1 _ _).trans (Eq.trans ?_ (congrArg (mp E a) (hi1 (T.1.unop, T.2.unop) b).symm))
    exact m₁.naturality a b
  have nat₂ : ∀ (T T' : Jᵒᵖ × J'ᵒᵖ) (a : T ⟶ T') (b : G.obj T.2), j₂ T' (mp G a.2 b) = mp E a (j₂ T b) := by
    intro T T' a b
    refine (hi2 _ _).trans (Eq.trans ?_ (congrArg (mp E a) (hi2 (T.1.unop, T.2.unop) b).symm))
    exact m₂.naturality a b
  let n₁ : CoefMap (RingHom.id K) F E :=
    { G := CategoryTheory.Prod.fst Jᵒᵖ J'ᵒᵖ
      α := fun T ↦ (j₁ T).toRingHom
      naturality := fun {T T'} a b ↦ nat₁ T T' a b
      smul := fun T r b ↦ map_smul (j₁ T) r b }
  let n₂ : CoefMap (RingHom.id K) G E :=
    { G := CategoryTheory.Prod.snd Jᵒᵖ J'ᵒᵖ
      α := fun T ↦ (j₂ T).toRingHom
      naturality := fun {T T'} a b ↦ nat₂ T T' a b
      smul := fun T r b ↦ map_smul (j₂ T) r b }
  let rU := CoefMap.restrict (OAff X.hom) hU.functor.op
  let rV := CoefMap.restrict (OAff Y.hom) hV.functor.op
  let rE := CoefMap.restrict (OAff (X ⊗ Y).hom) Ψ
  have key₁ : ∀ a, rE.pull1 (pO1 (fst X Y) a) = n₁.pull1 (rU.pull1 a) := fun a ↦ by
    refine (restrict_pullHO1 Ψ B₁ hle₁ (ovw (fst X Y)) a).trans ?_
    refine (CoefMap.pullCohomologyOne_eq_of_natTrans m₁ (rU.comp n₁) (𝟙 B₁) (fun T b ↦ ?_) a).trans
      (CoefMap.pullCohomologyOne_comp rU n₁ a)
    refine (congrArg ((rU.comp n₁).α T) (mp_id (OAff X.hom) _ b)).trans ?_
    exact hi1 (T.1.unop, T.2.unop) b
  have key₂ : ∀ a, rE.pull1 (pO1 (snd X Y) a) = n₂.pull1 (rV.pull1 a) := fun a ↦ by
    refine (restrict_pullHO1 Ψ B₂ hle₂ (ovw (snd X Y)) a).trans ?_
    refine (CoefMap.pullCohomologyOne_eq_of_natTrans m₂ (rV.comp n₂) (𝟙 B₂) (fun T b ↦ ?_) a).trans
      (CoefMap.pullCohomologyOne_comp rV n₂ a)
    refine (congrArg ((rV.comp n₂).α T) (mp_id (OAff Y.hom) _ b)).trans ?_
    exact hi2 (T.1.unop, T.2.unop) b
  have hbU : Function.Bijective rU.pull1 := GlobalTheory.T.cech_pull_one_bijective_lattice_cover K X.left X.hom J U hU hUi hUc
  have hbV : Function.Bijective rV.pull1 := GlobalTheory.T.cech_pull_one_bijective_lattice_cover K Y.left Y.hom J' V hV hVi hVc
  choose x' hx' using fun i ↦ H1.mk_surjective F (rU.pull1 (x i))
  choose y' hy' using fun i ↦ H1.mk_surjective G (rV.pull1 (y i))
  have hz : H2.mk E (∑ i, cupZ E (n₁.pullbackOneCocycle (x' i)) (n₂.pullbackOneCocycle (y' i))) = 0 := by
    have h0 := congrArg rE.pull2 hsum
    rw [map_zero, map_sum] at h0
    rw [map_sum]
    refine Eq.trans (Finset.sum_congr rfl fun i _ ↦ ?_) h0
    rw [CoefMap.pullCohomologyTwo_cup, key₁, key₂, ← hx', ← hy']
    rfl
  obtain ⟨f, hf⟩ := H2.mk_eq_zero.1 hz
  have e := GlobalTheory.T.tensor_algebra_product_diagram_compat K Jᵒᵖ J'ᵒᵖ F G E j₁ j₂ nat₁ nat₂ (fun T ↦ hbij (T.1.unop, T.2.unop)) n x' y' f
    (fun T T' T'' a b ↦ by
      rw [hf]
      simp only [Submodule.coe_sum, Finset.sum_apply]
      rfl)
  simp only [hx', hy'] at e
  let eU := LinearEquiv.ofBijective rU.pull1 hbU
  let eV := LinearEquiv.ofBijective rV.pull1 hbV
  apply (TensorProduct.congr eU eV).injective
  rw [map_sum, map_zero]
  exact e

end GlobalTheory.Kunneth
