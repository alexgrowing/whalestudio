import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.TangentLinearity.ConstPullback
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.WeightedChartPullback.CancelSecAct

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
  CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

namespace ReciprocityTheory.ChartRestriction.G.Out.TLinPf

open Semi

abbrev A1 : Scheme.{0} := Spec (CommRingCat.of (Polynomial ℤ))

def mOf {X : Scheme.{0}} (ρ : Γ(X, ⊤)) : X ⟶ A1 :=
  X.toSpecΓ ≫ Spec.map (CommRingCat.ofHom (Polynomial.eval₂RingHom (Int.castRingHom _) ρ))

def fnOf {X : Scheme.{0}} (m : X ⟶ A1) : Γ(X, ⊤) :=
  m.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of (Polynomial ℤ))).inv.hom Polynomial.X)

lemma fnOf_comp {X Y : Scheme.{0}} (y : Y ⟶ X) (m : X ⟶ A1) :
    fnOf (y ≫ m) = y.appTop.hom (fnOf m) := by
  simp only [fnOf, Scheme.Hom.comp_appTop, CommRingCat.comp_apply]

lemma fnOf_mOf {X : Scheme.{0}} (ρ : Γ(X, ⊤)) : fnOf (mOf ρ) = ρ := by
  have h : (mOf ρ).appTop = (Scheme.ΓSpecIso _).hom ≫
      CommRingCat.ofHom (Polynomial.eval₂RingHom (Int.castRingHom _) ρ) := by
    rw [mOf, Scheme.Hom.comp_appTop, Scheme.toSpecΓ_appTop, Scheme.ΓSpecIso_naturality]
  rw [fnOf, h, CommRingCat.comp_apply, Iso.inv_hom_id_apply]
  simp

lemma comp_mOf {X Y : Scheme.{0}} (y : Y ⟶ X) (ρ : Γ(X, ⊤)) :
    y ≫ mOf ρ = mOf (y.appTop.hom ρ) := by
  rw [mOf, mOf, ← Category.assoc, Scheme.toSpecΓ_naturality, Category.assoc, ← Spec.map_comp]
  congr 2
  ext1
  refine Polynomial.ringHom_ext (fun a => ?_) ?_
  · simp
  · simp

lemma mOf_inj {X : Scheme.{0}} {ρ ρ' : Γ(X, ⊤)} (h : mOf ρ = mOf ρ') : ρ = ρ' := by
  rw [← fnOf_mOf ρ, h, fnOf_mOf]

section Desc

variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegPre R} {e : ℕ}
  {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G] (g : GtCoord I D e G)

theorem kp (ρ : Γ((thickObj R I e G).left, ⊤))
    (h : (WeightPf.act g).left.appTop.hom ρ =
      (snd (WeightPf.Te D I e) (thickObj R I e G)).left.appTop.hom ρ)
    {Z : Scheme.{0}} (y1 y2 : Z ⟶ (thickObj R I e G).left) (hq : y1 ≫ g.q.left = y2 ≫ g.q.left) :
    y1.appTop.hom ρ = y2.appTop.hom ρ := by
  have hw : y1 ≫ (thickObj R I e G).hom = y2 ≫ (thickObj R I e G).hom := by
    rw [← Over.w g.q, ← Category.assoc, hq, Category.assoc]
  let FinalForm : Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1)))) := Over.mk (y2 ≫ (thickObj R I e G).hom)
  let z1 : FinalForm ⟶ thickObj R I e G := Over.homMk y1 hw
  let z2 : FinalForm ⟶ thickObj R I e G := Over.homMk y2 rfl
  have hq' : z1 ≫ g.q = z2 ≫ g.q := Over.OverMorphism.ext (by simpa [z1, z2] using hq)
  have := g.q_hom
  have hinv : z2⁻¹ ≫ g.q = (z2 ≫ g.q)⁻¹ := by
    refine eq_inv_of_mul_eq_one_left ?_
    rw [← MonObj.mul_comp, inv_mul_cancel, MonObj.one_comp]
  have hd : (z1 * z2⁻¹) ≫ g.q = toUnit FinalForm ≫ η[thickObj R I e D.P.A] := by
    rw [MonObj.mul_comp, hinv, hq', mul_inv_cancel, Hom.one_def]
  let τ := g.isKernel.lift (z1 * z2⁻¹) (toUnit FinalForm) hd
  have hτ : τ ≫ g.i = z1 * z2⁻¹ := g.isKernel.lift_fst _ _ _
  have e1 : lift τ z2 ≫ WeightPf.act g = z1 := by
    have h1 : WeightPf.act g = (fst (WeightPf.Te D I e) (thickObj R I e G) ≫ g.i) * snd _ _ := rfl
    rw [h1, MonObj.comp_mul, lift_fst_assoc, lift_snd, hτ, inv_mul_cancel_right]
  have e2 : lift τ z2 ≫ snd (WeightPf.Te D I e) (thickObj R I e G) = z2 := lift_snd _ _
  have E1 : y1 = (lift τ z2).left ≫ (WeightPf.act g).left := by
    rw [← Over.comp_left, e1]; rfl
  have E2 : y2 = (lift τ z2).left ≫ (snd (WeightPf.Te D I e) (thickObj R I e G)).left := by
    rw [← Over.comp_left, e2]; rfl
  rw [E1, E2, Scheme.Hom.comp_appTop, Scheme.Hom.comp_appTop, CommRingCat.comp_apply,
    CommRingCat.comp_apply, h]

theorem descend (ρ : Γ((thickObj R I e G).left, ⊤))
    (h : (WeightPf.act g).left.appTop.hom ρ =
      (snd (WeightPf.Te D I e) (thickObj R I e G)).left.appTop.hom ρ) :
    ∃ v : Γ((thickObj R I e D.P.A).left, ⊤), g.q.left.appTop.hom v = ρ := by
  have := g.q_flat
  have := g.q_surj
  have := g.q_affine
  let 𝒰 := (thickObj R I e D.P.A).left.affineCover
  have hloc : ∀ i, ∃ u : 𝒰.X i ⟶ A1,
      pullback.snd g.q.left (𝒰.f i) ≫ u = pullback.fst g.q.left (𝒰.f i) ≫ mOf ρ := by
    intro i
    have : IsAffine (pullback g.q.left (𝒰.f i)) := isAffine_of_isAffineHom (pullback.snd g.q.left (𝒰.f i))
    have : IsRegularEpi (pullback.snd g.q.left (𝒰.f i)) :=
      isRegularEpi_of_flat_of_surjective_of_isAffine _
    refine IsRegularEpi.exists_of_isKernelPair _ (IsKernelPair.of_hasPullback _) _ ?_
    rw [← Category.assoc, ← Category.assoc, comp_mOf, comp_mOf]
    congr 1
    refine kp g ρ h _ _ ?_
    rw [Category.assoc, Category.assoc, pullback.condition, pullback.condition_assoc]
  choose u hu using hloc
  have hglue : ∀ i j, pullback.fst (𝒰.f i) (𝒰.f j) ≫ u i = pullback.snd (𝒰.f i) (𝒰.f j) ≫ u j := by
    intro i j
    let c := pullback.fst (𝒰.f i) (𝒰.f j) ≫ 𝒰.f i
    have : Epi (pullback.snd g.q.left c) := Flat.epi_of_flat_of_surjective _
    rw [← cancel_epi (pullback.snd g.q.left c)]
    have li : pullback.snd g.q.left c ≫ pullback.fst (𝒰.f i) (𝒰.f j) =
        pullback.lift (pullback.fst g.q.left c) (pullback.snd g.q.left c ≫ pullback.fst _ _)
          (by rw [pullback.condition, Category.assoc]) ≫ pullback.snd g.q.left (𝒰.f i) := by
      rw [pullback.lift_snd]
    have lj : pullback.snd g.q.left c ≫ pullback.snd (𝒰.f i) (𝒰.f j) =
        pullback.lift (pullback.fst g.q.left c) (pullback.snd g.q.left c ≫ pullback.snd _ _)
          (by rw [pullback.condition]; show _ ≫ pullback.fst (𝒰.f i) (𝒰.f j) ≫ 𝒰.f i = _
              rw [pullback.condition, Category.assoc])
          ≫ pullback.snd g.q.left (𝒰.f j) := by
      rw [pullback.lift_snd]
    rw [← Category.assoc, li, Category.assoc, hu, pullback.lift_fst_assoc, ← Category.assoc, lj,
      Category.assoc, hu, pullback.lift_fst_assoc]
  have hU : g.q.left ≫ 𝒰.glueMorphisms u hglue = mOf ρ := by
    refine Scheme.Cover.hom_ext (𝒰.pullback₁ g.q.left) _ _ fun i => ?_
    change pullback.fst g.q.left (𝒰.f i) ≫ g.q.left ≫ 𝒰.glueMorphisms u hglue =
      pullback.fst g.q.left (𝒰.f i) ≫ mOf ρ
    have hι : 𝒰.f i ≫ 𝒰.glueMorphisms u hglue = u i := Scheme.Cover.ι_glueMorphisms 𝒰 u hglue i
    rw [pullback.condition_assoc, hι]
    exact hu i
  refine ⟨fnOf (𝒰.glueMorphisms u hglue), ?_⟩
  rw [← fnOf_comp, hU, fnOf_mOf]

end Desc

end ReciprocityTheory.ChartRestriction.G.Out.TLinPf
