import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
  CartesianMonoidalCategory MonObj

attribute [local instance] Over.cartesianMonoidalCategory

namespace ReciprocityTheory.ChartRestriction.G.H1.SectionDivision

open ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi

theorem exists_section {k : Type} [Field k] [IsAlgClosed k] {P' : Scheme.{0}}
    (p : P' ⟶ Spec (CommRingCat.of k)) [IsFinite p] [Surjective p] :
    ∃ t : Spec (CommRingCat.of k) ⟶ P', t ≫ p = 𝟙 _ := by
  have : IsAffine P' := isAffine_of_isAffineHom p
  obtain ⟨w, -⟩ := Surjective.surj (f := p) (IsLocalRing.closedPoint k)
  have : Nonempty (⊤ : P'.Opens) := ⟨⟨w, trivial⟩⟩
  let θ := Scheme.ΓSpecIso (CommRingCat.of k)
  let ψ : k →+* Γ(P', ⊤) := (p.appTop).hom.comp θ.inv.hom
  let _ : Algebra k Γ(P', ⊤) := ψ.toAlgebra
  have hfin : ψ.Finite := (IsFinite.finite_app p ⊤ (isAffineOpen_top _)).comp
    (RingHom.Finite.of_surjective _ (ConcreteCategory.bijective_of_isIso θ.inv).2)
  have : Module.Finite k Γ(P', ⊤) := hfin
  obtain ⟨M, hM⟩ := Ideal.exists_maximal Γ(P', ⊤)
  let _ : Field (Γ(P', ⊤) ⧸ M) := Ideal.Quotient.field M
  have : Module.Finite k (Γ(P', ⊤) ⧸ M) :=
    Module.Finite.of_surjective (Ideal.Quotient.mkₐ k M).toLinearMap (Ideal.Quotient.mkₐ_surjective k M)
  have : Algebra.IsIntegral k (Γ(P', ⊤) ⧸ M) := Algebra.IsIntegral.of_finite k _
  have hb := IsAlgClosed.algebraMap_bijective_of_isIntegral (k := k) (K := Γ(P', ⊤) ⧸ M)
  let e : k ≃+* Γ(P', ⊤) ⧸ M := RingEquiv.ofBijective (algebraMap k (Γ(P', ⊤) ⧸ M)) hb
  let φ' : Γ(P', ⊤) →+* k := e.symm.toRingHom.comp (Ideal.Quotient.mk M)
  have hφ : ∀ c, φ' (ψ c) = c := fun c => by
    show e.symm (Ideal.Quotient.mk M (algebraMap k Γ(P', ⊤) c)) = c
    rw [← Ideal.Quotient.algebraMap_eq, ← RingHom.comp_apply, ← IsScalarTower.algebraMap_eq]
    exact e.symm_apply_apply c
  let φ : Γ(P', ⊤) ⟶ Γ(Spec (CommRingCat.of k), ⊤) := CommRingCat.ofHom φ' ≫ θ.inv
  have hret : p.appTop ≫ φ = 𝟙 _ := by
    ext c
    obtain ⟨d, rfl⟩ : ∃ d, θ.inv.hom d = c := (ConcreteCategory.bijective_of_isIso θ.inv).2 c
    show θ.inv.hom (φ' (ψ d)) = θ.inv.hom d
    rw [hφ]
  refine ⟨(Spec (CommRingCat.of k)).isoSpec.hom ≫ Spec.map φ ≫ P'.isoSpec.inv, ?_⟩
  have nat' : P'.isoSpec.inv ≫ p = Spec.map p.appTop ≫ (Spec (CommRingCat.of k)).isoSpec.inv := by
    rw [Iso.inv_comp_eq, ← Category.assoc, Scheme.isoSpec_hom_naturality, Category.assoc, Iso.hom_inv_id,
      Category.comp_id]
  rw [Category.assoc, Category.assoc, nat', ← Category.assoc (Spec.map φ), ← Spec.map_comp, hret, Spec.map_id,
    Category.id_comp, Iso.hom_inv_id]

theorem exists_div (hmul : MulNSt) {k : Type} [Field k] [IsAlgClosed k]
    (P : PolAV (Spec (CommRingCat.of k))) (a₀ : baseOver (Spec (CommRingCat.of k)) ⟶ P.A) (r : ℕ)
    (hr : 1 ≤ r) : ∃ b : baseOver (Spec (CommRingCat.of k)) ⟶ P.A, b ^ r = a₀ := by
  obtain ⟨hfin, -, hsurj, -, -⟩ := hmul (Spec (CommRingCat.of k)) P r hr
  obtain ⟨t, ht⟩ := exists_section (pullback.snd (mulA P.A r).left a₀.left)
  have hb' : (t ≫ pullback.fst (mulA P.A r).left a₀.left) ≫ (mulA P.A r).left = a₀.left := by
    rw [Category.assoc, pullback.condition, ← Category.assoc, ht, Category.id_comp]
  have hw : (t ≫ pullback.fst (mulA P.A r).left a₀.left) ≫ P.A.hom = (baseOver (Spec (CommRingCat.of k))).hom := by
    rw [← Over.w (mulA P.A r), ← Category.assoc, hb', Over.w a₀]
  refine ⟨Over.homMk _ hw, ?_⟩
  have e : ∀ b : baseOver (Spec (CommRingCat.of k)) ⟶ P.A, b ^ r = b ≫ mulA P.A r := fun b =>
    (congrArg (· ^ r) (Category.comp_id b).symm).trans (MonObj.comp_pow (𝟙 P.A) r b).symm
  rw [e]
  exact Over.OverMorphism.ext hb'

end ReciprocityTheory.ChartRestriction.G.H1.SectionDivision
