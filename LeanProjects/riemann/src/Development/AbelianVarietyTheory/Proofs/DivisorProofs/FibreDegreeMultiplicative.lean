import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.GlobalHeightBoundIffAtGoodPrimes
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ResidueDegreeOfIsOpenImmersion
open CategoryTheory Limits AlgebraicGeometry IsLocalRing MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.DV Formalism.DegreeFormula Formalism.MainNotions.LatticeTransfer Formalism.MainNotions.WeightThresholdDefs
open GlobalTheory GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.Vert GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.Mean4O GlobalTheory.MixedLocalChains

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace GlobalTheory.Vert.Model.Hom

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]

theorem eq_genericPoint_of_relDim_eq_zero : ∀ (O : Type) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] (Z₁ Z : GlobalTheory.Vert.Model O) (f : GlobalTheory.Vert.Model.Hom Z₁ Z),
    f.relDim = 0 → ∀ x : Z₁.X, f.f x = genericPoint Z.X → x = genericPoint Z₁.X := by
  intro O _ _ _ Z₁ Z f hf x hx
  by_contra hne
  have hA : IsClosed (closure {x} : Set Z₁.X) := isClosed_closure
  have : QuasiSober (closure {x} : Set Z₁.X) := hA.isClosedEmbedding_subtypeVal.quasiSober
  have hη : genericPoint Z₁.X ∉ (closure {x} : Set Z₁.X) := fun h =>
    hne ((specializes_iff_mem_closure.2 h).antisymm (genericPoint_specializes x)).eq
  have h₁ := topologicalKrullDim_add_one_le hA isClosed_univ
    fun y _ => ⟨genericPoint Z₁.X, Set.mem_univ _, hη, genericPoint_specializes y⟩
  rw [topologicalKrullDim_eq_of_isEmbedding Topology.IsEmbedding.id Set.range_id, Z₁.dim_eq] at h₁
  have hc : IsClosedMap (fun a : (closure {x} : Set Z₁.X) => f.f a.1) :=
    f.f.isClosedMap.comp hA.isClosedMap_subtype_val
  have h₂ := dim_add_dim_le (W := Unit) hc (j := fun _ => ⟨x, subset_closure rfl⟩)
    continuous_const (fun _ _ _ => rfl) fun _ => hx
  rw [Z.dim_eq] at h₂
  have hr : Z.relDim = Z₁.relDim := by have := f.relDim_add; omega
  rw [hr] at h₂
  have h₀ : (0 : WithBot ℕ∞) ≤ topologicalKrullDim Unit := by
    have := mt topologicalKrullDim_eq_bot_iff.1 (not_isEmpty_iff.2 ⟨()⟩)
    generalize topologicalKrullDim Unit = b at *
    lift b to ℕ∞ using this
    exact_mod_cast (zero_le : (0 : ℕ∞) ≤ b)
  replace h₂ := (le_add_of_nonneg_left h₀).trans h₂
  generalize topologicalKrullDim (closure {x} : Set Z₁.X) = a at *
  generalize Z₁.relDim + 1 = n at *
  have ha : a ≠ ⊥ := fun h => by simp [h] at h₂
  lift a to ℕ∞ using ha
  have h₃ : (n : ℕ∞) ≤ a := by exact_mod_cast h₂
  have h₄ : a + 1 ≤ (n : ℕ∞) := by exact_mod_cast h₁
  lift a to ℕ using fun h => by simp [h] at h₄
  have : (n : ℕ) ≤ a := by exact_mod_cast h₃
  have : a + 1 ≤ n := by exact_mod_cast h₄
  omega

theorem isIso_asFiberHom_genericPoint {X Y : Scheme.{0}} [IsIntegral X] (g : X ⟶ Y)
    (hfib : ∀ x : X, g x = g (genericPoint X) → x = genericPoint X) :
    IsIso (g.asFiberHom (genericPoint X)) := by
  set a := g.asFiberHom (genericPoint X)
  have hpt : ∀ q : g.fiber (g (genericPoint X)), g.fiberι _ q = genericPoint X := fun q =>
    hfib _ ((g.range_fiberι _).le ⟨q, rfl⟩)
  have hsurj : Function.Surjective a := fun q => by
    obtain ⟨r⟩ := (inferInstance : Nonempty (Spec (X.residueField (genericPoint X))))
    refine ⟨r, (g.fiberι _).isEmbedding.injective ?_⟩
    rw [g.asFiberHom_apply, g.fiberι_asFiber, hpt]
  have : Surjective a := ⟨hsurj⟩
  have hemb : Topology.IsOpenEmbedding a :=
    ⟨a.isEmbedding, by rw [hsurj.range_eq]; exact isOpen_univ⟩
  have hfield : ∀ (z : X) (_ : z = genericPoint X), IsField (X.presheaf.stalk z) := by
    rintro z rfl
    exact Field.toIsField (X.functionField)
  have : ∀ r, IsIso (a.stalkMap r) := fun r => by
    have hF : IsField ((g.fiber (g (genericPoint X))).presheaf.stalk (a r)) := by
      letI := (hfield _ (hpt (a r))).toField
      have hs := (g.fiberι _).stalkMap_surjective (a r)
      have hi := ((g.fiberι _).stalkMap (a r)).hom.injective
      exact MulEquiv.isField (hfield _ (hpt (a r)))
        (RingEquiv.ofBijective _ ⟨hi, hs⟩).symm.toMulEquiv
    letI := hF.toField
    rw [ConcreteCategory.isIso_iff_bijective]
    exact ⟨(a.stalkMap r).hom.injective, a.stalkMap_surjective r⟩
  have := IsOpenImmersion.of_isIso_stalkMap a hemb
  exact (isIso_iff_isOpenImmersion_and_surjective a).2 ⟨inferInstance, inferInstance⟩

theorem finrank_fiber_eq_residueDegree : ∀ (X Y : Scheme.{0}) [IsIntegral X] (g : X ⟶ Y) (y : Y),
    g (genericPoint X) = y → (∀ x : X, g x = y → x = genericPoint X) →
    letI : Algebra (Y.residueField y) Γ(g.fiber y, ⊤) := algebraΓOfHom (g.fiberToSpecResidueField y)
    Module.finrank (Y.residueField y) Γ(g.fiber y, ⊤) = g.residueDegree (genericPoint X) := by
  intro X Y _ g y hy hfib
  subst hy
  have := isIso_asFiberHom_genericPoint g hfib
  set a := g.asFiberHom (genericPoint X)
  letI : Algebra (Y.residueField (g (genericPoint X))) Γ(g.fiber (g (genericPoint X)), ⊤) :=
    algebraΓOfHom (g.fiberToSpecResidueField _)
  letI := (g.residueFieldMap (genericPoint X)).hom.toAlgebra
  let ψ := a.appTop ≫ (Scheme.ΓSpecIso _).hom
  have key : (Scheme.ΓSpecIso _).inv ≫ (g.fiberToSpecResidueField _).appTop ≫ ψ =
      g.residueFieldMap (genericPoint X) := by
    simp only [ψ, ← Category.assoc]
    rw [Category.assoc _ (g.fiberToSpecResidueField _).appTop, ← Scheme.Hom.comp_appTop,
      g.asFiberHom_fiberToSpecResidueField, Category.assoc, Scheme.ΓSpecIso_naturality,
      Iso.inv_hom_id_assoc]
  have hbij : Function.Bijective ψ := ConcreteCategory.bijective_of_isIso ψ
  let e : Γ(g.fiber (g (genericPoint X)), ⊤) ≃ₐ[Y.residueField (g (genericPoint X))]
      X.residueField (genericPoint X) :=
    AlgEquiv.ofRingEquiv (f := RingEquiv.ofBijective ψ.hom hbij) fun r =>
      congr($(key).hom r)
  exact e.toLinearEquiv.finrank_eq

theorem apply_genericPoint {Z₁ Z : Model O} (f : Hom Z₁ Z) :
    f.f (genericPoint Z₁.X) = genericPoint Z.X := by
  have h : ∀ z : Z.X, f.f (genericPoint Z₁.X) ⤳ z := fun z => by
    obtain ⟨x, rfl⟩ := f.f.surjective z
    exact (genericPoint_specializes x).map f.f.continuous
  refine ((genericPoint_spec Z.X).eq ?_).symm
  rw [isGenericPoint_iff_specializes]
  exact fun z => ⟨fun _ => Set.mem_univ _, fun _ => h z⟩

theorem isAffine_genFibre {Z₁ Z : Model O} (f : Hom Z₁ Z) (hf : f.relDim = 0) :
    IsAffine f.genFibre := by
  have hpt : ∀ p : f.genFibre, f.genFibreι p = genericPoint Z₁.X := fun p =>
    eq_genericPoint_of_relDim_eq_zero O Z₁ Z f hf _ ((f.f.range_fiberι _).le ⟨p, rfl⟩)
  obtain ⟨p⟩ := (inferInstance : Nonempty f.genFibre)
  obtain ⟨U, hU, hp⟩ := GlobalTheory.QCoh.exists_affine_mem p
  have hU' : U = ⊤ := by
    refine top_le_iff.1 fun q _ => ?_
    have : q = p := (f.f.fiberι _).isEmbedding.injective ((hpt q).trans (hpt p).symm)
    exact this ▸ hp
  subst hU'
  have : IsAffine (⊤ : f.genFibre.Opens).toScheme := hU
  exact IsAffine.of_isIso f.genFibre.topIso.inv

theorem fibreDeg_one_eq_finrank {Z₁ Z : Model O} (f : Hom Z₁ Z) (hf : f.relDim = 0) :
    f.fibreDeg 1 = (Module.finrank f.fnField Γ(f.genFibre, ⊤) : ℚ) := by
  have := isAffine_genFibre f hf
  have h := f.fibreDeg_prod (ι := Fin 0) (L := finZeroElim) (fun i => i.elim0)
  rw [Finset.univ_eq_empty, Finset.prod_empty, Fintype.card_fin, hf, if_pos rfl,
    interNum_of_isEmpty, chi_structureModule_of_isAffine] at h
  exact h

theorem fibreDeg_one_eq_residueDegree {Z₁ Z : Model O} (f : Hom Z₁ Z) (hf : f.relDim = 0) :
    f.fibreDeg 1 = (f.f.residueDegree (genericPoint Z₁.X) : ℚ) := by
  rw [fibreDeg_one_eq_finrank f hf]
  exact congrArg Nat.cast (finrank_fiber_eq_residueDegree Z₁.X Z.X f.f _ f.apply_genericPoint (eq_genericPoint_of_relDim_eq_zero O Z₁ Z f hf))

theorem fibreDeg_one_comp : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (B₁ B₂ B₃ : GlobalTheory.Vert.Model O) (g : GlobalTheory.Vert.Model.Hom B₃ B₂) (f : GlobalTheory.Vert.Model.Hom B₂ B₁), g.relDim = 0 → f.relDim = 0 → (g.comp f).fibreDeg 1 = g.fibreDeg 1 * f.fibreDeg 1 := by
  intro O _ _ _ B₁ B₂ B₃ g f hg hf
  have hgf : (g.comp f).relDim = 0 := by
    have h₁ := g.relDim_add
    have h₂ := f.relDim_add
    have h₃ := (g.comp f).relDim_add
    omega
  rw [fibreDeg_one_eq_residueDegree _ hgf, fibreDeg_one_eq_residueDegree _ hg,
    fibreDeg_one_eq_residueDegree _ hf]
  change ((g.f ≫ f.f).residueDegree _ : ℚ) = _
  rw [CurveDegreesCompare.residueDegree_comp, g.apply_genericPoint, Nat.cast_mul, mul_comm]

end GlobalTheory.Vert.Model.Hom
