import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRingHomOfGeneric
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagInduces
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLieFrames
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LieBaseIff
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ScholzeWeinsteinB
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsFlagBundleRankOne
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.RegularAlteration
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ValuativeLiftUniqueClosedPoint
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AbProj
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.ExistsChartFiniteType
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.DualGramInterpGram
import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.IsOpenOfMemIrreducibleComponentsOfFinite
import Formalism.LocalToGlobal.LatticeGeometry.CmTypeMeetsConjugatePair
import Development.AutomorphicArithmetic.DivisorFrames.ExistsAdaptedFlagCharts
open NumberField MvPolynomial Filter Topology Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovTest GlobalTheory.Published
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt
open Formalism.BasicNotions.DV Formalism.MainNotions.WeightThresholdDefs GlobalTheory.FlagAr GlobalTheory.ShFam.Pad GlobalTheory.VB GlobalTheory.ShFam GlobalTheory.TrueGeo Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ArLieBase
open GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.ProjVar
open scoped Classical

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FlagExt

open Limits

section Ext

variable {F : Type} [Field F] {G X : Scheme.{0}} [IsIntegral G] (s : G ⟶ Sp F) (t : X ⟶ Sp F)

private theorem spMap_fromSpecStalk (y : G) :
    spMap (algebraMap (G.presheaf.stalk y) G.functionField) ≫ G.fromSpecStalk y =
      G.fromSpecStalk (genericPoint G) :=
  Scheme.SpecMap_stalkSpecializes_fromSpecStalk ((genericPoint_spec G).specializes trivial)

private theorem isDominant_generic : IsDominant (G.fromSpecStalk (genericPoint G)) := ⟨by
  refine Dense.mono ?_ (dense_iff_closure_eq.2 (genericPoint_spec G))
  rintro _ rfl
  exact ⟨IsLocalRing.closedPoint _, Scheme.fromSpecStalk_closedPoint⟩⟩

private theorem exists_hom_of_extends [IsProper t] (p' : Sp G.functionField ⟶ X)
    (hp : p' ≫ t = G.fromSpecStalk (genericPoint G) ≫ s)
    (hl : ∀ y : G, ∃ l : Sp (G.presheaf.stalk y) ⟶ X,
      spMap (algebraMap (G.presheaf.stalk y) G.functionField) ≫ l = p') :
    ∃ φ : G ⟶ X, G.fromSpecStalk (genericPoint G) ≫ φ = p' ∧ φ ≫ t = s := by
  have hsep : X.IsSeparated := ⟨by rw [← terminal.comp_from t]; infer_instance⟩
  have hdom := isDominant_generic (G := G)
  have hcan : ∀ (y : G) (a b : Sp (G.presheaf.stalk y) ⟶ Sp F),
      spMap (algebraMap (G.presheaf.stalk y) G.functionField) ≫ a =
        spMap (algebraMap (G.presheaf.stalk y) G.functionField) ≫ b → a = b := by
    intro y a b hab
    rw [← Spec.map_preimage a, ← Spec.map_preimage b] at hab ⊢
    simp only [spMap, ← Spec.map_comp] at hab
    congr 1
    ext z
    have := congrArg (fun g => g.hom z) (Spec.map_injective hab)
    exact FaithfulSMul.algebraMap_injective (G.presheaf.stalk y) G.functionField this
  have hspec := spMap_fromSpecStalk (G := G)
  let f : G ⤏ X := Scheme.RationalMap.ofFunctionField s t p' hp
  have hfF : f.fromFunctionField = p' := Scheme.RationalMap.fromFunctionField_ofFunctionField _ _ _ _
  have htop : f.domain = ⊤ := by
    refine top_le_iff.1 fun y _ => ?_
    obtain ⟨l, hl1⟩ := hl y
    have h2 : l ≫ t = G.fromSpecStalk y ≫ s := by
      apply hcan y
      rw [← Category.assoc, hl1, hp, ← Category.assoc, hspec]
    refine Scheme.RationalMap.mem_domain.2 ⟨Scheme.PartialMap.ofFromSpecStalk (x := y) s t l h2,
      Scheme.PartialMap.mem_domain_ofFromSpecStalk (x := y) s t l h2, ?_⟩
    apply Scheme.RationalMap.eq_of_fromFunctionField_eq
    rw [Scheme.RationalMap.fromFunctionField_toRationalMap, hfF, ← hl1]
    have hm := Scheme.PartialMap.mem_domain_ofFromSpecStalk (x := y) s t l h2
    have e1 : spMap (algebraMap (G.presheaf.stalk y) G.functionField) ≫
        (Scheme.PartialMap.ofFromSpecStalk (x := y) s t l h2).fromSpecStalkOfMem hm =
        (Scheme.PartialMap.ofFromSpecStalk (x := y) s t l h2).fromFunctionField := by
      simp only [Scheme.PartialMap.fromSpecStalkOfMem]
      rw [← Category.assoc]
      congr 1
      rw [← cancel_mono (Scheme.PartialMap.ofFromSpecStalk (x := y) s t l h2).domain.ι,
        Category.assoc, Scheme.Opens.fromSpecStalkOfMem_ι, Scheme.Opens.fromSpecStalkOfMem_ι]
      exact hspec y
    rw [← e1, Scheme.PartialMap.fromSpecStalkOfMem_ofFromSpecStalk]
  let k : G ⟶ f.domain.toScheme := IsOpenImmersion.lift f.domain.ι (𝟙 G)
    (by rw [Scheme.Opens.range_ι, htop]; simp)
  have hk : k ≫ f.domain.ι = 𝟙 G := IsOpenImmersion.lift_fac _ _ _
  have hm : genericPoint G ∈ f.toPartialMap.domain := by
    change _ ∈ f.domain
    rw [htop]; trivial
  have hm' : genericPoint G ∈ f.domain := by rw [htop]; trivial
  have e2 : G.fromSpecStalk (genericPoint G) ≫ k = f.domain.fromSpecStalkOfMem _ hm' := by
    rw [← cancel_mono f.domain.ι, Scheme.Opens.fromSpecStalkOfMem_ι, Category.assoc, hk,
      Category.comp_id]
  have hg : G.fromSpecStalk (genericPoint G) ≫ (k ≫ f.toPartialMap.hom) = p' := by
    calc G.fromSpecStalk (genericPoint G) ≫ (k ≫ f.toPartialMap.hom) = f.toPartialMap.fromSpecStalkOfMem hm := by
          exact (Category.assoc _ _ _).symm.trans (congrArg (· ≫ f.toPartialMap.hom) e2)
      _ = f.toPartialMap.fromFunctionField := rfl
      _ = p' := by
          rw [← Scheme.RationalMap.fromFunctionField_toRationalMap,
            Scheme.RationalMap.toRationalMap_toPartialMap, hfF]
  refine ⟨k ≫ f.toPartialMap.hom, hg, ?_⟩
  apply ext_of_isDominant (G.fromSpecStalk (genericPoint G))
  rw [← Category.assoc, hg, hp]

private theorem extends_stalk [IsProper t] (p' : Sp G.functionField ⟶ X)
    (hp' : p' ≫ t = G.fromSpecStalk (genericPoint G) ≫ s) (y : G) [IsIntegrallyClosed (G.presheaf.stalk y)]
    (hcen : ∀ (W₁ W₂ : ValuationSubring G.functionField) (q₁ : Sp W₁ ⟶ X) (q₂ : Sp W₂ ⟶ X),
        GlobalTheory.DominatesStalk W₁ y → GlobalTheory.DominatesStalk W₂ y → spMap (algebraMap W₁ G.functionField) ≫ q₁ = p' →
        spMap (algebraMap W₂ G.functionField) ≫ q₂ = p' →
        q₁ (IsLocalRing.closedPoint W₁) = q₂ (IsLocalRing.closedPoint W₂)) :
      ∃ l : Sp (G.presheaf.stalk y) ⟶ X, spMap (algebraMap (G.presheaf.stalk y) G.functionField) ≫ l = p' := by
  have lift : ∀ W : ValuationSubring G.functionField, GlobalTheory.DominatesStalk W y →
      ∃ q : Sp W ⟶ X, spMap (algebraMap W G.functionField) ≫ q = p' := by
    intro W hW
    obtain ⟨l, hl, -⟩ := GlobalTheory.dominatesStalk_iff_exists_hom.mp hW
    have hsq : p' ≫ t = spMap (algebraMap W G.functionField) ≫ (l ≫ s) := by
      rw [hp', ← Category.assoc]
      congr 1
      exact hl.symm
    obtain ⟨q, ⟨-, q1⟩, -⟩ := GlobalTheory.ModelPoints.existsUnique_extension t p' (l ≫ s) hsq
    exact ⟨q, q1⟩
  obtain ⟨W₀, hW₀⟩ := GlobalTheory.exists_dominatesStalk y
  obtain ⟨q₀, hq₀⟩ := lift W₀ hW₀
  obtain ⟨y', hy'⟩ : ∃ y', q₀ (IsLocalRing.closedPoint W₀) = y' := ⟨_, rfl⟩
  obtain ⟨φ₀, hφ₀⟩ := GalCarry.Corr.exists_spec_stalk_of_closedPoint X _ W₀ q₀ hy'
  let χ : X.presheaf.stalk y' →+* G.functionField := (algebraMap W₀ G.functionField).comp φ₀.hom
  have hχ : Spec.map (CommRingCat.ofHom χ) ≫ X.fromSpecStalk y' = p' := by
    rw [← hq₀, ← hφ₀]
    show Spec.map (φ₀ ≫ CommRingCat.ofHom (algebraMap W₀ G.functionField)) ≫ _ = _
    rw [Spec.map_comp, Category.assoc]
  have hmem : ∀ a, χ a ∈ (algebraMap (G.presheaf.stalk y) G.functionField).range := by
    intro a
    refine GalCarry.Corr.mem_range_of_forall_dominatesStalk G y (χ a) (fun W hW => ?_)
    obtain ⟨q, hq⟩ := lift W hW
    obtain ⟨φ, hφ⟩ := GalCarry.Corr.exists_spec_stalk_of_closedPoint X _ W q
      ((hcen W W₀ q q₀ hW hW₀ hq hq₀).trans hy')
    have e : Spec.map (φ ≫ CommRingCat.ofHom (algebraMap W G.functionField)) ≫ X.fromSpecStalk y' =
        Spec.map (CommRingCat.ofHom χ) ≫ X.fromSpecStalk y' := by
      rw [hχ, Spec.map_comp, Category.assoc, hφ, ← hq]
    have e' := Spec.map_injective ((cancel_mono _).mp e)
    have : χ a = algebraMap W G.functionField (φ.hom a) := (congr($(e') a)).symm
    rw [this]
    exact (φ.hom a).2
  let ι := algebraMap (G.presheaf.stalk y) G.functionField
  have hinj : Function.Injective ι := IsFractionRing.injective _ _
  let e := RingEquiv.ofLeftInverse (Function.leftInverse_invFun hinj)
  let ψ : X.presheaf.stalk y' →+* G.presheaf.stalk y :=
    e.symm.toRingHom.comp (χ.codRestrict ι.range hmem)
  have hψ : ι.comp ψ = χ := by
    ext a
    show ι (e.symm ⟨χ a, hmem a⟩) = χ a
    exact congrArg Subtype.val (e.apply_symm_apply ⟨χ a, hmem a⟩)
  refine ⟨Spec.map (CommRingCat.ofHom ψ) ≫ X.fromSpecStalk y', ?_⟩
  rw [← hχ, ← hψ, ← Category.assoc]
  congr 1
  exact (Spec.map_comp (CommRingCat.ofHom ψ) (CommRingCat.ofHom ι)).symm

private theorem exists_common_field {R A B : Type} [CommRing R] [CommRing A] [CommRing B] [IsLocalRing R] [IsLocalRing A]
    [IsLocalRing B] (α : R →+* A) (β : R →+* B) [IsLocalHom α] [IsLocalHom β] :
    ∃ (k : Type) (_ : Field k) (_ : IsAlgClosed k) (ρ : A →+* k) (σ : B →+* k),
      IsLocalHom ρ ∧ IsLocalHom σ ∧ ρ.comp α = σ.comp β := by
  let κ := IsLocalRing.ResidueField R
  letI : Algebra κ (IsLocalRing.ResidueField A) := (IsLocalRing.ResidueField.map α).toAlgebra
  letI : Algebra κ (IsLocalRing.ResidueField B) := (IsLocalRing.ResidueField.map β).toAlgebra
  let T := TensorProduct κ (IsLocalRing.ResidueField A) (IsLocalRing.ResidueField B)
  obtain ⟨m, hm⟩ := Ideal.exists_maximal T
  letI : Field (T ⧸ m) := Ideal.Quotient.field m
  let k := AlgebraicClosure (T ⧸ m)
  let j : T →+* k := (algebraMap (T ⧸ m) k).comp (Ideal.Quotient.mk m)
  let j₁ : IsLocalRing.ResidueField A →+* k := j.comp Algebra.TensorProduct.includeLeftRingHom
  let j₂ : IsLocalRing.ResidueField B →+* k := j.comp Algebra.TensorProduct.includeRight.toRingHom
  have loc : ∀ {C : Type} [CommRing C] [IsLocalRing C] (i : IsLocalRing.ResidueField C →+* k),
      IsLocalHom (i.comp (IsLocalRing.residue C)) := fun i => ⟨fun a ha => by
    by_contra hn
    rw [RingHom.comp_apply, (IsLocalRing.residue_eq_zero_iff a).2 hn, map_zero] at ha
    exact not_isUnit_zero ha⟩
  refine ⟨k, inferInstance, inferInstance, j₁.comp (IsLocalRing.residue A), j₂.comp (IsLocalRing.residue B),
    loc _, loc _, RingHom.ext fun r => ?_⟩
  have h1 : IsLocalRing.residue A (α r) = algebraMap κ _ (IsLocalRing.residue R r) := rfl
  have h2 : IsLocalRing.residue B (β r) = algebraMap κ _ (IsLocalRing.residue R r) := rfl
  simp only [RingHom.comp_apply, h1, h2, j₁, j₂]
  congr 1
  exact (RingHom.congr_fun Algebra.TensorProduct.includeLeftRingHom_comp_algebraMap _)

end Ext

section Frames

open scoped MonObj

attribute [local instance] Over.cartesianMonoidalCategory

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Z : Model Xo c β}

private theorem spMap_comp' {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap (g.comp f) = spMap g ≫ spMap f := by
  rw [← Spec.map_comp]; rfl

private theorem comb_unique {X : Scheme.{0}} {t : SAB H X} {S : Type} [CommRing S] {x : Sp S ⟶ X} {m : ℕ}
    {v : Fin m → (Sp (DualNumber S) ⟶ t.G.left)}
    {a : Fin m → S} {w w' : Sp (DualNumber S) ⟶ t.G.left} (h : IsCombAtG t x v a w) (h' : IsCombAtG t x v a w') :
    w = w' := by
  obtain ⟨u, hu, e⟩ := h
  obtain ⟨u', hu', e'⟩ := h'
  have : u = u' := by
    funext k
    ext1
    exact ((hu k).trans (hu' k).symm)
  subst this
  exact e.symm.trans e'

section Same

variable {R : Type} [CommRing R] {φ : c.F →+* R} {x : Sp R ⟶ Z.X}

private def Same (f g : EigFrame Z φ x) : Prop := ∀ τ, (f.co g τ).BlockTriangular id

private theorem Same.trans {f g k : EigFrame Z φ x} (h : Same f g) (h' : Same g k) : Same f k := fun τ => by
  rw [← f.co_mul g k τ]; exact (h τ).mul (h' τ)

private theorem tri_symm {f g : EigFrame Z φ x} {τ : E →+* ℂ} (h : (f.co g τ).BlockTriangular id) :
    (g.co f τ).BlockTriangular id := by
  have := Matrix.invertibleOfIsUnitDet _ (f.isUnit_det_co g τ)
  rw [← Matrix.inv_eq_right_inv ((f.co_mul g f τ).trans (f.co_self τ))]
  exact Matrix.blockTriangular_inv_of_blockTriangular h

private theorem Same.symm {f g : EigFrame Z φ x} (h : Same f g) : Same g f := fun τ => tri_symm (h τ)

variable {R' : Type} [CommRing R'] {φ' : c.F →+* R'} {x' : Sp R' ⟶ Z.X}

private theorem Same.map {f g : EigFrame Z φ x} (h : Same f g) {ψ : R →+* R'} {f' g' : EigFrame Z φ' x'}
    (hf : f.IsMap ψ f') (hg : g.IsMap ψ g') (hx : x' = spMap ψ ≫ x) : Same f' g' := fun τ i j hij => by
  rw [hf.co τ hg hx, Matrix.map_apply, h τ hij, map_zero]

private theorem Same.of_map {f g : EigFrame Z φ x} {ψ : R →+* R'} (hψ : Function.Injective ψ) {f' g' : EigFrame Z φ' x'}
    (h : Same f' g') (hf : f.IsMap ψ f') (hg : g.IsMap ψ g') (hx : x' = spMap ψ ≫ x) : Same f g := fun τ i j hij => by
  have := h τ hij
  rw [hf.co τ hg hx, Matrix.map_apply] at this
  exact hψ (this.trans (map_zero _).symm)

private theorem Same.tri {f : EigFrame Z φ x} {ψ : R →+* R'} {f' g' : EigFrame Z φ' x'} (h : Same f' g') (hf : f.IsMap ψ f')
    (hφ : φ' = ψ.comp φ) (hx : x' = spMap ψ ≫ x) : ∃ t, f.Tri ψ g' t := by
  have hu (τ i) : IsUnit (f'.co g' τ i i) := by
    have := f'.isUnit_det_co g' τ
    rw [Matrix.det_of_upperTriangular (h τ)] at this
    exact isUnit_of_dvd_unit (Finset.dvd_prod_of_mem (fun i => f'.co g' τ i i) (Finset.mem_univ i)) this
  refine ⟨fun τ i => (hu τ i).unit, hx, hφ, fun τ i => ⟨fun a => f'.co g' τ a i, rfl, fun k hk => h τ hk, ?_⟩⟩
  rw [← funext (hf τ)]
  exact f'.co_spec g' τ i

private theorem isMap_of_comp {R'' : Type} [CommRing R''] {φ'' : c.F →+* R''} {x'' : Sp R'' ⟶ Z.X} {f : EigFrame Z φ x}
    {f' : EigFrame Z φ' x'} {f'' : EigFrame Z φ'' x''} {ψ : R →+* R'} {ψ' : R' →+* R''} {χ : R →+* R''}
    (h : f.IsMap ψ f') (h' : f.IsMap χ f'') (e : χ = ψ'.comp ψ) : f'.IsMap ψ' f'' := fun τ i => by
  rw [h' τ i, h τ i, GlobalTheory.GradedPieces.dual_comp, e]

private theorem exists_co_eq (f : EigFrame Z φ x) (T : ∀ τ : E →+* ℂ, Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) R)
    (hT : ∀ τ, IsUnit (T τ).det) : ∃ g : EigFrame Z φ x, ∀ τ, f.co g τ = T τ := by
  have key (τ) (a : Fin (Dw.mult τ) → R) : ∑ i, a i • ∑ b, T τ b i • f.vec τ b = ∑ b, (T τ).mulVec a b • f.vec τ b := by
    simp only [Finset.smul_sum, smul_smul, Matrix.mulVec, dotProduct, Finset.sum_smul]
    rw [Finset.sum_comm]
    simp only [mul_comm]
  refine ⟨EigFrame.ofVec (fun τ i => ∑ b, T τ b i • f.vec τ b) (fun τ i a => ?_) (fun τ w hw => ?_), fun τ => ?_⟩
  · simp only [map_sum, map_smul, f.act_vec, Finset.smul_sum, smul_smul, mul_comm]
  · obtain ⟨a, ha, hu⟩ := f.existsUnique_sum τ w hw
    refine ⟨(T τ)⁻¹.mulVec a, ?_, fun a' ha' => ?_⟩
    · dsimp only
      rw [key, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ (hT τ), Matrix.one_mulVec]; exact ha
    · dsimp only at ha'
      rw [key] at ha'
      rw [← hu _ ha', Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ (hT τ), Matrix.one_mulVec]
  · exact EigFrame.co_eq fun i => (LieMet.isComb_iff (f.vec τ) _ _).2 rfl

end Same

variable {F : Type} [Field F] {e : F ≃+* c.F}

private theorem carries_of_same (C : FlagCpt Z e) {R K V k : Type} [CommRing R] [CommRing K] [CommRing V] [IsLocalRing V] [Field k]
    (φ₀ : C.Y.Fn →+* K) (ιV : R →+* V) (ν : V →+* K) (hν : Function.Injective ν) (ρ : V →+* k)
    {xR : Sp R ⟶ Z.X} {χ : c.F →+* R} (f : EigFrame Z χ xR) {xK : Sp K ⟶ Z.X} {χK : c.F →+* K}
    (fK vK : EigFrame Z χK xK) (hχ : χK = (ν.comp ιV).comp χ) (hχ' : χK = φ₀.comp (constF e C.Y))
    (hf : f.IsMap (ν.comp ιV) fK) (hv : C.f0.IsMap φ₀ vK) (hs : Same fK vK)
    (hxK : xK = spMap φ₀ ≫ genericPt C.Y ≫ C.π ≫ genι Z)
    (q : Sp V ⟶ C.Y.X) (hq : spMap ν ≫ q = spMap φ₀ ≫ genericPt C.Y) (hqx : q ≫ C.π ≫ genι Z = spMap ιV ≫ xR)
    {xk : Sp k ⟶ Z.X} {χk : c.F →+* k} (g : EigFrame Z χk xk) (hχk : χk = (ρ.comp ιV).comp χ)
    (hxk : xk = spMap (ρ.comp ιV) ≫ xR) (hg : f.IsMap (ρ.comp ιV) g) : C.Carries (spMap ρ ≫ q) g := by
  obtain ⟨y, hy⟩ : ∃ y, q (IsLocalRing.closedPoint V) = y := ⟨_, rfl⟩
  obtain ⟨ψ', hψ'⟩ := GalCarry.Corr.exists_spec_stalk_of_closedPoint C.Y.X y V q hy
  let ψ : C.Y.X.presheaf.stalk y →+* V := ψ'.hom
  have hψ : spMap ψ ≫ stalkPt C.Y y = q := hψ'
  obtain ⟨φ₁, fy, t, hT, -⟩ := C.gr_spec y
  have hg0 : spMap (algebraMap (C.Y.X.presheaf.stalk y) C.Y.X.functionField) ≫ stalkPt C.Y y = genericPt C.Y :=
    spMap_fromSpecStalk y
  have hc : ν.comp ψ = φ₀.comp (algebraMap (C.Y.X.presheaf.stalk y) C.Y.X.functionField) := by
    refine EigLoc.spMap_inj ((cancel_mono (C.Y.X.fromSpecStalk y)).1 ?_)
    rw [spMap_comp', spMap_comp', Category.assoc, Category.assoc]
    exact (congrArg (spMap ν ≫ ·) hψ).trans (hq.trans (congrArg (spMap φ₀ ≫ ·) hg0.symm))
  have hχV : ιV.comp χ = ψ.comp φ₁ := RingHom.ext fun a => hν (by
    have h1 := RingHom.congr_fun (hχ.symm.trans hχ') a
    have h2 := RingHom.congr_fun hc (φ₁ a)
    have h3 := RingHom.congr_fun hT.2.1 a
    simp only [RingHom.comp_apply] at h1 h2 h3 ⊢
    rw [h1, h2, h3])
  have hxV : spMap ιV ≫ xR = spMap ψ ≫ stalkPt C.Y y ≫ C.π ≫ genι Z := by
    rw [← hqx, ← hψ, Category.assoc]
  obtain ⟨fV, hfV⟩ := f.exists_isMap ιV (φ' := ιV.comp χ) (x' := spMap ιV ≫ xR) rfl rfl
  obtain ⟨fyV, hfyV⟩ := fy.exists_isMap ψ hχV hxV
  obtain ⟨fyF, hfyF⟩ := fy.exists_isMap _ hT.2.1 hT.1
  have hxK' : xK = spMap ν ≫ spMap ιV ≫ xR := by
    rw [hxK, ← hqx, ← Category.assoc, ← hq, Category.assoc]
  obtain ⟨fyK, hfyK⟩ := fy.exists_isMap (ν.comp ψ) (φ' := χK) (x' := xK)
    (by rw [hχ, RingHom.comp_assoc, hχV, RingHom.comp_assoc]) (by rw [hxK', hxV, spMap_comp', Category.assoc])
  have s1 : Same fyF C.f0 := fun τ a i h => (hT.co τ hfyF).1 a i h
  have s2 : Same fyK vK := s1.map (isMap_of_comp hfyF hfyK hc) hv hxK
  have s3 : Same fyV fV := (s2.trans hs.symm).of_map hν (isMap_of_comp hfyV hfyK rfl) (isMap_of_comp hfV hf rfl) hxK'
  have hxk' : xk = spMap ρ ≫ spMap ιV ≫ xR := by rw [hxk, spMap_comp', Category.assoc]
  have e1 : χk = (ρ.comp ψ).comp φ₁ := by rw [hχk, RingHom.comp_assoc, hχV, RingHom.comp_assoc]
  have e2 : xk = spMap (ρ.comp ψ) ≫ stalkPt C.Y y ≫ C.π ≫ genι Z := by rw [hxk', hxV, spMap_comp', Category.assoc]
  obtain ⟨fyk, hfyk⟩ := fy.exists_isMap (ρ.comp ψ) e1 e2
  have s4 : Same fyk g := s3.map (isMap_of_comp hfyV hfyk rfl) (isMap_of_comp hfV hg rfl) hxk'
  obtain ⟨t', ht'⟩ := s4.tri hfyk e1 e2
  exact ⟨y, ρ.comp ψ, φ₁, fy, t, t', by rw [spMap_comp', Category.assoc, hψ], hT, ht'⟩

end Frames

section Local

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Z : Model Xo c β}

section Adapt

variable {R K : Type} [CommRing R] [CommRing K] (ψ : R →+* K) (φ : c.F →+* R) (x : Sp R ⟶ Z.X) {φ' : c.F →+* K}
  {x' : Sp K ⟶ Z.X} (v : EigFrame Z φ' x')

private def HasFlagBasis (τ : E →+* ℂ) : Prop :=
  ∃ (u : Fin (Dw.mult τ) → (Sp (DualNumber R) ⟶ Z.t.G.left)) (T : Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) R),
    IsEigBasis Z φ x τ u ∧ IsUnit T.det ∧ ∀ uK fK : EigFrame Z φ' x', (uK.v τ = fun b => spMap (dualMap ψ) ≫ u b) →
      uK.co fK τ = T.map ψ → (fK.co v τ).BlockTriangular id

variable {ψ φ x v}

private theorem exists_same (hφ : φ' = ψ.comp φ) (hx : x' = spMap ψ ≫ x) (h : ∀ τ, HasFlagBasis ψ φ x v τ) :
    ∃ (f : EigFrame Z φ x) (fK : EigFrame Z φ' x'), f.IsMap ψ fK ∧ Same fK v := by
  choose u T hu hT h using h
  let g : EigFrame Z φ x := ⟨u, fun τ i => ((hu τ).1 i).1, fun τ i => ((hu τ).1 i).2, fun τ w h1 h2 => (hu τ).2 w ⟨h1, h2⟩⟩
  obtain ⟨f, hf⟩ := exists_co_eq g T hT
  obtain ⟨gK, hgK⟩ := g.exists_isMap ψ hφ hx
  obtain ⟨fK, hfK⟩ := f.exists_isMap ψ hφ hx
  exact ⟨f, fK, hfK, fun τ => h τ gK fK (funext (hgK τ)) (by rw [hgK.co τ hfK hx, hf])⟩

variable {τ : E →+* ℂ} {m : ℕ} (hr : m = Dw.mult τ) {u : Fin m → (Sp (DualNumber R) ⟶ Z.t.G.left)}
  (hu : IsEigBasis Z φ x τ u) {A : Matrix (Fin m) (Fin m) R} (hA : IsUnit A.det)

include hu hA

private theorem hasFlagBasis_of_comb
    (h : ∀ i, ∃ (w : Sp (DualNumber K) ⟶ Z.t.G.left) (cf : Fin (Dw.mult τ) → K),
      IsCombAtG Z.t x' (fun b => spMap (dualMap ψ) ≫ u b) (fun b => ψ (A b i)) w ∧ IsCombAtG Z.t x' (v.v τ) cf w ∧
        ∀ k, Fin.cast hr i < k → cf k = 0) : HasFlagBasis ψ φ x v τ := by
  subst hr
  refine ⟨u, A, hu, hA, fun uK fK h1 h2 => tri_symm ?_⟩
  choose w cf e1 e2 e3 using h
  have e (i) : w i = fK.v τ i := by
    have := uK.co_spec fK τ i
    rw [h1, h2] at this
    exact comb_unique (e1 i) this
  rw [EigFrame.co_eq (T := Matrix.of fun a i => cf i a) fun i => e i ▸ e2 i]
  exact fun a i hai => e3 i a hai

include hr in

private theorem hasFlagBasis_of_dual
    (h : ∀ (i : Fin m) (k : Fin (Dw.mult τ)) (d : Fin m → K),
      IsCombAtG Z.t x' (fun b => spMap (dualMap ψ) ≫ u b) d (v.v τ k) →
        (k : ℕ) + i + 1 < m → ∑ b, ψ (A b i) * d b = 0) : HasFlagBasis ψ φ x v τ := by
  subst hr
  let A' : Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) R := A.transpose.submatrix Fin.revPerm id
  have hA' : IsUnit A'.det := by
    rw [Matrix.det_permute, Matrix.det_transpose]
    exact ((Equiv.Perm.sign _).isUnit.map (Int.castRingHom R)).mul hA
  refine ⟨u, A'⁻¹, hu, Matrix.isUnit_nonsing_inv_det _ hA', fun uK fK h1 h2 => ?_⟩
  have e : fK.co v τ = A'.map ψ * uK.co v τ := by
    rw [← uK.co_mul fK v τ, h2, ← Matrix.mul_assoc, ← Matrix.map_mul, Matrix.mul_nonsing_inv _ hA',
      Matrix.map_one _ (map_zero ψ) (map_one ψ), Matrix.one_mul]
  rw [e]
  rw [← h1] at h
  exact fun a k hk => h a.rev k _ (uK.co_spec v τ k)
    (by have : (k : ℕ) < a := hk; have := a.2; rw [Fin.val_rev]; omega)

end Adapt

variable {F : Type} [Field F] {e : F ≃+* c.F}

private theorem exists_hom_of_frames {σ : c.F →+* ℂ} {N : ℕ} {U : Formalism.L2.PjFree.Unf Xo c σ N} (Φ : FlagTor Z e U) (i : U.Comp)
    {G : Scheme.{0}} [IsIntegral G] (hN : ∀ g : G, IsIntegrallyClosed (G.presheaf.stalk g)) (b : G ⟶ gen Z)
    (φ₀ : (Φ.C i).Y.Fn →+* G.functionField)
    (h₂ : G.fromSpecStalk (genericPoint G) ≫ b = spMap φ₀ ≫ genericPt (Φ.C i).Y ≫ (Φ.C i).π)
    {xK : Sp G.functionField ⟶ Z.X} (hxK : xK = spMap φ₀ ≫ genericPt (Φ.C i).Y ≫ (Φ.C i).π ≫ genι Z)
    (vK : EigFrame Z (φ₀.comp (constF e (Φ.C i).Y)) xK) (hv : (Φ.C i).f0.IsMap φ₀ vK)
    (hfr : ∀ g : G, ∃ (χ : c.F →+* G.presheaf.stalk g) (xR : Sp (G.presheaf.stalk g) ⟶ Z.X) (f : EigFrame Z χ xR)
      (fK : EigFrame Z (φ₀.comp (constF e (Φ.C i).Y)) xK), xR = G.fromSpecStalk g ≫ b ≫ genι Z ∧
      G.fromSpecStalk g ≫ b ≫ genStr Z = spMap χ ∧
      φ₀.comp (constF e (Φ.C i).Y) = (algebraMap _ G.functionField).comp χ ∧
      f.IsMap (algebraMap _ G.functionField) fK ∧ Same fK vK) :
    ∃ p : G ⟶ (Φ.C i).Y.X, G.fromSpecStalk (genericPoint G) ≫ p = spMap φ₀ ≫ genericPt (Φ.C i).Y ∧
      p ≫ (Φ.C i).π = b := by
  have hZ : IsProper Z.s := projProper O Z.X Z.s Z.proj
  have : IsProper (genStr Z) := inferInstance
  have hsep : (gen Z).IsSeparated := ⟨by rw [← terminal.comp_from (genStr Z)]; infer_instance⟩
  have hdom := isDominant_generic (G := G)
  have hp : (spMap φ₀ ≫ genericPt (Φ.C i).Y) ≫ (Φ.C i).Y.str =
      G.fromSpecStalk (genericPoint G) ≫ b ≫ genStr Z ≫ spMap e.toRingHom := by
    rw [← Category.assoc (G.fromSpecStalk _), h₂, ← (Φ.C i).π_str]
    simp only [Category.assoc]
  obtain ⟨p, hp1, -⟩ := exists_hom_of_extends (b ≫ genStr Z ≫ spMap e.toRingHom) (Φ.C i).Y.str _ hp fun g => by
    have := hN g
    obtain ⟨χ, xR, f, fK, rfl, hχ, hχ', hf, hs⟩ := hfr g
    have key : ∀ (W : ValuationSubring G.functionField) (q : Sp W ⟶ (Φ.C i).Y.X) (j : G.presheaf.stalk g →+* W),
        (∀ a, (j a : G.functionField) = algebraMap _ G.functionField a) →
        spMap (algebraMap W G.functionField) ≫ q = spMap φ₀ ≫ genericPt (Φ.C i).Y →
        ∀ (k : Type) [Field k] (ρ : W →+* k) (r : G.presheaf.stalk g →+* k), ρ.comp j = r →
        ∀ gk : EigFrame Z (r.comp χ) ((spMap r ≫ G.fromSpecStalk g ≫ b) ≫ genι Z), f.IsMap r gk →
          (spMap ρ ≫ q) ≫ (Φ.C i).π = spMap r ≫ G.fromSpecStalk g ≫ b ∧ (Φ.C i).Carries (spMap ρ ≫ q) gk := by
      rintro W q j hj hq k _ ρ _ rfl gk hgk
      have hj' : (algebraMap W G.functionField).comp j = algebraMap _ G.functionField := RingHom.ext hj
      have hinj : Function.Injective (algebraMap W G.functionField) := Subtype.val_injective
      have : IsDominant (spMap (algebraMap W G.functionField)) :=
        ⟨(PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical _).2
          (((RingHom.injective_iff_ker_eq_bot _).1 hinj).le.trans bot_le)⟩
      have hqb : q ≫ (Φ.C i).π = spMap j ≫ G.fromSpecStalk g ≫ b := by
        apply ext_of_isDominant (spMap (algebraMap W G.functionField))
        rw [← Category.assoc, hq, Category.assoc, ← h₂, ← Category.assoc, ← spMap_comp', hj', ← Category.assoc,
          spMap_fromSpecStalk]
      refine ⟨by rw [Category.assoc, hqb, spMap_comp', Category.assoc], ?_⟩
      exact carries_of_same (Φ.C i) φ₀ j (algebraMap W G.functionField) hinj ρ f fK vK (hj' ▸ hχ') rfl (hj' ▸ hf) hv hs
        hxK q hq (by rw [← Category.assoc, hqb]; simp only [Category.assoc]) gk rfl (by simp only [Category.assoc]) hgk
    refine extends_stalk _ _ _ hp g fun W₁ W₂ q₁ q₂ d₁ d₂ e₁ e₂ => ?_
    obtain ⟨j₁, l₁, hj₁⟩ := dominatesStalk_iff_exists_isLocalHom.1 d₁
    obtain ⟨j₂, l₂, hj₂⟩ := dominatesStalk_iff_exists_isLocalHom.1 d₂
    obtain ⟨k, _, _, ρ₁, ρ₂, m₁, m₂, hρ⟩ := exists_common_field j₁ j₂
    obtain ⟨gk, hgk⟩ := f.exists_isMap (ρ₁.comp j₁) (φ' := (ρ₁.comp j₁).comp χ)
      (x' := (spMap (ρ₁.comp j₁) ≫ G.fromSpecStalk g ≫ b) ≫ genι Z) rfl (by simp only [Category.assoc])
    have k₁ := key W₁ q₁ j₁ hj₁ e₁ k ρ₁ _ rfl gk hgk
    have k₂ := key W₂ q₂ j₂ hj₂ e₂ k ρ₂ _ hρ.symm gk hgk
    have hu := (Φ.lifts k _ _ (by rw [spMap_comp' χ, ← hχ]; simp only [Category.assoc]) gk).unique
      (y₁ := ⟨i, spMap ρ₁ ≫ q₁⟩) (y₂ := ⟨i, spMap ρ₂ ≫ q₂⟩) k₁ k₂
    have hq : spMap ρ₁ ≫ q₁ = spMap ρ₂ ≫ q₂ := eq_of_heq (Sigma.mk.inj hu).2
    have h3 : q₁ (spMap ρ₁ (IsLocalRing.closedPoint k)) = q₂ (spMap ρ₂ (IsLocalRing.closedPoint k)) :=
      congrArg (fun t : Sp k ⟶ (Φ.C i).Y.X => t (IsLocalRing.closedPoint k)) hq
    have h4 : spMap ρ₁ (IsLocalRing.closedPoint k) = IsLocalRing.closedPoint W₁ := IsLocalRing.comap_closedPoint ρ₁
    have h5 : spMap ρ₂ (IsLocalRing.closedPoint k) = IsLocalRing.closedPoint W₂ := IsLocalRing.comap_closedPoint ρ₂
    rwa [h4, h5] at h3
  refine ⟨p, hp1, ?_⟩
  apply ext_of_isDominant (G.fromSpecStalk (genericPoint G))
  rw [← Category.assoc, hp1, h₂, Category.assoc]

end Local

private theorem embB_surjective (D : D7) : Function.Surjective (embB D) := fun τ => by
  obtain ⟨g, hg⟩ := (factEmb D.R D.host).1.2 τ
  by_cases hgP : g ∈ D.R.Psi
  · obtain ⟨t, ht⟩ := (Formalism.L2.Geo.exists_tauEmb_iff D g).2 hgP
    exact ⟨(t, true), ht.symm.trans hg⟩
  · have h2 : g * D.R.cc ∈ D.R.Psi := by
      by_contra h
      exact hgP ((Formalism.L2.Geo.mem_Psi_iff_mul_cc_notMem g).2 h)
    obtain ⟨t, ht⟩ := (Formalism.L2.Geo.exists_tauEmb_iff D (g * D.R.cc)).2 h2
    refine ⟨(t, false), RingHom.ext fun z => ?_⟩
    show starRingEnd ℂ (DV.tauEmb D t z) = τ z
    rw [← ht, Formalism.L2.Geo.emb_mul_cc_comp, hg, RingHom.comp_apply]
    exact (congrArg (starRingEnd ℂ) (Formalism.MainNotions.WeightFamilies.emb_conj D τ z)).trans (star_star _)

private theorem hasFlagBasis_stalk {D : D7} {O : Setup D} {c : O.s.Comp} {Bs : Scheme.{0}}
    {E : D.what₂.Tau × Bool → Bs.Modules} (hE : ∀ a, IsVB (E a) (rkB D.what₂.Tau O.N O.j a))
    {Bg : Scheme.{0}} {jB : Bg ⟶ Bs} {πB : Bg ⟶ gen O.s.T.Z}
    {u : ∀ a, FrAssign O.s.T.Z (E a) (rkB D.what₂.Tau O.N O.j a) jB}
    (frB : ∀ a, IsLieFrames O.s.T.Z O.κ.e jB πB (E a) _ (embB D a) (!a.2) (u a))
    {Y₀ : Scheme.{0}} {π₀ : Y₀ ⟶ Bs}
    (fl₀ : ∀ a, Vert.Flag ((Scheme.Modules.pullback π₀).obj (E a)) (rkB D.what₂.Tau O.N O.j a))
    {G : Scheme.{0}} [IsIntegral G] {j : G ⟶ Y₀} {φ : (O.var c).Fn →+* G.functionField} {jG : G ⟶ Bg}
    (c1 : jG ≫ jB = j ≫ π₀) (a : D.what₂.Tau × Bool) (hr : rkB D.what₂.Tau O.N O.j a = O.S.Dw.mult (embB D a))
    (c3 : ∀ i, ∃ r : (((fl₀ a).root i).pull j).ι → G.functionFieldˣ,
      GlobalTheory.FlagCov.IsFrameSec hE jB πB u π₀ fl₀ j φ jG a i hr r)
    (x : G) (ψ₀ : D.what₂.LL →+* G.presheaf.stalk x)
    (hψ₀ : (G.fromSpecStalk x ≫ jG) ≫ πB ≫ genStr O.s.T.Z ≫ spMap O.κ.e.toRingHom = spMap ψ₀)
    (v : EigFrame O.s.T.Z (φ.comp (constF O.κ.e (O.Φ.C c).Y)) (FlagCov.genPt G ≫ jG ≫ πB ≫ genι O.s.T.Z))
    (e2 : (O.Φ.C c).f0.IsMap φ v) :
    HasFlagBasis (algebraMap (G.presheaf.stalk x) G.functionField) (ψ₀.comp O.κ.e.symm.toRingHom)
      ((G.fromSpecStalk x ≫ jG) ≫ πB ≫ genι O.s.T.Z) v (embB D a) := by
  choose r c3 using c3
  have hqc := (hE a).isQuasicoherent
  obtain ⟨V, f, hV, hf⟩ := hE a (π₀ (j x))
  obtain ⟨cc, W, hWV, hW, s, hxW, hs, hfr⟩ : ∃ (cc : ∀ k, (((fl₀ a).root k).pull j).ι) (W : Y₀.Opens)
      (_ : W ≤ π₀ ⁻¹ᵁ V) (hW : ∀ k, W ≤ (cc k PUnit.unit).U) (s : ∀ k : Fin (rkB D.what₂.Tau O.N O.j a), Γ((fl₀ a).F k.succ, W)), j x ∈ W ∧
      (∀ k, ((fl₀ a).π k).app W (s k) = Twist.resM _ (hW k) ((cc k PUnit.unit).e 0)) ∧
      IsFrame fun k : Fin (rkB D.what₂.Tau O.N O.j a) => ((fl₀ a).ι k.succ).app W (s k) := by
    obtain ⟨h1, h2⟩ := UpperTheory.exists_adapted_flag_charts _ _ _ (fl₀ a)
    obtain ⟨ch, hx, hch⟩ := h1 (j x)
    choose t ht using id hch
    refine ⟨fun k _ => ⟨ch.U, _, h2 ch hch k (t k) (ht k)⟩, ch.U ⊓ π₀ ⁻¹ᵁ V, inf_le_right, fun _ => inf_le_left,
      fun k => Twist.resM _ inf_le_left (t k), ⟨hx, hV⟩, fun k => Twist.app_resM _ _ _, ?_⟩
    simp only [Twist.app_resM, ht]
    exact ch.isFrame.res _
  let ψ := algebraMap (G.presheaf.stalk x) G.functionField
  have hg : FlagCov.genPt G = spMap ψ ≫ G.fromSpecStalk x := (spMap_fromSpecStalk x).symm
  have hst {U : G.Opens} (hU : x ∈ U) : ⊤ ≤ G.fromSpecStalk x ⁻¹ᵁ U := fun w _ => by
    have : G.fromSpecStalk x w ∈ Set.range (G.fromSpecStalk x) := ⟨w, rfl⟩
    rw [Scheme.range_fromSpecStalk] at this
    exact Specializes.mem_open (x := G.fromSpecStalk x w) this U.isOpen hU
  have hRW : ⊤ ≤ (G.fromSpecStalk x ≫ j) ⁻¹ᵁ W := hst (U := j ⁻¹ᵁ W) hxW
  have hRV : ⊤ ≤ ((G.fromSpecStalk x ≫ jG) ≫ jB) ⁻¹ᵁ V := by
    rw [Category.assoc, c1]
    exact hst (U := (j ≫ π₀) ⁻¹ᵁ V) hV
  have hKW : ⊤ ≤ (FlagCov.genPt G ≫ j) ⁻¹ᵁ W := by
    rw [hg, Category.assoc]
    exact fun w _ => hRW (x := spMap ψ w) trivial
  have hKV' : ⊤ ≤ ((spMap ψ ≫ G.fromSpecStalk x ≫ jG) ≫ jB) ⁻¹ᵁ V := by
    rw [Category.assoc]
    exact fun w _ => hRV (x := spMap ψ w) trivial
  have hgj : FlagCov.genPt G ≫ jG = spMap ψ ≫ G.fromSpecStalk x ≫ jG := by rw [hg, Category.assoc]
  have hKV : ⊤ ≤ ((FlagCov.genPt G ≫ jG) ≫ jB) ⁻¹ᵁ V := hgj ▸ hKV'
  have hu := (frB a).1 V f hf _ (G.fromSpecStalk x ≫ jG) hRV ψ₀ hψ₀
  have hu' : u a V f hf G.functionField (FlagCov.genPt G ≫ jG) hKV =
      fun b => spMap (dualMap ψ) ≫ u a V f hf _ (G.fromSpecStalk x ≫ jG) hRV b := by
    have key : ∀ (y : Sp G.functionField ⟶ Bg) (hy : ⊤ ≤ (y ≫ jB) ⁻¹ᵁ V), y = spMap ψ ≫ G.fromSpecStalk x ≫ jG →
        u a V f hf G.functionField y hy = fun b => spMap (dualMap ψ) ≫ u a V f hf _ (G.fromSpecStalk x ≫ jG) hRV b := by
      rintro y hy rfl
      exact funext ((frB a).2.2 V f hf _ _ ψ _ hRV hy)
    exact key _ _ hgj
  let A₀ := ((hf.pullback π₀).basis hWV).toMatrix fun k => ((fl₀ a).ι k.succ).app W (s k)
  have hA₀ : IsUnit A₀.det := by
    have := ((hf.pullback π₀).detUnit hfr hWV le_rfl).isUnit
    simpa only [IsFrame.val_detUnit, Twist.resM_self, Module.Basis.det_apply] using this
  let A := A₀.map (TangentOrigin.evalPt (G.fromSpecStalk x ≫ j) W hRW)
  have hA : IsUnit A.det := by
    have := hA₀.map (TangentOrigin.evalPt (G.fromSpecStalk x ≫ j) W hRW)
    rwa [RingHom.map_det] at this
  have hev (k) : (fun b => TangentOrigin.evalPt (FlagCov.genPt G ≫ j) W hKW
      (((hf.pullback π₀).basis hWV).repr (((fl₀ a).ι k.succ).app W (s k)) b)) = fun b => ψ (A b k) := by
    have key : ∀ (y : Sp G.functionField ⟶ Y₀) (hy : ⊤ ≤ y ⁻¹ᵁ W), y = spMap ψ ≫ G.fromSpecStalk x ≫ j → ∀ z,
        TangentOrigin.evalPt y W hy z = ψ (TangentOrigin.evalPt (G.fromSpecStalk x ≫ j) W hRW z) := by
      rintro y hy rfl z
      exact TangentOrigin.evalPt_spMap_comp ψ _ W hRW hy z
    exact funext fun b => key _ _ (by rw [hg, Category.assoc]) _
  have hsec (k) := c3 k (cc k) V f hf W (hW k) hWV (s k) (hs k) hKW hKV
  have hv : (fun k => spMap (dualMap φ) ≫ (O.Φ.C c).f0.v (embB D a) k) = v.v (embB D a) := (funext (e2 _)).symm
  obtain ⟨τ, _ | _⟩ := a
  · refine hasFlagBasis_of_dual hr hu hA fun k k' d hd => ?_
    have := (hsec k k' d (by rw [hu', hv]; exact hd)).1
    simpa only [fun b => congrFun (hev k) b] using this
  · refine hasFlagBasis_of_comb hr hu hA fun k => ?_
    have := hsec k
    simp only [cond_true] at this
    rw [hu', hv, hev] at this
    obtain ⟨w, cf, h1, h2, -, h4⟩ := this
    exact ⟨w, cf, h1, h2, h4⟩

private theorem isIntegrallyClosed_stalk_Gf {D : D7} {Bs Y₀ : Scheme.{0}} (q : Bs ⟶ Sp (𝓞 D.what₂.LL)) (π₀ : Y₀ ⟶ Bs)
    (n₀ : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme Y₀) (g : FlagGenFib.Gf q π₀) :
    IsIntegrallyClosed ((FlagGenFib.Gf q π₀).presheaf.stalk g) := by
  have : IsPreimmersion (spMap (algebraMap (𝓞 D.what₂.LL) D.what₂.LL)) :=
    IsPreimmersion.of_isLocalization (nonZeroDivisors (𝓞 D.what₂.LL)) (S := D.what₂.LL)
  have : Flat (spMap (algebraMap (𝓞 D.what₂.LL) D.what₂.LL)) := by
    refine (HasRingHomProperty.Spec_iff (P := @Flat)).2 ?_
    exact RingHom.flat_algebraMap_iff.2 (IsLocalization.flat _ (nonZeroDivisors (𝓞 D.what₂.LL)))
  have : IsPreimmersion (FlagGenFib.jf q π₀) := by unfold FlagGenFib.jf FlagGenFib.Gf; infer_instance
  have : Flat (FlagGenFib.jf q π₀) := by unfold FlagGenFib.jf FlagGenFib.Gf; infer_instance
  have := isIso_stalkMap_of_flat_of_surjectiveOnStalks (FlagGenFib.jf q π₀)
  have : GlobalTheory.IsNormalScheme Y₀ := ⟨fun y => (n₀ y).1, fun y => (n₀ y).2⟩
  exact (GlobalTheory.IsNormalScheme.of_isIso_stalkMap (FlagGenFib.jf q π₀)).isIntegrallyClosed_stalk g

private theorem exists_extension : ∀ (P2 : Hypotheses2) (PH : HypothesesH) (RA : RegularAlteration) (SW : ScholzeWeinsteinB)
    (D : D7) (O : Setup D) (hO : O.Core) (B : ℝ) (hB : 2 ≤ B) (R : ℝ) (hR : 2 ≤ R) (c : O.s.Comp)
    (Bs : Scheme.{0}) [IsIntegral Bs] (q : Bs ⟶ Sp (𝓞 D.what₂.LL)) (arq : IsArithVar q (dimGr D.what₂.Tau O.N O.j))
    (nBs : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme Bs) (E : D.what₂.Tau × Bool → Bs.Modules)
    (h : ∀ a, VMetric q (E a) (rkB D.what₂.Tau O.N O.j a)) (H : ∀ a, (h a).IsCInf)
    (Bg : Scheme.{0}) (jB : Bg ⟶ Bs) (πB : Bg ⟶ gen O.s.T.Z)
    (u : ∀ a, FrAssign O.s.T.Z (E a) (rkB D.what₂.Tau O.N O.j a) jB) (Gm : ∀ σ', EigMet O.s.T.Z σ')
    (hL : GlobalTheory.FlagCov.LieWit O B R c q E h jB πB u Gm)
    (Y₀ : Scheme.{0}) [IsIntegral Y₀] (π₀ : Y₀ ⟶ Bs)
    (fl₀ : ∀ a, Vert.Flag ((Scheme.Modules.pullback π₀).obj (E a)) (rkB D.what₂.Tau O.N O.j a))
    (hfb : IsFlagBundle π₀ E (rkB D.what₂.Tau O.N O.j) fl₀) (ar₀ : IsArithVar (π₀ ≫ q) (O.var c).dim)
    (n₀ : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme Y₀) [IsIntegral (GlobalTheory.FlagGenFib.Gf q π₀)] (φ₀ : (O.var c).Fn →+* (GlobalTheory.FlagGenFib.Gf q π₀).functionField)
    (h₁ : (GlobalTheory.FlagGenFib.Gf q π₀).fromSpecStalk (genericPoint _) ≫ GlobalTheory.FlagGenFib.sf q π₀ =
        spMap φ₀ ≫ (O.var c).X.fromSpecStalk (genericPoint (O.var c).X) ≫ (O.var c).str)
    (h₂ : (GlobalTheory.FlagGenFib.Gf q π₀).fromSpecStalk (genericPoint _) ≫ GlobalTheory.FlagGenFib.jGf q π₀ jB _ hL.1 ≫ πB =
        spMap φ₀ ≫ (O.var c).X.fromSpecStalk (genericPoint (O.var c).X) ≫ (O.Φ.C c).π)
    (h₃ : ∀ a i (hr : rkB D.what₂.Tau O.N O.j a = O.S.Dw.mult (embB D a)),
          ∃ r : (((fl₀ a).root i).pull (GlobalTheory.FlagGenFib.jf q π₀)).ι → (GlobalTheory.FlagGenFib.Gf q π₀).functionFieldˣ,
            GlobalTheory.FlagCov.IsFrameSec (fun a => (h a).isVB) jB πB u π₀ fl₀ (GlobalTheory.FlagGenFib.jf q π₀) φ₀
              (GlobalTheory.FlagGenFib.jGf q π₀ jB _ hL.1) a i hr r), ∃ πG : (GlobalTheory.FlagGenFib.Gf q π₀) ⟶ (O.var c).X,
      πG ≫ (O.var c).str = GlobalTheory.FlagGenFib.sf q π₀ ∧
      GlobalTheory.FlagGenFib.jGf q π₀ jB _ hL.1 ≫ πB = πG ≫ (O.Φ.C c).π ∧
      (GlobalTheory.FlagGenFib.Gf q π₀).fromSpecStalk (genericPoint _) ≫ πG = spMap φ₀ ≫ (O.var c).X.fromSpecStalk (genericPoint (O.var c).X) := by
  intro _ _ _ _ D O _ B _ R _ c Bs _ q _ _ E h _ Bg jB πB u Gm hL Y₀ _ π₀ fl₀ _ _ n₀ _ φ₀ h₁ h₂ h₃
  have hs : FlagGenFib.jGf q π₀ jB _ hL.1 ≫ πB ≫ genStr O.s.T.Z ≫ spMap O.κ.e.toRingHom = FlagGenFib.sf q π₀ :=
    hL.1.lift_snd _ _ _
  have c1 := FlagGenFib.jGf_jB q π₀ jB _ hL.1
  have frB := hL.2.2.2.1
  have hr := fun a => (hL.2.2.2.2.2.2 a).1
  generalize FlagGenFib.jGf q π₀ jB _ hL.1 = jG at *
  have hN := isIntegrallyClosed_stalk_Gf q π₀ n₀
  generalize FlagGenFib.jf q π₀ = j at *
  generalize FlagGenFib.sf q π₀ = s at *
  generalize FlagGenFib.Gf q π₀ = G at *
  have hxK : FlagCov.genPt G ≫ jG ≫ πB ≫ genι O.s.T.Z =
      spMap φ₀ ≫ genericPt (O.Φ.C c).Y ≫ (O.Φ.C c).π ≫ genι O.s.T.Z := by
    have := congrArg (· ≫ genι O.s.T.Z) h₂
    simp only [Category.assoc] at this
    exact this
  obtain ⟨v, hv⟩ := (O.Φ.C c).f0.exists_isMap φ₀ rfl hxK
  have hg : genericPt (O.Φ.C c).Y ≫ (O.Φ.C c).Y.str = spMap (algebraMap D.what₂.LL (O.Φ.C c).Y.Fn) :=
    (GlobalTheory.FlagBundle.ratOf (O.Φ.C c).Y).pt_s
  have he : spMap O.κ.e.toRingHom ≫ spMap O.κ.e.symm.toRingHom = 𝟙 _ := by
    rw [← Spec.map_comp, ← Spec.map_id]
    exact congrArg Spec.map (CommRingCat.hom_ext (RingHom.ext O.κ.e.apply_symm_apply))
  obtain ⟨p, hp1, hp2⟩ := exists_hom_of_frames O.Φ c hN (jG ≫ πB) φ₀ h₂ hxK v hv fun x => by
    obtain ⟨ψ₀, hψ₀⟩ : ∃ ψ₀ : D.what₂.LL →+* G.presheaf.stalk x, G.fromSpecStalk x ≫ s = spMap ψ₀ :=
      ⟨(Spec.preimage (G.fromSpecStalk x ≫ s)).hom, (Spec.map_preimage _).symm⟩
    have e1 : (algebraMap (G.presheaf.stalk x) G.functionField).comp ψ₀ =
        φ₀.comp (algebraMap D.what₂.LL (O.Φ.C c).Y.Fn) := by
      refine EigLoc.spMap_inj ?_
      rw [spMap_comp', spMap_comp', ← hψ₀, ← hg, ← Category.assoc, spMap_fromSpecStalk]
      exact h₁
    have e2 : φ₀.comp (constF O.κ.e (O.Φ.C c).Y) =
        (algebraMap (G.presheaf.stalk x) G.functionField).comp (ψ₀.comp O.κ.e.symm.toRingHom) := by
      rw [← RingHom.comp_assoc, e1]; rfl
    have e3 : (G.fromSpecStalk x ≫ jG) ≫ πB ≫ genStr O.s.T.Z ≫ spMap O.κ.e.toRingHom = spMap ψ₀ := by
      rw [Category.assoc, hs, hψ₀]
    obtain ⟨f, fK, hf, hS⟩ := exists_same (v := v) (x := (G.fromSpecStalk x ≫ jG) ≫ πB ≫ genι O.s.T.Z) e2
      (((congrArg (· ≫ jG ≫ πB ≫ genι O.s.T.Z) (spMap_fromSpecStalk x).symm).trans (Category.assoc _ _ _)).trans
        (congrArg (spMap _ ≫ ·) (Category.assoc _ _ _).symm))
      fun τ => by
        obtain ⟨a, rfl⟩ := embB_surjective D τ
        exact hasFlagBasis_stalk (fun a => (h a).isVB) frB fl₀ c1 a (hr a) (fun i => h₃ a i (hr a)) x ψ₀ e3 v hv
    refine ⟨_, _, f, fK, (Category.assoc _ _ _).trans (congrArg _ (Category.assoc _ _ _).symm), ?_, e2, hf, hS⟩
    rw [spMap_comp', ← e3]
    simp only [Category.assoc]
    rw [he, Category.comp_id]
  refine ⟨p, ?_, hp2.symm, hp1⟩
  rw [← hs, ← Category.assoc jG, ← hp2, Category.assoc]
  exact congrArg (p ≫ ·) (O.Φ.C c).π_str.symm

end GlobalTheory.FlagExt

end

theorem _root_.GlobalTheory.T.arithmetic_bundle_height_limit : ∀ (P2 : Hypotheses2) (PH : HypothesesH) (RA : RegularAlteration) (SW : ScholzeWeinsteinB)
    (D : D7) (O : Setup D) (hO : O.Core) (B : ℝ) (hB : 2 ≤ B) (R : ℝ) (hR : 2 ≤ R) (c : O.s.Comp)
    (Bs : Scheme.{0}) [IsIntegral Bs] (q : Bs ⟶ Sp (𝓞 D.what₂.LL)) (arq : IsArithVar q (dimGr D.what₂.Tau O.N O.j))
    (nBs : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme Bs) (E : D.what₂.Tau × Bool → Bs.Modules)
    (h : ∀ a, VMetric q (E a) (rkB D.what₂.Tau O.N O.j a)) (H : ∀ a, (h a).IsCInf)
    (Bg : Scheme.{0}) (jB : Bg ⟶ Bs) (πB : Bg ⟶ gen O.s.T.Z)
    (u : ∀ a, FrAssign O.s.T.Z (E a) (rkB D.what₂.Tau O.N O.j a) jB) (Gm : ∀ σ', EigMet O.s.T.Z σ')
    (hL : GlobalTheory.FlagCov.LieWit O B R c q E h jB πB u Gm)
    (Y₀ : Scheme.{0}) [IsIntegral Y₀] (π₀ : Y₀ ⟶ Bs)
    (fl₀ : ∀ a, Vert.Flag ((Scheme.Modules.pullback π₀).obj (E a)) (rkB D.what₂.Tau O.N O.j a))
    (hfb : IsFlagBundle π₀ E (rkB D.what₂.Tau O.N O.j) fl₀) (ar₀ : IsArithVar (π₀ ≫ q) (O.var c).dim)
    (n₀ : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme Y₀) [IsIntegral (GlobalTheory.FlagGenFib.Gf q π₀)] (φ₀ : (O.var c).Fn →+* (GlobalTheory.FlagGenFib.Gf q π₀).functionField)
    (h₁ : (GlobalTheory.FlagGenFib.Gf q π₀).fromSpecStalk (genericPoint _) ≫ GlobalTheory.FlagGenFib.sf q π₀ =
        spMap φ₀ ≫ (O.var c).X.fromSpecStalk (genericPoint (O.var c).X) ≫ (O.var c).str)
    (h₂ : (GlobalTheory.FlagGenFib.Gf q π₀).fromSpecStalk (genericPoint _) ≫ GlobalTheory.FlagGenFib.jGf q π₀ jB _ hL.1 ≫ πB =
        spMap φ₀ ≫ (O.var c).X.fromSpecStalk (genericPoint (O.var c).X) ≫ (O.Φ.C c).π)
    (h₃ : ∀ a i (hr : rkB D.what₂.Tau O.N O.j a = O.S.Dw.mult (embB D a)),
          ∃ r : (((fl₀ a).root i).pull (GlobalTheory.FlagGenFib.jf q π₀)).ι → (GlobalTheory.FlagGenFib.Gf q π₀).functionFieldˣ,
            GlobalTheory.FlagCov.IsFrameSec (fun a => (h a).isVB) jB πB u π₀ fl₀ (GlobalTheory.FlagGenFib.jf q π₀) φ₀
              (GlobalTheory.FlagGenFib.jGf q π₀ jB _ hL.1) a i hr r), ∃ πG : (GlobalTheory.FlagGenFib.Gf q π₀) ⟶ (O.var c).X,
      πG ≫ (O.var c).str = GlobalTheory.FlagGenFib.sf q π₀ ∧
      GlobalTheory.FlagGenFib.jGf q π₀ jB _ hL.1 ≫ πB = πG ≫ (O.Φ.C c).π ∧
      (GlobalTheory.FlagGenFib.Gf q π₀).fromSpecStalk (genericPoint _) ≫ πG = spMap φ₀ ≫ (O.var c).X.fromSpecStalk (genericPoint (O.var c).X) :=
  GlobalTheory.FlagExt.exists_extension
