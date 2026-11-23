import Development.EtaleCohomology.EtaleSheaves.LeafGeoVCut

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite LateralTheory.E.E4

namespace LateralTheory.E.LeafCurveVCut

def LeafFibreField : Prop := ∀ (k : Type) [Field k] {X : Scheme.{0}} [IsIntegral X] (p : X ⟶ Sp k) [IsProper p],
  0 < topologicalKrullDim X → ∃ (F : Type) (_ : Field F) (_ : Algebra k F) (K : Type) (_ : Field K) (_ : Algebra F K)
    (n : ℕ) (s : Finset F) (t : K) (η : Sp K ⟶ X), (n : WithBot ℕ∞) < topologicalKrullDim X ∧ s.card ≤ n ∧
    Algebra.IsAlgebraic (IntermediateField.adjoin k (s : Set F)) F ∧ Transcendental F t ∧
    FiniteDimensional (IntermediateField.adjoin F {t}) K ∧
    η ≫ p = Spec.map (CommRingCat.ofHom ((algebraMap F K).comp (algebraMap k F))) ∧ genericPoint X ∈ Set.range η

def LeafTrdegDim : Prop := ∀ (k F Ω : Type) [Field k] [Field F] [Field Ω] [Algebra k F] [Algebra F Ω] [Algebra k Ω]
  [IsScalarTower k F Ω] [Algebra.IsAlgebraic F Ω] (n : ℕ) (s : Finset F), s.card ≤ n →
    Algebra.IsAlgebraic (IntermediateField.adjoin k (s : Set F)) F →
    ∀ R : Subalgebra k Ω, R.FG → ringKrullDim R ≤ n

def LeafBaseChangeField : Prop := ∀ (F Ω K : Type) [Field F] [Field Ω] [Field K] [Algebra F Ω] [Algebra F K] (t : K),
  Transcendental F t → FiniteDimensional (IntermediateField.adjoin F {t}) K →
    ∃ (L : Type) (_ : Field L) (_ : Algebra Ω L) (u : L) (φ : K →+* L), Transcendental Ω u ∧
      FiniteDimensional (IntermediateField.adjoin Ω {u}) L ∧ φ.comp (algebraMap F K) = (algebraMap Ω L).comp (algebraMap F Ω)

def LeafModelCurve : Prop := ∀ (Ω L : Type) [Field Ω] [IsAlgClosed Ω] [Field L] [Algebra Ω L] (u : L),
  Transcendental Ω u → FiniteDimensional (IntermediateField.adjoin Ω {u}) L →
    ∃ (C0 : Scheme.{0}) (c0 : C0 ⟶ Sp Ω) (x : C0) (ψ : Spec (C0.presheaf.stalk x) ⟶ Sp L), IsCurve c0 ∧
      IsGenericPoint x (⊤ : Set C0) ∧ ψ ≫ Spec.map (CommRingCat.ofHom (algebraMap Ω L)) = C0.fromSpecStalk x ≫ c0

def LeafExtend : Prop := ∀ (k Ω : Type) [Field k] [Field Ω] [Algebra k Ω] {X C0 : Scheme.{0}} (p : X ⟶ Sp k)
  [IsProper p] (c0 : C0 ⟶ Sp Ω) (x : C0), IsCurve c0 → IsGenericPoint x (⊤ : Set C0) →
    ∀ ψ : Spec (C0.presheaf.stalk x) ⟶ X,
      ψ ≫ p = C0.fromSpecStalk x ≫ c0 ≫ Spec.map (CommRingCat.ofHom (algebraMap k Ω)) →
      ∃ e : C0 ⟶ X, C0.fromSpecStalk x ≫ e = ψ ∧ e ≫ p = c0 ≫ Spec.map (CommRingCat.ofHom (algebraMap k Ω))

theorem goal_of (hA : LeafFibreField) (hT : LeafTrdegDim) (hB1 : LeafBaseChangeField) (hB2 : LeafModelCurve)
    (hC : LeafExtend) : LateralTheory.E.LeafGeoVCut.LeafCurveV := by
  intro k _ _ X _ p _ hd
  obtain ⟨F, _, _, K, _, _, n, s, t, η, hn, hs, halg, ht, hfin, hη, hgen⟩ := hA k p hd
  obtain ⟨L, _, _, u, φ, hu, hufin, hφ⟩ := hB1 F (AlgebraicClosure F) K t ht hfin
  obtain ⟨C0, c0, x, ψ, hc0, hx, hψ⟩ := hB2 (AlgebraicClosure F) L u hu hufin
  have hring : CommRingCat.ofHom ((algebraMap F K).comp (algebraMap k F)) ≫ CommRingCat.ofHom φ =
      CommRingCat.ofHom (algebraMap k (AlgebraicClosure F)) ≫ CommRingCat.ofHom (algebraMap (AlgebraicClosure F) L) := by
    ext a
    have := congrArg (fun f => f (algebraMap k F a)) hφ
    simp only [RingHom.coe_comp, Function.comp_apply] at this
    simp only [CommRingCat.hom_comp, CommRingCat.hom_ofHom, RingHom.coe_comp, Function.comp_apply, this,
      IsScalarTower.algebraMap_apply k F (AlgebraicClosure F)]
  have hcompat : (ψ ≫ Spec.map (CommRingCat.ofHom φ) ≫ η) ≫ p =
      C0.fromSpecStalk x ≫ c0 ≫ Spec.map (CommRingCat.ofHom (algebraMap k (AlgebraicClosure F))) := by
    rw [Category.assoc, Category.assoc, hη, ← Spec.map_comp, hring, Spec.map_comp, ← Category.assoc, hψ,
      Category.assoc]
  obtain ⟨e, he1, he2⟩ := hC k (AlgebraicClosure F) p c0 x hc0 hx _ hcompat
  refine ⟨AlgebraicClosure F, inferInstance, inferInstance, inferInstance, C0, c0, e, hc0, he2, ?_, ?_⟩
  · obtain ⟨z, hz⟩ := hgen
    let w : Spec (C0.presheaf.stalk x) := IsLocalRing.closedPoint (C0.presheaf.stalk x)
    refine ⟨C0.fromSpecStalk x w, ?_⟩
    rw [← Scheme.Hom.comp_apply, he1, ← hz]
    simp only [Scheme.Hom.comp_apply]
    congr 1
    exact Subsingleton.elim _ _
  · intro R hR
    exact lt_of_le_of_lt (hT k F (AlgebraicClosure F) n s hs halg R hR) hn

end LateralTheory.E.LeafCurveVCut

end
