import Development.EtaleCohomology.CohomologicalPurity.LeafWEqvRPf

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.CohomologicalPurity.Thom.ExcP.Chart

abbrev vtx (n : ℕ) (i : Fin (n + 1)) : SimplexCategory.mk 0 ⟶ SimplexCategory.mk n :=
  SimplexCategory.const _ _ i

def LeafCechRec : Prop := ∀ (X : Spc) (P Z : PSh) (φ : P ⟶ Z) (r : X ⟶ disc.obj Z)
  (g : X.obj (op (SimplexCategory.mk 0)) ⟶ P), g ≫ φ = r.app (op (SimplexCategory.mk 0)) →
  (∀ (n : ℕ) (U : Scheme.{0}ᵒᵖ) (x x' : (X.obj (op (SimplexCategory.mk n))).obj U),
    (∀ i, g.app U ((X.map (vtx n i).op).app U x) = g.app U ((X.map (vtx n i).op).app U x')) → x = x') →
  (∀ (n : ℕ) (U : Scheme.{0}ᵒᵖ) (y : Fin (n + 1) → P.obj U) (z : Z.obj U), (∀ i, φ.app U (y i) = z) →
    ∃ x, ∀ i, g.app U ((X.map (vtx n i).op).app U x) = y i) →
  ∃ ψ : X ⟶ (Arrow.mk φ).cechNerve, IsIso ψ ∧ ψ ≫ (Arrow.mk φ).augmentedCechNerve.hom = r

def LeafWData : Prop := ∀ (d : ℕ) (R : Type) [CommRing R],
  ∃ (r : W d R ⟶ disc.obj (yoneda.obj (Spec (CommRingCat.of (MvPolynomial (Fin d) R)))))
    (g : (W d R).obj (op (SimplexCategory.mk 0)) ⟶
      yoneda.obj (Spec (CommRingCat.of (LaurentPolynomial (MvPolynomial (Fin d) R))))),
    wa d R ≫ r = 𝟙 _ ∧ g ≫ yoneda.map (fW d R) = r.app (op (SimplexCategory.mk 0)) ∧
    (∀ (n : ℕ) (U : Scheme.{0}ᵒᵖ) (x x' : ((W d R).obj (op (SimplexCategory.mk n))).obj U),
      (∀ i, g.app U (((W d R).map (vtx n i).op).app U x) = g.app U (((W d R).map (vtx n i).op).app U x')) →
        x = x') ∧
    (∀ (n : ℕ) (U : Scheme.{0}ᵒᵖ) (y : Fin (n + 1) → (yoneda.obj (Spec (CommRingCat.of
        (LaurentPolynomial (MvPolynomial (Fin d) R))))).obj U) (z : (yoneda.obj (Spec (CommRingCat.of
        (MvPolynomial (Fin d) R)))).obj U), (∀ i, (yoneda.map (fW d R)).app U (y i) = z) →
      ∃ x, ∀ i, g.app U (((W d R).map (vtx n i).op).app U x) = y i)

theorem LeafWCech_of (hC : LeafCechRec) (hD : LeafWData) : LeafWCech := by
  intro d R _
  obtain ⟨r, g, hr, hg, hi, hs⟩ := hD d R
  obtain ⟨ψ, hψ, he⟩ := hC (W d R) _ _ (yoneda.map (fW d R)) r g hg hi hs
  refine ⟨ψ, hψ, ?_⟩
  change wa d R ≫ ψ ≫ (Arrow.mk (yoneda.map (fW d R))).augmentedCechNerve.hom = 𝟙 _
  subst he
  exact hr

end LateralTheory.CohomologicalPurity.Thom.ExcP.Chart
