import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.SqMap
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.FormalGermDimensionUniqueStatement

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Flat.FrGauge

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Fl Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ (PS Pt ev pt comp1)
open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

theorem actComm_aug_subst {R : Type} [CommRing R] {κ κ' : Type} (m : ℕ) (φ : κ → MvPolynomial κ' R) :
    (jetAug : Jet R κ' m →ₐ[R] R).comp (jetSubstP m φ) = jetAug := by
  refine Ideal.Quotient.algHom_ext R (MvPolynomial.algHom_ext fun i => ?_)
  show MvPolynomial.aeval (fun _ => (0 : R)) (MvPolynomial.aeval (fun i => φ i - MvPolynomial.C (MvPolynomial.constantCoeff (φ i))) (MvPolynomial.X i)) = MvPolynomial.aeval (fun _ => (0 : R)) (MvPolynomial.X i)
  simp [MvPolynomial.aeval_X, MvPolynomial.aeval_zero']

theorem actComm_aug_X {R : Type} [CommRing R] {κ : Type} (m : ℕ) (q : κ) :
    (jetAug : Jet R κ m →ₐ[R] R) (Ideal.Quotient.mk _ (MvPolynomial.X q)) = 0 := by
  show MvPolynomial.aeval (fun _ : κ => (0 : R)) (MvPolynomial.X q) = 0
  simp

theorem actComm_homAt_comp {X : Scheme.{0}} {S : Type} [CommRing S] (x0 : Sp S ⟶ X) {A B C : Type} [CommRing A]
    [Algebra S A] [CommRing B] [Algebra S B] [CommRing C] [Algebra S C] (f : A →ₐ[S] B) (g : B →ₐ[S] C) :
    homAt x0 g ≫ homAt x0 f = homAt x0 (g.comp f) := by
  apply Over.OverMorphism.ext
  simp only [homAt, Over.comp_left, Over.homMk_left, spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  rfl

section Fib

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {X : Scheme.{0}} (t : SAB H X)
  {k : Type} [Field k] (x : Sp k ⟶ X)

theorem fibPt_fst {A : Type} [CommRing A] [Algebra k A] (y : overAt x A ⟶ t.G) :
    (fibPt t x y).left ≫ pullback.fst t.G.hom x = y.left :=
  pullback.lift_fst _ _ _

theorem fibPt_snd {A : Type} [CommRing A] [Algebra k A] (y : overAt x A ⟶ t.G) :
    (fibPt t x y).left ≫ pullback.snd t.G.hom x = spMap (algebraMap k A) :=
  (pullback.lift_snd _ _ _).trans (Category.comp_id _)

theorem homAt_fibPt {A B : Type} [CommRing A] [Algebra k A] [CommRing B] [Algebra k B] (f : A →ₐ[k] B)
    (y : overAt x A ⟶ t.G) :
    homAt (𝟙 (Sp k)) f ≫ fibPt t x y = fibPt t x (homAt x f ≫ y) := by
  apply Over.OverMorphism.ext
  apply pullback.hom_ext
  · rw [Over.comp_left, Category.assoc, fibPt_fst, fibPt_fst, Over.comp_left]
    rfl
  · rw [Over.comp_left, Category.assoc, fibPt_snd, fibPt_snd]
    exact spMap_comp_alg f

theorem fibPt_map {A : Type} [CommRing A] [Algebra k A] (y : overAt x A ⟶ t.G) (b : t.G ⟶ t.G) :
    fibPt t x y ≫ (Over.pullback x).map b = fibPt t x (y ≫ b) := by
  have h1 : ((Over.pullback x).map b).left ≫ pullback.fst t.G.hom x = pullback.fst t.G.hom x ≫ b.left :=
    pullback.lift_fst _ _ _
  have h2 : ((Over.pullback x).map b).left ≫ pullback.snd t.G.hom x = pullback.snd t.G.hom x :=
    pullback.lift_snd _ _ _
  apply Over.OverMorphism.ext
  apply pullback.hom_ext
  · rw [Over.comp_left, Category.assoc, h1, ← Category.assoc, fibPt_fst, fibPt_fst, Over.comp_left]
  · rw [Over.comp_left, Category.assoc, h2, fibPt_snd, fibPt_snd]

end Fib

theorem substitution_action_commutes : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)], (∀ a : 𝓞 E, star a = H.bar a) → ∀ (X : Scheme.{0}) (t : SAB H X) (k : Type) [Field k] [IsAlgClosed k] (p : ℕ) [Fact p.Prime] [CharP k p] (x : Sp k ⟶ X) (Q : AbQuot t x) (d d' : ℕ) (g : GermAt t x d) (gB : GermAt Q.tB (𝟙 (Sp k)) d'), ∀ Qs : Fin d' → PS k 1 d, (∀ i, MvPowerSeries.constantCoeff (Qs i) = 0) → (∀ m, fibPt t x (g.x m) ≫ Q.q = homAt (𝟙 (Sp k)) (sub1 Qs m) ≫ gB.x m) → ∀ (m : ℕ) (a : 𝓞 E), (jetSubstP m fun p : Fin 1 × Fin d => psTrunc m (g.B.A.act a p.2)).comp (sub1 Qs m) = (sub1 Qs m).comp (jetSubstP m fun p : Fin 1 × Fin d' => psTrunc m (gB.B.A.act a p.2)) := by
  intro E _ _ _ H _ hst X t k _ _ p _ _ x Q d d' g gB Qs _ hQ m a
  set A := jetSubstP (S := k) m fun p : Fin 1 × Fin d => psTrunc m (g.B.A.act a p.2) with hA
  set B := jetSubstP (S := k) m fun p : Fin 1 × Fin d' => psTrunc m (gB.B.A.act a p.2) with hB
  have h1 : homAt (𝟙 (Sp k)) (A.comp (sub1 Qs m)) ≫ gB.x m =
      fibPt t x (g.x m) ≫ (Over.pullback x).map (t.act.act a) ≫ Q.q := by
    rw [← actComm_homAt_comp, Category.assoc, ← hQ m, ← Category.assoc, homAt_fibPt, ← g.chart.act m a,
      ← fibPt_map, Category.assoc]
  have h2 : homAt (𝟙 (Sp k)) ((sub1 Qs m).comp B) ≫ gB.x m =
      fibPt t x (g.x m) ≫ (Over.pullback x).map (t.act.act a) ≫ Q.q := by
    rw [← actComm_homAt_comp, Category.assoc, ← gB.chart.act m a, Q.act_q, ← Category.assoc, ← Category.assoc, ← hQ m]
  have haug : ∀ χ : Jet k (Fin 1 × Fin d') m →ₐ[k] Jet k (Fin 1 × Fin d) m,
      (jetAug : Jet k (Fin 1 × Fin d) m →ₐ[k] k).comp χ = jetAug →
      ∀ q, (jetAug : Jet k (Fin 1 × Fin d) m →ₐ[k] k) (χ (Ideal.Quotient.mk _ (MvPolynomial.X q))) = 0 := by
    intro χ h q
    rw [← AlgHom.comp_apply, h, actComm_aug_X]
  have a1 : (jetAug : Jet k (Fin 1 × Fin d) m →ₐ[k] k).comp (A.comp (sub1 Qs m)) = jetAug := by
    rw [← AlgHom.comp_assoc, hA, actComm_aug_subst, sub1, actComm_aug_subst]
  have a2 : (jetAug : Jet k (Fin 1 × Fin d) m →ₐ[k] k).comp ((sub1 Qs m).comp B) = jetAug := by
    rw [← AlgHom.comp_assoc, sub1, actComm_aug_subst, hB, actComm_aug_subst]
  have hz : homAt (𝟙 (Sp k)) (jetAug : Jet k (Fin 1 × Fin d) m →ₐ[k] k) ≫
      (homAt (𝟙 (Sp k)) (A.comp (sub1 Qs m)) ≫ gB.x m) = 1 := by
    rw [← Category.assoc, actComm_homAt_comp, a1]
    exact gB.chart.zero m
  exact ((GlobalTheory.T.formal_germ_dimension_unique E H hst (Sp k) Q.tB k (𝟙 (Sp k)) d' gB).2 (Fin 1 × Fin d) m _ hz).unique
    ⟨haug _ a1, rfl⟩ ⟨haug _ a2, h1.trans h2.symm⟩

end GlobalTheory.CompanionTheory.Ar.Flat.FrGauge
