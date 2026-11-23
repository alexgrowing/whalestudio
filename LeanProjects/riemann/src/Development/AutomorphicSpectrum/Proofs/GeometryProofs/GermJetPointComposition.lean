import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.TranslDiffEq
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj GlobalTheory.CompanionTheory.Ar.Coc
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Coc.JetPts

section
variable {X0 : Scheme.{0}} {k : Type} [Field k] (x : Sp k ⟶ X0)

theorem homAt_comp_homAt {A B C : Type} [CommRing A] [Algebra k A] [CommRing B] [Algebra k B] [CommRing C] [Algebra k C]
    (g : A →ₐ[k] B) (f : B →ₐ[k] C) : homAt x f ≫ homAt x g = homAt x (f.comp g) := by
  apply Over.OverMorphism.ext
  simp only [homAt, Over.comp_left, Over.homMk_left, spMap]
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  rfl

theorem homAt_id_eq {A : Type} [CommRing A] [Algebra k A] : homAt x (AlgHom.id k A) = 𝟙 _ := by
  apply Over.OverMorphism.ext
  simp only [homAt, Over.homMk_left, spMap]
  exact Spec.map_id _

def trJ (κ : Type) {n M : ℕ} (h : n ≤ M) : Jet k κ M →ₐ[k] Jet k κ n :=
  Ideal.Quotient.factorₐ k (Ideal.pow_le_pow_right (by omega))

theorem trJ_mk (κ : Type) {n M : ℕ} (h : n ≤ M) (P : MvPolynomial κ k) :
    trJ (k := k) κ h (Ideal.Quotient.mk _ P) = Ideal.Quotient.mk _ P := rfl

theorem x_eq_of_trunc {Y : Over X0} {κ : Type} (z : ∀ m, overAt x (Jet k κ m) ⟶ Y)
    (hz : ∀ m, homAt x (jetTrunc : Jet k κ (m + 1) →ₐ[k] Jet k κ m) ≫ z (m + 1) = z m) {n M : ℕ} (h : n ≤ M) :
    homAt x (trJ κ h) ≫ z M = z n := by
  induction M, h using Nat.le_induction with
  | base =>
    have e : trJ (k := k) κ (le_refl n) = AlgHom.id k _ := by
      apply Ideal.Quotient.algHom_ext
      apply MvPolynomial.algHom_ext
      intro i
      rfl
    rw [e, homAt_id_eq, Category.id_comp]
  | succ M h ih =>
    have e : (trJ (k := k) κ (Nat.le_succ_of_le h)) = (trJ κ h).comp jetTrunc := by
      apply Ideal.Quotient.algHom_ext
      apply MvPolynomial.algHom_ext
      intro i
      rfl
    rw [← ih, ← hz M, e, ← homAt_comp_homAt, Category.assoc]

end

section
variable {k : Type} [Field k] {d : ℕ}

theorem liftJet_mk_eq {κ B : Type} [CommRing B] [Algebra k B] {n : ℕ} (f : MvPolynomial κ k →ₐ[k] B)
    (h : Ideal.span (Set.range fun i => f (MvPolynomial.X i)) ^ (n + 1) = ⊥) (P : MvPolynomial κ k) :
    liftJet f h (Ideal.Quotient.mk _ P) = f P := rfl

theorem jetMap_mk_eq {κ κ' : Type} {n : ℕ} (φ : κ → MvPolynomial κ' k) (hφ : ∀ i, φ i ∈ orig k κ') (P : MvPolynomial κ k) :
    (jetMap φ hφ : Jet k κ n →ₐ[k] Jet k κ' n) (Ideal.Quotient.mk _ P) = Ideal.Quotient.mk _ (MvPolynomial.aeval φ P) := rfl

theorem jq_mk_zero (w : Fin d → k) (p m : ℕ) (j : Fin d) :
    jq w p m (Ideal.Quotient.mk _ (MvPolynomial.X ((0 : Fin 2), j))) =
      algebraMap k _ (w j) * dQ (Jet k (Fin 1 × Fin d) m) p := by
  rw [jq, liftJet_mk_eq]
  simp

theorem jq_mk_one (w : Fin d → k) (p m : ℕ) (j : Fin d) :
    jq w p m (Ideal.Quotient.mk _ (MvPolynomial.X ((1 : Fin 2), j))) =
      inR (k := k) (Jet k (Fin 1 × Fin d) m) p (Ideal.Quotient.mk _ (MvPolynomial.X ((0 : Fin 1), j))) := by
  rw [jq, liftJet_mk_eq]
  simp

theorem inL_mk (B : Type) [CommRing B] [Algebra k B] (p : ℕ) :
    inL (k := k) B p (Ideal.Quotient.mk _ (MvPolynomial.X ())) = dQ B p := by
  rw [inL, liftJet_mk_eq]
  simp

theorem ring_zero (w : Fin d → k) (p m : ℕ) :
    (jq w p m).comp (jetCopy d (p + m + 1) (0 : Fin 2)) =
      (inL (k := k) (Jet k (Fin 1 × Fin d) m) p).comp
        ((jetSubstP p fun q : Fin 1 × Fin d => MvPolynomial.C (w q.2) * MvPolynomial.X ()).comp
          (trJ (Fin 1 × Fin d) (show p ≤ p + m + 1 by omega))) := by
  apply Ideal.Quotient.algHom_ext
  apply MvPolynomial.algHom_ext
  rintro ⟨a, j⟩
  have ha : a = 0 := Subsingleton.elim _ _
  subst ha
  have h1 : jetCopy (S := k) d (p + m + 1) (0 : Fin 2) (Ideal.Quotient.mk _ (MvPolynomial.X ((0 : Fin 1), j))) =
      Ideal.Quotient.mk _ (MvPolynomial.X ((0 : Fin 2), j)) := by
    rw [jetCopy, jetMap_mk_eq]
    simp
  have h2 : jetSubstP (S := k) p (fun q : Fin 1 × Fin d => MvPolynomial.C (w q.2) * MvPolynomial.X ())
      (Ideal.Quotient.mk _ (MvPolynomial.X ((0 : Fin 1), j))) =
      algebraMap k _ (w j) * Ideal.Quotient.mk _ (MvPolynomial.X ()) := by
    rw [jetSubstP, jetMap_mk_eq]
    simp only [MvPolynomial.aeval_X, map_mul, MvPolynomial.constantCoeff_C, MvPolynomial.constantCoeff_X, mul_zero,
      map_zero, sub_zero]
    rfl
  simp only [AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk, trJ_mk, h1, h2, jq_mk_zero, map_mul, AlgHom.commutes, inL_mk]

theorem ring_one (w : Fin d → k) (p m : ℕ) :
    (jq w p m).comp (jetCopy d (p + m + 1) (1 : Fin 2)) =
      (inR (k := k) (Jet k (Fin 1 × Fin d) m) p).comp
        (trJ (Fin 1 × Fin d) (show m ≤ p + m + 1 by omega)) := by
  apply Ideal.Quotient.algHom_ext
  apply MvPolynomial.algHom_ext
  rintro ⟨a, j⟩
  have ha : a = 0 := Subsingleton.elim _ _
  subst ha
  have h1 : jetCopy (S := k) d (p + m + 1) (1 : Fin 2) (Ideal.Quotient.mk _ (MvPolynomial.X ((0 : Fin 1), j))) =
      Ideal.Quotient.mk _ (MvPolynomial.X ((1 : Fin 2), j)) := by
    rw [jetCopy, jetMap_mk_eq]
    simp
  simp only [AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk, trJ_mk, h1, jq_mk_one]

end

theorem main : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)] (X0 : Scheme.{0}) (t : SAB H X0) (k : Type) [Field k] (p : ℕ) (x : Sp k ⟶ X0) (d : ℕ) (g : GermAt t x d) (w : Fin d → k) (m : ℕ), homAt x (jq w p m) ≫ jptG t x d g.x (p + m + 1) (0 : Fin 2) = homAt x (inL (k := k) (Jet k (Fin 1 × Fin d) m) p) ≫ homAt x (jetSubstP p fun q : Fin 1 × Fin d => MvPolynomial.C (w q.2) * MvPolynomial.X ()) ≫ g.x p ∧ homAt x (jq w p m) ≫ jptG t x d g.x (p + m + 1) (1 : Fin 2) = homAt x (inR (k := k) (Jet k (Fin 1 × Fin d) m) p) ≫ g.x m := by
  intro E _ _ _ H _ X0 t k _ p x d g w m
  constructor
  · have hx := x_eq_of_trunc x g.x g.chart.trunc (show p ≤ p + m + 1 by omega)
    show homAt x (jq w p m) ≫ homAt x (jetCopy d (p + m + 1) (0 : Fin 2)) ≫ g.x (p + m + 1) = _
    rw [← hx, ← Category.assoc, homAt_comp_homAt, ring_zero, ← homAt_comp_homAt, ← homAt_comp_homAt]
    simp only [Category.assoc]
  · have hx := x_eq_of_trunc x g.x g.chart.trunc (show m ≤ p + m + 1 by omega)
    show homAt x (jq w p m) ≫ homAt x (jetCopy d (p + m + 1) (1 : Fin 2)) ≫ g.x (p + m + 1) = _
    rw [← hx, ← Category.assoc, homAt_comp_homAt, ring_one, ← homAt_comp_homAt]
    simp only [Category.assoc]

end GlobalTheory.CompanionTheory.Ar.Coc.JetPts
