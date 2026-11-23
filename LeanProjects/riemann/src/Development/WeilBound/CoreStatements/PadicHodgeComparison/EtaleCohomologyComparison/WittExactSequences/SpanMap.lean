import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.WittExactSequences.IsCompl
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.WittExactSequences.TensCompl
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.WittExactSequences.PerfectoidProd
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.WittExactSequences.CechTens

set_option autoImplicit false

open TensorProduct CrystallineSemistableComparison.D
open scoped LaurentPolynomial

namespace CrystallineSemistableComparison.D

open MvPolynomial in

def eqA {A : Type} [CommRing A] (P : Polynomial A) : Set (MvPolynomial (Fin 3) A) := {Polynomial.aeval (X 0) P}

open MvPolynomial in

def eqB {A : Type} [CommRing A] (f g : A) : Set (MvPolynomial (Fin 3) A) :=
  {X 0 * X 0 - X 0, X 0 * C f - X 1 * C g, (1 - X 0) * C g - X 2 * C f}

theorem pt_eqA {A B : Type} [CommRing A] [CommRing B] (φ : A →+* B) (P : Polynomial A) :
    Pt φ (eqA P) ↔ ∃ x, (P.map φ).IsRoot x := by
  have e : ∀ y : Fin 3 → B, MvPolynomial.eval₂ φ y (Polynomial.aeval (MvPolynomial.X 0) P) = (P.map φ).eval (y 0) := by
    intro y
    induction P using Polynomial.induction_on' with
    | add a b ha hb => simp [ha, hb]
    | monomial n a => simp [Polynomial.aeval_monomial]
  constructor
  · rintro ⟨y, hy⟩
    exact ⟨y 0, (e y).symm.trans (hy _ rfl)⟩
  · rintro ⟨x, hx⟩
    exact ⟨fun _ => x, fun q hq => by rw [show q = _ from hq, e]; exact hx⟩

theorem pt_eqB {A B : Type} [CommRing A] [CommRing B] (φ : A →+* B) (f g : A) :
    Pt φ (eqB f g) ↔ ∃ e : B, IsIdempotentElem e ∧ e * φ f ∈ Ideal.span {φ g} ∧ (1 - e) * φ g ∈ Ideal.span {φ f} := by
  constructor
  · rintro ⟨y, hy⟩
    have h1 := hy _ (Or.inl rfl)
    have h2 := hy _ (Or.inr (Or.inl rfl))
    have h3 := hy _ (Or.inr (Or.inr rfl))
    simp only [MvPolynomial.eval₂_sub, MvPolynomial.eval₂_mul, MvPolynomial.eval₂_X, MvPolynomial.eval₂_C,
      MvPolynomial.eval₂_one, sub_eq_zero] at h1 h2 h3
    exact ⟨y 0, h1, Ideal.mem_span_singleton'.2 ⟨_, h2.symm⟩, Ideal.mem_span_singleton'.2 ⟨_, h3.symm⟩⟩
  · rintro ⟨e, h1, h2, h3⟩
    obtain ⟨u, hu⟩ := Ideal.mem_span_singleton'.1 h2
    obtain ⟨v, hv⟩ := Ideal.mem_span_singleton'.1 h3
    refine ⟨![e, u, v], ?_⟩
    rintro q (rfl | rfl | rfl) <;>
      simp [MvPolynomial.eval₂_sub, MvPolynomial.eval₂_mul, hu, hv, h1.eq]

theorem root_map {A B : Type} [CommRing A] [CommRing B] (φ : A →+* B) (h : AIC B) : AICm φ := by
  intro P hP hd
  rcases subsingleton_or_nontrivial B with _ | _
  · exact ⟨0, Subsingleton.elim _ _⟩
  · exact h _ (hP.map φ) (by rwa [hP.natDegree_map])

theorem span_map {A B : Type} [CommRing A] [CommRing B] (φ : A →+* B) {π f g : A} {N : ℕ} (h : π ^ N ∈ Ideal.span {f, g}) :
    φ π ^ N ∈ Ideal.span {φ f, φ g} := by
  obtain ⟨a, b, e⟩ := Ideal.mem_span_pair.1 h
  exact Ideal.mem_span_pair.2 ⟨φ a, φ b, by rw [← map_pow, ← e, map_add, map_mul, map_mul]⟩

theorem cov_step : ∀ (p : ℕ) [Fact p.Prime] (A : Type) [CommRing A] (r : ℕ → A), Pf p A → IsRt p r → ∃ (B : Type) (_ : CommRing B) (_ : Algebra A B), Pf p B ∧ Cov p r B ∧ AICm (algebraMap A B) ∧ VALm (r 0) (algebraMap A B) ∧ Splits p (r 0) (algebraMap A B) := by
  intro p _ A _ r hA hr
  let 𝓔 : Set (Set (MvPolynomial (Fin 3) A)) := {E | (∃ P : Polynomial A, P.Monic ∧ 0 < P.natDegree ∧ E = eqA P) ∨
    ∃ f g : A, (∃ N : ℕ, r 0 ^ N ∈ Ideal.span {f, g}) ∧ E = eqB f g}
  obtain ⟨B, _, _, hB, hc, hE, hs⟩ := Leaf.big_step p A r 𝓔 hA (fin_step p A r 𝓔 hA hr (by
    rintro E (⟨P, hP, hd, rfl⟩ | ⟨f, g, ⟨N, hN⟩, rfl⟩) B _ _ hB
    · rcases subsingleton_or_nontrivial B with _ | _
      · exact ⟨B, inferInstance, inferInstance, hB, (Leaf.cov_mono p B _).1, (pt_eqA _ _).2 ⟨0, Subsingleton.elim _ _⟩⟩
      · obtain ⟨B₁, _, _, h1, h2, x, hx⟩ := Leaf.cov_root p B (fun k => algebraMap A B (r k)) (P.map (algebraMap A B)) hB
          (hP.map _) (by rwa [hP.natDegree_map])
        refine ⟨B₁, inferInstance, inferInstance, h1, h2, (pt_eqA _ _).2 ⟨x, ?_⟩⟩
        rw [← Polynomial.map_map, Polynomial.IsRoot, Polynomial.eval_map, ← Polynomial.aeval_def]
        exact hx
    · obtain ⟨B₁, _, _, h1, h2, e, u, v, he, hu, hv⟩ := cov_blow p B (fun k => algebraMap A B (r k)) (algebraMap A B f)
        (algebraMap A B g) N hB (fun k => by rw [← map_pow, hr k]) (span_map _ hN)
      exact ⟨B₁, inferInstance, inferInstance, h1, h2, (pt_eqB _ _ _).2
        ⟨e, he, Ideal.mem_span_singleton'.2 ⟨u, hu.symm⟩, Ideal.mem_span_singleton'.2 ⟨v, hv.symm⟩⟩⟩))
  refine ⟨B, inferInstance, inferInstance, hB, hc, fun P hP hd => (pt_eqA _ _).1 (hE _ (Or.inl ⟨P, hP, hd, rfl⟩)),
    fun f g h => (pt_eqB _ _ _).1 (hE _ (Or.inr ⟨f, g, h, rfl⟩)), fun T _ x hT h1 h2 => hs T x hT ?_⟩
  rintro E (⟨P, hP, hd, rfl⟩ | ⟨f, g, ⟨N, hN⟩, rfl⟩)
  · exact (pt_eqA _ _).2 (root_map x h1 P hP hd)
  · exact (pt_eqB _ _ _).2 (h2 _ _ ⟨N, span_map x hN⟩)

end CrystallineSemistableComparison.D
