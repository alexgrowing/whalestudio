import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NoCommonZeroSpreadsConstructibleNbhdStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj TopologicalSpace TensorProduct
open scoped CategoryTheory.Obj

namespace GlobalTheory.SplitSpread

open MvPolynomial

abbrev Mon (σ : Type) (D : ℕ) := {m : σ →₀ ℕ // m.degree ≤ D}

instance instFiniteMon (σ : Type) [Finite σ] (D : ℕ) : Finite (Mon σ D) :=
  (Finsupp.finite_of_degree_le (σ := σ) D).to_subtype

noncomputable instance instFintypeMon (σ : Type) [Finite σ] (D : ℕ) : Fintype (Mon σ D) :=
  Fintype.ofFinite _

abbrev Var (σ : Type) (D : ℕ) := (Bool × Mon σ D) ⊕ (Bool × σ) ⊕ Bool

theorem sum_eq_degree {σ : Type} (s : σ →₀ ℕ) : (s.sum fun _ e => e) = s.degree := rfl

theorem hom_eval {R S τ : Type} [CommSemiring R] [CommSemiring S] (h : R →+* S) (x : τ → R)
    (W : MvPolynomial τ R) : h (eval x W) = MvPolynomial.eval (h ∘ x) (MvPolynomial.map h W) := by
  rw [MvPolynomial.eval_map, MvPolynomial.eval, MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_comp_left, RingHom.comp_id]

variable {σ : Type} [Finite σ] (A : Type) [CommRing A] (D : ℕ)

noncomputable def gen (b : Bool) : MvPolynomial σ (MvPolynomial (Var σ D) A) :=
  ∑ m : Mon σ D, monomial m.1 (X (Sum.inl (b, m)))

noncomputable def eqs (f g : MvPolynomial σ A) :
    ((σ →₀ ℕ) ⊕ Bool ⊕ Bool) → MvPolynomial (Var σ D) A
  | Sum.inl n => coeff n (gen A D true * gen A D false - MvPolynomial.map C f)
  | Sum.inr (Sum.inl b) => MvPolynomial.eval (fun i => X (Sum.inr (Sum.inl (b, i)))) (gen A D b)
  | Sum.inr (Sum.inr b) =>
      X (Sum.inr (Sum.inr b)) * MvPolynomial.eval (fun i => X (Sum.inr (Sum.inl (b, i)))) (MvPolynomial.map C g) - 1

variable {A D}

theorem map_gen {k : Type} [CommRing k] (ψ : A →+* k) (z : Var σ D → k) (b : Bool) :
    MvPolynomial.map (eval₂Hom ψ z) (gen A D b) = ∑ m : Mon σ D, monomial m.1 (z (Sum.inl (b, m))) := by
  simp [gen, map_sum, map_monomial]

theorem totalDegree_sum_le {k : Type} [CommRing k] (c : Mon σ D → k) :
    (∑ m : Mon σ D, monomial m.1 (c m)).totalDegree ≤ D := by
  refine (totalDegree_finsetSum _ _).trans (Finset.sup_le fun m _ => ?_)
  exact (totalDegree_monomial_le _ _).trans m.2

theorem sum_coeff {k : Type} [CommRing k] (p : MvPolynomial σ k) (hp : p.totalDegree ≤ D) :
    ∑ m : Mon σ D, monomial m.1 (coeff m.1 p) = p := by
  classical
  ext n
  simp only [coeff_sum, coeff_monomial]
  by_cases hn : n.degree ≤ D
  · rw [Finset.sum_eq_single ⟨n, hn⟩]
    · simp
    · intro m _ hm
      rw [if_neg]
      intro h; exact hm (Subtype.ext h)
    · simp
  · rw [Finset.sum_eq_zero]
    · by_contra h
      exact hn ((sum_eq_degree n ▸ le_totalDegree (mem_support_iff.mpr (Ne.symm h))).trans hp)
    · intro m _
      rw [if_neg]
      rintro rfl; exact hn m.2

end GlobalTheory.SplitSpread

namespace GlobalTheory.SplitSpread
open MvPolynomial
variable {σ : Type} [Finite σ] {A : Type} [CommRing A] {D : ℕ}

noncomputable def spec {k : Type} [CommRing k] (z : Var σ D → k) (b : Bool) : MvPolynomial σ k :=
  ∑ m : Mon σ D, monomial m.1 (z (Sum.inl (b, m)))

theorem eval_eqs_coeff {k : Type} [CommRing k] (ψ : A →+* k) (z : Var σ D → k)
    (f g : MvPolynomial σ A) (n : σ →₀ ℕ) :
    eval₂ ψ z (eqs A D f g (Sum.inl n)) = coeff n (spec z true * spec z false - MvPolynomial.map ψ f) := by
  rw [← coe_eval₂Hom]
  simp only [eqs]
  rw [← MvPolynomial.coeff_map, map_sub, map_mul, map_gen, map_gen, MvPolynomial.map_map,
    eval₂Hom_comp_C]
  rfl

theorem eval_eqs_point {k : Type} [CommRing k] (ψ : A →+* k) (z : Var σ D → k)
    (f g : MvPolynomial σ A) (b : Bool) :
    eval₂ ψ z (eqs A D f g (Sum.inr (Sum.inl b))) =
      MvPolynomial.eval (fun i => z (Sum.inr (Sum.inl (b, i)))) (spec z b) := by
  rw [← coe_eval₂Hom]
  simp only [eqs]
  rw [hom_eval, map_gen]
  congr 2
  funext i
  simp

theorem eval_eqs_inv {k : Type} [CommRing k] (ψ : A →+* k) (z : Var σ D → k)
    (f g : MvPolynomial σ A) (b : Bool) :
    eval₂ ψ z (eqs A D f g (Sum.inr (Sum.inr b))) =
      z (Sum.inr (Sum.inr b)) *
        MvPolynomial.eval (fun i => z (Sum.inr (Sum.inl (b, i)))) (MvPolynomial.map ψ g) - 1 := by
  simp only [eqs, eval₂_sub, eval₂_mul, eval₂_X, eval₂_one]
  rw [← coe_eval₂Hom, hom_eval, MvPolynomial.map_map, eval₂Hom_comp_C]
  congr 4
  funext i
  simp
end GlobalTheory.SplitSpread

namespace GlobalTheory.SplitSpread
open MvPolynomial
variable {σ : Type} [Finite σ] {A : Type} [CommRing A]

def Bad (f g : MvPolynomial σ A) (D : ℕ) (k : Type) [Field k] (ψ : A →+* k) : Prop :=
  ∃ u v : MvPolynomial σ k, u.totalDegree ≤ D ∧ v.totalDegree ≤ D ∧
    u * v = MvPolynomial.map ψ f ∧ ∃ P Q : σ → k, MvPolynomial.eval P u = 0 ∧
      MvPolynomial.eval P (MvPolynomial.map ψ g) ≠ 0 ∧ MvPolynomial.eval Q v = 0 ∧
      MvPolynomial.eval Q (MvPolynomial.map ψ g) ≠ 0

theorem bad_iff (f g : MvPolynomial σ A) (D : ℕ) (k : Type) [Field k] (ψ : A →+* k) :
    (∃ z : Var σ D → k, ∀ j, eval₂ ψ z (eqs A D f g j) = 0) ↔ Bad f g D k ψ := by
  constructor
  · rintro ⟨z, hz⟩
    have hinv : ∀ b, MvPolynomial.eval (fun i => z (Sum.inr (Sum.inl (b, i))))
        (MvPolynomial.map ψ g) ≠ 0 := by
      intro b h0
      have := hz (Sum.inr (Sum.inr b))
      rw [eval_eqs_inv, h0] at this
      simp at this
    refine ⟨spec z true, spec z false, totalDegree_sum_le _, totalDegree_sum_le _, ?_,
      fun i => z (Sum.inr (Sum.inl (true, i))), fun i => z (Sum.inr (Sum.inl (false, i))),
      ?_, hinv true, ?_, hinv false⟩
    · ext n
      have := hz (Sum.inl n)
      rw [eval_eqs_coeff, coeff_sub, sub_eq_zero] at this
      exact this
    · have := hz (Sum.inr (Sum.inl true)); rwa [eval_eqs_point] at this
    · have := hz (Sum.inr (Sum.inl false)); rwa [eval_eqs_point] at this
  · rintro ⟨u, v, hu, hv, huv, P, Q, hPu, hPg, hQv, hQg⟩
    let z : Var σ D → k := Sum.elim (fun p => coeff p.2.1 (if p.1 then u else v))
      (Sum.elim (fun p => if p.1 then P p.2 else Q p.2)
        (fun b => (MvPolynomial.eval (if b then P else Q) (MvPolynomial.map ψ g))⁻¹))
    have hs : ∀ b, spec z b = if b then u else v := by
      intro b
      cases b
      · exact sum_coeff v hv
      · exact sum_coeff u hu
    refine ⟨z, ?_⟩
    rintro (n | b | b)
    · rw [eval_eqs_coeff, hs, hs]
      simp [huv]
    · rw [eval_eqs_point, hs]
      cases b <;> simpa [z]
    · rw [eval_eqs_inv]
      cases b
      · simp only [z, Sum.elim_inr, Bool.false_eq_true, if_false]
        exact sub_eq_zero.mpr (inv_mul_cancel₀ hQg)
      · simp only [z, Sum.elim_inr, if_true]
        exact sub_eq_zero.mpr (inv_mul_cancel₀ hPg)

end GlobalTheory.SplitSpread

theorem GlobalTheory.splitting_absence_spreads : ∀ (A : Type) [CommRing A] (σ : Type) [Finite σ] (f g : MvPolynomial σ A) (D : ℕ) (Ω : Type) [Field Ω] [IsAlgClosed Ω] (φ : A →+* Ω), ¬ (∃ u v : MvPolynomial σ Ω, u.totalDegree ≤ D ∧ v.totalDegree ≤ D ∧ u * v = MvPolynomial.map φ f ∧ ∃ P Q : σ → Ω, MvPolynomial.eval P u = 0 ∧ MvPolynomial.eval P (MvPolynomial.map φ g) ≠ 0 ∧ MvPolynomial.eval Q v = 0 ∧ MvPolynomial.eval Q (MvPolynomial.map φ g) ≠ 0) → ∃ (a : A) (I : Finset A), φ a ≠ 0 ∧ (∀ c ∈ I, φ c = 0) ∧ ∀ (k : Type) [Field k] (ψ : A →+* k), ψ a ≠ 0 → (∀ c ∈ I, ψ c = 0) → ¬ (∃ u v : MvPolynomial σ k, u.totalDegree ≤ D ∧ v.totalDegree ≤ D ∧ u * v = MvPolynomial.map ψ f ∧ ∃ P Q : σ → k, MvPolynomial.eval P u = 0 ∧ MvPolynomial.eval P (MvPolynomial.map ψ g) ≠ 0 ∧ MvPolynomial.eval Q v = 0 ∧ MvPolynomial.eval Q (MvPolynomial.map ψ g) ≠ 0) := by
  intro A _ σ _ f g D Ω _ _ φ hbad
  have h0 : ¬ ∃ z : GlobalTheory.SplitSpread.Var σ D → Ω, ∀ j,
      MvPolynomial.eval₂ φ z (GlobalTheory.SplitSpread.eqs A D f g j) = 0 := by
    rw [GlobalTheory.SplitSpread.bad_iff]; exact hbad
  obtain ⟨a, I, ha, hI, hk⟩ := GlobalTheory.T.no_common_zero_spreads_constructible_nbhd A _ _ (GlobalTheory.SplitSpread.eqs A D f g) Ω φ h0
  refine ⟨a, I, ha, hI, fun k _ ψ hψa hψI hb => hk k ψ hψa hψI ?_⟩
  exact (GlobalTheory.SplitSpread.bad_iff f g D k ψ).mpr hb
