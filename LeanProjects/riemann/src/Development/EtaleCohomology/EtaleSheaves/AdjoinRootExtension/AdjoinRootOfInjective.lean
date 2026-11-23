import Mathlib

noncomputable section
open Polynomial

namespace LateralTheory.E.AICExtPf

universe u

def MonP (R : Type u) [CommRing R] : Type u := {p : R[X] // p.Monic ∧ 0 < p.natDegree}

variable (R : Type u) [CommRing R]

def stepIdeal : Ideal (MvPolynomial (MonP R) R) :=
  Ideal.span (Set.range fun p : MonP R => p.1.eval₂ MvPolynomial.C (MvPolynomial.X p))

abbrev StepRing : Type u := MvPolynomial (MonP R) R ⧸ stepIdeal R

def stepHom : R →+* StepRing R := algebraMap R (StepRing R)

lemma stepHom_eq : stepHom R = (Ideal.Quotient.mk (stepIdeal R)).comp MvPolynomial.C := rfl

lemma eval_map_hom {A B : Type*} [CommRing A] [CommRing B] (P : A[X]) (g : A →+* B) (a : A) :
    (P.map g).eval (g a) = g (P.eval a) := by
  rw [eval_map, eval₂_at_apply]

lemma step_root (p : MonP R) :
    (p.1.map (stepHom R)).eval (Ideal.Quotient.mk (stepIdeal R) (MvPolynomial.X p)) = 0 := by
  rw [eval_map, stepHom_eq, ← hom_eval₂]
  exact Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.subset_span ⟨p, rfl⟩)

lemma adjoinRoot_of_injective {T : Type u} [CommRing T] (q : T[X]) (hq : q.Monic)
    (hd : 0 < q.natDegree) : Function.Injective (AdjoinRoot.of q) := by
  rw [injective_iff_map_eq_zero]
  intro r hr
  by_contra h
  have h1 : AdjoinRoot.mk q (C r) = 0 := hr
  rw [AdjoinRoot.mk_eq_zero] at h1
  exact hq.not_dvd_of_natDegree_lt (by simpa using h) (by simpa using hd) h1

lemma finite_roots (F : Finset (MonP R)) : ∃ (T : Type u) (_ : CommRing T) (φ : R →+* T),
    Function.Injective φ ∧ ∀ p ∈ F, ∃ a : T, (p.1.map φ).eval a = 0 := by
  classical
  induction F using Finset.induction_on with
  | empty => exact ⟨R, inferInstance, RingHom.id R, Function.injective_id, by simp⟩
  | insert q F _ ih =>
    obtain ⟨T, _, φ, hφ, hF⟩ := ih
    by_cases hT : Subsingleton T
    · refine ⟨T, inferInstance, φ, hφ, fun p _ => ⟨0, Subsingleton.elim _ _⟩⟩
    haveI : Nontrivial T := not_subsingleton_iff_nontrivial.1 hT
    set q' := q.1.map φ with hq'
    have hm : q'.Monic := q.2.1.map φ
    have hd : 0 < q'.natDegree := by rw [hq', q.2.1.natDegree_map]; exact q.2.2
    refine ⟨AdjoinRoot q', inferInstance, (AdjoinRoot.of q').comp φ,
      (adjoinRoot_of_injective q' hm hd).comp hφ, ?_⟩
    intro p hp
    rcases Finset.mem_insert.1 hp with rfl | hp
    · refine ⟨AdjoinRoot.root q', ?_⟩
      rw [← Polynomial.map_map, eval_map, AdjoinRoot.eval₂_root]
    · obtain ⟨a, ha⟩ := hF p hp
      refine ⟨AdjoinRoot.of q' a, ?_⟩
      rw [← Polynomial.map_map, eval_map_hom, ha, map_zero]

theorem stepHom_injective : Function.Injective (stepHom R) := by
  classical
  rw [injective_iff_map_eq_zero]
  intro r hr
  have hmem : MvPolynomial.C r ∈ stepIdeal R := Ideal.Quotient.eq_zero_iff_mem.1 hr
  obtain ⟨S, hS, hx⟩ := Submodule.mem_span_finite_of_mem_span hmem
  rw [← Set.image_univ] at hS
  obtain ⟨F, -, rfl⟩ := Finset.subset_set_image_iff.1 hS
  obtain ⟨T, _, φ, hφ, hF⟩ := finite_roots R F
  let v : MonP R → T := fun p => if h : p ∈ F then (hF p h).choose else 0
  let ev := MvPolynomial.eval₂Hom φ v
  have hk : Ideal.span (↑(F.image fun p : MonP R => p.1.eval₂ MvPolynomial.C (MvPolynomial.X p)) :
      Set (MvPolynomial (MonP R) R)) ≤ RingHom.ker ev := by
    rw [Ideal.span_le]
    intro t ht
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.1 (Finset.mem_coe.1 ht)
    rw [SetLike.mem_coe, RingHom.mem_ker, hom_eval₂, MvPolynomial.eval₂Hom_comp_C]
    have : ev (MvPolynomial.X p) = (hF p hp).choose := by
      simp [ev, v, hp]
    rw [this, ← eval_map]
    exact (hF p hp).choose_spec
  have h0 : ev (MvPolynomial.C r) = 0 := RingHom.mem_ker.1 (hk hx)
  have : ev (MvPolynomial.C r) = φ r := by simp [ev]
  exact (injective_iff_map_eq_zero φ).1 hφ r (this ▸ h0)

theorem stepHom_isIntegral : (stepHom R).IsIntegral := by
  intro z
  change IsIntegral R z
  obtain ⟨q, rfl⟩ := Ideal.Quotient.mk_surjective z
  induction q using MvPolynomial.induction_on with
  | C a => exact isIntegral_algebraMap
  | add a b ha hb => rw [map_add]; exact ha.add hb
  | mul_X a p ha =>
    rw [map_mul]
    refine ha.mul ⟨p.1, p.2.1, ?_⟩
    rw [← eval_map]
    exact step_root R p

theorem step_has_root (p : R[X]) (hp : p.Monic) (hd : 0 < p.natDegree) :
    ∃ a : StepRing R, (p.map (stepHom R)).eval a = 0 :=
  ⟨_, step_root R ⟨p, hp, hd⟩⟩

end LateralTheory.E.AICExtPf
