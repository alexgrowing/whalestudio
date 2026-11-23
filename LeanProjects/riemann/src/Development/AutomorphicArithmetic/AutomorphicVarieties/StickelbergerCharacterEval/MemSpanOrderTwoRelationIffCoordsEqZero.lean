import Development.AutomorphicArithmetic.AutomorphicVarieties.StickelbergerCharacterEval.MemZpowersIff

open Finset UpperTheory.V.Bern UpperTheory.V.B4 UpperTheory.V.B5

private theorem single_mul_rel {A : Type} [CommRing A] {Γ : Type} [CommGroup Γ] (c : Γ) (ε : ℤ) (g : Γ) (b : A) :
    MonoidAlgebra.single g b * rel A c ε =
      MonoidAlgebra.single g (-((ε : A) * b)) + MonoidAlgebra.single (c * g) b := by
  rw [rel, MonoidAlgebra.intCast_def, mul_sub, MonoidAlgebra.single_mul_single,
    MonoidAlgebra.single_mul_single, mul_one, mul_one, mul_comm g c, mul_comm b,
    MonoidAlgebra.single_neg, sub_eq_add_neg, add_comm]

private theorem coeff_mul_rel {A : Type} [CommRing A] {Γ : Type} [CommGroup Γ] {c : Γ} (h2 : c * c = 1) (ε : ℤ)
    (u : MonoidAlgebra A Γ) (g : Γ) :
    (u * rel A c ε).coeff g = u.coeff (c * g) - (ε : A) * u.coeff g := by
  classical
  induction u using MonoidAlgebra.induction_linear with
  | zero => simp
  | add x y hx hy =>
    rw [add_mul]
    simp only [MonoidAlgebra.coeff_add, Finsupp.add_apply, hx, hy]
    ring
  | single a b =>
    rw [single_mul_rel]
    have h : (c * a = g) ↔ (a = c * g) := by
      constructor
      · rintro rfl; rw [← mul_assoc, h2, one_mul]
      · rintro rfl; rw [← mul_assoc, h2, one_mul]
    simp only [MonoidAlgebra.coeff_add, Finsupp.add_apply, MonoidAlgebra.coeff_single, Finsupp.single_apply, h]
    split_ifs <;> ring

theorem UpperTheory.V.B5.mem_span_orderTwoRelation_iff_coords_eq_zero :
    ∀ {A : Type} [CommRing A] {Γ : Type} [CommGroup Γ] [Finite Γ] (c : Γ) (ε : ℤ), c * c = 1 → c ≠ 1 → ε * ε = 1 → ∀ w : MonoidAlgebra A Γ, w ∈ Ideal.span {rel A c ε} ↔ coord c ε w = 0 := by
  intro A _ Γ _ _ c ε h2 hc hε w
  classical
  letI := Fintype.ofFinite Γ
  have hε' : (ε : A) * ε = 1 := by
    have := congrArg (fun n : ℤ => (n : A)) hε
    simpa using this
  rw [Ideal.mem_span_singleton']
  constructor
  · rintro ⟨u, rfl⟩
    funext i
    simp only [coord, coeff_mul_rel h2, Pi.zero_apply]
    rw [← mul_assoc c c, h2, one_mul]
    linear_combination (-(u.coeff (c * rep i))) * hε'
  · intro hw
    refine ⟨∑ i : Qc c, MonoidAlgebra.single (rep i) (w.coeff (c * rep i)), ?_⟩
    rw [Finset.sum_mul]
    simp only [single_mul_rel]
    apply MonoidAlgebra.ext
    conv_rhs => rw [← Finsupp.univ_sum_single w.coeff]
    rw [sum_rep h2 hc (fun g => Finsupp.single g (w.coeff g)), MonoidAlgebra.coeff_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    have hi := congrFun hw i
    simp only [coord, Pi.zero_apply] at hi
    rw [MonoidAlgebra.coeff_add, MonoidAlgebra.coeff_single, MonoidAlgebra.coeff_single,
      show -((ε : A) * w.coeff (c * rep i)) = w.coeff (rep i) by linear_combination -hi]
