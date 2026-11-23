import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.OfDetToDet
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.IsLocalHom
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.HomTwo

open TensorProduct IsLocalRing Polynomial UpperTheory.V.W UpperTheory.V.Alg UpperTheory.V.CA

namespace UpperTheory.V.CA

section Fac

variable {k : ℕ} {F : Type} [Ring F]

private def amJ (x : Fin k → F) (N : ℕ) : AddSubmonoid F :=
  AddSubmonoid.closure {z | ∃ (c : ℤ) (w : FreeMonoid (Fin k)), N ≤ w.length ∧ z = c • FreeMonoid.lift x w}

private def amP (x : Fin k → F) (L : List (ℤ × FreeMonoid (Fin k))) : F :=
  (L.map fun p => 1 + p.1 • FreeMonoid.lift x p.2).prod

private theorem amJ_mono (x : Fin k → F) {a b : ℕ} (h : a ≤ b) : amJ x b ≤ amJ x a :=
  AddSubmonoid.closure_mono fun _ ⟨c, w, hw, e⟩ => ⟨c, w, h.trans hw, e⟩

private theorem amJ_mul (x : Fin k → F) {a b : ℕ} {y z : F} (hy : y ∈ amJ x a) (hz : z ∈ amJ x b) :
    y * z ∈ amJ x (a + b) := by
  induction hy using AddSubmonoid.closure_induction with
  | zero => simp
  | add u v _ _ hu hv => rw [add_mul]; exact add_mem hu hv
  | mem u hu =>
    induction hz using AddSubmonoid.closure_induction with
    | zero => simp
    | add u v _ _ hu hv => rw [mul_add]; exact add_mem hu hv
    | mem v hv =>
      obtain ⟨c, w, hw, rfl⟩ := hu
      obtain ⟨c', w', hw', rfl⟩ := hv
      refine AddSubmonoid.subset_closure ⟨c * c', w * w', ?_, ?_⟩
      · rw [FreeMonoid.length_mul]; omega
      · rw [map_mul, smul_mul_smul_comm]

private theorem amJ_neg (x : Fin k → F) {a : ℕ} {y : F} (hy : y ∈ amJ x a) : -y ∈ amJ x a := by
  induction hy using AddSubmonoid.closure_induction with
  | zero => simp
  | add u v _ _ hu hv => rw [neg_add]; exact add_mem hu hv
  | mem u hu =>
    obtain ⟨c, w, hw, rfl⟩ := hu
    exact AddSubmonoid.subset_closure ⟨-c, w, hw, (neg_smul _ _).symm⟩

private theorem amJ_step (x : Fin k → F) {N : ℕ} {d : F} (hd : d ∈ amJ x (N + 1)) :
    ∃ L : List (ℤ × FreeMonoid (Fin k)), (∀ p ∈ L, p.2 ≠ 1) ∧ ∃ e ∈ amJ x (N + 2), amP x L = 1 + d + e := by
  induction hd using AddSubmonoid.closure_induction with
  | zero => exact ⟨[], by simp, 0, zero_mem _, by simp [amP]⟩
  | mem u hu =>
    obtain ⟨c, w, hw, rfl⟩ := hu
    refine ⟨[(c, w)], ?_, 0, zero_mem _, by simp [amP]⟩
    intro p hp h
    rw [List.mem_singleton] at hp
    subst hp
    simp only at h
    rw [h] at hw
    simp at hw
  | add u v hu hv ihu ihv =>
    obtain ⟨L, hL, e, he, h⟩ := ihu
    obtain ⟨L', hL', e', he', h'⟩ := ihv
    refine ⟨L ++ L', fun p hp => (List.mem_append.1 hp).elim (hL p) (hL' p), e + e' + (u + e) * (v + e'), ?_, ?_⟩
    · refine add_mem (add_mem he he') (amJ_mono x (by omega)
        (amJ_mul x (add_mem hu (amJ_mono x (by omega) he)) (add_mem hv (amJ_mono x (by omega) he'))))
    · have : amP x (L ++ L') = amP x L * amP x L' := by simp [amP]
      rw [this, h, h']; noncomm_ring

private theorem amJ_fac (x : Fin k → F) (N : ℕ) :
    ∃ L : List (ℤ × FreeMonoid (Fin k)), (∀ p ∈ L, p.2 ≠ 1) ∧ (∃ q ∈ amJ x 1, amP x L = 1 + q) ∧
      ∃ d ∈ amJ x (N + 1), 1 + ∑ a, x a = amP x L + d := by
  induction N with
  | zero =>
    refine ⟨[], by simp, ⟨0, zero_mem _, by simp [amP]⟩, ∑ a, x a, ?_, by simp [amP]⟩
    exact sum_mem fun a _ => AddSubmonoid.subset_closure ⟨1, FreeMonoid.of a, by simp, by simp⟩
  | succ N ih =>
    obtain ⟨L, hL, ⟨q, hq, h1⟩, d, hd, h2⟩ := ih
    obtain ⟨L', hL', e, he, h3⟩ := amJ_step x hd
    have h4 : amP x (L ++ L') = amP x L * amP x L' := by simp [amP]
    have hde : d + e ∈ amJ x (N + 1) := add_mem hd (amJ_mono x (by omega) he)
    refine ⟨L ++ L', fun p hp => (List.mem_append.1 hp).elim (hL p) (hL' p),
      ⟨q + (d + e) + q * (d + e), ?_, ?_⟩, -(e + q * (d + e)), ?_, ?_⟩
    · exact add_mem (add_mem hq (amJ_mono x (by omega) hde)) (amJ_mono x (by omega) (amJ_mul x hq hde))
    · rw [h4, h1, h3]; noncomm_ring
    · exact amJ_neg x (add_mem he (amJ_mono x (by omega) (amJ_mul x hq hde)))
    · rw [h2, h4, h1, h3]; noncomm_ring

private theorem am_univ (k N : ℕ) :
    ∃ L : List (ℤ × FreeMonoid (Fin k)), (∀ p ∈ L, p.2 ≠ 1) ∧ ∀ (F : Type) [Ring F] (x : Fin k → F),
      (∀ w : FreeMonoid (Fin k), N < w.length → FreeMonoid.lift x w = 0) → 1 + ∑ a, x a = amP x L := by
  obtain ⟨L, hL, -, d, hd, h⟩ := amJ_fac (FreeAlgebra.ι ℤ : Fin k → FreeAlgebra ℤ (Fin k)) N
  refine ⟨L, hL, fun F _ x hx => ?_⟩
  have hw : ∀ w : FreeMonoid (Fin k), FreeAlgebra.lift ℤ x (FreeMonoid.lift (FreeAlgebra.ι ℤ) w) =
      FreeMonoid.lift x w := by
    intro w
    induction w using FreeMonoid.inductionOn' with
    | one => simp
    | of_mul a w ih => simp [ih]
  have h0 : FreeAlgebra.lift ℤ x d = 0 := by
    clear h
    induction hd using AddSubmonoid.closure_induction with
    | zero => simp
    | add u v _ _ hu hv => rw [map_add, hu, hv, add_zero]
    | mem u hu =>
      obtain ⟨c, w, hw', rfl⟩ := hu
      rw [map_zsmul, hw, hx w (by omega), smul_zero]
  have := congrArg (FreeAlgebra.lift ℤ x) h
  rw [map_add, map_add, h0, add_zero, map_one, map_sum, amP, map_list_prod, List.map_map] at this
  simp only [FreeAlgebra.lift_ι_apply] at this
  rw [this, amP]
  congr 1
  refine List.map_congr_left fun p _ => ?_
  simp only [Function.comp, map_add, map_one, map_zsmul, hw]

end Fac

section Pol

variable {k : ℕ}

private noncomputable def amWt (w : FreeMonoid (Fin k)) : Fin k →₀ ℕ := Multiset.toFinsupp (w.toList : Multiset (Fin k))

private def amGood (n : ℕ) (Q : MvPolynomial (Fin k) (MvPolynomial (ℕ × FreeMonoid (Fin k)) ℤ)) : Prop :=
  ∀ β, MvPolynomial.coeff β Q ∈ MvPolynomial.supported ℤ {v : ℕ × FreeMonoid (Fin k) | 1 ≤ v.1 ∧ v.1 ≤ n ∧ v.2 ≠ 1} ∧
    (MvPolynomial.coeff β Q).IsWeightedHomogeneous (fun v => v.1 • amWt v.2) β

private theorem amGood_mon (n : ℕ) (γ : Fin k →₀ ℕ) (P : MvPolynomial (ℕ × FreeMonoid (Fin k)) ℤ)
    (h1 : P ∈ MvPolynomial.supported ℤ {v : ℕ × FreeMonoid (Fin k) | 1 ≤ v.1 ∧ v.1 ≤ n ∧ v.2 ≠ 1})
    (h2 : P.IsWeightedHomogeneous (fun v => v.1 • amWt v.2) γ) : amGood n (MvPolynomial.monomial γ P) := by
  intro β
  rw [MvPolynomial.coeff_monomial]
  split_ifs with h
  · exact ⟨h1, h ▸ h2⟩
  · exact ⟨zero_mem _, MvPolynomial.isWeightedHomogeneous_zero _ _ _⟩

private theorem amGood_one (n : ℕ) : amGood (k := k) n 1 :=
  amGood_mon n 0 1 (one_mem _) (MvPolynomial.isWeightedHomogeneous_one _ _)

private theorem amGood_add {n : ℕ} {Q Q'} (h : amGood (k := k) n Q) (h' : amGood n Q') : amGood n (Q + Q') := by
  intro β
  rw [MvPolynomial.coeff_add]
  exact ⟨add_mem (h β).1 (h' β).1, (h β).2.add (h' β).2⟩

private theorem amGood_sum {n : ℕ} {ι : Type} (s : Finset ι) (f : ι → _) (h : ∀ i ∈ s, amGood (k := k) n (f i)) :
    amGood n (∑ i ∈ s, f i) := by
  intro β
  rw [MvPolynomial.coeff_sum]
  exact ⟨sum_mem fun i hi => (h i hi β).1, MvPolynomial.IsWeightedHomogeneous.sum _ _ _ fun i hi => (h i hi β).2⟩

private theorem amGood_mul {n : ℕ} {Q Q'} (h : amGood (k := k) n Q) (h' : amGood n Q') : amGood n (Q * Q') := by
  intro β
  rw [MvPolynomial.coeff_mul]
  refine ⟨sum_mem fun i hi => mul_mem (h _).1 (h' _).1, MvPolynomial.IsWeightedHomogeneous.sum _ _ _ fun i hi => ?_⟩
  have hi' : i.1 + i.2 = β := by simpa using hi
  rw [← hi']
  exact (h _).2.mul (h' _).2

private noncomputable def amF (n : ℕ) (p : ℤ × FreeMonoid (Fin k)) :
    MvPolynomial (Fin k) (MvPolynomial (ℕ × FreeMonoid (Fin k)) ℤ) :=
  1 + ∑ i ∈ Finset.range n, MvPolynomial.monomial ((i + 1) • amWt p.2)
    (MvPolynomial.C (p.1 ^ (i + 1)) * MvPolynomial.X (i + 1, p.2))

private theorem amGood_F (n : ℕ) (p : ℤ × FreeMonoid (Fin k)) (hp : p.2 ≠ 1) : amGood n (amF n p) := by
  refine amGood_add (amGood_one n) (amGood_sum _ _ fun i hi => amGood_mon n _ _ ?_ ?_)
  · refine mul_mem (Subalgebra.algebraMap_mem _ _) (MvPolynomial.X_mem_supported.2 ⟨by simp, ?_, hp⟩)
    exact Finset.mem_range.1 hi
  · exact (MvPolynomial.isWeightedHomogeneous_X ℤ (fun v : ℕ × FreeMonoid (Fin k) => v.1 • amWt v.2)
      (i + 1, p.2)).C_mul _

private theorem amGood_prod (n : ℕ) (L : List (ℤ × FreeMonoid (Fin k))) (hL : ∀ p ∈ L, p.2 ≠ 1) :
    amGood n (L.map (amF n)).prod := by
  induction L with
  | nil => exact amGood_one n
  | cons p L ih =>
    rw [List.map_cons, List.prod_cons]
    exact amGood_mul (amGood_F n p (hL p (by simp))) (ih fun q hq => hL q (by simp [hq]))

private theorem amWt_degree (w : FreeMonoid (Fin k)) : (amWt w).degree = w.length := by
  induction w using FreeMonoid.inductionOn' with
  | one => simp [amWt]
  | of_mul a w ih =>
    have : amWt (FreeMonoid.of a * w) = Finsupp.single a 1 + amWt w := by
      simp only [amWt, FreeMonoid.toList_of_mul, ← Multiset.cons_coe, ← Multiset.singleton_add, map_add,
        Multiset.toFinsupp_singleton]
    rw [this, map_add, ih]; simp

private theorem am_lift {A E B : Type} [CommRing A] [Ring E] [Algebra A E] [CommRing B] [Algebra A B]
    (π : MvPolynomial (Fin k) A →ₐ[A] B) (x : Fin k → E) (w : FreeMonoid (Fin k)) :
    FreeMonoid.lift (fun a => π (MvPolynomial.X a) ⊗ₜ[A] x a) w =
      π (MvPolynomial.monomial (amWt w) 1) ⊗ₜ[A] FreeMonoid.lift x w := by
  induction w using FreeMonoid.inductionOn' with
  | one => simp [amWt, Algebra.TensorProduct.one_def]
  | of_mul a w ih =>
    have : amWt (FreeMonoid.of a * w) = Finsupp.single a 1 + amWt w := by
      simp only [amWt, FreeMonoid.toList_of_mul, ← Multiset.cons_coe, ← Multiset.singleton_add, map_add,
        Multiset.toFinsupp_singleton]
    rw [this, map_mul, map_mul, ih, FreeMonoid.lift_eval_of, FreeMonoid.lift_eval_of,
      Algebra.TensorProduct.tmul_mul_tmul, ← map_mul, MvPolynomial.X, MvPolynomial.monomial_mul, one_mul]

private theorem am_one {n : ℕ} {A E B : Type} [CommRing A] [Ring E] [Algebra A E] [CommRing B] [Algebra A B]
    (D : Det n A E) (b : B) (y : E) :
    D.D B (1 + b ⊗ₜ y) = 1 + ∑ i ∈ Finset.range n, algebraMap A B (D.lam (i + 1) y) * b ^ (i + 1) := by
  obtain ⟨h0, -, h, -⟩ := d_chi D y
  have := D.nat A[X] B (Polynomial.aeval b) (1 + X ⊗ₜ y)
  rw [h, map_add, map_one, Algebra.TensorProduct.map_tmul, aeval_X, AlgHom.id_apply] at this
  rw [this, Finset.sum_range_succ', h0, add_comm]
  simp

end Pol

end UpperTheory.V.CA

theorem UpperTheory.V.CA.d_amitsur :
    ∀ (n k : ℕ) (α : Fin k →₀ ℕ), ∃ P : MvPolynomial (ℕ × FreeMonoid (Fin k)) ℤ, (∀ v ∈ P.vars, 1 ≤ v.1 ∧ v.1 ≤ n ∧ v.2 ≠ 1) ∧ P.IsWeightedHomogeneous (fun v => v.1 • Multiset.toFinsupp (v.2.toList : Multiset (Fin k))) α ∧ ∀ {A E : Type} [CommRing A] [Ring E] [Algebra A E] (D : Det n A E) (x : Fin k → E), MvPolynomial.coeff α (D.D (MvPolynomial (Fin k) A) (1 + Det.gen x)) = MvPolynomial.aeval (fun v => D.lam v.1 (FreeMonoid.lift x v.2)) P := by
  intro n k α
  obtain ⟨L, hL, hu⟩ := am_univ k α.degree
  have hg := amGood_prod n L hL α
  refine ⟨_, fun v hv => MvPolynomial.mem_supported.1 hg.1 hv, hg.2, ?_⟩
  intro A E _ _ _ D x
  let I : Ideal (MvPolynomial (Fin k) A) :=
    Ideal.span ((fun s => MvPolynomial.monomial s 1) '' {β : Fin k →₀ ℕ | α.degree < β.degree})
  let π := Ideal.Quotient.mkₐ A I
  let φ : MvPolynomial (ℕ × FreeMonoid (Fin k)) ℤ →+* A :=
    (MvPolynomial.aeval (R := ℤ) (fun v : ℕ × FreeMonoid (Fin k) => D.lam v.1 (FreeMonoid.lift x v.2))).toRingHom
  have h1 := hu ((MvPolynomial (Fin k) A ⧸ I) ⊗[A] E) (fun a => π (MvPolynomial.X a) ⊗ₜ[A] x a) fun w hw => by
    have : π (MvPolynomial.monomial (amWt w) 1) = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.subset_span ⟨amWt w, by simpa [amWt_degree] using hw, rfl⟩)
    rw [am_lift, this, zero_tmul]
  have h2 : π (D.D (MvPolynomial (Fin k) A) (1 + Det.gen x)) = π (MvPolynomial.map φ (L.map (amF n)).prod) := by
    rw [← D.nat, map_add, map_one, Det.gen, map_sum]
    simp only [Algebra.TensorProduct.map_tmul, AlgHom.id_apply]
    rw [h1, amP, map_list_prod, map_list_prod, map_list_prod, List.map_map, List.map_map, List.map_map]
    congr 1
    refine List.map_congr_left fun p _ => ?_
    simp only [Function.comp]
    rw [am_lift, smul_tmul', am_one, amF, map_add, map_add, map_one (MvPolynomial.map φ), map_one π, map_sum, map_sum]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← map_zsmul, ← map_pow, ← π.commutes, ← map_mul]
    congr 1
    rw [MvPolynomial.map_monomial, _root_.smul_pow, MvPolynomial.monomial_pow, MvPolynomial.smul_monomial,
      MvPolynomial.algebraMap_eq, MvPolynomial.C_mul_monomial]
    congr 1
    simp [φ, mul_comm]
  have h3 := MvPolynomial.mem_ideal_span_monomial_image.1 (Ideal.Quotient.eq.1 h2)
  have h4 : MvPolynomial.coeff α (D.D (MvPolynomial (Fin k) A) (1 + Det.gen x) -
      MvPolynomial.map φ (L.map (amF n)).prod) = 0 := by
    by_contra h
    obtain ⟨β, hβ, hle⟩ := h3 α (MvPolynomial.mem_support_iff.2 h)
    exact absurd (Finsupp.degree_mono hle) (not_le.2 hβ)
  rw [MvPolynomial.coeff_sub, sub_eq_zero, MvPolynomial.coeff_map] at h4
  exact h4
