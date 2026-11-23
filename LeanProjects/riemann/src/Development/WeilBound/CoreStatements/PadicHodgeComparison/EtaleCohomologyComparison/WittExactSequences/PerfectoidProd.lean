import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.WittExactSequences.IsCompl
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.WittExactSequences.TensCompl

set_option autoImplicit false

open TensorProduct CrystallineSemistableComparison.D
open scoped LaurentPolynomial

namespace CrystallineSemistableComparison.D

theorem perfectoid_prod (p : ℕ) (B₁ B₂ : Type) [CommRing B₁] [CommRing B₂] (h₁ : Pf p B₁) (h₂ : Pf p B₂) :
    Pf p (B₁ × B₂) := by
  refine ⟨Prod.ext (by simp [h₁.char]) (by simp [h₂.char]), fun x y hxy => ?_, fun y => ?_⟩
  · have h1 : x.1 ^ p = y.1 ^ p := congrArg Prod.fst hxy
    have h2 : x.2 ^ p = y.2 ^ p := congrArg Prod.snd hxy
    exact Prod.ext (h₁.bij.1 h1) (h₂.bij.1 h2)
  · obtain ⟨a, ha⟩ := h₁.bij.2 y.1
    obtain ⟨b, hb⟩ := h₂.bij.2 y.2
    exact ⟨(a, b), Prod.ext ha hb⟩

theorem cov_blow : ∀ (p : ℕ) [Fact p.Prime] (A : Type) [CommRing A] (r : ℕ → A) (f g : A) (N : ℕ), Pf p A → IsRt p r → r 0 ^ N ∈ Ideal.span {f, g} → ∃ (B : Type) (_ : CommRing B) (_ : Algebra A B), Pf p B ∧ Cov p r B ∧ ∃ e u v : B, e * e = e ∧ e * algebraMap A B f = u * algebraMap A B g ∧ (1 - e) * algebraMap A B g = v * algebraMap A B f := by
  intro p _ A _ r f g N hA hr hN
  have hpA : ((p : Polynomial A)) = 0 := by
    rw [← map_natCast Polynomial.C, hA.char, map_zero]
  have hpL : ((p : A[T;T⁻¹])) = 0 := by
    rw [← map_natCast LaurentPolynomial.C, hA.char, map_zero]
  obtain ⟨T₁, _, i₁, hP1⟩ := Leaf.pq_ex p (Polynomial A)
    (Ideal.span {Polynomial.C f - Polynomial.X * Polynomial.C g}) hpA
  obtain ⟨T₂, _, i₂, hP2⟩ := Leaf.pq_ex p (Polynomial A)
    (Ideal.span {Polynomial.C g - Polynomial.X * Polynomial.C f}) hpA
  obtain ⟨T₃, _, i₃, hP3⟩ := Leaf.pq_ex p A[T;T⁻¹]
    (Ideal.span {LaurentPolynomial.C f - LaurentPolynomial.T 1 * LaurentPolynomial.C g}) hpL
  have k1 : i₁ (Polynomial.C f - Polynomial.X * Polynomial.C g) = 0 :=
    (hP1.ker _).2 ⟨0, by rw [pow_zero, pow_one]; exact Ideal.subset_span (Set.mem_singleton _)⟩
  have k2 : i₂ (Polynomial.C g - Polynomial.X * Polynomial.C f) = 0 :=
    (hP2.ker _).2 ⟨0, by rw [pow_zero, pow_one]; exact Ideal.subset_span (Set.mem_singleton _)⟩
  have k3 : i₃ (LaurentPolynomial.C f - LaurentPolynomial.T 1 * LaurentPolynomial.C g) = 0 :=
    (hP3.ker _).2 ⟨0, by rw [pow_zero, pow_one]; exact Ideal.subset_span (Set.mem_singleton _)⟩
  have k1' : i₁ (Polynomial.C f) = i₁ Polynomial.X * i₁ (Polynomial.C g) := by
    rwa [map_sub, map_mul, sub_eq_zero] at k1
  have k2' : i₂ (Polynomial.C g) = i₂ Polynomial.X * i₂ (Polynomial.C f) := by
    rwa [map_sub, map_mul, sub_eq_zero] at k2
  have e1 : Polynomial.toLaurent (Polynomial.C f - Polynomial.X * Polynomial.C g) =
      LaurentPolynomial.C f - LaurentPolynomial.T 1 * LaurentPolynomial.C g := by
    rw [map_sub, map_mul, Polynomial.toLaurent_C, Polynomial.toLaurent_C, Polynomial.toLaurent_X]
  have e2 : LaurentPolynomial.invert (Polynomial.toLaurent (Polynomial.C g - Polynomial.X * Polynomial.C f)) =
      -LaurentPolynomial.T (-1) * (LaurentPolynomial.C f - LaurentPolynomial.T 1 * LaurentPolynomial.C g) := by
    have hT : (LaurentPolynomial.T (-1) : A[T;T⁻¹]) * LaurentPolynomial.T 1 = 1 := by
      rw [← LaurentPolynomial.T_add]; simp
    rw [map_sub, map_mul, Polynomial.toLaurent_C, Polynomial.toLaurent_C, Polynomial.toLaurent_X, map_sub, map_mul,
      LaurentPolynomial.invert_C, LaurentPolynomial.invert_C, LaurentPolynomial.invert_T]
    linear_combination (-(LaurentPolynomial.C g : A[T;T⁻¹])) * hT
  let φ₁ : Polynomial A →+* T₃ := i₃.comp Polynomial.toLaurent
  let φ₂ : Polynomial A →+* T₃ :=
    i₃.comp ((RingHomClass.toRingHom (LaurentPolynomial.invert (R := A))).comp Polynomial.toLaurent)
  have hs1 : ∀ x ∈ Ideal.span {Polynomial.C f - Polynomial.X * Polynomial.C g}, φ₁ x = 0 := by
    intro x hx
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.1 hx
    have : φ₁ (Polynomial.C f - Polynomial.X * Polynomial.C g) = 0 := by
      show i₃ (Polynomial.toLaurent _) = 0
      rw [e1, k3]
    rw [map_mul, this, mul_zero]
  have hs2 : ∀ x ∈ Ideal.span {Polynomial.C g - Polynomial.X * Polynomial.C f}, φ₂ x = 0 := by
    intro x hx
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.1 hx
    have : φ₂ (Polynomial.C g - Polynomial.X * Polynomial.C f) = 0 := by
      show i₃ (LaurentPolynomial.invert (Polynomial.toLaurent _)) = 0
      rw [e2, map_mul, k3, mul_zero]
    rw [map_mul, this, mul_zero]
  obtain ⟨ψ₁, hψ₁, -⟩ := Leaf.pq_lift p (Polynomial A) T₁ T₃ i₁ _ φ₁ hP1 hP3.pf hs1
  obtain ⟨ψ₂, hψ₂, -⟩ := Leaf.pq_lift p (Polynomial A) T₂ T₃ i₂ _ φ₂ hP2 hP3.pf hs2
  have hρ1 : ∀ α, ψ₁ (i₁ α) = i₃ (Polynomial.toLaurent α) := fun α => RingHom.congr_fun hψ₁ α
  have hρ2 : ∀ β, ψ₂ (i₂ β) = i₃ (LaurentPolynomial.invert (Polynomial.toLaurent β)) :=
    fun β => RingHom.congr_fun hψ₂ β
  letI : Algebra A T₁ := (i₁.comp Polynomial.C).toAlgebra
  letI : Algebra A T₂ := (i₂.comp Polynomial.C).toAlgebra
  letI : Algebra A T₃ := (i₃.comp LaurentPolynomial.C).toAlgebra
  have c1' : ∀ a : A, i₁ (algebraMap A (Polynomial A) a) = algebraMap A T₁ a := fun a => by
    rw [Polynomial.algebraMap_eq]; rfl
  have c2' : ∀ a : A, i₂ (algebraMap A (Polynomial A) a) = algebraMap A T₂ a := fun a => by
    rw [Polynomial.algebraMap_eq]; rfl
  have c3' : ∀ a : A, i₃ (algebraMap A A[T;T⁻¹] a) = algebraMap A T₃ a := fun a => by
    rw [LaurentPolynomial.algebraMap_apply]; rfl
  have d1' : ∀ a : A, ψ₁ (algebraMap A T₁ a) = algebraMap A T₃ a := fun a => by
    show ψ₁ (i₁ (Polynomial.C a)) = i₃ (LaurentPolynomial.C a)
    rw [hρ1, Polynomial.toLaurent_C]
  have d2' : ∀ a : A, ψ₂ (algebraMap A T₂ a) = algebraMap A T₃ a := fun a => by
    show ψ₂ (i₂ (Polynomial.C a)) = i₃ (LaurentPolynomial.C a)
    rw [hρ2, Polynomial.toLaurent_C, LaurentPolynomial.invert_C]
  let i₁' : Polynomial A →ₐ[A] T₁ := { i₁ with commutes' := c1' }
  let i₂' : Polynomial A →ₐ[A] T₂ := { i₂ with commutes' := c2' }
  let i₃' : A[T;T⁻¹] →ₐ[A] T₃ := { i₃ with commutes' := c3' }
  let ρ₁ : T₁ →ₐ[A] T₃ := { ψ₁ with commutes' := d1' }
  let ρ₂ : T₂ →ₐ[A] T₃ := { ψ₂ with commutes' := d2' }
  refine ⟨T₁ × T₂, inferInstance, inferInstance, perfectoid_prod p T₁ T₂ hP1.pf hP2.pf, ?_,
    (1, 0), (i₁ Polynomial.X, 0), (0, i₂ Polynomial.X), ?_, ?_, ?_⟩
  · refine Leaf.mv_prod p A T₁ T₂ T₃ r ρ₁ ρ₂ hr hP3.pf
      (Leaf.b_surj p A T₁ T₂ T₃ f g i₁ i₂ i₃ ψ₁ ψ₂ hA hP1 hP2 hP3 hρ1 hρ2) ?_
    intro K _ _ hK
    obtain ⟨j₁, hj1, hj1C, hj1X⟩ := Leaf.bc_poly p A T₁ K i₁'
      (Polynomial.C f - Polynomial.X * Polynomial.C g) hA hK hP1
    obtain ⟨j₂, hj2, hj2C, hj2X⟩ := Leaf.bc_poly p A T₂ K i₂'
      (Polynomial.C g - Polynomial.X * Polynomial.C f) hA hK hP2
    obtain ⟨j₃, hj3, hj3C, hj3T⟩ := Leaf.bc_laur p A T₃ K i₃' f g hA hK hP3
    rw [Polynomial.map_sub, Polynomial.map_mul, Polynomial.map_C, Polynomial.map_C, Polynomial.map_X] at hj1 hj2
    refine ⟨fun a h1 h2 k => ?_, fun w₁ w₂ hw => ?_⟩
    · have hr' : IsRt p (fun k => algebraMap A K (r k)) := fun k => by
        show algebraMap A K (r (k + 1)) ^ p = algebraMap A K (r k)
        rw [← map_pow, hr k]
      have hN' : algebraMap A K (r 0) ^ N ∈ Ideal.span {algebraMap A K f, algebraMap A K g} := by
        have := Ideal.mem_map_of_mem (algebraMap A K) hN
        rwa [Ideal.map_span, Set.image_pair, map_pow] at this
      rw [Algebra.smul_def]
      exact Leaf.b_inj p K _ _ _ _ j₁ j₂ (fun k => algebraMap A K (r k)) N hK hr' hN' hj1 hj2 a
        (by rw [hj1C]; exact h1) (by rw [hj2C]; exact h2) k
    · let σ₁ : T₁ ⊗[A] K →+* T₃ ⊗[A] K := (Algebra.TensorProduct.map ρ₁ (AlgHom.id A K)).toRingHom
      let σ₂ : T₂ ⊗[A] K →+* T₃ ⊗[A] K := (Algebra.TensorProduct.map ρ₂ (AlgHom.id A K)).toRingHom
      have c1 : ∀ α, σ₁ (j₁ α) = j₃ (Polynomial.toLaurent α) := by
        have : σ₁.comp j₁ = j₃.comp Polynomial.toLaurent := by
          refine Polynomial.ringHom_ext (fun a => ?_) ?_
          · show Algebra.TensorProduct.map ρ₁ (AlgHom.id A K) (j₁ (Polynomial.C a)) =
              j₃ (Polynomial.toLaurent (Polynomial.C a))
            rw [hj1C, Polynomial.toLaurent_C, hj3C, Algebra.TensorProduct.map_tmul, map_one, AlgHom.id_apply]
          · show Algebra.TensorProduct.map ρ₁ (AlgHom.id A K) (j₁ Polynomial.X) =
              j₃ (Polynomial.toLaurent Polynomial.X)
            rw [hj1X, Polynomial.toLaurent_X, hj3T, Algebra.TensorProduct.map_tmul, AlgHom.id_apply]
            congr 1
            exact (hρ1 _).trans (congrArg i₃ Polynomial.toLaurent_X)
        exact fun α => RingHom.congr_fun this α
      have c2 : ∀ β, σ₂ (j₂ β) = j₃ (LaurentPolynomial.invert (Polynomial.toLaurent β)) := by
        have : σ₂.comp j₂ =
            j₃.comp ((RingHomClass.toRingHom (LaurentPolynomial.invert (R := K))).comp Polynomial.toLaurent) := by
          refine Polynomial.ringHom_ext (fun a => ?_) ?_
          · show Algebra.TensorProduct.map ρ₂ (AlgHom.id A K) (j₂ (Polynomial.C a)) =
              j₃ (LaurentPolynomial.invert (Polynomial.toLaurent (Polynomial.C a)))
            rw [hj2C, Polynomial.toLaurent_C, LaurentPolynomial.invert_C, hj3C, Algebra.TensorProduct.map_tmul,
              map_one, AlgHom.id_apply]
          · show Algebra.TensorProduct.map ρ₂ (AlgHom.id A K) (j₂ Polynomial.X) =
              j₃ (LaurentPolynomial.invert (Polynomial.toLaurent Polynomial.X))
            rw [hj2X, Polynomial.toLaurent_X, LaurentPolynomial.invert_T, hj3T, Algebra.TensorProduct.map_tmul,
              AlgHom.id_apply]
            congr 1
            exact (hρ2 _).trans (by rw [Polynomial.toLaurent_X, LaurentPolynomial.invert_T]; rfl)
        exact fun β => RingHom.congr_fun this β
      obtain ⟨a, ha1, ha2⟩ := Leaf.b_mid p K _ _ _ _ _ j₁ j₂ j₃ σ₁ σ₂ hK hj1 hj2 hj3 c1 c2 w₁ w₂ hw
      exact ⟨a, by rw [← ha1, hj1C], by rw [← ha2, hj2C]⟩
  · ext <;> simp
  · refine Prod.ext ?_ ?_
    · show 1 * i₁ (Polynomial.C f) = i₁ Polynomial.X * i₁ (Polynomial.C g)
      rw [one_mul, k1']
    · show (0 : T₂) * i₂ (Polynomial.C f) = 0 * i₂ (Polynomial.C g)
      rw [zero_mul, zero_mul]
  · refine Prod.ext ?_ ?_
    · show (1 - 1 : T₁) * i₁ (Polynomial.C g) = 0 * i₁ (Polynomial.C f)
      rw [sub_self, zero_mul, zero_mul]
    · show (1 - 0 : T₂) * i₂ (Polynomial.C g) = i₂ Polynomial.X * i₂ (Polynomial.C f)
      rw [sub_zero, one_mul, k2']

end CrystallineSemistableComparison.D
