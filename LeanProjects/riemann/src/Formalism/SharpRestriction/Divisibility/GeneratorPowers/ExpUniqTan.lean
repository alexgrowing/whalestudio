import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ExpUniqLoc

set_option autoImplicit false

noncomputable section

namespace Formalism.MainNotions.ModuliIntegralCharts.H1.ExpUniqTan

open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open MvPolynomial Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1.ExpUniqJet Formalism.MainNotions.ModuliIntegralCharts.H1.ExpUniqLoc
open ReciprocityTheory.ChartRestriction.G.Chart (JetR zR IsUnivChart sp spMap spMap_comp comp_one')

attribute [local instance] Over.cartesianMonoidalCategory

variable {R : Type} [CommRing R]

theorem jetTan_alt {κ : Type} [DecidableEq κ] (ℓ j : κ) :
    (jetTan ℓ : Jet R κ (0 + 1) →ₐ[R] DualNumber R) (zz (0 + 1) j) = if j = ℓ then DualNumber.eps else 0 := by
  show (aeval fun i => if i = ℓ then (DualNumber.eps : DualNumber R) else 0) (X j) = _
  rw [aeval_X]

private theorem sub_C_mem_lemma {κ : Type} (r : MvPolynomial κ R) : r - C (constantCoeff r) ∈ orig R κ := by
  refine MvPolynomial.induction_on (motive := fun r => r - C (constantCoeff r) ∈ orig R κ) r ?_ ?_ ?_
  · intro a
    simp
  · intro p q hp hq
    have e : p + q - C (constantCoeff (p + q)) = (p - C (constantCoeff p)) + (q - C (constantCoeff q)) := by
      rw [map_add, map_add]
      ring
    rw [e]
    exact add_mem hp hq
  · intro p i _
    have e : p * X i - C (constantCoeff (p * X i)) = p * X i := by simp
    rw [e]
    exact Ideal.mul_mem_left _ _ (by first | exact Ideal.subset_span ⟨i, rfl⟩ | (unfold orig; exact Ideal.subset_span ⟨i, rfl⟩))

private theorem aug_mk_lemma_2 {κ : Type} (r : MvPolynomial κ R) :
    (jetAug : Jet R κ (0 + 1) →ₐ[R] R) (Ideal.Quotient.mk (orig R κ ^ (0 + 1 + 1)) r) = constantCoeff r := by
  have e : (jetAug : Jet R κ (0 + 1) →ₐ[R] R) (Ideal.Quotient.mk (orig R κ ^ (0 + 1 + 1)) r)
      = (aeval fun _ : κ => (0 : R)) r := by
    first | rfl | simp [jetAug, liftJet]
  rw [e]
  refine MvPolynomial.induction_on (motive := fun r => (aeval fun _ : κ => (0 : R)) r = constantCoeff r) r ?_ ?_ ?_
  · intro a
    simp
  · intro p q hp hq
    simp only [map_add, hp, hq]
  · intro p i _
    simp

private theorem orig_sq_lemma_3 {κ : Type} : orig R κ ^ (0 + 1 + 1) = orig R κ * orig R κ := by
  first | exact pow_two _ | rw [pow_succ, pow_succ, pow_zero, one_mul]

private theorem mul_zz_lemma_4 {κ : Type} (c : Jet R κ (0 + 1)) (i : κ) :
    c * zz (0 + 1) i = algebraMap R (Jet R κ (0 + 1)) ((jetAug : Jet R κ (0 + 1) →ₐ[R] R) c) * zz (0 + 1) i := by
  obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective c
  rw [aug_mk_lemma_2]
  change Ideal.Quotient.mk (orig R κ ^ (0 + 1 + 1)) r * Ideal.Quotient.mk (orig R κ ^ (0 + 1 + 1)) (X i)
    = Ideal.Quotient.mk (orig R κ ^ (0 + 1 + 1)) (C (constantCoeff r)) * Ideal.Quotient.mk (orig R κ ^ (0 + 1 + 1)) (X i)
  rw [← map_mul, ← map_mul, Ideal.Quotient.eq, ← sub_mul, orig_sq_lemma_3]
  exact Ideal.mul_mem_mul (sub_C_mem_lemma r) (by first | exact Ideal.subset_span ⟨i, rfl⟩ | (unfold orig; exact Ideal.subset_span ⟨i, rfl⟩))

private theorem aug_zero_mem_lemma_5 {κ : Type} (p : Jet R κ (0 + 1)) (h : (jetAug : Jet R κ (0 + 1) →ₐ[R] R) p = 0) :
    p ∈ Ij R κ (0 + 1) := by
  obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective p
  rw [aug_mk_lemma_2] at h
  have hr0 : r ∈ orig R κ := by simpa [h] using sub_C_mem_lemma r
  have hr : r ∈ Ideal.span (Set.range (X : κ → MvPolynomial κ R)) := hr0
  have h2 := Ideal.mem_map_of_mem (Ideal.Quotient.mk (orig R κ ^ (0 + 1 + 1))) hr
  rw [Ideal.map_span, ← Set.range_comp] at h2
  exact h2

private theorem ker_aug_sq_lemma_6 {κ : Type} :
    RingHom.ker (jetAug : Jet R κ (0 + 1) →ₐ[R] R) ^ (1 + 1) = ⊥ := by
  have e : RingHom.ker (jetAug : Jet R κ (0 + 1) →ₐ[R] R) ^ (1 + 1)
      = RingHom.ker (jetAug : Jet R κ (0 + 1) →ₐ[R] R) * RingHom.ker (jetAug : Jet R κ (0 + 1) →ₐ[R] R) := by
    first | exact pow_two _ | rw [pow_succ, pow_one]
  rw [e, eq_bot_iff, Ideal.mul_le]
  intro r hr s hs
  rw [RingHom.mem_ker] at hr hs
  rw [Ideal.mem_bot]
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective r
  obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective s
  rw [aug_mk_lemma_2] at hr hs
  have ha : a ∈ orig R κ := by simpa [hr] using sub_C_mem_lemma a
  have hb : b ∈ orig R κ := by simpa [hs] using sub_C_mem_lemma b
  rw [← map_mul, Ideal.Quotient.eq_zero_iff_mem, orig_sq_lemma_3]
  exact Ideal.mul_mem_mul ha hb

theorem eq_zero_of_tan {κ : Type} [Fintype κ] [DecidableEq κ] (p : Jet R κ (0 + 1)) (hp : p ∈ Ij R κ (0 + 1))
    (ht : ∀ ℓ, (jetTan ℓ : Jet R κ (0 + 1) →ₐ[R] DualNumber R) p = 0) : p = 0 := by
  have hp' : p ∈ Ideal.span (Set.range (zz (R := R) (κ := κ) (0 + 1))) := hp
  obtain ⟨c, rfl⟩ := Ideal.mem_span_range_iff_exists_fun.1 hp'
  have e : ∑ i, c i * zz (0 + 1) i
      = ∑ i, algebraMap R (Jet R κ (0 + 1)) ((jetAug : Jet R κ (0 + 1) →ₐ[R] R) (c i)) * zz (0 + 1) i :=
    Finset.sum_congr rfl fun i _ => mul_zz_lemma_4 (c i) i
  rw [e] at ht ⊢
  have ha : ∀ i, (jetAug : Jet R κ (0 + 1) →ₐ[R] R) (c i) = 0 := by
    intro ℓ
    have h := ht ℓ
    simp only [map_sum, map_mul, AlgHom.commutes, jetTan_alt, mul_ite, mul_zero, Finset.sum_ite_eq',
      Finset.mem_univ, if_true] at h
    first
      | (rw [← Algebra.smul_def] at h; simpa using congrArg TrivSqZeroExt.snd h)
      | simpa using congrArg TrivSqZeroExt.snd h
  simp only [ha, map_zero, zero_mul, Finset.sum_const_zero]

abbrev fstA : DualNumber R →ₐ[R] R := TrivSqZeroExt.fstHom R R R

private theorem fst_tan_lemma_7 {κ : Type} [DecidableEq κ] (ℓ : κ) :
    (fstA (R := R)).comp (jetTan ℓ : Jet R κ (0 + 1) →ₐ[R] DualNumber R) = (jetAug : Jet R κ (0 + 1) →ₐ[R] R) := by
  apply Ideal.Quotient.algHom_ext
  apply MvPolynomial.algHom_ext
  intro i
  change fstA (R := R) ((jetTan ℓ : Jet R κ (0 + 1) →ₐ[R] DualNumber R) (zz (0 + 1) i))
    = (jetAug : Jet R κ (0 + 1) →ₐ[R] R) (Ideal.Quotient.mk (orig R κ ^ (0 + 1 + 1)) (X i))
  rw [jetTan_alt, aug_mk_lemma_2]
  split_ifs <;> simp [fstA]

theorem ker_fst_sq : RingHom.ker (fstA (R := R)) ^ (1 + 1) = ⊥ := by
  have e : RingHom.ker (fstA (R := R)) ^ (1 + 1) = RingHom.ker (fstA (R := R)) * RingHom.ker (fstA (R := R)) := by
    first | exact pow_two _ | rw [pow_succ, pow_one]
  rw [e, eq_bot_iff, Ideal.mul_le]
  intro r hr s hs
  rw [RingHom.mem_ker] at hr hs
  rw [Ideal.mem_bot]
  have hr' : r.fst = 0 := by simpa [fstA] using hr
  have hs' : s.fst = 0 := by simpa [fstA] using hs
  first | (ext <;> simp [hr', hs']) | exact TrivSqZeroExt.ext (by simp [hr', hs']) (by simp [hr', hs'])

section Univ

variable {G : Over (Spec (CommRingCat.of R))} [GrpObj G] {n : ℕ} {x : ∀ m : ℕ, sp (R₀ := R) (JetR R (Fin n) m) ⟶ G}
  (hx : IsUnivChart G n x)
include hx

private theorem one_eq_lemma_8 {A : Type} [CommRing A] [Algebra R A] :
    (1 : sp (R₀ := R) A ⟶ G) = spMap ((Algebra.ofId R A).comp (ReciprocityTheory.ChartRestriction.G.Chart.jetAug R (Fin n) 1)) ≫ x 1 := by
  have e : (Algebra.ofId R A).comp (ReciprocityTheory.ChartRestriction.G.Chart.jetAug R (Fin n) 1)
      = ((Algebra.ofId R A).comp (ReciprocityTheory.ChartRestriction.G.Chart.jetAug R (Fin n) 0)).comp
          (ReciprocityTheory.ChartRestriction.G.Chart.jetZeroR R (Fin n) 1) := by
    apply Ideal.Quotient.algHom_ext
    apply MvPolynomial.algHom_ext
    intro i
    first | rfl | simp [ReciprocityTheory.ChartRestriction.G.Chart.jetAug, ReciprocityTheory.ChartRestriction.G.Chart.jetZeroR]
  rw [e, ← spMap_comp, Category.assoc, hx.2.1 1, comp_one']

private theorem eq_triv_lemma_9 {A : Type} [CommRing A] [Algebra R A] (aug : A →ₐ[R] R)
    (hk : RingHom.ker aug ^ (1 + 1) = ⊥) (ψ : JetR R (Fin n) 1 →ₐ[R] A)
    (h1 : aug.comp ψ = ReciprocityTheory.ChartRestriction.G.Chart.jetAug R (Fin n) 1) (h2 : spMap ψ ≫ x 1 = 1) :
    ψ = (Algebra.ofId R A).comp (ReciprocityTheory.ChartRestriction.G.Chart.jetAug R (Fin n) 1) := by
  obtain ⟨_, _, hu⟩ := hx.2.2 A aug 1 hk 1 (comp_one' _)
  refine (hu ψ ⟨h1, h2.symm⟩).trans (hu _ ⟨?_, one_eq_lemma_8 hx⟩).symm
  exact AlgHom.ext fun z => by simp

theorem one_of_tan {κ : Type} [Fintype κ] [DecidableEq κ] (δ : sp (R₀ := R) (Jet R κ (0 + 1)) ⟶ G)
    (hu : spMap (jetAug : Jet R κ (0 + 1) →ₐ[R] R) ≫ δ = 1)
    (ht : ∀ ℓ, spMap (jetTan ℓ : Jet R κ (0 + 1) →ₐ[R] DualNumber R) ≫ δ = 1) : δ = 1 := by
  obtain ⟨ψ, ⟨hψ1, hψ2⟩, -⟩ := hx.2.2 (Jet R κ (0 + 1)) jetAug 1 ker_aug_sq_lemma_6 δ hu
  have htan : ∀ ℓ, (jetTan ℓ : Jet R κ (0 + 1) →ₐ[R] DualNumber R).comp ψ
      = (Algebra.ofId R (DualNumber R)).comp (ReciprocityTheory.ChartRestriction.G.Chart.jetAug R (Fin n) 1) := by
    intro ℓ
    refine eq_triv_lemma_9 hx (fstA (R := R)) ker_fst_sq _ ?_ ?_
    · rw [← AlgHom.comp_assoc, fst_tan_lemma_7, hψ1]
    · rw [← spMap_comp, Category.assoc, ← hψ2, ht ℓ]
  have hψ : ψ = (Algebra.ofId R (Jet R κ (0 + 1))).comp (ReciprocityTheory.ChartRestriction.G.Chart.jetAug R (Fin n) 1) := by
    apply Ideal.Quotient.algHom_ext
    apply MvPolynomial.algHom_ext
    intro k
    have hJ : ReciprocityTheory.ChartRestriction.G.Chart.jetAug R (Fin n) 1 (Ideal.Quotient.mk (Ideal.span (Set.range (X : Fin n → MvPolynomial (Fin n) R)) ^ (1 + 1)) (X k)) = 0 := aeval_X (fun _ : Fin n => (0 : R)) k
    have hz : ψ (Ideal.Quotient.mk (Ideal.span (Set.range (X : Fin n → MvPolynomial (Fin n) R)) ^ (1 + 1)) (X k)) = 0 := by
      apply eq_zero_of_tan
      · apply aug_zero_mem_lemma_5
        have h := congrArg (fun f : JetR R (Fin n) 1 →ₐ[R] R => f (Ideal.Quotient.mk (Ideal.span (Set.range (X : Fin n → MvPolynomial (Fin n) R)) ^ (1 + 1)) (X k))) hψ1
        simp only [AlgHom.comp_apply] at h
        rw [h, hJ]
      · intro ℓ
        have h := congrArg (fun f : JetR R (Fin n) 1 →ₐ[R] DualNumber R => f (Ideal.Quotient.mk (Ideal.span (Set.range (X : Fin n → MvPolynomial (Fin n) R)) ^ (1 + 1)) (X k))) (htan ℓ)
        simp only [AlgHom.comp_apply] at h
        rw [h, hJ, map_zero]
    change ψ (Ideal.Quotient.mk (Ideal.span (Set.range (X : Fin n → MvPolynomial (Fin n) R)) ^ (1 + 1)) (X k)) = _
    rw [hz]
    change 0 = Algebra.ofId R (Jet R κ (0 + 1)) (ReciprocityTheory.ChartRestriction.G.Chart.jetAug R (Fin n) 1 (Ideal.Quotient.mk (Ideal.span (Set.range (X : Fin n → MvPolynomial (Fin n) R)) ^ (1 + 1)) (X k)))
    rw [hJ, map_zero]
  rw [hψ2, hψ, ← one_eq_lemma_8 hx]

theorem trivT [Algebra ℚ R] {d : ℕ} (δ : ∀ m, sp (R₀ := R) (Jet R (Fin 1 × Fin d) m) ⟶ G)
    (htr : ∀ m, spMap (jetTrunc : Jet R (Fin 1 × Fin d) (m + 1) →ₐ[R] Jet R (Fin 1 × Fin d) m) ≫ δ (m + 1) = δ m)
    (hhom : ∀ m, spMap (sumJ d m) ≫ δ m = (spMap (cpy d m 0) ≫ δ m) * (spMap (cpy d m 1) ≫ δ m))
    (ht : ∀ j : Fin d, spMap (jetTan ((0 : Fin 1), j) : Jet R (Fin 1 × Fin d) (0 + 1) →ₐ[R] DualNumber R) ≫ δ 1 = 1) :
    ∀ m, δ m = 1 := by
  refine triv hx δ htr hhom ?_
  have hu : spMap (jetAug : Jet R (Fin 1 × Fin d) 1 →ₐ[R] R) ≫ δ 1 = 1 := by
    have e := congrArg (fun f => spMap (jetAug : Jet R (Fin 2 × Fin d) 1 →ₐ[R] R) ≫ f) (hhom 1)
    simp only [MonObj.comp_mul, ← Category.assoc, spMap_comp, aug_comp_sum, aug_comp_cpy] at e
    exact _root_.mul_eq_left.1 e.symm
  refine one_of_tan hx (δ 1) hu fun ℓ => ?_
  have hℓ : ℓ = ((0 : Fin 1), ℓ.2) := (fin_one_pair_eq_local d ℓ).symm
  rw [hℓ]
  exact ht ℓ.2

end Univ

end Formalism.MainNotions.ModuliIntegralCharts.H1.ExpUniqTan
