import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GaussManinPeriods
import Development.AbelianVarietyTheory.Definitions.ThetaValues.MemAnalyticAtZeroOfEventuallyDifferentiableAt
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ConstantCoeffDpolyOfAdditiveTaylorPts
open Filter Topology

namespace GlobalTheory
namespace SquareZeroSum

open TrivSqZeroExt

theorem isNilpotent_comap {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) (I : Ideal B)
    (hI : IsNilpotent I) (hf : ∀ x y, f x = 0 → f y = 0 → x * y = 0) :
    IsNilpotent (I.comap f) := by
  obtain ⟨m, hm⟩ := hI
  have h1 : (I.comap f) ^ m ≤ RingHom.ker f := by
    have := Ideal.le_comap_pow f (K := I) m
    rw [hm] at this
    exact this
  refine ⟨m + m, ?_⟩
  rw [pow_add, Ideal.zero_eq_bot, eq_bot_iff, Ideal.mul_le]
  intro r hr s hs
  exact (Submodule.mem_bot _).2 (hf r s (h1 hr) (h1 hs))

theorem isNilpotent_of_comap {A B : Type} [CommRing A] [CommRing B] (f : A →+* B)
    (hf : Function.Surjective f) (I : Ideal B) (hI : IsNilpotent (I.comap f)) :
    IsNilpotent I := by
  obtain ⟨m, hm⟩ := hI
  refine ⟨m, ?_⟩
  rw [← Ideal.map_comap_of_surjective f hf I, ← Ideal.map_pow, hm]
  simp

section
variable {K : Type} [Fintype K] [DecidableEq K] {D : Type} [CommRing D] (δ : K → D)

theorem prod_fst_snd {ι : Type} [DecidableEq ι] (s : ι → K) (t : Finset ι) :
    (∏ a ∈ t, ((inl (δ (s a)) : TrivSqZeroExt D (K → D)) - inr (Pi.single (s a) 1))).fst
        = ∏ a ∈ t, δ (s a) ∧
      ∑ k, (∏ a ∈ t, ((inl (δ (s a)) : TrivSqZeroExt D (K → D))
          - inr (Pi.single (s a) 1))).snd k * δ k = -(t.card : D) * ∏ a ∈ t, δ (s a) := by
  induction t using Finset.induction_on with
  | empty => simp
  | insert a t ha ih =>
    obtain ⟨h1, h2⟩ := ih
    rw [Finset.prod_insert ha, Finset.prod_insert ha, Finset.card_insert_of_notMem ha]
    generalize (∏ a ∈ t, ((inl (δ (s a)) : TrivSqZeroExt D (K → D))
      - inr (Pi.single (s a) 1))) = P at h1 h2 ⊢
    refine ⟨by simp [h1], ?_⟩
    have h3 : ∀ k, ((((inl (δ (s a)) : TrivSqZeroExt D (K → D))
        - inr (Pi.single (s a) 1))) * P).snd k * δ k
        = δ (s a) * (P.snd k * δ k) - P.fst * ((Pi.single (s a) 1 : K → D) k * δ k) := by
      intro k
      simp [snd_mul]
      ring
    simp only [h3, Finset.sum_sub_distrib, ← Finset.mul_sum, h2, h1]
    simp [Pi.single_apply]
    ring

end

theorem step (N : ℕ) {K : Type} [Fintype K] (D : Type) [CommRing D] [Algebra ℂ D]
    (π : D →ₐ[ℂ] ℂ) (δ : K → D) (hπ : IsNilpotent (RingHom.ker π)) (hδ : ∀ a, π (δ a) = 0)
    (hs : ∀ s : Fin (N + 1 + 1) → K, ∏ a, δ (s a) = 0) :
    ∃ (D' : Type) (_ : CommRing D') (_ : Algebra ℂ D') (ι : D →ₐ[ℂ] D') (π' : D' →ₐ[ℂ] ℂ)
      (ν : K → D'), Function.Injective ι ∧ (∀ d, π' (ι d) = π d) ∧
      IsNilpotent (RingHom.ker π') ∧ (∀ a, π' (ν a) = 0) ∧ (∀ a b, ν a * ν b = 0) ∧
      ∀ s : Fin (N + 1) → K, ∏ a, (ι (δ (s a)) - ν (s a)) = 0 := by
  classical
  let g : (Fin (N + 1) → K) → TrivSqZeroExt D (K → D) := fun s =>
    ∏ a, ((inl (δ (s a)) : TrivSqZeroExt D (K → D)) - inr (Pi.single (s a) 1))
  let Q : Ideal (TrivSqZeroExt D (K → D)) := Ideal.span (Set.range g)
  let E : TrivSqZeroExt D (K → D) → D := fun x => ((N + 1 : ℕ) : D) * x.fst + ∑ k, x.snd k * δ k
  have hEadd : ∀ x y, E (x + y) = E x + E y := by
    intro x y
    simp only [E, fst_add, snd_add, Pi.add_apply, add_mul, Finset.sum_add_distrib]
    ring
  have hg : ∀ s c, E (c * g s) = 0 := by
    intro s c
    obtain ⟨h1, h2⟩ := prod_fst_snd δ s Finset.univ
    change (g s).fst = _ at h1
    change ∑ k, (g s).snd k * δ k = _ at h2
    have h3 : ∀ k, (c * g s).snd k * δ k
        = c.fst * ((g s).snd k * δ k) + c.snd k * (δ k * ∏ a, δ (s a)) := by
      intro k
      simp [snd_mul, h1]
      ring
    have h4 : ∀ k, δ k * ∏ a, δ (s a) = 0 := by
      intro k
      have := hs (Fin.cons k s)
      rw [Fin.prod_univ_succ] at this
      simpa using this
    simp only [E, h3, h4, mul_zero, add_zero, ← Finset.mul_sum, h2, fst_mul, h1,
      Finset.card_univ, Fintype.card_fin]
    ring
  have hQ : ∀ x ∈ Q, ∀ c, E (c * x) = 0 := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem x hx => obtain ⟨s, rfl⟩ := hx; exact hg s
    | zero => intro c; simp [E]
    | add x y _ _ hx hy => intro c; rw [mul_add, hEadd, hx, hy, add_zero]
    | smul a x _ hx => intro c; rw [smul_eq_mul, ← mul_assoc]; exact hx _
  let p : TrivSqZeroExt D (K → D) →ₐ[ℂ] ℂ := π.comp (fstHom ℂ D (K → D))
  have hp : ∀ x ∈ Q, p x = 0 := by
    have : Q ≤ RingHom.ker p := by
      rw [Ideal.span_le]
      rintro _ ⟨s, rfl⟩
      have h1 : (g s).fst = _ := (prod_fst_snd δ s Finset.univ).1
      simp [p, h1, hδ, map_prod]
    exact this
  refine ⟨TrivSqZeroExt D (K → D) ⧸ Q, inferInstance, inferInstance,
    (Ideal.Quotient.mkₐ ℂ Q).comp (inlAlgHom ℂ D (K → D)), Ideal.Quotient.liftₐ Q p hp,
    fun a => Ideal.Quotient.mk Q (inr (Pi.single a 1)), ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [injective_iff_map_eq_zero]
    intro d hd
    have hd' : (inl d : TrivSqZeroExt D (K → D)) ∈ Q := Ideal.Quotient.eq_zero_iff_mem.1 hd
    have h := hQ _ hd' 1
    simp only [E, one_mul, fst_inl, snd_inl, Pi.zero_apply, zero_mul, Finset.sum_const_zero,
      add_zero] at h
    have hu : IsUnit ((N + 1 : ℕ) : D) := by
      rw [← map_natCast (algebraMap ℂ D)]
      exact (IsUnit.mk0 _ (Nat.cast_ne_zero.2 (Nat.succ_ne_zero N))).map _
    exact hu.mul_right_eq_zero.1 h
  · intro d
    rfl
  · refine isNilpotent_of_comap (Ideal.Quotient.mk Q) Ideal.Quotient.mk_surjective _ ?_
    have := isNilpotent_comap (fstHom ℂ D (K → D)).toRingHom _ hπ (by
      intro x y hx hy
      have hx' : x.fst = 0 := hx
      have hy' : y.fst = 0 := hy
      ext1 <;> simp [snd_mul, hx', hy'])
    exact this
  · intro a
    change p (inr _) = 0
    simp [p]
  · intro a b
    rw [← map_mul, inr_mul_inr, map_zero]
  · intro s
    have : Ideal.Quotient.mk Q (g s) = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.subset_span ⟨s, rfl⟩)
    rw [← this]
    simp only [g, map_prod, map_sub]
    rfl

theorem exists_sum_sq_zero : ∀ (N : ℕ) {K : Type} [Fintype K] (D : Type) [CommRing D] [Algebra ℂ D] (π : D →ₐ[ℂ] ℂ) (δ : K → D), IsNilpotent (RingHom.ker π) → (∀ a, π (δ a) = 0) → (∀ s : Fin (N + 1) → K, ∏ a, δ (s a) = 0) → ∃ (D' : Type) (_ : CommRing D') (_ : Algebra ℂ D') (ι : D →ₐ[ℂ] D') (π' : D' →ₐ[ℂ] ℂ) (n : Fin N → K → D'), Function.Injective ι ∧ (∀ d, π' (ι d) = π d) ∧ IsNilpotent (RingHom.ker π') ∧ (∀ j a, π' (n j a) = 0) ∧ (∀ j a b, n j a * n j b = 0) ∧ ∀ a, ι (δ a) = ∑ j, n j a := by
  intro N
  induction N with
  | zero =>
    intro K _ D _ _ π δ hπ hδ hs
    refine ⟨D, inferInstance, inferInstance, AlgHom.id ℂ D, π, fun j => j.elim0,
      Function.injective_id, fun _ => rfl, hπ, fun j => j.elim0, fun j => j.elim0, ?_⟩
    intro a
    simpa using hs (fun _ => a)
  | succ N ih =>
    intro K _ D _ _ π δ hπ hδ hs
    obtain ⟨D₁, _, _, ι₁, π₁, ν, hi₁, hc₁, hn₁, hν, hνν, hs₁⟩ := step N D π δ hπ hδ hs
    obtain ⟨D₂, _, _, ι₂, π₂, n, hi₂, hc₂, hn₂, hn, hnn, hsum⟩ :=
      ih D₁ π₁ (fun a => ι₁ (δ a) - ν a) hn₁ (fun a => by simp [hc₁, hδ, hν]) hs₁
    refine ⟨D₂, inferInstance, inferInstance, ι₂.comp ι₁, π₂,
      Fin.cons (fun a => ι₂ (ν a)) n, hi₂.comp hi₁, fun d => by simp [hc₂, hc₁], hn₂, ?_, ?_, ?_⟩
    · intro j
      refine Fin.cases (fun a => ?_) (fun j a => ?_) j
      · simp [hc₂, hν]
      · simp [hn]
    · intro j
      refine Fin.cases (fun a b => ?_) (fun j a b => ?_) j
      · simp [← map_mul, hνν]
      · simp [hnn]
    · intro a
      rw [Fin.sum_univ_succ]
      simp [← hsum]

end SquareZeroSum
end GlobalTheory
