import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.DeltaStructureOfWittLengthTwoSection
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BasisOfCongrBasisModNilpotentIdealStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TriangularSystemMonomialProductsBasisStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

namespace GlobalTheory.EnvLevel

theorem mem_smul_top_of_mem_map_C {R : Type} [CommRing R] (I : Ideal R) (p : MvPolynomial ℕ R)
    (hp : p ∈ Ideal.map (MvPolynomial.C : R →+* MvPolynomial ℕ R) I) :
    p ∈ I • (⊤ : Submodule R (MvPolynomial ℕ R)) := by
  rw [MvPolynomial.mem_map_C_iff] at hp
  rw [MvPolynomial.as_sum p]
  refine Submodule.sum_mem _ fun s _ => ?_
  have : MvPolynomial.monomial s (p.coeff s) = p.coeff s • MvPolynomial.monomial s (1 : R) := by
    rw [MvPolynomial.smul_monomial, smul_eq_mul, mul_one]
  rw [this]
  exact Submodule.smul_mem_smul (hp s) Submodule.mem_top

theorem tri_map {A R : Type} [CommRing A] [CommRing R] (f : A →+* R) (l i : ℕ) (v : Aˣ)
    (a b : MvPolynomial ℕ A)
    (ha : a ∈ MvPolynomial.supported A (Set.Iio i)) (hb : b ∈ MvPolynomial.supported A (Set.Iio i)) :
    ∃ (v' : Rˣ) (a' b' : MvPolynomial ℕ R), a' ∈ MvPolynomial.supported R (Set.Iio i) ∧
      b' ∈ MvPolynomial.supported R (Set.Iio i) ∧
      MvPolynomial.map f (MvPolynomial.C (v : A) * MvPolynomial.X i ^ l + a * MvPolynomial.X i + b) =
        MvPolynomial.C (v' : R) * MvPolynomial.X i ^ l + a' * MvPolynomial.X i + b' := by
  refine ⟨Units.map f.toMonoidHom v, MvPolynomial.map f a, MvPolynomial.map f b, ?_, ?_, ?_⟩
  · rw [MvPolynomial.mem_supported] at ha ⊢
    exact (Finset.coe_subset.mpr (MvPolynomial.vars_map a f)).trans ha
  · rw [MvPolynomial.mem_supported] at hb ⊢
    exact (Finset.coe_subset.mpr (MvPolynomial.vars_map b f)).trans hb
  · simp [map_add, map_mul, map_pow, MvPolynomial.map_C, MvPolynomial.map_X]

end GlobalTheory.EnvLevel

theorem GlobalTheory.digitMonomials_basis_mod_pow : ∀ (l : ℕ) [Fact l.Prime] (A : Type) [CommRing A] (J : Ideal A) (r : ℕ → MvPolynomial ℕ A), (∀ i, ∃ (v : Aˣ) (a b : MvPolynomial ℕ A), a ∈ MvPolynomial.supported A (Set.Iio i) ∧ b ∈ MvPolynomial.supported A (Set.Iio i) ∧ r i - (MvPolynomial.C (v : A) * MvPolynomial.X i ^ l + a * MvPolynomial.X i + b) ∈ J.map (MvPolynomial.C : A →+* MvPolynomial ℕ A)) → ∀ n : ℕ, (∀ x : MvPolynomial ℕ A, ∃ c : Digits l →₀ A, x - c.sum (fun α a => MvPolynomial.monomial α.1 a) ∈ Ideal.span (Set.range r) ⊔ (J ^ n).map (MvPolynomial.C : A →+* MvPolynomial ℕ A)) ∧ ∀ c : Digits l →₀ A, c.sum (fun α a => MvPolynomial.monomial α.1 a) ∈ Ideal.span (Set.range r) ⊔ (J ^ n).map (MvPolynomial.C : A →+* MvPolynomial ℕ A) → ∀ α, c α ∈ J ^ n := by
  intro l _ A _ J r hr n
  classical
  let π : MvPolynomial ℕ A →+* MvPolynomial ℕ (A ⧸ J ^ n) := MvPolynomial.map (Ideal.Quotient.mk (J ^ n))
  have hπs : Function.Surjective π := MvPolynomial.map_surjective _ Ideal.Quotient.mk_surjective
  have hker : RingHom.ker π = (J ^ n).map (MvPolynomial.C : A →+* MvPolynomial ℕ A) := by
    simp only [π]; rw [MvPolynomial.ker_map, Ideal.mk_ker]
  let I : Ideal (A ⧸ J ^ n) := J.map (Ideal.Quotient.mk (J ^ n))
  have hIn : I ^ n = ⊥ := by
    simp only [I]; rw [← Ideal.map_pow, Ideal.map_eq_bot_iff_le_ker, Ideal.mk_ker]
  choose v a b ha hb hrab using hr
  let t : ℕ → MvPolynomial ℕ (A ⧸ J ^ n) := fun i =>
    π (MvPolynomial.C (v i : A) * MvPolynomial.X i ^ l + a i * MvPolynomial.X i + b i)
  have ht := fun i => GlobalTheory.EnvLevel.tri_map (Ideal.Quotient.mk (J ^ n)) l i (v i) (a i) (b i) (ha i) (hb i)
  obtain ⟨htli, htsp⟩ := GlobalTheory.T.triangular_system_monomial_products_basis l (A ⧸ J ^ n) t ht
  let B : Digits l × (ℕ →₀ ℕ) → MvPolynomial ℕ (A ⧸ J ^ n) := fun x =>
    MvPolynomial.monomial x.1.1 (1 : A ⧸ J ^ n) * x.2.prod fun i m => π (r i) ^ m
  have hK : ∀ i, π (r i) - t i ∈ Ideal.map (MvPolynomial.C : (A ⧸ J ^ n) →+* MvPolynomial ℕ (A ⧸ J ^ n)) I := by
    intro i
    have h1 : π (r i) - t i = π (r i - (MvPolynomial.C (v i : A) * MvPolynomial.X i ^ l + a i * MvPolynomial.X i + b i)) := by
      simp only [t, map_sub]
    have h2 : Ideal.map (MvPolynomial.C : (A ⧸ J ^ n) →+* MvPolynomial ℕ (A ⧸ J ^ n)) I =
        Ideal.map π (J.map (MvPolynomial.C : A →+* MvPolynomial ℕ A)) := by
      simp only [I, π]
      rw [Ideal.map_map, Ideal.map_map, MvPolynomial.map_comp_C]
    rw [h1, h2]
    exact Ideal.mem_map_of_mem _ (hrab i)
  have hBK : ∀ x, B x - (MvPolynomial.monomial x.1.1 (1 : A ⧸ J ^ n) * x.2.prod fun i m => t i ^ m) ∈
      I • (⊤ : Submodule (A ⧸ J ^ n) (MvPolynomial ℕ (A ⧸ J ^ n))) := by
    intro x
    apply GlobalTheory.EnvLevel.mem_smul_top_of_mem_map_C
    rw [← Ideal.Quotient.eq]
    simp only [B, map_mul, Finsupp.prod, map_prod, map_pow]
    congr 1
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [Ideal.Quotient.eq.mpr (hK i)]
  obtain ⟨hBli, hBsp⟩ := GlobalTheory.T.basis_of_congr_basis_mod_nilpotent_ideal (A ⧸ J ^ n) (MvPolynomial ℕ (A ⧸ J ^ n)) (Digits l × (ℕ →₀ ℕ))
    _ B I n hIn htli htsp hBK
  have hBmem : ∀ k : Digits l × (ℕ →₀ ℕ), k.2 ≠ 0 → B k ∈ Ideal.span (Set.range (⇑π ∘ r)) := by
    intro k hk
    obtain ⟨i, hi⟩ := Finsupp.support_nonempty_iff.mpr hk
    apply Ideal.mul_mem_left
    have hd : π (r i) ^ k.2 i ∣ k.2.prod fun i m => π (r i) ^ m :=
      Finset.dvd_prod_of_mem (fun i => π (r i) ^ k.2 i) hi
    obtain ⟨d, hd⟩ := hd
    rw [hd]
    apply Ideal.mul_mem_right
    exact Ideal.pow_mem_of_mem _ (Ideal.subset_span (Set.mem_range_self (f := ⇑π ∘ r) i)) _
      (Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp hi))
  let S : Submodule (A ⧸ J ^ n) (MvPolynomial ℕ (A ⧸ J ^ n)) :=
    Submodule.span (A ⧸ J ^ n) (B '' {x | x.2 ≠ 0})
  have hmulS : ∀ i (p : MvPolynomial ℕ (A ⧸ J ^ n)), p * π (r i) ∈ S := by
    intro i p
    have hp : p ∈ Submodule.span (A ⧸ J ^ n) (Set.range B) := by rw [hBsp]; exact Submodule.mem_top
    induction hp using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨k, rfl⟩ := hx
      have : B k * π (r i) = B (k.1, k.2 + Finsupp.single i 1) := by
        simp only [B]
        rw [Finsupp.prod_add_index' (fun _ => pow_zero _) (fun _ _ _ => pow_add _ _ _),
          Finsupp.prod_single_index (by simp)]
        simp only [pow_one, mul_assoc]
      rw [this]
      refine Submodule.subset_span ⟨(k.1, k.2 + Finsupp.single i 1), ?_, rfl⟩
      intro h
      have := DFunLike.congr_fun h i
      simp at this
    | zero => simp
    | add x y _ _ hx hy => rw [add_mul]; exact S.add_mem hx hy
    | smul c x _ hx => rw [smul_mul_assoc]; exact S.smul_mem c hx
  have hspanS : ∀ x ∈ Ideal.span (Set.range (⇑π ∘ r)), ∀ p, p * x ∈ S := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem y hy => obtain ⟨i, rfl⟩ := hy; exact fun p => hmulS i p
    | zero => intro p; simp
    | add y z _ _ hy hz => intro p; rw [mul_add]; exact S.add_mem (hy p) (hz p)
    | smul c y _ hy => intro p; rw [smul_eq_mul, ← mul_assoc]; exact hy (p * c)
  refine ⟨?_, ?_⟩
  · intro x
    have hx : π x ∈ Submodule.span (A ⧸ J ^ n) (Set.range B) := by rw [hBsp]; exact Submodule.mem_top
    obtain ⟨f, hf⟩ := Finsupp.mem_span_range_iff_exists_finsupp.mp hx
    let f0 := f.filter fun k => k.2 = 0
    let f1 := f.filter fun k => ¬ k.2 = 0
    let g : Digits l →₀ (A ⧸ J ^ n) := f0.mapDomain Prod.fst
    have hsplit : π x = (f0.sum fun k a => a • B k) + (f1.sum fun k a => a • B k) := by
      rw [← hf, ← Finsupp.sum_add_index' (h := fun k a => a • B k) (fun _ => zero_smul _ _)
        (fun _ _ _ => add_smul _ _ _)]
      simp only [f0, f1]
      rw [Finsupp.filter_add_filter_not]
    have h0sum : (f0.sum fun k a => a • B k) = g.sum fun α a => MvPolynomial.monomial α.1 a := by
      simp only [g]
      rw [Finsupp.sum_mapDomain_index (h := fun (α : Digits l) (a : A ⧸ J ^ n) => MvPolynomial.monomial α.1 a)
        (fun (α : Digits l) => (MvPolynomial.monomial (R := A ⧸ J ^ n) α.1).map_zero)
        (fun (α : Digits l) _ _ => (MvPolynomial.monomial (R := A ⧸ J ^ n) α.1).map_add _ _)]
      refine Finsupp.sum_congr fun k hk => ?_
      have hk2 : k.2 = 0 := by
        simp only [f0] at hk
        rw [Finsupp.support_filter, Finset.mem_filter] at hk; exact hk.2
      simp only [B, hk2, Finsupp.prod_zero_index, mul_one, MvPolynomial.smul_monomial, smul_eq_mul]
    have h1mem : (f1.sum fun k a => a • B k) ∈ Ideal.span (Set.range (⇑π ∘ r)) := by
      unfold Finsupp.sum
      refine Ideal.sum_mem _ fun k hk => ?_
      have hk2 : k.2 ≠ 0 := by
        simp only [f1] at hk
        rw [Finsupp.support_filter, Finset.mem_filter] at hk; exact hk.2
      show f1 k • B k ∈ _
      rw [MvPolynomial.smul_eq_C_mul]
      exact Ideal.mul_mem_left _ _ (hBmem k hk2)
    let sec : (A ⧸ J ^ n) → A := fun y =>
      if y = 0 then 0 else Function.surjInv (Ideal.Quotient.mk_surjective (I := J ^ n)) y
    have hsec0 : sec 0 = 0 := by simp [sec]
    have hsec : ∀ y, Ideal.Quotient.mk (J ^ n) (sec y) = y := by
      intro y
      by_cases h : y = 0
      · simp [sec, h]
      · simp only [sec, h, if_false]; exact Function.surjInv_eq _ y
    refine ⟨g.mapRange sec hsec0, ?_⟩
    have hmap : π ((g.mapRange sec hsec0).sum fun α a => MvPolynomial.monomial α.1 a) =
        g.sum fun α a => MvPolynomial.monomial α.1 a := by
      rw [map_finsuppSum, Finsupp.sum_mapRange_index (h := fun (α : Digits l) (a : A) => π (MvPolynomial.monomial α.1 a))
        (fun _ => by simp)]
      simp only [π, MvPolynomial.map_monomial, hsec]
    have hmem : x - ((g.mapRange sec hsec0).sum fun α a => MvPolynomial.monomial α.1 a) ∈
        Ideal.comap π (Ideal.map π (Ideal.span (Set.range r))) := by
      rw [Ideal.mem_comap, Ideal.map_span, ← Set.range_comp, map_sub, hmap, hsplit, ← h0sum,
        add_sub_cancel_left]
      exact h1mem
    rwa [Ideal.comap_map_of_surjective _ hπs, ← RingHom.ker_eq_comap_bot, hker] at hmem
  · intro c hc α
    have h1 : π (c.sum fun α a => MvPolynomial.monomial α.1 a) ∈ Ideal.span (Set.range (⇑π ∘ r)) := by
      have := Ideal.mem_map_of_mem π hc
      rwa [Ideal.map_sup, ← hker, (Ideal.map_eq_bot_iff_le_ker π).mpr le_rfl, sup_bot_eq, Ideal.map_span,
        ← Set.range_comp] at this
    have h2 : π (c.sum fun α a => MvPolynomial.monomial α.1 a) ∈ S := by
      simpa using hspanS _ h1 1
    have hinj : Function.Injective (fun α : Digits l => (α, (0 : ℕ →₀ ℕ))) :=
      fun _ _ h => congrArg Prod.fst h
    let g' : Digits l × (ℕ →₀ ℕ) →₀ (A ⧸ J ^ n) :=
      Finsupp.mapDomain (fun α => (α, (0 : ℕ →₀ ℕ))) (c.mapRange (Ideal.Quotient.mk (J ^ n)) (map_zero _))
    have hg' : Finsupp.linearCombination (A ⧸ J ^ n) B g' = π (c.sum fun α a => MvPolynomial.monomial α.1 a) := by
      rw [Finsupp.linearCombination_mapDomain, Finsupp.linearCombination_apply,
        Finsupp.sum_mapRange_index (h := fun i a => a • (B ∘ fun α => (α, (0 : ℕ →₀ ℕ))) i)
          (fun _ => zero_smul _ _), map_finsuppSum]
      refine Finsupp.sum_congr fun β _ => ?_
      simp [B, π, MvPolynomial.smul_monomial]
    obtain ⟨l', hl', hl'eq⟩ := (Finsupp.mem_span_image_iff_linearCombination (A ⧸ J ^ n)).mp h2
    have hl : l' = g' := hBli (hl'eq.trans hg'.symm)
    have h3 : g' (α, 0) = 0 := by
      rw [← hl]; exact (Finsupp.mem_supported' (A ⧸ J ^ n) l').mp hl' _ (by simp)
    have h4 : g' (α, 0) = Ideal.Quotient.mk (J ^ n) (c α) :=
      Finsupp.mapDomain_apply hinj (c.mapRange (Ideal.Quotient.mk (J ^ n)) (map_zero _)) α
    rw [h4] at h3
    exact Ideal.Quotient.eq_zero_iff_mem.mp h3
