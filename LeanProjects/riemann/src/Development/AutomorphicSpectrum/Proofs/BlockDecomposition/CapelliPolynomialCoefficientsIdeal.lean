import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MonicFactorCoefficientsIntegralStatement

open Polynomial

namespace GlobalTheory.CompanionTheory.Dblock.CentreBlocks

variable {V : Type} [AddCommGroup V] [Module ℂ V]

def preserving (I : Submodule ℂ V) : Subalgebra ℂ (Module.End ℂ V) where
  carrier := {f | ∀ F ∈ I, f F ∈ I}
  mul_mem' {f g} hf hg F hF := hf _ (hg F hF)
  add_mem' {f g} hf hg F hF := I.add_mem (hf F hF) (hg F hF)
  algebraMap_mem' r F hF := by
    simp only [Set.mem_setOf_eq, Module.algebraMap_end_apply]
    exact I.smul_mem r hF

lemma pow_apply_mem (D : Module.End ℂ V) (Wn : Submodule ℂ V) (hD : ∀ F ∈ Wn, D F ∈ Wn) :
    ∀ n : ℕ, ∀ F ∈ Wn, (D ^ n) F ∈ Wn := by
  intro n
  induction n with
  | zero => intro F hF; simpa using hF
  | succ n ih =>
    intro F hF
    rw [pow_succ', Module.End.mul_apply]
    exact hD _ (ih F hF)

lemma pow_sub_pow_mem (β D : Module.End ℂ V) (Wn I : Submodule ℂ V)
    (hβ : ∀ F ∈ I, β F ∈ I) (hD : ∀ F ∈ Wn, D F ∈ Wn) (hDβ : ∀ F ∈ Wn, D F - β F ∈ I) :
    ∀ n : ℕ, ∀ F ∈ Wn, (β ^ n) F - (D ^ n) F ∈ I := by
  intro n
  induction n with
  | zero => intro F _; simp
  | succ n ih =>
    intro F hF
    have h1 := hβ _ (ih F hF)
    have h2 := hDβ _ (pow_apply_mem D Wn hD n F hF)
    have : (β ^ (n + 1)) F - (D ^ (n + 1)) F
        = β ((β ^ n) F - (D ^ n) F) - (D ((D ^ n) F) - β ((D ^ n) F)) := by
      rw [pow_succ', pow_succ', Module.End.mul_apply, Module.End.mul_apply, map_sub]
      abel
    rw [this]
    exact I.sub_mem h1 h2

lemma aeval_sub_aeval_mem (β D : Module.End ℂ V) (Wn I : Submodule ℂ V)
    (hβ : ∀ F ∈ I, β F ∈ I) (hD : ∀ F ∈ Wn, D F ∈ Wn) (hDβ : ∀ F ∈ Wn, D F - β F ∈ I)
    (p : ℂ[X]) : ∀ F ∈ Wn, (aeval β p) F - (aeval D p) F ∈ I := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    intro F hF
    have := I.add_mem (hp F hF) (hq F hF)
    simp only [map_add, LinearMap.add_apply]
    convert this using 1
    abel
  | monomial n c =>
    intro F hF
    simp only [aeval_monomial, Module.End.mul_apply, Module.algebraMap_end_apply]
    rw [← smul_sub]
    exact I.smul_mem c (pow_sub_pow_mem β D Wn I hβ hD hDβ n F hF)

lemma isIntegral_eval {A : Type} [CommRing A] [Algebra ℂ A] (P : A[X])
    (h : ∀ k, IsIntegral ℂ (P.coeff k)) (x : A) (hx : IsIntegral ℂ x) :
    IsIntegral ℂ (P.eval x) := by
  rw [Polynomial.eval_eq_sum_range]
  exact (integralClosure ℂ A).sum_mem fun i _ =>
    (integralClosure ℂ A).mul_mem (h i) ((integralClosure ℂ A).pow_mem hx _)

end GlobalTheory.CompanionTheory.Dblock.CentreBlocks

namespace GlobalTheory.CompanionTheory.Dblock.CentreBlocks

noncomputable def sumPoly {A : Type} [CommRing A] (c : ℕ → A) (n : ℕ) : A[X] :=
  ∑ k ∈ Finset.range (n + 1), C (c k) * X ^ k

lemma sumPoly_eval {A : Type} [CommRing A] (c : ℕ → A) (n : ℕ) (x : A) :
    (sumPoly c n).eval x = ∑ k ∈ Finset.range (n + 1), c k * x ^ k := by
  simp [sumPoly, eval_finset_sum]

lemma sumPoly_coeff {A : Type} [CommRing A] (c : ℕ → A) (n m : ℕ) :
    (sumPoly c n).coeff m = if m < n + 1 then c m else 0 := by
  simp [sumPoly, finset_sum_coeff, coeff_C_mul_X_pow]

lemma sumPoly_monic {A : Type} [CommRing A] (c : ℕ → A) (n : ℕ) (h : c n = 1) :
    (sumPoly c n).Monic := by
  apply Polynomial.monic_of_natDegree_le_of_coeff_eq_one n
  · apply Polynomial.natDegree_sum_le_of_forall_le
    intro k hk
    exact (natDegree_C_mul_X_pow_le _ _).trans (Nat.lt_succ_iff.mp (Finset.mem_range.mp hk))
  · rw [sumPoly_coeff]; simp [h]

theorem monic_relations_to_blocks : ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (D R S : ℂ → Module.End ℂ V) (Wn I : Submodule ℂ V) (W₀ : Set V) (c₁ c₂ : ℂ) (n₁ n₂ : ℕ) (a b : ℕ → Module.End ℂ V), (∀ u v, Commute (R u) (R v)) → (∀ u v, Commute (R u) (S v)) → (∀ u v, Commute (S u) (S v)) → (∀ u, ∀ F ∈ Wn, D u F ∈ Wn) → (∀ u, ∀ F ∈ I, R u F ∈ I) → (∀ u, ∀ F ∈ I, S u F ∈ I) → (∀ u, ∀ F ∈ Wn, D u F - S (u + c₂) (R (u + c₁) F) ∈ I) → a n₁ = 1 → (∀ k, a k ∈ Submodule.span ℂ (Set.range R)) → (∀ u : ℂ, R u = ∑ k ∈ Finset.range (n₁ + 1), u ^ k • a k) → b n₂ = 1 → (∀ k, b k ∈ Submodule.span ℂ (Set.range S)) → (∀ u : ℂ, S u = ∑ k ∈ Finset.range (n₂ + 1), u ^ k • b k) → W₀ ⊆ Wn → (∀ u, ∃ p : Polynomial ℂ, p.Monic ∧ ∀ F ∈ W₀, Polynomial.aeval (D u) p F = 0) → (∀ u, ∃ q : Polynomial ℂ, q.Monic ∧ ∀ F ∈ W₀, Polynomial.aeval (R u) q F ∈ I) ∧ ∀ u, ∃ q : Polynomial ℂ, q.Monic ∧ ∀ F ∈ W₀, Polynomial.aeval (S u) q F ∈ I := by
  intro V _ _ D R S Wn I W₀ c₁ c₂ n₁ n₂ a b hRR hRS hSS hD hRI hSI hDβ ha1 haspan hRform hb1
    hbspan hSform hW0 hp
  let s : Set (Module.End ℂ V) := Set.range R ∪ Set.range S
  have hcomm : ∀ x ∈ s, ∀ y ∈ s, x * y = y * x := by
    rintro x (⟨u, rfl⟩ | ⟨u, rfl⟩) y (⟨v, rfl⟩ | ⟨v, rfl⟩)
    · exact (hRR u v).eq
    · exact (hRS u v).eq
    · exact (hRS v u).eq.symm
    · exact (hSS u v).eq
  letI : CommRing (Algebra.adjoin ℂ s) := Algebra.adjoinCommRingOfComm ℂ hcomm
  have hpres : Algebra.adjoin ℂ s ≤ preserving I := by
    rw [Algebra.adjoin_le_iff]
    rintro x (⟨u, rfl⟩ | ⟨u, rfl⟩)
    · exact hRI u
    · exact hSI u
  let Y : Ideal (Algebra.adjoin ℂ s) :=
    { carrier := {x | ∀ F ∈ W₀, (x : Module.End ℂ V) F ∈ I}
      add_mem' := fun {x y} hx hy F hF => by
        simpa using I.add_mem (hx F hF) (hy F hF)
      zero_mem' := fun F _ => by simp
      smul_mem' := fun c x hx F hF => by
        show ((c * x : Algebra.adjoin ℂ s) : Module.End ℂ V) F ∈ I
        rw [Subalgebra.coe_mul, Module.End.mul_apply]
        exact hpres c.2 _ (hx F hF) }
  let π := Ideal.Quotient.mkₐ ℂ Y
  have hRmem : ∀ u, R u ∈ Algebra.adjoin ℂ s := fun u => Algebra.subset_adjoin (Or.inl ⟨u, rfl⟩)
  have hSmem : ∀ u, S u ∈ Algebra.adjoin ℂ s := fun u => Algebra.subset_adjoin (Or.inr ⟨u, rfl⟩)
  have hamem : ∀ k, a k ∈ Algebra.adjoin ℂ s := fun k =>
    (Submodule.span_le (p := Subalgebra.toSubmodule (Algebra.adjoin ℂ s))).mpr
      (by rintro x ⟨u, rfl⟩; exact hRmem u) (haspan k)
  have hbmem : ∀ k, b k ∈ Algebra.adjoin ℂ s := fun k =>
    (Submodule.span_le (p := Subalgebra.toSubmodule (Algebra.adjoin ℂ s))).mpr
      (by rintro x ⟨u, rfl⟩; exact hSmem u) (hbspan k)
  let P : (Algebra.adjoin ℂ s ⧸ Y)[X] := sumPoly (fun k => π ⟨a k, hamem k⟩) n₁
  let Q : (Algebra.adjoin ℂ s ⧸ Y)[X] := sumPoly (fun k => π ⟨b k, hbmem k⟩) n₂
  have hPm : P.Monic := sumPoly_monic _ _ (by
    have : (⟨a n₁, hamem n₁⟩ : Algebra.adjoin ℂ s) = 1 := Subtype.ext ha1
    simp only [this, map_one])
  have hQm : Q.Monic := sumPoly_monic _ _ (by
    have : (⟨b n₂, hbmem n₂⟩ : Algebra.adjoin ℂ s) = 1 := Subtype.ext hb1
    simp only [this, map_one])
  have hPev : ∀ t : ℂ, P.eval (algebraMap ℂ _ t) = π ⟨R t, hRmem t⟩ := by
    intro t
    have : (⟨R t, hRmem t⟩ : Algebra.adjoin ℂ s)
        = ∑ k ∈ Finset.range (n₁ + 1), t ^ k • (⟨a k, hamem k⟩ : Algebra.adjoin ℂ s) := by
      apply Subtype.ext; simp [hRform t]
    rw [this, map_sum, sumPoly_eval]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_smul, Algebra.smul_def, map_pow, mul_comm]
  have hQev : ∀ t : ℂ, Q.eval (algebraMap ℂ _ t) = π ⟨S t, hSmem t⟩ := by
    intro t
    have : (⟨S t, hSmem t⟩ : Algebra.adjoin ℂ s)
        = ∑ k ∈ Finset.range (n₂ + 1), t ^ k • (⟨b k, hbmem k⟩ : Algebra.adjoin ℂ s) := by
      apply Subtype.ext; simp [hSform t]
    rw [this, map_sum, sumPoly_eval]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_smul, Algebra.smul_def, map_pow, mul_comm]
  have hβ : ∀ u : ℂ, IsIntegral ℂ (P.eval (algebraMap ℂ _ (u + c₁)) *
      Q.eval (algebraMap ℂ _ (u + c₂))) := by
    intro u
    rw [hPev, hQev, ← map_mul]
    obtain ⟨p, hpm, hp0⟩ := hp u
    refine ⟨p, hpm, ?_⟩
    rw [← Polynomial.aeval_def, Polynomial.aeval_algHom_apply, Ideal.Quotient.mkₐ_eq_mk,
      Ideal.Quotient.eq_zero_iff_mem]
    intro F hF
    rw [Polynomial.aeval_subalgebra_coe]
    have key := aeval_sub_aeval_mem (R (u + c₁) * S (u + c₂)) (D u) Wn I
      (hpres (mul_mem (hRmem _) (hSmem _))) (hD u)
      (fun F hF => by rw [(hRS _ _).eq]; exact hDβ u F hF) p F (hW0 hF)
    rw [hp0 F hF, sub_zero] at key
    exact key
  have hcoef := GlobalTheory.T.monic_factor_coefficients_integral (Algebra.adjoin ℂ s ⧸ Y) P Q c₁ c₂ hPm hQm hβ
  refine ⟨fun u => ?_, fun u => ?_⟩
  · have hint : IsIntegral ℂ (π ⟨R u, hRmem u⟩) := by
      rw [← hPev]
      exact isIntegral_eval P (fun k => (hcoef k).1) _ isIntegral_algebraMap
    obtain ⟨q, hqm, hq0⟩ := hint
    refine ⟨q, hqm, fun F hF => ?_⟩
    rw [← Polynomial.aeval_def, Polynomial.aeval_algHom_apply, Ideal.Quotient.mkₐ_eq_mk,
      Ideal.Quotient.eq_zero_iff_mem] at hq0
    have := hq0 F hF
    rwa [Polynomial.aeval_subalgebra_coe] at this
  · have hint : IsIntegral ℂ (π ⟨S u, hSmem u⟩) := by
      rw [← hQev]
      exact isIntegral_eval Q (fun k => (hcoef k).2) _ isIntegral_algebraMap
    obtain ⟨q, hqm, hq0⟩ := hint
    refine ⟨q, hqm, fun F hF => ?_⟩
    rw [← Polynomial.aeval_def, Polynomial.aeval_algHom_apply, Ideal.Quotient.mkₐ_eq_mk,
      Ideal.Quotient.eq_zero_iff_mem] at hq0
    have := hq0 F hF
    rwa [Polynomial.aeval_subalgebra_coe] at this

end GlobalTheory.CompanionTheory.Dblock.CentreBlocks
