import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HermSysHypOneLeLambdaZero
import ReciprocityTheory.SemistableReduction.TorusL2CauchyInequality
open NumberField MvPolynomial ReciprocityTheory.MultiplicativeHeights ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.ChowHt GlobalTheory.Adelic GlobalTheory.HermTools GlobalTheory.HilbertSamuel GlobalTheory.HSChoice GlobalTheory.HSShort

namespace GlobalTheory.HSShort

theorem linearIndependent_of_symbol_det_ne_zero :
    ∀ (E A' : Type) [Field E] [AddCommGroup A'] [Module E A'] (r d : ℕ) (I : Fin r → Type) [∀ a, Fintype (I a)] [∀ a, DecidableEq (I a)] (U : ℕ → Submodule E A') (sym : ∀ a : Fin r, U a →ₗ[E] (I a → E)), (∀ a < r, U (a + 1) ≤ U a) → (∀ (a : Fin r) (x : U a), sym a x = 0 ↔ x.1 ∈ U (a + 1)) → ∀ (ix : (Σ a, I a) ↪ Fin d) (J : Finset (Fin d)) (v : Fin d → A') (hv : ∀ q, v (ix q) ∈ U q.1), (∀ k ∈ J, k ∉ Set.range ix ∧ v k ∈ U r) → (∀ a, (Matrix.of fun i i' : I a => sym a ⟨v (ix ⟨a, i'⟩), hv ⟨a, i'⟩⟩ i).det ≠ 0) → LinearIndependent E (fun k : J => v k) → LinearIndependent E fun k : {k // k ∈ Set.range ix ∨ k ∈ J} => v k := by
  classical
  intro E A' _ _ _ r d I _ _ U sym hmono hker ix J v hv hJ hdet hJli
  have hle : ∀ b c : ℕ, b ≤ c → c ≤ r → U c ≤ U b := by
    intro b c hbc hcr
    induction c, hbc using Nat.le_induction with
    | base => exact le_rfl
    | succ c hbc ih => exact (hmono c (by omega)).trans (ih (by omega))
  let h : (Σ a, I a) ⊕ J → Fin d := Sum.elim ix (fun k => k.1)
  have hinj : Function.Injective h := by
    rintro (q|k) (q'|k') heq
    · exact congrArg Sum.inl (ix.injective heq)
    · exact ((hJ _ k'.2).1 ⟨q, heq⟩).elim
    · exact ((hJ _ k.2).1 ⟨q', heq.symm⟩).elim
    · exact congrArg Sum.inr (Subtype.ext heq)
  let e : (Σ a, I a) ⊕ J → {k // k ∈ Set.range ix ∨ k ∈ J} := fun x =>
    ⟨h x, by rcases x with q | k; exacts [Or.inl ⟨q, rfl⟩, Or.inr k.2]⟩
  have hb : Function.Bijective e := by
    refine ⟨fun x y hxy => hinj (congrArg Subtype.val hxy), ?_⟩
    rintro ⟨k, hk | hk⟩
    · obtain ⟨q, rfl⟩ := hk
      exact ⟨Sum.inl q, rfl⟩
    · exact ⟨Sum.inr ⟨k, hk⟩, rfl⟩
  have key : LinearIndependent E (fun x : (Σ a, I a) ⊕ J => v (h x)) := by
    rw [Fintype.linearIndependent_iff]
    intro g hg
    have hg' : (∑ q, g (Sum.inl q) • v (ix q)) + ∑ k : J, g (Sum.inr k) • v k = 0 := by
      rw [Fintype.sum_sum_type] at hg; exact hg
    have hA : ∀ n, ∀ a : Fin r, (a : ℕ) = n → ∀ i, g (Sum.inl ⟨a, i⟩) = 0 := by
      intro n
      induction n using Nat.strong_induction_on with
      | _ n ih =>
      intro a ha i
      subst ha
      obtain ⟨G, hG⟩ := LinearMap.exists_extend (sym a)
      have hGv : ∀ x (hx : x ∈ U a), G x = sym a ⟨x, hx⟩ := fun x hx =>
        LinearMap.congr_fun hG ⟨x, hx⟩
      have hker' : ∀ x ∈ U ((a : ℕ) + 1), G x = 0 := fun x hx => by
        rw [hGv x (hmono a a.isLt hx)]
        exact (hker a ⟨x, _⟩).mpr hx
      have hJ0 : ∑ k : J, g (Sum.inr k) • G (v k) = 0 :=
        Finset.sum_eq_zero fun k _ => by
          rw [hker' _ (hle ((a : ℕ) + 1) r (by have := a.isLt; omega) le_rfl (hJ k.1 k.2).2), smul_zero]
      have hS : ∑ q : (Σ b, I b), g (Sum.inl q) • G (v (ix q))
          = ∑ i : I a, g (Sum.inl ⟨a, i⟩) • sym a ⟨v (ix ⟨a, i⟩), hv ⟨a, i⟩⟩ := by
        rw [Fintype.sum_sigma, Finset.sum_eq_single a]
        · exact Finset.sum_congr rfl fun i _ => by rw [hGv]
        · intro b _ hba
          apply Finset.sum_eq_zero
          intro i _
          rcases lt_or_gt_of_ne hba with hlt | hlt
          · rw [ih b (Fin.lt_iff_val_lt_val.mp hlt) b rfl i, zero_smul]
          · have h1 := Fin.lt_iff_val_lt_val.mp hlt
            have h2 := b.isLt
            rw [hker' _ (hle ((a : ℕ) + 1) (b : ℕ) (by omega) (by omega) (hv ⟨b, i⟩)), smul_zero]
        · intro hn; exact absurd (Finset.mem_univ a) hn
      have hGg := congrArg G hg'
      simp only [map_add, map_sum, map_smul, map_zero] at hGg
      rw [hS, hJ0, add_zero] at hGg
      have hM : Matrix.mulVec (Matrix.of fun i i' : I a => sym a ⟨v (ix ⟨a, i'⟩), hv ⟨a, i'⟩⟩ i)
          (fun i' => g (Sum.inl ⟨a, i'⟩)) = 0 := by
        funext j
        have hj := congrFun hGg j
        simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at hj
        simp only [Matrix.mulVec, dotProduct, Matrix.of_apply, Pi.zero_apply]
        rw [← hj]; exact Finset.sum_congr rfl fun _ _ => mul_comm _ _
      exact congrFun (Matrix.eq_zero_of_mulVec_eq_zero (hdet a) hM) i
    have hJs : ∑ k : J, g (Sum.inr k) • v k = 0 := by
      have h0 : ∑ q : (Σ a, I a), g (Sum.inl q) • v (ix q) = 0 :=
        Finset.sum_eq_zero fun ⟨b, i⟩ _ => by rw [hA _ b rfl i, zero_smul]
      rw [h0, zero_add] at hg'; exact hg'
    rintro (⟨b, i⟩ | k)
    · exact hA _ b rfl i
    · exact Fintype.linearIndependent_iff.mp hJli (fun k => g (Sum.inr k)) hJs k
  refine (linearIndependent_equiv (Equiv.ofBijective e hb)).mp ?_
  exact key

end GlobalTheory.HSShort
