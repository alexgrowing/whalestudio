import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.DiscreteSeriesCharacter

open Matrix Polynomial GlobalTheory.Orb GlobalTheory.HCChar
open Formalism.REAL (UJ)

namespace GlobalTheory.HCChar

theorem finite_comm_diagonal {n : ℕ} {z : Fin n → ℂ} (hz : Function.Injective z) :
    {M : Matrix (Fin n) (Fin n) ℂ | M * diagonal z = diagonal z * M ∧ M.charpoly = (diagonal z).charpoly}.Finite := by
  refine (Set.finite_range fun f : Fin n → Fin n => diagonal (z ∘ f)).subset ?_
  rintro M ⟨h1, h2⟩
  have hd : M = diagonal fun a => M a a := by
    ext a b
    by_cases hab : a = b
    · simp [hab]
    · have := congrFun (congrFun h1 a) b
      rw [mul_diagonal, diagonal_mul, mul_comm, mul_eq_mul_right_iff] at this
      rw [diagonal_apply_ne _ hab, this.resolve_left fun e => hab (hz e).symm]
  have hr : ∀ a, ∃ b, z b = M a a := fun a => by
    have h3 := congrArg (eval (M a a)) h2
    rw [hd, charpoly_diagonal, charpoly_diagonal, eval_prod, eval_prod,
      Finset.prod_eq_zero (i := a) (by simp) (by simp), eq_comm, Finset.prod_eq_zero_iff] at h3
    obtain ⟨b, -, hb⟩ := h3
    exact ⟨b, by simpa [sub_eq_zero, eq_comm] using hb⟩
  choose f hf using hr
  exact ⟨f, by rw [hd]; exact congrArg diagonal (funext hf)⟩

theorem finite_comm_charpoly {n : ℕ} {S : Matrix (Fin n) (Fin n) ℂ} (hS : IsRegSS S) :
    {M : Matrix (Fin n) (Fin n) ℂ | M * S = S * M ∧ M.charpoly = S.charpoly}.Finite := by
  obtain ⟨z, hz⟩ : ∃ z : Fin n → ℂ, S.charpoly = ∏ a, (X - C (z a)) := by
    have hsp := IsAlgClosed.splits S.charpoly
    have hc : S.charpoly.roots.toList.length = n := by
      rw [Multiset.length_toList, ← hsp.natDegree_eq_card_roots, charpoly_natDegree_eq_dim, Fintype.card_fin]
    have h1 := hsp.eq_prod_roots_of_monic S.charpoly_monic
    rw [← Multiset.coe_toList S.charpoly.roots] at h1
    generalize S.charpoly.roots.toList = l at hc h1
    subst hc
    refine ⟨l.get, h1.trans ?_⟩
    rw [Multiset.map_coe, Multiset.prod_coe, ← List.prod_ofFn]
    congr 1
    conv_lhs => rw [← List.ofFn_get l, List.map_ofFn]
    rfl
  have hinj : Function.Injective z := by
    rwa [IsRegSS, hz, separable_prod_X_sub_C_iff] at hS
  have he : (diagonal z).charpoly = S.charpoly := by rw [hz, charpoly_diagonal]
  obtain ⟨x, hx⟩ := hS.exists_conj he
  have hD : diagonal z = x * S * (x⁻¹ : GL (Fin n) ℂ) := by rw [← hx, Units.mul_inv_cancel_right]
  refine Set.Finite.of_finite_image (f := fun M => (x : Matrix (Fin n) (Fin n) ℂ) * M * (x⁻¹ : GL (Fin n) ℂ))
    ((finite_comm_diagonal hinj).subset ?_) ?_
  · rintro _ ⟨M, ⟨h1, h2⟩, rfl⟩
    refine ⟨?_, ?_⟩
    · rw [hD]
      simp only [mul_assoc, Units.inv_mul_cancel_left]
      rw [← mul_assoc M, h1, mul_assoc]
    · rw [he, ← h2, Matrix.coe_units_inv, Matrix.charpoly_units_conj]
  · intro M _ N _ h
    simpa only [Units.mul_left_inj, Units.mul_right_inj] using h

theorem weylOrder_ne_zero : ∀ (n : ℕ) (ε : Fin n → Bool) (T : Subgroup (UJ ε)), IsCartanSub T → weylOrder T ≠ 0 := by
  rintro n ε T ⟨s, hs, rfl⟩
  have hF := (finite_comm_charpoly hs).to_subtype
  have hinj : Function.Injective (ujMat ε) := Units.val_injective.comp Subtype.val_injective
  let φ : Subgroup.normalizer (cent s : Set (UJ ε)) →
      {M : Matrix (Fin n) (Fin n) ℂ | M * ujMat ε s = ujMat ε s * M ∧ M.charpoly = (ujMat ε s).charpoly} :=
    fun x => ⟨ujMat ε (x * s * x⁻¹), by
      have := mem_cent.1 ((Subgroup.mem_normalizer_iff.1 x.2 s).1 (mem_cent.2 rfl))
      rw [← map_mul, ← map_mul]
      exact congrArg _ this, by
      have := Matrix.charpoly_units_conj x.1.1 (ujMat ε s)
      rw [← Matrix.coe_units_inv] at this
      exact this⟩
  have hφ : ∀ x y, φ x = φ y → x⁻¹ * y ∈ (cent s).subgroupOf (Subgroup.normalizer (cent s : Set (UJ ε))) :=
    fun x y h => by
      have h1 : (x : UJ ε) * s * (x : UJ ε)⁻¹ = y * s * (y : UJ ε)⁻¹ := hinj (congrArg Subtype.val h)
      rw [Subgroup.mem_subgroupOf, mem_cent]
      push_cast
      calc (x : UJ ε)⁻¹ * y * s = (x : UJ ε)⁻¹ * (y * s * (y : UJ ε)⁻¹) * y := by group
        _ = s * ((x : UJ ε)⁻¹ * y) := by rw [← h1]; group
  have : Finite (Subgroup.normalizer (cent s : Set (UJ ε)) ⧸
      (cent s).subgroupOf (Subgroup.normalizer (cent s : Set (UJ ε)))) :=
    Finite.of_injective (fun q => φ q.out) fun q r h => by
      rw [← q.out_eq, ← r.out_eq]
      exact QuotientGroup.eq.2 (hφ _ _ h)
  exact Subgroup.index_ne_zero_of_finite

end GlobalTheory.HCChar
