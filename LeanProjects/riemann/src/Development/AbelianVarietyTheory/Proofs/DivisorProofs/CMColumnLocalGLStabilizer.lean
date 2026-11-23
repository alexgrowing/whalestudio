import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeviBlockSizesSum
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsBlockCentre
import Development.AbelianVarietyTheory.Definitions.Foundations.GLintEqKOAndPrincEqKOne
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LocalFieldNormValuation
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SmGL GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.LeviBlockExponent GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.UAut GlobalTheory.SiegelSet GlobalTheory.ThK.SquareIntegrability
open scoped TensorProduct
open Matrix

noncomputable section

namespace GlobalTheory.LeviBlockFrame

theorem mulVec_sub_mem_span_frame : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (hJ : IsHermND σ J) (r : ℕ)
    (X : Matrix (Fin n) (Fin r) E), r ≤ n →
    ∀ (v : HeightOneSpectrum (𝓞 F)) (t : E →ₐ[F] Fv F v) (hcm : IsCMExt F E σ) (B : GL (Fin n) (Fv F v)),
    (∀ (j : Fin r) (k : Fin n), (k : ℕ) = j → ∀ a, B.1 a k = t (X a j)) → ∀ (i : Fin r) (g : GL (Fin n) (Fv F v)),
    (∀ l j : Fin n, (g.1 - 1) l j ≠ 0 → (l : ℕ) ≤ i ∧ (l : ℕ) < j) → ∀ y : Fin n → Fv F v ⊗[F] E,
    (∀ l : Fin r, l ≤ i → (((Formalism.UG.cT (σ : E →+* E) X * J).map (inclR (F := F) (Fv F v))) *ᵥ y) l = 0) →
    (matHom _ σ J ((splitEquiv hcm hJ t).symm (B * g * B⁻¹))).1 *ᵥ y - y ∈
      Submodule.span (Fv F v ⊗[F] E) ((fun l a => inclR (F := F) (Fv F v) (X a l)) '' {l : Fin r | l ≤ i}) := by
  intro F E _ _ _ _ _ σ n J hJ r X hrn v t hcm B hB i g hg y hy
  set h : GL (Fin n) (Fv F v) := B * g * B⁻¹ with hh
  set x := (splitEquiv hcm hJ t).symm h with hx
  have h1 : splitHom σ J t x = h := (splitEquiv hcm hJ t).apply_symm_apply h
  have h2 : splitHom σ J (t.comp σ) x = dualConj (splitGram hJ t) h := by rw [splitHom_comp hJ, h1]
  set u := splitVec t y with hu
  set u' := splitVec (t.comp σ) y with hu'
  have hrow : ∀ (k : Fin n) (w : Fin n → Fv F v), (i : ℕ) < k → ((g.1 - 1) *ᵥ w) k = 0 := by
    intro k w hk
    simp only [Matrix.mulVec, dotProduct]
    refine Finset.sum_eq_zero fun j _ => ?_
    by_contra hne
    have := hg k j (left_ne_zero_of_mul hne)
    omega
  set w := (g.1 - 1) *ᵥ ((B⁻¹).1 *ᵥ u) with hw
  set S := Finset.univ.filter (fun l : Fin r => l ≤ i) with hS

  have key1 : h.1 *ᵥ u - u = ∑ l ∈ S, w (Fin.castLE hrn l) • (fun a => t (X a l)) := by
    have e : h.1 - 1 = B.1 * (g.1 - 1) * (B⁻¹).1 := by
      rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, Units.mul_inv, hh, Units.val_mul, Units.val_mul]
    have e' : h.1 *ᵥ u - u = B.1 *ᵥ w := by
      rw [hw, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ← e, Matrix.sub_mulVec, Matrix.one_mulVec]
    rw [e']
    funext a
    simp only [Matrix.mulVec, dotProduct, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    have hB' : ∀ l : Fin r, t (X a l) = B.1 a (Fin.castLE hrn l) := fun l => (hB l (Fin.castLE hrn l) rfl a).symm
    simp only [hB']
    rw [show (∑ l ∈ S, w (Fin.castLE hrn l) * B.1 a (Fin.castLE hrn l)) =
        ∑ k ∈ S.map (Fin.castLEEmb hrn), B.1 a k * w k by
      rw [Finset.sum_map]; exact Finset.sum_congr rfl fun _ _ => mul_comm _ _]
    symm
    refine Finset.sum_subset (Finset.subset_univ _) fun k _ hk => ?_
    by_cases hki : (i : ℕ) < k
    · rw [hw, hrow k _ hki, mul_zero]
    · exfalso
      refine hk (Finset.mem_map.2 ⟨⟨k, by omega⟩, Finset.mem_filter.2 ⟨Finset.mem_univ _, ?_⟩, Fin.ext rfl⟩)
      change (k : ℕ) ≤ i
      omega

  have key2 : (dualConj (splitGram hJ t) h).1 *ᵥ u' = u' := by
    set z := u' ᵥ* (splitGram hJ t).1 ᵥ* B.1 with hz
    have hz0 : ∀ l : Fin n, (l : ℕ) ≤ i → z l = 0 := by
      intro l hli
      set l' : Fin r := ⟨l, lt_of_le_of_lt hli i.2⟩
      have hq := congrArg (splitProj (t.comp σ)) (hy l' (by change (l : ℕ) ≤ i; exact hli))
      have hBl : ∀ a, B.1 a l = t (X a l') := hB l' l rfl
      simp only [Matrix.mulVec, dotProduct, map_sum, map_mul, Matrix.map_apply, splitProj_inclR, map_zero,
        Formalism.UG.cT, Matrix.mul_apply, Matrix.transpose_apply, AlgHom.comp_apply, RingHom.coe_coe,
        cm_conj_conj hcm, hJ.1] at hq
      simp only [hz, Matrix.vecMul, dotProduct, splitGram_val, Matrix.map_apply, hBl]
      rw [← hq]
      simp only [Finset.sum_mul]
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by simp only [hu', splitVec]; ring
    have hzg : z ᵥ* g.1 = z := by
      have : z ᵥ* (g.1 - 1) = 0 := by
        funext j
        simp only [Matrix.vecMul, dotProduct, Pi.zero_apply]
        refine Finset.sum_eq_zero fun l _ => ?_
        by_cases hl : (g.1 - 1) l j = 0
        · rw [hl, mul_zero]
        · rw [hz0 l (hg l j hl).1, zero_mul]
      rwa [Matrix.vecMul_sub, Matrix.vecMul_one, sub_eq_zero] at this
    have hzg' : z ᵥ* (g⁻¹).1 = z := by
      conv_lhs => rw [← hzg]
      rw [Matrix.vecMul_vecMul, Units.mul_inv, Matrix.vecMul_one]
    have hhi : (h⁻¹).1 = B.1 * (g⁻¹).1 * (B⁻¹).1 := by
      rw [hh, _root_.mul_inv_rev, _root_.mul_inv_rev, inv_inv, Units.val_mul, Units.val_mul, Matrix.mul_assoc]
    have e3 : u' ᵥ* (splitGram hJ t).1 ᵥ* (h⁻¹).1 = u' ᵥ* (splitGram hJ t).1 := by
      rw [hhi, ← Matrix.vecMul_vecMul, ← Matrix.vecMul_vecMul, ← hz, hzg', hz, Matrix.vecMul_vecMul _ B.1,
        Units.mul_inv, Matrix.vecMul_one]
    rw [dualConj_val, Matrix.mulVec_transpose, ← Matrix.vecMul_vecMul, ← Matrix.vecMul_vecMul, e3,
      Matrix.vecMul_vecMul, Units.mul_inv, Matrix.vecMul_one]
  have heq : (matHom _ σ J x).1 *ᵥ y - y =
      ∑ l ∈ S, (w (Fin.castLE hrn l) • splitIdem hcm t) • (fun a => inclR (F := F) (Fv F v) (X a l)) := by
    refine splitVec_ext hcm t ?_ ?_
    · have e1 : splitVec t ((matHom _ σ J x).1 *ᵥ y) = h.1 *ᵥ u := by rw [splitVec_matHom_mulVec, h1]
      have : splitVec t ((matHom _ σ J x).1 *ᵥ y - y) = splitVec t ((matHom _ σ J x).1 *ᵥ y) - u :=
        funext fun a => map_sub _ _ _
      rw [this, e1, key1]
      funext a
      simp [splitVec, Finset.sum_apply, map_sum, splitProj_inclR]
    · have e2 : splitVec (t.comp σ) ((matHom _ σ J x).1 *ᵥ y) = u' := by rw [splitVec_matHom_mulVec, h2, key2]
      have : splitVec (t.comp σ) ((matHom _ σ J x).1 *ᵥ y - y) = splitVec (t.comp σ) ((matHom _ σ J x).1 *ᵥ y) - u' :=
        funext fun a => map_sub _ _ _
      rw [this, e2, sub_self]
      funext a
      simp [splitVec, Finset.sum_apply, map_sum]
  rw [heq]
  exact Submodule.sum_mem _ fun l hl => Submodule.smul_mem _ _
    (Submodule.subset_span ⟨l, (Finset.mem_filter.1 hl).2, rfl⟩)

end GlobalTheory.LeviBlockFrame
