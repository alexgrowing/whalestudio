import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusOfSpec
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedOrbitalIntegralSummandGoodPlaceIndicator
open NumberField GlobalTheory.UnitaryBC IsDedekindDomain Matrix Polynomial GlobalTheory.CuspRep Formalism.UG GlobalTheory.BCT GlobalTheory.KapLat GlobalTheory.KapOrb
open scoped Classical

noncomputable section

namespace GlobalTheory.KapCong

theorem mem_GLint_of_entries {L : Type} [Field L] {n : ℕ} {O : Subring L} {x : GL (Fin n) L}
    (h1 : ∀ i j, x.1 i j ∈ O) (h2 : ∀ i j, (x⁻¹).1 i j ∈ O) : x ∈ GLint (Fin n) O := by
  refine ⟨⟨Matrix.of fun i j => ⟨_, h1 i j⟩, Matrix.of fun i j => ⟨_, h2 i j⟩, ?_, ?_⟩, rfl⟩
  · refine Matrix.map_injective O.subtype_injective ?_
    simp only
    rw [Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _)]
    exact x.mul_inv
  · refine Matrix.map_injective O.subtype_injective ?_
    simp only
    rw [Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _)]
    exact x.inv_mul

theorem pullLat_stable_iff_cong : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (w : Pl E), ¬ IsSplitAt w → ∀ (K : GlobalTheory.UnitLemma.UQ) (e : K.E ≃+* w.adicCompletion E), Bridge w K e → ∀ (k : ℕ) (t : K.O), K.Small t → GlobalTheory.UnitLemma.val K.O (algebraMap K.O K.E t) = k → ∀ (B : GlobalTheory.UnitLemma.InvAlg K) (u x : B.A) (n : ℕ) (γ : GLw n w) (ψ : B.A ≃+ (Fin n → w.adicCompletion E)), IsModelMap w e B u x γ ψ → u = 1 + algebraMap K.O B.A t * B.g → γ ∈ UL n w → ∀ g ∈ UL n w, ((∀ y ∈ pullLat w B ψ g, B.g * y ∈ pullLat w B ψ g) ↔ g⁻¹ * γ * g ∈ congSet w n k) := by
  intro E _ _ _ w hns K e hB k t ht hval B u x n γ ψ hψ hu hγ g hg
  obtain ⟨hsemi, hmul, -⟩ := hψ
  obtain ⟨hBc, hBint, hBval, -⟩ := hB
  have hO : ∀ z : w.adicCompletion E, z ∈ w.adicCompletionIntegers E ↔ Valued.v z ≤ 1 :=
    fun z => HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 E) E w
  have heO : ∀ c : K.O, e (algebraMap K.O K.E c) ∈ w.adicCompletionIntegers E :=
    fun c => (hO _).2 ((hBint _).1 ⟨c, rfl⟩)
  have hcjO : ∀ z ∈ w.adicCompletionIntegers E, cj w z ∈ w.adicCompletionIntegers E := by
    intro z hz
    obtain ⟨o, ho⟩ := (hBint (e.symm z)).2 (by rw [e.apply_symm_apply]; exact (hO z).1 hz)
    obtain ⟨o', ho'⟩ := K.c_int o
    have h2 : cj w z = e (algebraMap K.O K.E o') := by
      rw [← ho', ho, hBc, e.apply_symm_apply]
    rw [h2]; exact heO o'
  obtain ⟨et, het⟩ : ∃ et, e (algebraMap K.O K.E t) = et := ⟨_, rfl⟩
  have het0 : et ≠ 0 := by
    rw [← het]; intro h0
    apply ht.1
    have h1 : algebraMap K.O K.E t = 0 := e.injective (h0.trans (map_zero e).symm)
    exact IsFractionRing.injective K.O K.E (h1.trans (map_zero _).symm)
  have hvet : Valued.v et = WithZero.exp (-(k : ℤ)) := by
    have h1 := hBval (algebraMap K.O K.E t)
    rw [hval, het] at h1
    have hv0 : Valued.v et ≠ 0 := (Valuation.ne_zero_iff _).2 het0
    unfold ordL at h1
    rw [dif_neg hv0] at h1
    rw [← WithZero.coe_unzero hv0, WithZero.exp]
    congr 1
    apply Multiplicative.toAdd.injective
    rw [toAdd_ofAdd]
    omega
  have hkey : ∀ y, ψ (B.g * y) = et⁻¹ • (γ.val *ᵥ ψ y - ψ y) := by
    intro y
    have h1 := hmul y
    rw [hu, add_mul, one_mul, mul_assoc, map_add, IsScalarTower.algebraMap_apply K.O K.E B.A, ← Algebra.smul_def,
      hsemi, het] at h1
    rw [← h1, add_sub_cancel_left, smul_smul, inv_mul_cancel₀ het0, one_smul]
  have hmem : ∀ (h : GLw n w) y, y ∈ pullLat w B ψ h ↔
      ∀ i, ((h⁻¹ : GLw n w).val *ᵥ ψ y) i ∈ w.adicCompletionIntegers E := by
    intro h y
    constructor
    · intro hy i
      have h1 : ((h⁻¹ : GLw n w).val *ᵥ ψ ((1 : K.O) • y)) i ∈ w.adicCompletionIntegers E := hy 1 i
      rwa [one_smul] at h1
    · intro hy c i
      show ((h⁻¹ : GLw n w).val *ᵥ ψ (c • y)) i ∈ _
      rw [← IsScalarTower.algebraMap_smul K.E c y, hsemi, Matrix.mulVec_smul, Pi.smul_apply, smul_eq_mul]
      exact mul_mem (heO c) (hy i)
  have hgg : (g⁻¹ * γ * g : GLw n w).val * (g⁻¹ : GLw n w).val = (g⁻¹ : GLw n w).val * γ.val := by
    rw [← Units.val_mul, mul_inv_cancel_right, Units.val_mul]
  have hG : ∀ y, (g⁻¹ : GLw n w).val *ᵥ ψ (B.g * y) =
      et⁻¹ • (((g⁻¹ * γ * g : GLw n w).val - 1) *ᵥ ((g⁻¹ : GLw n w).val *ᵥ ψ y)) := by
    intro y
    rw [hkey, Matrix.mulVec_smul, Matrix.mulVec_sub, Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.mulVec_mulVec,
      Matrix.mulVec_mulVec (ψ y) ((g⁻¹ * γ * g : GLw n w).val), hgg]
  have hinvg : ∀ v : Fin n → w.adicCompletion E, (g⁻¹ : GLw n w).val *ᵥ (g.val *ᵥ v) = v := by
    intro v
    rw [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec]
  have hP : (∀ y ∈ pullLat w B ψ g, B.g * y ∈ pullLat w B ψ g) ↔
      ∀ v : Fin n → w.adicCompletion E, (∀ i, v i ∈ w.adicCompletionIntegers E) →
        ∀ i, (et⁻¹ • (((g⁻¹ * γ * g : GLw n w).val - 1) *ᵥ v)) i ∈ w.adicCompletionIntegers E := by
    constructor
    · intro H v hv i
      have hy : ψ.symm (g.val *ᵥ v) ∈ pullLat w B ψ g := by
        rw [hmem]; intro j; rw [ψ.apply_symm_apply, hinvg]; exact hv j
      have h1 := (hmem g _).1 (H _ hy) i
      rwa [hG, ψ.apply_symm_apply, hinvg] at h1
    · intro H y hy
      rw [hmem] at hy ⊢
      intro i; rw [hG]; exact H _ hy i
  have hent : ∀ z, et⁻¹ * z ∈ w.adicCompletionIntegers E ↔ Valued.v z ≤ WithZero.exp (-(k : ℤ)) := by
    intro z
    rw [hO, map_mul, map_inv₀, hvet]
    exact inv_mul_le_one₀ (WithZero.exp_pos)
  have hPQ : (∀ v : Fin n → w.adicCompletion E, (∀ i, v i ∈ w.adicCompletionIntegers E) →
        ∀ i, (et⁻¹ • (((g⁻¹ * γ * g : GLw n w).val - 1) *ᵥ v)) i ∈ w.adicCompletionIntegers E) ↔
      ∀ i j, Valued.v (((g⁻¹ * γ * g : GLw n w).val - 1) i j) ≤ WithZero.exp (-(k : ℤ)) := by
    constructor
    · intro H i j
      have h1 := H (Pi.single j 1) (fun l => by
        rw [Pi.single_apply]; split_ifs
        · exact one_mem _
        · exact zero_mem _) i
      rw [Pi.smul_apply, smul_eq_mul, Matrix.mulVec_single_one] at h1
      change et⁻¹ * ((g⁻¹ * γ * g : GLw n w).val - 1) i j ∈ _ at h1
      rwa [hent] at h1
    · intro H v hv i
      rw [Pi.smul_apply, smul_eq_mul, Matrix.mulVec, dotProduct, Finset.mul_sum]
      refine sum_mem fun j _ => ?_
      rw [← mul_assoc]
      exact mul_mem ((hent _).2 (H i j)) (hv j)
  rw [hP, hPQ]
  constructor
  · intro H
    refine ⟨?_, fun i j => by simpa [Matrix.sub_apply] using H i j⟩
    have hγ' : g⁻¹ * γ * g ∈ UL n w := mul_mem (mul_mem (inv_mem hg) hγ) hg
    unfold UL at hγ'
    rw [if_neg hns] at hγ'
    have hU : cT (cj w) (g⁻¹ * γ * g : GLw n w).val * 1 * (g⁻¹ * γ * g : GLw n w).val = 1 := hγ'
    rw [Matrix.mul_one] at hU
    have hinv : ((g⁻¹ * γ * g)⁻¹ : GLw n w).val = cT (cj w) (g⁻¹ * γ * g : GLw n w).val :=
      Units.inv_eq_of_mul_eq_one_left hU
    have hint : ∀ i j, (g⁻¹ * γ * g : GLw n w).val i j ∈ w.adicCompletionIntegers E := by
      intro i j
      have h1 : (g⁻¹ * γ * g : GLw n w).val i j =
          ((g⁻¹ * γ * g : GLw n w).val - 1) i j + (1 : Matrix (Fin n) (Fin n) (w.adicCompletion E)) i j := by
        rw [Matrix.sub_apply, sub_add_cancel]
      rw [h1]
      refine add_mem ((hO _).2 ((H i j).trans ((WithZero.exp_le_exp.2 (by omega)).trans_eq WithZero.exp_zero))) ?_
      rw [Matrix.one_apply]; split_ifs
      · exact one_mem _
      · exact zero_mem _
    refine mem_GLint_of_entries (fun i j => hint i j) (fun i j => ?_)
    rw [hinv]
    exact hcjO _ (hint j i)
  · intro H i j
    simpa [Matrix.sub_apply] using H.2 i j

end GlobalTheory.KapCong
