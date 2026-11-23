import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SelfDualOne
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LatticeModelVacuumTranslateClassesIndependent
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.UnramifiedLocalDualPairSwapHermitianAdjoint
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.DualIntegralPreimageLeSumTransposeImageStatement

open Matrix

namespace GlobalTheory.Hk3.HoweG

theorem dualA_hform_eq {L : Type} [Field L] (σ : L →+* L) {n : ℕ} (J : Matrix (Fin n) (Fin n) L) (u v : Fin n → L) :
    Formalism.UG.hform σ J u v = (fun i => σ (u i)) ⬝ᵥ (J *ᵥ v) := by
  simp [Formalism.UG.hform, dotProduct, Matrix.mulVec, Finset.mul_sum, mul_assoc]

theorem dualA_conj_mulVec {L : Type} [Field L] (σ : L →+* L) {a b : ℕ} (y : Matrix (Fin a) (Fin b) L) (w : Fin b → L) :
    (fun i => σ ((y *ᵥ w) i)) = (y.map σ) *ᵥ (fun i => σ (w i)) := by
  funext i
  simp [dotProduct, Matrix.mulVec, map_sum]

theorem dualA_mulVec_int {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {a b : ℕ}
    {A : Matrix (Fin a) (Fin b) L} (hA : ∀ i j, A i j ∈ Formalism.UG.intL L) {w : Fin b → L}
    (hw : ∀ i, w i ∈ Formalism.UG.intL L) (i : Fin a) : (A *ᵥ w) i ∈ Formalism.UG.intL L := by
  simp only [Matrix.mulVec, dotProduct]
  exact Subring.sum_mem _ fun k _ => Subring.mul_mem _ (hA i k) (hw k)

theorem hermDual_subset_of_gram_int : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (σ : L →+* L) (n n' : ℕ) (JS : GL (Fin n) L) (JT : GL (Fin n') L),
    (∀ z, σ (σ z) = z) → (∀ z, Valued.v (σ z) = Valued.v z) →
    JS ∈ Formalism.UG.GLint (Fin n) (Formalism.UG.intL L) → JT ∈ Formalism.UG.GLint (Fin n') (Formalism.UG.intL L) →
    (∀ i j, σ ((JS : Matrix (Fin n) (Fin n) L) i j) = (JS : Matrix (Fin n) (Fin n) L) j i) →
    (∀ i j, σ ((JT : Matrix (Fin n') (Fin n') L) i j) = (JT : Matrix (Fin n') (Fin n') L) j i) →
    ∀ x : Matrix (Fin n') (Fin n) L, (∀ i j, (x * ((JS⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) * Matrix.transpose (x.map σ)) i j ∈ Formalism.UG.intL L) →
    ∀ v : Fin n → L,
      (∀ u : Fin n → L, (∀ i, u i ∈ Formalism.UG.intL L) → (∀ i, (x *ᵥ u) i ∈ Formalism.UG.intL L) →
        Formalism.UG.hform σ (JS : Matrix (Fin n) (Fin n) L) u v ∈ Formalism.UG.intL L) →
      (∀ w : Fin n' → L, (∀ i, w i ∈ Formalism.UG.intL L) →
        Formalism.UG.hform σ (JS : Matrix (Fin n) (Fin n) L) (GlobalTheory.Hk3.HoweG.adj σ JS JT x *ᵥ w) v ∈ Formalism.UG.intL L) →
      ∃ u : Fin n → L, ∃ w : Fin n' → L, (∀ i, u i ∈ Formalism.UG.intL L) ∧ (∀ i, (x *ᵥ u) i ∈ Formalism.UG.intL L) ∧
        (∀ i, w i ∈ Formalism.UG.intL L) ∧ v = u + GlobalTheory.Hk3.HoweG.adj σ JS JT x *ᵥ w := by
  intro L _ _ σ n n' JS JT hσ hv hJS hJT hS0 hT0 x hx v h1 h2
  have hS : Formalism.UG.cT σ (JS : Matrix (Fin n) (Fin n) L) = JS := HoweSwap.cT_herm hS0
  have hT : Formalism.UG.cT σ (JT : Matrix (Fin n') (Fin n') L) = JT := HoweSwap.cT_herm hT0
  have hSi := HoweSwap.cT_inv_herm JS hS
  obtain ⟨hS1, hS2⟩ := HoweSwap.glint_int hJS
  obtain ⟨hT1, hT2⟩ := HoweSwap.glint_int hJT
  have hint : ∀ z, z ∈ Formalism.UG.intL L → σ z ∈ Formalism.UG.intL L := by
    intro z hz
    simp only [Formalism.UG.intL, Valuation.mem_integer_iff] at hz ⊢
    rwa [hv]
  obtain ⟨l, w, hl, hw, hz⟩ := GlobalTheory.T.dual_integral_preimage_le_sum_transpose_image L n' n (x.map σ) ((JS : Matrix (Fin n) (Fin n) L) *ᵥ v) (by
    intro u hu hxu
    have e : x *ᵥ (fun i => σ (u i)) = fun i => σ ((x.map σ *ᵥ u) i) := by
      rw [dualA_conj_mulVec]
      congr 1
      ext i j; simp [hσ]
    have := h1 (fun i => σ (u i)) (fun i => hint _ (hu i)) (fun i => by rw [e]; exact hint _ (hxu i))
    rw [dualA_hform_eq] at this
    simpa [dotProduct, hσ] using this)
  have hc : ∀ {a b : Type} (Z : Matrix a b L), (Z.map σ)ᵀ = Formalism.UG.cT σ Z := fun _ => rfl
  have hy : Formalism.UG.cT σ (adj σ JS JT x) * (JS : Matrix (Fin n) (Fin n) L) = (JT : Matrix (Fin n') (Fin n') L) * x := by
    simp only [adj, Formalism.UG.cT_mul, HoweSwap.cT_cT hσ, hT, hSi, Matrix.mul_assoc, Units.inv_mul, Matrix.mul_one]
  have hTxv : ∀ k, (((JT : Matrix (Fin n') (Fin n') L) * x) *ᵥ v) k ∈ Formalism.UG.intL L := by
    intro k
    have := h2 (Pi.single k 1) (fun i => by
      by_cases h : i = k
      · subst h; simp
      · simp [h])
    rw [dualA_hform_eq, dualA_conj_mulVec, dotProduct_comm, Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, hc,
      Matrix.mulVec_mulVec, hy] at this
    have e : (fun i => σ ((Pi.single k 1 : Fin n' → L) i)) = Pi.single k 1 := by
      funext i
      by_cases h : i = k
      · subst h; simp
      · simp [h]
    rw [e] at this
    simpa using this
  have hxv : ∀ k, (x *ᵥ v) k ∈ Formalism.UG.intL L := by
    intro k
    have := dualA_mulVec_int hT2 hTxv k
    rwa [Matrix.mulVec_mulVec, HoweSwap.inv_mul_cl] at this
  have hyw : adj σ JS JT x *ᵥ (((JT⁻¹ : GL (Fin n') L) : Matrix (Fin n') (Fin n') L) *ᵥ w) =
      (((JS⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) * (x.map σ)ᵀ) *ᵥ w := by
    rw [Matrix.mulVec_mulVec, adj, Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one, hc]
  have hv2 : v = ((JS⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) *ᵥ l +
      (((JS⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) * (x.map σ)ᵀ) *ᵥ w := by
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_add, ← hz, Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec]
  refine ⟨((JS⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) *ᵥ l,
    ((JT⁻¹ : GL (Fin n') L) : Matrix (Fin n') (Fin n') L) *ᵥ w, dualA_mulVec_int hS2 hl, fun i => ?_,
    dualA_mulVec_int hT2 hw, by rw [hyw]; exact hv2⟩
  have e : x *ᵥ (((JS⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) *ᵥ l) = x *ᵥ v -
      (x * ((JS⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) * (x.map σ)ᵀ) *ᵥ w := by
    conv_rhs => rw [hv2]
    rw [Matrix.mulVec_add, Matrix.mulVec_mulVec w, ← Matrix.mul_assoc, add_sub_cancel_right]
  rw [e, Pi.sub_apply]
  exact Subring.sub_mem _ (hxv i) (dualA_mulVec_int hx hw i)

end GlobalTheory.Hk3.HoweG
