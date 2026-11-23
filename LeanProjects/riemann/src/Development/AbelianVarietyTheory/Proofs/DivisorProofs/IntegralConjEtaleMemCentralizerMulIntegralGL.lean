import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnifAt
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NormEqOneOfIsUnit
import Development.AbelianVarietyTheory.Definitions.Foundations.GLintEqKOAndPrincEqKOne
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.SplitUniq

theorem splitUniq : ∀ (E : Type) [Field E] [NumberField E] (n : ℕ) (w : HeightOneSpectrum (𝓞 E))
    (N g : GL (Fin n) (w.adicCompletion E)), N ∈ GlobalTheory.LFun.KGL w n →
    (∃ u v : (w.adicCompletion E)[X], (∀ i, u.coeff i ∈ w.adicCompletionIntegers E) ∧
      (∀ i, v.coeff i ∈ w.adicCompletionIntegers E) ∧ u * N.val.charpoly + v * derivative N.val.charpoly = 1) →
    g⁻¹ * N * g ∈ GlobalTheory.LFun.KGL w n → ∃ t : GL (Fin n) (w.adicCompletion E), t * N = N * t ∧ ∃ k ∈ GlobalTheory.LFun.KGL w n, g = t * k := by
  intro E _ _ n w N g hN hs hg
  letI : NontriviallyNormedField (w.adicCompletion E) := Valued.toNontriviallyNormedField _ _
  have key : ∀ x : w.adicCompletion E, ‖x‖ ≤ 1 ↔ x ∈ w.adicCompletionIntegers E := fun x => by
    rw [Valued.toNormedField.norm_le_one_iff, HeightOneSpectrum.mem_adicCompletionIntegers]
  have memK : ∀ h : GL (Fin n) (w.adicCompletion E), h ∈ GlobalTheory.LFun.KGL w n ↔
      (∀ i j, h.1 i j ∈ w.adicCompletionIntegers E) ∧ ∀ i j, (h⁻¹).1 i j ∈ w.adicCompletionIntegers E := fun h => by
    rw [GlobalTheory.LFun.KGL, GlobalTheory.AdelicU.mem_GLint_iff]; rfl
  obtain ⟨hN1, -⟩ := (memK N).1 hN
  obtain ⟨hg1, -⟩ := (memK _).1 hg
  obtain ⟨u, v, hu, hv, huv⟩ := hs
  have hconj : ((g⁻¹ * N * g : GL (Fin n) (w.adicCompletion E)) : Matrix (Fin n) (Fin n) (w.adicCompletion E)) =
      (g : Matrix (Fin n) (Fin n) (w.adicCompletion E))⁻¹ * N * g := by
    rw [Units.val_mul, Units.val_mul, Matrix.coe_units_inv]
  obtain ⟨t, k, ht, htN, hk, hdet, hgtk⟩ := GlobalTheory.SplitLattice.split_place (w.adicCompletion E) n N.val g.val
    (fun i j => (key _).2 (hN1 i j)) ⟨u, v, fun i => (key _).2 (hu i), fun i => (key _).2 (hv i), huv⟩ g.isUnit
    (fun i j => (key _).2 (by rw [← hconj]; exact hg1 i j))
  set tU := ht.unit with htU
  refine ⟨tU, Units.ext htN, tU⁻¹ * g, ?_, by rw [mul_inv_cancel_left]⟩
  have hkv : ((tU⁻¹ * g : GL (Fin n) (w.adicCompletion E)) : Matrix (Fin n) (Fin n) (w.adicCompletion E)) = k := by
    have htt : (tU : Matrix (Fin n) (Fin n) (w.adicCompletion E)) = t := ht.unit_spec
    rw [Units.val_mul, hgtk, ← htt, ← mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_mul]
  have hkI : ∀ i j, k i j ∈ w.adicCompletionIntegers E := fun i j => (key _).1 (hk i j)
  let M : Matrix (Fin n) (Fin n) (w.adicCompletionIntegers E) := Matrix.of fun i j => ⟨k i j, hkI i j⟩
  have hMk : M.map (w.adicCompletionIntegers E).subtype = k := by ext i j; rfl
  have hdetM : ((M.det : w.adicCompletionIntegers E) : w.adicCompletion E) = k.det := by
    rw [← hMk]
    exact (RingHom.map_det (w.adicCompletionIntegers E).subtype M)
  have hk0 : k.det ≠ 0 := by
    intro h0; rw [h0, norm_zero] at hdet; exact zero_ne_one hdet
  have hMu : IsUnit M.det := by
    have h1 : M.det * ⟨(k.det)⁻¹, (key _).1 (by rw [norm_inv, hdet, inv_one])⟩ = 1 := by
      apply Subtype.ext
      show ((M.det : w.adicCompletionIntegers E) : w.adicCompletion E) * (k.det)⁻¹ = 1
      rw [hdetM, mul_inv_cancel₀ hk0]
    exact ⟨⟨_, _, h1, by rw [mul_comm]; exact h1⟩, rfl⟩
  have hMM : M * M⁻¹ = 1 := Matrix.mul_nonsing_inv M hMu
  have hinv : k⁻¹ = M⁻¹.map (w.adicCompletionIntegers E).subtype := by
    apply Matrix.inv_eq_right_inv
    rw [← hMk, ← Matrix.map_mul, hMM, Matrix.map_one _ (map_zero _) (map_one _)]
  refine (memK _).2 ⟨fun i j => by rw [hkv]; exact hkI i j, fun i j => ?_⟩
  rw [Matrix.coe_units_inv, hkv, hinv]
  exact (M⁻¹ i j).2

end GlobalTheory.SplitUniq
