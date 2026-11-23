import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnifAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PlaceConjugationPropertiesCmField
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsUniqueIsConjAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHermitianFormCharPolyStatement
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section
namespace GlobalTheory.ExInertUnit

theorem globalForm : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (P : E[X]), P ∈ Ell E n →
    ∃ M G : Matrix (Fin n) (Fin n) E, M.charpoly = P ∧ IsUnit G ∧
      cT (IsCMField.complexConj E).toRingEquiv.toRingHom G = G ∧
      cT (IsCMField.complexConj E).toRingEquiv.toRingHom M * G * M = G := GlobalTheory.T.exists_hermitian_form_char_poly

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

theorem eventually_mem_integers (a : E) :
    ∀ᶠ w : Pl E in cofinite, algebraMap E (w.adicCompletion E) a ∈ w.adicCompletionIntegers E :=
  (algebraMap E (FiniteAdeleRing (𝓞 E) E) a).2

theorem mem_KGL_of_entries (w : Pl E) (g : GLw n w)
    (h1 : ∀ a b, g.val a b ∈ w.adicCompletionIntegers E)
    (h2 : ∀ a b, (g⁻¹).val a b ∈ w.adicCompletionIntegers E) : g ∈ GlobalTheory.LFun.KGL w n := by
  let O : Subring (w.adicCompletion E) := Ov E w
  have inj : Function.Injective (O.subtype.mapMatrix (m := Fin n)) :=
    fun A B h => funext fun i => funext fun j => Subtype.ext (congrFun (congrFun h i) j)
  let A : Matrix (Fin n) (Fin n) O := fun i j => ⟨g.val i j, h1 i j⟩
  let B : Matrix (Fin n) (Fin n) O := fun i j => ⟨(g⁻¹).val i j, h2 i j⟩
  have hA : O.subtype.mapMatrix A = g.val := rfl
  have hB : O.subtype.mapMatrix B = (g⁻¹).val := rfl
  refine ⟨⟨A, B, inj ?_, inj ?_⟩, Units.ext rfl⟩
  · rw [map_mul, hA, hB, map_one, Units.mul_inv]
  · rw [map_mul, hA, hB, map_one, Units.inv_mul]

theorem entries_of_mem_KGL {w : Pl E} {k : GLw n w} (hk : k ∈ GlobalTheory.LFun.KGL w n) (i j : Fin n) :
    k.val i j ∈ w.adicCompletionIntegers E := by
  obtain ⟨a, rfl⟩ := hk
  exact (a.val i j).2

theorem mul_entries {w : Pl E} {A B : Matrix (Fin n) (Fin n) (w.adicCompletion E)}
    (hA : ∀ i j, A i j ∈ w.adicCompletionIntegers E) (hB : ∀ i j, B i j ∈ w.adicCompletionIntegers E)
    (i j : Fin n) : (A * B) i j ∈ w.adicCompletionIntegers E := by
  rw [Matrix.mul_apply]
  exact sum_mem fun k _ => mul_mem (hA i k) (hB k j)

set_option maxHeartbeats 800000 in

theorem local_step (hE : Unr E) (w : Pl E) (hw : ¬ IsSplitAt w) (M G : Matrix (Fin n) (Fin n) E)
    (hG : IsUnit G) (hGh : cT (IsCMField.complexConj E).toRingEquiv.toRingHom G = G)
    (hMG : cT (IsCMField.complexConj E).toRingEquiv.toRingHom M * G * M = G)
    (hM : ∀ i j, algebraMap E (w.adicCompletion E) (M i j) ∈ w.adicCompletionIntegers E)
    (hG1 : ∀ i j, algebraMap E (w.adicCompletion E) (G i j) ∈ w.adicCompletionIntegers E)
    (hG2 : ∀ i j, algebraMap E (w.adicCompletion E) (G⁻¹ i j) ∈ w.adicCompletionIntegers E) :
    ∃ γ : UL n w, γ ∈ KL n w ∧ γ.1.val.charpoly = M.charpoly.map (algebraMap E (w.adicCompletion E)) := by
  obtain ⟨-, -, hv, hns, -⟩ := GlobalTheory.ConjAtPlace.main E hE w
  obtain ⟨hconj, ⟨ϖ, q, hU, -⟩, -⟩ := hns hw
  let f := algebraMap E (w.adicCompletion E)
  let c := (IsCMField.complexConj E).toRingEquiv.toRingHom
  have hcT : ∀ A : Matrix (Fin n) (Fin n) E, cT (cj w) (f.mapMatrix A) = f.mapMatrix (cT c A) := by
    intro A
    refine Matrix.ext fun i j => ?_
    simp only [cT, Matrix.transpose_apply, Matrix.map_apply, RingHom.mapMatrix_apply]
    exact hconj _
  have hdet : IsUnit G.det := (Matrix.isUnit_iff_isUnit_det G).1 hG
  have hGu : IsUnit (f.mapMatrix G) := hG.map _
  have hginv : ((hGu.unit)⁻¹ : GLw n w).val = f.mapMatrix G⁻¹ := by
    have h : f.mapMatrix G⁻¹ * f.mapMatrix G = 1 := by
      rw [← map_mul, Matrix.nonsing_inv_mul _ hdet, map_one]
    rw [Matrix.coe_units_inv, IsUnit.unit_spec]
    exact Matrix.inv_eq_left_inv h
  have hgK : hGu.unit ∈ GlobalTheory.LFun.KGL w n :=
    mem_KGL_of_entries w _ (fun a b => by rw [IsUnit.unit_spec]; exact hG1 a b)
      (fun a b => by rw [hginv]; exact hG2 a b)
  have hgh : cT (cj w) hGu.unit.val = hGu.unit.val := by
    rw [IsUnit.unit_spec, hcT, hGh]
  obtain ⟨k, hk, hkk⟩ := GlobalTheory.LFun.InertChart.exists_norm hU hgK hgh
  have hMu : IsUnit M := by
    have h : (G⁻¹ * cT c M * G) * M = 1 := by
      have h' := hMG
      simp only [Matrix.mul_assoc] at h' ⊢
      rw [h', Matrix.nonsing_inv_mul _ hdet]
    exact (Matrix.isUnit_iff_isUnit_det M).2 (Matrix.isUnit_det_of_left_inverse h)
  have hMwu : IsUnit (f.mapMatrix M) := hMu.map _
  have hmG : cT (cj w) hMwu.unit.val * hGu.unit.val * hMwu.unit.val = hGu.unit.val := by
    rw [IsUnit.unit_spec, IsUnit.unit_spec, hcT, ← map_mul, ← map_mul, hMG]
  have hkinv : cT (cj w) (k⁻¹ : GLw n w).val * cT (cj w) k.val = 1 := by
    rw [← cT_mul, Units.mul_inv, cT_one]
  set γ0 : GLw n w := k * hMwu.unit * k⁻¹ with hγ0
  have hγU : cT (cj w) γ0.val * 1 * γ0.val = 1 := by
    calc cT (cj w) γ0.val * 1 * γ0.val
        = cT (cj w) (k⁻¹ : GLw n w).val * (cT (cj w) hMwu.unit.val * (cT (cj w) k.val * k.val) * hMwu.unit.val)
            * (k⁻¹ : GLw n w).val := by
          rw [hγ0, Units.val_mul, Units.val_mul, cT_mul, cT_mul]
          simp only [Matrix.mul_assoc, Matrix.mul_one]
      _ = cT (cj w) (k⁻¹ : GLw n w).val * (cT (cj w) k.val * k.val) * (k⁻¹ : GLw n w).val := by
          rw [hkk, hmG]
      _ = 1 := by
          simp only [← Matrix.mul_assoc]
          rw [hkinv, Matrix.one_mul, Units.mul_inv]
  have hγUL : γ0 ∈ UL n w := by
    rw [UL, if_neg hw]
    exact hγU
  refine ⟨⟨γ0, hγUL⟩, ?_, ?_⟩
  · rw [KL, Subgroup.mem_subgroupOf]
    have hinv : cT (cj w) γ0.val = (γ0⁻¹ : GLw n w).val := by
      rw [Matrix.coe_units_inv]
      exact (Matrix.inv_eq_left_inv (by simpa using hγU)).symm
    have hint : ∀ a b, γ0.val a b ∈ w.adicCompletionIntegers E := by
      intro a b
      rw [hγ0, Units.val_mul, Units.val_mul]
      refine mul_entries (mul_entries (entries_of_mem_KGL hk) (fun i j => ?_))
        (entries_of_mem_KGL (inv_mem hk)) a b
      rw [IsUnit.unit_spec]
      exact hM i j
    refine mem_KGL_of_entries w γ0 hint (fun a b => ?_)
    rw [← hinv]
    have h0 := hint b a
    rw [HeightOneSpectrum.mem_adicCompletionIntegers] at h0 ⊢
    simp only [cT, Matrix.transpose_apply, Matrix.map_apply]
    rw [hv]
    exact h0
  · show (k.val * hMwu.unit.val * (k⁻¹ : GLw n w).val).charpoly = _
    rw [Matrix.coe_units_inv, Matrix.charpoly_units_conj, IsUnit.unit_spec]
    exact Matrix.charpoly_map M f

theorem exists_integral_unitary_charpoly : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ n : ℕ, 1 ≤ n →
    ∀ P ∈ Ell E n, ∀ᶠ w in cofinite, ¬ IsSplitAt w → ∃ γ : UL n w, γ ∈ KL n w ∧ γ.1.val.charpoly = atPl w P := by
  intro E _ _ _ hE n _ P hP
  obtain ⟨M, G, hMP, hG, hGh, hMG⟩ := globalForm E n P hP
  have h1 : ∀ᶠ w : Pl E in cofinite, ∀ i j,
      algebraMap E (w.adicCompletion E) (M i j) ∈ w.adicCompletionIntegers E :=
    eventually_all.2 fun i => eventually_all.2 fun j => eventually_mem_integers _
  have h2 : ∀ᶠ w : Pl E in cofinite, ∀ i j,
      algebraMap E (w.adicCompletion E) (G i j) ∈ w.adicCompletionIntegers E :=
    eventually_all.2 fun i => eventually_all.2 fun j => eventually_mem_integers _
  have h3 : ∀ᶠ w : Pl E in cofinite, ∀ i j,
      algebraMap E (w.adicCompletion E) (G⁻¹ i j) ∈ w.adicCompletionIntegers E :=
    eventually_all.2 fun i => eventually_all.2 fun j => eventually_mem_integers _
  filter_upwards [h1, h2, h3] with w hw1 hw2 hw3 hw
  obtain ⟨γ, hγ, hc⟩ := local_step hE w hw M G hG hGh hMG hw1 hw2 hw3
  exact ⟨γ, hγ, by rw [hc, hMP]⟩

end GlobalTheory.ExInertUnit
