import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalMaximality.ResidueOfTraceIsFiberSum
open KaehlerDifferential GlobalTheory.CechDR GlobalTheory.PD GlobalTheory.WH GlobalTheory.W1 UpperTheory.Gal.productCup_of_system
open scoped TensorProduct

section OmLocAux
variable {L : Type} [Field L] [Algebra ℂ L]

private noncomputable def om1 (B : Subalgebra ℂ L) : Submodule ℂ Ω[L⁄ℂ] :=
  Submodule.span ℂ {w | ∃ b ∈ B, ∃ u ∈ B, w = b • D ℂ L u}

private lemma omB_stab (B : Subalgebra ℂ L) (q : ℕ) {r : L} (hr : r ∈ B) {m : DR ℂ L}
    (hm : m ∈ omB ℂ L B q) : r • m ∈ omB ℂ L B q := by
  have h : omB ℂ L B q ≤ (omB ℂ L B q).comap (Algebra.lsmul ℂ ℂ (DR ℂ L) r) := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨b, hb, v, hv, rfl⟩
    refine Submodule.subset_span ⟨r * b, B.mul_mem hr hb, v, hv, ?_⟩
    simp [mul_smul]
  exact h hm

private lemma omB_mono {B B' : Subalgebra ℂ L} (h : B ≤ B') (q : ℕ) : omB ℂ L B q ≤ omB ℂ L B' q := by
  refine Submodule.span_mono ?_
  rintro _ ⟨b, hb, v, hv, rfl⟩
  exact ⟨b, h hb, v, fun j => h (hv j), rfl⟩

private lemma ι_mul_mem (B : Subalgebra ℂ L) (q : ℕ) {w : Ω[L⁄ℂ]} (hw : w ∈ om1 B) {y : DR ℂ L}
    (hy : y ∈ omB ℂ L B q) : ExteriorAlgebra.ι L w * y ∈ omB ℂ L B (q + 1) := by
  induction hw using Submodule.span_induction with
  | mem w hw =>
    obtain ⟨b, hb, u, hu, rfl⟩ := hw
    induction hy using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨c, hc, v, hv, rfl⟩ := hy
      refine Submodule.subset_span ⟨b * c, B.mul_mem hb hc, Fin.cons u v, fun j => ?_, ?_⟩
      · exact Fin.cases hu hv j
      · rw [ExteriorAlgebra.ιMulti_succ_apply]
        simp [Matrix.vecTail, mul_smul, Function.comp_def, smul_comm b c]
    | zero => simp
    | add a a' _ _ h h' => rw [mul_add]; exact Submodule.add_mem _ h h'
    | smul t a _ h => rw [mul_smul_comm]; exact Submodule.smul_mem _ t h
  | zero => simp
  | add a a' _ _ h h' => rw [map_add, add_mul]; exact Submodule.add_mem _ h h'
  | smul t a _ h => rw [LinearMap.map_smul_of_tower, smul_mul_assoc]; exact Submodule.smul_mem _ t h

private lemma ιMulti_mem (B : Subalgebra ℂ L) (q : ℕ) (w : Fin q → Ω[L⁄ℂ]) (hw : ∀ j, w j ∈ om1 B) :
    ExteriorAlgebra.ιMulti L q w ∈ omB ℂ L B q := by
  induction q with
  | zero =>
    refine Submodule.subset_span ⟨1, B.one_mem, Fin.elim0, fun j => j.elim0, ?_⟩
    rw [one_smul]
    exact congrArg _ (Subsingleton.elim _ _)
  | succ q ih =>
    rw [ExteriorAlgebra.ιMulti_succ_apply]
    exact ι_mul_mem B q (hw 0) (ih _ fun j => hw _)

private lemma two_mem (B : Subalgebra ℂ L) {b v : L} (hb : b ∈ B) (hv : b * v ∈ B) :
    (b ^ 2) • D ℂ L v ∈ om1 B := by
  have h : (b ^ 2) • D ℂ L v = b • D ℂ L (b * v) - (b * v) • D ℂ L b := by
    rw [Derivation.leibniz, smul_add, smul_smul, smul_smul, pow_two, mul_comm b v]
    abel
  rw [h]
  exact Submodule.sub_mem _ (Submodule.subset_span ⟨b, hb, _, hv, rfl⟩)
    (Submodule.subset_span ⟨_, hv, b, hb, rfl⟩)

private lemma common_den (B : Subalgebra ℂ L) (e : B →ₐ[ℂ] ℂ) {q : ℕ} {c : L} {v : Fin q → L}
    (hc : c ∈ loc B e) (hv : ∀ j, v j ∈ loc B e) :
    ∃ b : B, e b ≠ 0 ∧ (b : L) * c ∈ B ∧ ∀ j, (b : L) * v j ∈ B := by
  obtain ⟨b0, h0, hc'⟩ := hc
  choose f hf hf' using hv
  refine ⟨b0 * ∏ j, f j, ?_, ?_, fun j => ?_⟩
  · rw [map_mul, map_prod]
    exact mul_ne_zero h0 (Finset.prod_ne_zero_iff.2 fun j _ => hf j)
  · have h := B.mul_mem (∏ j, f j).2 hc'
    convert h using 1
    push_cast
    ring
  · have h := B.mul_mem (b0 * ∏ i ∈ Finset.univ.erase j, f i).2 (hf' j)
    rw [← Finset.mul_prod_erase Finset.univ f (Finset.mem_univ j)]
    convert h using 1
    push_cast
    ring

end OmLocAux

theorem UpperTheory.Gal.productCup_of_system.omLoc_of :
    OmLoc := by
  intro L _ _ B e q
  have hle : B ≤ loc B e := fun v hv => ⟨1, by simp, by simpa using hv⟩
  refine ⟨le_antisymm ?_ ?_, fun r hr m hm => omB_stab B q hr hm, fun B' h => omB_mono h q⟩
  · refine Submodule.span_le.2 ?_
    rintro v ⟨b, hb, hv⟩
    have hb0 : (b : L) ≠ 0 := fun h => hb (by rw [show b = 0 from Subtype.ext h, map_zero])
    have hinv : (b : L)⁻¹ ∈ loc B e := ⟨b, hb, by rw [mul_inv_cancel₀ hb0]; exact B.one_mem⟩
    have h := omB_stab (loc B e) q hinv (omB_mono hle q hv)
    rwa [smul_smul, inv_mul_cancel₀ hb0, one_smul] at h
  · refine Submodule.span_le.2 ?_
    rintro _ ⟨c, hc, v, hv, rfl⟩
    obtain ⟨b, hb, hbc, hbv⟩ := common_den B e hc hv
    refine Submodule.subset_span ⟨b ^ (2 * q + 1), by rw [map_pow]; exact pow_ne_zero _ hb, ?_⟩
    have h1 := ιMulti_mem B q (fun j => ((b : L) ^ 2) • D ℂ L (v j)) fun j => two_mem B b.2 (hbv j)
    have h2 := omB_stab B q hbc h1
    rw [AlternatingMap.map_smul_univ, smul_smul, Finset.prod_const, Finset.card_univ,
      Fintype.card_fin] at h2
    convert h2 using 1
    rw [smul_smul]
    congr 1
    push_cast
    ring
