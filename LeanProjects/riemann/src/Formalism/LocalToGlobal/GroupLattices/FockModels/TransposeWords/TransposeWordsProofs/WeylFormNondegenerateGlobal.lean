import Formalism.LocalToGlobal.GroupLattices.FockModels.TransposeWords.DualWeylIn
import Formalism.ThetaLogCoordinates.SandwichModelDomains.FinalW
import Formalism.GradedWeylDivisibility.FockSpaceTableaux.LClosedeqLemmas
import Formalism.GradedWeylDivisibility.FockSpaceTableaux.ColSums
import Formalism.LocalToGlobal.GroupLattices.FockModels.TransposeWords.TransposeWordsProofs.ProdBlockEmbMonomial
import Formalism.LocalToGlobal.GroupLattices.FockModels.TransposeWords.TransposeWordsProofs.FockPairingDividedAdjoint
import Formalism.LocalToGlobal.GroupLattices.FockModels.TransposeWords.TransposeWordsProofs.FockPairingRowAction
import Formalism.LocalToGlobal.GroupLattices.FockModels.TransposeWords.TransposeWordsProofs.FockPairingHighestWeightProof
import Formalism.LocalToGlobal.GroupLattices.FockModels.TransposeWords.TransposeWordsProofs.CwlApplyWordAppendSingle
import Formalism.LocalToGlobal.GroupLattices.FockModels.TransposeWords.TransposeWordsProofs.LowerTriangularOverField

open MvPolynomial

noncomputable section

namespace Formalism.L2.G.Model.TS

open Formalism.GradedWeylDivisibility Formalism.InvariantFactorPaths.INST

section bil

variable {σ R : Type} [CommRing R]

lemma tsc_add_left (hB : FockRBilin) (f f' g : MvPolynomial σ R) :
    fockR (f + f') g = fockR f g + fockR f' g := (hB σ R f f' g 0).1

lemma tsc_smul_left (hB : FockRBilin) (a : R) (f g : MvPolynomial σ R) :
    fockR (a • f) g = a * fockR f g := (hB σ R f 0 g a).2.1

lemma tsc_symm (hB : FockRBilin) (f g : MvPolynomial σ R) : fockR f g = fockR g f := (hB σ R f 0 g 0).2.2

lemma tsc_add_right (hB : FockRBilin) (f g g' : MvPolynomial σ R) :
    fockR f (g + g') = fockR f g + fockR f g' := by
  rw [tsc_symm hB f, tsc_add_left hB, tsc_symm hB g, tsc_symm hB g']

lemma tsc_smul_right (hB : FockRBilin) (a : R) (f g : MvPolynomial σ R) :
    fockR f (a • g) = a * fockR f g := by
  rw [tsc_symm hB f, tsc_smul_left hB, tsc_symm hB g]

lemma tsc_zero_left (hB : FockRBilin) (g : MvPolynomial σ R) : fockR (0 : MvPolynomial σ R) g = 0 := by
  have h := tsc_smul_left hB (0 : R) (0 : MvPolynomial σ R) g
  simpa using h

end bil

lemma tsc_toK_apply (O K : Type*) [CommRing O] [CommRing K] [Algebra O K] {σ : Type*} (f : MvPolynomial σ O) :
    toK O K f = map (algebraMap O K) f := rfl

lemma tsc_map_smul {O K : Type*} [CommRing O] [CommRing K] (φ : O →+* K) {σ : Type*} (a : O) (f : MvPolynomial σ O) :
    map φ (a • f) = φ a • map φ f := by
  rw [smul_eq_C_mul, smul_eq_C_mul, map_mul, map_C]

lemma tsc_eval_map {O K : Type*} [CommRing O] [CommRing K] (φ : O →+* K) {r n : ℕ}
    (f : MvPolynomial (Fin r × Fin n) O) :
    eval (idFrame K r n) (map φ f) = φ (eval (idFrame O r n) f) := by
  induction f using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp [hp, hq]
  | mul_X p v hp =>
    simp only [map_mul, hp, map_X, eval_X]
    congr 1
    unfold idFrame
    split_ifs <;> simp

lemma tsc_applyWord_mem {R : Type} [CommRing R] {r n : ℕ} (ν : Fin n → ℕ) (w : List (Fin r × Fin r × ℕ))
    (f : MvPolynomial (Fin r × Fin n) R) (hf : f ∈ dualWeyl R r n ν) : applyWord R w f ∈ dualWeyl R r n ν := by
  induction w with
  | nil => exact hf
  | cons x w ih =>
    rw [applyWord_cons]
    exact rowDivStable R r n ν _ _ _ _ ih

lemma tsc_transpose_transpose {r : ℕ} (w : List (Fin r × Fin r × ℕ)) : transposeWord (transposeWord w) = w := by
  simp [transposeWord, List.map_reverse, Function.comp_def]

lemma tsc_word_pair (hA : FockRWordAdj) (hH : FockPairingHighestWeight) {K : Type} [Field K] [CharZero K] {r n : ℕ} (hn : n ≤ r)
    (ν : Fin n → ℕ) (hν : Antitone ν) (w : List (Fin r × Fin r × ℕ)) (Q : MvPolynomial (Fin r × Fin n) K)
    (hQ : Q ∈ dualWeyl K r n ν) :
    fockR (applyWord K w (hw K hn ν)) Q =
      eval (idFrame K r n) (applyWord K (transposeWord w) Q) * fockR (hw K hn ν) (hw K hn ν) := by
  rw [hA K r n w, hH K r n hn ν hν _ (tsc_applyWord_mem ν _ Q hQ)]

lemma tsc_norm_ne (hN : HWNorm) (K : Type) [Field K] [CharZero K] {r n : ℕ} (hn : n ≤ r) (ν : Fin n → ℕ) :
    fockR (hw K hn ν) (hw K hn ν) ≠ 0 := by
  obtain ⟨N, hN0, hNK⟩ := hN r n hn ν
  rw [hNK K]
  exact_mod_cast hN0.ne'

lemma tsc_coeff_pair (hA : FockRWordAdj) (hH : FockPairingHighestWeight) (hC : CoeffWord) {K : Type} [Field K] [CharZero K] {r n : ℕ}
    (hn : n ≤ r) (ν : Fin n → ℕ) (hν : Antitone ν) (Q : MvPolynomial (Fin r × Fin n) K) (hQ : Q ∈ dualWeyl K r n ν)
    (e : Fin r × Fin n →₀ ℕ) (he : LowerTri e) :
    coeff e Q = 0 ∨ fockR (applyWord K (transposeWord (wordOf e)) (hw K hn ν)) Q =
      coeff e Q * fockR (hw K hn ν) (hw K hn ν) := by
  by_cases hcol : ∀ s : Fin n, ∑ a : Fin r, e (a, s) = ν s
  · right
    have h1 : IsWeightedHomogeneous (colW r n) Q ν := (mem_weightedHomogeneousSubmodule K _ _ _).1 hQ.1
    rw [tsc_word_pair hA hH hn ν hν _ Q hQ, tsc_transpose_transpose, hC K r n ν Q e h1 he hcol]
  · left
    by_contra h0
    exact hcol (columnSums_holds K r n ν Q hQ e (mem_support_iff.2 h0))

theorem weylPair_of (hB : FockRBilin) (hA : FockRWordAdj) (hH : FockPairingHighestWeight) : WeylPair := by
  intro O K _ _ _ _ _ _ r n hn ν hν P hP Q hQ
  obtain ⟨P0, hP0, rfl⟩ := hP
  obtain ⟨Q0, hQ0, rfl⟩ := hQ
  rw [tsc_toK_apply, tsc_toK_apply]
  have hQK : map (algebraMap O K) Q0 ∈ dualWeyl K r n ν := dualWeylMap O K _ r n ν Q0 hQ0
  have hP1 : P0 ∈ Submodule.span O (Set.range fun w : List (Fin r × Fin r × ℕ) => applyWord O w (hw O hn ν)) := hP0
  clear hP0
  induction hP1 using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨w, rfl⟩ := hx
    refine ⟨eval (idFrame O r n) (applyWord O (transposeWord w) Q0), ?_⟩
    rw [← lclosedeq_applyWord_map, lclosedeq_hw_map, tsc_word_pair hA hH hn ν hν w _ hQK,
      lclosedeq_applyWord_map, tsc_eval_map]
  | zero => exact ⟨0, by rw [map_zero, map_zero, tsc_zero_left hB, zero_mul]⟩
  | add x y _ _ hx hy =>
    obtain ⟨a, ha⟩ := hx
    obtain ⟨b, hb⟩ := hy
    exact ⟨a + b, by rw [map_add, tsc_add_left hB, ha, hb, map_add, add_mul]⟩
  | smul a x _ hx =>
    obtain ⟨z, hz⟩ := hx
    exact ⟨a * z, by rw [tsc_map_smul, tsc_smul_left hB, hz, map_mul, mul_assoc]⟩

theorem dualWeylIn_of (hA : FockRWordAdj) (hH : FockPairingHighestWeight) (hN : HWNorm) (hC : CoeffWord) (hL : LowerTriK) :
    DualWeylIn := by
  intro O K _ _ _ _ _ _ r n hn ν hν Q hQ H
  refine (hL O K r n ν Q hQ).1 fun e he => ?_
  have hc := tsc_norm_ne hN K hn ν
  rcases tsc_coeff_pair hA hH hC hn ν hν Q hQ e he with h0 | h1
  · exact ⟨0, by rw [map_zero, h0]⟩
  · obtain ⟨z, hz⟩ := H (toK O K (applyWord O (transposeWord (wordOf e)) (hw O hn ν)))
      (Submodule.mem_map_of_mem (Submodule.subset_span ⟨_, rfl⟩))
    rw [tsc_toK_apply, ← lclosedeq_applyWord_map, lclosedeq_hw_map, h1] at hz
    exact ⟨z, (mul_right_cancel₀ hc hz).symm⟩

theorem nondegK_of (hA : FockRWordAdj) (hH : FockPairingHighestWeight) (hN : HWNorm) (hC : CoeffWord) (hL : LowerTriK) :
    NondegK := by
  intro K _ _ r n hn ν hν Q hQ H
  refine (hL K K r n ν Q hQ).2 fun e he => ?_
  have hc := tsc_norm_ne hN K hn ν
  rcases tsc_coeff_pair hA hH hC hn ν hν Q hQ e he with h0 | h1
  · exact h0
  · rw [H _ (tsc_applyWord_mem ν _ _ (hwMem K r n hn ν hν))] at h1
    exact (mul_eq_zero.1 h1.symm).resolve_right hc

def tscForm (hB : FockRBilin) {K σ : Type} [Field K] (c : K) : MvPolynomial σ K →ₗ[K] MvPolynomial σ K →ₗ[K] K :=
  LinearMap.mk₂ K (fun P Q => c⁻¹ * fockR P Q)
    (fun P P' Q => by rw [tsc_add_left hB, mul_add])
    (fun a P Q => by rw [tsc_smul_left hB, smul_eq_mul, mul_left_comm])
    (fun P Q Q' => by rw [tsc_add_right hB, mul_add])
    (fun a P Q => by rw [tsc_smul_right hB, smul_eq_mul, mul_left_comm])

lemma tscForm_apply (hB : FockRBilin) {K σ : Type} [Field K] (c : K) (P Q : MvPolynomial σ K) :
    tscForm hB c P Q = c⁻¹ * fockR P Q := rfl

lemma tsc_range_iff {O K : Type} [CommRing O] [Field K] [Algebra O K] {c : K} (hc : c ≠ 0) (x : K) :
    c⁻¹ * x ∈ Set.range (algebraMap O K) ↔ ∃ z : O, x = algebraMap O K z * c := by
  constructor
  · rintro ⟨z, hz⟩
    exact ⟨z, by rw [hz]; field_simp⟩
  · rintro ⟨z, rfl⟩
    exact ⟨z, by field_simp⟩

lemma tsc_zero_weight {O : Type} [CommRing O] {r n : ℕ} (hn : n ≤ r) (ν : Fin n → ℕ) (h0 : ∀ t, ν t = 0) :
    dualWeyl O r n ν ≤ weyl O r n hn ν := by
  intro P hP
  have hhw : hw O hn ν = 1 := by
    unfold hw
    refine Finset.prod_eq_one fun s _ => ?_
    rw [h0 s, Nat.zero_sub, pow_zero]
  have hPc : P = C (coeff 0 P) := by
    ext m
    rw [coeff_C]
    split_ifs with hm
    · rw [hm]
    · by_contra hne
      apply hm
      have hs := columnSums_holds O r n ν P hP m (mem_support_iff.2 hne)
      ext ⟨a, t⟩
      have h1 := hs t
      rw [h0 t] at h1
      have h2 := (Finset.sum_eq_zero_iff.1 h1) a (Finset.mem_univ a)
      simpa using h2.symm
  have h1 : (1 : MvPolynomial (Fin r × Fin n) O) ∈ weyl O r n hn ν :=
    Submodule.subset_span ⟨[], hhw⟩
  rw [hPc, ← mul_one (C (coeff 0 P)), ← smul_eq_C_mul]
  exact Submodule.smul_mem _ _ h1

theorem formCoreG_of (hB : FockRBilin) (hR : FockRRowAct) (hN : HWNorm) (hW : WeylPair) (hD : DualWeylIn)
    (hG : NondegK) : FormCoreG := by
  intro p _ O K _ _ _ _ _ _ _ hp r n hn ν hν
  have hc := tsc_norm_ne hN K hn ν
  refine ⟨tscForm hB (fockR (hw K hn ν) (hw K hn ν)), ?_, ?_, ?_, ?_, ?_⟩
  · intro g P Q
    rw [tscForm_apply, tscForm_apply, hR K r n g P Q]
  · intro Q hQ H
    refine hG K r n hn ν hν Q hQ fun P hP => ?_
    have h := H P hP
    rw [tscForm_apply] at h
    exact (mul_eq_zero.1 h).resolve_left (inv_ne_zero hc)
  · intro Q hQ H
    refine hD O K r n hn ν hν Q hQ fun P hP => ?_
    have h := H P (Submodule.map_mono (weylLeDual O r n hn ν hν) hP)
    rw [tscForm_apply] at h
    exact (tsc_range_iff hc _).1 h
  · intro l hl Q hQ P hP
    obtain ⟨Q0, hQ0, rfl⟩ := hQ
    have hs := (Top.sandwichLocal p r n hn ν hν l hl O hp).1 Q0 hQ0
    have he : ((p : K) ^ sExp p r l) • toK O K Q0 = toK O K (((p : O) ^ sExp p r l) • Q0) := by
      rw [tsc_toK_apply, tsc_toK_apply, tsc_map_smul, map_pow, map_natCast]
    rw [tscForm_apply, he, tsc_symm hB P]
    exact (tsc_range_iff hc _).2 (hW O K r n hn ν hν _ (Submodule.mem_map_of_mem hs) P hP)
  · intro h0 Q hQ P hP
    rw [tscForm_apply]
    exact (tsc_range_iff hc _).2
      (hW O K r n hn ν hν P (Submodule.map_mono (tsc_zero_weight hn ν h0) hP) Q hQ)

theorem weyl_pairing : WeylPair := weylPair_of fock_pairing_bilinear fock_pairing_word_adjoint fock_pairing_highest_weight_proof

theorem dual_weyl_inclusion : DualWeylIn :=
  dualWeylIn_of fock_pairing_word_adjoint fock_pairing_highest_weight_proof highest_weight_norm coeffWord' lower_triangular_over_field

theorem nondegenerate_over_field : NondegK :=
  nondegK_of fock_pairing_word_adjoint fock_pairing_highest_weight_proof highest_weight_norm coeffWord' lower_triangular_over_field

theorem weyl_form_nondegenerate_global : FormCoreG :=
  formCoreG_of fock_pairing_bilinear fock_pairing_row_action highest_weight_norm weyl_pairing dual_weyl_inclusion nondegenerate_over_field

end Formalism.L2.G.Model.TS
