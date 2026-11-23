import Formalism.LocalToGlobal.GlobalTheory.GL6.PBwLocGlob
import Formalism.LocalToGlobal.GlobalTheory.GL6.PBwLocElim

noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.LocalLatticeBases

open Formalism.BasicNotions Formalism.MainNotions.product_first_zeroth_parts Formalism.L2.Forms NumberField Classical
open scoped Matrix

theorem substitution_one {ι : Type} {n : ℕ} (P : MvPolynomial (ι × Fin n × Fin n) ℂ) :
    subP (fun _ => (1 : Matrix (Fin n) (Fin n) ℂ)) P = P := by
  have h : (subP (fun _ : ι => (1 : Matrix (Fin n) (Fin n) ℂ)) :
      MvPolynomial (ι × Fin n × Fin n) ℂ →ₐ[ℂ] MvPolynomial (ι × Fin n × Fin n) ℂ) = AlgHom.id ℂ _ := by
    apply MvPolynomial.algHom_ext
    intro x
    simp [subP, Matrix.one_apply]
  rw [h]
  rfl

theorem substitution_substitution {ι : Type} {n : ℕ} (o o' : ι → Matrix (Fin n) (Fin n) ℂ) (P : MvPolynomial (ι × Fin n × Fin n) ℂ) :
    subP o (subP o' P) = subP (fun τ => o' τ * o τ) P := by
  have h : (subP o).comp (subP o') = subP (fun τ => o' τ * o τ) := by
    apply MvPolynomial.algHom_ext
    intro x
    simp only [AlgHom.comp_apply, subP, MvPolynomial.aeval_X, map_sum, map_mul, MvPolynomial.aeval_C,
      MvPolynomial.algebraMap_eq, Matrix.mul_apply, Finset.mul_sum, Finset.sum_mul, mul_assoc]
    rw [Finset.sum_comm]
  show ((subP o).comp (subP o')) P = _
  rw [h]

variable (D : D7)

def BwGLStab (w : D.what₂.places.Pl) : Prop :=
  ∀ (n : ℕ) (ν : DomWeight n) (s : ℤ) (M M' : Matrix (Fin n) (Fin n) ℂ), M * M' = 1 →
    (∀ a b, M a b ∈ bwA_Ow D w) → (∀ a b, M' a b ∈ bwA_Ow D w) →
    ∀ g ∈ delSq ℤ n ν, M.det ^ s • Formalism.GradedWeylDivisibility.rowAct ℂ M (MvPolynomial.map (Int.castRingHom ℂ) g) ∈
      bwA_span (bwA_Ow D w) le_rfl ν.natW

theorem bwG_intSpan_allSubP (w : D.what₂.places.Pl) {n : ℕ} (lam : D.what₂.Tau → DomWeight n)
    (N : D.what₂.Tau → Matrix (Fin n) (Fin n) ℂ) (s : D.what₂.Tau → ℤ)
    (hB : ∀ τ, ∀ g ∈ delSq ℤ n (lam τ), (N τ).det ^ s τ • Formalism.GradedWeylDivisibility.rowAct ℂ (N τ) (MvPolynomial.map (Int.castRingHom ℂ) g) ∈
      bwA_span (bwA_Ow D w) le_rfl (lam τ).natW)
    (Q : MvPolynomial (D.what₂.Tau × Fin n × Fin n) ℂ) (hQ : Q ∈ Formalism.L2.Forms.IntSpan D w lam) :
    MvPolynomial.C (∏ τ, (N τ).det ^ s τ) * subP N Q ∈ Formalism.L2.Forms.IntSpan D w lam := by
  have key : ∀ S : Finset D.what₂.Tau, MvPolynomial.C (∏ τ ∈ S, (N τ).det ^ s τ) *
      subP (fun τ => if τ ∈ S then N τ else 1) Q ∈ Formalism.L2.Forms.IntSpan D w lam := by
    intro S
    induction S using Finset.induction_on with
    | empty =>
      simp only [Finset.prod_empty, map_one, one_mul, Finset.notMem_empty, if_false]
      rw [substitution_one]
      exact hQ
    | insert τ0 S h0 ih =>
      set U : D.what₂.Tau → Matrix (Fin n) (Fin n) ℂ := Function.update 1 τ0 (N τ0) with hU
      have hU1 : ∀ τ, τ ≠ τ0 → U τ = 1 := fun τ hτ => by rw [hU, Function.update_of_ne hτ]; rfl
      have hUτ : U τ0 = N τ0 := by rw [hU, Function.update_self]
      have hcomp : (fun τ => (if τ ∈ S then N τ else 1) * U τ) = fun τ => if τ ∈ insert τ0 S then N τ else 1 := by
        funext τ
        by_cases hτ : τ = τ0
        · subst hτ
          rw [if_neg h0, if_pos (Finset.mem_insert_self _ _), one_mul, hUτ]
        · rw [hU1 τ hτ, mul_one]
          by_cases hS : τ ∈ S
          · rw [if_pos hS, if_pos (Finset.mem_insert_of_mem hS)]
          · rw [if_neg hS, if_neg (by simp [hτ, hS])]
      have e : MvPolynomial.C (∏ τ ∈ insert τ0 S, (N τ).det ^ s τ) *
          subP (fun τ => if τ ∈ insert τ0 S then N τ else 1) Q =
          (N τ0).det ^ s τ0 • subP U (MvPolynomial.C (∏ τ ∈ S, (N τ).det ^ s τ) *
            subP (fun τ => if τ ∈ S then N τ else 1) Q) := by
        have hC : ∀ x, subP U (MvPolynomial.C x) = MvPolynomial.C x := fun x => by
          rw [← MvPolynomial.algebraMap_eq, AlgHom.commutes]
        rw [map_mul, substitution_substitution, hcomp, Finset.prod_insert h0, map_mul, MvPolynomial.smul_eq_C_mul, hC, mul_assoc]
      rw [e]
      refine bwA_intSpan_subP D w lam τ0 U hU1 _ ?_ _ ih
      intro g hg
      rw [hUτ]
      exact hB τ0 g hg
  have h := key Finset.univ
  simp only [Finset.mem_univ, if_true] at h
  exact h

theorem local_GL_stabilises_lattice (w : D.what₂.places.Pl) : BwGLStab D w := by
  intro n ν s M M' hMM' hM hM' g hg
  have hM'M : M' * M = 1 := mul_eq_one_comm.1 hMM'
  have hEO : M ∈ bwA_EO (bwA_Ow D w) n := bwE_elim (bwE_loc_Ow D w) M hM ⟨M', hM', hM'M⟩
  have hg' : MvPolynomial.map (Int.castRingHom ℂ) g ∈ bwA_span (bwA_Ow D w) le_rfl ν.natW :=
    Submodule.subset_span ⟨g, hg, rfl⟩
  have hrow := bwA_span_closure (bwA_Ow D w) le_rfl ν.natW M hEO _ hg'
  have hdet : M.det * M'.det = 1 := by rw [← Matrix.det_mul, hMM', Matrix.det_one]
  have hdM : M.det ∈ bwA_Ow D w := bwE_det_mem hM
  have hdM' : M'.det ∈ bwA_Ow D w := bwE_det_mem hM'
  have hds : M.det ^ s ∈ bwA_Ow D w := by
    rcases s with k | k
    · rw [Int.ofNat_eq_natCast, zpow_natCast]
      exact pow_mem hdM k
    · have e : M.det ^ (Int.negSucc k) = M'.det ^ (k + 1) := by
        rw [zpow_negSucc, ← inv_pow]
        congr 1
        exact inv_eq_of_mul_eq_one_right hdet
      rw [e]
      exact pow_mem hdM' _
  have e : M.det ^ s • Formalism.GradedWeylDivisibility.rowAct ℂ M (MvPolynomial.map (Int.castRingHom ℂ) g) =
      (⟨M.det ^ s, hds⟩ : bwA_Ow D w) • Formalism.GradedWeylDivisibility.rowAct ℂ M (MvPolynomial.map (Int.castRingHom ℂ) g) := rfl
  rw [e]
  exact Submodule.smul_mem _ _ hrow

variable (u : D.what₂.Word)

theorem bwG_change_mem (w : D.what₂.places.Pl) (hw : OverT D u w) (τ : D.what₂.Tau) {n : ℕ}
    {L : Set (Fin n → D.host.E)} {B B₂ : GL (Fin n) D.host.E}
    (hB : IsLocBasis (D.mem u).A.T L B) (hB₂ : IsLocBasis (D.mem u).A.T L B₂) (a b : Fin n) :
    atInf (embT D) ((B₂⁻¹ * B : GL (Fin n) D.host.E) : Matrix (Fin n) (Fin n) D.host.E) τ a b ∈ bwA_Ow D w := by
  obtain ⟨s, hs, hx⟩ := bwE_col_loc D u w hw hB b
  have h := bwE_locBasis_int D u w hw τ hB₂ _ s hs hx a
  rw [bwE_mulVec_col, ← Units.val_mul] at h
  exact h

theorem bwBasisInd_of_stab (Tt : FormsTied D u) (hS : ∀ w, OverT D u w → BwGLStab D w) : BwBasisInd D u Tt := by
  intro w hw i hi c B B₂ hB hB₂ Q hQ
  set N : D.what₂.Tau → Matrix (Fin (D.R.N i)) (Fin (D.R.N i)) ℂ :=
    fun τ => atInf (embT D) ((B⁻¹ * B₂ : GL (Fin (D.R.N i)) D.host.E) : Matrix (Fin (D.R.N i)) (Fin (D.R.N i)) D.host.E) τ
    with hN
  set N' : D.what₂.Tau → Matrix (Fin (D.R.N i)) (Fin (D.R.N i)) ℂ :=
    fun τ => atInf (embT D) ((B₂⁻¹ * B : GL (Fin (D.R.N i)) D.host.E) : Matrix (Fin (D.R.N i)) (Fin (D.R.N i)) D.host.E) τ
    with hN'
  have hNN' : ∀ τ, N τ * N' τ = 1 := fun τ => by
    simp only [hN, hN', atInf]
    rw [← Matrix.map_mul, ← Units.val_mul]
    have : (B⁻¹ * B₂ * (B₂⁻¹ * B) : GL (Fin (D.R.N i)) D.host.E) = 1 := by group
    rw [this, Units.val_one, Matrix.map_one _ (map_zero _) (map_one _)]
  refine ⟨MvPolynomial.C (∏ τ, (N τ).det ^ shiftOf (lamT u i) τ) * subP N Q,
    bwG_intSpan_allSubP D w _ N _ (fun τ g hg => hS w hw _ _ _ (N τ) (N' τ) (hNN' τ)
      (bwG_change_mem D u w hw τ hB₂ hB) (bwG_change_mem D u w hw τ hB hB₂) g hg) Q hQ, fun z => ?_⟩
  rw [← fnOf_mul]
  have hM : atInf (embT D) ((B⁻¹ : GL (Fin (D.R.N i)) D.host.E) : Matrix (Fin (D.R.N i)) (Fin (D.R.N i)) D.host.E) =
      fun τ => N τ * atInf (embT D) ((B₂⁻¹ : GL (Fin (D.R.N i)) D.host.E) : Matrix (Fin (D.R.N i)) (Fin (D.R.N i)) D.host.E) τ := by
    funext τ
    simp only [hN, atInf]
    rw [← Matrix.map_mul, ← Units.val_mul]
    congr 2
    group
  rw [hM]

theorem local_global_lattice_of_compatible_forms (Tt : FormsTied D u) : BwLocGlob D u Tt := bwLocGlob_of_ind (D := D) (u := u) Tt (bwBasisInd_of_stab D u Tt (fun w _ => local_GL_stabilises_lattice D w))

theorem bwLocGlob_all : ∀ (D : D7) (u : D.what₂.Word) (Tt : FormsTied D u), BwLocGlob D u Tt := fun D u Tt => local_global_lattice_of_compatible_forms D u Tt

theorem lattice_inclusion_of_decomp
    (h2 : ∀ (D : D7) (u : D.what₂.Word) (Tt : FormsTied D u), BwDecomp D u Tt) : WeightLatticeInclusionFamily := lattice_inclusion_of_decomp_glob (fun D u Tt => local_bases_exist_of_compatible_forms (D := D) (u := u) Tt) h2
    (fun D u Tt => local_global_lattice_of_compatible_forms D u Tt)

theorem local_bases_exist_all : ∀ (D : D7) (u : D.what₂.Word) (Tt : FormsTied D u), BwLocBases D u Tt := fun D u Tt => local_bases_exist_of_compatible_forms (D := D) (u := u) Tt

theorem local_global_lattice_all : ∀ (D : D7) (u : D.what₂.Word) (Tt : FormsTied D u), BwLocGlob D u Tt := fun D u Tt => local_global_lattice_of_compatible_forms D u Tt

end Formalism.L2.GlobalTheoryTheory.LocalLatticeBases
