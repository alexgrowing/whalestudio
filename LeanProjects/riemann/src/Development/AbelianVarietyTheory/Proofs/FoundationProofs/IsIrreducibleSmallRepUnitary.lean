import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.PublishedFoundations.FiniteIntertwining
import Formalism.BranchSandwichDivisors.DivFromPassageAndNorm
import Formalism.LocalToGlobal.Columns.PolyFn
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RowActCoefPolyAndUnitaryDense

open MvPolynomial Formalism.BasicNotions Formalism.GradedWeylDivisibility GlobalTheory.Branching
open Formalism.MainNotions.PrimeDegreeVariant (embGL Interlace)
open scoped DirectSum

namespace GlobalTheory.Branching

theorem rowAct_mem_of_unitary_stable {n k : ℕ} (M : Submodule ℂ (MvPolynomial (Fin n × Fin k) ℂ))
    (hM : ∀ u ∈ Matrix.unitaryGroup (Fin n) ℂ, ∀ f ∈ M, rowAct ℂ u f ∈ M)
    (g : Matrix (Fin n) (Fin n) ℂ) (f : MvPolynomial (Fin n × Fin k) ℂ) (hf : f ∈ M) : rowAct ℂ g f ∈ M := by
  rw [← Subspace.forall_mem_dualAnnihilator_apply_eq_zero_iff]
  intro l hl
  obtain ⟨P, hP⟩ := exists_poly_rowAct_coef n k f l
  have h0 : P = 0 := eq_zero_of_vanish_unitaryGroup n P fun u hu => by
    rw [← hP]
    exact (Submodule.mem_dualAnnihilator l).1 hl _ (hM u hu f hf)
  rw [hP, h0, map_zero]

theorem rowDivClosed_of_rowAct_stable {n k : ℕ} (M : Submodule ℂ (MvPolynomial (Fin n × Fin k) ℂ))
    (hM : ∀ (g : Matrix (Fin n) (Fin n) ℂ), ∀ f ∈ M, rowAct ℂ g f ∈ M) : RowDivClosed M := by
  intro a b j p hp
  rw [← Subspace.forall_mem_dualAnnihilator_apply_eq_zero_iff]
  intro l hl
  set N := (rowGen ℂ a b p).natDegree + j + 1 with hN
  have h1 : (rowGen ℂ a b p).natDegree < N := by omega
  have hk : j ∈ Finset.range N := Finset.mem_range.mpr (by omega)
  set P : Polynomial ℂ := ∑ i ∈ Finset.range N, Polynomial.monomial i (l (rowDiv ℂ a b i p)) with hP
  have hP0 : P = 0 := by
    apply Polynomial.funext
    intro c
    simp only [hP, Polynomial.eval_finsetSum, Polynomial.eval_monomial, Polynomial.eval_zero]
    have e := (Submodule.mem_dualAnnihilator l).1 hl _ (hM (lfockq_mat a b c) p hp)
    rw [← lfockq_eval_rowGen, lfockq_eval_C _ N h1, map_sum] at e
    rw [← e]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← smul_eq_C_mul, map_smul, smul_eq_mul, mul_comm]
    rfl
  have := congrArg (fun p => Polynomial.coeff p j) hP0
  simp only [hP, Polynomial.finsetSum_coeff, Polynomial.coeff_monomial, Finset.sum_ite_eq',
    if_pos hk, Polynomial.coeff_zero] at this
  exact this

theorem height_rowDiv_le {n k : ℕ} (H : ℤ) (a b : Fin n) (j : ℕ) (f : MvPolynomial (Fin n × Fin k) ℂ)
    (hf : ∀ d ∈ f.support, Finsupp.weight (lhwinHt n k) d ≤ H) :
    ∀ d ∈ (rowDiv ℂ a b j f).support, Finsupp.weight (lhwinHt n k) d ≤ H + j * ((a.val : ℤ) - b.val) := by
  intro e he
  have hs : rowDiv ℂ a b j f = ∑ d ∈ f.support, (rowGen ℂ a b (monomial d (coeff d f))).coeff j := by
    unfold rowDiv
    conv_lhs => rw [f.as_sum]
    rw [map_sum, Polynomial.finsetSum_coeff]
  rw [mem_support_iff, hs, coeff_sum] at he
  obtain ⟨d, hd, hne⟩ := Finset.exists_ne_zero_of_sum_ne_zero he
  have h1 := lhwinShift_rowGen_monomial ℂ a b d (coeff d f) j hne
  have h2 := hf d hd
  omega

theorem exists_killed_of_rowDivClosed {n k : ℕ} (M : Submodule ℂ (MvPolynomial (Fin n × Fin k) ℂ))
    (hM : RowDivClosed M) (hne : M ≠ ⊥) :
    ∃ v ∈ M, v ≠ 0 ∧ ∀ a b : Fin n, a < b → ∀ j : ℕ, 1 ≤ j → rowDiv ℂ a b j v = 0 := by
  classical
  have hex : ∃ N : ℕ, ∃ v ∈ M, v ≠ 0 ∧ ∀ d ∈ v.support, Finsupp.weight (lhwinHt n k) d ≤ (N : ℤ) := by
    obtain ⟨f, hfM, hf0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
    refine ⟨f.support.sup fun d => (Finsupp.weight (lhwinHt n k) d).toNat, f, hfM, hf0, fun d hd => ?_⟩
    have := Finset.le_sup (f := fun d => (Finsupp.weight (lhwinHt n k) d).toNat) hd
    have h2 : ((Finsupp.weight (lhwinHt n k) d).toNat : ℤ) ≤ _ := Int.ofNat_le.2 this
    exact (Int.self_le_toNat _).trans h2
  obtain ⟨v, hvM, hv0, hvH⟩ := Nat.find_spec hex
  refine ⟨v, hvM, hv0, fun a b hab j hj => ?_⟩
  by_contra hne'
  have hH := height_rowDiv_le _ a b j v hvH
  obtain ⟨d, hd⟩ := ne_zero_iff.mp hne'
  have hnn := (lhwin_weight_nonneg d).trans (hH d (mem_support_iff.2 hd))
  have hab' : (a.val : ℤ) < b.val := by exact_mod_cast (Fin.lt_def.mp hab)
  have hk' : (1 : ℤ) ≤ j := by exact_mod_cast hj
  have hlt : ((Nat.find hex : ℕ) : ℤ) + j * ((a.val : ℤ) - b.val) < (Nat.find hex : ℕ) := by
    nlinarith
  have hmin := Nat.find_min hex (m := (((Nat.find hex : ℕ) : ℤ) + j * ((a.val : ℤ) - b.val)).toNat)
    (by omega)
  apply hmin
  refine ⟨_, hM a b j v hvM, hne', ?_⟩
  rw [Int.toNat_of_nonneg hnn]
  exact hH

theorem dualWeyl_le_of_rowDivClosed {r n : ℕ} (hn : n ≤ r) (ν : Fin n → ℕ) (hν : Antitone ν)
    (M : Submodule ℂ (MvPolynomial (Fin r × Fin n) ℂ)) (hle : M ≤ dualWeyl ℂ r n ν) (hM : RowDivClosed M)
    (hne : M ≠ ⊥) : dualWeyl ℂ r n ν ≤ M := by
  obtain ⟨v, hvM, hv0, hkill⟩ := exists_killed_of_rowDivClosed M hM hne
  obtain ⟨c, hc⟩ := hwLine ℂ r n hn ν hν v (hle hvM) hkill
  have hc0 : c ≠ 0 := by
    rintro rfl
    exact hv0 (by simpa using hc)
  have e : hw ℂ hn ν = c⁻¹ • v := by
    rw [hc, smul_smul, inv_mul_cancel₀ hc0, one_smul]
  have hhw : hw ℂ hn ν ∈ M := e ▸ M.smul_mem _ hvM
  refine (Formalism.BranchingDeterminantCap.bs_dual_le_weyl hn ν hν).trans ?_
  unfold weyl
  rw [Submodule.span_le]
  rintro _ ⟨w, rfl⟩
  induction w with
  | nil => exact hhw
  | cons x w ih => exact hM _ _ _ _ ih

theorem isIrreducible_smallRep_unitary (n : ℕ) (mu : DomWeight n) :
    (smallRep (unitaryIncl n) mu).IsIrreducible := by
  have hnt : Nontrivial (Subrepresentation (smallRep (unitaryIncl n) mu)) :=
    ⟨⊥, ⊤, fun e => bot_ne_top (congrArg Subrepresentation.toSubmodule e)⟩
  refine ⟨fun S => ?_⟩
  by_cases hS : S.toSubmodule = ⊥
  · exact Or.inl (Subrepresentation.ext hS)
  refine Or.inr (Subrepresentation.ext ?_)
  let M : Submodule ℂ (MvPolynomial (Fin n × Fin n) ℂ) := S.toSubmodule.map (nablaSq ℂ n mu).subtype
  have hU : ∀ u ∈ Matrix.unitaryGroup (Fin n) ℂ, ∀ f ∈ M, rowAct ℂ u f ∈ M := by
    rintro u hu _ ⟨f, hf, rfl⟩
    let t : Matrix.unitaryGroup (Fin n) ℂ := Matrix.UnitaryGroup.transpose ⟨u, hu⟩
    have h1 : (smallRep (unitaryIncl n) mu t f : MvPolynomial (Fin n × Fin n) ℂ) ∈ M :=
      ⟨_, S.apply_mem_toSubmodule t hf, rfl⟩
    have h2 : (smallRep (unitaryIncl n) mu t f : MvPolynomial (Fin n × Fin n) ℂ) =
        detPow ℂ n (unitaryIncl n t) mu.detShift • rowAct ℂ u f := rfl
    rw [h2] at h1
    exact (M.smul_mem_iff (Units.ne_zero _)).1 h1
  have hcl := rowDivClosed_of_rowAct_stable M (rowAct_mem_of_unitary_stable M hU)
  have hne : M ≠ ⊥ := fun e => hS (Submodule.map_injective_of_injective (nablaSq ℂ n mu).injective_subtype
    (e.trans (Submodule.map_bot _).symm))
  have hle := dualWeyl_le_of_rowDivClosed le_rfl mu.natW (factNatW n mu).1 M
    (Submodule.map_subtype_le (nablaSq ℂ n mu) _) hcl hne
  refine eq_top_iff.2 fun f _ => ?_
  obtain ⟨g, hg, e⟩ := hle f.2
  rwa [← Subtype.ext e]

end GlobalTheory.Branching
