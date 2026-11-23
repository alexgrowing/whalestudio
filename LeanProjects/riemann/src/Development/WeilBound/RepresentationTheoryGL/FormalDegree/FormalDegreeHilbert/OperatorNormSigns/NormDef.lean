import Development.WeilBound.RepresentationTheoryGL.FormalDegree.FormalDegreeHilbert.HlamStable
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.IntMuCD
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.RhoNSubNab
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.KSchur
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.HaarMirror
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.ToMKMulInv

noncomputable section

open Finset MeasureTheory Matrix
open scoped InnerProductSpace

namespace PositivityTheory.RgFd

open ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7

variable {n : ℕ}

theorem nd_const_sign {ε : Fin n → Bool} (hq : q0 ε = 0) : ∃ s : Bool, ∀ a, ε a = s := by
  unfold q0 at hq
  rcases Nat.min_eq_zero_iff.1 hq with h | h
  · refine ⟨false, fun a => ?_⟩
    unfold pOf at h
    have := Finset.filter_eq_empty_iff.1 (Finset.card_eq_zero.1 h) (Finset.mem_univ a)
    simpa using this
  · refine ⟨true, fun a => ?_⟩
    unfold qOf at h
    have := Finset.filter_eq_empty_iff.1 (Finset.card_eq_zero.1 h) (Finset.mem_univ a)
    simpa using this

theorem nd_Jm {ε : Fin n → Bool} {s : Bool} (hs : ∀ a, ε a = s) :
    Jm ε = (if s then (1 : ℂ) else -1) • (1 : Matrix (Fin n) (Fin n) ℂ) := by
  ext i j
  by_cases h : i = j
  · subst h; simp [Jm, hs]
  · simp [Jm, h]

theorem nd_mem_Kset {ε : Fin n → Bool} (hq : q0 ε = 0) {g : Matrix (Fin n) (Fin n) ℂ} (hg : inUJ ε g) :
    g ∈ Kset ε := by
  obtain ⟨s, hs⟩ := nd_const_sign hq
  set c : ℂ := if s then 1 else -1 with hc
  have hc0 : c ≠ 0 := by simp only [hc]; split_ifs <;> norm_num
  have hJ := nd_Jm hs
  rw [← hc] at hJ
  have hg' : gᴴ * Jm ε * g = Jm ε := hg
  rw [hJ, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul] at hg'
  have hu : gᴴ * g = 1 := smul_right_injective _ hc0 hg'
  refine ⟨Matrix.mem_unitaryGroup_iff'.2 (by rw [star_eq_conjTranspose]; exact hu), ?_⟩
  rw [hJ, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, Matrix.one_mul]

theorem nd_hsOp_op {ε : Fin n → Bool} {Λ : Fin n → ℝ} (T : KType ε Λ) (k : KG ε) :
    hsOp (T.op k) = (Module.finrank ℂ T.V : ℝ) := by
  have hn : ∀ v : T.V, ‖T.op k v‖ = ‖v‖ := by
    intro v
    have hU := (T.τ k).2
    have h1 : star (T.op k) * T.op k = 1 := hU.1
    have h2 : ⟪T.op k v, T.op k v⟫_ℂ = ⟪v, v⟫_ℂ := by
      rw [← ContinuousLinearMap.adjoint_inner_right, ← ContinuousLinearMap.mul_apply,
        ← ContinuousLinearMap.star_eq_adjoint, h1, ContinuousLinearMap.one_apply]
    rw [inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K] at h2
    have h3 : ‖T.op k v‖ ^ 2 = ‖v‖ ^ 2 := by exact_mod_cast h2
    exact (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 h3
  unfold hsOp
  simp only [hn, (stdOrthonormalBasis ℂ T.V).orthonormal.1, one_pow, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul, mul_one]

theorem nd_psiM_K {ε : Fin n → Bool} {Λ : Fin n → ℝ} (T : KType ε Λ) (μ : Fin n → ℤ) (k : KG ε) :
    PsiM T μ (toMK k) = T.op k := by
  have h1 : inUJ ε (1 : Matrix (Fin n) (Fin n) ℂ) := by simp [inUJ]
  have e := psiM_equiv T μ k 1 h1
  rw [show toMK (1 : KG ε) = 1 from rfl, Matrix.mul_one, Matrix.mul_one, psiM_one] at e
  rw [e]
  simp [KType.op, map_one]

theorem nd_pev_zero {ε : Fin n → Bool} {s : Bool} (hs : ∀ a, ε a = s) (z : PCoord ε → ℂ) : pev z = 0 := by
  have h0 : pmat z = 0 := by
    ext a b
    simp [pmat, hs]
  exact (pmat_isHermitian z).eigenvalues_eq_zero_iff.2 h0

theorem nd_jac_one {ε : Fin n → Bool} {s : Bool} (hs : ∀ a, ε a = s) (z : PCoord ε → ℂ) : Jac z = 1 := by
  unfold Jac
  refine Finset.prod_eq_one fun a _ => Finset.prod_eq_one fun b _ => ?_
  rw [nd_pev_zero hs z]
  simp [shc]

theorem nd_isEmpty {ε : Fin n → Bool} {s : Bool} (hs : ∀ a, ε a = s) : IsEmpty (PCoord ε) :=
  ⟨fun ab => ab.2.2 (by rw [hs, hs])⟩

theorem nd_counts {ε : Fin n → Bool} (hq : q0 ε = 0) :
    (pOf ε = n ∧ qOf ε = 0) ∨ (pOf ε = 0 ∧ qOf ε = n) := by
  obtain ⟨s, hs⟩ := nd_const_sign hq
  cases s
  · right
    refine ⟨?_, ?_⟩
    · unfold pOf; simp [hs]
    · unfold qOf; simp [hs]
  · left
    refine ⟨?_, ?_⟩
    · unfold pOf; simp [hs]
    · unfold qOf; simp [hs]

theorem nd_cPQ {ε : Fin n → Bool} (hq : q0 ε = 0) : cPQ ε = 1 := by
  unfold cPQ
  have hpos : 0 < ∏ i ∈ range n, (i.factorial : ℝ) :=
    Finset.prod_pos fun i _ => by exact_mod_cast Nat.factorial_pos i
  rcases nd_counts hq with ⟨hp, hq'⟩ | ⟨hp, hq'⟩ <;> rw [hp, hq'] <;> simp [hpos.ne']

theorem nd_muCD_univ {ε : Fin n → Bool} (hq : q0 ε = 0) : muCD ε Set.univ = 1 := by
  obtain ⟨s, hs⟩ := nd_const_sign hq
  have := nd_isEmpty hs
  have h := lintegral_muCD ε (fun _ => 1) measurable_const
  rw [lintegral_one] at h
  rw [h, nd_cPQ hq, ENNReal.ofReal_one, one_mul]
  have hz : ∫⁻ z : PCoord ε → ℂ, ENNReal.ofReal (Jac z) = 1 := by
    simp only [nd_jac_one hs, ENNReal.ofReal_one, lintegral_one]
    rw [MeasureTheory.volume_pi, Measure.pi_of_empty]
    simp
  simp only [one_mul, hz, lintegral_one, measure_univ]

theorem nd_finrank {ε : Fin n → Bool} (hq : q0 ε = 0) {lam : Fin n → ℝ} (hl : StrictAnti lam)
    (T : KType ε (lowK ε lam)) : (Module.finrank ℂ T.V : ℝ) = dimVlam lam := by
  obtain ⟨s, hs⟩ := nd_const_sign hq
  rw [lemma7 T, dimVlam, prod_pairs_eq_factorial]
  have hden : (∏ i ∈ range (pOf ε), (i.factorial : ℝ)) * ∏ i ∈ range (qOf ε), (i.factorial : ℝ) =
      ∏ i ∈ range n, (i.factorial : ℝ) := by
    rcases nd_counts hq with ⟨hp, hq'⟩ | ⟨hp, hq'⟩ <;> rw [hp, hq'] <;> simp
  rw [hden]
  congr 1
  refine Finset.prod_congr rfl fun a _ => ?_
  have hf : (univ.filter fun b : Fin n => a < b ∧ ε a = ε b) = univ.filter fun b : Fin n => a < b := by
    ext b; simp [hs]
  rw [hf]
  refine Finset.prod_congr rfl fun b hb => ?_
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hb
  have hn : nab ε a b = 0 := by
    unfold nab
    simp [hs]
  rw [hn, Nat.cast_zero, add_zero, abs_of_pos (sub_pos.2 (hl hb))]

theorem normDef : NormDef := by
  intro n ε hq lam hl T μ hμ
  have hK : ∀ g : Formalism.REAL.UJ ε, hsOp (PsiM T μ (Formalism.MainNotions.S.umat g)) = (Module.finrank ℂ T.V : ℝ) := by
    intro g
    have hg : inUJ ε (Formalism.MainNotions.S.umat g) := by
      have h := g.2
      unfold inUJ Jm
      exact h
    obtain ⟨u, hu⟩ := exists_toMK (nd_mem_Kset hq hg)
    rw [← hu, nd_psiM_K, nd_hsOp_op]
  simp only [hK, lintegral_const, nd_muCD_univ hq, mul_one]
  rw [← nd_finrank hq hl.1 T]
  congr 1
  have hpos : (0 : ℝ) < Module.finrank ℂ T.V := by
    have : Nontrivial T.V := ⟨⟨T.w, 0, fun h => by simpa [h] using T.w_norm⟩⟩
    exact_mod_cast Module.finrank_pos
  field_simp

end PositivityTheory.RgFd
