import Formalism.SharpRestriction.GrowthBounds.PlaneCoefficients.RestPlOf
import Formalism.SharpRestriction.GrowthBounds.PolynomialLevels.FrRevInj

noncomputable section

open MvPolynomial Finset Classical

namespace Formalism.MainNotions.PairMembershipBlocks

open Formalism.MainNotions.G Formalism.GradedWeylDivisibility Formalism.MainNotions.SourceCleaning Formalism.MainNotions.Pf14 Formalism.MainNotions.PlaneGramData Formalism.MainNotions.TestSideCounting Formalism.MainNotions.TestSideWords Formalism.MainNotions.Proposition5Numerics Formalism.MainNotions.TraceSpectra
open Formalism.MainNotions.G.WittFrameLocaliserOrders

namespace LkD

section MD

variable {ι : Type*} {n : ℕ}

theorem multideg_add (a b : ι × Fin n →₀ ℕ) (x : ι) : multideg (a + b) x = multideg a x + multideg b x := by
  simp [multideg, Finset.sum_add_distrib]

theorem multideg_zero (x : ι) : multideg (0 : ι × Fin n →₀ ℕ) x = 0 := by
  simp [multideg]

theorem multideg_smul (k : ℕ) (a : ι × Fin n →₀ ℕ) (x : ι) : multideg (k • a) x = k * multideg a x := by
  simp [multideg, Finset.mul_sum]

theorem multideg_single (v : ι × Fin n) (k : ℕ) (x : ι) :
    multideg (Finsupp.single v k) x = if v.1 = x then k else 0 := by
  unfold multideg
  by_cases h : v.1 = x
  · rw [if_pos h, Finset.sum_eq_single v.2]
    · have hv : v = (x, v.2) := by
        obtain ⟨v1, v2⟩ := v
        simp only at h
        rw [h]
      rw [Finsupp.single_apply, if_pos hv]
    · intro c _ hc
      rw [Finsupp.single_apply, if_neg]
      intro e
      exact hc (congrArg Prod.snd e).symm
    · intro h'
      exact absurd (Finset.mem_univ _) h'
  · rw [if_neg h]
    apply Finset.sum_eq_zero
    intro c _
    rw [Finsupp.single_apply, if_neg]
    intro e
    exact h (congrArg Prod.fst e)

end MD

theorem ne_pred {J : ℕ} (hJ : 2 ≤ J) (j : ZMod J) : j ≠ j - 1 := by
  intro h
  haveI : Fact (1 < J) := ⟨by omega⟩
  have h1 : (1 : ZMod J) = 0 := by linear_combination h
  exact one_ne_zero h1

section Phi

variable {p : ℕ} {n' r : ℕ} [NeZero n'] [NeZero r] {O : Type} [CommRing O] [IsDomain O]
  [IsDiscreteValuationRing O] {Fr : Frames n' r} {L₁ N₁ : ℕ} {J : ℕ} [NeZero J] (Dt : SignedChainData p O r J)

theorem ph_ll (j : ZMod J) (l : Fin (Dt.nL j)) (a : Fin r) :
    Dt.ph (X (ML.ll j l, a)) = monomial (Finsupp.single ((⟨j, Sum.inl l⟩ : TL J Dt.nL r), a) 1) 1 := by
  rw [SignedChainData.ph, aeval_X]
  rfl

theorem ph_lab (j : ZMod J) (m : Fin r) (a : Fin r) :
    Dt.ph (X (ML.lab j m, a)) = monomial (Finsupp.single ((⟨j, Sum.inr m⟩ : TL J Dt.nL r), a) 1) 1 := by
  rw [SignedChainData.ph, aeval_X]
  rfl

theorem ph_wc (j : ZMod J) (m : Fin r) (a : Fin r) :
    Dt.ph (X (ML.wc j m, a)) = monomial (Finsupp.single ((⟨j, Sum.inr m⟩ : TL J Dt.nL r), a) (Dt.P j m)) 1 := by
  rw [SignedChainData.ph, aeval_X]
  exact X_pow_eq_monomial

theorem PhiJ_X (j : ZMod J) (v : ℤ × Fin r) (hv : v.1 ∈ Fr.letters (segZ j)) :
    PhiJ Fr Dt j (X v) = Dt.ph (X (mlOf Fr Dt.nL j v.1, v.2)) := by
  rw [PhiJ, AlgHom.comp_apply, chi, aeval_X, if_pos hv]

theorem PhiJ_X_mon (hV : Fr.Valid L₁ N₁) (hnL : ∀ j, Dt.nL j = (Fr.LLset (segZ j)).card) (hJ : 2 ≤ J) (j : ZMod J)
    (v : ℤ × Fin r) (hv : v.1 ∈ Fr.letters (segZ j)) :
    ∃ e : TL J Dt.nL r × Fin r →₀ ℕ, PhiJ Fr Dt j (X v) = monomial e 1 ∧
      ∀ m' : Fin r, multideg e ⟨j - 1, Sum.inr m'⟩ =
        Dt.P (j - 1) m' * (if v.1 = Fr.fr (segZ j - 1) (r - 1 - m'.val) then 1 else 0) := by
  have hne := ne_pred hJ j
  have hr : 1 ≤ r := NeZero.one_le
  rw [PhiJ_X Dt j v hv]
  have hord := hV.2.2.2.1 (segZ j - 1)
  rw [sub_add_cancel] at hord
  rcases Formalism.MainNotions.NormalSetCounting.restSpec n' r Fr L₁ N₁ hV J Dt.nL hnL j v.1 hv with ⟨l, hy, hml⟩ | ⟨m, hy, hml⟩ | ⟨m, hy, hml⟩
  · rw [hml]
    refine ⟨_, ph_ll Dt j l v.2, fun m' => ?_⟩
    rw [multideg_single, if_neg (fun h => hne (congrArg Sigma.fst h)), if_neg, mul_zero]
    intro h
    have h1 := (Formalism.MainNotions.NormalSetCounting.ll_between hnL j l).1
    have h2 := frame_entry_le_last Fr L₁ N₁ hV (segZ j - 1) (r - 1 - m'.val) (by omega)
    omega
  · rw [hml]
    refine ⟨_, ph_lab Dt j m v.2, fun m' => ?_⟩
    rw [multideg_single, if_neg (fun h => hne (congrArg Sigma.fst h)), if_neg, mul_zero]
    intro h
    have h1 := frame_row_monotone Fr L₁ N₁ hV (segZ j) (r - 1 - m.val) (by omega)
    have h2 := frame_entry_le_last Fr L₁ N₁ hV (segZ j - 1) (r - 1 - m'.val) (by omega)
    omega
  · rw [hml]
    refine ⟨_, ph_wc Dt (j - 1) m v.2, fun m' => ?_⟩
    rw [multideg_single]
    by_cases hmm : m = m'
    · subst hmm
      rw [if_pos rfl, if_pos hy, mul_one]
    · rw [if_neg, if_neg, mul_zero]
      · intro h
        rw [hy] at h
        exact hmm (Formalism.MainNotions.NormalSetCounting.fr_rev_inj hV _ h)
      · intro h
        have h3 := eq_of_heq (Sigma.mk.inj_iff.1 h).2
        exact hmm (Sum.inr.inj h3)

theorem PhiJ_monomial (hV : Fr.Valid L₁ N₁) (hnL : ∀ j, Dt.nL j = (Fr.LLset (segZ j)).card) (hJ : 2 ≤ J) (j : ZMod J)
    (μ : ℤ × Fin r →₀ ℕ) : (∀ v ∈ μ.support, v.1 ∈ Fr.letters (segZ j)) →
    ∃ ν : TL J Dt.nL r × Fin r →₀ ℕ, (∀ c : KK O, PhiJ Fr Dt j (monomial μ c) = monomial ν c) ∧
      ∀ m' : Fin r, multideg ν ⟨j - 1, Sum.inr m'⟩ =
        Dt.P (j - 1) m' * multideg μ (Fr.fr (segZ j - 1) (r - 1 - m'.val)) := by
  induction μ using Finsupp.induction_linear with
  | zero =>
    intro _
    refine ⟨0, fun c => ?_, fun m' => by rw [multideg_zero, multideg_zero, mul_zero]⟩
    exact MvPolynomial.algHom_C _ c
  | add f g hf hg =>
    intro h
    obtain ⟨ν1, a1, b1⟩ := hf (fun v hv => h v (by
      rw [Finsupp.mem_support_iff] at hv ⊢
      rw [Finsupp.add_apply]
      omega))
    obtain ⟨ν2, a2, b2⟩ := hg (fun v hv => h v (by
      rw [Finsupp.mem_support_iff] at hv ⊢
      rw [Finsupp.add_apply]
      omega))
    refine ⟨ν1 + ν2, fun c => ?_, fun m' => ?_⟩
    · have e : (monomial (f + g) c : MvPolynomial (ℤ × Fin r) (KK O)) = monomial f c * monomial g 1 := by
        rw [monomial_mul, mul_one]
      rw [e, map_mul, a1, a2, monomial_mul, mul_one]
    · rw [multideg_add, multideg_add, b1, b2, mul_add]
  | single v k =>
    intro h
    by_cases hk0 : k = 0
    · subst hk0
      refine ⟨0, fun c => ?_, fun m' => by rw [Finsupp.single_zero, multideg_zero, multideg_zero, mul_zero]⟩
      rw [Finsupp.single_zero]
      exact MvPolynomial.algHom_C _ c
    · have hv : v.1 ∈ Fr.letters (segZ j) := h v (by rw [Finsupp.mem_support_iff, Finsupp.single_eq_same]; exact hk0)
      obtain ⟨e, he, hm⟩ := PhiJ_X_mon Dt hV hnL hJ j v hv
      refine ⟨k • e, fun c => ?_, fun m' => ?_⟩
      · have e1 : (monomial (Finsupp.single v k) c : MvPolynomial (ℤ × Fin r) (KK O)) = C c * X v ^ k := by
          rw [X_pow_eq_monomial, C_mul_monomial, mul_one]
        rw [e1, map_mul, map_pow, he, MvPolynomial.algHom_C, MvPolynomial.algebraMap_eq, monomial_pow, one_pow,
          C_mul_monomial, mul_one]
      · rw [multideg_smul, hm, multideg_single]
        split_ifs <;> ring

end Phi

end LkD

theorem lkDeg : LkDeg := by
  intro p _ n' r _ _ O _ _ _ Fr L₁ N₁ hV J _ Dt hS hJ j F hF δ hδ ν hν m'
  have hFs := congrArg (PhiJ Fr Dt j) F.as_sum
  rw [map_sum] at hFs
  rw [hFs] at hν
  obtain ⟨μ, hμ, hν'⟩ := Finset.mem_biUnion.1 (MvPolynomial.support_sum hν)
  obtain ⟨ν0, a0, b0⟩ := LkD.PhiJ_monomial Dt hV hS.2.1 hJ j μ (fun v hv =>
    (mem_supported.1 hF) (Finset.mem_coe.2 ((mem_vars v).2 ⟨μ, hμ, hv⟩)))
  rw [a0] at hν'
  have := support_monomial_subset hν'
  rw [Finset.mem_singleton] at this
  rw [this, b0, hδ μ hμ]

theorem lkVars : LkVars := by
  intro p n' r _ _ O _ _ _ Fr J _ Dt j
  let s : Set (TL J Dt.nL r × Fin r) :=
    {v | (∃ l, v.1 = ⟨j, Sum.inl l⟩) ∨ ∃ (j' : ZMod J) (m' : Fin r), v.1 = ⟨j', Sum.inr m'⟩}
  have hmon : ∀ (x : TL J Dt.nL r × Fin r) (k : ℕ), x ∈ s →
      (monomial (Finsupp.single x k) (1 : KK O)) ∈ supported (KK O) s := by
    intro x k hx
    rw [← X_pow_eq_monomial]
    refine Subalgebra.pow_mem _ ?_ _
    rw [supported_eq_adjoin_X]
    exact Algebra.subset_adjoin (Set.mem_image_of_mem _ hx)
  have hX : ∀ u : ℤ × Fin r, PhiJ Fr Dt j (X u) ∈ supported (KK O) s := by
    intro u
    unfold PhiJ chi
    rw [AlgHom.comp_apply, aeval_X]
    split_ifs with hu
    · unfold mlOf
      split_ifs with h1 h2 h3
      · rw [LkD.ph_ll]; exact hmon _ _ (Or.inl ⟨_, rfl⟩)
      · rw [LkD.ph_lab]; exact hmon _ _ (Or.inr ⟨_, _, rfl⟩)
      · rw [LkD.ph_wc]; exact hmon _ _ (Or.inr ⟨_, _, rfl⟩)
      · rw [LkD.ph_lab]; exact hmon _ _ (Or.inr ⟨_, _, rfl⟩)
    · rw [map_zero]; exact Subalgebra.zero_mem _
  have hall : ∀ F : MvPolynomial (ℤ × Fin r) (KK O), PhiJ Fr Dt j F ∈ supported (KK O) s := by
    intro F
    induction F using MvPolynomial.induction_on with
    | C a => rw [MvPolynomial.algHom_C]; exact Subalgebra.algebraMap_mem _ a
    | add f g hf hg => rw [map_add]; exact Subalgebra.add_mem _ hf hg
    | mul_X f u hf => rw [map_mul]; exact Subalgebra.mul_mem _ hf (hX u)
  intro F v hv
  exact (mem_supported.1 (hall F)) (Finset.mem_coe.2 hv)

end Formalism.MainNotions.PairMembershipBlocks
