import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.FrameInert
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NormOneUnitHilbertNinety
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PlaceConjugationPropertiesCmFieldStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIntegralElementCharPolyNonsplit

noncomputable section

open NumberField IsDedekindDomain Matrix
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC GlobalTheory.BCT
open scoped Classical

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PositivityTheory.Rg.BcB.F.Inert.WittBasisGramMatrix

variable {R : Type} [CommRing R]

theorem antiJ_eq_rev {L : Type} [Field L] {n : ℕ} (i j : Fin n) :
    antiJ L n i j = if i = Fin.rev j then 1 else 0 := by
  have key : ((i : ℕ) + j + 1 = n) ↔ i = Fin.rev j := by
    have hi := i.isLt
    have hj := j.isLt
    rw [Fin.ext_iff, Fin.val_rev]
    omega
  show (if (i : ℕ) + j + 1 = n then (1 : L) else 0) = _
  exact if_congr key rfl rfl

theorem antiJ_mul_self {L : Type} [Field L] (n : ℕ) : antiJ L n * antiJ L n = 1 := by
  ext i k
  rw [Matrix.mul_apply, Matrix.one_apply]
  simp only [antiJ_eq_rev]
  rw [Finset.sum_eq_single (Fin.rev k)]
  · simp [Fin.rev_rev]
  · intro b _ hb
    simp [hb]
  · intro h
    exact absurd (Finset.mem_univ _) h

def bM {n : ℕ} (d₁ d₂ : Fin n → R) : Matrix (Fin n) (Fin n) R :=
  fun i j => (if i = j then d₁ i else 0) + (if i = Fin.rev j then d₂ i else 0)

theorem bM_map {n : ℕ} (σ : R →+* R) (d₁ d₂ : Fin n → R) (i j : Fin n) :
    σ (bM d₁ d₂ i j) = (if i = j then σ (d₁ i) else 0) + (if i = Fin.rev j then σ (d₂ i) else 0) := by
  simp only [bM]
  split_ifs <;> simp

theorem gram_bM {n : ℕ} (σ : R →+* R) (d₁ d₂ : Fin n → R)
    (P1 : ∀ j, j ≠ Fin.rev j → σ (d₁ j) * d₁ j + σ (d₂ (Fin.rev j)) * d₂ (Fin.rev j) = 0)
    (P2 : ∀ j, j ≠ Fin.rev j → σ (d₁ j) * d₂ j + σ (d₂ (Fin.rev j)) * d₁ (Fin.rev j) = 1)
    (P3 : ∀ j, j = Fin.rev j → d₂ j = 0 ∧ σ (d₁ j) * d₁ j = 1) (j k : Fin n) :
    (((bM d₁ d₂).map σ)ᵀ * bM d₁ d₂) j k = if j = Fin.rev k then 1 else 0 := by
  rw [Matrix.mul_apply]
  simp only [Matrix.transpose_apply, Matrix.map_apply, bM_map]
  simp only [bM, add_mul, mul_add, Finset.sum_add_distrib, ite_mul, mul_ite, zero_mul, mul_zero,
    Finset.sum_ite_eq', Finset.mem_univ, if_true]
  by_cases hjk : j = k
  · subst hjk
    by_cases hs : j = Fin.rev j
    · obtain ⟨h0, h1⟩ := P3 j hs
      rw [← hs]
      simp [h0, h1]
    · simp only [if_neg hs, if_neg (Ne.symm hs), eq_self_iff_true, if_true, add_zero, zero_add]
      exact P1 j hs
  · by_cases hr : j = Fin.rev k
    · have hk : k = Fin.rev j := by rw [hr, Fin.rev_rev]
      subst hk
      have hs : j ≠ Fin.rev j := hjk
      simp only [Fin.rev_rev, if_neg (Ne.symm hs), if_neg hs, eq_self_iff_true, if_true, zero_add,
        add_zero]
      rw [add_comm]
      exact P2 j hs
    · have h1 : k ≠ j := Ne.symm hjk
      have h2 : k ≠ Fin.rev j := fun h => hr (by rw [h, Fin.rev_rev])
      have h3 : Fin.rev k ≠ j := fun h => hr h.symm
      have h4 : Fin.rev k ≠ Fin.rev j := fun h => hjk (Fin.rev_injective h).symm
      simp only [if_neg h1, if_neg h2, if_neg h3, if_neg h4, if_neg hr, add_zero]

end PositivityTheory.Rg.BcB.F.Inert.WittBasisGramMatrix

namespace PositivityTheory.Rg.BcB.F.Inert

theorem wittEx : WittEx := by
  intro E _ _ _ hU n w hw
  obtain ⟨_, hinv, hval, hsplit, _⟩ := GlobalTheory.T.placeConjugation_properties_cmField E hU w
  obtain ⟨_, ⟨ϖ, q, hUI, _⟩, _, _⟩ := hsplit hw
  obtain ⟨_, _, _, _, ⟨x₀, hx₀, hδ⟩, _, _⟩ := hUI
  have hx0 : Valued.v x₀ ≤ 1 := (Valuation.mem_integer_iff _ _).1 hx₀
  obtain ⟨t, ht1, htn⟩ := GlobalTheory.CompanionTheory.UnitNormLocal.exists_unit_norm_eq E hU w hw (-1) (by simp) (by simp)
  obtain ⟨δ, hδdef⟩ : ∃ δ, δ = GlobalTheory.BCT.cj w x₀ - x₀ := ⟨_, rfl⟩
  have hδv : Valued.v δ = 1 := by rw [hδdef]; exact hδ
  have hδ0 : δ ≠ 0 := by
    intro h
    rw [h, Valuation.map_zero] at hδv
    exact zero_ne_one hδv
  have hσδ : GlobalTheory.BCT.cj w δ = -δ := by rw [hδdef, map_sub, hinv]; ring
  obtain ⟨wv, hwvdef⟩ : ∃ u, u = GlobalTheory.BCT.cj w x₀ * δ⁻¹ := ⟨_, rfl⟩
  have htr : GlobalTheory.BCT.cj w wv + wv = 1 := by
    rw [hwvdef, map_mul, map_inv₀, hinv, hσδ, inv_neg]
    have e : x₀ * -δ⁻¹ + GlobalTheory.BCT.cj w x₀ * δ⁻¹ = (GlobalTheory.BCT.cj w x₀ - x₀) * δ⁻¹ := by ring
    rw [e, ← hδdef, mul_inv_cancel₀ hδ0]
  have hwv1 : Valued.v wv ≤ 1 := by
    rw [hwvdef, map_mul, map_inv₀, hval, hδv, inv_one, mul_one]
    exact hx0
  obtain ⟨d₁, hd₁⟩ : ∃ f : Fin n → IsDedekindDomain.HeightOneSpectrum.adicCompletion E w, ∀ j, f j =
      if (j : ℕ) < (Fin.rev j : ℕ) then 1 else if j = Fin.rev j then 1 else -(t * wv) :=
    ⟨_, fun _ => rfl⟩
  obtain ⟨d₂, hd₂⟩ : ∃ f : Fin n → IsDedekindDomain.HeightOneSpectrum.adicCompletion E w, ∀ j, f j =
      if (j : ℕ) < (Fin.rev j : ℕ) then 1 - wv else if j = Fin.rev j then 0 else t :=
    ⟨_, fun _ => rfl⟩
  have hfirst : ∀ j : Fin n, (j : ℕ) < (Fin.rev j : ℕ) → d₁ j = 1 ∧ d₂ j = 1 - wv := by
    intro j h
    rw [hd₁, hd₂, if_pos h, if_pos h]
    exact ⟨rfl, rfl⟩
  have hsecond : ∀ j : Fin n, (Fin.rev j : ℕ) < (j : ℕ) → d₁ j = -(t * wv) ∧ d₂ j = t := by
    intro j h
    have h1 : ¬ ((j : ℕ) < (Fin.rev j : ℕ)) := by omega
    have h2 : j ≠ Fin.rev j := fun e => by rw [← e] at h; exact lt_irrefl _ h
    rw [hd₁, hd₂, if_neg h1, if_neg h1, if_neg h2, if_neg h2]
    exact ⟨rfl, rfl⟩
  have hmid : ∀ j : Fin n, j = Fin.rev j → d₁ j = 1 ∧ d₂ j = 0 := by
    intro j e
    have h1 : ¬ ((j : ℕ) < (Fin.rev j : ℕ)) := by rw [← e]; exact lt_irrefl _
    rw [hd₁, hd₂, if_neg h1, if_neg h1, if_pos e, if_pos e]
    exact ⟨rfl, rfl⟩
  have hside : ∀ j : Fin n, j ≠ Fin.rev j → (j : ℕ) < (Fin.rev j : ℕ) ∨ (Fin.rev j : ℕ) < (j : ℕ) :=
    fun j hj => lt_or_gt_of_ne (fun e => hj (Fin.ext e))
  have P1 : ∀ j, j ≠ Fin.rev j → GlobalTheory.BCT.cj w (d₁ j) * d₁ j +
      GlobalTheory.BCT.cj w (d₂ (Fin.rev j)) * d₂ (Fin.rev j) = 0 := by
    intro j hj
    rcases hside j hj with h | h
    · obtain ⟨a1, -⟩ := hfirst j h
      obtain ⟨-, b2⟩ := hsecond (Fin.rev j) (by rw [Fin.rev_rev]; exact h)
      rw [a1, b2, map_one, htn]
      ring
    · obtain ⟨a1, -⟩ := hsecond j h
      obtain ⟨-, b2⟩ := hfirst (Fin.rev j) (by rw [Fin.rev_rev]; exact h)
      rw [a1, b2, map_neg, map_mul, map_sub, map_one]
      linear_combination (GlobalTheory.BCT.cj w wv * wv) * htn - htr
  have P2 : ∀ j, j ≠ Fin.rev j → GlobalTheory.BCT.cj w (d₁ j) * d₂ j +
      GlobalTheory.BCT.cj w (d₂ (Fin.rev j)) * d₁ (Fin.rev j) = 1 := by
    intro j hj
    rcases hside j hj with h | h
    · obtain ⟨a1, a2⟩ := hfirst j h
      obtain ⟨b1, b2⟩ := hsecond (Fin.rev j) (by rw [Fin.rev_rev]; exact h)
      rw [a1, a2, b1, b2, map_one]
      linear_combination (-wv) * htn
    · obtain ⟨a1, a2⟩ := hsecond j h
      obtain ⟨b1, b2⟩ := hfirst (Fin.rev j) (by rw [Fin.rev_rev]; exact h)
      rw [a1, a2, b1, b2, map_neg, map_mul, map_sub, map_one]
      linear_combination (-GlobalTheory.BCT.cj w wv) * htn
  have P3 : ∀ j, j = Fin.rev j → d₂ j = 0 ∧ GlobalTheory.BCT.cj w (d₁ j) * d₁ j = 1 := by
    intro j hj
    obtain ⟨a1, a2⟩ := hmid j hj
    exact ⟨a2, by rw [a1, map_one, one_mul]⟩
  have hG : ((WittBasisGramMatrix.bM d₁ d₂).map (GlobalTheory.BCT.cj w))ᵀ * WittBasisGramMatrix.bM d₁ d₂ =
      antiJ (IsDedekindDomain.HeightOneSpectrum.adicCompletion E w) n := by
    ext j k
    rw [WittBasisGramMatrix.gram_bM (GlobalTheory.BCT.cj w) d₁ d₂ P1 P2 P3 j k, WittBasisGramMatrix.antiJ_eq_rev]
  have hCB : (antiJ (IsDedekindDomain.HeightOneSpectrum.adicCompletion E w) n *
      ((WittBasisGramMatrix.bM d₁ d₂).map (GlobalTheory.BCT.cj w))ᵀ) * WittBasisGramMatrix.bM d₁ d₂ = 1 := by
    rw [Matrix.mul_assoc, hG, WittBasisGramMatrix.antiJ_mul_self]
  have hBC : WittBasisGramMatrix.bM d₁ d₂ * (antiJ (IsDedekindDomain.HeightOneSpectrum.adicCompletion E w) n *
      ((WittBasisGramMatrix.bM d₁ d₂).map (GlobalTheory.BCT.cj w))ᵀ) = 1 := (Matrix.mul_eq_one_comm_of_equiv (Equiv.refl _)).mp hCB
  have hd1int : ∀ j, Valued.v (d₁ j) ≤ 1 := by
    intro j
    rw [hd₁]
    split_ifs
    · simp
    · simp
    · rw [Valuation.map_neg, map_mul, ht1, one_mul]
      exact hwv1
  have hd2int : ∀ j, Valued.v (d₂ j) ≤ 1 := by
    intro j
    rw [hd₂]
    split_ifs
    · exact (Valuation.map_sub _ _ _).trans (max_le (by simp) hwv1)
    · simp
    · rw [ht1]
  have hBint : ∀ a c, WittBasisGramMatrix.bM d₁ d₂ a c ∈ IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers E w := by
    intro a c
    rw [IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers]
    show Valued.v ((if a = c then d₁ a else 0) + (if a = Fin.rev c then d₂ a else 0)) ≤ 1
    refine (Valuation.map_add _ _ _).trans (max_le ?_ ?_)
    · split_ifs
      · exact hd1int a
      · simp
    · split_ifs
      · exact hd2int a
      · simp
  have hAint : ∀ a c, antiJ (IsDedekindDomain.HeightOneSpectrum.adicCompletion E w) n a c ∈
      IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers E w := by
    intro a c
    rw [WittBasisGramMatrix.antiJ_eq_rev]
    split_ifs
    · exact one_mem _
    · exact zero_mem _
  have hTint : ∀ a c, ((WittBasisGramMatrix.bM d₁ d₂).map (GlobalTheory.BCT.cj w))ᵀ a c ∈
      IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers E w := by
    intro a c
    have h := hBint c a
    rw [IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers] at h ⊢
    rw [Matrix.transpose_apply, Matrix.map_apply, hval]
    exact h
  refine ⟨(⟨WittBasisGramMatrix.bM d₁ d₂, antiJ (IsDedekindDomain.HeightOneSpectrum.adicCompletion E w) n *
      ((WittBasisGramMatrix.bM d₁ d₂).map (GlobalTheory.BCT.cj w))ᵀ, hBC, hCB⟩ :
      GL (Fin n) (IsDedekindDomain.HeightOneSpectrum.adicCompletion E w)), ?_⟩
  refine (show _ ∧ _ from ⟨?_, hG⟩)
  exact GlobalTheory.ExInertUnit.mem_KGL_of_entries w _ hBint (GlobalTheory.ExInertUnit.mul_entries hAint hTint)

end PositivityTheory.Rg.BcB.F.Inert

end
