import Mathlib
import Development.WeilBound.CoreStatements.AutomorphicKernels.UnitarySchrodingerModel.LocalDefs
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ResAlgSplitTwo
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FixedNondeg
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnramifiedQuotientCardStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ResidueAlgebraUnramifiedStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NormFibreCardNonzeroStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NormFibreCardZeroStatement

open PositivityTheory.PfSWUS.Loc GlobalTheory.CompanionTheory.UnrDens GlobalTheory.CompanionTheory.SiegLoc Filter Topology

namespace GlobalTheory.CompanionTheory.SiegLoc.GaussOne

variable {E : Type} [CommRing E] [Fintype E] {τ : E →+* E} {q : ℕ} {ε : ℤ}

open Classical in

theorem sum_fixed_eq_zero (χ : AddChar E ℂ) (A b : E) (hb : τ b = b) (hχ : χ (A * b) ≠ 1) :
    ∑ t ∈ Finset.univ.filter (fun t : E => τ t = t), χ (A * t) = 0 := by
  set S := ∑ t ∈ Finset.univ.filter (fun t : E => τ t = t), χ (A * t) with hS
  have key : χ (A * b) * S = S := by
    rw [hS, Finset.mul_sum]
    refine Finset.sum_nbij' (fun t => t + b) (fun t => t - b) ?_ ?_ ?_ ?_ ?_
    · intro t ht
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ht ⊢
      rw [map_add, ht, hb]
    · intro t ht
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ht ⊢
      rw [map_sub, ht, hb]
    · intro t _
      simp
    · intro t _
      simp
    · intro t _
      rw [← AddChar.map_add_eq_mul, mul_add, add_comm]
  have h1 : (1 - χ (A * b)) * S = 0 := by rw [sub_mul, one_mul, key, sub_self]
  rcases mul_eq_zero.mp h1 with h | h
  · exact absurd (sub_eq_zero.mp h).symm hχ
  · exact h

open Classical in

theorem card_filter_norm (t : E) :
    (((Finset.univ.filter (fun w : E => τ w * w = t)).card : ℕ) : ℤ) =
      (Nat.card {a : E // a * τ a = t} : ℤ) := by
  have hf : Finset.univ.filter (fun w : E => τ w * w = t) =
      Finset.univ.filter (fun a : E => a * τ a = t) := by
    ext w
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rw [mul_comm]
  rw [hf, Nat.card_eq_fintype_card, Fintype.card_subtype]

open Classical in

theorem gauss_core (h : ResAlg E τ q ε) (χ : AddChar E ℂ) (A b : E) (hb : τ b = b)
    (hχ : χ (A * b) ≠ 1) :
    ∑ w : E, χ (A * (τ w * w)) = (ε : ℂ) * q := by
  have hmap : ∀ w ∈ (Finset.univ : Finset E),
      τ w * w ∈ Finset.univ.filter (fun t : E => τ t = t) := by
    intro w _
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, map_mul, h.inv]
    exact mul_comm _ _
  rw [← Finset.sum_fiberwise_of_maps_to hmap]
  have hfib : ∀ t ∈ Finset.univ.filter (fun t : E => τ t = t),
      (∑ w ∈ Finset.univ.filter (fun w : E => τ w * w = t), χ (A * (τ w * w))) =
        (((q : ℂ) - ε) + if t = 0 then (q : ℂ) * ε else 0) * χ (A * t) := by
    intro t ht
    have ht' : τ t = t := (Finset.mem_filter.mp ht).2
    rw [Finset.sum_congr rfl (fun w hw => by rw [(Finset.mem_filter.mp hw).2]), Finset.sum_const,
      nsmul_eq_mul]
    congr 1
    have hc := card_filter_norm (τ := τ) t
    have hc' : (((Finset.univ.filter (fun w : E => τ w * w = t)).card : ℕ) : ℂ) =
        ((Nat.card {a : E // a * τ a = t} : ℤ) : ℂ) := by
      rw [← hc]
      push_cast
      rfl
    rw [hc']
    by_cases h0 : t = 0
    · subst h0
      rw [GlobalTheory.T.norm_fibre_card_zero E τ q ε h, if_pos rfl]
      push_cast
      ring
    · rw [GlobalTheory.T.norm_fibre_card_nonzero E τ q ε h t ht' h0, if_neg h0]
      push_cast
      ring
  rw [Finset.sum_congr rfl hfib]
  simp only [add_mul, Finset.sum_add_distrib, ← Finset.mul_sum]
  rw [sum_fixed_eq_zero χ A b hb hχ, mul_zero, zero_add]
  simp only [ite_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_filter, Finset.mem_univ, true_and,
    map_zero, if_true, mul_zero, AddChar.map_zero_eq_one, mul_one]
  ring

end GlobalTheory.CompanionTheory.SiegLoc.GaussOne

namespace GlobalTheory.CompanionTheory.SiegLoc

theorem gauss_level_one : ∀ (R : Type) [CommRing R] (σ : R →+* R) (ϖ : R) (q : ℕ) (ε : ℤ)
    (hR : IsUnrQuad R σ ϖ q ε) [∀ k, Fintype (R ⧸ lev ϖ k)] (ψ : ∀ k, AddChar (R ⧸ lev ϖ k) ℂ),
    IsLevelChars σ ϖ ψ → ∀ (a : R), σ a = a → a ∉ lev ϖ 1 →
    (∑ w : R ⧸ lev ϖ 1, ψ 1 (Ideal.Quotient.mk (lev ϖ 1) a * (barσ σ ϖ hR.fix_ϖ 1 w * w))) =
      (ε : ℂ) * q := by
  intro R _ σ ϖ q ε hR _ ψ hψ a ha hna
  have hex : ∃ b, σ b = b ∧ ψ 1 (Ideal.Quotient.mk _ (a * b)) ≠ 1 := by
    by_contra hcon
    push_neg at hcon
    exact hna (hψ.prim a ha hcon)
  obtain ⟨b, hb, hχ⟩ := hex
  refine GaussOne.gauss_core (GlobalTheory.T.residue_algebra_unramified R σ ϖ q ε hR) (ψ 1) _ (Ideal.Quotient.mk _ b) ?_ ?_
  · rw [barσ_mk, hb]
  · rwa [← map_mul]

end GlobalTheory.CompanionTheory.SiegLoc
