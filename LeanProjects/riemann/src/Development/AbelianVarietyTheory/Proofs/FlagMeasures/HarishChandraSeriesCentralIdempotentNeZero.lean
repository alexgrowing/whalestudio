import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.IsMirClass
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CharacterDecompositionAndClassFunctionExpansionStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HarishChandraProductListDegreeStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HarishChandraProductListIsCharacterAndPermInvariStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GroupAlgebraTraceIdempotentAndIrreducibleDegreeStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CentralIdempotentOfIrrCharacterOrthogonalCentralStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FiniteIrrCharactersAndFinsumCentralIdempotentsEqStatement

open Polynomial Formalism.MainNotions.ArithmeticCylinders GlobalTheory.GLq GlobalTheory.GLm
open scoped Classical

namespace GlobalTheory.GLm

theorem ip_symm_of_inv {G : Type} [Group G] [Fintype G] (α β : G → ℂ) : ip α β = ip β α := by
  unfold ip
  congr 1
  refine Fintype.sum_equiv (Equiv.inv G) _ _ fun x => ?_
  simp [mul_comm]

theorem exists_cusp_list (g : ℕ) [Fact g.Prime] (L : LabelDatum g) (hG : Green) :
    ∀ (n : ℕ) (f : (ZMod g)[X]), f.Monic → f.natDegree = n → f.coeff 0 ≠ 0 →
      ∃ Q : List ((ZMod g)[X] × Pc g), (∀ p ∈ Q, IsCuspOf L p.1 p.2.2) ∧ degL (Q.map Prod.snd) = n ∧
        f = (Q.map Prod.fst).prod := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro f hf hn h0
    by_cases hu : IsUnit f
    · have h1 : f = 1 := hf.isUnit_iff.mp hu
      refine ⟨[], by simp, ?_, by simpa using h1⟩
      rw [← hn, h1]; simp [degL]
    · obtain ⟨P, hPm, hPi, q, hq⟩ := Polynomial.exists_monic_irreducible_factor f hu
      have hqm : q.Monic := hPm.of_mul_monic_left (hq ▸ hf)
      have hdeg : n = P.natDegree + q.natDegree := by
        rw [← hn, hq, hPm.natDegree_mul hqm]
      have hpos : 0 < P.natDegree := hPi.natDegree_pos
      have hc : P.coeff 0 * q.coeff 0 ≠ 0 := by
        rwa [hq, Polynomial.mul_coeff_zero] at h0
      obtain ⟨Q, hQ1, hQ2, hQ3⟩ := ih q.natDegree (by omega) q hqm rfl (right_ne_zero_of_mul hc)
      obtain ⟨τ, hτ, -⟩ := hG g L P.natDegree hpos
      have hP : IsPrimeLab P.natDegree P := ⟨hPm, hPi, left_ne_zero_of_mul hc, rfl⟩
      refine ⟨(P, ⟨P.natDegree, τ P⟩) :: Q, ?_, ?_, ?_⟩
      · intro p hp
        rcases List.mem_cons.mp hp with rfl | hp
        · exact (hτ P hP).1
        · exact hQ1 p hp
      · rw [hdeg, ← hQ2]; simp [degL]
      · rw [List.map_cons, List.prod_cons, ← hQ3]; exact hq

theorem exists_irr_hasLabel (g : ℕ) [Fact g.Prime] (L : LabelDatum g) (hG : Green) (n : ℕ) (f : (ZMod g)[X])
    (hf : f.Monic) (hn : f.natDegree = n) (h0 : f.coeff 0 ≠ 0) :
    ∃ ρ : Gn g n → ℂ, IsIrr ρ ∧ HasLabel L ρ f := by
  obtain ⟨Q, hQ1, hQ2, hQ3⟩ := exists_cusp_list g L hG n f hf hn h0
  have hirr : ∀ p ∈ Q.map Prod.snd, IsIrr p.2 := by
    intro p hp
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
    exact (hQ1 q hq).2.1.2.1
  have hch : IsChar (hcL (Q.map Prod.snd) n) :=
    (GlobalTheory.T.harishChandraProductList_isCharacter_and_perm_invariant g _ (Q.map Prod.snd) n hQ2.symm fun p hp => by
      obtain ⟨V, -, hV⟩ := hirr p hp
      exact ⟨V, hV⟩).1
  have hne : hcL (Q.map Prod.snd) n 1 ≠ 0 := by
    intro h
    have hd := GlobalTheory.T.harishChandraProductList_degree g (Q.map Prod.snd) n hQ2.symm
    rw [h, zero_mul] at hd
    refine mul_ne_zero ?_ ?_ hd.symm
    · refine Finset.prod_ne_zero_iff.mpr fun i hi => ?_
      have hi1 : i ≠ 0 := by have := (Finset.mem_Icc.mp hi).1; omega
      have h1 : 1 < g ^ i := Nat.one_lt_pow hi1 (Fact.out : g.Prime).one_lt
      rw [sub_ne_zero]
      exact_mod_cast h1.ne'
    · refine List.prod_ne_zero fun hz => ?_
      obtain ⟨p, hp, hp0⟩ := List.mem_map.mp hz
      obtain ⟨d, hd0, hd1⟩ := (GlobalTheory.T.groupAlgebraTrace_idempotent_and_irreducible_degree (Gn g p.1) 1 p.2).2.1 (hirr p hp)
      rw [hp0] at hd1
      have : d = 0 := by exact_mod_cast hd1.symm
      omega
  have hdec := GlobalTheory.T.character_decomposition_and_classFunction_expansion (Gn g n) (hcL (Q.map Prod.snd) n)
  have hsum := hdec.2.1 (hdec.2.2.1 hch)
  by_contra hcon
  push Not at hcon
  apply hne
  rw [hsum, finsum_mem_of_eqOn_zero]
  · rfl
  · intro ρ hρ
    have : ip (hcL (Q.map Prod.snd) n) ρ = 0 := by
      by_contra hip
      exact hcon ρ hρ ⟨Q, hQ1, hQ2, hQ3, by rwa [ip_symm_of_inv]⟩
    simp [this]

theorem zOf_ne_zero_of_isIrr {G : Type} [Group G] [Fintype G] {ρ : G → ℂ} (hρ : IsIrr ρ) : zOf ρ ≠ 0 := by
  intro h
  obtain ⟨-, h1, h2⟩ := GlobalTheory.T.groupAlgebraTrace_idempotent_and_irreducible_degree G 1 ρ
  obtain ⟨d, hd0, hd1⟩ := h1 hρ
  have htr : tr (1 : MonoidAlgebra ℂ G) ρ = ρ 1 := by
    unfold tr
    rw [Finset.sum_eq_single 1]
    · simp [MonoidAlgebra.one_def]
    · intro b _ hb
      simp [MonoidAlgebra.one_def, Finsupp.single_apply, hb, hb.symm]
    · simp
  have hd : ρ 1 ≠ 0 := by rw [hd1]; exact_mod_cast hd0.ne'
  have hc : (Fintype.card G : ℂ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  rw [h, mul_zero, htr] at h2
  exact mul_ne_zero (div_ne_zero hd hc) hd (h2.symm.trans (by simp))

theorem eSerC_ne_zero : ∀ (g : ℕ) [Fact g.Prime] (L : LabelDatum g), Green → ∀ (n : ℕ) (f : (ZMod g)[X]),
    f.Monic → f.natDegree = n → f.coeff 0 ≠ 0 → eSerC L n f ≠ 0 := by
  intro g _ L hG n f hf hn h0 he
  obtain ⟨ρ, hρ, hl⟩ := exists_irr_hasLabel g L hG n f hf hn h0
  have hfin : {χ : Gn g n → ℂ | IsIrr χ ∧ HasLabel L χ f}.Finite :=
    (GlobalTheory.T.finite_irrCharacters_and_finsum_centralIdempotents_eq_one (Gn g n)).1.subset fun χ hχ => hχ.1
  apply zOf_ne_zero_of_isIrr hρ
  have h : zOf ρ * eSerC L n f = zOf ρ := by
    unfold eSerC
    rw [finsum_mem_eq_finite_toFinset_sum _ hfin, Finset.mul_sum, Finset.sum_eq_single ρ]
    · rw [(GlobalTheory.T.centralIdempotentOfIrrCharacter_orthogonal_central _ ρ ρ hρ hρ).1, if_pos rfl]
    · intro b hb hne
      rw [(GlobalTheory.T.centralIdempotentOfIrrCharacter_orthogonal_central _ ρ b hρ (hfin.mem_toFinset.mp hb).1).1, if_neg hne.symm]
    · intro hb
      exact absurd (hfin.mem_toFinset.mpr ⟨hρ, hl⟩) hb
  rw [← h, he, mul_zero]

end GlobalTheory.GLm
