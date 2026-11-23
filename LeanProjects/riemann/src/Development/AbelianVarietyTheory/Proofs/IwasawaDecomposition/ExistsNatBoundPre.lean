import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.DuStarPos
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SpreadLe
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.AssembleLattice
import Formalism.SharpRestriction.InertJacobiLevels.HostFam
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NcardPrimesOverOfStabilizer
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsHostCongruencePrimesStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLevelCharactersLargeStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsDiagSpacesOfCh
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsHarishChandraWeightsStatement
import Development.AutomorphicArithmetic.WeightCongruences.IsRootOfIntegral

open Formalism.BasicNotions NumberField IsDedekindDomain GlobalTheory.Mem
open scoped TensorProduct

namespace GlobalTheory.Mem

theorem exists_nat_bound_pre {ι : Type} [Finite ι] (s : ι → ℝ) (c : ℕ) :
    ∃ a : ℕ, c < 4 * a ∧ ∀ i, s i ≤ 2 * (a : ℝ) := by
  obtain ⟨b, hb⟩ := (Set.finite_range s).bddAbove
  obtain ⟨a, ha⟩ := exists_nat_ge b
  refine ⟨a + c + 1, by omega, fun i => ?_⟩
  have h1 : s i ≤ b := hb ⟨i, rfl⟩
  have h2 : (0 : ℝ) ≤ a := Nat.cast_nonneg a
  have h3 : (0 : ℝ) ≤ c := Nat.cast_nonneg c
  push_cast
  linarith

theorem exists_pre_two_words : ∃ B : Pre, Nonempty (PreX B) ∧ 2 ≤ Fintype.card B.Word ∧ B.host.TT.Nonempty ∧ (letI := B.host.cmStar; DiagSpaces B.sp ∧ ∀ j, B.sp.Vneg j = false) ∧ (∃ (Del : ℚ) (letter : B.Word → Fin (B.R.k - 2) → Bool), 0 < Del ∧ Function.Injective letter ∧ (∀ w τ (l : ℕ) (h : l + 1 < B.R.k - 1), (B.hcW w τ).v ⟨l, by omega⟩ - (B.hcW w τ).v ⟨l + 1, h⟩ = 4 * Del) ∧ ∀ w τ (l : ℕ) (h : l < B.R.k - 2), (B.hcW w τ).u ⟨l + 1, by omega⟩ = (B.hcW w τ).v ⟨l, by omega⟩ - 1 / 2 - (if letter w ⟨l, h⟩ then Del else 0)) := by
  obtain ⟨R, hRi, hRo, hR⟩ : ∃ R : Ranks, Function.Injective R.h ∧ R.o ^ 64 ≤ 2 ^ R.e ∧ 2 ≤ R.e := by
    refine ⟨Formalism.MainNotions.Inhab.Rt 0, Formalism.HC.frameCyc_h_injective 2 1, ?_, le_rfl⟩
    have h1 : (Formalism.MainNotions.Inhab.Rt 0).o = 1 := Formalism.HC.cyclicFrame_index 2
    rw [h1, one_pow]
    exact Nat.one_le_two_pow
  obtain ⟨H, -, -, -, hcc, hTT, -, hBB, hlev, hg, hπ, hp, hp'⟩ :=
    GlobalTheory.T.exists_host_congruence_primes R hRi hRo hR 0 (2 * R.f * R.k + 1) {0}
  have hk : 0 < R.k - 2 := by have := R.m_add_three_le_k; omega
  let c : Fin 2 → Fin (R.k - 2) → Bool := fun u _ => decide (u = 0)
  have hc : Function.Injective c := by
    intro u u' h
    have h0 := congrFun h ⟨0, hk⟩
    simp only [c, decide_eq_decide] at h0
    fin_cases u <;> fin_cases u' <;> simp_all
  obtain ⟨hcW, hW, P, hPR, hPH, hPW, hPc⟩ :=
    GlobalTheory.T.exists_harish_chandra_weights R H H.u0 hcc hlev hBB 2 (by norm_num) c 1 (R.t + 3)
      (fun _ => ((R.k - 2 : ℕ) : ℤ) * (4 * (1 : ℕ))) (fun _ => -1) (fun _ => 1) le_rfl (by omega)
      (fun _ => ⟨le_rfl, le_rfl, le_rfl⟩)
  obtain ⟨R', H', hcc', hlev', hBB', Wd, u₀, hcW', hv, hb, he, hf, hl⟩ := P
  dsimp only at hPR hPH hPW hPc
  subst hPR hPW
  have e1 : H' = H := eq_of_heq hPH
  have e2 : hcW' = hcW := eq_of_heq hPc
  subst e1 e2
  rename_i inst
  obtain ⟨a, ha1, ha2⟩ := exists_nat_bound_pre
    (fun x : Fin 2 × Fin (R'.m + 1) × Tau R' => ((Formalism.BasicNotions.Examples₂.lamOf (hcW' x.1 x.2.2) x.2.1.1).spread : ℝ))
    (2 * R'.f * R'.N R'.m + 1)
  let P : PreCh := @PreCh.mk R' H' hcc' hlev' hBB' (Fin 2) inst u₀ hcW' hv hb he hf hl
  obtain ⟨L, hL⟩ := GlobalTheory.T.exists_level_characters_large P (4 * a)
  obtain ⟨sp, hT, hY, hA, hV, hz, hD, -⟩ := GlobalTheory.Mem.exists_diagSpaces_ofCh P L
  choose πg hπ1 hπ2 hπ3 using hπ
  have hne : Nonempty (Tau R') := Fintype.card_pos_iff.1 (by
    rw [card_Tau H']; unfold Ranks.f Ranks.n; have := R'.ord_pos; positivity)
  refine ⟨Pre.ofCh P L sp hT hY hA hV hz, ⟨{
      piG := πg
      piG_K := hπ1
      piG_norm := hπ2
      piG_cong := hπ3
      piT := L.piT
      piT_K := L.piT_K
      piT_norm := L.piT_norm
      piT_cong := fun u => Ideal.mem_span_singleton.1 (L.piT_cong u)
      pde_split := ⟨?_, ?_⟩
      ccK_top := hcc'
      e_even := ?_
      hcW_inj := ?_
      a := a
      g_big := ?_
      T_gt := ?_
      a_gt := ?_
      spread_le := ?_ }⟩, ?_, ?_, hD, 1, c, one_pos, hc, ?_, ?_⟩
  · exact (GlobalTheory.HostSplit.ncard_placesOver H'.E H'.pde_prime).symm.trans
      (GlobalTheory.HostSplit.split_of_one_mod R' H' _ H'.pde_prime hp).1
  · exact (GlobalTheory.HostSplit.ncard_placesOver H'.E H'.pde'_prime).symm.trans
      (GlobalTheory.HostSplit.split_of_one_mod R' H' _ H'.pde'_prime hp').1
  · intro j
    refine UpperTheory.Mu.muq_of_const H' (Equiv.refl _)
      (1 + (j.1 : ℤ) * (2 * ((R'.t + 3 : ℕ) : ℤ)) + ((R'.t + 3 : ℕ) : ℤ)) (fun τ => ?_)
    show (hcW' u₀ τ).e j = _
    rw [((hW u₀ τ).2.1 j).2, ((hW u₀ τ).2.1 j).1]
    push_cast
    ring
  · show Function.Injective hcW'
    intro u u' h
    obtain ⟨τ⟩ := hne
    have h1 := (hW u τ).2.2.2 0 hk
    have h2 := (hW u' τ).2.2.2 0 hk
    rw [h, h2] at h1
    have h3 : (if c u' ⟨0, hk⟩ = true then ((1 : ℕ) : ℚ) else 0) = if c u ⟨0, hk⟩ = true then ((1 : ℕ) : ℚ) else 0 :=
      sub_right_injective h1
    clear h h1 h2
    revert h3
    simp only [c]
    revert u u'
    simp [Fin.forall_fin_two]
  · intro i
    have := hg i
    show 2 * R'.f * R'.k < H'.g i - 1
    omega
  · intro u
    have := hL u
    show 4 * (a : ℝ) < (L.T u : ℝ)
    exact_mod_cast this
  · show ((2 * R'.f * R'.N R'.m + 1 : ℕ) : ℝ) < 4 * (a : ℝ)
    exact_mod_cast ha1
  · intro u j hj τ
    exact ha2 (u, ⟨j, Nat.lt_succ_of_le hj⟩, τ)
  · show 2 ≤ @Fintype.card (Fin 2) inst
    rw [Subsingleton.elim inst (Fin.fintype 2), Fintype.card_fin]
  · show H'.TT.Nonempty
    rw [hTT]
    exact Finset.singleton_nonempty _
  · intro w τ l h
    have h' : l + 1 < R'.k - 1 := h
    show (hcW' w τ).v ⟨l, by omega⟩ - (hcW' w τ).v ⟨l + 1, h'⟩ = 4 * 1
    rw [(hW w τ).1, (hW w τ).1]
    have h3 : R'.k - 2 - l = (R'.k - 2 - (l + 1)) + 1 := by omega
    dsimp only
    rw [h3]
    push_cast
    ring
  · intro w τ l h
    have h1 := (hW w τ).2.2.2 l h
    rw [Nat.cast_one] at h1
    exact h1

end GlobalTheory.Mem
