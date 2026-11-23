import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.DecompositionInvariantsCondition
import Formalism.GaloisCohomology.LocalTateDualityK
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.RationalDualityOfAllCoefficients
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.InvariantsVanishAtPrimeOfAdmissibleStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FontaineBoundsCrystallineDeRhamAll
import Formalism.SharpRestriction.LevelLetterCocycles.JsetEmb
open Formalism Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations

namespace GlobalTheory.HubX.InvariantsNoJump

theorem mem_Jset_of_isJumpV (S : LocalSituation.Sit) (Y : LocLat S.G S.Qp S.LL S.O) (τ : S.K →ₐ[S.Qp] S.LL) (a : ℤ)
    (ha : IsJumpV S.PD Y.ρ τ a) : a ∈ LocalSituation.Jset S Y := by
  intro heq
  apply ha
  unfold FildR DdRE
  rw [inf_right_comm, heq, inf_right_comm]

theorem two_add_sum_jumps_le_intervalExponent (S : LocalSituation.Sit) (Y : LocLat S.G S.Qp S.LL S.O) (τ : S.K →ₐ[S.Qp] S.LL) (l m vd : ℕ)
    (hfin : (LocalSituation.Jset S Y).Finite) (h0 : ¬ IsJumpV S.PD Y.ρ τ 0) :
    2 + ∑ᶠ (u : ℤ) (_ : IsJumpV S.PD Y.ρ τ u), (m + LocalSituation.vZ l u) ≤ LocalSituation.cLL l m vd (LocalSituation.Jset S Y) 0 1 := by
  classical
  have hI : Finset.Ico (0 : ℤ) 1 = {0} := by decide
  unfold LocalSituation.cLL LocalSituation.rI
  rw [hI, Finset.sum_singleton]
  simp only [sub_zero]
  have hle : ∑ᶠ (u : ℤ) (_ : IsJumpV S.PD Y.ρ τ u), (m + LocalSituation.vZ l u) ≤
      ∑ᶠ (u : ℤ) (_ : u ∈ LocalSituation.Jset S Y) (_ : u ≠ 0), (m + LocalSituation.vZ l u) := by
    simp only [finsum_eq_if]
    rw [finsum_eq_sum_of_support_subset _ (s := hfin.toFinset) ?_,
      finsum_eq_sum_of_support_subset _ (s := hfin.toFinset) ?_]
    rotate_left
    all_goals try
      intro u hu
      rw [Set.Finite.coe_toFinset]
      by_contra hn
      have hn' : ¬ IsJumpV S.PD Y.ρ τ u := fun hj => hn (mem_Jset_of_isJumpV S Y τ u hj)
      apply hu
      simp [hn, hn']
    apply Finset.sum_le_sum
    · intro u _
      by_cases hj : IsJumpV S.PD Y.ρ τ u
      · have hu0 : u ≠ 0 := by rintro rfl; exact h0 hj
        simp only [if_pos hj, if_pos (mem_Jset_of_isJumpV S Y τ u hj), if_pos hu0, le_refl]
      · simp only [if_neg hj]
        exact Nat.zero_le _
  omega

end GlobalTheory.HubX.InvariantsNoJump

namespace GlobalTheory.HubX.InvariantsNoJump

theorem torsion_exponent_kills_invariants_no_jump_zero : GlobalTheory.Published.BlochKatoLocal → Formalism.GaloisCohomology.LocalTateDualityK → Formalism.GaloisCohomology.LocalEulerCharK → ∀ (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F), ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL), let S := LocalSituation.sit D.loc HW l (D.locA l) K s LL h; ∀ (M0 h0 : ℕ) (T : LocLat S.G S.Qp S.LL S.O), LocalSituation.HypW S ((F l).E K s LL h).tie T M0 h0 → (∀ τ, ¬ IsJumpV S.PD T.ρ τ 0) → ∀ x : T.V ⧸ T.L.T, (∀ g, actD T.L g x = x) → ((LocalSituation.ell S : S.O) ^ GlobalTheory.HubX.invariantsCountConstant D.loc HW D.locA l K s LL h M0 h0 T) • x = 0 := by
  intro _ _ _ D HW F _ l _ K s LL h S M0 h0 T hW hJ x hx
  have hat := GlobalTheory.T.invariants_vanish_at_prime_of_admissible D HW F (GlobalTheory.Per.FontaineAll.fontaine_bounds D) l K s LL h
  have hp : LocalSituation.ell S = l := (D.loc l).PD_p K
  have hs : S.W.s = s := (HW l).W_s K s LL h
  have hcard := Formalism.MainNotions.N.JsetEmb.card_emb_good h
  have hpos : 0 < Nat.card (↥K.1 →ₐ[ℚ_[l]] ↥LL.1) := by
    haveI : FiniteDimensional ℚ_[l] ↥K.1 := K.2
    rw [hcard]; exact Module.finrank_pos
  obtain ⟨τ⟩ := (Nat.card_pos_iff.1 hpos).1
  have key := hat M0 h0 T τ hW (hJ τ) x hx
  have hfin : (LocalSituation.Jset S T).Finite :=
    (Set.finite_Icc (-(M0 : ℤ)) h0).subset fun a ha => hW.2.1 a ha
  have hle : LocalSituation.c0 S T τ M0 h0 ≤ GlobalTheory.HubX.invariantsCountConstant D.loc HW D.locA l K s LL h M0 h0 T := by
    unfold LocalSituation.c0
    rw [hp, hs]
    exact two_add_sum_jumps_le_intervalExponent S T τ l _ _ hfin (hJ τ)
  obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le hle
  rw [hk, pow_add, mul_comm, mul_smul, key, smul_zero]

end GlobalTheory.HubX.InvariantsNoJump
