import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.DecompositionInvariantsCondition
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CLLUnitIntervalLe
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PadicValNatFinrankKs

open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Module

namespace GlobalTheory.HubX

theorem window_cLL_of_jumps_level_one (S : LocalSituation.Sit) (Y : LocLat S.G S.Qp S.LL S.O) (l h r n v : ℕ)
    [CharZero S.Qp] [FiniteDimensional S.Qp S.K] (hl : l.Prime)
    (hcard : Nat.card (S.K →ₐ[S.Qp] S.LL) = finrank S.Qp S.K) (hn : finrank S.Qp S.K ≤ n) (hr : 1 ≤ r)
    (hv : v ≤ LocalSituation.mN l 1 (h + h) - 1)
    (hU : ∀ τ : S.K →ₐ[S.Qp] S.LL, ∃ U : Finset ℤ, U.card ≤ r ∧ (∀ u ∈ U, -(h : ℤ) ≤ u ∧ u ≤ h) ∧
      ∀ a, IsJumpV S.PD Y.ρ τ a → a ∈ U) :
    (∀ a ∈ LocalSituation.Jset S Y, -(h : ℤ) ≤ a ∧ a ≤ h) ∧
      LocalSituation.cLL l (LocalSituation.mN l 1 (h + h)) v (LocalSituation.Jset S Y) 0 1 ≤ 5 + Nat.log l (2 * h) + n * r * (4 + 2 * Nat.log l (2 * h)) := by
  classical
  choose U hUc hUb hUj using hU
  have hpos : 0 < finrank S.Qp S.K := finrank_pos
  have hfin : Finite (S.K →ₐ[S.Qp] S.LL) := Nat.finite_of_card_ne_zero (by omega)
  letI : Fintype (S.K →ₐ[S.Qp] S.LL) := Fintype.ofFinite _
  have hsub : LocalSituation.Jset S Y ⊆ ((Finset.univ.biUnion U : Finset ℤ) : Set ℤ) := by
    intro a ha
    obtain ⟨τ, hτ⟩ := GlobalTheory.HubLoc.jump_of_total S.PD Y.ρ hcard a ha
    exact Finset.mem_coe.2 (Finset.mem_biUnion.2 ⟨τ, Finset.mem_univ _, hUj τ a hτ⟩)
  have hb : ∀ u ∈ Finset.univ.biUnion U, -(h : ℤ) ≤ u ∧ u ≤ h := by
    intro u hu
    obtain ⟨τ, -, hτ⟩ := Finset.mem_biUnion.1 hu
    exact hUb τ u hτ
  have hc : (Finset.univ.biUnion U).card ≤ n * r := by
    refine (Finset.card_biUnion_le_card_mul _ _ r fun τ _ => hUc τ).trans (Nat.mul_le_mul_right _ ?_)
    rw [Finset.card_univ, ← Nat.card_eq_fintype_card, hcard]
    exact hn
  exact ⟨fun a ha => hb a (Finset.mem_coe.1 (hsub ha)),
    GlobalTheory.HubLoc.cLL_unit_interval_le l h (n * r) v _ _ hl (Nat.mul_pos (by omega) hr) hsub hc hb hv⟩

theorem cH0all_le_of_jumps_at_embeddings : ∀ (LT : LocTheory) (HW : HWOf LT) (AI : ∀ (l : ℕ) [Fact l.Prime], LocAinf l (LT l)) (l : ℕ) [Fact l.Prime] (K LL : FinExt l) (hs : Good K 1 LL) (h r n : ℕ) (T : LocLat (LocalSituation.sit LT HW l (AI l) K 1 LL hs).G (LocalSituation.sit LT HW l (AI l) K 1 LL hs).Qp (LocalSituation.sit LT HW l (AI l) K 1 LL hs).LL (LocalSituation.sit LT HW l (AI l) K 1 LL hs).O), K.1 ≤ MaximalUnramifiedExtension l → finrank ℚ_[l] ↥K.1 ≤ n → 1 ≤ r → (∀ τ, ∃ U : Finset ℤ, U.card ≤ r ∧ (∀ u ∈ U, -(h : ℤ) ≤ u ∧ u ≤ h) ∧ ∀ a, IsJumpV (LocalSituation.sit LT HW l (AI l) K 1 LL hs).PD T.ρ τ a → a ∈ U) → (∀ a ∈ LocalSituation.Jset (LocalSituation.sit LT HW l (AI l) K 1 LL hs) T, -(h : ℤ) ≤ a ∧ a ≤ h) ∧ GlobalTheory.HubX.invariantsCountConstant LT HW AI l K 1 LL hs h h T ≤ 5 + Nat.log l (2 * h) + n * r * (4 + 2 * Nat.log l (2 * h)) := by
  intro LT HW AI l _ K LL hs h r n T hK hn hr hU
  have hl : l.Prime := Fact.out

  have hK1 : K.1 ≤ Ks K 1 := GlobalTheory.HubLoc.le_Ks_one_of_Kur K hK
  have hsplit : ∀ (τ : ↥K.1 →ₐ[ℚ_[l]] Om l) (x : ↥K.1), τ x ∈ LL.1 := by
    intro τ x
    have e := hs.2.2.2 ((τ.liftNormal (Om l)).comp (Ks K 1).val) ⟨x.1, hK1 x.2⟩
    have e2 : τ.liftNormal (Om l) (algebraMap ↥K.1 (Om l) x) = algebraMap (Om l) (Om l) (τ x) :=
      AlgHom.liftNormal_commutes τ (Om l) x
    have e3 : ((τ.liftNormal (Om l)).comp (Ks K 1).val) ⟨x.1, hK1 x.2⟩ = τ x := e2
    rwa [e3] at e
  have hcard : Nat.card (↥K.1 →ₐ[ℚ_[l]] ↥LL.1) = finrank ℚ_[l] ↥K.1 := GlobalTheory.HubLoc.card_emb K LL hsplit
  have := K.2
  have hm : 0 < LocalSituation.mN l 1 (h + h) := by unfold LocalSituation.mN; omega
  obtain ⟨h1, h2⟩ := GlobalTheory.HubLoc.padicValNat_finrank_Ks l K
  have e1 := h1 _ hm
  have e2 := h2 hK
  have hv : padicValNat l (finrank ℚ_[l] ↥(Ks K (LocalSituation.mN l 1 (h + h)))) - padicValNat l (finrank ℚ_[l] ↥K.1) ≤
      LocalSituation.mN l 1 (h + h) - 1 := by omega
  haveI : CharZero (LocalSituation.sit LT HW l (AI l) K 1 LL hs).Qp := (inferInstance : CharZero ℚ_[l])
  haveI : FiniteDimensional (LocalSituation.sit LT HW l (AI l) K 1 LL hs).Qp (LocalSituation.sit LT HW l (AI l) K 1 LL hs).K :=
    (inferInstance : FiniteDimensional ℚ_[l] ↥K.1)
  exact window_cLL_of_jumps_level_one (LocalSituation.sit LT HW l (AI l) K 1 LL hs) T l h r n _ hl hcard hn hr hv hU

end GlobalTheory.HubX
