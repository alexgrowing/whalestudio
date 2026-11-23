import Mathlib
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsComponentDim
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MultihomogeneousIdeals.CycDim
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterDivSuppAB
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.WithBotEqOfLeOfAddOneLe
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

noncomputable section

universe u

section PolynomialHeights

variable {σ : Type*} [Finite σ]

theorem ringKrullDim_mvPolynomial_dvr (O : Type*) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] :
    ringKrullDim (MvPolynomial σ O) = ((Nat.card σ + 1 : ℕ) : WithBot ℕ∞) := by
  rw [MvPolynomial.ringKrullDim_of_isNoetherianRing, IsDiscreteValuationRing.ringKrullDim_eq_one]
  push_cast
  ring

theorem height_mvPolynomial_field_of_isMaximal {k : Type*} [Field k]
    (M : Ideal (MvPolynomial σ k)) (hM : M.IsMaximal) :
    (M.height : WithBot ℕ∞) = (Nat.card σ : WithBot ℕ∞) := by
  have h := DimF.height_eq_ringKrullDim_of_forall
    (DimF.height_eq_of_isMaximal_of_field (k := k)) M hM
  rw [h, MvPolynomial.ringKrullDim_of_isNoetherianRing, ringKrullDim_eq_zero_of_field]
  simp

theorem le_height_of_isMaximal_of_uniformiser_mem {O : Type*} [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] {ϖ : O} (hϖ : Irreducible ϖ) (m : Ideal (MvPolynomial σ O))
    (hm : m.IsMaximal) (hϖm : (C ϖ : MvPolynomial σ O) ∈ m) :
    ((Nat.card σ + 1 : ℕ) : ℕ∞) ≤ m.height := by
  set p0 : Ideal (MvPolynomial σ O) := Ideal.map C (IsLocalRing.maximalIdeal O) with hp0def
  have hp0 : p0 = Ideal.span {C ϖ} := by
    rw [hp0def, hϖ.maximalIdeal_eq, Ideal.map_span, Set.image_singleton]
  let e : (MvPolynomial σ O ⧸ p0) ≃+* MvPolynomial σ (IsLocalRing.ResidueField O) :=
    (MvPolynomial.quotientEquivQuotientMvPolynomial (IsLocalRing.maximalIdeal O)).symm.toRingEquiv
  have hdom : IsDomain (MvPolynomial σ O ⧸ p0) := Function.Injective.isDomain e.toRingHom (by exact e.injective)
  have hp0p : p0.IsPrime := (Ideal.Quotient.isDomain_iff_prime p0).mp hdom
  have hle : p0 ≤ m := by
    rw [hp0]
    exact Ideal.span_le.mpr (Set.singleton_subset_iff.mpr hϖm)
  have hmb : (m.map (Ideal.Quotient.mk p0)).IsMaximal :=
    Ideal.IsMaximal.map_of_surjective_of_ker_le Ideal.Quotient.mk_surjective
      (by rw [Ideal.mk_ker]; exact hle)
  have h1 : (m.map (Ideal.Quotient.mk p0)).height = Nat.card σ := by
    rw [← e.height_map]
    have := height_mvPolynomial_field_of_isMaximal (k := IsLocalRing.ResidueField O) _
      (Ideal.map_isMaximal_of_equiv e (p := m.map (Ideal.Quotient.mk p0)))
    exact_mod_cast this
  have h0 : 1 ≤ p0.height := by
    rw [Order.one_le_iff_ne_zero, Ne, Ideal.height_eq_zero_iff_eq_bot, hp0,
      Ideal.span_singleton_eq_bot, C_eq_zero]
    exact hϖ.ne_zero
  have hfin : FiniteRingKrullDim (MvPolynomial σ O) := by
    rw [finiteRingKrullDim_iff_ne_bot_and_top, ringKrullDim_mvPolynomial_dvr]
    exact ⟨by simp, by
      rw [← WithBot.coe_natCast]
      exact ne_of_lt (WithBot.coe_lt_coe.mpr (ENat.natCast_lt_top _))⟩
  have h2 := DimF.height_add_height_map_le (q := p0) (M := m) hle
  rw [h1] at h2
  calc ((Nat.card σ + 1 : ℕ) : ℕ∞) = 1 + (Nat.card σ : ℕ∞) := by push_cast; ring
    _ ≤ p0.height + (Nat.card σ : ℕ∞) := add_le_add h0 le_rfl
    _ ≤ m.height := h2

theorem ringKrullDim_quotient_le_sub_height {A : Type*} [CommRing A] [IsNoetherianRing A]
    [FiniteRingKrullDim A] (P : Ideal A) [P.IsPrime] (N h : ℕ)
    (hmax : ∀ m : Ideal A, m.IsMaximal → m.height ≤ N) (hP : P.height = h) :
    ringKrullDim (A ⧸ P) ≤ ((N - h : ℕ) : WithBot ℕ∞) := by
  refine (ringKrullDim_le_iff_isMaximal_height_le _).mpr fun M hM => ?_
  have hc : (M.comap (Ideal.Quotient.mk P)).IsMaximal :=
    Ideal.comap_isMaximal_of_surjective _ Ideal.Quotient.mk_surjective
  have : (M.comap (Ideal.Quotient.mk P)).IsPrime := hc.isPrime
  have hPle : P ≤ M.comap (Ideal.Quotient.mk P) := fun x hx => by
    rw [Ideal.mem_comap, Ideal.Quotient.eq_zero_iff_mem.mpr hx]
    exact M.zero_mem
  have e : (M.comap (Ideal.Quotient.mk P)).map (Ideal.Quotient.mk P) = M :=
    Ideal.map_comap_of_surjective _ Ideal.Quotient.mk_surjective M
  have h2 := DimF.height_add_height_map_le (q := P) (M := M.comap (Ideal.Quotient.mk P)) hPle
  rw [e, hP] at h2
  have h3 := DimF.le_natSub_of_add_le (h2.trans (hmax _ hc))
  calc (M.height : WithBot ℕ∞) ≤ (((N - h : ℕ) : ℕ∞) : WithBot ℕ∞) := WithBot.coe_le_coe.mpr h3
    _ = ((N - h : ℕ) : WithBot ℕ∞) := WithBot.coe_natCast _

theorem withBot_eq_of_le_of_add_one_le {x : WithBot ℕ∞} {c : ℕ} (h1 : (c : WithBot ℕ∞) ≤ x)
    (h2 : x + 1 ≤ ((c + 1 : ℕ) : WithBot ℕ∞)) : x = c :=
  _root_.UpperTheory.Reformulated.B.Ydd3.withBot_eq_of_le_of_add_one_le h1 h2

end PolynomialHeights

theorem ComponentDim.proof : ComponentDim.Statement := by
  intro O _ _ _ ϖ hϖ K _ _ ι _ P d hP a f hfa hfP W hW hϖW
  have hWmin : W ∈ (P ⊔ Ideal.span {f}).minimalPrimes := by
    unfold divCycle at hW
    split_ifs at hW with h
    · exact h.1
    · exact absurd rfl hW
  have hWp : W.IsPrime := hWmin.1.1
  have hPp : P.IsPrime := hP.multiProj.isPrime
  have hPW : P ≤ W := le_sup_left.trans hWmin.1.2
  have hfW : f ∈ W := hWmin.1.2 (Ideal.mem_sup_right (Ideal.mem_span_singleton_self f))

  have hup := ReciprocityTheory.ChartRestriction.G.AI.I1.cyc_dim_add_one_le hPW hfW hfP

  have hq : W.map (Ideal.Quotient.mk P) ∈ (Ideal.span {Ideal.Quotient.mk P f}).minimalPrimes := by
    have e : Ideal.span {Ideal.Quotient.mk P f} = (Ideal.span {f}).map (Ideal.Quotient.mk P) := by
      rw [Ideal.map_span, Set.image_singleton]
    rw [e, Ideal.minimalPrimes_map_of_surjective Ideal.Quotient.mk_surjective, Ideal.mk_ker,
      sup_comm]
    exact ⟨W, hWmin, rfl⟩
  have : (W.map (Ideal.Quotient.mk P)).IsPrime := hq.1.1
  have : (Ideal.span {Ideal.Quotient.mk P f}).IsPrincipal := ⟨⟨_, rfl⟩⟩
  have hk : (W.map (Ideal.Quotient.mk P)).height ≤ 1 :=
    Ideal.height_le_one_of_isPrincipal_of_mem_minimalPrimes _ _ hq

  obtain ⟨m, hm, hWm⟩ := Ideal.exists_le_maximal W hWp.ne_top
  have : m.IsPrime := hm.isPrime
  have hmge := le_height_of_isMaximal_of_uniformiser_mem hϖ m hm (hWm hϖW)
  have hdimS := ringKrullDim_mvPolynomial_dvr (σ := Σ k, ι k) O
  have hfin : FiniteRingKrullDim (MRing ι O) := by
    rw [finiteRingKrullDim_iff_ne_bot_and_top, hdimS]
    exact ⟨by rw [← WithBot.coe_natCast]; exact WithBot.coe_ne_bot, by
      rw [← WithBot.coe_natCast]
      exact ne_of_lt (WithBot.coe_lt_coe.mpr (ENat.natCast_lt_top _))⟩
  have hmax : ∀ m' : Ideal (MRing ι O), m'.IsMaximal →
      m'.height ≤ ((Nat.card (Σ k, ι k) + 1 : ℕ) : ℕ∞) := by
    intro m' hm'
    have := Ideal.height_le_ringKrullDim_of_ne_top hm'.ne_top
    rw [hdimS] at this
    exact_mod_cast this
  have hmeq : m.height = ((Nat.card (Σ k, ι k) + 1 : ℕ) : ℕ∞) := le_antisymm (hmax m hm) hmge

  have hcat1 := DimF.height_eq_height_add_of_isRegularRing P W hPW
  have hcat2 := DimF.height_eq_height_add_of_isRegularRing W m hWm
  have hsum : P.height + (W.map (Ideal.Quotient.mk P)).height + (m.map (Ideal.Quotient.mk W)).height
      = ((Nat.card (Σ k, ι k) + 1 : ℕ) : ℕ∞) := by
    rw [← hcat1, ← hcat2, hmeq]
  have hPfin : P.height ≠ ⊤ := fun h => by
    simp only [h, top_add] at hsum; exact ENat.top_ne_natCast _ hsum
  have hafin : (W.map (Ideal.Quotient.mk P)).height ≠ ⊤ := fun h => by
    simp only [h, top_add, add_top] at hsum; exact ENat.top_ne_natCast _ hsum
  have hbfin : (m.map (Ideal.Quotient.mk W)).height ≠ ⊤ := fun h => by
    simp only [h, add_top] at hsum; exact ENat.top_ne_natCast _ hsum
  obtain ⟨h0, hh0⟩ : ∃ h0 : ℕ, P.height = h0 := ⟨_, (ENat.natCast_toNat hPfin).symm⟩
  obtain ⟨a0, ha0⟩ : ∃ a0 : ℕ, (W.map (Ideal.Quotient.mk P)).height = a0 :=
    ⟨_, (ENat.natCast_toNat hafin).symm⟩
  obtain ⟨b0, hb0⟩ : ∃ b0 : ℕ, (m.map (Ideal.Quotient.mk W)).height = b0 :=
    ⟨_, (ENat.natCast_toNat hbfin).symm⟩
  rw [hh0, ha0, hb0] at hsum
  rw [ha0] at hk
  have hsum' : h0 + a0 + b0 = Nat.card (Σ k, ι k) + 1 := by exact_mod_cast hsum
  have hk' : a0 ≤ 1 := by exact_mod_cast hk

  have hPdim := ringKrullDim_quotient_le_sub_height P (Nat.card (Σ k, ι k) + 1) h0 hmax hh0
  rw [hP.dim] at hPdim
  have hPdim' : d + 1 + Fintype.card K ≤ Nat.card (Σ k, ι k) + 1 - h0 := by exact_mod_cast hPdim

  have hlow := Ideal.height_le_ringKrullDim_of_ne_top
    (DimF.isPrime_map_mk (A := MRing ι O) (q := W) (M := m) hWm).ne_top
  rw [hb0] at hlow
  have hb' : d + Fintype.card K ≤ b0 := by omega
  have hlow' : ((d + Fintype.card K : ℕ) : WithBot ℕ∞) ≤ ringKrullDim (MRing ι O ⧸ W) :=
    le_trans (by exact_mod_cast hb') hlow
  rw [hP.dim] at hup
  exact withBot_eq_of_le_of_add_one_le hlow' (by rw [show d + Fintype.card K + 1 = d + 1 + Fintype.card K by ring]; exact hup)

end

end GroundTheory.Heights₂.Heights.NumbersDVR
