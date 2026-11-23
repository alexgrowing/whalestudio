import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.IdMeetVolSteps

noncomputable section

namespace Formalism.L2.SG.Pf.IdMeet

attribute [local instance] Formalism.BasicNotions.Host.cmStar

open scoped Classical ENNReal
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat
open Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.PoincareInHH.Cut

theorem gcS_sub {D : D7} (X : HidaSetting D) (u : D.what₂.Word) (hK : X.LevelSubgroupCharacter) (c : X.B.I.Gf) :
    ((GcS X u hK c : Subgroup X.B.I.Ginf) : Set X.B.I.Ginf) ⊆ X.NinfU u := by
  intro s hs
  obtain ⟨γ, hγ, rfl⟩ := Subgroup.mem_map.1 hs
  exact (Subgroup.mem_prod.1 (Subgroup.mem_inf.1 hγ).2).1

theorem isSFund_conjImg {D : D7} (X : HidaSetting D) (S S' : Set X.B.I.Ginf) (Ω : Set X.B.I.Ginf) (c : X.B.I.Ginf)
    (hS : ∀ s, s ∈ S' ↔ ∃ t ∈ S, c * t * c⁻¹ = s) (hΩ : IsSFund X.B.I S Ω) :
    IsSFund X.B.I S' ((fun s => c * s * c⁻¹) '' Ω) := by
  have himg : (fun s => c * s * c⁻¹) '' Ω = (fun s => c⁻¹ * s * c) ⁻¹' Ω := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      simpa [mul_assoc] using hy
    · intro hx
      exact ⟨c⁻¹ * x * c, hx, by group⟩
  refine ⟨?_, ?_, ?_⟩
  · rw [himg]
    exact ((measurable_const_mul c⁻¹).mul_const c) hΩ.1
  · intro x
    obtain ⟨t, ht, htx⟩ := hΩ.2.1 (c⁻¹ * x * c)
    refine ⟨c * t * c⁻¹, (hS _).2 ⟨t, ht, rfl⟩, ?_⟩
    exact ⟨t * (c⁻¹ * x * c), htx, by group⟩
  · intro x hx s hs hsx
    obtain ⟨ω, hω, rfl⟩ := hx
    obtain ⟨t, ht, rfl⟩ := (hS s).1 hs
    rw [himg] at hsx
    have h1 : t * ω ∈ Ω := by
      have e : c⁻¹ * (c * t * c⁻¹ * (c * ω * c⁻¹)) * c = t * ω := by group
      have h0 : c⁻¹ * (c * t * c⁻¹ * (c * ω * c⁻¹)) * c ∈ Ω := hsx
      rw [e] at h0
      exact h0
    have := hΩ.2.2 ω hω t ht h1
    rw [this]; group

theorem volColC_of (h1 : NOinfEqC) (h2 : NOcolEqC) (h3 : GcCountC) (h4 : FundMeasEqC) (h5 : IndexVolC)
    (h6 : IndexTransferC) (h7 : ConjUC) (h8 : GcFundC) (h9 : GcConjC) (h10 : HinfConjC) : VolColC := by
  intro D X Y u ρ Ω hΩ
  let Γ : Hfin X u → Subgroup X.B.I.Ginf := fun h => GcS X u Y.hK ((h : X.B.I.Gf) * X.xu u)
  let U : Hfin X u → Subgroup X.B.I.Gf := fun h => UcS X u Y.hK ((h : X.B.I.Gf) * X.xu u)
  have hsub : ∀ h, ((Γ h : Subgroup X.B.I.Ginf) : Set X.B.I.Ginf) ⊆ X.NinfU u := fun h => gcS_sub X u Y.hK _
  have hcnt : ∀ h, Countable (Γ h) := fun h => h3 D X u Y.hK _
  let Ωh : Hfin X u → Set X.B.I.Ginf := fun h => Classical.choose (h8 D X Y u h)
  have hΩh : ∀ h, IsSFund X.B.I (Γ h) (Ωh h) := fun h => Classical.choose_spec (h8 D X Y u h)
  let F : Hfin X u → ℝ≥0∞ := fun h => X.muN u (Ωh h)
  have hF : ∀ h Ω', IsSFund X.B.I (Γ h) Ω' → X.muN u Ω' = F h := fun h Ω' hΩ' =>
    h4 D X u (Γ h) Ω' (Ωh h) (hsub h) (hcnt h) hΩ' (hΩh h)

  have hratio : ∀ g h : Hfin X u,
      F g * ((Γ h).relIndex (Γ g) : ℝ≥0∞) = F h * ((Γ g).relIndex (Γ h) : ℝ≥0∞) := by
    intro g h
    have hne1 : (Γ h ⊓ Γ g).relIndex (Γ g) ≠ 0 := by
      rw [Subgroup.inf_relIndex_right, (h6 D X u Y.hK g h).1]; exact (h6 D X u Y.hK g h).2
    have hne2 : (Γ g ⊓ Γ h).relIndex (Γ h) ≠ 0 := by
      rw [Subgroup.inf_relIndex_right, (h6 D X u Y.hK h g).1]; exact (h6 D X u Y.hK h g).2
    obtain ⟨Ω1, hΩ1, hμ1⟩ := h5 D X u (Γ g) (Γ h ⊓ Γ g) (Ωh g) inf_le_right (hsub g) (hcnt g) hne1 (hΩh g)
    obtain ⟨Ω2, hΩ2, hμ2⟩ := h5 D X u (Γ h) (Γ g ⊓ Γ h) (Ωh h) inf_le_right (hsub h) (hcnt h) hne2 (hΩh h)
    rw [inf_comm] at hΩ2
    have hc : Countable ↥(Γ h ⊓ Γ g) := by
      exact Set.countable_coe_iff.2 ((Set.countable_coe_iff.1 (hcnt g)).mono (fun x hx => (Subgroup.mem_inf.1 hx).2))
    have heq := h4 D X u (Γ h ⊓ Γ g) Ω1 Ω2 (fun x hx => hsub g (Subgroup.mem_inf.1 hx).2) hc hΩ1 hΩ2
    rw [hμ1, hμ2, Subgroup.inf_relIndex_right, Subgroup.inf_relIndex_right] at heq
    rw [mul_comm, heq, mul_comm]

  have hU : ∀ g h : Hfin X u, U (g * h) = (U h).map (MulAut.conj (g : X.B.I.Gf)).toMonoidHom := by
    intro g h
    have := h7 D X u Y.hK g ((h : X.B.I.Gf) * X.xu u)
    simp only [U, Subgroup.coe_mul, mul_assoc]
    exact this
  have hinj : ∀ g : Hfin X u, Function.Injective (MulAut.conj (g : X.B.I.Gf)).toMonoidHom :=
    fun g => (MulAut.conj (g : X.B.I.Gf)).injective
  have hidx : ∀ g h : Hfin X u, (U (g * h)).relIndex (U g) = (U h).relIndex (U 1) := by
    intro g h
    have e := hU g 1
    rw [mul_one] at e
    rw [hU g h, e, Subgroup.relIndex_map_map_of_injective _ _ (hinj g)]
  have hidx' : ∀ g h : Hfin X u, (U g).relIndex (U (g * h)) = (U 1).relIndex (U h) := by
    intro g h
    have e := hU g 1
    rw [mul_one] at e
    rw [hU g h, e, Subgroup.relIndex_map_map_of_injective _ _ (hinj g)]
  have hG : ∀ g h : Hfin X u, (Γ h).relIndex (Γ g) = (U h).relIndex (U g) := fun g h => (h6 D X u Y.hK g h).1
  have hGne : ∀ g h : Hfin X u, (Γ h).relIndex (Γ g) ≠ 0 := fun g h => by
    rw [hG]; exact (h6 D X u Y.hK g h).2

  have hmul : ∀ g h : Hfin X u, F (g * h) * F 1 = F g * F h := by
    intro g h
    have E1 := hratio g (g * h)
    have E2 := hratio 1 h
    set A : ℕ := (U h).relIndex (U 1) with hA
    set B : ℕ := (U 1).relIndex (U h) with hB
    have hA1 : (Γ (g * h)).relIndex (Γ g) = A := by
      rw [hG, hA, hidx g h]
    have hB1 : (Γ g).relIndex (Γ (g * h)) = B := by
      rw [hG, hB, hidx' g h]
    have hA2 : (Γ h).relIndex (Γ 1) = A := by rw [hG]
    have hB2 : (Γ 1).relIndex (Γ h) = B := by rw [hG]
    have hA0 : A ≠ 0 := by rw [← hA2]; exact hGne 1 h
    have hB0 : B ≠ 0 := by rw [← hB2]; exact hGne h 1
    rw [hA1, hB1] at E1
    rw [hA2, hB2] at E2
    have hAB0 : ((A : ℝ≥0∞) * B) ≠ 0 := mul_ne_zero (by exact_mod_cast hA0) (by exact_mod_cast hB0)
    have hABt : ((A : ℝ≥0∞) * B) ≠ ⊤ := ENNReal.mul_ne_top (ENNReal.natCast_ne_top A) (ENNReal.natCast_ne_top B)
    refine (ENNReal.mul_left_inj hAB0 hABt).1 ?_
    calc F (g * h) * F 1 * (A * B) = (F (g * h) * B) * (F 1 * A) := by ring
      _ = (F g * A) * (F h * B) := by rw [← E1, E2]
      _ = F g * F h * (A * B) := by ring

  have hinv : ∀ (γ : Gam X u) (h : Hfin X u) (κ : Ku X u Y.hK), F (iotaF X u γ * h * (κ : Hfin X u)) = F h := by
    intro γ h κ
    set c : X.B.I.Ginf := (γ : X.B.I.GA).1 with hc
    have hcH : c ∈ Hinf X u := (Subgroup.mem_prod.1 (Subgroup.mem_inf.1 γ.2).2).1
    have hset := h9 D X u Y.hK γ h κ
    have hS : ∀ s, s ∈ ((Γ (iotaF X u γ * h * (κ : Hfin X u)) : Subgroup X.B.I.Ginf) : Set X.B.I.Ginf) ↔
        ∃ t ∈ ((Γ h : Subgroup X.B.I.Ginf) : Set X.B.I.Ginf), c * t * c⁻¹ = s := by
      intro s
      have := Set.ext_iff.1 hset s
      simpa [Γ] using this
    have hfund := isSFund_conjImg X _ _ (Ωh h) c hS (hΩh h)
    rw [← hF _ _ hfund]
    exact h10 D X u c hcH (Ωh h) (hΩh h).1

  have hfin : (Set.range F).Finite := by
    refine (Set.finite_range (fun ρ : (Y.cs u).Cl => F ((Y.cs u).h ρ))).subset ?_
    rintro _ ⟨h, rfl⟩
    obtain ⟨ρ, ⟨γ, κ, hh⟩, -⟩ := Y.colReps u h
    exact ⟨ρ, by rw [hh, hinv]⟩

  have hconst : ∀ h, F h = F 1 := by
    intro h
    have E := hratio 1 h
    have ha : (Γ h).relIndex (Γ 1) ≠ 0 := hGne 1 h
    have hb : (Γ 1).relIndex (Γ h) ≠ 0 := hGne h 1
    have ha' : ((Γ h).relIndex (Γ 1) : ℝ≥0∞) ≠ 0 := by exact_mod_cast ha
    have hb' : ((Γ 1).relIndex (Γ h) : ℝ≥0∞) ≠ 0 := by exact_mod_cast hb
    by_cases h0 : F 1 = 0
    · rw [h0, zero_mul] at E
      rcases mul_eq_zero.1 E.symm with e | e
      · rw [e, h0]
      · exact absurd e hb'
    by_cases ht : F 1 = ⊤
    · rw [ht, ENNReal.top_mul ha'] at E
      rcases ENNReal.mul_eq_top.1 E.symm with ⟨-, e⟩ | ⟨e, -⟩
      · exact absurd e (ENNReal.natCast_ne_top _)
      · rw [e, ht]

    have hpos : ∀ k, F k ≠ 0 ∧ F k ≠ ⊤ := by
      intro k
      have Ek := hratio 1 k
      have hak : ((Γ k).relIndex (Γ 1) : ℝ≥0∞) ≠ 0 := by exact_mod_cast hGne 1 k
      have hbk : ((Γ 1).relIndex (Γ k) : ℝ≥0∞) ≠ 0 := by exact_mod_cast hGne k 1
      constructor
      · intro e; rw [e, zero_mul] at Ek
        rcases mul_eq_zero.1 Ek with e' | e'
        · exact h0 e'
        · exact hak e'
      · intro e; rw [e, ENNReal.top_mul hbk] at Ek
        rcases ENNReal.mul_eq_top.1 Ek with ⟨-, e'⟩ | ⟨e', -⟩
        · exact ENNReal.natCast_ne_top _ e'
        · exact ht e'
    let q : Hfin X u → ℝ := fun k => (F k).toReal / (F 1).toReal
    have hF1 : 0 < (F 1).toReal := ENNReal.toReal_pos h0 ht
    have hq : ∀ g k, q (g * k) = q g * q k := by
      intro g k
      have := congrArg ENNReal.toReal (hmul g k)
      rw [ENNReal.toReal_mul, ENNReal.toReal_mul] at this
      simp only [q]
      field_simp
      linarith [this]
    have hqpow : ∀ n : ℕ, q (h ^ n) = q h ^ n := by
      intro n
      induction n with
      | zero => simp [q, hF1.ne']
      | succ n ih => rw [pow_succ, hq, ih, pow_succ]
    have hqpos : 0 < q h := div_pos (ENNReal.toReal_pos (hpos h).1 (hpos h).2) hF1
    have hq1 : q h = 1 := by
      by_contra hne
      have hinjq : Function.Injective (fun n : ℕ => q h ^ n) := pow_right_injective₀ hqpos hne
      have hrange : (Set.range (fun n : ℕ => q h ^ n)).Finite := by
        refine ((hfin.image (fun x : ℝ≥0∞ => x.toReal / (F 1).toReal))).subset ?_
        rintro _ ⟨n, rfl⟩
        exact ⟨F (h ^ n), ⟨h ^ n, rfl⟩, by simp only [q] at hqpow; exact hqpow n⟩
      exact Set.infinite_range_of_injective hinjq hrange
    have : (F h).toReal = (F 1).toReal := by
      have := hq1; simp only [q] at this
      field_simp at this; linarith
    exact (ENNReal.toReal_eq_toReal_iff' (hpos h).2 ht).1 this

  have hρ : IsSFund X.B.I (Γ ((Y.cs u).h ρ)) Ω := by
    have := h2 D X Y u ρ
    rw [this] at hΩ
    exact hΩ
  have h1' : IsSFund X.B.I (Γ 1) (Y.FN u) := by
    have e := h1 D X u Y.hK
    have hFN := Y.FN_fund u
    rw [e] at hFN
    simpa [Γ] using hFN
  rw [hF _ _ hρ, hF _ _ h1', hconst]

end Formalism.L2.SG.Pf.IdMeet
