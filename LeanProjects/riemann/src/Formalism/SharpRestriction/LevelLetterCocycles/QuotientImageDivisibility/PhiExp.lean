import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.QuotientImageDivisibility.IsExpSmulA

noncomputable section
open Classical

namespace Formalism.MainNotions.N.Pv.LocalLengthBound

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct Formalism.MainNotions.N.Pv.LocalLengthBound.Ser

section Phi

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ} (W : LocWach PD LL O v n)
    {Zl Ai : Type} [CommRing Zl] [CommRing Ai] [Algebra Zl O]
    [Algebra Zl Ai] {RW : Type} [CommRing RW] [Algebra O RW] {inclR : (O ⊗[Zl] Ai) →ₐ[O] RW}
    {φR : RW →ₐ[O] RW} {gR : G → (RW →ₐ[O] RW)} {πA : O ⊗[Zl] Ai}
    {E : EtTie W (O ⊗[Zl] Ai) RW inclR φR gR πA} {ιdR : Ai →+* BdR} {p1 : Ai} {tS zS : BdR}

theorem phi_exp (hs : W.s = 1) (C : CmpTie W E ιdR p1 tS zS)
    {Pt : ZMod n → LL → (K →ₐ[Qp] LL) → Prop} (h4W : Formalism.MainNotions.DeltaInvariantLattices.P4W W Pt)
    (T : LocLat G Qp LL O) (hT : IsCrys PD T.ρ) (i : ZMod n) {ζ : LL} (hζ : IsPrimitiveRoot ζ PD.p)
    (y : W.DD T) (hy : y ∈ W.N T) (hyl : (letE (i - 1) : LetA O n) • y = y) :
    ∃ d : ℤ → T.V ⊗[Qp] BdR, Formalism.MainNotions.RamifiedCoefficientChains.Sh.IsExp W T i ζ (W.φD T y) d ∧ (∀ k : ℤ, k < 0 → d k = 0) ∧
      d 0 = ιV PD (LL := LL) (V := T.V) (φVB PD (LL := LL) (V := T.V) (W.cmp T ⟨y, hy⟩)) := by
  have hp := p_ne_zero_LL W
  obtain ⟨u, hu0, hq⟩ := MC.lev_q_eq W i hζ hp
  have hQ : W.lev i ζ W.Q = PowerSeries.X * u := by rw [MC.Q_eq_q W hs]; exact hq
  obtain ⟨m, hm⟩ := W.N_φ T y hy
  have hm' : W.Q ^ m • W.φD T y ∈ W.N T := hm
  set y' : ↥(W.N T) := ⟨y, hy⟩ with hy'

  have hcX : PowerSeries.constantCoeff (W.lev (i - 1) 1 W.X) = 0 := by
    have e : W.X = letπ := by simp [LocWach.X, hs]
    rw [e, MC.cc_lev_pi W (i - 1) 1 ⟨0, by rw [pow_zero]; exact IsPrimitiveRoot.one⟩, sub_self]
  have hneg : ∀ k : ℤ, k < 0 → C.levB T (i - 1) 1 y' k = 0 := by
    intro k hk
    have h0 := (((h4W T hT).1 (i - 1) 1 ⟨0, by simp⟩ hcX).1 y' k).2 hk
    rw [C.levN_eq] at h0
    exact Formalism.MainNotions.UnusedSlot80.LevR.ιV_inj (PD := PD) (V := T.V) (h0.trans (map_zero _).symm)
  have hζp : ζ ^ PD.p = 1 := hζ.pow_eq_one
  have hφrule : ∀ k : ℤ, W.levN T i ζ ⟨W.Q ^ m • W.φD T y, hm'⟩ k =
      ιV PD (LL := LL) (V := T.V) (∑ᶠ j : ℕ, PowerSeries.coeff j (W.lev i ζ (W.Q ^ m)) •
        (((PD.p : LL) ^ (k - (j : ℤ))) •
          φVB PD (LL := LL) (V := T.V) (C.levB T (i - 1) 1 y' (k - (j : ℤ))))) := by
    intro k
    rw [C.levN_eq, C.levB_φ T hT i ζ ⟨1, by rwa [pow_one]⟩ y' m hm' k, hζp]
  have hcoef : ∀ j : ℕ, j < m → PowerSeries.coeff j (W.lev i ζ (W.Q ^ m)) = 0 := by
    intro j hj
    rw [map_pow, hQ, mul_pow, PowerSeries.coeff_X_pow_mul', if_neg (by omega)]
  have hterm0 : ∀ (k : ℤ) (j : ℕ), (j < m ∨ k < (j : ℤ)) →
      PowerSeries.coeff j (W.lev i ζ (W.Q ^ m)) • (((PD.p : LL) ^ (k - (j : ℤ))) •
        φVB PD (LL := LL) (V := T.V) (C.levB T (i - 1) 1 y' (k - (j : ℤ)))) = 0 := by
    intro k j h
    rcases h with h | h
    · rw [hcoef j h, zero_smul]
    · rw [hneg _ (by omega), map_zero, smul_zero, smul_zero]
  set e : ℤ → T.V ⊗[Qp] BdR := W.levN T i ζ ⟨W.Q ^ m • W.φD T y, hm'⟩ with he
  have he_low : ∀ k : ℤ, k < m → e k = 0 := by
    intro k hk
    rw [hφrule, finsum_eq_zero_of_forall_eq_zero, map_zero]
    intro j
    by_cases hj : j < m
    · exact hterm0 k j (Or.inl hj)
    · exact hterm0 k j (Or.inr (by omega))
  have he_m : e m = (PowerSeries.constantCoeff u) ^ m •
      ιV PD (LL := LL) (V := T.V) (φVB PD (LL := LL) (V := T.V) (C.levB T (i - 1) 1 y' 0)) := by
    rw [hφrule, finsum_eq_single _ m (fun j hj => ?_)]
    · rw [map_pow, hQ, mul_pow, PowerSeries.coeff_X_pow_mul', if_pos le_rfl, Nat.sub_self,
        PowerSeries.coeff_zero_eq_constantCoeff_apply, map_pow, sub_self, zpow_zero, one_smul,
        map_smul]
    · rcases Nat.lt_or_gt_of_ne hj with h | h
      · exact hterm0 _ j (Or.inl h)
      · exact hterm0 _ j (Or.inr (by exact_mod_cast h))

  set e' : ℤ → T.V ⊗[Qp] BdR := fun k => e (k + m) with he'
  have hLBe' : LB 0 e' := fun k hk => he_low _ (by omega)
  have huK : PowerSeries.constantCoeff (u ^ m) ≠ 0 := by rw [map_pow]; exact pow_ne_zero _ hu0
  set d : ℤ → T.V ⊗[Qp] BdR := smulS (u ^ m)⁻¹ e' with hd
  have hLBd : LB 0 d := LB_smulS hLBe' _
  have hde : smulS ((PowerSeries.X * u) ^ m) d = e := by
    rw [mul_pow, smulS_mul hLBd, hd, ← smulS_mul hLBe', PowerSeries.mul_inv_cancel _ huK,
      smulS_one hLBe', smulS_X_pow hLBe']
    funext k
    simp [he']
  refine ⟨d, ⟨⟨0, hLBd⟩, W.Q ^ m, hm', ?_, fun k => ?_⟩, fun k hk => hLBd k hk, ?_⟩
  · rw [map_pow, hQ]
    exact pow_ne_zero _ (mul_ne_zero PowerSeries.X_ne_zero
      (fun h0 => hu0 (by rw [h0, map_zero])))
  · rw [map_pow, hQ, conv_eq, hde]
  ·
    have h1 : d 0 = PowerSeries.constantCoeff ((u ^ m)⁻¹) • e' 0 := by
      rw [hd, smulS_eq_sum hLBe' _ 0 1 (by norm_num)]
      simp
    rw [h1]
    simp only [he']
    rw [zero_add, he_m, smul_smul, PowerSeries.constantCoeff_inv, map_pow, inv_mul_cancel₀
      (pow_ne_zero _ hu0), one_smul]
    congr 2
    rw [← C.cmp_eq T hT (i - 1) y']
    congr 1
    exact Subtype.ext hyl

end Phi

end Formalism.MainNotions.N.Pv.LocalLengthBound
