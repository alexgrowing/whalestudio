import Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.ModelFPfC

noncomputable section

namespace Formalism.MainNotions.N.Ln34.ModelFPf

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Module Formalism.MainNotions.N.Ln34 TensorProduct

section Core

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    (W : LocWach PD LL O v n)
    (T : LocLat G Qp LL O) (Pt : ZMod n → LL → (K →ₐ[Qp] LL) → Prop) (π' Eπ : LetA O n)
    (h' M σ : ℕ) (c : ZMod n) (α : FrA W π' Eπ h' M c) (β : FrB W π' Eπ h' M c)

theorem alpha_core (hfr : IsFrame W Pt π' Eπ h' M σ c α β) (hcry : IsCrys PD T.ρ)
    (hjmp : ∀ τ, JumpsInV PD T.ρ τ (Set.Icc (-(h' : ℤ)) h')) (hs : W.s = 1) {w w' : LetA O n}
    (hww : w' * w = 1) (hQ : W.Q = w * Eπ)
    (h5a : ∀ x ∈ W.Nl T (c - 1), W.Q ^ h' • W.φD T x ∈ W.N T) (hp4 : Formalism.MainNotions.DeltaInvariantLattices.p4 W Pt T)
    (hpt : ∀ ζ τ, Pt c ζ τ → ζ ^ PD.p = 1 ∧ ζ ≠ 1) (hexp : ExpansionFormLetter W T Pt)
    (x : LA W T π' c) (hx : x ∈ LamLA W T π' Eπ h' c ⊤) (hxS : x ∈ NLset W T Pt π' Eπ h' c)
    (y0 : W.DD T) (hy0 : y0 ∈ LamPS W T Eπ h' c) (hα : α T ⟨x, hx⟩ = mkP W T π' Eπ h' M c y0 hy0) :
    y0 ∈ W.N T := by
  obtain ⟨h1, h2, h3⟩ := (mem_LamPS W T Eπ h' c y0).1 hy0
  have hE2 : Eπ ^ h' • (Eπ ^ h' • y0) ∈ W.N T := Eπ_φspan W T Eπ h' c hww hQ h5a h1
  have eEQ : Eπ ^ h' = w' ^ h' * W.Q ^ h' := by
    rw [hQ, mul_pow, ← mul_assoc, ← mul_pow, hww, one_pow, one_mul]
  refine hexp c y0 ((mem_DelS W T y0).2 h2) ((mem_letS W T c y0).2 h3) ⟨2 * h', ?_⟩ ?_
  · rw [hQ, mul_pow, mul_smul, show Eπ ^ (2 * h') = Eπ ^ h' * Eπ ^ h' by rw [two_mul, pow_add],
      mul_smul]
    exact Submodule.smul_mem _ _ hE2
  · intro ζ τ hPt k hk i
    obtain ⟨hc0, hc1⟩ := levQ_pt W hs c ζ (hpt ζ τ hPt).1 (hpt ζ τ hPt).2
    obtain ⟨m, a, z, hrep, hfil⟩ := hxS
    have e1 : W.Q ^ k • (Eπ ^ h' • y0) = (w' ^ h' * W.Q ^ h') • (W.Q ^ k • y0) := by
      rw [eEQ, smul_smul, smul_smul, mul_comm (W.Q ^ k)]
    have hQΛ : W.Q ^ k • (Eπ ^ h' • y0) ∈ W.N T := e1 ▸ Submodule.smul_mem _ _ hk
    have hF : ∀ i' : ℤ, W.levN T c ζ ⟨_, hQΛ⟩ i' ∈
        Formalism.MainNotions.DeltaInvariantLattices.FilC (PD := PD) T τ ((k : ℤ) + h' - i') := by
      intro i'
      rcases lt_or_ge i' ((k : ℤ) + 4 * h') with hi | hi
      · rw [(hfr.1 T hcry hjmp).2.2.2.2.2.2.2.2 τ ζ hPt x hx y0 hy0 hα m a z hrep k hQΛ i' hi]
        refine nsmul_mem ?_ _
        have := serMul_mem (fun i => Formalism.MainNotions.DeltaInvariantLattices.FilC (PD := PD) T τ ((h' : ℤ) - i))
          (FilC_mono_shift T τ _) (W.lev c ζ (W.Q ^ k)) k
          (by rw [map_pow]; exact pow_vanish' _ hc0 k) _ (hfil τ ζ hPt) i'
        convert this using 2
        ring
      · have h0 := (Submodule.mem_inf.1 (levN_fil W T c hp4 hPt ⟨_, hQΛ⟩ i')).2
        exact FilC_anti T τ (by omega) (FilC_top T h' τ (hjmp τ) _ h0)
    have hsub : (⟨_, hQΛ⟩ : ↥(W.N T)) = (w' ^ h' * W.Q ^ h') • (⟨_, hk⟩ : ↥(W.N T)) :=
      Subtype.ext e1
    obtain ⟨m₀, hm₀⟩ := W.levN_supp T c ζ ⟨_, hk⟩
    obtain ⟨B', hB'⟩ := PowerSeries.X_dvd_iff.2 hc0
    have hw0 : PowerSeries.constantCoeff (W.lev c ζ w') ≠ 0 := by
      intro h
      have hw : PowerSeries.constantCoeff (W.lev c ζ w') *
          PowerSeries.constantCoeff (W.lev c ζ w) = 1 := by
        rw [← map_mul, ← map_mul, hww, map_one, map_one]
      rw [h, zero_mul] at hw
      exact zero_ne_one hw
    have hB0 : PowerSeries.constantCoeff B' ≠ 0 := by
      rw [hB', PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_zero_eq_constantCoeff_apply] at hc1
      exact hc1
    have eg : W.lev c ζ (w' ^ h' * W.Q ^ h') =
        PowerSeries.X ^ h' * (W.lev c ζ w' ^ h' * B' ^ h') := by
      rw [map_mul, map_pow, map_pow, hB', mul_pow]
      ring
    refine serMul_inv (fun i => Formalism.MainNotions.DeltaInvariantLattices.FilC (PD := PD) T τ ((k : ℤ) - i)) (FilC_mono_shift T τ _)
      (W.lev c ζ (w' ^ h' * W.Q ^ h')) h' ?_ ?_ (W.levN T c ζ ⟨_, hk⟩) m₀ hm₀ ?_ i
    · intro j hj
      rw [eg, PowerSeries.coeff_X_pow_mul', if_neg (by omega)]
    · rw [eg, PowerSeries.coeff_X_pow_mul', if_pos le_rfl, Nat.sub_self,
        PowerSeries.coeff_zero_eq_constantCoeff_apply, map_mul, map_pow, map_pow]
      exact mul_ne_zero (pow_ne_zero _ hw0) (pow_ne_zero _ hB0)
    · intro i''
      rw [← levN_eq_serMul, ← hsub]
      have := hF (i'' + h')
      convert this using 2
      ring

end Core

end Formalism.MainNotions.N.Ln34.ModelFPf

end
