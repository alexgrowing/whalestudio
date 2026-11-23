import Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.ModelFPfD

noncomputable section

namespace Formalism.MainNotions.N.Ln34.ModelFPf

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Module Formalism.MainNotions.N.Ln34 TensorProduct

section Core2

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

theorem beta_core (hfr : IsFrame W Pt π' Eπ h' M σ c α β) (hcry : IsCrys PD T.ρ)
    (hjmp : ∀ τ, JumpsInV PD T.ρ τ (Set.Icc (-(h' : ℤ)) h')) (hs : W.s = 1) {w w' : LetA O n}
    (hww : w' * w = 1) (hQ : W.Q = w * Eπ) (hp4 : Formalism.MainNotions.DeltaInvariantLattices.p4 W Pt T)
    (hpt : ∀ ζ τ, Pt c ζ τ → ζ ^ PD.p = 1 ∧ ζ ≠ 1)
    (y : W.DD T) (hy : y ∈ LamPS W T Eπ h' c) (hyN : y ∈ W.N T) (x : LA W T π' c)
    (hx : x ∈ LamLA W T π' Eπ h' c ⊤) (hβ : β T ⟨y, hy⟩ = mkLA W T π' Eπ h' M c x hx) :
    x ∈ NLset W T Pt π' Eπ h' c := by
  obtain ⟨m, a, z, hz, heq⟩ := range_rep W T π' c _ hx
  have hrep : IsRepL W T π' Eπ h' c x a z := ⟨hz, heq⟩
  refine ⟨m, a, z, hrep, ?_⟩
  intro τ ζ hPt i
  have hzN : ∀ j, z j ∈ W.N T := fun j => ((mem_NcS W T _ _).1 (hz j)).1
  have hα := (hfr.1 T hcry hjmp).2.2.2.1 y hy x hx hβ
  have hcE := levE_zero W Eπ c hs hww hQ ζ (hpt ζ τ hPt).1 (hpt ζ τ hPt).2
  rcases lt_or_ge i (4 * h') with hi | hi
  · have hpy : ((PD.p : ℕ) : O) ^ (2 * σ) • y ∈ W.N T := Submodule.smul_of_tower_mem _ _ hyN
    have hk : W.Q ^ 0 • (Eπ ^ h' • (((PD.p : ℕ) : O) ^ (2 * σ) • y)) ∈ W.N T := by
      rw [pow_zero, one_smul]
      exact Submodule.smul_mem _ _ hpy
    have hexp := (hfr.1 T hcry hjmp).2.2.2.2.2.2.2.2 τ ζ hPt x hx _ _ hα m a z hrep 0 hk i
      (by simpa using hi)
    have hl1 : W.lev c ζ (W.Q ^ 0) = 1 := by rw [pow_zero, map_one]
    rw [hl1, serMul_one] at hexp
    have hsub : (⟨_, hk⟩ : ↥(W.N T)) = Eπ ^ h' • (⟨_, hpy⟩ : ↥(W.N T)) :=
      Subtype.ext (by
        show W.Q ^ 0 • (Eπ ^ h' • (((PD.p : ℕ) : O) ^ (2 * σ) • y)) =
          Eπ ^ h' • (((PD.p : ℕ) : O) ^ (2 * σ) • y)
        rw [pow_zero, one_smul])
    have hL : W.levN T c ζ ⟨_, hk⟩ i ∈ Formalism.MainNotions.DeltaInvariantLattices.FilC (PD := PD) T τ ((h' : ℤ) - i) := by
      rw [hsub, levN_eq_serMul]
      have := serMul_mem (fun i => Formalism.MainNotions.DeltaInvariantLattices.FilC (PD := PD) T τ (0 - i)) (FilC_mono_shift T τ 0)
        (W.lev c ζ (Eπ ^ h')) h' (by rw [map_pow]; exact pow_vanish' _ hcE h') _
        (fun i => by
          have := (Submodule.mem_inf.1 (levN_fil W T c hp4 hPt ⟨_, hpy⟩ i)).2
          simpa using this) i
      convert this using 2
      ring
    rw [hexp, ← Nat.cast_smul_eq_nsmul LL] at hL
    exact (Submodule.smul_mem_iff _ (by rw [Nat.cast_pow]; exact pow_ne_zero _ (p_ne_zero W))).1 hL
  · exact FilC_anti T τ (by omega) (ιDi_le_top W T h' c hp4 hPt (hjmp τ) (expS_mem W T c hp4 hPt _ z hzN i))

theorem JLA_le (hs : W.s = 1) {w w' : LetA O n} (hww : w' * w = 1) (hQ : W.Q = w * Eπ)
    (hp4 : Formalism.MainNotions.DeltaInvariantLattices.p4 W Pt T) (hpt : ∀ ζ τ, Pt c ζ τ → ζ ^ PD.p = 1 ∧ ζ ≠ 1)
    (hjmp : ∀ τ, JumpsInV PD T.ρ τ (Set.Icc (-(h' : ℤ)) h')) (hπΔ : π' ∈ W.AΔ) (hEΔ : Eπ ∈ W.AΔ)
    (j : ℕ) (hj : j ≤ M) : JLA W T π' Eπ h' M c ≤ piNL W T Pt π' Eπ h' c j := by
  intro u hu
  obtain ⟨v, hv, rfl⟩ := Submodule.mem_map.1 hu
  obtain ⟨m, a, z, hz, rfl⟩ := range_rep W T π' c v hv
  have hb : π' ^ (M - j) * Eπ ^ (3 * h') ∈ W.AΔ :=
    W.AΔ.mul_mem (W.AΔ.pow_mem hπΔ _) (W.AΔ.pow_mem hEΔ _)
  refine ⟨smulLA W T π' c (π' ^ (M - j) * Eπ ^ (3 * h')) (∑ k, algebraMap (LetA O n) W.EE
    ((letE c : LetA O n) * (a k : LetA O n)) ⊗ₜ mkL W T π' c (z k) (hz k)), ?_, ?_⟩
  · apply Submodule.subset_span
    refine ⟨m, fun k => ⟨Eπ ^ h' * ((π' ^ (M - j) * Eπ ^ (3 * h')) * a k),
      W.AΔ.mul_mem (W.AΔ.pow_mem hEΔ _) (W.AΔ.mul_mem hb (a k).2)⟩, z, ⟨hz, ?_⟩, ?_⟩
    · rw [smulLA_rep, smulLA_rep]
    · intro τ ζ hPt i
      have hzN : ∀ k, z k ∈ W.N T := fun k => ((mem_NcS W T _ _).1 (hz k)).1
      have hcE := levE_zero W Eπ c hs hww hQ ζ (hpt ζ τ hPt).1 (hpt ζ τ hPt).2
      rcases lt_or_ge i (4 * h') with hi | hi
      · unfold expS serC
        refine Submodule.sum_mem _ fun k _ => ?_
        split_ifs with h0
        · have e : Eπ ^ h' * ((π' ^ (M - j) * Eπ ^ (3 * h')) * (a k : LetA O n)) =
              Eπ ^ (4 * h') * (π' ^ (M - j) * a k) := by ring
          show PowerSeries.coeff i.toNat (W.lev c ζ (Eπ ^ h' * ((π' ^ (M - j) * Eπ ^ (3 * h')) *
            (a k : LetA O n)))) • valAt W T c ζ (z k) ∈ _
          rw [e, map_mul, map_pow, pow_vanish _ hcE _ _ _ (by omega), zero_smul]
          exact Submodule.zero_mem _
        · exact Submodule.zero_mem _
      · exact FilC_anti T τ (by omega)
          (ιDi_le_top W T h' c hp4 hPt (hjmp τ) (expS_mem W T c hp4 hPt _ z hzN i))
  · show smulLA W T π' c (π' ^ j) (smulLA W T π' c _ _) = _
    rw [smulLA_smulLA, ← mul_assoc, ← pow_add, Nat.add_sub_cancel' hj]

end Core2

end Formalism.MainNotions.N.Ln34.ModelFPf

end
