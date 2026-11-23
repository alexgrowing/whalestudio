import Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.ModelFPfB
import Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.ExtPfMultVEqZero

noncomputable section

namespace Formalism.MainNotions.N.Ln34.ModelFPf

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Module Formalism.MainNotions.N.Ln34 TensorProduct

section Exp

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    (W : LocWach PD LL O v n)
    (T : LocLat G Qp LL O) (π' Eπ : LetA O n) (h' : ℕ) (c : ZMod n)

theorem FilC_succ_le (τ : K →ₐ[Qp] LL) (a : ℤ) :
    Formalism.MainNotions.DeltaInvariantLattices.FilC (PD := PD) T τ (a + 1) ≤ Formalism.MainNotions.DeltaInvariantLattices.FilC (PD := PD) T τ a := by
  unfold Formalism.MainNotions.DeltaInvariantLattices.FilC
  exact sup_le_sup_right (ExtPf.extPf_fildR_succ_le PD T.ρ τ a) _

theorem FilC_anti (τ : K →ₐ[Qp] LL) : Antitone fun a => Formalism.MainNotions.DeltaInvariantLattices.FilC (PD := PD) T τ a :=
  antitone_int_of_succ_le (fun a => FilC_succ_le T τ a)

theorem FilC_mono_shift (τ : K →ₐ[Qp] LL) (b : ℤ) :
    Monotone fun i : ℤ => Formalism.MainNotions.DeltaInvariantLattices.FilC (PD := PD) T τ (b - i) :=
  fun i j hij => FilC_anti T τ (by omega : b - j ≤ b - i)

theorem FilC_top (τ : K →ₐ[Qp] LL) (hj : JumpsInV PD T.ρ τ (Set.Icc (-(h' : ℤ)) h')) (b : ℤ) :
    Formalism.MainNotions.DeltaInvariantLattices.FilC (PD := PD) T τ b ≤ Formalism.MainNotions.DeltaInvariantLattices.FilC (PD := PD) T τ (-(h' : ℤ)) := by
  rcases le_or_gt (-(h' : ℤ)) b with hb | hb
  · exact FilC_anti T τ hb
  · have key : ∀ d : ℕ, FildR PD T.ρ τ (-(h' : ℤ) - (d : ℤ)) = FildR PD T.ρ τ (-(h' : ℤ)) := by
      intro d
      induction d with
      | zero => simp
      | succ d ih =>
        rw [← ih]
        have hnj : ¬ IsJumpV PD T.ρ τ (-(h' : ℤ) - ((d + 1 : ℕ) : ℤ)) := fun hJ => by
          have := (hj _ hJ).1
          push_cast at this
          omega
        unfold IsJumpV at hnj
        rw [not_not] at hnj
        have e : -(h' : ℤ) - ((d + 1 : ℕ) : ℤ) + 1 = -(h' : ℤ) - (d : ℤ) := by push_cast; ring
        rw [e] at hnj
        exact hnj.symm
    have := key ((-(h' : ℤ) - b).toNat)
    rw [show -(h' : ℤ) - (((-(h' : ℤ) - b).toNat : ℕ) : ℤ) = b by omega] at this
    unfold Formalism.MainNotions.DeltaInvariantLattices.FilC
    rw [this]

include W in
theorem p_ne_zero : (PD.p : LL) ≠ 0 := by
  intro h
  have := W.v_l
  rw [h, AddValuation.map_zero] at this
  exact WithTop.top_ne_coe this

theorem pow_vanish (g : PowerSeries LL) (hg : PowerSeries.constantCoeff g = 0) (m : ℕ)
    (a : PowerSeries LL) : ∀ j < m, PowerSeries.coeff j (g ^ m * a) = 0 := by
  intro j hj
  have hX : (PowerSeries.X : PowerSeries LL) ∣ g := PowerSeries.X_dvd_iff.mpr hg
  obtain ⟨h, hh⟩ := pow_dvd_pow_of_dvd hX m
  rw [hh, mul_assoc, PowerSeries.coeff_X_pow_mul', if_neg (by omega)]

theorem pow_vanish' (g : PowerSeries LL) (hg : PowerSeries.constantCoeff g = 0) (m : ℕ) :
    ∀ j < m, PowerSeries.coeff j (g ^ m) = 0 := by
  intro j hj
  simpa using pow_vanish g hg m 1 j hj

variable {Pt : ZMod n → LL → (K →ₐ[Qp] LL) → Prop}

theorem levN_fil (hp4 : Formalism.MainNotions.DeltaInvariantLattices.p4 W Pt T) {ζ : LL} {τ : K →ₐ[Qp] LL} (hPt : Pt c ζ τ)
    (x : ↥(W.N T)) (k : ℤ) :
    W.levN T c ζ x k ∈ Formalism.MainNotions.DeltaInvariantLattices.ιDi W T c ⊓ Formalism.MainNotions.DeltaInvariantLattices.FilC (PD := PD) T τ (-k) := by
  rw [← levN_letE]
  exact (hp4.2 c ζ τ hPt).2.1 x k

theorem ιDi_le_top (hp4 : Formalism.MainNotions.DeltaInvariantLattices.p4 W Pt T) {ζ : LL} {τ : K →ₐ[Qp] LL} (hPt : Pt c ζ τ)
    (hj : JumpsInV PD T.ρ τ (Set.Icc (-(h' : ℤ)) h')) :
    Formalism.MainNotions.DeltaInvariantLattices.ιDi W T c ≤ Formalism.MainNotions.DeltaInvariantLattices.FilC (PD := PD) T τ (-(h' : ℤ)) := by
  rw [← (hp4.2 c ζ τ hPt).1.2]
  refine Submodule.span_le.2 ?_
  rintro _ ⟨x, k, hk, rfl⟩
  exact FilC_top T h' τ hj _ (Submodule.mem_inf.1 (levN_fil W T c hp4 hPt ⟨_, hk⟩ k)).2

theorem valAt_mem (hp4 : Formalism.MainNotions.DeltaInvariantLattices.p4 W Pt T) {ζ : LL} {τ : K →ₐ[Qp] LL} (hPt : Pt c ζ τ)
    {x : W.DD T} (hx : x ∈ W.N T) : valAt W T c ζ x ∈ Formalism.MainNotions.DeltaInvariantLattices.ιDi W T c := by
  classical
  unfold valAt
  split_ifs with h
  · exact Submodule.smul_mem _ _ ((hp4.2 c ζ τ hPt).1.1 ⟨x, hx⟩ _ (Nat.find_spec h) _).1
  · exact Submodule.zero_mem _

theorem expS_mem (hp4 : Formalism.MainNotions.DeltaInvariantLattices.p4 W Pt T) {ζ : LL} {τ : K →ₐ[Qp] LL} (hPt : Pt c ζ τ) {m : ℕ}
    (a : Fin m → LetA O n) (y : Fin m → W.DD T) (hy : ∀ j, y j ∈ W.N T) (i : ℤ) :
    expS W T c ζ a y i ∈ Formalism.MainNotions.DeltaInvariantLattices.ιDi W T c := by
  unfold expS serC
  refine Submodule.sum_mem _ fun j _ => ?_
  split_ifs
  · exact Submodule.smul_mem _ _ (valAt_mem W T c hp4 hPt (hy j))
  · exact Submodule.zero_mem _

theorem levE_zero (hs : W.s = 1) {w w' : LetA O n} (hww : w' * w = 1) (hQ : W.Q = w * Eπ)
    (ζ : LL) (hζ : ζ ^ PD.p = 1) (hζ1 : ζ ≠ 1) :
    PowerSeries.constantCoeff (W.lev c ζ Eπ) = 0 := by
  have h0 := (levQ_pt W hs c ζ hζ hζ1).1
  have hw : PowerSeries.constantCoeff (W.lev c ζ w') * PowerSeries.constantCoeff (W.lev c ζ w) = 1 := by
    rw [← map_mul, ← map_mul, hww, map_one, map_one]
  rw [hQ, map_mul, map_mul] at h0
  rcases mul_eq_zero.1 h0 with h | h
  · rw [h, mul_zero] at hw
    exact absurd hw zero_ne_one
  · exact h

end Exp

end Formalism.MainNotions.N.Ln34.ModelFPf

end
