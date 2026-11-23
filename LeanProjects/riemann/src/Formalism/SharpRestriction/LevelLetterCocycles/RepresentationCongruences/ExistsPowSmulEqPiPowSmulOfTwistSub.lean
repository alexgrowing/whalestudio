import Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.ImportsAlt
import Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.DivAddLogbLeEightMulErrorScale
import Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.TruncatedCoefficientPoly
import Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.SaturationFractionModule
import Formalism.SharpRestriction.LevelLetterCocycles.RelayGeneralCaseOfAdmissible

noncomputable section

namespace Formalism.MainNotions.N.FrobeniusPowerSeries.DYCA

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL] [CommRing O] [Algebra O LL]
    {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    {PD : PeriodData G Qp K₀ K B BdR}

theorem sum_split {R M : Type} [CommRing R] [AddCommGroup M] [Module R M] (π : R) (f : ℕ → M)
    (N : ℕ) (hN : 1 ≤ N) :
    ∑ r ∈ Finset.range N, π ^ r • f r = π • ∑ r ∈ Finset.range (N - 1), π ^ r • f (r + 1) + f 0 := by
  obtain ⟨N', rfl⟩ : ∃ N', N = N' + 1 := ⟨N - 1, by omega⟩
  rw [Finset.sum_range_succ', Nat.add_sub_cancel, Finset.smul_sum, pow_zero, one_smul]
  congr 1
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [pow_succ, mul_comm, mul_smul]

section Gen
variable {R M : Type} [CommRing R] [AddCommGroup M] [Module R M]

theorem g_step (L π g h a : R) (k k₂ r m : ℕ) (E γE x x' z : M)
    (hkx : L ^ k • (g • E) = π ^ r • x)
    (hzE : L ^ k₂ • (g • (γE - E)) = (π ^ r * π * π ^ m) • z)
    (h1x : L ^ k • ((g * (1 + π * h)) • γE) - π ^ r • x = a • (π ^ r • x) + π ^ (r + 1) • x') :
    π ^ r • (L ^ k₂ • (a • x) - π • (L ^ k₂ • (h • x) + L ^ k • ((1 + π * h) • (π ^ m • z)) -
      L ^ k₂ • x')) = 0 := by
  linear_combination (norm := module) (-(L ^ k₂)) • h1x + (L ^ k * (1 + π * h)) • hzE +
    (L ^ k₂ * (1 + π * h)) • hkx

theorem g_fin (L π g ε a : R) (k k₂ r : ℕ) (E x y : M) (hkx : L ^ k • (g • E) = π ^ r • x)
    (h4 : L ^ k₂ • (a • x) = π • y) :
    (L ^ (k + k₂) * (ε * a)) • (g • E) = π ^ (r + 1) • (ε • y) := by
  linear_combination (norm := module) (L ^ k₂ * ε * a) • hkx + (π ^ r * ε) • h4

theorem g_A (L π q P2 p1 aJ t : R) (κ' b1 κ κ₁ E σ e : ℕ) (FX FX' FD Fn Fz lam φHh y4 : M)
    (E1 : FX = π • FX' + L ^ κ₁ • FD) (E2 : Fn = FD + π • Fz)
    (E3 : q ^ b1 • Fn = L ^ E • (p1 ^ e • lam))
    (E4 : L ^ κ' • (L ^ κ • lam - L ^ σ • φHh) = (π * aJ) • y4)
    (ht : L ^ b1 * p1 ^ e - L ^ e * q ^ b1 = π * t) :
    L ^ κ' • ((q ^ b1 * P2) • (L ^ (b1 + κ) • FX - L ^ (κ₁ + E + σ + e) • φHh)) =
      π • ((L ^ (κ₁ + E) * L ^ b1 * p1 ^ e * aJ) • (P2 • y4) +
        (L ^ (κ' + b1 + κ) * (q ^ b1 * P2)) • (FX' - L ^ κ₁ • Fz) +
        (L ^ (κ₁ + E + κ' + σ) * t) • (P2 • φHh)) := by
  have key : L ^ κ' • ((q ^ b1 * P2) • (L ^ (b1 + κ) • FX - L ^ (κ₁ + E + σ + e) • φHh)) =
      π • ((L ^ (κ₁ + E) * L ^ b1 * p1 ^ e * aJ) • (P2 • y4) +
        (L ^ (κ' + b1 + κ) * (q ^ b1 * P2)) • (FX' - L ^ κ₁ • Fz)) +
      (L ^ (κ₁ + E + κ' + σ) * (L ^ b1 * p1 ^ e - L ^ e * q ^ b1)) • (P2 • φHh) := by
    linear_combination (norm := module) (L ^ κ' * (q ^ b1 * P2) * L ^ (b1 + κ)) • E1 -
    (L ^ κ' * (q ^ b1 * P2) * L ^ (b1 + κ + κ₁)) • E2 + (L ^ κ' * P2 * L ^ (b1 + κ + κ₁)) • E3 +
    (P2 * L ^ (b1 + κ₁ + E) * p1 ^ e) • E4
  rw [key, ht]
  module

theorem g_B (L π q P2 u3 Pk : R) (b1 κ c Rr R' M' : ℕ) (FX γFX Fx φHh γφHh φxH : M)
    (B1 : γFX - FX = (π ^ Rr * π ^ R') • Fx)
    (B2 : γφHh - φHh = (u3 * (π ^ Rr * π ^ M') * Pk) • φxH) :
    (q ^ b1 * P2) • (L ^ (b1 + κ) • γFX - L ^ c • γφHh - (L ^ (b1 + κ) • FX - L ^ c • φHh)) =
      π ^ Rr • ((L ^ (b1 + κ) * π ^ R' * (q ^ b1 * P2)) • Fx -
        (L ^ c * u3 * π ^ M' * Pk * q ^ b1) • (P2 • φxH)) := by
  linear_combination (norm := module) (q ^ b1 * P2 * L ^ (b1 + κ)) • B1 - (q ^ b1 * P2 * L ^ c) • B2

theorem g_K (L g π qB : R) (kU κ₁ b1 κ σ₁ E σ e₁ e₂ : ℕ) (Fy FZ φFX φφHh φV : M)
    (hrelF : L ^ κ₁ • Fy + (π * qB) • FZ = L ^ σ₁ • φFX)
    (hφV : φV = L ^ (b1 + κ) • φFX - L ^ (κ₁ + E + σ + (e₁ + e₂)) • φφHh) :
    L ^ (kU + κ₁) • g • (L ^ (b1 + κ) • Fy - L ^ (σ₁ + E + σ + e₁ + e₂) • φφHh) =
      L ^ σ₁ • (L ^ kU • (g • φV)) - (L ^ (kU + b1 + κ) * g * π) • (qB • FZ) := by
  rw [hφV]
  linear_combination (norm := module) (L ^ (kU + b1 + κ) * g) • hrelF

end Gen

variable (W : LocWach PD LL O v n)

theorem γ_mul_form {g g' h h' : LetA O n} (hg : W.γA W.gam g = g * (1 + W.π₀ * h))
    (hg' : W.γA W.gam g' = g' * (1 + W.π₀ * h')) :
    W.γA W.gam (g * g') = g * g' * (1 + W.π₀ * (h + h' + W.π₀ * h * h')) := by
  rw [map_mul, hg, hg']; ring

theorem γ_pow_form {g h : LetA O n} (hh : h ∈ W.AΔ) (hπ : W.π₀ ∈ W.AΔ)
    (hg : W.γA W.gam g = g * (1 + W.π₀ * h)) (k : ℕ) :
    ∃ h' ∈ W.AΔ, W.γA W.gam (g ^ k) = g ^ k * (1 + W.π₀ * h') := by
  induction k with
  | zero => exact ⟨0, W.AΔ.zero_mem, by simp⟩
  | succ k ih =>
    obtain ⟨h', hh', e⟩ := ih
    refine ⟨h' + h + W.π₀ * h' * h, ?_, ?_⟩
    · exact W.AΔ.add_mem (W.AΔ.add_mem hh' hh) (W.AΔ.mul_mem (W.AΔ.mul_mem hπ hh') hh)
    · rw [pow_succ, γ_mul_form W e hg]

theorem exists_pow_smul_eq_pi_pow_smul_of_twist_sub (T : LocLat G Qp LL O) (hC : Formalism.MainNotions.UnusedSlot80.Relay2.Ctx W T) (c : ZMod n)
    (g₀ h : LetA O n) (hh : h ∈ W.AΔ)
    (hγg : W.γA W.gam g₀ = g₀ * (1 + W.π₀ * h)) (R : ℕ) (E : W.DD T)
    (hE : ∃ (k : ℕ) (E' : W.DD T), Formalism.MainNotions.LiftingTheory.InNΔi W T c E' ∧
      Formalism.MainNotions.ArcLiftingSetup.lA W ^ k • (g₀ • E) = W.π₀ • E')
    (hγ : ∃ (k : ℕ) (z : W.DD T), Formalism.MainNotions.LiftingTheory.InNΔi W T c z ∧
      Formalism.MainNotions.ArcLiftingSetup.lA W ^ k • (g₀ • (W.γ T E - E)) = W.π₀ ^ R • z) :
    ∃ (k : ℕ) (x : W.DD T), Formalism.MainNotions.LiftingTheory.InNΔi W T c x ∧
      Formalism.MainNotions.ArcLiftingSetup.lA W ^ k • (g₀ • E) = W.π₀ ^ R • x := by
  obtain ⟨k₂, z, hz, hzE⟩ := hγ
  have hπ : W.π₀ ∈ W.AΔ := hC.hπ
  have key : ∀ r, 1 ≤ r → r ≤ R → ∃ (k : ℕ) (x : W.DD T), Formalism.MainNotions.LiftingTheory.InNΔi W T c x ∧
      Formalism.MainNotions.ArcLiftingSetup.lA W ^ k • (g₀ • E) = W.π₀ ^ r • x := by
    intro r hr1
    induction r with
    | zero => omega
    | succ r ih =>
      intro hrR
      rcases Nat.eq_zero_or_pos r with h0 | hpos
      · subst h0
        obtain ⟨k, E', hE', hk⟩ := hE
        exact ⟨k, E', hE', by rw [hk, zero_add, pow_one]⟩
      obtain ⟨k, x, hx, hkx⟩ := ih hpos (by omega)
      obtain ⟨x', hx', h1x⟩ := hC.H1 c r x hx
      obtain ⟨e, he⟩ := Formalism.MainNotions.UnusedSlot80.Relay2.principal_unit_pow_sub_one_dvd W hC.inj hC.O2 r (hC.H2 r hpos)
      set a : LetA O n := algebraMap O (LetA O n) (Formalism.MainNotions.LiftingTheory.u₁ W ^ r - 1) with ha
      rw [← algebraMap_smul (LetA O n) (Formalism.MainNotions.LiftingTheory.u₁ W ^ r - 1), ← ha] at h1x
      have hγx : W.γ T (W.π₀ ^ r • x) =
          Formalism.MainNotions.ArcLiftingSetup.lA W ^ k • ((g₀ * (1 + W.π₀ * h)) • W.γ T E) := by
        rw [← hkx, Formalism.MainNotions.UnusedSlot80.Relay2.γ_lsmul, ← hγg]
        congr 1
        exact Formalism.MainNotions.LiftingTheory.frame_γD_smul W T W.gam g₀ E
      rw [hγx] at h1x
      have hR : W.π₀ ^ R = W.π₀ ^ r * W.π₀ * W.π₀ ^ (R - (r + 1)) := by
        rw [← pow_succ, ← pow_add]; congr 1; omega
      rw [hR] at hzE
      obtain ⟨y, hy⟩ : ∃ y : W.DD T, y = Formalism.MainNotions.ArcLiftingSetup.lA W ^ k₂ • (h • x) +
        Formalism.MainNotions.ArcLiftingSetup.lA W ^ k • ((1 + W.π₀ * h) • (W.π₀ ^ (R - (r + 1)) • z)) -
        Formalism.MainNotions.ArcLiftingSetup.lA W ^ k₂ • x' := ⟨_, rfl⟩
      have h3 : W.π₀ ^ r • (Formalism.MainNotions.ArcLiftingSetup.lA W ^ k₂ • (a • x) - W.π₀ • y) = 0 := by
        rw [hy]; exact g_step _ _ _ _ _ _ _ _ _ _ _ _ _ _ hkx hzE h1x
      have h4 := Formalism.MainNotions.LiftingTheory.frame_π₀_inj W T hC.hw r _ h3
      rw [sub_eq_zero] at h4
      have h1h : (1 + W.π₀ * h) ∈ W.AΔ := W.AΔ.add_mem W.AΔ.one_mem (W.AΔ.mul_mem hπ hh)
      have hyN : Formalism.MainNotions.LiftingTheory.InNΔi W T c y := by
        rw [hy]
        refine Formalism.MainNotions.UnusedSlot80.Relay2.InNΔi_sub W T c (Formalism.MainNotions.UnusedSlot80.Relay2.InNΔi_add W T c ?_ ?_)
          (Formalism.MainNotions.UnusedSlot80.Relay2.InNΔi_lsmul W T c _ hx')
        · exact Formalism.MainNotions.UnusedSlot80.Relay2.InNΔi_lsmul W T c _ (Formalism.MainNotions.UnusedSlot80.Relay2.InNΔi_smul W T c hh hx)
        · exact Formalism.MainNotions.UnusedSlot80.Relay2.InNΔi_lsmul W T c _ (Formalism.MainNotions.UnusedSlot80.Relay2.InNΔi_smul W T c h1h
            (Formalism.MainNotions.UnusedSlot80.Relay2.InNΔi_smul W T c (W.AΔ.pow_mem hπ _) hz))
      obtain ⟨ε, hε⟩ : ∃ ε : LetA O n, ε = algebraMap O (LetA O n) e := ⟨_, rfl⟩
      have he' : ε * a = Formalism.MainNotions.ArcLiftingSetup.lA W ^ (1 + padicValNat PD.p r) := by
        rw [hε, ha, ← map_mul, he, map_pow, map_natCast]; rfl
      refine ⟨k + k₂ + (1 + padicValNat PD.p r), ε • y,
        Formalism.MainNotions.UnusedSlot80.Relay2.InNΔi_smul W T c (by rw [hε]; exact W.AΔ.algebraMap_mem e) hyN, ?_⟩
      rw [pow_add, ← he']
      exact g_fin _ _ _ _ _ _ _ _ _ _ _ hkx h4
  rcases Nat.eq_zero_or_pos R with h0 | hpos
  · subst h0
    obtain ⟨k, E', hE', hk⟩ := hE
    exact ⟨k, W.π₀ • E', Formalism.MainNotions.UnusedSlot80.Relay2.InNΔi_smul W T c hπ hE', by rw [hk, pow_zero, one_smul]⟩
  · exact key R hpos le_rfl

end Formalism.MainNotions.N.FrobeniusPowerSeries.DYCA
