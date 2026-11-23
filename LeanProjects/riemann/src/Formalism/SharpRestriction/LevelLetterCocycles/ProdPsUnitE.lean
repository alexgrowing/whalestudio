import Formalism.SharpRestriction.LevelLetterCocycles.MemOfSecEq

noncomputable section

open Classical

namespace Formalism.MainNotions.UnusedSlot80.LevC

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.WachCoordinates.Br

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR}
    {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL] [CommRing O] [Algebra O LL]
    {v : AddValuation LL (WithTop ℚ)} {n : ℕ} (W : LocWach PD LL O v n)

open Formalism.MainNotions.ArcLiftingSetup Formalism.MainNotions.UnusedSlot80.PhiPowers

variable [IsDomain O] [NeZero n]

theorem ps_unitE (hR : Formalism.MainNotions.UnusedSlot80.ToolsR.RingP W) (s : ℕ) : IsUnit (algebraMap (LetA O n) W.EE (ps W s)) := by
  obtain ⟨h3, h6⟩ := Formalism.MainNotions.UnusedSlot80.SatW.ring_clauses W hR
  exact Formalism.MainNotions.UnusedSlot80.SatW.isUnit_EE_of_UPi W (Formalism.MainNotions.UnusedSlot80.SatW.UPi_qpow W h3 h6 s)

theorem prod_ps_unitE (hR : Formalism.MainNotions.UnusedSlot80.ToolsR.RingP W) (e : ℕ) (E : ℕ → ℕ) :
    IsUnit (algebraMap (LetA O n) W.EE (∏ s ∈ Finset.range e, ps W s ^ E s)) := by
  rw [map_prod]
  exact Finset.prod_induction _ IsUnit (fun a b ha hb => ha.mul hb) isUnit_one
    fun s _ => by rw [map_pow]; exact (ps_unitE W hR s).pow _

theorem prod_succ_φ (e : ℕ) (E : ℕ → ℕ) :
    ∏ s ∈ Finset.range (e + 1), ps W s ^ E s =
      W.φA (∏ s ∈ Finset.range e, ps W s ^ E (s + 1)) * ps W 0 ^ E 0 := by
  rw [Finset.prod_range_succ', map_prod]
  congr 1
  exact Finset.prod_congr rfl fun s _ => by rw [map_pow, ← ps_succ]

theorem mono_lift (hR : Formalism.MainNotions.UnusedSlot80.ToolsR.RingP W) (A : ArcP n) (a : ZMod n) (e : ℕ) (α : ℕ → ℤ)
    (g : W.EE) (hg : InId W (a + 1) (e + 1) α g)
    (hα : ∀ s, s < e → -(A.Hs a e s : ℤ) ≤ α (s + 1)) (N H : ℕ) (hN : H + (-(α 0)).toNat ≤ N)
    {s₁ : LetA O n} (hs₁ : s₁ ∈ W.AΔ) :
    ∃ vv ∈ W.AΔ, ∃ g' : W.EE,
      algebraMap (LetA O n) W.EE (ps W 0 ^ N * s₁) * g =
        algebraMap (LetA O n) W.EE (ps W 0 ^ H * vv) * W.φE g' ∧
      InId W a e (fun s => α (s + 1)) g' ∧ InFr W a 1 (abelian₂ W A a e) g' := by
  obtain ⟨u, hu, hgu⟩ := hg
  set num' : LetA O n := ∏ s ∈ Finset.range e, ps W s ^ (α (s + 1)).toNat with hnum'
  set den' : LetA O n := ∏ s ∈ Finset.range e, ps W s ^ (-(α (s + 1))).toNat with hden'
  have hnum := prod_succ_φ W e (fun s => (α s).toNat)
  have hden := prod_succ_φ W e (fun s => (-(α s)).toNat)
  obtain ⟨D, hD⟩ := prod_ps_unitE W hR e (fun s => (-(α (s + 1))).toNat)
  set ι : W.EE := ((D⁻¹ : W.EEˣ) : W.EE) with hιdef
  have hι : ι * algebraMap (LetA O n) W.EE den' = 1 := by rw [hden', ← hD]; exact Units.inv_mul D
  have hp0Δ : ps W 0 ∈ W.AΔ := ps_mem_AΔ W hR.1 0
  set E0 : ℕ := (-(α 0)).toNat with hE0
  set F0 : ℕ := (α 0).toNat with hF0
  refine ⟨ps W 0 ^ (N + F0 - E0 - H) * s₁ * u, W.AΔ.mul_mem (W.AΔ.mul_mem (W.AΔ.pow_mem hp0Δ _) hs₁) hu,
    algebraMap (LetA O n) W.EE (letE a * num') * ι, ?_, ?_, ?_⟩
  ·
    obtain ⟨Dd, hDd⟩ := prod_ps_unitE W hR (e + 1) (fun s => (-(α s)).toNat)
    have hcan : ∀ y z : W.EE, algebraMap (LetA O n) W.EE
        (∏ s ∈ Finset.range (e + 1), ps W s ^ (-(α s)).toNat) * y =
        algebraMap (LetA O n) W.EE (∏ s ∈ Finset.range (e + 1), ps W s ^ (-(α s)).toNat) * z → y = z := by
      intro y z h
      rw [← hDd] at h
      have := congrArg (fun w => ((Dd⁻¹ : W.EEˣ) : W.EE) * w) h
      simpa only [← mul_assoc, Units.inv_mul, one_mul] using this
    apply hcan
    have hφι : W.φE ι * algebraMap (LetA O n) W.EE (W.φA den') = 1 := by
      rw [← φE_alg, ← map_mul, hι, map_one]
    have hl : W.φA (letE a : LetA O n) = letE (a + 1) := by
      have := φA_letE W (a + 1); rwa [show a + 1 - 1 = a by ring] at this
    have hexp : N + F0 = E0 + H + (N + F0 - E0 - H) := by omega
    rw [hnum, hden] at hgu
    simp only [map_mul, map_pow] at hgu
    rw [hden]
    simp only [map_mul, map_pow, φE_alg, hl]
    have e1 : algebraMap (LetA O n) W.EE (ps W 0) ^ N * algebraMap (LetA O n) W.EE (ps W 0) ^ F0 =
        algebraMap (LetA O n) W.EE (ps W 0) ^ E0 * algebraMap (LetA O n) W.EE (ps W 0) ^ H *
          algebraMap (LetA O n) W.EE (ps W 0) ^ (N + F0 - E0 - H) := by
      rw [← pow_add, ← pow_add, ← pow_add, ← hexp]
    rw [hden'] at hφι
    rw [hnum'] at *
    linear_combination (algebraMap (LetA O n) W.EE (ps W 0) ^ N * algebraMap (LetA O n) W.EE s₁) * hgu +
      (algebraMap (LetA O n) W.EE s₁ * algebraMap (LetA O n) W.EE u *
        algebraMap (LetA O n) W.EE (letE (a + 1)) *
        algebraMap (LetA O n) W.EE (W.φA (∏ s ∈ Finset.range e, ps W s ^ (α (s + 1)).toNat))) * e1 -
      (algebraMap (LetA O n) W.EE (ps W 0) ^ E0 * algebraMap (LetA O n) W.EE (ps W 0) ^ H *
        algebraMap (LetA O n) W.EE (ps W 0) ^ (N + F0 - E0 - H) * algebraMap (LetA O n) W.EE s₁ *
        algebraMap (LetA O n) W.EE u * algebraMap (LetA O n) W.EE (letE (a + 1)) *
        algebraMap (LetA O n) W.EE (W.φA (∏ s ∈ Finset.range e, ps W s ^ (α (s + 1)).toNat))) * hφι
  ·
    refine ⟨1, W.AΔ.one_mem, ?_⟩
    show algebraMap (LetA O n) W.EE den' * (algebraMap (LetA O n) W.EE (letE a * num') * ι) =
      algebraMap (LetA O n) W.EE (letE a * num' * 1)
    rw [mul_one, mul_comm (algebraMap (LetA O n) W.EE (letE a * num')), ← mul_assoc,
      mul_comm (algebraMap (LetA O n) W.EE den'), hι, one_mul]
  ·
    have hle : ∀ s ∈ Finset.range e, (-(α (s + 1))).toNat ≤ A.Hs a e s := by
      intro s hs
      have := hα s (Finset.mem_range.1 hs)
      omega
    set R : LetA O n := ∏ s ∈ Finset.range e, ps W s ^ (A.Hs a e s - (-(α (s + 1))).toNat) with hRdef
    refine ⟨R * num', W.AΔ.mul_mem (W.AΔ.prod_mem fun s _ => W.AΔ.pow_mem (ps_mem_AΔ W hR.1 s) _)
        (W.AΔ.prod_mem fun s _ => W.AΔ.pow_mem (ps_mem_AΔ W hR.1 s) _), ?_⟩
    have hsplit : abelian₂ W A a e = den' * R := by
      rw [hden', hRdef, abelian₂, ← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun s hs => ?_
      rw [← pow_add, Nat.add_sub_cancel' (hle s hs)]
    rw [hsplit]
    simp only [map_mul, mul_one]
    linear_combination (algebraMap (LetA O n) W.EE R * algebraMap (LetA O n) W.EE (letE a) *
      algebraMap (LetA O n) W.EE num') * hι

end Formalism.MainNotions.UnusedSlot80.LevC
