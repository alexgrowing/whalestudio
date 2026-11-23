import Formalism.SharpRestriction.LevelLetterCocycles.InvariantLetterIdempotentOfFixed

noncomputable section

open Classical

namespace Formalism.MainNotions.RamifiedCoefficientChains.S9.ExtensionLemmaAlt.Step2C

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc
open Formalism.MainNotions.CrystallineLiftingInputs (DL InPN)
open Formalism.MainNotions.RamifiedCoefficientChains.S9.ExtensionLemmaAlt.Step2L
open Formalism.MainNotions.N.Pv.LocalLengthBound

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}

variable (W : LocWach PD LL O v n) (T : LocLat G Qp LL O)

theorem coboundary_mem_invariant_cocycles {m : W.DD T} (hm : ∀ δ ∈ W.DelF, W.γD T δ m = m) :
    ((W.φD T m - m, W.γD T W.gamK m - m) : W.DD T × W.DD T) ∈ W.wachCocyclesDelta T := by
  refine (RL.mem_Z1DΔ_iff W T _).2 ⟨?_, fun δ hδ => ⟨?_, ?_⟩⟩
  · simp only [map_sub, W.φγ_comm]
    abel
  · simp only [map_sub, gammaD_frobenius_comm, hm δ hδ]
  · simp only [map_sub]
    rw [← W.γD_mul, mul_comm, W.γD_mul, hm δ hδ]

theorem sum_clK_eq_pow_smul_clK_of_level_decomposition [NeZero n] (M s σ : ℕ) (ev : Finset (ZMod n)) (hgam : W.gamK = W.gam)
    (hπ : W.π₀ ∈ W.AΔ)
    (hF2 : ∀ w, InPN W T M w → ∃! z, InPN W T M z ∧ W.φD T z - z = w)
    (hF3 : ∀ (i : ZMod n) (x : ↥(W.wachCocyclesDelta T)), DL W T i (x : W.DD T × W.DD T).1 →
      InPN W T M (x : W.DD T × W.DD T).2 → InPN W T M (x : W.DD T × W.DD T).1 → W.clK T x = 0)
    (hcob : ∀ x : ↥(W.wachCocyclesDelta T), (∃ m : W.DD T, (∀ δ ∈ W.DelF, W.γD T δ m = m) ∧
      (x : W.DD T × W.DD T) = (W.φD T m - m, W.γD T W.gamK m - m)) → W.clK T x = 0)
    (yz : ↥(W.wachCocyclesDelta T)) (mE : W.DD T) (hmE : ∀ δ ∈ W.DelF, W.γD T δ mE = mE)
    (Y : ZMod n → W.DD T) (x : ZMod n → ↥(W.wachCocyclesDelta T))
    (hY1 : ((PD.p : ℕ) : O) ^ s • (yz : W.DD T × W.DD T).1 + (W.φD T mE - mE) = ∑ c ∈ ev, Y c)
    (hY2 : InPN W T M (((PD.p : ℕ) : O) ^ s • (yz : W.DD T × W.DD T).2 + (W.γ T mE - mE)))
    (hYg : ∀ c ∈ ev, InPN W T M (W.γ T (Y c) - Y c))
    (hYΔ : ∀ c ∈ ev, ∀ δ ∈ W.DelF, W.γD T δ (Y c) = Y c)
    (hx1 : ∀ c ∈ ev, DL W T (c + 1) ((x c : W.DD T × W.DD T).1 - ((PD.p : ℕ) : O) ^ σ • Y c) ∧
      InPN W T M ((x c : W.DD T × W.DD T).1 - ((PD.p : ℕ) : O) ^ σ • Y c))
    (hx2 : ∀ c ∈ ev, InPN W T M (x c : W.DD T × W.DD T).2) :
    ∑ c ∈ ev, W.clK T (x c) = ((PD.p : ℕ) : O) ^ (s + σ) • W.clK T yz := by
  have hγ : W.γ T = W.γD T W.gamK := by rw [hgam]; rfl

  have hZex : ∀ c, ∃ z, c ∈ ev → InPN W T M z ∧ W.φD T z - z = W.γ T (Y c) - Y c := by
    intro c
    by_cases hc : c ∈ ev
    · obtain ⟨z, hz⟩ := (hF2 _ (hYg c hc)).exists
      exact ⟨z, fun _ => hz⟩
    · exact ⟨0, fun h => (hc h).elim⟩
  choose Z hZ using hZex
  have hCmem : ∀ c (hc : c ∈ ev), ((Y c, Z c) : W.DD T × W.DD T) ∈ W.wachCocyclesDelta T := by
    intro c hc
    refine (RL.mem_Z1DΔ_iff W T _).2 ⟨?_, fun δ hδ => ⟨hYΔ c hc δ hδ, ?_⟩⟩
    · simp only
      rw [← hγ, (hZ c hc).2]
    · exact uniformizerLattice_delta_fixed W T hπ (hZ c hc).1 δ hδ
  obtain ⟨C, hC⟩ : ∃ C : ZMod n → ↥(W.wachCocyclesDelta T), ∀ c (hc : c ∈ ev),
      (C c : W.DD T × W.DD T) = (Y c, Z c) :=
    ⟨fun c => if hc : c ∈ ev then ⟨(Y c, Z c), hCmem c hc⟩ else 0, fun c hc => by simp [hc]⟩

  have hxc : ∀ c ∈ ev, W.clK T (x c) = ((PD.p : ℕ) : O) ^ σ • W.clK T (C c) := by
    intro c hc
    have h0 := hF3 (c + 1) (x c - ((PD.p : ℕ) : O) ^ σ • C c)
      (by simpa [hC c hc] using (hx1 c hc).1)
      (by simpa [hC c hc] using
        (uniformizerLattice_sub W T (hx2 c hc) (Formalism.MainNotions.RamifiedCoefficientChains.S9.inPN_smul W T (((PD.p : ℕ) : O) ^ σ) (hZ c hc).1)))
      (by simpa [hC c hc] using (hx1 c hc).2)
    have e := (W.clK T).map_sub (x c) (((PD.p : ℕ) : O) ^ σ • C c)
    have e' := (W.clK T).map_smul (((PD.p : ℕ) : O) ^ σ) (C c)
    have h1 := e.symm.trans h0
    rw [sub_eq_zero] at h1
    exact h1.trans e'

  let cb : ↥(W.wachCocyclesDelta T) := ⟨_, coboundary_mem_invariant_cocycles W T hmE⟩
  have hsum : ∑ c ∈ ev, C c = ((PD.p : ℕ) : O) ^ s • yz + cb := by
    have hyz := ((RL.mem_Z1DΔ_iff W T _).1 yz.2).1
    apply Subtype.ext
    rw [Submodule.coe_sum]
    refine Prod.ext ?_ ?_
    · rw [Prod.fst_sum, Finset.sum_congr rfl (fun c hc => congrArg Prod.fst (hC c hc))]
      simp only [Submodule.coe_add, Submodule.coe_smul, Prod.fst_add, Prod.smul_fst, cb]
      exact hY1.symm
    · rw [Prod.snd_sum, Finset.sum_congr rfl (fun c hc => congrArg Prod.snd (hC c hc))]
      simp only [Submodule.coe_add, Submodule.coe_smul, Prod.snd_add, Prod.smul_snd, cb]
      rw [← hγ]
      have hw : InPN W T M (W.γ T (∑ c ∈ ev, Y c) - ∑ c ∈ ev, Y c) := by
        rw [map_sum, ← Finset.sum_sub_distrib]
        exact Finset.sum_induction _ _ (fun a b ha hb => Formalism.MainNotions.RamifiedCoefficientChains.S9.inPN_add W T ha hb)
          (uniformizerLattice_zero W T M) (fun c hc => hYg c hc)
      refine (hF2 _ hw).unique ⟨?_, ?_⟩ ⟨hY2, ?_⟩
      · exact Finset.sum_induction _ _ (fun a b ha hb => Formalism.MainNotions.RamifiedCoefficientChains.S9.inPN_add W T ha hb)
          (uniformizerLattice_zero W T M) (fun c hc => (hZ c hc).1)
      · rw [map_sum, ← Finset.sum_sub_distrib, map_sum, ← Finset.sum_sub_distrib]
        exact Finset.sum_congr rfl fun c hc => (hZ c hc).2
      · rw [← hY1]
        have hyz' : W.γ T (yz : W.DD T × W.DD T).1 - (yz : W.DD T × W.DD T).1 =
            W.φD T (yz : W.DD T × W.DD T).2 - (yz : W.DD T × W.DD T).2 := by rw [hγ]; exact hyz
        simp only [map_add, map_sub, map_smul, gamma_frobenius_comm]
        have e : ((PD.p : ℕ) : O) ^ s • W.γ T (yz : W.DD T × W.DD T).1 =
            ((PD.p : ℕ) : O) ^ s • (yz : W.DD T × W.DD T).1 +
              ((PD.p : ℕ) : O) ^ s • (W.φD T (yz : W.DD T × W.DD T).2 - (yz : W.DD T × W.DD T).2) := by
          rw [← hyz', smul_sub]; abel
        rw [e, smul_sub]
        abel
  have hcb : W.clK T cb = 0 := hcob cb ⟨mE, hmE, rfl⟩
  have e1 : W.clK T (∑ c ∈ ev, C c) = ∑ c ∈ ev, W.clK T (C c) := map_sum (W.clK T) _ _
  have e3 := congrArg (W.clK T) hsum
  have e2 : W.clK T (((PD.p : ℕ) : O) ^ s • yz + cb) = ((PD.p : ℕ) : O) ^ s • W.clK T yz := by
    have h1 := (W.clK T).map_add (((PD.p : ℕ) : O) ^ s • yz) cb
    have h2 := (W.clK T).map_smul (((PD.p : ℕ) : O) ^ s) yz
    rw [hcb, add_zero] at h1
    exact h1.trans h2
  calc ∑ c ∈ ev, W.clK T (x c) = ∑ c ∈ ev, ((PD.p : ℕ) : O) ^ σ • W.clK T (C c) :=
        Finset.sum_congr rfl hxc
    _ = ((PD.p : ℕ) : O) ^ σ • ∑ c ∈ ev, W.clK T (C c) := (Finset.smul_sum ..).symm
    _ = ((PD.p : ℕ) : O) ^ σ • W.clK T (∑ c ∈ ev, C c) := by rw [e1]
    _ = ((PD.p : ℕ) : O) ^ σ • W.clK T (((PD.p : ℕ) : O) ^ s • yz + cb) :=
        congrArg (fun u => ((PD.p : ℕ) : O) ^ σ • u) e3
    _ = ((PD.p : ℕ) : O) ^ σ • (((PD.p : ℕ) : O) ^ s • W.clK T yz) :=
        congrArg (fun u => ((PD.p : ℕ) : O) ^ σ • u) e2
    _ = ((PD.p : ℕ) : O) ^ (s + σ) • W.clK T yz := by rw [smul_smul, ← pow_add, add_comm σ s]

end Formalism.MainNotions.RamifiedCoefficientChains.S9.ExtensionLemmaAlt.Step2C

end
