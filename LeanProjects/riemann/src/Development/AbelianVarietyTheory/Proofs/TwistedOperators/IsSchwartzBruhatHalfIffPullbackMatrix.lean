import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RestrictedTensorBasePointNormSq
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsIntOv

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting GlobalTheory.PlaceTensor
open scoped TensorProduct ComplexOrder Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.HalfCoordSB

theorem eventually_pow_nsmul_mem {K M : Type} [NormedField K] [AddCommGroup M] [Module K M] [TopologicalSpace M]
    [ContinuousSMul K M] {p : ℕ} (hp : ‖(p : K)‖ < 1) {C U : Set M} (hC : IsCompact C) (hU : U ∈ 𝓝 (0 : M)) :
    ∀ᶠ n in Filter.atTop, ∀ x ∈ C, p ^ n • x ∈ U := by
  have hsmul : ∀ᶠ c in 𝓝 (0 : K), ∀ x ∈ C, c • x ∈ U := by
    refine hC.eventually_forall_of_forall_eventually fun y _ => ?_
    have ht : Filter.Tendsto (fun z : K × M => z.1 • z.2) (𝓝 ((0 : K), y)) (𝓝 (0 : M)) := (continuous_smul (M := K) (X := M)).tendsto' _ _ (by simp)
    exact ht hU
  have hpow : Filter.Tendsto (fun n : ℕ => (p : K) ^ n) Filter.atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_norm_lt_one hp
  filter_upwards [hpow.eventually hsmul] with n hn x hx
  have hx' := hn x hx
  rwa [← Nat.cast_pow, Nat.cast_smul_eq_nsmul] at hx'

theorem eventually_invariant {M : Type} [AddCommGroup M] [TopologicalSpace M] [IsTopologicalAddGroup M] {Φ : M → ℂ}
    (h1 : IsLocallyConstant Φ) (h2 : HasCompactSupport Φ) : ∀ᶠ u in 𝓝 (0 : M), ∀ x, Φ (x + u) = Φ x := by
  have hloc : ∀ y, ∀ᶠ z in 𝓝 y, Φ z = Φ y := fun y => (h1.isOpen_fiber (Φ y)).mem_nhds rfl
  have hK : IsCompact (tsupport Φ) := h2
  have hA : ∀ᶠ u in 𝓝 (0 : M), ∀ x ∈ tsupport Φ, Φ (x + u) = Φ x := by
    refine hK.eventually_forall_of_forall_eventually fun y _ => ?_
    have hc : Filter.Tendsto (fun z : M × M => z.2 + z.1) (𝓝 ((0 : M), y)) (𝓝 y) := (show Continuous fun z : M × M => z.2 + z.1 from continuous_snd.add continuous_fst).tendsto' _ _ (by simp)
    have hs : Filter.Tendsto (fun z : M × M => z.2) (𝓝 ((0 : M), y)) (𝓝 y) := continuous_snd.tendsto _
    filter_upwards [hc.eventually (hloc y), hs.eventually (hloc y)] with z h h'
    exact h.trans h'.symm
  have hB : ∀ᶠ u in 𝓝 (0 : M), ∀ x ∈ tsupport Φ, Φ (x - u) = Φ x := by
    refine hK.eventually_forall_of_forall_eventually fun y _ => ?_
    have hc : Filter.Tendsto (fun z : M × M => z.2 - z.1) (𝓝 ((0 : M), y)) (𝓝 y) := (show Continuous fun z : M × M => z.2 - z.1 from continuous_snd.sub continuous_fst).tendsto' _ _ (by simp)
    have hs : Filter.Tendsto (fun z : M × M => z.2) (𝓝 ((0 : M), y)) (𝓝 y) := continuous_snd.tendsto _
    filter_upwards [hc.eventually (hloc y), hs.eventually (hloc y)] with z h h'
    exact h.trans h'.symm
  filter_upwards [hA, hB] with u hu hu' x
  by_cases hx : x ∈ tsupport Φ
  · exact hu x hx
  by_cases hxu : x + u ∈ tsupport Φ
  · simpa using (hu' (x + u) hxu).symm
  have h0 : Φ x = 0 := by
    by_contra h
    exact hx (subset_tsupport Φ h)
  have h0' : Φ (x + u) = 0 := by
    by_contra h
    exact hxu (subset_tsupport Φ h)
  rw [h0, h0']

variable {D : D7} {m n : ℕ} {a : AE D}

theorem isHalf_add {x y : Mx D m n} (hx : IsHalf a x) (hy : IsHalf a y) : IsHalf a (x + y) := by
  unfold IsHalf at hx hy ⊢
  intro i j
  rw [Matrix.add_apply, mul_add, hx i j, hy i j]

theorem isHalf_sub {x y : Mx D m n} (hx : IsHalf a x) (hy : IsHalf a y) : IsHalf a (x - y) := by
  unfold IsHalf at hx hy ⊢
  intro i j
  rw [Matrix.sub_apply, mul_sub, hx i j, hy i j]

theorem isHalf_nsmul {x : Mx D m n} (hx : IsHalf a x) (k : ℕ) : IsHalf a (k • x) := by
  induction k with
  | zero =>
    unfold IsHalf
    intro i j
    simp
  | succ k ih =>
    rw [succ_nsmul]
    exact isHalf_add ih hx

theorem isSBHalf_iff_pull : ∀ (D : D7) (S T : HSp D) (v : FinPl D) (m n : ℕ) (a : AE D) (Λ : AddSubgroup (WO S T)) (κ : WO S T → Matrix (Fin m) (Fin n) (Fv D.host.F v)), IsCoord a Λ κ → (∀ Φ ∈ GlobalTheory.SplitWeil.SB (Matrix (Fin m) (Fin n) (Fv D.host.F v)), IsSBHalf a Λ (pull a κ Φ)) ∧ ∀ Ψ, IsSBHalf a Λ Ψ → ∃ Φ ∈ GlobalTheory.SplitWeil.SB (Matrix (Fin m) (Fin n) (Fv D.host.F v)), Ψ = pull a κ Φ := by
  intro D S T v m n a Λ κ hκ
  unfold IsCoord at hκ
  obtain ⟨hadd, hbij, hopen, hcpt⟩ := hκ
  have h0 : κ 0 = 0 := by simpa using hadd 0 0
  have hns : ∀ (k : ℕ) (t : WO S T), κ (k • t) = k • κ t := by
    intro k t
    induction k with
    | zero => simp [h0]
    | succ k ih => rw [succ_nsmul, succ_nsmul, hadd, ih]
  have hz : IsHalf a (0 : WO S T) := by
    unfold IsHalf
    intro i j
    simp
  have hO0 : κ '' {t | t ∈ Λ ∧ IsHalf a t} ∈ 𝓝 (0 : Matrix (Fin m) (Fin n) (Fv D.host.F v)) :=
    hopen.mem_nhds ⟨0, ⟨Λ.zero_mem, hz⟩, h0⟩
  refine ⟨fun Φ hΦ => ?_, fun Ψ hΨ => ?_⟩
  ·
    obtain ⟨p, hp0, hp⟩ : ∃ p : ℕ, 0 < p ∧ ‖(p : Fv D.host.F v)‖ < 1 := by
      refine ⟨Ideal.absNorm v.asIdeal, Nat.pos_of_ne_zero ?_, ?_⟩
      · rw [Ne, Ideal.absNorm_eq_zero_iff]
        exact v.ne_bot
      · have h := (NumberField.FinitePlace.norm_lt_one_iff_mem D.host.F v
          ((Ideal.absNorm v.asIdeal : ℕ) : 𝓞 D.host.F)).mpr (Ideal.absNorm_mem v.asIdeal)
        simpa using h
    have hΦ' : IsLocallyConstant Φ ∧ HasCompactSupport Φ := hΦ
    obtain ⟨h1, h2⟩ := hΦ'
    have hU := eventually_invariant h1 h2
    have E1 := eventually_pow_nsmul_mem hp hcpt hU
    have E2 := eventually_pow_nsmul_mem hp h2 hO0
    obtain ⟨N, hN1, hN2⟩ := (E1.and E2).exists
    unfold IsSBHalf
    refine ⟨fun t ht => ?_, p ^ N, pow_pos hp0 N, fun u hu hhu t => ?_, fun t ht => ?_⟩
    · by_contra hh
      exact ht (by simp [pull, hh])
    · by_cases htH : IsHalf a t
      · have h' : IsHalf a (t + (p ^ N) • u) := isHalf_add htH (isHalf_nsmul hhu _)
        have hm : ∀ x, Φ (x + (p ^ N) • κ u) = Φ x := hN1 (κ u) ⟨u, ⟨hu, hhu⟩, rfl⟩
        simp only [pull, if_pos htH, if_pos h']
        rw [hadd, hns]
        exact hm (κ t)
      · have h' : ¬ IsHalf a (t + (p ^ N) • u) := by
          intro hc
          apply htH
          have hc' := isHalf_sub hc (isHalf_nsmul hhu (p ^ N))
          simpa using hc'
        simp only [pull, if_neg htH, if_neg h']
    · have htH : IsHalf a t := by
        by_contra hh
        exact ht (by simp [pull, hh])
      have hΦt : Φ (κ t) ≠ 0 := by simpa [pull, htH] using ht
      obtain ⟨s, ⟨hsΛ, hsH⟩, hs⟩ := hN2 (κ t) (subset_tsupport Φ hΦt)
      have hk : IsHalf a ((p ^ N) • t) := isHalf_nsmul htH _
      have hst : s = (p ^ N) • t := hbij.injOn hsH hk (by rw [hs, hns])
      rw [← hst]
      exact hsΛ
  · unfold IsSBHalf at hΨ
    obtain ⟨hsupp, k, hk0, hinv, hΛ⟩ := hΨ

    obtain ⟨g, hg⟩ : ∃ g : Matrix (Fin m) (Fin n) (Fv D.host.F v) → WO S T,
        ∀ x, IsHalf a (g x) ∧ κ (g x) = x :=
      ⟨Function.invFunOn κ {t | IsHalf a t}, fun x =>
        ⟨Function.invFunOn_mem (hbij.surjOn (Set.mem_univ x)), Function.invFunOn_eq (hbij.surjOn (Set.mem_univ x))⟩⟩
    have hgk : ∀ t, IsHalf a t → g (κ t) = t := fun t ht => hbij.injOn (hg _).1 ht (hg _).2
    have : CharZero (Fv D.host.F v) :=
      charZero_of_injective_algebraMap (R := D.host.F) (algebraMap D.host.F (Fv D.host.F v)).injective
    have hkF : ((k : ℕ) : Fv D.host.F v) ≠ 0 := Nat.cast_ne_zero.mpr hk0.ne'
    refine ⟨fun x => Ψ (g x), ?_, ?_⟩
    · show IsLocallyConstant (fun x => Ψ (g x)) ∧ HasCompactSupport (fun x => Ψ (g x))
      refine ⟨?_, ?_⟩
      · rw [IsLocallyConstant.iff_eventually_eq]
        intro x
        have hW : (fun z : Matrix (Fin m) (Fin n) (Fv D.host.F v) => (k : Fv D.host.F v) • z) ''
            (κ '' {t | t ∈ Λ ∧ IsHalf a t}) ∈ 𝓝 (0 : Matrix (Fin m) (Fin n) (Fv D.host.F v)) :=
          (isOpenMap_smul₀ hkF _ hopen).mem_nhds ⟨0, ⟨0, ⟨Λ.zero_mem, hz⟩, h0⟩, smul_zero _⟩
        have hc : Filter.Tendsto (fun y : Matrix (Fin m) (Fin n) (Fv D.host.F v) => y - x) (𝓝 x) (𝓝 0) :=
          (show Continuous fun y : Matrix (Fin m) (Fin n) (Fv D.host.F v) => y - x from
            continuous_id.sub continuous_const).tendsto' _ _ (by simp)
        filter_upwards [hc.eventually_mem hW] with y hy
        obtain ⟨w, ⟨u, ⟨huΛ, huH⟩, rfl⟩, hw0⟩ := hy
        have hw : (k : Fv D.host.F v) • κ u = y - x := hw0
        have hy' : y = x + κ (k • u) := by
          rw [hns, ← Nat.cast_smul_eq_nsmul (Fv D.host.F v), hw]
          abel
        have hgy : g y = g x + k • u := by
          rw [hy']
          apply hbij.injOn (hg _).1 (isHalf_add (hg x).1 (isHalf_nsmul huH k))
          rw [(hg _).2, hadd, (hg x).2]
        show Ψ (g y) = Ψ (g x)
        rw [hgy]
        exact hinv u huΛ huH (g x)
      · refine HasCompactSupport.intro
          (K := (fun z : Matrix (Fin m) (Fin n) (Fv D.host.F v) => (k : Fv D.host.F v)⁻¹ • z) ''
            (κ '' {t | t ∈ Λ ∧ IsHalf a t}))
          (hcpt.image (continuous_const_smul _)) ?_
        intro x hx
        by_contra hne
        apply hx
        have hm := hΛ (g x) hne
        have hmem : κ (k • g x) ∈ κ '' {t | t ∈ Λ ∧ IsHalf a t} := ⟨_, ⟨hm, isHalf_nsmul (hg x).1 k⟩, rfl⟩
        rw [hns, (hg x).2, ← Nat.cast_smul_eq_nsmul (Fv D.host.F v)] at hmem
        exact ⟨_, hmem, inv_smul_smul₀ hkF x⟩
    · funext t
      by_cases ht : IsHalf a t
      · simp only [pull, if_pos ht]
        rw [hgk t ht]
      · simp only [pull, if_neg ht]
        by_contra hne
        exact ht (hsupp t hne)

end GlobalTheory.HalfCoordSB

end
