import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RatVInjective
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnitaryAdelicIwasawaStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MinimalParabolicRationalCompactStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WittFrameReduceRankStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RationalUnitarySendsIsotropicStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RationalUnitaryWittExtensionStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MinimalParabolicScalesIsotropicStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsNearMinimalVectorStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ReductionTheoryHeightBoundStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ReductionTheoryLowerBoundStatement

set_option linter.unusedSectionVars false
noncomputable section
open NumberField MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet PositivityTheory.ThKR
open Formalism.UG (cT)
open scoped TensorProduct NNReal ENNReal Pointwise

open GlobalTheory.CompanionTheory.RedCov

namespace GlobalTheory.CompanionTheory.RedCov

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {r : ℕ}

theorem torus_zero {X Y : Matrix (Fin n) (Fin r) E} {a : (Fin r → ℝ) → GAd σ J} (ha : IsTorus σ J X Y a) : a 0 = 1 := by
  have := ha.add 0 0
  rw [add_zero] at this
  exact mul_eq_left.1 this.symm

theorem mul_mem_one (h : IsCMExt F E σ) (hJ : IsHermND σ J) {X Y : Matrix (Fin n) (Fin r) E} (hW : IsWittFrame σ J X Y)
    {a : (Fin r → ℝ) → GAd σ J} (ha : IsTorus σ J X Y a) {p q : GAd σ J} (hp : p ∈ minParOne σ J X)
    (hq : q ∈ minParOne σ J X) : p * q ∈ minParOne σ J X := by
  obtain ⟨τ, -, h2, -, h4, h5⟩ := exists_tau h hJ hW ha
  have hp' := minParOne_subset hp
  have hq' := minParOne_subset hq
  have e := h2 ⟨p, hp'⟩ ⟨q, hq'⟩
  rw [h4 p hp, h4 q hq, add_zero] at e
  have := h5 (⟨p, hp'⟩ * ⟨q, hq'⟩)
  rw [e, torus_zero ha, inv_one, mul_one] at this
  exact this

theorem ratV_zero : ratV F (0 : Fin n → E) = 0 := by
  funext i
  simp [ratV]

theorem nearMin_rat (hact : ∀ γ ∈ ratPts σ J, ∀ w : Fin n → E, ∃ w' : Fin n → E, Sends σ J γ w w' ∧ hE σ J w' w' = hE σ J w w)
    {g γ : GAd σ J} {u v : Fin n → E} (hN : NearMin σ J g v) (hγ : γ ∈ ratPts σ J)
    (hs : Sends σ J γ u v) : NearMin σ J (γ⁻¹ * g) u := by
  have hz : ∀ {w w' : Fin n → E}, Sends σ J γ w w' → w ≠ 0 → w' ≠ 0 := by
    intro w w' hs' hw e
    apply hw
    have h1 := hs'.inv
    unfold Sends at h1
    rw [e, ratV_zero, Matrix.mulVec_zero] at h1
    exact ratV_injective (h1.symm.trans ratV_zero.symm)
  obtain ⟨v', hv', hvv⟩ := hact γ hγ u
  have e : v' = v := ratV_injective (hv'.symm.trans hs)
  subst e
  refine ⟨?_, ?_, ?_⟩
  · intro hu
    subst hu
    apply hN.1
    unfold Sends at hs
    rw [ratV_zero, Matrix.mulVec_zero] at hs
    exact ratV_injective (hs.symm.trans ratV_zero.symm)
  · rw [← hvv]; exact hN.2.1
  · intro w hw hww
    obtain ⟨w', hw', hww'⟩ := hact γ hγ w
    rw [hgt_mul hs.inv, hgt_mul hw'.inv]
    exact hN.2.2 w' (hz hw' hw) (hww'.trans hww)

theorem step {r : ℕ} (h : IsCMExt F E σ) (hJ : IsHermND σ J) {X Y : Matrix (Fin n) (Fin (r + 1)) E} (hW : IsWittFrame σ J X Y)
    (IH : ∀ (n' : ℕ) (J' : Matrix (Fin n') (Fin n') E) (X' Y' : Matrix (Fin n') (Fin r) E),
      IsHermND σ J' → IsWittFrame σ J' X' Y' → HasRed σ J' X' Y') : HasRed σ J X Y := by
  intro a ha
  obtain ⟨K, hKc, hIw⟩ := GlobalTheory.T.unitary_adelic_iwasawa F E σ h n J hJ (r + 1) X Y hW
  obtain ⟨n', J', X', Y', ι, hJ', hW', hιc, hιr, hιx, hι1, hιa⟩ := GlobalTheory.T.witt_frame_reduce_rank F E σ h n J hJ r X Y hW
  obtain ⟨hιt, hιcomm, hιdec⟩ := hιa a ha
  obtain ⟨a', ha'⟩ := exists_isTorus h hJ' hW'
  obtain ⟨C', c', hC', hc', hred'⟩ := IH n' J' X' Y' hJ' hW' a' ha'
  obtain ⟨Ω, hΩc, hΩ1, hΩ⟩ := GlobalTheory.T.minimal_parabolic_rational_compact F E σ h n J hJ (r + 1) X Y hW
  have hC₁ : IsCompact ((ι '' C') * (K : Set (GAd σ J))) := (hC'.image hιc).mul hKc
  obtain ⟨M₁, hM₁, hfirst⟩ := GlobalTheory.T.reduction_theory_height_bound F E σ h n J hJ r X Y hW a ha Ω _ hΩc hΩ1 hC₁
  obtain ⟨M₂, hM₂, hsimple⟩ := GlobalTheory.T.reduction_theory_lower_bound F E σ h n J hJ r X Y hW a ha Ω _ hΩc hΩ1 hC₁
  have hact := GlobalTheory.T.rational_unitary_witt_extension F E σ h n J hJ
  refine ⟨_, min c' (min M₁⁻¹ M₂⁻¹), hC₁, lt_min hc' (lt_min (inv_pos.2 hM₁) (inv_pos.2 hM₂)), fun g => ?_⟩
  obtain ⟨v, hv⟩ := GlobalTheory.T.exists_near_minimal_vector F E σ h n J hJ r X Y hW g
  obtain ⟨γ₁, hγ₁, hs₁⟩ := GlobalTheory.T.rational_unitary_sends_isotropic F E σ h n J hJ r X Y hW v hv.1 hv.2.1
  obtain ⟨p, hp, k, hk, hg₁⟩ := hIw (γ₁⁻¹ * g)
  obtain ⟨g', q₀, hq₀, s₁, hpe, hconj⟩ := hιdec p hp
  obtain ⟨γ', hγ', q', hq', s', hs', κ', hκ', hg'⟩ := hred' g'
  have hQ : (ι γ')⁻¹ * q₀ * ι γ' * ι q' ∈ minParOne σ J X := mul_mem_one h hJ hW ha (hconj γ') (hι1 q' hq')
  obtain ⟨δ, hδ, hδP, ω, hω, hQe⟩ := hΩ _ hQ
  obtain ⟨e, he, hse⟩ := GlobalTheory.T.minimal_parabolic_scales_isotropic F E σ h n J hJ r X Y hW δ hδ hδP
  set S : Fin (r + 1) → ℝ := Fin.cons s₁ s' with hS
  have hadd : a (Fin.cons s₁ 0) * a (Fin.cons 0 s') = a S := by
    rw [← ha.add]
    congr 1
    funext i
    refine Fin.cases ?_ (fun j => ?_) i <;> simp [hS]
  have hcm : ∀ x, a (Fin.cons s₁ 0) * ι x = ι x * a (Fin.cons s₁ 0) := fun x => hιcomm s₁ x
  have key : δ⁻¹ * ((ι γ')⁻¹ * (γ₁⁻¹ * g)) = ω * a S * (ι κ' * k) := by
    have e1 : γ₁⁻¹ * g = q₀ * ι γ' * ι q' * a S * ι κ' * k := by
      rw [hg₁, hpe, hg', map_mul, map_mul, map_mul, hιt a' ha' s', ← hadd]
      have e2 := hcm γ'
      have e3 := hcm q'
      calc q₀ * a (Fin.cons s₁ 0) * (ι γ' * ι q' * a (Fin.cons 0 s') * ι κ') * k
          = q₀ * (a (Fin.cons s₁ 0) * ι γ') * ι q' * a (Fin.cons 0 s') * ι κ' * k := by group
        _ = q₀ * ι γ' * (a (Fin.cons s₁ 0) * ι q') * a (Fin.cons 0 s') * ι κ' * k := by rw [e2]; group
        _ = _ := by rw [e3]; group
    have e4 : ω = δ⁻¹ * ((ι γ')⁻¹ * q₀ * ι γ' * ι q') := by rw [hQe]; group
    rw [e1, e4]
    group
  have N3 : NearMin σ J (ω * a S * (ι κ' * k)) (e • Xᵀ 0) := by
    rw [← key]
    exact nearMin_rat hact (nearMin_rat hact (nearMin_rat hact hv hγ₁ hs₁) (hιr _ hγ') (hιx _)) hδ hse
  have hκ : ι κ' * k ∈ (ι '' C') * (K : Set (GAd σ J)) := Set.mul_mem_mul ⟨κ', hκ', rfl⟩ hk
  have b1 := hfirst ω hω S _ hκ e he N3
  have b2 := hsimple ω hω S _ hκ e he N3
  have hgeq : g = (γ₁ * ι γ' * δ) * ω * a S * (ι κ' * k) := by
    have : ω * a S * (ι κ' * k) = δ⁻¹ * ((ι γ')⁻¹ * (γ₁⁻¹ * g)) := key.symm
    calc g = (γ₁ * ι γ' * δ) * (δ⁻¹ * ((ι γ')⁻¹ * (γ₁⁻¹ * g))) := by group
      _ = _ := by rw [← this]; group
  refine ⟨γ₁ * ι γ' * δ, mul_mem (mul_mem hγ₁ (hιr _ hγ')) hδ, ω, hΩ1 hω, S, ?_, _, hκ, hgeq⟩
  obtain ⟨-, h2, h3⟩ := hs'
  have hS0 : S 0 = s₁ := rfl
  have hSs : ∀ i : Fin r, S i.succ = s' i := fun i => rfl
  have hc1 : min c' (min M₁⁻¹ M₂⁻¹) ≤ c' := min_le_left _ _
  have hc2 : min c' (min M₁⁻¹ M₂⁻¹) ≤ M₁⁻¹ := (min_le_right _ _).trans (min_le_left _ _)
  have hc3 : min c' (min M₁⁻¹ M₂⁻¹) ≤ M₂⁻¹ := (min_le_right _ _).trans (min_le_right _ _)
  set c := min c' (min M₁⁻¹ M₂⁻¹) with hcdef
  refine ⟨fun i => Real.exp_pos _, fun i j hij => ?_, fun i hi => ?_⟩
  · refine Fin.cases (motive := fun i => j.val = i.val + 1 → c * Real.exp (S j) ≤ Real.exp (S i)) ?_ (fun i' => ?_) i hij
    · intro hj
      have := b2 j hj
      calc c * Real.exp (S j) ≤ M₂⁻¹ * (M₂ * Real.exp (S 0)) :=
            mul_le_mul hc3 this (Real.exp_pos _).le (inv_pos.2 hM₂).le
        _ = Real.exp (S 0) := by field_simp
    · intro hj
      have hj0 : j ≠ 0 := by
        intro e0
        rw [e0] at hj
        simp at hj
      obtain ⟨j', rfl⟩ := Fin.exists_succ_eq.2 hj0
      have := h2 i' j' (by simpa using hj)
      rw [hSs, hSs]
      exact (mul_le_mul_of_nonneg_right hc1 (Real.exp_pos _).le).trans this
  · refine Fin.cases (motive := fun i => i.val + 1 = r + 1 → c ≤ Real.exp (S i)) ?_ (fun i' => ?_) i hi
    · intro _
      have h4 : Real.exp (-S 0) * Real.exp (S 0) = 1 := by rw [← Real.exp_add]; simp
      have h5 : M₁⁻¹ ≤ Real.exp (S 0) := by
        rw [inv_le_comm₀ hM₁ (Real.exp_pos _)]
        rw [← Real.exp_neg]
        exact b1
      exact hc2.trans h5
    · intro hi'
      rw [hSs]
      exact hc1.trans (h3 i' (by simpa using hi'))

theorem hasRed_zero (h : IsCMExt F E σ) (hJ : IsHermND σ J) {X Y : Matrix (Fin n) (Fin 0) E} : HasRed σ J X Y := by
  intro a ha
  refine ⟨{1}, 1, isCompact_singleton, one_pos, fun g => ?_⟩
  refine ⟨1, one_mem _, g, ⟨0, fun i => i.elim0, ?_, fun i => i.elim0⟩, 0, ?_, 1, rfl, ?_⟩
  · ext i j
    exact j.elim0
  · exact ⟨fun i => i.elim0, fun i => i.elim0, fun i => i.elim0⟩
  · rw [torus_zero ha]
    simp

theorem hasRed_all (h : IsCMExt F E σ) (r : ℕ) : ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (X Y : Matrix (Fin n) (Fin r) E),
    IsHermND σ J → IsWittFrame σ J X Y → HasRed σ J X Y := by
  induction r with
  | zero => exact fun n J X Y hJ _ => hasRed_zero h hJ
  | succ r ih => exact fun n J X Y hJ hW => step h hJ hW ih

end GlobalTheory.CompanionTheory.RedCov

namespace GlobalTheory.CompanionTheory.RedCov

theorem torus_neg {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {σ : E →ₐ[F] E} {n r : ℕ} {J : Matrix (Fin n) (Fin n) E} {X Y : Matrix (Fin n) (Fin r) E}
    {a : (Fin r → ℝ) → GAd σ J} (ha : IsTorus σ J X Y a) (s : Fin r → ℝ) : a (-s) = (a s)⁻¹ := by
  rw [eq_inv_iff_mul_eq_one, ← ha.add, neg_add_cancel, torus_zero ha]

theorem conj_mem_one {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {σ : E →ₐ[F] E} {n r : ℕ} {J : Matrix (Fin n) (Fin n) E} (h : IsCMExt F E σ) (hJ : IsHermND σ J)
    {X Y : Matrix (Fin n) (Fin r) E} (hW : IsWittFrame σ J X Y) {a : (Fin r → ℝ) → GAd σ J} (ha : IsTorus σ J X Y a)
    (s : Fin r → ℝ) {x : GAd σ J} (hx : x ∈ minParOne σ J X) : a s * x * (a s)⁻¹ ∈ minParOne σ J X := by
  obtain ⟨τ, -, h2, h3, h4, h5⟩ := exists_tau h hJ hW ha
  have e : τ (ha.sub h hJ hW s * ⟨x, minParOne_subset hx⟩ * ha.sub h hJ hW (-s)) = 0 := by
    rw [h2, h2, h3, h3, h4 x hx]
    simp
  have := h5 (ha.sub h hJ hW s * ⟨x, minParOne_subset hx⟩ * ha.sub h hJ hW (-s))
  rw [e, torus_zero ha, inv_one, mul_one] at this
  have e2 : ((ha.sub h hJ hW s * ⟨x, minParOne_subset hx⟩ * ha.sub h hJ hW (-s) : minParSub X h hJ hW) : GAd σ J) =
      a s * x * (a s)⁻¹ := by
    rw [← torus_neg ha]
    rfl
  rwa [e2] at this

theorem cov_main : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ (r : ℕ) (X Y : Matrix (Fin n) (Fin r) E), IsWittFrame σ J X Y → ∀ K : Subgroup (GAd σ J), IsCompact (K : Set (GAd σ J)) → (∀ g, ∃ p ∈ minPar σ J X, ∃ k ∈ K, g = p * k) → GoodPosition σ J X Y K → ∃ (Ω : Set (GAd σ J)) (c : ℝ), IsCompact Ω ∧ Ω ⊆ minParOne σ J X ∧ 0 < c ∧ ∀ g, ∃ γ ∈ ratPts σ J, ∃ s ∈ siegelSet σ J X Y Ω c K, g = γ * s := by
  intro F E _ _ _ _ _ σ h n J hJ r X Y hW K hKc hIw _
  obtain ⟨a, ha⟩ := exists_isTorus h hJ hW
  obtain ⟨C, c, hC, hc, hred⟩ := hasRed_all h r n J X Y hJ hW a ha
  obtain ⟨Ω, hΩc, hΩ1, hΩ⟩ := GlobalTheory.T.minimal_parabolic_rational_compact F E σ h n J hJ r X Y hW
  obtain ⟨τ, hτc, hτadd, hτa, hτ1, hτp⟩ := exists_tau h hJ hW ha
  have hD : IsCompact ((C * (K : Set (GAd σ J))) ∩ minPar σ J X) :=
    (hC.mul hKc).inter_right (isClosed_minPar h hJ hW)
  have hT : IsCompact (Subtype.val ⁻¹' ((C * (K : Set (GAd σ J))) ∩ minPar σ J X) : Set (minParSub X h hJ hW)) := by
    have hcl : IsClosed ((minParSub X h hJ hW : Subgroup (GAd σ J)) : Set (GAd σ J)) := isClosed_minPar h hJ hW
    exact hcl.isClosedEmbedding_subtypeVal.isCompact_preimage hD
  obtain ⟨B, hB⟩ := hT.exists_bound_of_continuousOn hτc.continuousOn
  have hB0 : ∀ p ∈ (Subtype.val ⁻¹' ((C * (K : Set (GAd σ J))) ∩ minPar σ J X) : Set (minParSub X h hJ hW)),
      ∀ i, |τ p i| ≤ max B 0 := fun p hp i =>
    ((norm_le_pi_norm (τ p) i).trans (hB p hp)).trans (le_max_left _ _)
  set B' := max B 0 with hB'
  have hB'0 : 0 ≤ B' := le_max_right _ _
  refine ⟨Ω, c * Real.exp (-(2 * B')), hΩc, hΩ1, mul_pos hc (Real.exp_pos _), fun g => ?_⟩
  obtain ⟨γ, hγ, q, hq, s, hs, κ, hκ, hg⟩ := hred g
  obtain ⟨p, hp, k, hk, hκe⟩ := hIw κ
  have hpD : p ∈ (C * (K : Set (GAd σ J))) ∩ minPar σ J X := by
    refine ⟨?_, hp⟩
    have : p = κ * k⁻¹ := by rw [hκe]; group
    rw [this]
    exact Set.mul_mem_mul hκ (inv_mem hk)
  set pP : minParSub X h hJ hW := ⟨p, hp⟩ with hpP
  set u := τ pP with hu
  have hub : ∀ i, |u i| ≤ B' := hB0 pP hpD
  have hp1 : p * (a u)⁻¹ ∈ minParOne σ J X := hτp pP
  have hQ := mul_mem_one h hJ hW ha hq (conj_mem_one h hJ hW ha s hp1)
  obtain ⟨δ, hδ, hδP, ω, hω, hQe⟩ := hΩ _ hQ
  have hge : g = (γ * δ) * (ω * a (s + u) * k) := by
    have e1 : γ * δ * (ω * a (s + u) * k) = γ * (δ * ω) * a (s + u) * k := by group
    rw [e1, ← hQe, ha.add, hg, hκe]
    group
  refine ⟨γ * δ, mul_mem hγ hδ, _, ⟨ω, hω, fun i => Real.exp ((s + u) i), ?_, a (s + u), ha.tor _, k, hk, rfl⟩, hge⟩
  obtain ⟨-, h2, h3⟩ := hs
  have hup : ∀ i, Real.exp (u i) ≤ Real.exp B' := fun i => Real.exp_le_exp.2 ((le_abs_self _).trans (hub i))
  have hlo : ∀ i, Real.exp (-B') ≤ Real.exp (u i) := fun i =>
    Real.exp_le_exp.2 (neg_le_of_abs_le (hub i))
  have e2 : Real.exp (-(2 * B')) * Real.exp B' = Real.exp (-B') := by
    rw [← Real.exp_add]; congr 1; ring
  refine ⟨fun i => Real.exp_pos _, fun i j hij => ?_, fun i hi => ?_⟩
  · have a1 := h2 i j hij
    simp only [Pi.add_apply, Real.exp_add]
    calc c * Real.exp (-(2 * B')) * (Real.exp (s j) * Real.exp (u j))
        ≤ c * Real.exp (-(2 * B')) * (Real.exp (s j) * Real.exp B') := by
          gcongr
          exact (le_abs_self _).trans (hub j)
      _ = (c * Real.exp (s j)) * (Real.exp (-(2 * B')) * Real.exp B') := by ring
      _ ≤ Real.exp (s i) * Real.exp (-B') := by
          rw [e2]
          exact mul_le_mul_of_nonneg_right a1 (Real.exp_pos _).le
      _ ≤ Real.exp (s i) * Real.exp (u i) := by
          gcongr
          exact neg_le_of_abs_le (hub i)
  · have a1 := h3 i hi
    simp only [Pi.add_apply, Real.exp_add]
    have e3 : Real.exp (-(2 * B')) ≤ Real.exp (-B') := Real.exp_le_exp.2 (by linarith)
    calc c * Real.exp (-(2 * B')) ≤ c * Real.exp (-B') := by gcongr
      _ ≤ Real.exp (s i) * Real.exp (-B') := mul_le_mul_of_nonneg_right a1 (Real.exp_pos _).le
      _ ≤ Real.exp (s i) * Real.exp (u i) := by
          gcongr
          exact neg_le_of_abs_le (hub i)

end GlobalTheory.CompanionTheory.RedCov

end
