import Mathlib
import Development.AutomorphicSpectrum.Proofs.MetricProofs.IsLocSec
import Development.AutomorphicSpectrum.Proofs.MetricProofs.MinorIJMap
import Development.AutomorphicSpectrum.Proofs.MetricProofs.HoloOnDivCongr
import Development.AutomorphicSpectrum.Proofs.MetricProofs.FrameChangeScalarFactor
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq GlobalTheory.CompanionTheory.Ar.PB.WSq.Sec GlobalTheory.CompanionTheory.Ar.PB.CovMap.LocImg

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.WSq.Sec.Factor

section Holo

variable {e : ℕ} {S : Type} [TopologicalSpace S]

theorem holoOn_mono (A : FinHolAtlas e S) {U V : Set S} {f : S → ℂ} (h : A.HoloOn V f) (hU : U ⊆ V) :
    A.HoloOn U f :=
  fun j => (h j).mono (Set.inter_subset_inter_right _ (Set.preimage_mono hU))

theorem holoOn_const (A : FinHolAtlas e S) (U : Set S) (c : ℂ) : A.HoloOn U fun _ => c := fun _ _ _ =>
  analyticAt_const

theorem holoOn_mul (A : FinHolAtlas e S) {U : Set S} {f g : S → ℂ} (hf : A.HoloOn U f) (hg : A.HoloOn U g) :
    A.HoloOn U fun w => f w * g w := fun j u hu => (hf j u hu).mul (hg j u hu)

theorem holoOn_zpow (A : FinHolAtlas e S) {U : Set S} {f : S → ℂ} (hf : A.HoloOn U f)
    (h0 : ∀ w ∈ U, f w ≠ 0) (n : ℤ) : A.HoloOn U fun w => f w ^ n := fun j u hu =>
  (hf j u hu).zpow (h0 _ hu.2)

theorem holoOn_prod (A : FinHolAtlas e S) {U : Set S} {κ : Type} (s : Finset κ) {f : κ → S → ℂ}
    (hf : ∀ i ∈ s, A.HoloOn U (f i)) : A.HoloOn U fun w => ∏ i ∈ s, f i w := by
  induction s using Finset.induction_on with
  | empty => simpa using holoOn_const A U 1
  | insert i s hi ih =>
    have h := holoOn_mul A (hf i (Finset.mem_insert_self i s))
      (ih fun k hk => hf k (Finset.mem_insert_of_mem hk))
    simpa only [Finset.prod_insert hi] using h

theorem holoOn_minor (A : FinHolAtlas e S) {U : Set S} {N : ℕ} {H : S → Matrix (Fin N) (Fin N) ℂ}
    (hH : ∀ r s, A.HoloOn U fun w => H w r s) (I J : Finset (Fin N)) :
    A.HoloOn U fun w => minorIJ (H w) I J := by
  have h := StepW.ValHolo.holoOn_eval A (b := fun w (q : Fin N × Fin N) => H w q.1 q.2) (fun q => hH q.1 q.2)
    (minorIJ (Matrix.of fun r s => (MvPolynomial.X (r, s) : MvPolynomial (Fin N × Fin N) ℤ)) I J)
  have e : (fun w => minorIJ (H w) I J) = fun w => eval (fun q : Fin N × Fin N => H w q.1 q.2)
      (map (Int.castRingHom ℂ)
        (minorIJ (Matrix.of fun r s => (MvPolynomial.X (r, s) : MvPolynomial (Fin N × Fin N) ℤ)) I J)) := by
    funext w
    let f : MvPolynomial (Fin N × Fin N) ℤ →+* ℂ :=
      (eval fun q : Fin N × Fin N => H w q.1 q.2).comp (map (Int.castRingHom ℂ))
    have hm : (Matrix.of fun r s => (MvPolynomial.X (r, s) : MvPolynomial (Fin N × Fin N) ℤ)).map f = H w := by
      ext r s
      simp [f]
    have := minorIJ_map f (Matrix.of fun r s => (MvPolynomial.X (r, s) : MvPolynomial (Fin N × Fin N) ℤ)) I J
    rw [hm] at this
    exact this
  rw [e]
  exact h

theorem prod_local (A : FinHolAtlas e S) {V : Set S} {y₀ : S} {N : ℕ} (hV : IsOpen V) (hy : y₀ ∈ V)
    (g : Fin N → S → ℂ) (n : Fin N → ℤ)
    (key : ∀ i, ∃ W : Set S, IsOpen W ∧ y₀ ∈ W ∧ W ⊆ V ∧ A.HoloOn W (g i) ∧ ∀ w ∈ W, g i w ≠ 0) :
    ∃ V' : Set S, IsOpen V' ∧ y₀ ∈ V' ∧ V' ⊆ V ∧ A.HoloOn V' (fun w => ∏ i, g i w ^ n i) ∧
      ∀ w ∈ V', ∏ i, g i w ^ n i ≠ 0 := by
  choose W hW hyW hWV hh h0 using key
  have hsub : ∀ i, V ∩ ⋂ i, W i ⊆ W i := fun i => Set.inter_subset_right.trans (Set.iInter_subset _ i)
  refine ⟨V ∩ ⋂ i, W i, hV.inter (isOpen_iInter_of_finite hW), ⟨hy, Set.mem_iInter.2 hyW⟩,
    Set.inter_subset_left, ?_, ?_⟩
  · exact holoOn_prod A _ fun i _ =>
      holoOn_zpow A (holoOn_mono A (hh i) (hsub i)) (fun w hw => h0 i w (hsub i hw)) (n i)
  · exact fun w hw => Finset.prod_ne_zero_iff.2 fun i _ => zpow_ne_zero _ (h0 i w (hsub i hw))

end Holo

theorem minor_w_ne {N j : ℕ} (hj : j ≤ N) (i : Fin N) (hi : (i : ℕ) + 1 = j) {T : Matrix (Fin N) (Fin N) ℂ}
    (hT : IsBlockDiag j T) (hd : T.det ≠ 0) : minorIJ T (wIdx N j) (wIdx N j) ≠ 0 := by
  have h := FrameChange.detFac_ne_zero hj i hT hd
  rw [detFac, if_pos hi.ge] at h
  exact left_ne_zero_of_mul h

theorem minor_om_ne {N j : ℕ} (hj : j ≤ N) (i : Fin N) (hi : (i : ℕ) + 1 = N) {T : Matrix (Fin N) (Fin N) ℂ}
    (hT : IsBlockDiag j T) (hd : T.det ≠ 0) : minorIJ T (omIdx N j) (omIdx N j) ≠ 0 := by
  have h := FrameChange.detFac_ne_zero hj i hT hd
  rw [detFac, if_pos hi] at h
  exact right_ne_zero_of_mul h

theorem val_ne {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω]
    {x : (Σ k, ι k) → Ω} {z : (Σ k, ι k) → ℂ} (hz : z ∈ mcPts (mCoordIdeal x)) {s : Ω} (h0 : s ≠ 0)
    (hs : RegAt x (mCoordIdeal z) s) (hi : RegAt x (mCoordIdeal z) s⁻¹) : valAt x s z ≠ 0 := by
  intro e
  have h := (reg_mul hz hs hi).2
  rw [mul_inv_cancel₀ h0, e, zero_mul] at h
  exact one_ne_zero (((ValRing.regAt_valAt_ring K ι Ω x z hz).2.2.2.1).symm.trans h)

theorem improper_factor : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (e : ℕ) (X : Type) [TopologicalSpace X] (A : FinHolAtlas e X) (V : Set X) (y₀ : X) (zb : X → (Σ k, baseIdx ι M.blk k) → ℂ) (Hm : X → Matrix (Fin N) (Fin N) ℂ) (F : FrameData ι Ψ N M.Ω M.blk) (τ : Ψ) (a : Fin N), IsOpen V → y₀ ∈ V → (∀ q, A.HoloOn V fun w => zb w q) → (∀ w ∈ V, zb w ∈ mcPts (mCoordIdeal M.x)) → (∀ w ∈ V, M.GoodAt F (mCoordIdeal (zb w))) → (∀ r s, A.HoloOn V fun w => Hm w r s) → (∀ w ∈ V, IsBlockDiag j (Hm w) ∧ (Hm w).det ≠ 0) → ∃ V' : Set X, IsOpen V' ∧ y₀ ∈ V' ∧ V' ⊆ V ∧ A.HoloOn V' (fun w => ∏ i : Fin N, (if IsProperStep N j i then 1 else valAt M.x (F.υ (τ, i)) (zb w) * (if (i : ℕ) + 1 = j then (if (a : ℕ) < j then minorIJ (Hm w) (wIdx N j) (wIdx N j) else 1) else minorIJ (Hm w) (omIdx N j) (omIdx N j))) ^ xiCoef τ a (τ, i)) ∧ ∀ w ∈ V', (∏ i : Fin N, (if IsProperStep N j i then 1 else valAt M.x (F.υ (τ, i)) (zb w) * (if (i : ℕ) + 1 = j then (if (a : ℕ) < j then minorIJ (Hm w) (wIdx N j) (wIdx N j) else 1) else minorIJ (Hm w) (omIdx N j) (omIdx N j))) ^ xiCoef τ a (τ, i)) ≠ 0 := by
  intro K _ ι _ Φ _ y Ψ _ _ N j M e X _ A V y₀ zb Hm F τ a hV hy hzb hpt hgood hHm hdiag
  refine prod_local A hV hy (fun i w => if IsProperStep N j i then 1 else valAt M.x (F.υ (τ, i)) (zb w) *
    (if (i : ℕ) + 1 = j then (if (a : ℕ) < j then minorIJ (Hm w) (wIdx N j) (wIdx N j) else 1)
      else minorIJ (Hm w) (omIdx N j) (omIdx N j))) (fun i => xiCoef τ a (τ, i)) fun i => ?_
  by_cases hp : IsProperStep N j i
  · refine ⟨V, hV, hy, subset_rfl, ?_, fun w _ => ?_⟩
    · simp only [if_pos hp]
      exact holoOn_const A V 1
    · simp only [if_pos hp]
      exact one_ne_zero
  · have hnone : M.blk (τ, i) = none := (M.blk_none (τ, i)).2 hp
    obtain ⟨W, hW, hyW, hWV, hval⟩ := StepW.ValHolo.holoOn_valAt _ _ M.Ω M.x (F.υ (τ, i)) e X A V zb y₀ hV hy hzb hpt
      ((hgood y₀ hy).2.2 _ hnone).2.1
    have hm : A.HoloOn W fun w => (if (i : ℕ) + 1 = j then (if (a : ℕ) < j then minorIJ (Hm w) (wIdx N j) (wIdx N j) else 1)
        else minorIJ (Hm w) (omIdx N j) (omIdx N j)) := by
      have hH : ∀ r s, A.HoloOn W fun w => Hm w r s := fun r s => holoOn_mono A (hHm r s) hWV
      by_cases h1 : (i : ℕ) + 1 = j
      · by_cases h2 : (a : ℕ) < j
        · simp only [if_pos h1, if_pos h2]
          exact holoOn_minor A hH _ _
        · simp only [if_pos h1, if_neg h2]
          exact holoOn_const A W 1
      · simp only [if_neg h1]
        exact holoOn_minor A hH _ _
    refine ⟨W, hW, hyW, hWV, ?_, fun w hw => ?_⟩
    · simp only [if_neg hp]
      exact holoOn_mul A hval hm
    · simp only [if_neg hp]
      have hwV := hWV hw
      have hv : valAt M.x (F.υ (τ, i)) (zb w) ≠ 0 :=
        val_ne (hpt w hwV) ((hgood w hwV).2.2 _ hnone).1 ((hgood w hwV).2.2 _ hnone).2.1
          ((hgood w hwV).2.2 _ hnone).2.2
      refine mul_ne_zero hv ?_
      by_cases h1 : (i : ℕ) + 1 = j
      · by_cases h2 : (a : ℕ) < j
        · simp only [if_pos h1, if_pos h2]
          exact minor_w_ne M.j_le i h1 (hdiag w hwV).1 (hdiag w hwV).2
        · simp only [if_pos h1, if_neg h2]
          exact one_ne_zero
      · simp only [if_neg h1]
        have h3 : (i : ℕ) + 1 = N := by
          by_contra h3
          exact hp ⟨h1, h3⟩
        exact minor_om_ne M.j_le i h3 (hdiag w hwV).1 (hdiag w hwV).2

end GlobalTheory.CompanionTheory.Ar.PB.WSq.Sec.Factor
