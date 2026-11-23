import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PTwoBlockCoeffCycle
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PChangeOfLattice
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

namespace TwoBlockHorizDiv

section Local

variable {R : Type*} [CommRing R]

theorem length_loc_eq (W : Ideal R) [W.IsPrime] {J₁ J₂ : Ideal R} (h : J₁ ≤ J₂) {t : R} (ht : t ∉ W)
    (htJ : ∀ a ∈ J₂, t * a ∈ J₁) :
    Module.length (Localization.AtPrime W) (LocalizedModule W.primeCompl (R ⧸ J₁)) =
      Module.length (Localization.AtPrime W) (LocalizedModule W.primeCompl (R ⧸ J₂)) := by
  let q : (R ⧸ J₁) →ₗ[R] (R ⧸ J₂) := Submodule.factor h
  let φ := IsLocalizedModule.mapExtendScalars W.primeCompl (LocalizedModule.mkLinearMap W.primeCompl (R ⧸ J₁))
    (LocalizedModule.mkLinearMap W.primeCompl (R ⧸ J₂)) (Localization.AtPrime W) q
  have hsurj : Function.Surjective φ :=
    IsLocalizedModule.map_surjective W.primeCompl _ _ q (Submodule.factor_surjective h)
  have hinj : Function.Injective φ := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro y hy
    induction y using LocalizedModule.induction_on with
    | h m s =>
      obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective _ m
      have h0 : LocalizedModule.mk (q (Submodule.Quotient.mk a)) s = 0 := by
        rw [← hy]
        exact (IsLocalizedModule.map_LocalizedModules W.primeCompl q _ s).symm
      rw [IsLocalizedModule.mk_eq_mk', IsLocalizedModule.mk'_eq_zero'] at h0 ⊢
      obtain ⟨u, hu⟩ := h0
      refine ⟨⟨t, ht⟩ * u, ?_⟩
      change u • (Submodule.Quotient.mk a : R ⧸ J₂) = 0 at hu
      rw [Submonoid.smul_def, ← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero, smul_eq_mul] at hu ⊢
      have := htJ _ hu
      simpa [mul_assoc] using this
  exact (LinearEquiv.ofBijective φ ⟨hinj, hsurj⟩).length_eq

theorem multAt_eq_of_mul {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)]
    (W : Ideal (MRingOver R ι)) [W.IsPrime] {J₁ J₂ : Ideal (MRingOver R ι)} {t₁ t₂ : MRingOver R ι} (h₁ : t₁ ∉ W)
    (h₂ : t₂ ∉ W) (hJ₁ : ∀ a ∈ J₂, t₁ * a ∈ J₁) (hJ₂ : ∀ a ∈ J₁, t₂ * a ∈ J₂) : multAt J₁ W = multAt J₂ W := by
  have e₁ := length_loc_eq W (le_sup_left : J₁ ≤ J₁ ⊔ J₂) h₁ fun a ha => by
    obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.mp ha
    rw [mul_add]
    exact J₁.add_mem (J₁.mul_mem_left _ hy) (hJ₁ z hz)
  have e₂ := length_loc_eq W (le_sup_right : J₂ ≤ J₁ ⊔ J₂) h₂ fun a ha => by
    obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.mp ha
    rw [mul_add]
    exact J₂.add_mem (hJ₂ y hy) (J₂.mul_mem_left _ hz)
  unfold multAt
  rw [dif_pos ‹W.IsPrime›, dif_pos ‹W.IsPrime›, e₁, e₂]

theorem mem_minimalPrimes_iff {I₁ I₂ W : Ideal R}
    (h : ∀ Q : Ideal R, Q.IsPrime → Q ≤ W → (I₁ ≤ Q ↔ I₂ ≤ Q)) :
    W ∈ I₁.minimalPrimes ↔ W ∈ I₂.minimalPrimes := by
  have key : ∀ {I₁ I₂ : Ideal R}, (∀ Q : Ideal R, Q.IsPrime → Q ≤ W → (I₁ ≤ Q ↔ I₂ ≤ Q)) →
      W ∈ I₁.minimalPrimes → W ∈ I₂.minimalPrimes := by
    intro I₁ I₂ h hW
    refine ⟨⟨hW.1.1, (h W hW.1.1 le_rfl).1 hW.1.2⟩, fun Q hQ hQW => hW.2 ⟨hQ.1, (h Q hQ.1 hQW).2 hQ.2⟩ hQW⟩
  exact ⟨key h, key fun Q hQ hQW => (h Q hQ hQW).symm⟩

end Local

variable {Ω : Type} [Field Ω] [CharZero Ω] {κ : Type} [Fintype κ]

theorem rel_mem' {x x' : Ix κ → Ω} {c : κ} {l : Ix κ → ℤ} (hl : x ⟨(), c⟩ = ∑ j, (l j : Ω) * x' j)
    (k : Ix κ) (n : Ix κ → ℤ) (hn : ∑ j, (n j : Ω) * x' j = x k) :
    X ⟨0, k.2⟩ * twoBlockNum l - X ⟨0, c⟩ * ∑ j : Ix κ, C (n j) * X ⟨1, j.2⟩ ∈ twoBlockIdeal x x' := by
  show mConeMap (pair x x') _ = 0
  rw [map_sub, map_mul, map_mul, TwoBlockCoeffCycle.mConeMap_X, TwoBlockCoeffCycle.mConeMap_X, twoBlockNum,
    TwoBlockCoeffCycle.mConeMap_lin, TwoBlockCoeffCycle.mConeMap_lin]
  simp only [TwoBlockCoeffCycle.pair_one, TwoBlockCoeffCycle.pair_zero', ← hl, hn]
  ring

theorem intCast_not_mem {ι : Fin 2 → Type} [∀ k, Fintype (ι k)] {Q : Ideal (MRing ι)} (hQ : IsHorizontal Q) {d : ℤ}
    (hd : d ≠ 0) : (d : MRing ι) ∉ Q := by
  intro h
  have : d ∈ Q.comap (C : ℤ →+* MRing ι) := by
    rw [Ideal.mem_comap, eq_intCast]
    exact h
  rw [hQ, Ideal.mem_bot] at this
  exact hd this

theorem mul_mem_of_sup {R : Type*} [CommRing R] {P J : Ideal R} {s t : R} (hP : P ≤ J) (hs : t * s ∈ J) :
    ∀ a ∈ P ⊔ Ideal.span {s}, t * a ∈ J := by
  intro a ha
  obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.mp ha
  obtain ⟨b, rfl⟩ := Ideal.mem_span_singleton'.mp hz
  rw [mul_add, mul_left_comm]
  exact J.add_mem (J.mul_mem_left _ (hP hy)) (J.mul_mem_left _ hs)

theorem den_rel {x : Ix κ → Ω} {B : Matrix (Ix κ) (Ix κ) ℚ} {c : κ} {l : Ix κ → ℤ}
    (hl : x ⟨(), c⟩ = ∑ j, (l j : Ω) * matAct B x j) :
    ∃ d : ℤ, d ≠ 0 ∧ ∀ j₀ : κ, (d : MRing (FinTwoTypeFamily κ)) * X ⟨0, c⟩ * X ⟨1, j₀⟩ ∈
      twoBlockIdeal x (matAct B x) ⊔ Ideal.span {twoBlockNum l} := by
  obtain ⟨d, hd0, hdB⟩ := ChangeOfLattice.exists_clear_den B
  refine ⟨d, by exact_mod_cast hd0, fun j₀ => ?_⟩
  let j : Ix κ := ⟨(), j₀⟩
  choose N hN using hdB j
  have hNx : ∑ k, (N k : Ω) * x k = ((d : ℤ) : Ω) * matAct B x j := by
    simp only [matAct, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    have : ((N k : ℚ) : Ω) = ((d : ℚ) : Ω) * ((B j k : ℚ) : Ω) := by rw [← hN k]; push_cast; ring
    push_cast at this ⊢
    rw [this]
    ring
  have hrel := TwoBlockCoeffCycle.rel_mem hl (d : ℤ) N j hNx
  have := Submodule.add_mem_sup hrel
    (Ideal.mul_mem_right (∑ k : Ix κ, C (N k) * X ⟨0, k.2⟩) _ (Ideal.mem_span_singleton_self (twoBlockNum l)))
  simpa using this

theorem num_rel {x : Ix κ → Ω} {B : Matrix (Ix κ) (Ix κ) ℚ} {c : κ} {l : Ix κ → ℤ}
    (hsp : Submodule.span ℤ (Set.range x) ≤ Submodule.span ℤ (Set.range (matAct B x)))
    (hl : x ⟨(), c⟩ = ∑ j, (l j : Ω) * matAct B x j) (i₀ : κ) :
    X ⟨0, i₀⟩ * twoBlockNum l ∈ twoBlockIdeal x (matAct B x) ⊔ Ideal.span {twoBlockDen c} := by
  let k : Ix κ := ⟨(), i₀⟩
  have hk : x k ∈ Submodule.span ℤ (Set.range (matAct B x)) := hsp (Submodule.subset_span ⟨k, rfl⟩)
  obtain ⟨n, hn⟩ := (Submodule.mem_span_range_iff_exists_fun ℤ).mp hk
  have hn' : ∑ j, (n j : Ω) * matAct B x j = x k := by simpa [zsmul_eq_mul] using hn
  have hrel := rel_mem' hl k n hn'
  have := Submodule.add_mem_sup hrel
    (Ideal.mul_mem_right (∑ j : Ix κ, C (n j) * X ⟨1, j.2⟩) _ (Ideal.mem_span_singleton_self (twoBlockDen c)))
  simpa [twoBlockDen] using this

theorem sup_le_iff_of_horiz {x : Ix κ → Ω} {B : Matrix (Ix κ) (Ix κ) ℚ} {c : κ} {l : Ix κ → ℤ}
    (hsp : Submodule.span ℤ (Set.range x) ≤ Submodule.span ℤ (Set.range (matAct B x)))
    (hl : x ⟨(), c⟩ = ∑ j, (l j : Ω) * matAct B x j) {Q : Ideal (MRing (FinTwoTypeFamily κ))} (hQ : Q.IsPrime)
    (hH : IsHorizontal Q) (hR : IsRelevant Q) :
    twoBlockIdeal x (matAct B x) ⊔ Ideal.span {twoBlockNum l} ≤ Q ↔
      twoBlockIdeal x (matAct B x) ⊔ Ideal.span {twoBlockDen c} ≤ Q := by
  obtain ⟨i₀, hi₀⟩ := hR 0
  obtain ⟨j₀, hj₀⟩ := hR 1
  obtain ⟨d, hd0, hd⟩ := den_rel (c := c) (l := l) hl
  constructor
  · intro h
    refine sup_le (le_sup_left.trans h) ((Ideal.span_singleton_le_iff_mem _).2 ?_)
    rcases hQ.mem_or_mem (h (hd j₀)) with h1 | h1
    · rcases hQ.mem_or_mem h1 with h2 | h2
      · exact absurd h2 (intCast_not_mem hH hd0)
      · exact h2
    · exact absurd h1 hj₀
  · intro h
    refine sup_le (le_sup_left.trans h) ((Ideal.span_singleton_le_iff_mem _).2 ?_)
    rcases hQ.mem_or_mem (h (num_rel hsp hl i₀)) with h1 | h1
    · exact absurd h1 hi₀
    · exact h1

end TwoBlockHorizDiv

open TwoBlockHorizDiv in

theorem TwoBlockHorizDiv.proof : TwoBlockHorizDiv.Statement := by
  intro Ω _ _ κ _ x B c l hsp hl W hW
  have hiff : IsRelevant W → ∀ Q : Ideal (MRing (FinTwoTypeFamily κ)), Q.IsPrime → Q ≤ W →
      (twoBlockIdeal x (matAct B x) ⊔ Ideal.span {twoBlockNum l} ≤ Q ↔
        twoBlockIdeal x (matAct B x) ⊔ Ideal.span {twoBlockDen c} ≤ Q) := by
    intro hr Q hQ hQW
    have hH : IsHorizontal Q := by
      unfold IsHorizontal at hW ⊢
      exact le_bot_iff.mp (hW ▸ Ideal.comap_mono hQW)
    have hR : IsRelevant Q := fun k => (hr k).imp fun i hi h => hi (hQW h)
    exact sup_le_iff_of_horiz hsp hl hQ hH hR
  refine ⟨⟨fun ⟨hm, hr⟩ => ⟨(mem_minimalPrimes_iff (hiff hr)).1 hm, hr⟩,
    fun ⟨hm, hr⟩ => ⟨(mem_minimalPrimes_iff (hiff hr)).2 hm, hr⟩⟩, ?_⟩
  rintro ⟨hm, hr⟩
  have : W.IsPrime := hm.1.1
  obtain ⟨i₀, hi₀⟩ := hr 0
  obtain ⟨j₀, hj₀⟩ := hr 1
  obtain ⟨d, hd0, hd⟩ := den_rel (c := c) (l := l) hl
  refine multAt_eq_of_mul W (t₁ := (d : MRing (FinTwoTypeFamily κ)) * X ⟨1, j₀⟩) (t₂ := X ⟨0, i₀⟩) ?_ hi₀ ?_ ?_
  · intro h
    rcases Ideal.IsPrime.mem_or_mem ‹W.IsPrime› h with h1 | h1
    · exact intCast_not_mem hW hd0 h1
    · exact hj₀ h1
  · refine mul_mem_of_sup le_sup_left ?_
    have : (d : MRing (FinTwoTypeFamily κ)) * X ⟨1, j₀⟩ * twoBlockDen c = (d : MRing (FinTwoTypeFamily κ)) * X ⟨0, c⟩ * X ⟨1, j₀⟩ := by
      rw [twoBlockDen]; ring
    rw [this]
    exact hd j₀
  · exact mul_mem_of_sup le_sup_left (num_rel hsp hl i₀)

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
