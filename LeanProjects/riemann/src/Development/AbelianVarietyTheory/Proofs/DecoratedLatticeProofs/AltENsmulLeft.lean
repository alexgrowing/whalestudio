import Mathlib
import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.AlternatingFormStandardHermitian
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HermitianCocycleIntegralOfLocalStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsNotMemDvdLocallyAway

open NumberField IsDedekindDomain Formalism.L2.Ker

noncomputable section

namespace GlobalTheory.TwPerSelfDual

open Formalism.L2.Col Formalism.HermitianLatticesTheory Formalism.L2.Th1.H

variable {E : Type} [Field E] [NumberField E] [StarRing E] {ι : Type} [Fintype ι] {a b : ℕ}

theorem hv_apply' (sc : ℝ) (z w : VV ι a b) :
    HV sc z w = (sc : ℂ) * ∑ τ, ∑ i, ∑ j, z τ i j * (starRingEnd ℂ) (w τ i j) := rfl

theorem embH_apply' (emb : ι → E →+* ℂ) (δ : ℂ) (x : HomE E a b) (τ : ι) (i : Fin b) (j : Fin a) :
    embH emb δ x τ i j = δ * emb τ (x (Pi.single j 1) i) := rfl

theorem hv_smul_emb (emb : ι → E →+* ℂ) (δ : ℂ) (sc : ℝ)
    (hst : ∀ (τ : ι) (x : E), emb τ (star x) = starRingEnd ℂ (emb τ x)) (r : E) (x y : HomE E a b) :
    HV sc (embH emb δ (r • x)) (embH emb δ y) = HV sc (embH emb δ x) (embH emb δ (star r • y)) := by
  rw [hv_apply', hv_apply']
  congr 1
  refine Finset.sum_congr rfl fun τ _ => Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  simp only [embH_apply', LinearMap.smul_apply, Pi.smul_apply, smul_eq_mul, map_mul, hst, Complex.conj_conj]
  ring

theorem embH_injective' [Nonempty ι] (emb : ι → E →+* ℂ) {δ : ℂ} (hδ : δ ≠ 0) :
    Function.Injective (embH emb δ : HomE E a b → VV ι a b) := by
  intro x y h
  obtain ⟨τ⟩ := ‹Nonempty ι›
  refine LinearMap.pi_ext' fun j => LinearMap.ext_ring ?_
  funext i
  have := congrFun (congrFun (congrFun h τ) i) j
  rw [embH_apply', embH_apply'] at this
  simpa using (emb τ).injective (mul_left_cancel₀ hδ this)

theorem altE_nsmul_left {V : Type} [AddCommGroup V] [Module ℂ V] (H : Sesq V) (n : ℕ) (v w : V) :
    altE H (n • v) w = altE H v (n • w) := by
  simp only [altE, map_nsmul, LinearMap.smul_apply]

section Mod

variable {W : Type} [AddCommGroup W] [Module E W] [Module (𝓞 E) W] [IsScalarTower (𝓞 E) E W]

theorem npow_smul_mem (L : Submodule (𝓞 E) W) (c n : ℕ) {y : W} (hy : y ∈ L) : ((c : E) ^ n) • y ∈ L := by
  induction n with
  | zero => simpa using hy
  | succ n ih => rw [pow_succ', mul_smul]; exact nat_smul_mem L c ih

theorem zpow_smul_mem (L : Submodule (𝓞 E) W) (c : ℕ) {k : ℤ} (hk : 0 ≤ k) {y : W} (hy : y ∈ L) :
    ((c : E) ^ k) • y ∈ L := by
  obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le hk
  rw [zpow_natCast]; exact npow_smul_mem L c n hy

end Mod

theorem twO_selfDual : ∀ (E : Type) [Field E] [NumberField E] [StarRing E] (ι : Type) [Fintype ι] [Nonempty ι] (a b : ℕ) (emb : ι → E →+* ℂ) (δ : ℂ) (d : ℕ) (sc : ℝ) (M : Submodule (𝓞 E) (Formalism.L2.Col.HomE E a b)) (c : ℕ) (e : HeightOneSpectrum (𝓞 E) → ℤ), δ ≠ 0 → (∀ (τ : ι) (x : E), emb τ (star x) = starRingEnd ℂ (emb τ x)) → 0 < c → (∀ Q, e (Formalism.L2.Col.conjPrime₂ Q) = -e Q) → (∀ Q, e Q = 1 ∨ e Q = 0 ∨ e Q = -1) → Formalism.L2.Th1.H.IsSelfDual (HV sc) (laV emb δ M) → Formalism.L2.Th1.H.IsSemiChar (HV sc) (laV emb δ M) (alV d sc) → Formalism.L2.Th1.H.IsSelfDual (HV sc) (laV emb δ (twist₂ M c e)) := by
  intro E _ _ _ ι _ _ a b emb δ d sc M c e hδ hst hc he her hSD hSC
  have hcE : (c : E) ≠ 0 := by exact_mod_cast hc.ne'
  have hstk : ∀ k : ℤ, star ((c : E) ^ k) = (c : E) ^ k := fun k => by rw [star_zpow₀, star_natCast]
  have hSD' : dualLat (HV sc) (laV emb δ M) = laV emb δ M := hSD
  have hdualM : ∀ z : HomE E a b, (∀ y ∈ M, ∃ m : ℤ, altE (HV sc) (embH emb δ z) (embH emb δ y) = m) → z ∈ M := by
    intro z hz
    have h1 : embH emb δ z ∈ dualLat (HV sc) (laV emb δ M) := by
      rintro _ ⟨y, hy, rfl⟩
      exact hz y hy
    rw [hSD'] at h1
    obtain ⟨z', hz', e'⟩ := h1
    rwa [← embH_injective' emb hδ e']
  have hcM : ∀ y ∈ M, (c : E) • y ∈ twist₂ M c e := by
    intro y hy
    rw [mem_twO]
    intro Q
    apply le_locP'
    rw [smul_smul, ← zpow_neg, ← zpow_add_one₀ hcE]
    apply zpow_smul_mem M c _ hy
    rcases her Q with h | h | h <;> rw [h] <;> norm_num
  show dualLat (HV sc) (laV emb δ (twist₂ M c e)) = laV emb δ (twist₂ M c e)
  apply le_antisymm
  · intro v hv
    have hcv : c • v ∈ dualLat (HV sc) (laV emb δ M) := by
      rintro _ ⟨y, hy, rfl⟩
      rw [altE_nsmul_left, ← map_nsmul]
      apply hv
      refine ⟨c • y, ?_, rfl⟩
      show c • y ∈ twist₂ M c e
      rw [← Nat.cast_smul_eq_nsmul E]
      exact hcM y hy
    rw [hSD'] at hcv
    obtain ⟨m, hm, hmv⟩ := hcv
    set x : HomE E a b := ((c : E)⁻¹) • m with hxdef
    have hxm : (c : E) • x = m := by rw [hxdef, smul_smul, mul_inv_cancel₀ hcE, one_smul]
    have hxv : embH emb δ x = v := by
      have h1 : c • embH emb δ x = c • v := by
        rw [← map_nsmul, ← Nat.cast_smul_eq_nsmul E, hxm]; exact hmv
      have hcC : (c : ℂ) ≠ 0 := by exact_mod_cast hc.ne'
      rw [← Nat.cast_smul_eq_nsmul ℂ, ← Nat.cast_smul_eq_nsmul ℂ] at h1
      exact smul_right_injective _ hcC h1
    refine ⟨x, ?_, hxv⟩
    show x ∈ twist₂ M c e
    rw [mem_twO]
    intro Q
    have hc2 : ((c : 𝓞 E) ^ 2) ≠ 0 := pow_ne_zero _ (by exact_mod_cast hc.ne')
    obtain ⟨t, ht, hwt⟩ := GlobalTheory.exists_not_mem_dvd_locally_away E (conjPrime₂ Q) _ hc2
    have hT : ∀ y ∈ M, (algebraMap (𝓞 E) E t * ((c : E) ^ e Q)⁻¹) • y ∈ twist₂ M c e := by
      intro y hy
      rw [mem_twO]
      intro Q'
      rw [smul_smul]
      by_cases hQ' : Q' = conjPrime₂ Q
      · subst hQ'
        rw [he Q, zpow_neg, inv_inv]
        have h1 : (c : E) ^ e Q * (algebraMap (𝓞 E) E t * ((c : E) ^ e Q)⁻¹) = algebraMap (𝓞 E) E t := by
          have : (c : E) ^ e Q ≠ 0 := zpow_ne_zero _ hcE
          field_simp
        rw [h1, IsScalarTower.algebraMap_smul]
        exact le_locP' M _ (M.smul_mem t hy)
      · obtain ⟨w, hw, z, hz⟩ := hwt Q' hQ'
        have hz' : algebraMap (𝓞 E) E w * algebraMap (𝓞 E) E t = (c : E) ^ 2 * algebraMap (𝓞 E) E z := by
          have := congrArg (algebraMap (𝓞 E) E) hz
          simpa using this
        have hn : (((2 - e Q' - e Q).toNat : ℕ) : ℤ) = 2 - e Q' - e Q :=
          Int.toNat_of_nonneg (by rcases her Q with h | h | h <;> rcases her Q' with h' | h' | h' <;> omega)
        refine loc_of_scal M Q' hw (ρ := (c : 𝓞 E) ^ (2 - e Q' - e Q).toNat * z) ?_ hy
        rw [map_mul, map_pow, map_natCast, ← zpow_natCast, hn, zpow_sub₀ hcE, zpow_sub₀ hcE, zpow_ofNat]
        linear_combination (((c : E) ^ e Q')⁻¹ * ((c : E) ^ e Q)⁻¹) * hz'
    refine ⟨cO E t, fun h => ht ((mem_conjP Q t).2 h), ?_⟩
    rw [← IsScalarTower.algebraMap_smul E (cO E t), smul_smul]
    apply hdualM
    intro y hy
    unfold altE
    rw [hv_smul_emb emb δ sc hst, star_mul', algebraMap_cO, star_star, star_inv₀, hstk, hxv]
    exact hv _ ⟨_, hT y hy, rfl⟩
  · rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    refine (GlobalTheory.T.hermitian_cocycle_integral_of_local E ι a b emb δ d sc M hδ hst hSD hSC x y fun Q =>
      ⟨(c : E) ^ e Q, zpow_ne_zero _ hcE, (mem_twO _ _ _ _).1 hx Q, ?_⟩).1
    rw [hstk]
    have := (mem_twO _ _ _ _).1 hy (conjPrime₂ Q)
    rwa [he Q, zpow_neg, inv_inv] at this

end GlobalTheory.TwPerSelfDual
