import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ConjugateOrderData
open NumberField IsDedekindDomain TensorProduct GlobalTheory.CMVal GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations
open Classical

namespace GlobalTheory.PairingBound

section V
variable (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CharZero O] {K : Type} [Field K] [Algebra O K]
  [IsFractionRing O K]

theorem ord_mul' {a b : K} (ha : a ≠ 0) (hb : b ≠ 0) : ord_vw O (a * b) = ord_vw O a + ord_vw O b := by
  unfold ord_vw
  rw [map_mul, WithZero.log_mul ((Valuation.ne_zero_iff _).2 ha) ((Valuation.ne_zero_iff _).2 hb), neg_add]

theorem ord_alg_nonneg (x : O) (hx : x ≠ 0) : 0 ≤ ord_vw O (algebraMap O K x) := by
  have hx' : algebraMap O K x ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective O K)).2 hx
  have h2 : (IsDiscreteValuationRing.maximalIdeal O).valuation K (algebraMap O K x) ≠ 0 :=
    (Valuation.ne_zero_iff _).2 hx'
  have h1 : (IsDiscreteValuationRing.maximalIdeal O).valuation K (algebraMap O K x) ≤ 1 := by
    rw [HeightOneSpectrum.valuation_of_algebraMap]; exact HeightOneSpectrum.intValuation_le_one _ x
  unfold ord_vw
  rw [← WithZero.exp_log h2, ← WithZero.exp_zero, WithZero.exp_le_exp] at h1
  linarith

theorem ord_l_pos (l : ℕ) (hl : l ≠ 0) (h : (l : O) ∈ IsLocalRing.maximalIdeal O) : 0 < ord_vw O (l : K) := by
  have h0 : (l : K) ≠ 0 := by
    rw [← map_natCast (algebraMap O K)]
    exact (map_ne_zero_iff _ (IsFractionRing.injective O K)).2 (Nat.cast_ne_zero.2 hl)
  have h1 : (IsDiscreteValuationRing.maximalIdeal O).valuation K (l : K) < 1 := by
    rw [← map_natCast (algebraMap O K), HeightOneSpectrum.valuation_lt_one_iff_mem]
    exact h
  have h2 : (IsDiscreteValuationRing.maximalIdeal O).valuation K (l : K) ≠ 0 := by simpa using h0
  unfold ord_vw
  rw [← WithZero.exp_log h2, ← WithZero.exp_zero, WithZero.exp_lt_exp] at h1
  linarith

theorem val_nonneg (l : ℕ) (hl : l ≠ 0) (h : (l : O) ∈ IsLocalRing.maximalIdeal O) (x : O) :
    0 ≤ val_vp O l (algebraMap O K x) := by
  unfold val_vp
  split_ifs with hx
  · exact le_top
  · have hx' : x ≠ 0 := by rintro rfl; exact hx (map_zero _)
    exact WithTop.coe_le_coe.2 (div_nonneg (by exact_mod_cast ord_alg_nonneg O x hx')
      (by exact_mod_cast (ord_l_pos O (K := K) l hl h).le))

theorem val_le_of_dvd (l : ℕ) (hl : l ≠ 0) (h : (l : O) ∈ IsLocalRing.maximalIdeal O) {x y : O} (hy : y ≠ 0)
    (hxy : x ∣ y) : val_vp O l (algebraMap O K x) ≤ val_vp O l (algebraMap O K y) := by
  obtain ⟨z, rfl⟩ := hxy
  have hx : x ≠ 0 := left_ne_zero_of_mul hy
  have hz : z ≠ 0 := right_ne_zero_of_mul hy
  have inj := IsFractionRing.injective O K
  have hx' : algebraMap O K x ≠ 0 := (map_ne_zero_iff _ inj).2 hx
  have hz' : algebraMap O K z ≠ 0 := (map_ne_zero_iff _ inj).2 hz
  have hy' : algebraMap O K (x * z) ≠ 0 := (map_ne_zero_iff _ inj).2 hy
  unfold val_vp
  rw [if_neg hx', if_neg hy', map_mul, ord_mul' O hx' hz']
  refine WithTop.coe_le_coe.2 (div_le_div_of_nonneg_right ?_ (by exact_mod_cast (ord_l_pos O (K := K) l hl h).le))
  push_cast
  linarith [(by exact_mod_cast ord_alg_nonneg O z hz : (0 : ℚ) ≤ ord_vw O (algebraMap O K z))]

end V

end GlobalTheory.PairingBound

namespace GlobalTheory.PairingBound

theorem pairing_val_bounds : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (c : Ideal (OF E)), c ≠ ⊥ → ∀ (l : ℕ), l.Prime → ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CharZero O] (K : Type) [Field K] [Algebra O K] [IsFractionRing O K], (l : O) ∈ IsLocalRing.maximalIdeal O → Nat.card (E →+* K) = Module.finrank ℚ E → ∀ (D : O), D ≠ 0 → ClearsIdem K c D → ∀ (I : Type) [Fintype I] (φ : I → E →+* K), IsCMTypeIn φ → ∀ (H : Type) [AddCommGroup H] [Module O H] (ρ : orderC c →+* Module.End O H) (Fil : Submodule O H) (B : LinearMap.BilinForm O H), IsCMLattice φ ρ Fil B → EigenClaims φ ρ Fil B D → ∀ e f : I → H, IsGens φ ρ e f → ∀ i, 0 ≤ val_vp O l (algebraMap O K (B (e i) (f i))) ∧ val_vp O l (algebraMap O K (B (e i) (f i))) ≤ val_vp O l (algebraMap O K D) := by
  intro E _ _ _ c _ l hl O _ _ _ _ K _ _ _ hlm _ D hD _ I _ φ _ H _ _ ρ Fil B hLat hEig e f hGen i
  obtain ⟨hfree, -, -, -, -, -, hbij, halt, -⟩ := hLat
  obtain ⟨-, hsat, ⟨-, hsum⟩, -, horth⟩ := hEig
  obtain ⟨he, hf⟩ := hGen i
  haveI := hfree
  obtain ⟨-, ⟨g, hg0, hgs⟩, -, -, C, hC⟩ := hsat (φ i)
  have he0 : e i ≠ 0 := by
    intro h0
    rw [he, h0, Submodule.span_singleton_eq_bot.2 rfl] at hgs
    exact hg0 (Submodule.span_singleton_eq_bot.1 hgs.symm)
  have heL : e i ∈ eigLat ρ (φ i) := by rw [he]; exact Submodule.mem_span_singleton_self _
  rw [he] at hC
  let lam : H →ₗ[O] O := ((LinearEquiv.toSpanNonzeroSingleton O H (e i) he0).symm.toLinearMap).comp
    (Submodule.linearProjOfIsCompl _ C hC)
  have hlam : lam (e i) = 1 := by
    simp only [lam, LinearMap.comp_apply, LinearEquiv.coe_coe]
    have hp : (Submodule.linearProjOfIsCompl _ C hC) (e i) = ⟨e i, Submodule.mem_span_singleton_self _⟩ :=
      Submodule.linearProjOfIsCompl_apply_left hC ⟨e i, Submodule.mem_span_singleton_self _⟩
    rw [hp, LinearEquiv.symm_apply_eq, LinearEquiv.toSpanNonzeroSingleton_one]
  obtain ⟨h, hh⟩ := hbij.2 lam
  have hBeh : B (e i) h = -1 := by
    rw [← LinearMap.IsAlt.neg halt h (e i), hh, hlam]
  have hle : (⨆ σ : E →+* K, eigLat ρ σ) ≤ LinearMap.ker (B (e i)) ⊔ (O ∙ f i) := by
    refine iSup_le fun σ => ?_
    by_cases hσ : σ = bar (φ i)
    · subst hσ; rw [hf]; exact le_sup_right
    · refine le_sup_of_le_left fun y hy => ?_
      rw [LinearMap.mem_ker]
      have h0 := horth (φ i) σ hσ _ heL _ hy
      simp only [inK, TensorProduct.mk_apply, LinearMap.BilinForm.baseChange_tmul, mul_one, Algebra.smul_def]
        at h0
      exact (IsFractionRing.injective O K) (by rw [h0, map_zero])
  obtain ⟨k, hk, y, hy, hky⟩ := Submodule.mem_sup.1 (hle (hsum h))
  obtain ⟨u, rfl⟩ := Submodule.mem_span_singleton.1 hy
  have hdiv : B (e i) (f i) ∣ D := by
    have h1 := congrArg (B (e i)) hky
    rw [map_add, LinearMap.mem_ker.1 hk, zero_add, map_smul, map_smul, hBeh, smul_eq_mul, smul_eq_mul] at h1
    exact ⟨-u, by linear_combination h1⟩
  exact ⟨val_nonneg O l hl.ne_zero hlm _, val_le_of_dvd O l hl.ne_zero hlm hD hdiv⟩

end GlobalTheory.PairingBound
