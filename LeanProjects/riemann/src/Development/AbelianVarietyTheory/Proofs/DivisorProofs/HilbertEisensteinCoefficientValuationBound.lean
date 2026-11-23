import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HasLevelStd
import Development.AbelianVarietyTheory.Definitions.Divisors.HasQIff
import Development.AbelianVarietyTheory.Definitions.Divisors.JetAnalytic
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AlgebraicValuationAtLeastAtEmbeddingRingOps
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHilbertEisensteinFourierCoeffFamilyStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OmegaFactorPowTwoMul
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasQExpansionOfLevelHilbertEisensteinQuasiPeriodStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSplitOfHilbertLatticeHasLevelStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AlgebraicValuationAtLeastInverseDifferentElement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AlgebraicValuationAtLeastRatCastAndExpRat
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PartialZetaConstTermEqRationalValueStatement
open NumberField UpperHalfPlane GlobalTheory.HilbFam GlobalTheory.QFam
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization (Emb Frac latM qPow upperHalf cK omegaFactor IsPartialZeta HasExpansion)
open GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates (iterD partialD)
open scoped Classical MatrixGroups nonZeroDivisors
open GlobalTheory.LatVal (Sz)
open GlobalTheory.LatJet (EisExp IsEis FR)

open NumberField UpperHalfPlane FractionalIdeal in
open scoped nonZeroDivisors in
variable {l : ℕ} [Fact l.Prime] {lam : algebraicClosure ℚ ℂ →+* ℂ_[l]} in
private theorem sz_mono_divisor {r s : ℝ} {x : ℂ} (hrs : r ≤ s)
    (hx : _root_.GlobalTheory.LatVal.Sz l lam r x) :
    _root_.GlobalTheory.LatVal.Sz l lam s x :=
  (_root_.GlobalTheory.QFam.SzSum.sz_ring l lam).2.2.2.1 r s x hrs hx

open NumberField UpperHalfPlane FractionalIdeal in
open scoped nonZeroDivisors in
private theorem valBound_embedding_mem_mul_lemma_2 {l : ℕ} [Fact l.Prime] {lam : algebraicClosure ℚ ℂ →+* ℂ_[l]}
    {F : Type} [Field F] [NumberField F] [IsTotallyReal F] [IsGalois ℚ F]
    {𝔞 𝔟 : _root_.GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.Frac F} {ρ₀ : ℝ} {M b : ℕ} (hM : ¬ l ∣ M)
    (ht : ((M * l ^ b : ℕ) : F) ∈ _root_.GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.latM 𝔞)
    (h𝔟 : ∀ β ∈ ((𝔟 : (FractionalIdeal (𝓞 F)⁰ F)ˣ) : FractionalIdeal (𝓞 F)⁰ F),
      ∀ i : _root_.GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.Emb F, _root_.GlobalTheory.LatVal.Sz l lam ρ₀ ((i β : ℝ) : ℂ))
    {ξ : F} (hξ : ξ ∈ (((𝔞 * 𝔟 : _root_.GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.Frac F) : (FractionalIdeal (𝓞 F)⁰ F)ˣ) :
      FractionalIdeal (𝓞 F)⁰ F)) (i : _root_.GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.Emb F) :
    _root_.GlobalTheory.LatVal.Sz l lam
      (b + (padicValInt l (discr F) : ℝ) / Module.finrank ℚ F + ρ₀) ((i ξ : ℝ) : ℂ) := by
  set t : F := ((M * l ^ b : ℕ) : F) with ht_def
  have hdual : ∀ α ∈ ((𝔞 : (FractionalIdeal (𝓞 F)⁰ F)ˣ) : FractionalIdeal (𝓞 F)⁰ F),
      t * α ∈ _root_.GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.latM (1 : _root_.GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.Frac F) := by
    intro α hα
    rw [_root_.GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.latM_eq_dual] at ht ⊢
    have h0 : ((𝔞 : (FractionalIdeal (𝓞 F)⁰ F)ˣ) : FractionalIdeal (𝓞 F)⁰ F) ≠ 0 := Units.ne_zero _
    have := FractionalIdeal.mul_mem_mul ht hα
    rw [FractionalIdeal.dual_mul_self ℤ ℚ h0] at this
    simpa using this
  have key : _root_.GlobalTheory.LatVal.Sz l lam
      ((padicValInt l (discr F) : ℝ) / Module.finrank ℚ F + ρ₀) ((i (t * ξ) : ℝ) : ℂ) := by
    rw [Units.val_mul, ← FractionalIdeal.mem_coe, FractionalIdeal.coe_mul] at hξ
    have hmul : t * ξ ∈ ({y | _root_.GlobalTheory.LatVal.Sz l lam
        ((padicValInt l (discr F) : ℝ) / Module.finrank ℚ F + ρ₀) ((i y : ℝ) : ℂ)} : Set F) := by
      refine Submodule.mul_induction_on hξ ?_ ?_
      · intro α hα β hβ
        show _root_.GlobalTheory.LatVal.Sz l lam _ _
        rw [← mul_assoc, map_mul, Complex.ofReal_mul]
        exact _root_.GlobalTheory.QFam.SzSum.sz_mul
          (_root_.GlobalTheory.DiffSize.sz_invDiff l lam F _ i (hdual α hα)) (h𝔟 β hβ i)
      · intro y z hy hz
        show _root_.GlobalTheory.LatVal.Sz l lam _ _
        rw [mul_add, map_add, Complex.ofReal_add]
        exact ((_root_.GlobalTheory.QFam.SzSum.sz_ring l lam).2.1 _ _ _ hy hz).1
    exact hmul
  have hl0 : l ≠ 0 := (Fact.out : l.Prime).ne_zero
  have hMl : M * l ^ b ≠ 0 := Nat.mul_ne_zero (by rintro rfl; exact hM (dvd_zero l)) (pow_ne_zero _ hl0)
  have hq : _root_.GlobalTheory.LatVal.Sz l lam b (((1 / (M * l ^ b : ℕ) : ℚ)) : ℂ) := by
    refine (_root_.GlobalTheory.SizeRat.sz_rat_exp l lam).1 _ _ ?_
    rw [one_div, padicValRat.inv, padicValRat.of_nat, padicValNat.mul
      (by rintro rfl; exact hM (dvd_zero l)) (pow_ne_zero _ hl0), padicValNat.prime_pow,
      padicValNat.eq_zero_of_not_dvd hM]
    simp
  have heq : ((i ξ : ℝ) : ℂ) = (((1 / (M * l ^ b : ℕ) : ℚ)) : ℂ) * ((i (t * ξ) : ℝ) : ℂ) := by
    have : ((M * l ^ b : ℕ) : ℂ) ≠ 0 := by exact_mod_cast hMl
    rw [ht_def, map_mul, map_natCast, Complex.ofReal_mul, Complex.ofReal_natCast, ← mul_assoc,
      one_div, Rat.cast_inv, Rat.cast_natCast, inv_mul_cancel₀ this, one_mul]
  rw [heq]
  have := _root_.GlobalTheory.QFam.SzSum.sz_mul hq key
  convert this using 1
  ring

open NumberField UpperHalfPlane FractionalIdeal in
open scoped nonZeroDivisors in
variable {l : ℕ} [Fact l.Prime] {lam : algebraicClosure ℚ ℂ →+* ℂ_[l]} in
private theorem sz_intCast_of_nonneg {r : ℝ} (hr : 0 ≤ r) (m : ℤ) :
    _root_.GlobalTheory.LatVal.Sz l lam r (m : ℂ) :=
  sz_mono_divisor hr ((_root_.GlobalTheory.QFam.SzSum.sz_ring l lam).2.2.2.2.1 m)

open NumberField UpperHalfPlane FractionalIdeal in
open scoped nonZeroDivisors in
variable {l : ℕ} [Fact l.Prime] {lam : algebraicClosure ℚ ℂ →+* ℂ_[l]} in
private theorem sz_zero' (r : ℝ) : _root_.GlobalTheory.LatVal.Sz l lam r 0 :=
  (_root_.GlobalTheory.QFam.SzSum.sz_ring l lam).1 r

open NumberField UpperHalfPlane FractionalIdeal in
open scoped nonZeroDivisors in
variable {l : ℕ} [Fact l.Prime] {lam : algebraicClosure ℚ ℂ →+* ℂ_[l]} in
private theorem sz_finsum {α : Type*} {r : ℝ} {f : α → ℂ}
    (hf : ∀ a, _root_.GlobalTheory.LatVal.Sz l lam r (f a)) :
    _root_.GlobalTheory.LatVal.Sz l lam r (∑ᶠ a, f a) := by
  by_cases h : (Function.support f).Finite
  · rw [finsum_eq_sum f h]
    exact _root_.GlobalTheory.QFam.SzSum.sz_sum _ fun a _ => hf a
  · rw [finsum_of_infinite_support h]
    exact sz_zero' r

open NumberField UpperHalfPlane FractionalIdeal in
open scoped nonZeroDivisors in
private theorem sz_finset_prod {l : ℕ} [Fact l.Prime] {lam : algebraicClosure ℚ ℂ →+* ℂ_[l]}
    {ι : Type*} [DecidableEq ι] (t : Finset ι) {w : ι → ℝ} {f : ι → ℂ}
    (hf : ∀ i ∈ t, _root_.GlobalTheory.LatVal.Sz l lam (w i) (f i)) :
    _root_.GlobalTheory.LatVal.Sz l lam (∑ i ∈ t, w i) (∏ i ∈ t, f i) := by
  induction t using Finset.induction_on with
  | empty => simpa using sz_intCast_of_nonneg (lam := lam) (le_refl (0 : ℝ)) 1
  | insert j t hj ih =>
    rw [Finset.prod_insert hj, Finset.sum_insert hj]
    exact _root_.GlobalTheory.QFam.SzSum.sz_mul (hf j (Finset.mem_insert_self j t))
      (ih fun i hi => hf i (Finset.mem_insert_of_mem hi))

open NumberField UpperHalfPlane FractionalIdeal in
open scoped nonZeroDivisors in
private theorem sz_pow' {l : ℕ} [Fact l.Prime] {lam : algebraicClosure ℚ ℂ →+* ℂ_[l]}
    {r : ℝ} {x : ℂ} (hx : _root_.GlobalTheory.LatVal.Sz l lam r x) (m : ℕ) :
    _root_.GlobalTheory.LatVal.Sz l lam (m * r) (x ^ m) := by
  induction m with
  | zero => simpa using sz_intCast_of_nonneg (lam := lam) (le_refl (0 : ℝ)) 1
  | succ m ih =>
    rw [pow_succ]
    convert _root_.GlobalTheory.QFam.SzSum.sz_mul ih hx using 1
    push_cast
    ring

open NumberField UpperHalfPlane FractionalIdeal in
open scoped nonZeroDivisors in
private theorem absNorm_mul_norm_mul_discr_eq_natCast_of_mem_dual {F : Type} [Field F] [NumberField F] (𝔞 : FractionalIdeal (𝓞 F)⁰ F) (h0 : 𝔞 ≠ 0) (t : F) (ht0 : t ≠ 0)
    (ht : t ∈ dual ℤ ℚ 𝔞) : ∃ n : ℕ, n ≠ 0 ∧
      absNorm 𝔞 * |Algebra.norm ℚ t| * |(discr F : ℚ)| = n := by
  have hd : (↑(differentIdeal ℤ (𝓞 F)) : FractionalIdeal (𝓞 F)⁰ F) = (dual ℤ ℚ 1)⁻¹ :=
    coeIdeal_differentIdeal ℤ ℚ F (𝓞 F)
  have hd0 : dual ℤ ℚ (1 : FractionalIdeal (𝓞 F)⁰ F) ≠ 0 := dual_ne_zero ℤ ℚ one_ne_zero
  have hle : spanSingleton (𝓞 F)⁰ t * 𝔞 * ↑(differentIdeal ℤ (𝓞 F)) ≤ 1 := by
    rw [hd]
    calc spanSingleton (𝓞 F)⁰ t * 𝔞 * (dual ℤ ℚ 1)⁻¹ ≤ dual ℤ ℚ 𝔞 * 𝔞 * (dual ℤ ℚ 1)⁻¹ := by
          gcongr
          exact spanSingleton_le_iff_mem.mpr ht
      _ = 1 := by rw [dual_mul_self ℤ ℚ h0, mul_inv_cancel₀ hd0]
  obtain ⟨I, hI⟩ := le_one_iff_exists_coeIdeal.mp hle
  refine ⟨Ideal.absNorm I, ?_, ?_⟩
  · rw [Ne, Ideal.absNorm_eq_zero_iff]
    rintro rfl
    rw [coeIdeal_bot] at hI
    have := hI.symm
    simp [mul_eq_zero, spanSingleton_eq_zero_iff, ht0, h0] at this
    exact (differentIdeal_ne_bot (A := ℤ) (B := 𝓞 F)) this
  · have := congrArg absNorm hI
    rw [coeIdeal_absNorm (R := 𝓞 F) (K := F) I, map_mul, map_mul, absNorm_span_singleton (𝓞 F),
      coeIdeal_absNorm (R := 𝓞 F) (K := F), absNorm_differentIdeal F (𝓞 F)] at this
    rw [this, Nat.cast_natAbs, Int.cast_abs]
    ring

open NumberField UpperHalfPlane FractionalIdeal in
open scoped nonZeroDivisors in
private theorem neg_padicValRat_le_of_mul_eq_natCast {l : ℕ} [hl : Fact l.Prime] {M b d : ℕ} {D : ℤ} {A : ℚ} {n : ℕ} (hn : n ≠ 0)
    (hM : ¬ l ∣ M) (hD : D ≠ 0) (h : A * |(((M * l ^ b : ℕ) : ℚ) ^ d)| * |(D : ℚ)| = n) :
    -(padicValRat l A) ≤ d * b + padicValInt l D := by
  have hM0 : M ≠ 0 := by rintro rfl; exact hM (dvd_zero l)
  have hl0 : l ≠ 0 := hl.out.ne_zero
  have hMl : M * l ^ b ≠ 0 := Nat.mul_ne_zero hM0 (pow_ne_zero _ hl0)
  have hDn : D.natAbs ≠ 0 := Int.natAbs_ne_zero.mpr hD
  have hprod : (M * l ^ b) ^ d * D.natAbs ≠ 0 := Nat.mul_ne_zero (pow_ne_zero _ hMl) hDn
  have hpos : |(((M * l ^ b : ℕ) : ℚ) ^ d)| * |(D : ℚ)| ≠ 0 := by
    have : ((M * l ^ b : ℕ) : ℚ) ≠ 0 := by exact_mod_cast hMl
    have : (D : ℚ) ≠ 0 := by exact_mod_cast hD
    positivity
  have hA : A = n / (|(((M * l ^ b : ℕ) : ℚ) ^ d)| * |(D : ℚ)|) := by
    rw [eq_div_iff hpos, ← h]; ring
  have hAbs1 : |(((M * l ^ b : ℕ) : ℚ) ^ d)| = (((M * l ^ b : ℕ) ^ d : ℕ) : ℚ) := by
    rw [abs_of_nonneg (by positivity)]; push_cast; ring
  have hAbs2 : |(D : ℚ)| = ((D.natAbs : ℕ) : ℚ) := by
    rw [Nat.cast_natAbs, Int.cast_abs]
  have hn' : (n : ℚ) ≠ 0 := by exact_mod_cast hn
  have hprod' : (((M * l ^ b) ^ d * D.natAbs : ℕ) : ℚ) ≠ 0 := by exact_mod_cast hprod
  rw [hA, hAbs1, hAbs2, ← Nat.cast_mul, padicValRat.div hn' hprod',
    padicValRat.of_nat, padicValRat.of_nat, padicValNat.mul (pow_ne_zero _ hMl) hDn,
    padicValNat.pow, padicValNat.mul hM0 (pow_ne_zero _ hl0), padicValNat.prime_pow,
    padicValNat.eq_zero_of_not_dvd hM]
  simp only [padicValInt]
  push_cast
  have h0 : (0 : ℤ) ≤ padicValRat l n := by rw [padicValRat.of_nat]; positivity
  linarith

open NumberField UpperHalfPlane FractionalIdeal in
open scoped nonZeroDivisors in
variable {l : ℕ} [Fact l.Prime] {lam : algebraicClosure ℚ ℂ →+* ℂ_[l]} in
private theorem sz_coeff_mul {r s : ℝ} {φ ψ : PowerSeries ℂ}
    (hφ : ∀ n, _root_.GlobalTheory.LatVal.Sz l lam r (PowerSeries.coeff n φ))
    (hψ : ∀ n, _root_.GlobalTheory.LatVal.Sz l lam s (PowerSeries.coeff n ψ)) (n : ℕ) :
    _root_.GlobalTheory.LatVal.Sz l lam (r + s) (PowerSeries.coeff n (φ * ψ)) := by
  rw [PowerSeries.coeff_mul]
  exact _root_.GlobalTheory.QFam.SzSum.sz_sum _ fun p _ =>
    _root_.GlobalTheory.QFam.SzSum.sz_mul (hφ p.1) (hψ p.2)

open NumberField UpperHalfPlane FractionalIdeal in
open scoped nonZeroDivisors in
variable {l : ℕ} [Fact l.Prime] {lam : algebraicClosure ℚ ℂ →+* ℂ_[l]} in
private theorem sz_coeff_pow {r : ℝ} {φ : PowerSeries ℂ}
    (hφ : ∀ n, _root_.GlobalTheory.LatVal.Sz l lam r (PowerSeries.coeff n φ)) (m : ℕ)
    (n : ℕ) : _root_.GlobalTheory.LatVal.Sz l lam (m * r) (PowerSeries.coeff n (φ ^ m)) := by
  induction m generalizing n with
  | zero =>
    rw [pow_zero, PowerSeries.coeff_one]
    split_ifs
    · simpa using sz_intCast_of_nonneg (lam := lam) (le_refl (0 : ℝ)) 1
    · simpa using sz_zero' (lam := lam) 0
  | succ m ih =>
    rw [pow_succ]
    have := sz_coeff_mul ih hφ n
    convert this using 1
    push_cast
    ring

open NumberField UpperHalfPlane FractionalIdeal in
open scoped nonZeroDivisors in
open scoped Classical MatrixGroups in

theorem _root_.GlobalTheory.HilbFam.sz_hfun_coef : _root_.GlobalTheory.LatJet.EisExp →
    ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F], 2 ≤ Module.finrank ℚ F →
    ∀ (s N : ℕ) (L : _root_.GlobalTheory.HilbFam.Lat F), 1 ≤ s → 0 < N → _root_.GlobalTheory.HilbFam.HasLevel N L →
    ∀ [IsGalois ℚ F] (z : ClassGroup (𝓞 F) → ℚ), _root_.GlobalTheory.HilbFam.ZetaVals (2 * s) z →
    ∀ (l : ℕ) [Fact l.Prime] (lam : algebraicClosure ℚ ℂ →+* ℂ_[l]) (κ : _root_.GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.Emb F → ℕ)
      (Ch : ℍ → ℂ) (M b : ℕ) (e ρ₀ ρ : ℝ), 0 ≤ e →
    (∀ C, -(padicValRat l (z C / 2 ^ Module.finrank ℚ F) : ℝ) ≤ e) → ¬ l ∣ M →
    ![0, ((M * l ^ b : ℕ) : F)] ∈ L →
    (∀ v ∈ L, ∀ i : _root_.GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.Emb F,
      _root_.GlobalTheory.LatVal.Sz l lam ρ₀ ((i (v 0) : ℝ) : ℂ)) →
    b + (padicValInt l (discr F) : ℝ) / Module.finrank ℚ F + ρ₀ ≤ ρ →
    _root_.GlobalTheory.QFam.QAll (_root_.GlobalTheory.LatVal.Sz l lam ρ) N Ch →
    _root_.GlobalTheory.QFam.QAll (_root_.GlobalTheory.LatVal.Sz l lam
      (e + s * (padicValInt l (discr F) : ℝ) + 2 * s * b * Module.finrank ℚ F +
        (∑ i, κ i : ℕ) * ρ)) N (_root_.GlobalTheory.HilbFam.hfun (2 * s) L κ Ch) := by
  intro hExp F _ _ _ hd s N L hs hN hL _ z hz l _ lam κ Ch M b e ρ₀ ρ he heC hM hML hρ₀ hρ hCh
  obtain ⟨𝔞, 𝔟, x, rfl⟩ := _root_.GlobalTheory.HilbFam.exists_eq_split_of_hasLevel F N L hN hL
  obtain ⟨Z, a, hZ, ha⟩ := _root_.GlobalTheory.HilbFam.exists_isCoef hExp F hd 𝔞 𝔟 s hs
  obtain ⟨c, hc, hcρ⟩ := hCh
  refine ⟨_, _root_.GlobalTheory.HilbFam.ExpH.hasQ_hfun F (2 * s) 𝔞 𝔟 _ a x N κ Ch c hN
    (even_two_mul s) ha hL hc, fun n => ?_⟩
  have hl0 : l ≠ 0 := (Fact.out : l.Prime).ne_zero
  set d := Module.finrank ℚ F with hd_def
  set t : F := ((M * l ^ b : ℕ) : F) with ht_def

  have ht : t ∈ _root_.GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.latM 𝔞 := by
    have := hML
    simp only [_root_.GlobalTheory.HilbFam.split] at this
    change (![0, t] : Fin 2 → F) 0 ∈ _ ∧ (![0, t] : Fin 2 → F) 1 - (![0, t] : Fin 2 → F) 0 * x ∈ _ at this
    simpa using this.2
  have ht0 : t ≠ 0 := by
    rw [ht_def]; exact_mod_cast Nat.mul_ne_zero (by rintro rfl; exact hM (dvd_zero l)) (pow_ne_zero _ hl0)

  have h𝔟 : ∀ β ∈ ((𝔟 : (FractionalIdeal (𝓞 F)⁰ F)ˣ) : FractionalIdeal (𝓞 F)⁰ F),
      ∀ i : _root_.GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.Emb F, _root_.GlobalTheory.LatVal.Sz l lam ρ₀ ((i β : ℝ) : ℂ) := by
    intro β hβ i
    have hv : (![β, β * x] : Fin 2 → F) ∈ _root_.GlobalTheory.HilbFam.split 𝔞 𝔟 x := by
      simp only [_root_.GlobalTheory.HilbFam.split]
      change (![β, β * x] : Fin 2 → F) 0 ∈ _ ∧
        (![β, β * x] : Fin 2 → F) 1 - (![β, β * x] : Fin 2 → F) 0 * x ∈ _
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, sub_self]
      exact ⟨hβ, zero_mem _⟩
    simpa using hρ₀ _ hv i

  have hξ : ∀ ξ, a ξ ≠ 0 → ∀ i : _root_.GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.Emb F,
      _root_.GlobalTheory.LatVal.Sz l lam ρ ((i ξ : ℝ) : ℂ) := by
    intro ξ hξ i
    have hmem : ξ ∈ (((𝔞 * 𝔟 : _root_.GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.Frac F) : (FractionalIdeal (𝓞 F)⁰ F)ˣ) :
        FractionalIdeal (𝓞 F)⁰ F) := by
      by_cases h0 : ξ = 0
      · rw [h0]; exact zero_mem _
      · exact (ha.2.2.1 ξ h0 hξ).1
    exact sz_mono_divisor hρ (valBound_embedding_mem_mul_lemma_2 hM ht h𝔟 hmem i)

  have haξ : ∀ ξ, _root_.GlobalTheory.LatVal.Sz l lam e (a ξ) := by
    intro ξ
    by_cases h0 : ξ = 0
    · rw [h0, ha.1, _root_.GlobalTheory.HilbFam.constTerm_eq_zetaVal F (2 * s) z _ Z (by omega) hz hZ]
      exact (_root_.GlobalTheory.SizeRat.sz_rat_exp l lam).1 _ _ (heC _)
    · obtain ⟨m, hm⟩ := ha.2.1 ξ h0
      rw [hm]
      exact_mod_cast sz_intCast_of_nonneg (lam := lam) he m

  have hT : ∀ μ : _root_.GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.Emb F → ℕ, ∀ m,
      _root_.GlobalTheory.LatVal.Sz l lam (e + ∑ i, (μ i : ℝ) * ρ)
        (_root_.GlobalTheory.HilbFam.ecoef N a x μ m) := by
    intro μ m
    unfold _root_.GlobalTheory.HilbFam.ecoef
    refine sz_finsum fun ξ => ?_
    rw [finsum_eq_if]
    split_ifs
    · by_cases h0 : a ξ = 0
      · rw [h0, zero_mul, zero_mul]; exact sz_zero' _
      · have hexp : _root_.GlobalTheory.LatVal.Sz l lam 0 (_root_.GlobalTheory.HilbFam.eTr (ξ * x)) := by
          unfold _root_.GlobalTheory.HilbFam.eTr
          exact (_root_.GlobalTheory.SizeRat.sz_rat_exp l lam).2 _
        have hprod := sz_finset_prod (lam := lam) Finset.univ (w := fun i => (μ i : ℝ) * ρ)
          (f := fun i => ((i ξ : ℝ) : ℂ) ^ μ i) fun i _ => sz_pow' (hξ ξ h0 i) (μ i)
        have := _root_.GlobalTheory.QFam.SzSum.sz_mul
          (_root_.GlobalTheory.QFam.SzSum.sz_mul (haξ ξ) hexp) hprod
        simpa using this
    · exact sz_zero' _

  have hω : _root_.GlobalTheory.LatVal.Sz l lam
      (s * (padicValInt l (discr F) : ℝ) + 2 * s * b * d)
      ((_root_.GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.omegaFactor 𝔞 : ℂ) ^ (2 * s)) := by
    rw [_root_.GlobalTheory.HilbFam.omegaFactor_pow_two_mul]
    refine (_root_.GlobalTheory.SizeRat.sz_rat_exp l lam).1 _ _ ?_
    have h𝔞0 : ((𝔞 : (FractionalIdeal (𝓞 F)⁰ F)ˣ) : FractionalIdeal (𝓞 F)⁰ F) ≠ 0 := Units.ne_zero _
    have htd : t ∈ FractionalIdeal.dual ℤ ℚ ((𝔞 : (FractionalIdeal (𝓞 F)⁰ F)ˣ) :
        FractionalIdeal (𝓞 F)⁰ F) := by
      rw [← _root_.GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.latM_eq_dual]; exact ht
    obtain ⟨k, hk0, hk⟩ := absNorm_mul_norm_mul_discr_eq_natCast_of_mem_dual _ h𝔞0 t ht0 htd
    rw [ht_def, ← map_natCast (algebraMap ℚ F), Algebra.norm_algebraMap] at hk
    have hD : discr F ≠ 0 := discr_ne_zero F
    have hv := neg_padicValRat_le_of_mul_eq_natCast hk0 hM hD hk
    have hA0 : FractionalIdeal.absNorm ((𝔞 : (FractionalIdeal (𝓞 F)⁰ F)ˣ) :
        FractionalIdeal (𝓞 F)⁰ F) ≠ 0 := by
      intro h0; rw [h0, zero_mul, zero_mul] at hk; exact hk0 (by exact_mod_cast hk.symm)
    have hD' : |(discr F : ℚ)| ≠ 0 := by simp [hD]
    rw [padicValRat.mul (pow_ne_zero _ hD') (pow_ne_zero _ hA0), padicValRat.pow, padicValRat.pow]
    have habs : padicValRat l |(discr F : ℚ)| = padicValInt l (discr F) := by
      rw [← Int.cast_abs, padicValRat.of_int]
      simp only [padicValInt, Int.natAbs_abs]
    rw [habs]
    have hv' : -(padicValRat l (FractionalIdeal.absNorm ((𝔞 : (FractionalIdeal (𝓞 F)⁰ F)ˣ) :
        FractionalIdeal (𝓞 F)⁰ F)) : ℝ) ≤ d * b + padicValInt l (discr F) := by
      exact_mod_cast hv
    push_cast
    nlinarith

  unfold _root_.GlobalTheory.HilbFam.hser
  rw [PowerSeries.coeff_smul, map_sum]
  simp only [PowerSeries.coeff_smul, smul_eq_mul, zsmul_eq_mul]
  have hsum : _root_.GlobalTheory.LatVal.Sz l lam (e + (∑ i, κ i : ℕ) * ρ)
      (∑ μ ∈ Finset.Iic κ, ((∏ i, _root_.GlobalTheory.HilbFam.rco (2 * s) (κ i) (μ i) *
        (-1) ^ μ i : ℤ) : ℂ) * PowerSeries.coeff n ((PowerSeries.mk c ^ ∑ i, (κ i - μ i)) *
          PowerSeries.mk (_root_.GlobalTheory.HilbFam.ecoef N a x μ))) := by
    refine _root_.GlobalTheory.QFam.SzSum.sz_sum _ fun μ hμ => ?_
    rw [Finset.mem_Iic] at hμ
    have hC := sz_coeff_pow (lam := lam) (φ := PowerSeries.mk c)
      (fun m => by rw [PowerSeries.coeff_mk]; exact hcρ m) (∑ i, (κ i - μ i))
    have hP := sz_coeff_mul hC (ψ := PowerSeries.mk (_root_.GlobalTheory.HilbFam.ecoef N a x μ))
      (fun m => by rw [PowerSeries.coeff_mk]; exact hT μ m) n
    have := _root_.GlobalTheory.QFam.SzSum.sz_mul (sz_intCast_of_nonneg (lam := lam) le_rfl
      (∏ i, _root_.GlobalTheory.HilbFam.rco (2 * s) (κ i) (μ i) * (-1) ^ μ i)) hP
    convert this using 1
    have hnat : ∑ i, (κ i - μ i) + ∑ i, μ i = ∑ i, κ i := by
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun i _ => Nat.sub_add_cancel (hμ i)
    rw [← hnat, ← Finset.sum_mul]
    push_cast
    ring
  have := _root_.GlobalTheory.QFam.SzSum.sz_mul hω hsum
  convert this using 1
  ring
