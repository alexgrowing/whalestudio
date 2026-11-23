import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DiagMod
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.NatDegreeMinpolyLe
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsFinsetSpanPrincipalCongruenceLevelFunction
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.MemClosureOfFixed
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsNumberFieldExpansionCoeffs
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.JTranslatesLevelAndScalarModStatement

open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ GlobalTheory.KZ.ES

noncomputable section

namespace GlobalTheory.KZ.ES.Quot

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ}

open scoped MatrixGroups TensorProduct in
open Matrix in
variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ} in
private lemma hahnSeries_coeff_algebraMap_mul (c : Ω) (x : HahnSeries ℚ Ω) (r : ℚ) :
    (algebraMap Ω (HahnSeries ℚ Ω) c * x).coeff r = c * x.coeff r := by
  rw [HahnSeries.algebraMap_apply', PowerSeries.algebraMap_apply, Algebra.algebraMap_self,
    RingHom.id_apply, HahnSeries.ofPowerSeries_C, HahnSeries.C_mul_eq_smul, HahnSeries.coeff_smul,
    smul_eq_mul]

open scoped MatrixGroups TensorProduct in
open Matrix in
variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ} in
theorem _root_.GlobalTheory.KZ.ES.Quot.intC_const_mul {X : _root_.GlobalTheory.KZ.Tower Ω ε}
    {V : ValuationSubring Ω} {c : Ω} (hc : c ∈ V) {f : X.K}
    (hf : _root_.GlobalTheory.KZ.ES.IntC X V f) :
    _root_.GlobalTheory.KZ.ES.IntC X V (algebraMap Ω X.K c * f) := by
  intro r
  rw [map_mul, AlgHom.commutes, hahnSeries_coeff_algebraMap_mul]
  exact V.mul_mem _ _ hc (hf r)

open scoped MatrixGroups TensorProduct in
open Matrix in
variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ} in
theorem _root_.GlobalTheory.KZ.ES.Quot.intC_add {X : _root_.GlobalTheory.KZ.Tower Ω ε}
    {V : ValuationSubring Ω} {f g : X.K}
    (hf : _root_.GlobalTheory.KZ.ES.IntC X V f) (hg : _root_.GlobalTheory.KZ.ES.IntC X V g) :
    _root_.GlobalTheory.KZ.ES.IntC X V (f + g) := by
  intro r
  rw [map_add, HahnSeries.coeff_add]
  exact V.add_mem _ _ (hf r) (hg r)

open scoped MatrixGroups TensorProduct in
open Matrix in
variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ} in
theorem _root_.GlobalTheory.KZ.ES.Quot.intC_mul {X : _root_.GlobalTheory.KZ.Tower Ω ε}
    {V : ValuationSubring Ω} {f g : X.K}
    (hf : _root_.GlobalTheory.KZ.ES.IntC X V f) (hg : _root_.GlobalTheory.KZ.ES.IntC X V g) :
    _root_.GlobalTheory.KZ.ES.IntC X V (f * g) := by
  intro r
  rw [map_mul, HahnSeries.coeff_mul]
  exact V.toSubring.sum_mem fun ij _ => V.mul_mem _ _ (hf _) (hg _)

open scoped MatrixGroups TensorProduct in
open Matrix in
variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ} in
theorem _root_.GlobalTheory.KZ.ES.Quot.intC_one {X : _root_.GlobalTheory.KZ.Tower Ω ε}
    {V : ValuationSubring Ω} : _root_.GlobalTheory.KZ.ES.IntC X V 1 := by
  intro r
  rw [map_one, HahnSeries.coeff_one]
  split_ifs
  · exact V.one_mem
  · exact V.zero_mem

def bddRing (X : Tower Ω ε) (V : ValuationSubring Ω) (M : ℕ) : Subalgebra Ω X.K where
  carrier := {x | Lev X M x ∧ ∃ c : Ω, c ≠ 0 ∧ IntC X V (algebraMap Ω X.K c * x)}
  mul_mem' := by
    rintro a b ⟨ha, c, hc, hca⟩ ⟨hb, d, hd, hdb⟩
    refine ⟨fun γ hγ => by rw [map_mul, ha γ hγ, hb γ hγ], c * d, mul_ne_zero hc hd, ?_⟩
    have := intC_mul hca hdb
    rwa [mul_mul_mul_comm, ← map_mul] at this
  add_mem' := by
    rintro a b ⟨ha, c, hc, hca⟩ ⟨hb, d, hd, hdb⟩
    refine ⟨fun γ hγ => by rw [map_add, ha γ hγ, hb γ hγ], ?_⟩
    rcases V.mem_or_inv_mem (c / d) with h | h
    · refine ⟨c, hc, ?_⟩
      have := intC_add hca (intC_const_mul h hdb)
      rwa [← mul_assoc, ← map_mul, div_mul_cancel₀ _ hd, ← mul_add] at this
    · refine ⟨d, hd, ?_⟩
      have := intC_add (intC_const_mul h hca) hdb
      rwa [← mul_assoc, ← map_mul, inv_div, div_mul_cancel₀ _ hc, ← mul_add] at this
  algebraMap_mem' := fun c => by
    refine ⟨fun γ _ => by rw [AlgEquiv.commutes], ?_⟩
    by_cases hc : c = 0
    · refine ⟨1, one_ne_zero, fun r => ?_⟩
      simp [hc, V.zero_mem]
    · refine ⟨c⁻¹, inv_ne_zero hc, ?_⟩
      rw [← map_mul, inv_mul_cancel₀ hc, map_one]
      exact intC_one

def rho (X : Tower Ω ε) (H : Subgroup SL(2, ℤ)) : H →* RingAut X.K where
  toFun g := (X.sl (ofSL (g : SL(2, ℤ))⁻¹)).toRingEquiv
  map_one' := by
    ext f
    simp [X.sl_one]
  map_mul' g h := by
    ext f
    show X.sl (ofSL ((g * h : H) : SL(2, ℤ))⁻¹) f = X.sl (ofSL (g : SL(2, ℤ))⁻¹) (X.sl (ofSL (h : SL(2, ℤ))⁻¹) f)
    rw [← X.sl_mul, ← map_mul, Subgroup.coe_mul, _root_.mul_inv_rev]

open scoped MatrixGroups TensorProduct in
open Matrix in
variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] {ε : Ω →+* ℂ} in
private lemma gamma_le_gamma_of_dvd' {n m : ℕ} (h : n ∣ m) :
    CongruenceSubgroup.Gamma m ≤ CongruenceSubgroup.Gamma n := by
  intro γ hγ
  rw [CongruenceSubgroup.Gamma_mem] at hγ ⊢
  have hcast : ∀ a : ℤ, (ZMod.castHom h (ZMod n)) (a : ZMod m) = (a : ZMod n) :=
    fun a => map_intCast _ a
  obtain ⟨h1, h2, h3, h4⟩ := hγ
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← hcast, h1, map_one]
  · rw [← hcast, h2, map_zero]
  · rw [← hcast, h3, map_zero]
  · rw [← hcast, h4, map_one]

open scoped MatrixGroups TensorProduct in
open Matrix in
variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] {ε : Ω →+* ℂ} in
private lemma mem_valuationSubring_of_isIntegral_natCast_pow_mul {V : ValuationSubring Ω} {q : ℕ} (hq : q.Prime)
    (hqV : ((q : ℕ) : Ω) ∈ V.nonunits) {D : ℕ} (hqD : ¬ q ∣ D) {y : Ω} {e : ℕ}
    (hy : IsIntegral ℤ ((D : Ω) ^ e * y)) : y ∈ V := by
  have hint : ∀ z : Ω, IsIntegral ℤ z → z ∈ V := fun z hz => by
    obtain ⟨w, hw⟩ := IsIntegrallyClosed.isIntegral_iff.1 (hz.tower_top : IsIntegral V z)
    rw [← hw]
    exact w.2
  have hD1 : V.valuation (D : Ω) = 1 := by
    refine le_antisymm ((V.valuation_le_one_iff _).2 (natCast_mem V D)) (not_lt.1 fun hlt => ?_)
    have hg := Nat.gcd_eq_gcd_ab q D
    rw [((Nat.Prime.coprime_iff_not_dvd hq).2 hqD : Nat.gcd q D = 1)] at hg
    have huw : ((q.gcdA D : ℤ) : Ω) * (q : Ω) + ((q.gcdB D : ℤ) : Ω) * (D : Ω) = 1 := by
      have : (q.gcdA D) * (q : ℤ) + q.gcdB D * (D : ℤ) = 1 := by push_cast at hg; linarith
      have h' := congrArg (Int.cast : ℤ → Ω) this
      push_cast at h'
      exact h'
    have hqlt : V.valuation ((q : ℕ) : Ω) < 1 := (V.mem_nonunits_iff).1 hqV
    have hlt1 : V.valuation (((q.gcdA D : ℤ) : Ω) * (q : Ω) + ((q.gcdB D : ℤ) : Ω) * (D : Ω)) < 1 := by
      refine Valuation.map_add_lt _ ?_ ?_
      · rw [map_mul]
        exact lt_of_le_of_lt (mul_le_of_le_one_left' ((V.valuation_le_one_iff _).2
          (intCast_mem V _))) hqlt
      · rw [map_mul]
        exact lt_of_le_of_lt (mul_le_of_le_one_left' ((V.valuation_le_one_iff _).2
          (intCast_mem V _))) hlt
    rw [huw, map_one] at hlt1
    exact lt_irrefl _ hlt1
  rw [← V.valuation_le_one_iff]
  have h := (V.valuation_le_one_iff _).2 (hint _ hy)
  rwa [map_mul, map_pow, hD1, one_pow, one_mul] at h

open scoped MatrixGroups TensorProduct in
open Matrix in
variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] {ε : Ω →+* ℂ} in
private lemma eOm_mem_valuationSubring (ε : Ω →+* ℂ) (V : ValuationSubring Ω) (s : ℚ) :
    _root_.GlobalTheory.KZ.eOm ε s ∈ V := by
  haveI := IsAlgClosure.isAlgClosed ℚ (K := Ω)
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap ℚ Ω).injective
  set n := s.den with hn
  haveI : NeZero n := ⟨s.den_nz⟩
  set w : ℂ := Complex.exp (2 * Real.pi * Complex.I * s) with hw
  have hwn : w ^ n = 1 := by
    rw [hw, ← Complex.exp_nat_mul]
    have e : (n : ℂ) * (2 * Real.pi * Complex.I * s) = (s.num : ℂ) * (2 * Real.pi * Complex.I) := by
      have hs : (s : ℂ) * n = s.num := by exact_mod_cast Rat.mul_den_eq_num s
      rw [← hs]
      ring
    rw [e, Complex.exp_int_mul_two_pi_mul_I]
  obtain ⟨ζ, hζ⟩ := IsAlgClosed.exists_root (Polynomial.cyclotomic n Ω)
    (Polynomial.degree_cyclotomic_pos n Ω (NeZero.pos n)).ne'
  haveI : NeZero (n : Ω) := ⟨Nat.cast_ne_zero.2 (NeZero.ne n)⟩
  have hζ' : IsPrimitiveRoot ζ n := Polynomial.isRoot_cyclotomic_iff.1 hζ
  obtain ⟨i, -, hi⟩ := (hζ'.map_of_injective ε.injective).eq_pow_of_pow_eq_one hwn
  have hrange : ∃ z, ε z = w := ⟨ζ ^ i, by rw [map_pow, hi]⟩
  have hz : ε (_root_.GlobalTheory.KZ.eOm ε s) = w := Function.invFun_eq hrange
  have hzn : _root_.GlobalTheory.KZ.eOm ε s ^ n = 1 := by
    apply ε.injective
    rw [map_pow, hz, hwn, map_one]
  have hint : IsIntegral ℤ (_root_.GlobalTheory.KZ.eOm ε s) :=
    ⟨Polynomial.X ^ n - 1, Polynomial.monic_X_pow_sub_C 1 (NeZero.ne n), by simp [hzn]⟩
  obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.1 (hint.tower_top : IsIntegral V _)
  rw [← hy]
  exact y.2

open scoped MatrixGroups TensorProduct in
open Matrix in
variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] {ε : Ω →+* ℂ} in
private lemma two_mul_pow_dvd_of_sq_dvd_of_dvd_mul_add_two {P x : ℤ} (k : ℕ) (hP : P ≠ 0)
    (hx : (2 * P) ^ 2 ∣ x) (hxx : (2 * P) ^ (k + 2) ∣ x * (x + 2)) : 2 * P ^ (k + 2) ∣ x := by
  obtain ⟨y, rfl⟩ := hx
  have h2P : (2 * P) ^ 2 ≠ 0 := pow_ne_zero _ (mul_ne_zero two_ne_zero hP)
  have h1 : (2 * P) ^ k ∣ y * ((2 * P) ^ 2 * y + 2) := by
    rw [pow_add, mul_comm ((2 * P) ^ k), mul_assoc] at hxx
    exact (mul_dvd_mul_iff_left h2P).1 hxx
  have h2 : P ^ k ∣ (2 * y) * (2 * P ^ 2 * y + 1) := by
    have h := (pow_dvd_pow_of_dvd (dvd_mul_left P 2) k).trans h1
    have e : y * ((2 * P) ^ 2 * y + 2) = (2 * y) * (2 * P ^ 2 * y + 1) := by ring
    rwa [e] at h
  have hcop : IsCoprime (P ^ k) (2 * P ^ 2 * y + 1) :=
    IsCoprime.pow_left ⟨-(2 * P * y), 1, by ring⟩
  have h3 : P ^ k ∣ 2 * y := hcop.dvd_of_dvd_mul_right h2
  have e : (2 * P) ^ 2 * y = (2 * P ^ 2) * (2 * y) := by ring
  have e' : 2 * P ^ (k + 2) = (2 * P ^ 2) * P ^ k := by ring
  rw [e, e']
  exact mul_dvd_mul_left _ h3

open scoped MatrixGroups TensorProduct in
open Matrix in
variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] {ε : Ω →+* ℂ} in
private lemma mem_gamma_of_scalar_mod_two_mul_pow {M₀ l k : ℕ} (hM₀ : 0 < M₀) (hl : 0 < l) {γ : SL(2, ℤ)}
    (hγ : γ ∈ CongruenceSubgroup.Gamma ((2 * M₀ * l) ^ 2))
    (h01 : ((γ 0 1 : ℤ) : ZMod ((2 * M₀ * l) ^ (k + 2))) = 0)
    (h10 : ((γ 1 0 : ℤ) : ZMod ((2 * M₀ * l) ^ (k + 2))) = 0)
    (hdiag : ((γ 0 0 : ℤ) : ZMod ((2 * M₀ * l) ^ (k + 2))) = ((γ 1 1 : ℤ) : ZMod ((2 * M₀ * l) ^ (k + 2)))) :
    γ ∈ CongruenceSubgroup.Gamma (M₀ * l ^ k) := by
  rw [CongruenceSubgroup.Gamma_mem] at hγ ⊢
  obtain ⟨g00, -, -, g11⟩ := hγ
  replace g00 := (ZMod.intCast_eq_intCast_iff_dvd_sub (γ 0 0) 1 ((2 * M₀ * l) ^ 2)).1 (by rw [Int.cast_one]; exact g00)
  replace g11 := (ZMod.intCast_eq_intCast_iff_dvd_sub (γ 1 1) 1 ((2 * M₀ * l) ^ 2)).1 (by rw [Int.cast_one]; exact g11)
  rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at h01 h10
  rw [ZMod.intCast_eq_intCast_iff_dvd_sub] at hdiag
  have hM : ((M₀ * l ^ k : ℕ) : ℤ) ∣ (((2 * M₀ * l) ^ (k + 2) : ℕ) : ℤ) := by
    exact_mod_cast (show M₀ * l ^ k ∣ (2 * M₀ * l) ^ (k + 2) from
      ⟨2 ^ (k + 2) * M₀ ^ (k + 1) * l ^ 2, by ring⟩)
  have hdet : γ 0 0 * γ 1 1 - γ 0 1 * γ 1 0 = 1 := by
    have := γ.2
    rw [Matrix.det_fin_two] at this
    exact this
  set P : ℤ := (M₀ : ℤ) * l
  have hP : P ≠ 0 := mul_ne_zero (by exact_mod_cast hM₀.ne') (by exact_mod_cast hl.ne')
  have hcast : (((2 * M₀ * l) ^ (k + 2) : ℕ) : ℤ) = (2 * P) ^ (k + 2) := by push_cast; ring
  have hcast2 : (((2 * M₀ * l) ^ 2 : ℕ) : ℤ) = (2 * P) ^ 2 := by push_cast; ring
  rw [hcast] at h01 h10 hdiag hM
  rw [hcast2] at g00 g11
  have hx : (2 * P) ^ 2 ∣ γ 0 0 - 1 := dvd_sub_comm.1 g00
  have hxx : (2 * P) ^ (k + 2) ∣ (γ 0 0 - 1) * (γ 0 0 - 1 + 2) := by
    have e : (γ 0 0 - 1) * (γ 0 0 - 1 + 2) =
        γ 0 0 * (γ 1 1 - γ 0 0) * (-1) + γ 0 1 * γ 1 0 + 0 := by
      linear_combination hdet
    rw [e]
    exact dvd_add (dvd_add (dvd_mul_of_dvd_left (dvd_mul_of_dvd_right hdiag _) _)
      (dvd_mul_of_dvd_left h01 _)) (dvd_zero _)
  have ha : ((M₀ * l ^ k : ℕ) : ℤ) ∣ γ 0 0 - 1 := by
    refine dvd_trans ?_ (two_mul_pow_dvd_of_sq_dvd_of_dvd_mul_add_two k hP hx hxx)
    exact ⟨2 * M₀ ^ (k + 1) * l ^ 2, by push_cast [P]; ring⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · have h := (ZMod.intCast_eq_intCast_iff_dvd_sub (γ 0 0) 1 (M₀ * l ^ k)).2 (dvd_sub_comm.1 ha)
    rwa [Int.cast_one] at h
  · rw [ZMod.intCast_zmod_eq_zero_iff_dvd]
    exact hM.trans h01
  · rw [ZMod.intCast_zmod_eq_zero_iff_dvd]
    exact hM.trans h10
  · have e : γ 1 1 - 1 = (γ 0 0 - 1) + (γ 1 1 - γ 0 0) := by ring
    have h := (ZMod.intCast_eq_intCast_iff_dvd_sub (γ 1 1) 1 (M₀ * l ^ k)).2
      (dvd_sub_comm.1 (e ▸ dvd_add ha (hM.trans hdiag)))
    rwa [Int.cast_one] at h

open scoped MatrixGroups TensorProduct in
open Matrix in
variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] {ε : Ω →+* ℂ} in
private lemma exists_finset_lev_mem_closure_bddRing (X : _root_.GlobalTheory.KZ.Tower Ω ε)
    (hj : ∃ φ : ℂ → ℂ, DifferentiableOn ℂ φ _root_.GlobalTheory.KZ.Hs ∧
      X.an X.jK = (φ : _root_.GlobalTheory.KZ.Mero))
    {l M₀ : ℕ} (hl : l.Prime) (hM₀ : 0 < M₀) :
    ∃ S : Finset ℕ, ∀ q : ℕ, q.Prime → q ∉ S → ∀ V : ValuationSubring Ω,
      ((q : ℕ) : Ω) ∈ V.nonunits → ∀ (k : ℕ) (f : X.K),
      _root_.GlobalTheory.KZ.ES.Lev X (M₀ * l ^ k) f →
      f ∈ Subfield.closure
        (_root_.GlobalTheory.KZ.ES.Quot.bddRing X V ((2 * M₀ * l) ^ (k + 2)) : Set X.K) := by
  have hn : 0 < 2 * M₀ * l := Nat.mul_pos (Nat.mul_pos two_pos hM₀) hl.pos
  obtain ⟨T, hTlev, hTspan⟩ := _root_.GlobalTheory.KZ.ES.LevFin.exists_finset_span ε X hj
    ((2 * M₀ * l) ^ 2) (pow_pos hn 2)
  choose D hD hDint using fun t : X.K => X.bdd t
  refine ⟨(T.prod D).primeFactors, fun q hq hqS V hqV k f hf => ?_⟩
  set m := (2 * M₀ * l) ^ (k + 2) with hm
  have hm0 : 0 < m := pow_pos hn _
  set B := _root_.GlobalTheory.KZ.ES.Quot.bddRing X V m
  set L : IntermediateField Ω X.K := (Subfield.closure (B : Set X.K)).toIntermediateField
    fun c => Subfield.subset_closure (B.algebraMap_mem c)
  have hN₀m : (2 * M₀ * l) ^ 2 ∣ m := pow_dvd_pow _ (by omega)
  have hdvd : M₀ * l ^ k ∣ m := by
    rw [hm, pow_add, mul_comm ((2 * M₀ * l) ^ k)]
    exact mul_dvd_mul (dvd_pow ⟨2 * l, by ring⟩ two_ne_zero)
      (pow_dvd_pow_of_dvd (dvd_mul_left l _) k)
  have hT : ∀ t ∈ T, t ∈ B := by
    intro t ht
    refine ⟨fun γ hγ => hTlev t ht γ (gamma_le_gamma_of_dvd' hN₀m hγ), 1, one_ne_zero, fun r => ?_⟩
    rw [map_one, one_mul]
    obtain ⟨e, he⟩ := hDint t r
    have hqD : ¬ q ∣ D t := fun h => hqS (Nat.mem_primeFactors.2
      ⟨hq, h.trans (Finset.dvd_prod_of_mem D ht), (Finset.prod_pos fun i _ => hD i).ne'⟩)
    exact mem_valuationSubring_of_isIntegral_natCast_pow_mul hq hqV hqD he
  have hjB : X.jK ∈ B := by
    refine ⟨_root_.GlobalTheory.KZ.ES.lev_jK X m, 1, one_ne_zero, fun r => ?_⟩
    rw [map_one, one_mul]
    obtain ⟨z, hz⟩ := X.j_exp.2.2 r
    rw [hz]
    exact intCast_mem V z
  have hY : ∀ g ∈ ({!![(m : ℤ), 0; 0, 1], !![1, 0; 0, (m : ℤ)], !![1, 1; 0, (m : ℤ)]} :
      Set (Matrix (Fin 2) (Fin 2) ℤ)), X.sl (_root_.GlobalTheory.KZ.toGQ g) X.jK ∈ B := by
    intro g hg
    refine ⟨(_root_.GlobalTheory.KZ.ES.Scal.lev_and_scalar ε X m hm0).1 g hg, 1, one_ne_zero, fun r => ?_⟩
    rw [map_one, one_mul]
    have hm' : (m : ℤ) ≠ 0 := by exact_mod_cast hm0.ne'
    have hg' : 0 < g.det ∧ g 1 0 = 0 ∧ g 0 0 ≠ 0 ∧ g 1 1 ≠ 0 := by
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
      have hm'' : (0 : ℤ) < m := by exact_mod_cast hm0
      rcases hg with rfl | rfl | rfl <;> simp [Matrix.det_fin_two, hm', hm'', hm0, hm0.ne']
    obtain ⟨hd, h10, h00, h11⟩ := hg'
    have hE : ∀ i j, _root_.GlobalTheory.KZ.ent (_root_.GlobalTheory.KZ.toGQ g) i j = g i j := fun i j => by
      unfold _root_.GlobalTheory.KZ.ent _root_.GlobalTheory.KZ.toGQ
      rw [dif_pos hd]
      simp
    have h := X.exp_upper (_root_.GlobalTheory.KZ.toGQ g)
      (by rw [hE, h10]; simp) X.jK (r * g 1 1 / g 0 0)
    simp only [hE] at h
    have h00' : (g 0 0 : ℚ) ≠ 0 := by exact_mod_cast h00
    have h11' : (g 1 1 : ℚ) ≠ 0 := by exact_mod_cast h11
    have hr : r * (g 1 1 : ℚ) / (g 0 0) * (g 0 0) / (g 1 1) = r := by field_simp
    rw [hr] at h
    rw [h]
    obtain ⟨z, hz⟩ := X.j_exp.2.2 (r * g 1 1 / g 0 0)
    rw [hz]
    exact V.mul_mem _ _ (eOm_mem_valuationSubring ε V _) (intCast_mem V z)
  have hfix : ∀ x : X.K, _root_.GlobalTheory.KZ.ES.Lev X ((2 * M₀ * l) ^ 2) x →
      x ∈ Subfield.closure (B : Set X.K) := by
    intro x hx
    have hjL : IntermediateField.adjoin Ω {X.jK} ≤ L :=
      IntermediateField.adjoin_simple_le_iff.2 (Subfield.subset_closure hjB)
    have hspan := hTspan x hx
    clear hx
    induction hspan using Submodule.span_induction with
    | mem t ht => exact Subfield.subset_closure (hT t ht)
    | zero => exact zero_mem _
    | add y z _ _ hy hz => exact add_mem hy hz
    | smul r y _ hy =>
      show (r : X.K) * y ∈ Subfield.closure (B : Set X.K)
      exact mul_mem (hjL r.2) hy
  haveI : NeZero m := ⟨hm0.ne'⟩
  have hart := _root_.GlobalTheory.ArtinFix.mem_closure_of_fixed X.K (CongruenceSubgroup.Gamma ((2 * M₀ * l) ^ 2))
    (_root_.GlobalTheory.KZ.ES.Quot.rho X _) ((CongruenceSubgroup.Gamma m).subgroupOf _)
    ((CongruenceSubgroup.Gamma_normal m).subgroupOf _) inferInstance
    ((fun g => X.sl (_root_.GlobalTheory.KZ.toGQ g) X.jK) ''
      ({!![(m : ℤ), 0; 0, 1], !![1, 0; 0, (m : ℤ)], !![1, 1; 0, (m : ℤ)]} :
        Set (Matrix (Fin 2) (Fin 2) ℤ))) f ?_ ?_ ?_
  · refine Subfield.closure_le.2 (Set.union_subset (fun x hx => hfix x ?_) ?_) hart
    · intro γ hγ
      have h := hx ⟨γ⁻¹, inv_mem hγ⟩
      change X.sl (_root_.GlobalTheory.KZ.ofSL (γ⁻¹)⁻¹) x = x at h
      rwa [inv_inv] at h
    · rintro _ ⟨g, hg, rfl⟩
      exact Subfield.subset_closure (hY g hg)
  · rintro _ ⟨g, hg, rfl⟩ δ hδ
    change X.sl (_root_.GlobalTheory.KZ.ofSL (δ : SL(2, ℤ))⁻¹) _ = _
    exact (_root_.GlobalTheory.KZ.ES.Scal.lev_and_scalar ε X m hm0).1 g hg _
      (inv_mem (Subgroup.mem_subgroupOf.1 hδ))
  · intro δ hδ
    change X.sl (_root_.GlobalTheory.KZ.ofSL (δ : SL(2, ℤ))⁻¹) f = f
    exact hf _ (gamma_le_gamma_of_dvd' hdvd (inv_mem (Subgroup.mem_subgroupOf.1 hδ)))
  · rintro ⟨g, hg⟩ hgY
    change X.sl (_root_.GlobalTheory.KZ.ofSL g⁻¹) f = f
    obtain ⟨h01, h10, hdiag⟩ := (_root_.GlobalTheory.KZ.ES.Scal.lev_and_scalar ε X m hm0).2 g⁻¹
      fun g' hg' => hgY _ ⟨g', hg', rfl⟩
    exact hf _ (mem_gamma_of_scalar_mod_two_mul_pow hM₀ hl.pos (inv_mem hg) h01 h10 hdiag)

open scoped MatrixGroups TensorProduct in
open Matrix in
variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] {ε : Ω →+* ℂ} in
private lemma exists_prim_mul_of_mem_bddRing {X : _root_.GlobalTheory.KZ.Tower Ω ε}
    {q : ℕ} (hq : q.Prime) {V : ValuationSubring Ω} (hqV : ((q : ℕ) : Ω) ∈ V.nonunits) {M : ℕ}
    {x : X.K} (hx : x ∈ _root_.GlobalTheory.KZ.ES.Quot.bddRing X V M) (hx0 : x ≠ 0) :
    ∃ (α : Ω) (a : X.K), α ≠ 0 ∧ _root_.GlobalTheory.KZ.ES.Lev X M a ∧
      _root_.GlobalTheory.KZ.ES.Prim X V a ∧ x = algebraMap Ω X.K α * a := by
  obtain ⟨hlev, c, hc, hcx⟩ := hx
  haveI : Algebra.IsAlgebraic ℚ Ω := IsAlgClosure.isAlgebraic
  obtain ⟨F, hF, hcoef⟩ := _root_.GlobalTheory.KZ.ES.NF.coeff_numberField ε X x
  have hne : ∃ r, (X.exp x).coeff r ≠ 0 := by
    by_contra h
    push_neg at h
    apply hx0
    apply (X.exp : X.K →+* HahnSeries ℚ Ω).injective
    rw [map_zero]
    exact HahnSeries.ext (funext h)
  obtain ⟨r, hr0, hmax⟩ := _root_.GlobalTheory.ValMax.exists_max_valuation F hF q hq V hqV ℚ
    (fun r => (X.exp x).coeff r) c hc hcoef
    (fun r => by simpa [map_mul, AlgHom.commutes, hahnSeries_coeff_algebraMap_mul] using hcx r) hne
  have hval : 0 < V.valuation ((X.exp x).coeff r) :=
    zero_lt_iff.2 ((Valuation.ne_zero_iff _).2 hr0)
  refine ⟨(X.exp x).coeff r, algebraMap Ω X.K ((X.exp x).coeff r)⁻¹ * x, hr0,
    fun γ hγ => by rw [map_mul, AlgEquiv.commutes, hlev γ hγ], ⟨fun r' => ?_, r, ?_⟩, ?_⟩
  · rw [map_mul, AlgHom.commutes, hahnSeries_coeff_algebraMap_mul,
      ← ValuationSubring.valuation_le_one_iff, map_mul, map_inv₀]
    exact (inv_mul_le_one₀ hval).2 (hmax r')
  · rw [map_mul, AlgHom.commutes, hahnSeries_coeff_algebraMap_mul, inv_mul_cancel₀ hr0,
      map_one]
  · rw [← mul_assoc, ← map_mul, mul_inv_cancel₀ hr0, map_one, one_mul]

open scoped MatrixGroups TensorProduct in
open Matrix in
variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] {ε : Ω →+* ℂ} in

theorem _root_.GlobalTheory.KZ.ES.Quot.quot_prim : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (X : _root_.GlobalTheory.KZ.Tower Ω ε), (∃ φ : ℂ → ℂ, DifferentiableOn ℂ φ _root_.GlobalTheory.KZ.Hs ∧ X.an X.jK = (φ : _root_.GlobalTheory.KZ.Mero)) → ∀ (l M₀ : ℕ), l.Prime → 0 < M₀ → ∃ S : Finset ℕ, ∀ q : ℕ, q.Prime → q ∉ S → ∀ V : ValuationSubring Ω, ((q : ℕ) : Ω) ∈ V.nonunits → ∀ (k : ℕ) (f : X.K), f ≠ 0 → _root_.GlobalTheory.KZ.ES.Lev X (M₀ * l ^ k) f → ∃ (M' : ℕ) (a b : X.K) (c : Ω), 0 < M' ∧ Nat.Coprime q M' ∧ M₀ * l ^ k ∣ M' ∧ _root_.GlobalTheory.KZ.ES.Lev X M' a ∧ _root_.GlobalTheory.KZ.ES.Lev X M' b ∧ _root_.GlobalTheory.KZ.ES.Prim X V a ∧ _root_.GlobalTheory.KZ.ES.Prim X V b ∧ c ≠ 0 ∧ f * b = algebraMap Ω X.K c * a := by
  intro Ω _ _ _ ε X hj l M₀ hl hM₀
  obtain ⟨S, hS⟩ := exists_finset_lev_mem_closure_bddRing X hj hl hM₀
  refine ⟨S ∪ (2 * M₀ * l).primeFactors, fun q hq hqS V hqV k f hf0 hf => ?_⟩
  have hN : 0 < 2 * M₀ * l := Nat.mul_pos (Nat.mul_pos two_pos hM₀) hl.pos
  have hcop : Nat.Coprime q (2 * M₀ * l) := by
    refine (Nat.Prime.coprime_iff_not_dvd hq).2 fun hdvd => hqS ?_
    exact Finset.mem_union_right _ (Nat.mem_primeFactors.2 ⟨hq, hdvd, hN.ne'⟩)
  have hmem := hS q hq (fun h => hqS (Finset.mem_union_left _ h)) V hqV k f hf
  set B := _root_.GlobalTheory.KZ.ES.Quot.bddRing X V ((2 * M₀ * l) ^ (k + 2))
  obtain ⟨y, hy, z, hz, hyz⟩ := Subfield.mem_closure_iff.1 hmem
  have hB : Subring.closure (B : Set X.K) = B.toSubring := Subring.closure_eq B.toSubring
  rw [hB] at hy hz
  have hz0 : z ≠ 0 := by
    rintro rfl
    rw [div_zero] at hyz
    exact hf0 hyz.symm
  have hfz : f * z = y := by rw [← hyz, div_mul_cancel₀ _ hz0]
  have hy0 : y ≠ 0 := by
    rw [← hfz]
    exact mul_ne_zero hf0 hz0
  obtain ⟨α, a, hα, ha, hpa, rfl⟩ := exists_prim_mul_of_mem_bddRing hq hqV hy hy0
  obtain ⟨β, b, hβ, hb, hpb, rfl⟩ := exists_prim_mul_of_mem_bddRing hq hqV hz hz0
  refine ⟨(2 * M₀ * l) ^ (k + 2), a, b, β⁻¹ * α, by positivity, Nat.Coprime.pow_right _ hcop,
    ?_, ha, hb, hpa, hpb, mul_ne_zero (inv_ne_zero hβ) hα, ?_⟩
  · rw [pow_add, mul_comm ((2 * M₀ * l) ^ k)]
    exact mul_dvd_mul (dvd_pow ⟨2 * l, by ring⟩ two_ne_zero)
      (pow_dvd_pow_of_dvd (dvd_mul_left l _) k)
  · calc f * b = algebraMap Ω X.K β⁻¹ * (f * (algebraMap Ω X.K β * b)) := by
          rw [mul_left_comm f, ← mul_assoc, ← map_mul, inv_mul_cancel₀ hβ, map_one, one_mul]
      _ = algebraMap Ω X.K (β⁻¹ * α) * a := by rw [hfz, map_mul, mul_assoc]

end GlobalTheory.KZ.ES.Quot
