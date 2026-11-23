import Mathlib
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsBlowUpFibreDegreeCut
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

noncomputable section

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.style.haveILetI false

namespace HomLocLaurent

variable {K : Type*} [DecidableEq K] {ι : K → Type*} {R : Type*} [CommRing R]

section Fractions

variable (P W : Ideal (MRing ι R)) [P.IsPrime]

abbrev fr : MRing ι R →+* FractionRing (MRing ι R ⧸ P) :=
  (algebraMap (MRing ι R ⧸ P) (FractionRing (MRing ι R ⧸ P))).comp (Ideal.Quotient.mk P)

variable {P W}

theorem fr_ne_zero {f : MRing ι R} (hf : f ∉ P) : fr P f ≠ 0 := by
  intro h
  apply hf
  rw [← Ideal.Quotient.eq_zero_iff_mem]
  exact IsFractionRing.injective _ (FractionRing (MRing ι R ⧸ P)) (by simpa using h)

theorem fr_eq_zero_iff {f : MRing ι R} : fr P f = 0 ↔ f ∈ P := by
  refine ⟨fun h => by_contra fun hf => fr_ne_zero hf h, fun h => ?_⟩
  simp [Ideal.Quotient.eq_zero_iff_mem.mpr h]

theorem frac_mem {b : K → ℕ} {f g : MRing ι R} (hf : IsMultiHomog f b) (hg : IsMultiHomog g b)
    (hgW : g ∉ W) : fr P f / fr P g ∈ homLocRing P W :=
  Subring.subset_closure ⟨b, f, g, hf, hg, hgW, rfl⟩

theorem isMultiHomog_add {f g : MRing ι R} {b : K → ℕ} (hf : IsMultiHomog f b)
    (hg : IsMultiHomog g b) : IsMultiHomog (f + g) b :=
  (mem_weightedHomogeneousSubmodule _ _ _ _).mp
    ((weightedHomogeneousSubmodule R (blockWeight ι) b).add_mem
      ((mem_weightedHomogeneousSubmodule _ _ _ _).mpr hf)
      ((mem_weightedHomogeneousSubmodule _ _ _ _).mpr hg))

theorem isMultiHomog_neg {f : MRing ι R} {b : K → ℕ} (hf : IsMultiHomog f b) :
    IsMultiHomog (-f) b :=
  (mem_weightedHomogeneousSubmodule _ _ _ _).mp
    ((weightedHomogeneousSubmodule R (blockWeight ι) b).neg_mem
      ((mem_weightedHomogeneousSubmodule _ _ _ _).mpr hf))

theorem isMultiHomog_mul {f g : MRing ι R} {b c : K → ℕ} (hf : IsMultiHomog f b)
    (hg : IsMultiHomog g c) : IsMultiHomog (f * g) (b + c) :=
  IsWeightedHomogeneous.mul hf hg

theorem exists_frac [W.IsPrime] (hPW : P ≤ W) {a : FractionRing (MRing ι R ⧸ P)}
    (ha : a ∈ homLocRing P W) : ∃ (b : K → ℕ) (f g : MRing ι R), IsMultiHomog f b ∧
      IsMultiHomog g b ∧ g ∉ W ∧ a = fr P f / fr P g := by
  have h1 : (1 : MRing ι R) ∉ W := (Ideal.ne_top_iff_one W).mp Ideal.IsPrime.ne_top'
  have hne : ∀ {g : MRing ι R}, g ∉ W → fr P g ≠ 0 := fun hg => fr_ne_zero (fun h => hg (hPW h))
  induction ha using Subring.closure_induction with
  | mem x hx =>
    obtain ⟨b, f, g, hf, hg, hgW, rfl⟩ := hx
    exact ⟨b, f, g, hf, hg, hgW, rfl⟩
  | zero => exact ⟨0, 0, 1, isWeightedHomogeneous_zero _ _ _, isWeightedHomogeneous_one _ _, h1, by simp⟩
  | one => exact ⟨0, 1, 1, isWeightedHomogeneous_one _ _, isWeightedHomogeneous_one _ _, h1, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨b, f, g, hf, hg, hgW, rfl⟩ := hx
    obtain ⟨b', f', g', hf', hg', hgW', rfl⟩ := hy
    refine ⟨b + b', f * g' + f' * g, g * g', isMultiHomog_add (isMultiHomog_mul hf hg')
      (add_comm b' b ▸ isMultiHomog_mul hf' hg), isMultiHomog_mul hg hg',
      fun h => (Ideal.IsPrime.mem_or_mem ‹_› h).elim hgW hgW', ?_⟩
    rw [div_add_div _ _ (hne hgW) (hne hgW')]
    simp only [map_add, map_mul]
    ring
  | neg x _ hx =>
    obtain ⟨b, f, g, hf, hg, hgW, rfl⟩ := hx
    exact ⟨b, -f, g, isMultiHomog_neg hf, hg, hgW, by simp [neg_div]⟩
  | mul x y _ _ hx hy =>
    obtain ⟨b, f, g, hf, hg, hgW, rfl⟩ := hx
    obtain ⟨b', f', g', hf', hg', hgW', rfl⟩ := hy
    refine ⟨b + b', f * f', g * g', isMultiHomog_mul hf hf', isMultiHomog_mul hg hg',
      fun h => (Ideal.IsPrime.mem_or_mem ‹_› h).elim hgW hgW', ?_⟩
    rw [div_mul_div_comm]
    simp only [map_mul]

end Fractions

section Laurent

variable [Fintype K] (P W : Ideal (MRing ι R)) [P.IsPrime] [W.IsPrime] (T : ∀ k, ι k)

def tpow (n : K → ℕ) : MRing ι R := ∏ k, X ⟨k, T k⟩ ^ n k

theorem isMultiHomog_tpow (n : K → ℕ) : IsMultiHomog (tpow T n : MRing ι R) n := by
  have := IsWeightedHomogeneous.prod (w := blockWeight ι) Finset.univ
    (fun k => (X ⟨k, T k⟩ : MRing ι R) ^ n k) (fun k => n k • Pi.single k 1)
    (fun k _ => (isWeightedHomogeneous_X R (blockWeight ι) ⟨k, T k⟩).pow (n k))
  have h : (∑ k, n k • Pi.single k 1 : K → ℕ) = n := by
    ext j
    simp [Finset.sum_apply, Pi.single_apply]
  rw [h] at this
  exact this

theorem tpow_add (m n : K → ℕ) : (tpow T (m + n) : MRing ι R) = tpow T m * tpow T n := by
  simp [tpow, pow_add, Finset.prod_mul_distrib]

theorem tpow_single (k : K) : (tpow T (Pi.single k 1) : MRing ι R) = X ⟨k, T k⟩ := by
  rw [tpow, Finset.prod_eq_single k]
  · simp
  · intro j _ hj
    simp [Pi.single_apply, hj]
  · simp

variable {W} in
theorem tpow_not_mem (hT : ∀ k, (X ⟨k, T k⟩ : MRing ι R) ∉ W) (n : K → ℕ) :
    (tpow T n : MRing ι R) ∉ W := by
  intro h
  obtain ⟨k, -, hk⟩ := Ideal.IsPrime.prod_mem_iff.mp h
  exact hT k (Ideal.IsPrime.mem_of_pow_mem ‹_› _ hk)

abbrev nz : (K → ℕ) →+ (K → ℤ) := (Nat.castAddMonoidHom ℤ).compLeft K

variable {P W} (hPW : P ≤ W) (hT : ∀ k, (X ⟨k, T k⟩ : MRing ι R) ∉ W)

include hPW hT in
theorem frX_ne_zero (k : K) : fr P (X ⟨k, T k⟩ : MRing ι R) ≠ 0 :=
  fr_ne_zero fun h => hT k (hPW h)

def chi : Multiplicative (K → ℤ) →* FractionRing (MRing ι R ⧸ P) where
  toFun d := ∏ k, fr P (X ⟨k, T k⟩ : MRing ι R) ^ (Multiplicative.toAdd d k)
  map_one' := by simp
  map_mul' a b := by
    simp only [toAdd_mul, Pi.add_apply]
    rw [← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun k _ => zpow_add₀ (frX_ne_zero T hPW hT k) _ _

theorem chi_apply (d : K → ℤ) :
    chi T hPW hT (Multiplicative.ofAdd d) = ∏ k, fr P (X ⟨k, T k⟩ : MRing ι R) ^ d k := rfl

theorem chi_nz (n : K → ℕ) :
    chi T hPW hT (Multiplicative.ofAdd (nz n)) = fr P (tpow T n : MRing ι R) := by
  rw [chi_apply, tpow, map_prod]
  simp [map_pow]

abbrev Lau (P W : Ideal (MRing ι R)) [P.IsPrime] := AddMonoidAlgebra (homLocRing P W) (K → ℤ)

def ev : Lau P W →+* FractionRing (MRing ι R ⧸ P) :=
  AddMonoidAlgebra.liftNCRingHom (homLocRing P W).subtype (chi T hPW hT) (fun _ _ => Commute.all _ _)

theorem ev_single (d : K → ℤ) (a : homLocRing P W) :
    ev T hPW hT (AddMonoidAlgebra.single d a) = a * chi T hPW hT (Multiplicative.ofAdd d) := by
  simp [ev, AddMonoidAlgebra.liftNCRingHom_single]

theorem one_not_mem_alt (W : Ideal (MRing ι R)) [W.IsPrime] : (1 : MRing ι R) ∉ W :=
  (Ideal.ne_top_iff_one W).mp Ideal.IsPrime.ne_top'

def constHom (P W : Ideal (MRing ι R)) [P.IsPrime] [W.IsPrime] : R →+* homLocRing P W :=
  RingHom.codRestrict ((fr P).comp (C : R →+* MRing ι R)) (homLocRing P W) fun r => by
    simpa using frac_mem (P := P) (W := W) (isWeightedHomogeneous_C (blockWeight ι) r)
      (isWeightedHomogeneous_one R (blockWeight ι)) (one_not_mem_alt W)

def uu (v : Σ k, ι k) : homLocRing P W :=
  ⟨fr P (X v) / fr P (X ⟨v.1, T v.1⟩),
    frac_mem (isWeightedHomogeneous_X R (blockWeight ι) v)
      (isWeightedHomogeneous_X R (blockWeight ι) ⟨v.1, T v.1⟩) (hT v.1)⟩

def psi : MRing ι R →+* Lau P W :=
  eval₂Hom (AddMonoidAlgebra.singleZeroRingHom.comp (constHom P W))
    (fun v => AddMonoidAlgebra.single (nz (blockWeight ι v)) (uu T hT v))

theorem ev_comp_psi : (ev T hPW hT).comp (psi T hT) = fr P := by
  apply MvPolynomial.ringHom_ext
  · intro r
    simp [psi, ev_single, constHom]
  · intro v
    simp only [psi, RingHom.comp_apply, coe_eval₂Hom, eval₂_X, ev_single]
    rw [chi_nz, show blockWeight ι v = Pi.single v.1 1 from rfl, tpow_single]
    exact div_mul_cancel₀ _ (frX_ne_zero T hPW hT v.1)

theorem psi_monomial (s : (Σ k, ι k) →₀ ℕ) (c : R) :
    psi T hT (monomial s c) = AddMonoidAlgebra.single (nz (Finsupp.weight (blockWeight ι) s))
      (constHom P W c * s.prod fun v n => uu T hT v ^ n) := by
  simp only [psi, coe_eval₂Hom, eval₂_monomial, RingHom.comp_apply,
    AddMonoidAlgebra.singleZeroRingHom_apply, Finsupp.prod, AddMonoidAlgebra.single_pow,
    AddMonoidAlgebra.prod_single, AddMonoidAlgebra.single_mul_single, zero_add, Finsupp.weight_apply,
    Finsupp.sum, map_sum, map_nsmul]
  change AddMonoidAlgebra.single 0 _ * _ = _
  rw [AddMonoidAlgebra.single_mul_single, zero_add]

end Laurent

section Localization

variable [Fintype K] {P W : Ideal (MRing ι R)} [P.IsPrime] [W.IsPrime] (T : ∀ k, ι k)
  (hPW : P ≤ W) (hT : ∀ k, (X ⟨k, T k⟩ : MRing ι R) ∉ W)

theorem psi_homog_exists {f : MRing ι R} {b : K → ℕ} (hf : IsMultiHomog f b) :
    ∃ a, psi (P := P) T hT f = AddMonoidAlgebra.single (nz b) a := by
  refine ⟨∑ s ∈ f.support, constHom P W (coeff s f) * s.prod fun v n => uu T hT v ^ n, ?_⟩
  conv_lhs => rw [f.as_sum]
  rw [map_sum, ← AddMonoidAlgebra.singleAddHom_apply, map_sum]
  refine Finset.sum_congr rfl fun s hs => ?_
  rw [psi_monomial, AddMonoidAlgebra.singleAddHom_apply]
  congr 2
  exact hf (mem_support_iff.mp hs)

include hPW in
theorem psi_homog {f : MRing ι R} {b : K → ℕ} (hf : IsMultiHomog f b) :
    psi (P := P) T hT f = AddMonoidAlgebra.single (nz b)
      (⟨fr P f / fr P (tpow T b), frac_mem hf (isMultiHomog_tpow T b) (tpow_not_mem T hT b)⟩ :
        homLocRing P W) := by
  obtain ⟨a, ha⟩ := psi_homog_exists (P := P) T hT hf
  rw [ha]
  congr 1
  apply Subtype.ext
  have h := congrArg (ev T hPW hT) ha
  rw [← RingHom.comp_apply, ev_comp_psi, ev_single, chi_nz] at h
  change (a : FractionRing (MRing ι R ⧸ P)) = fr P f / fr P (tpow T b)
  rw [h, mul_div_cancel_right₀ _ (fr_ne_zero fun h' => tpow_not_mem T hT b (hPW h'))]

include hPW in
theorem psi_eq_zero (hPh : IsMultiHomogIdeal P) {f : MRing ι R} (hf : f ∈ P) :
    psi (P := P) T hT f = 0 := by
  conv_lhs => rw [← sum_weightedHomogeneousComponent (w := blockWeight ι) f]
  refine finsum_induction (fun q => psi (P := P) T hT q = 0) (map_zero _)
    (fun x y hx hy => by rw [map_add, hx, hy, add_zero]) fun b => ?_
  rw [psi_homog T hPW hT (weightedHomogeneousComponent_isWeightedHomogeneous b f)]
  have h0 : fr P (weightedHomogeneousComponent (blockWeight ι) b f) = 0 :=
    fr_eq_zero_iff.mpr (hPh f hf b)
  have : (⟨fr P (weightedHomogeneousComponent (blockWeight ι) b f) / fr P (tpow T b), frac_mem
      (weightedHomogeneousComponent_isWeightedHomogeneous b f) (isMultiHomog_tpow T b)
      (tpow_not_mem T hT b)⟩ : homLocRing P W) = 0 := Subtype.ext (by simp [h0])
  rw [this, AddMonoidAlgebra.single_zero]

def psiQ (hPh : IsMultiHomogIdeal P) : (MRing ι R ⧸ P) →+* Lau P W :=
  Ideal.Quotient.lift P (psi T hT) fun _ hf => psi_eq_zero T hPW hT hPh hf

theorem psiQ_mk (hPh : IsMultiHomogIdeal P) (f : MRing ι R) :
    psiQ T hPW hT hPh (Ideal.Quotient.mk P f) = psi T hT f := Ideal.Quotient.lift_mk _ _ _

theorem ev_comp_psiQ (hPh : IsMultiHomogIdeal P) :
    (ev T hPW hT).comp (psiQ T hPW hT hPh) =
      algebraMap (MRing ι R ⧸ P) (FractionRing (MRing ι R ⧸ P)) := by
  refine Ideal.Quotient.ringHom_ext (RingHom.ext fun f => ?_)
  simp only [RingHom.comp_apply, psiQ_mk]
  rw [← RingHom.comp_apply (ev T hPW hT), ev_comp_psi]
  rfl

theorem psiQ_injective (hPh : IsMultiHomogIdeal P) : Function.Injective (psiQ T hPW hT hPh) := by
  intro x y h
  apply IsFractionRing.injective (MRing ι R ⧸ P) (FractionRing (MRing ι R ⧸ P))
  rw [← ev_comp_psiQ T hPW hT hPh, RingHom.comp_apply, RingHom.comp_apply, h]

def homSub (P W : Ideal (MRing ι R)) [W.IsPrime] : Submonoid (MRing ι R ⧸ P) where
  carrier := {r | ∃ (b : K → ℕ) (f : MRing ι R), IsMultiHomog f b ∧ f ∉ W ∧ Ideal.Quotient.mk P f = r}
  mul_mem' := by
    rintro _ _ ⟨b, f, hf, hfW, rfl⟩ ⟨b', f', hf', hfW', rfl⟩
    exact ⟨b + b', f * f', isMultiHomog_mul hf hf',
      fun h => (Ideal.IsPrime.mem_or_mem ‹_› h).elim hfW hfW', map_mul _ _ _⟩
  one_mem' := ⟨0, 1, isWeightedHomogeneous_one _ _, one_not_mem_alt W, map_one _⟩

theorem isLocalization_lau (hPh : IsMultiHomogIdeal P) :
    letI := (psiQ T hPW hT hPh).toAlgebra
    IsLocalization (homSub (K := K) P W) (Lau P W) := by
  let := (psiQ T hPW hT hPh).toAlgebra
  have hne : ∀ {g : MRing ι R}, g ∉ W → fr P g ≠ 0 := fun hg => fr_ne_zero fun h => hg (hPW h)
  rw [isLocalization_iff]
  refine ⟨?_, ?_, ?_⟩
  · rintro ⟨_, b, f, hf, hfW, rfl⟩
    change IsUnit (psiQ T hPW hT hPh (Ideal.Quotient.mk P f))
    rw [psiQ_mk, psi_homog T hPW hT hf]
    refine IsUnit.of_mul_eq_one (AddMonoidAlgebra.single (-nz b)
      ⟨fr P (tpow T b) / fr P f, frac_mem (isMultiHomog_tpow T b) hf hfW⟩) ?_
    rw [AddMonoidAlgebra.single_mul_single, add_neg_cancel, AddMonoidAlgebra.one_def]
    congr 1
    apply Subtype.ext
    have h1 := hne hfW
    have h2 := hne (tpow_not_mem T hT b)
    simp only [MulMemClass.coe_mul, OneMemClass.coe_one]
    field_simp
  · intro p
    induction p using AddMonoidAlgebra.induction_linear with
    | zero => exact ⟨⟨0, 1⟩, by simp⟩
    | add p q hp hq =>
      obtain ⟨⟨r, h⟩, hr⟩ := hp
      obtain ⟨⟨r', h'⟩, hr'⟩ := hq
      refine ⟨⟨r * h' + r' * h, h * h'⟩, ?_⟩
      simp only [Submonoid.coe_mul, map_mul, map_add] at hr hr' ⊢
      rw [← hr, ← hr']
      ring
    | single d a =>
      obtain ⟨b, f, g, hf, hg, hgW, ha⟩ := exists_frac hPW a.2
      set dp : K → ℕ := fun k => (d k).toNat
      set dm : K → ℕ := fun k => (-d k).toNat
      refine ⟨⟨Ideal.Quotient.mk P (f * tpow T dp), ⟨_, b + dm, g * tpow T dm,
        isMultiHomog_mul hg (isMultiHomog_tpow T dm),
        fun h => (Ideal.IsPrime.mem_or_mem ‹_› h).elim hgW (tpow_not_mem T hT dm), rfl⟩⟩, ?_⟩
      change AddMonoidAlgebra.single d a * psiQ T hPW hT hPh (Ideal.Quotient.mk P (g * tpow T dm)) =
        psiQ T hPW hT hPh (Ideal.Quotient.mk P (f * tpow T dp))
      rw [psiQ_mk, psiQ_mk, psi_homog T hPW hT (isMultiHomog_mul hg (isMultiHomog_tpow T dm)),
        psi_homog T hPW hT (isMultiHomog_mul hf (isMultiHomog_tpow T dp)),
        AddMonoidAlgebra.single_mul_single]
      congr 1
      · ext k
        simp only [Pi.add_apply, map_add, dp, dm]
        simp only [AddMonoidHom.compLeft_apply, Function.comp_apply, Nat.coe_castAddMonoidHom]
        omega
      · apply Subtype.ext
        have h1 := hne hgW
        have h2 := hne (tpow_not_mem T hT b)
        have h3 := hne (tpow_not_mem T hT dm)
        have h4 := hne (tpow_not_mem T hT dp)
        simp only [MulMemClass.coe_mul, ha, tpow_add, map_mul]
        field_simp
  · intro x y h
    exact ⟨1, by simpa using psiQ_injective T hPW hT hPh h⟩

end Localization

section Local

variable [Fintype K] {P W : Ideal (MRing ι R)} [P.IsPrime] [W.IsPrime]

theorem wbar_isPrime (hPW : P ≤ W) : (W.map (Ideal.Quotient.mk P)).IsPrime :=
  Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective (by rw [Ideal.mk_ker]; exact hPW)

def locC (hPW : P ≤ W) : Subring (FractionRing (MRing ι R ⧸ P)) :=
  haveI := wbar_isPrime hPW
  (Localization.subalgebra.ofField (FractionRing (MRing ι R ⧸ P))
    (W.map (Ideal.Quotient.mk P)).primeCompl (Ideal.primeCompl_le_nonZeroDivisors _)).toSubring

def algQC (hPW : P ≤ W) : (MRing ι R ⧸ P) →+* locC hPW :=
  haveI := wbar_isPrime hPW
  (algebraMap (MRing ι R ⧸ P) (FractionRing (MRing ι R ⧸ P))).codRestrict (locC hPW)
    fun r => ⟨r, 1, Submonoid.one_mem _, by simp⟩

theorem locC_isLocalization (hPW : P ≤ W) :
    letI := (algQC hPW).toAlgebra
    haveI := wbar_isPrime hPW
    IsLocalization.AtPrime (locC hPW) (W.map (Ideal.Quotient.mk P)) := by
  letI := (algQC hPW).toAlgebra
  haveI := wbar_isPrime hPW
  have hnz : ∀ s ∈ (W.map (Ideal.Quotient.mk P)).primeCompl,
      algebraMap (MRing ι R ⧸ P) (FractionRing (MRing ι R ⧸ P)) s ≠ 0 := by
    intro s hs h
    apply hs
    rw [IsFractionRing.injective _ (FractionRing (MRing ι R ⧸ P)) (h.trans (map_zero _).symm)]
    exact zero_mem _
  show IsLocalization _ _
  rw [isLocalization_iff]
  refine ⟨fun ⟨s, hs⟩ => ?_, fun ⟨z, hz⟩ => ?_, fun {x y} h => ?_⟩
  · refine IsUnit.of_mul_eq_one (⟨(algebraMap _ (FractionRing (MRing ι R ⧸ P)) s)⁻¹,
      ⟨1, s, hs, by simp⟩⟩ : locC hPW) (Subtype.ext ?_)
    exact mul_inv_cancel₀ (hnz s hs)
  · obtain ⟨a, s, hs, rfl⟩ := hz
    refine ⟨(a, ⟨s, hs⟩), Subtype.ext ?_⟩
    change _ * algebraMap _ (FractionRing (MRing ι R ⧸ P)) s = algebraMap _ _ a
    rw [mul_assoc, inv_mul_cancel₀ (hnz s hs), mul_one]
  · refine ⟨1, ?_⟩
    have := congrArg Subtype.val h
    rw [IsFractionRing.injective _ (FractionRing (MRing ι R ⧸ P)) this]

theorem mem_locC (hPW : P ≤ W) {y : FractionRing (MRing ι R ⧸ P)} (a s : MRing ι R) (hs : s ∉ W)
    (hy : y = fr P a * (fr P s)⁻¹) : y ∈ locC hPW := by
  haveI := wbar_isPrime hPW
  exact ⟨Ideal.Quotient.mk P a, Ideal.Quotient.mk P s,
    fun h => hs ((Ideal.mem_quotient_iff_mem hPW).mp h), hy⟩

theorem homLocRing_le_locC (hPW : P ≤ W) : homLocRing P W ≤ locC hPW := by
  unfold homLocRing
  rw [Subring.closure_le]
  rintro _ ⟨b, f, g, -, -, hgW, rfl⟩
  exact mem_locC hPW f g hgW (div_eq_mul_inv _ _)

theorem zpow_mem_locC (hPW : P ≤ W) {x : FractionRing (MRing ι R ⧸ P)} (hx : x ∈ locC hPW)
    (hx' : x⁻¹ ∈ locC hPW) (n : ℤ) : x ^ n ∈ locC hPW := by
  cases n with
  | ofNat m => rw [Int.ofNat_eq_natCast, zpow_natCast]; exact pow_mem hx m
  | negSucc m => rw [zpow_negSucc, ← inv_pow]; exact pow_mem hx' _

def incAC (hPW : P ≤ W) : homLocRing P W →+* locC hPW :=
  (homLocRing P W).subtype.codRestrict (locC hPW) fun a => homLocRing_le_locC hPW a.2

variable (T : ∀ k, ι k) (hPW : P ≤ W) (hT : ∀ k, (X ⟨k, T k⟩ : MRing ι R) ∉ W)

theorem ev_mem_locC (p : Lau P W) : ev T hPW hT p ∈ locC hPW := by
  induction p using AddMonoidAlgebra.induction_linear with
  | zero => rw [map_zero]; exact zero_mem _
  | add p q hp hq => rw [map_add]; exact add_mem hp hq
  | single d a =>
    rw [ev_single, chi_apply]
    refine mul_mem (homLocRing_le_locC hPW a.2) (prod_mem fun k _ => zpow_mem_locC hPW ?_ ?_ _)
    · exact mem_locC hPW (X ⟨k, T k⟩) 1 (one_not_mem_alt W) (by simp)
    · exact mem_locC hPW 1 (X ⟨k, T k⟩) (hT k) (by simp)

def evC : Lau P W →+* locC hPW := (ev T hPW hT).codRestrict (locC hPW) (ev_mem_locC T hPW hT)

include hT in

theorem incAC_isLocalHom : IsLocalHom (incAC hPW) := by
  letI := (algQC hPW).toAlgebra
  haveI := wbar_isPrime hPW
  haveI := locC_isLocalization hPW
  refine ⟨fun a ha => ?_⟩
  obtain ⟨b, f, g, hf, hg, hgW, hag⟩ := exists_frac hPW a.2
  have hne : ∀ {g : MRing ι R}, g ∉ W → fr P g ≠ 0 := fun hg => fr_ne_zero fun h => hg (hPW h)
  have hgu : IsUnit (algQC hPW (Ideal.Quotient.mk P g)) :=
    (IsLocalization.AtPrime.isUnit_to_map_iff (locC hPW) (W.map (Ideal.Quotient.mk P)) _).mpr
      fun h => hgW ((Ideal.mem_quotient_iff_mem hPW).mp h)
  have hfe : algQC hPW (Ideal.Quotient.mk P f) =
      incAC hPW a * algQC hPW (Ideal.Quotient.mk P g) := by
    apply Subtype.ext
    change fr P f = (a : FractionRing (MRing ι R ⧸ P)) * fr P g
    rw [hag, div_mul_cancel₀ _ (hne hgW)]
  have hfW : f ∉ W := by
    intro hfW
    have hfu : IsUnit (algQC hPW (Ideal.Quotient.mk P f)) := by
      rw [hfe]; exact ha.mul hgu
    exact (IsLocalization.AtPrime.isUnit_to_map_iff (locC hPW) (W.map (Ideal.Quotient.mk P)) _).mp hfu
      (Ideal.mem_map_of_mem _ hfW)
  refine IsUnit.of_mul_eq_one (⟨fr P g / fr P f, frac_mem hg hf hfW⟩ : homLocRing P W) ?_
  apply Subtype.ext
  have h1 := hne hgW
  have h2 := hne hfW
  simp only [MulMemClass.coe_mul, OneMemClass.coe_one, hag]
  field_simp

include hT in

theorem map_maximalIdeal_incAC [IsLocalRing (homLocRing P W)] (hWh : IsMultiHomogIdeal W) :
    letI := (algQC hPW).toAlgebra
    haveI := wbar_isPrime hPW
    haveI := locC_isLocalization hPW
    haveI := IsLocalization.AtPrime.isLocalRing (locC hPW) (W.map (Ideal.Quotient.mk P))
    (IsLocalRing.maximalIdeal (homLocRing P W)).map (incAC hPW) =
      IsLocalRing.maximalIdeal (locC hPW) := by
  letI := (algQC hPW).toAlgebra
  haveI := wbar_isPrime hPW
  haveI := locC_isLocalization hPW
  haveI := IsLocalization.AtPrime.isLocalRing (locC hPW) (W.map (Ideal.Quotient.mk P))
  haveI := incAC_isLocalHom T hPW hT
  have hne : ∀ {g : MRing ι R}, g ∉ W → fr P g ≠ 0 := fun hg => fr_ne_zero fun h => hg (hPW h)
  have hunit : ∀ {g : MRing ι R}, g ∉ W →
      IsUnit (algQC hPW (Ideal.Quotient.mk P g)) := fun hg =>
    (IsLocalization.AtPrime.isUnit_to_map_iff (locC hPW) (W.map (Ideal.Quotient.mk P)) _).mpr
      fun h => hg ((Ideal.mem_quotient_iff_mem hPW).mp h)
  apply le_antisymm
  · rw [Ideal.map_le_iff_le_comap]
    intro x hx
    rw [Ideal.mem_comap, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    exact fun h => (IsLocalRing.mem_maximalIdeal _).mp hx (isUnit_of_map_unit _ _ h)
  · rw [← IsLocalization.AtPrime.map_eq_maximalIdeal (W.map (Ideal.Quotient.mk P)) (locC hPW),
      Ideal.map_map, Ideal.map_le_iff_le_comap]
    intro w hw
    rw [Ideal.mem_comap]
    conv => rw [← sum_weightedHomogeneousComponent (w := blockWeight ι) w]
    refine finsum_induction (fun q => ((algQC hPW).comp
        (Ideal.Quotient.mk P)) q ∈ (IsLocalRing.maximalIdeal (homLocRing P W)).map (incAC hPW))
      (by rw [RingHom.map_zero]; exact zero_mem _)
      (fun x y hx hy => by rw [RingHom.map_add]; exact add_mem hx hy)
      fun b => ?_
    set wb := weightedHomogeneousComponent (blockWeight ι) b w
    have hwb : IsMultiHomog wb b := weightedHomogeneousComponent_isWeightedHomogeneous b w
    have hwbW : wb ∈ W := hWh w hw b
    set c : homLocRing P W := ⟨fr P wb / fr P (tpow T b), frac_mem hwb (isMultiHomog_tpow T b)
      (tpow_not_mem T hT b)⟩
    have hce : ((algQC hPW).comp (Ideal.Quotient.mk P)) wb =
        incAC hPW c * algQC hPW (Ideal.Quotient.mk P (tpow T b)) := by
      apply Subtype.ext
      change fr P wb = fr P wb / fr P (tpow T b) * fr P (tpow T b)
      rw [div_mul_cancel₀ _ (hne (tpow_not_mem T hT b))]
    rw [hce]
    refine Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ ?_)
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    intro hc
    have hu : IsUnit (((algQC hPW).comp (Ideal.Quotient.mk P)) wb) := by
      rw [hce]; exact (hc.map _).mul (hunit (tpow_not_mem T hT b))
    exact (IsLocalization.AtPrime.isUnit_to_map_iff (locC hPW) (W.map (Ideal.Quotient.mk P)) _).mp hu
      (Ideal.mem_map_of_mem _ hwbW)

end Local

section Length

variable [Fintype K] {P W : Ideal (MRing ι R)} [P.IsPrime] [W.IsPrime]
  (T : ∀ k, ι k) (hPW : P ≤ W) (hT : ∀ k, (X ⟨k, T k⟩ : MRing ι R) ∉ W)

include hT in

theorem flat_incAC (hPh : IsMultiHomogIdeal P) :
    letI := (incAC hPW).toAlgebra
    Module.Flat (homLocRing P W) (locC hPW) := by
  letI := (algQC hPW).toAlgebra
  haveI := wbar_isPrime hPW
  haveI := locC_isLocalization hPW
  letI : Algebra (MRing ι R ⧸ P) (Lau P W) := (psiQ T hPW hT hPh).toAlgebra
  haveI := isLocalization_lau T hPW hT hPh
  letI : Algebra (Lau P W) (locC hPW) := (evC T hPW hT).toAlgebra
  haveI : IsScalarTower (MRing ι R ⧸ P) (Lau P W) (locC hPW) :=
    IsScalarTower.of_algebraMap_eq fun x => by
      apply Subtype.ext
      change algebraMap _ (FractionRing _) x = ev T hPW hT (psiQ T hPW hT hPh x)
      rw [← RingHom.comp_apply, ev_comp_psiQ]
  have hle : homSub (K := K) P W ≤ (W.map (Ideal.Quotient.mk P)).primeCompl := by
    rintro _ ⟨b, f, -, hfW, rfl⟩ h
    exact hfW ((Ideal.mem_quotient_iff_mem hPW).mp h)
  haveI := IsLocalization.isLocalization_of_submonoid_le (Lau P W) (locC hPW)
    (homSub (K := K) P W) _ hle
  haveI : Module.Flat (Lau P W) (locC hPW) := IsLocalization.flat (locC hPW)
    ((W.map (Ideal.Quotient.mk P)).primeCompl.map (algebraMap (MRing ι R ⧸ P) (Lau P W)))
  haveI : Module.Free (homLocRing P W) (Lau P W) :=
    Module.Free.of_basis (AddMonoidAlgebra.basis (K → ℤ) (homLocRing P W))
  haveI : Module.Flat (homLocRing P W) (Lau P W) := Module.Flat.of_free
  letI := (incAC hPW).toAlgebra
  haveI : IsScalarTower (homLocRing P W) (Lau P W) (locC hPW) :=
    IsScalarTower.of_algebraMap_eq fun a => by
      apply Subtype.ext
      change (a : FractionRing _) = ev T hPW hT (algebraMap (homLocRing P W) (Lau P W) a)
      rw [AddMonoidAlgebra.coe_algebraMap, Function.comp_apply, ev_single]
      simp
  exact Module.Flat.trans (homLocRing P W) (Lau P W) (locC hPW)

include hT in

theorem length_quotient_incAC (hPh : IsMultiHomogIdeal P) (hWh : IsMultiHomogIdeal W)
    [IsLocalRing (homLocRing P W)] (a : homLocRing P W) :
    Module.length (locC hPW) (locC hPW ⧸ Ideal.span {incAC hPW a}) =
      Module.length (homLocRing P W) (homLocRing P W ⧸ Ideal.span {a}) := by
  letI := (algQC hPW).toAlgebra
  haveI := wbar_isPrime hPW
  haveI := locC_isLocalization hPW
  haveI := IsLocalization.AtPrime.isLocalRing (locC hPW) (W.map (Ideal.Quotient.mk P))
  letI := (incAC hPW).toAlgebra
  haveI : IsLocalHom (algebraMap (homLocRing P W) (locC hPW)) := incAC_isLocalHom T hPW hT
  haveI := flat_incAC T hPW hT hPh
  have key := IsLocalRing.length_baseChange (homLocRing P W) (locC hPW)
    (homLocRing P W ⧸ Ideal.span {a})
  have hm := map_maximalIdeal_incAC T hPW hT hWh
  have h1 : Module.length (locC hPW) (locC hPW ⧸ IsLocalRing.maximalIdeal (locC hPW)) = 1 := by
    have : IsSimpleModule (locC hPW) (locC hPW ⧸ IsLocalRing.maximalIdeal (locC hPW)) :=
      isSimpleModule_iff_quot_maximal.mpr
        ⟨_, IsLocalRing.maximalIdeal.isMaximal _, ⟨LinearEquiv.refl _ _⟩⟩
    exact Module.length_eq_one _ _
  rw [show algebraMap (homLocRing P W) (locC hPW) = incAC hPW from rfl, hm, h1, mul_one,
    ← (Algebra.TensorProduct.quotIdealMapEquivTensorQuot (locC hPW)
      (Ideal.span {a})).toLinearEquiv.length_eq, Ideal.map_span, Set.image_singleton] at key
  exact key

end Length

end HomLocLaurent

end

end GroundTheory.Heights₂.Heights.NumbersDVR
