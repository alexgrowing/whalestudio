import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Formalism.PairingDivisors.StatementH
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RationalPointsIntegralPointsMembership
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.UnitaryGroupWeakApproximationAtPrimes
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Afsplit
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.CsGlob
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.CsScale
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ConjugateMinimaInstance

noncomputable section

namespace GlobalTheory.NormSum.RepAt

open NumberField IsDedekindDomain Formalism.UG Formalism.UG.P
open scoped TensorProduct Matrix

theorem unit_of_integral {A R : Type} [CommRing A] [CommRing R] (φ : A →+* R) (hφ : φ.IsIntegral)
    (a : A) (ha : ∀ c, IsUnit (1 + a * c)) (x : R) : IsUnit (1 + φ a * x) := by
  by_contra h
  obtain ⟨m, hm, hle⟩ := Ideal.exists_le_maximal (Ideal.span {1 + φ a * x})
    (fun h' => h (Ideal.span_singleton_eq_top.1 h'))
  have h1 : 1 + φ a * x ∈ m := hle (Ideal.mem_span_singleton_self _)
  have hm' : (m.comap φ).IsMaximal := Ideal.isMaximal_comap_of_isIntegral_of_isMaximal' φ hφ m
  have h2 : a ∈ m.comap φ := by
    by_contra hn
    obtain ⟨y, i, hi, e⟩ := hm'.exists_inv hn
    have : i = 1 + a * (-y) := by linear_combination e
    exact hm'.ne_top (Ideal.eq_top_of_isUnit_mem _ hi (this ▸ ha _))
  have h3 : φ a * x ∈ m := m.mul_mem_right _ h2
  exact hm.ne_top ((Ideal.eq_top_iff_one _).2 (by simpa using sub_mem h1 h3))

theorem exists_unit_det {K B : Type} [Field K] [CommRing B] [IsArtinianRing B] (ι : K →+* B) {n : ℕ}
    (h : Matrix (Fin n) (Fin n) B) (Z : Set K) (hZ : Z.Infinite) :
    ∃ z ∈ Z, IsUnit (1 + ι z • h).det := by
  have key : ∀ m : MaximalSpectrum B, {z : K | (1 + ι z • h).det ∈ m.asIdeal}.Finite := by
    intro m
    classical
    haveI := m.isMaximal
    letI : Field (B ⧸ m.asIdeal) := Ideal.Quotient.field _
    let π := Ideal.Quotient.mk m.asIdeal
    let P := ((-h).map π).charpolyRev
    have hP : P ≠ 0 := by
      intro h0
      have := Matrix.eval_charpolyRev (M := (-h).map π)
      rw [show ((-h).map π).charpolyRev = 0 from h0] at this
      simp at this
    refine ((P.roots.toFinset.finite_toSet).preimage (f := π.comp ι)
      (π.comp ι).injective.injOn).subset fun z hz => ?_
    simp only [Set.mem_preimage, Finset.mem_coe, Multiset.mem_toFinset, Polynomial.mem_roots hP,
      Polynomial.IsRoot]
    have h1 : π (1 + ι z • h).det = 0 := Ideal.Quotient.eq_zero_iff_mem.2 hz
    rw [← h1, RingHom.map_det]
    change Polynomial.evalRingHom _ (Matrix.det _) = _
    rw [RingHom.map_det]
    congr 1
    ext i j
    by_cases hij : i = j <;> simp [Matrix.one_apply, hij] <;> exact mul_comm _ _
  have hfin : (⋃ m : MaximalSpectrum B, {z : K | (1 + ι z • h).det ∈ m.asIdeal}).Finite :=
    Set.finite_iUnion key
  obtain ⟨z, hz, hn⟩ := hZ.exists_notMem_finite hfin
  refine ⟨z, hz, ?_⟩
  by_contra hu
  obtain ⟨m, hm, hle⟩ := Ideal.exists_le_maximal (Ideal.span {(1 + ι z • h).det})
    (fun h' => hu (Ideal.span_singleton_eq_top.1 h'))
  exact hn (Set.mem_iUnion.2 ⟨⟨m, hm⟩, hle (Ideal.mem_span_singleton_self _)⟩)

theorem normOne_infinite {K : Type} [Field K] [CharZero K] (c : K →+* K) (hc : ∀ x, c (c x) = x)
    (hne : ∃ z, c z ≠ z) : {z : K | z * c z = 1 ∧ 1 + z ≠ 0}.Infinite := by
  obtain ⟨z, hz⟩ := hne
  set d := c z - z with hd
  have hd0 : d ≠ 0 := sub_ne_zero.2 hz
  have hcd : c d = -d := by rw [hd, map_sub, hc]; ring
  have h1 : ∀ t : ℕ, 1 - (t : K) * d ≠ 0 ∧ 1 + (t : K) * d ≠ 0 := by
    intro t
    have e : c (1 - (t : K) * d) = 1 + (t : K) * d := by
      rw [map_sub, map_one, map_mul, map_natCast, hcd]; ring
    have a : 1 - (t : K) * d ≠ 0 := fun h => by
      have h' := e
      rw [h, map_zero] at h'
      have : (2 : K) = 0 := by linear_combination h - h'
      exact two_ne_zero this
    exact ⟨a, by rw [← e]; exact (map_ne_zero c).2 a⟩
  refine Set.infinite_of_injective_forall_mem
    (f := fun t : ℕ => (1 + (t : K) * d) / (1 - (t : K) * d)) (fun s t hst => ?_) fun t => ?_
  · simp only at hst
    rw [div_eq_div_iff (h1 s).1 (h1 t).1] at hst
    have : 2 * d * ((s : K) - t) = 0 := by linear_combination hst
    have h2 := (mul_eq_zero.1 this).resolve_left (mul_ne_zero two_ne_zero hd0)
    exact_mod_cast sub_eq_zero.1 h2
  · obtain ⟨a, b⟩ := h1 t
    refine ⟨?_, ?_⟩
    · rw [map_div₀, map_add, map_sub, map_one, map_mul, map_natCast, hcd, mul_neg, sub_neg_eq_add,
        ← sub_eq_add_neg]
      field_simp
    · have : 1 + (1 + (t : K) * d) / (1 - (t : K) * d) = 2 / (1 - (t : K) * d) := by
        field_simp; ring
      rw [this]
      exact div_ne_zero two_ne_zero a

def matIn {R : Type} [CommRing R] (O : Subring R) (n : ℕ) : Subring (Matrix (Fin n) (Fin n) R) where
  carrier := {M | ∀ i j, M i j ∈ O}
  mul_mem' := fun {a b} ha hb i j => by
    rw [Matrix.mul_apply]; exact sum_mem fun l _ => mul_mem (ha i l) (hb l j)
  one_mem' := afsplit_one_mem O
  add_mem' := fun {a b} ha hb i j => add_mem (ha i j) (hb i j)
  zero_mem' := fun _ _ => zero_mem _
  neg_mem' := fun {a} ha i j => neg_mem (ha i j)

theorem mat_inv {R : Type} [CommRing R] (O : Subring R) {n : ℕ} (a : O) (ha : ∀ x : O, IsUnit (1 + a * x))
    (X : Matrix (Fin n) (Fin n) R) (hX : X ∈ matIn O n) :
    ∃ W ∈ matIn O n, (1 + (a : R) • X) * W = 1 := by
  let X' : Matrix (Fin n) (Fin n) O := fun i j => ⟨X i j, hX i j⟩
  have hu : IsUnit (1 + a • X').det := by
    rw [Matrix.det_one_add_smul, add_assoc, pow_two, ← mul_assoc, ← add_mul, mul_comm]
    exact ha _
  refine ⟨(1 + a • X')⁻¹.map O.subtype, fun i j => ((1 + a • X')⁻¹ i j).2, ?_⟩
  have e : (1 + (a : R) • X) = (1 + a • X').map O.subtype := by
    ext i j
    by_cases hij : i = j <;> simp [Matrix.one_apply, hij, X'] <;> rfl
  rw [e, ← Matrix.map_mul, Matrix.mul_nonsing_inv _ hu, Matrix.map_one _ (map_zero _) (map_one _)]

section Ad

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

local notation "𝔸" => FiniteAdeleRing (𝓞 F) F
local notation "𝒜" => E ⊗[F] FiniteAdeleRing (𝓞 F) F
local notation "𝒮" => tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (intOE E) (intAd F)
local notation "ιA" => inclE (F := F) (E := E) (FiniteAdeleRing (𝓞 F) F)

theorem levelafC_nat (m : ℕ) : levelafC (F := F) E (m : 𝓞 F) = (m : 𝒜) := by
  rw [levelafC, map_natCast]
  exact map_natCast (Algebra.TensorProduct.includeRight : 𝔸 →ₐ[F] 𝒜) m

theorem denom (x : 𝒜) : ∃ m : ℕ, 0 < m ∧ (m : 𝒜) * x ∈ 𝒮 := by
  obtain ⟨d, hd, h⟩ := levelaf_denom x
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 (Ideal.absNorm_mem (Ideal.span {d}))
  refine ⟨Ideal.absNorm (Ideal.span {d}), Nat.pos_of_ne_zero ?_, ?_⟩
  · rw [Ne, Ideal.absNorm_eq_zero_iff, Ideal.span_singleton_eq_bot]; exact hd
  · rw [← levelafC_nat, ← hc, levelafC_mul, mul_assoc]
    exact mul_mem (levelafC_mem _) h

theorem approx (x : 𝒜) (D : ℕ) (hD : 0 < D) : ∃ y : E, ∃ o ∈ 𝒮, x = ιA y + (D : 𝒜) * o := by
  obtain ⟨m, hm, h⟩ := denom x
  obtain ⟨b, t, ht, e⟩ := csGlob_approx csGlob_intAdApprox ((m * D : ℕ) : 𝓞 F)
    (Nat.cast_ne_zero.2 (by positivity)) _ h
  refine ⟨(m : E)⁻¹ * algebraMap (𝓞 E) E b, t, ht, ?_⟩
  have h1 : ιA (m : E)⁻¹ * (m : 𝒜) = 1 := by
    rw [← map_natCast ιA, ← map_mul, inv_mul_cancel₀ (Nat.cast_ne_zero.2 hm.ne'), map_one]
  rw [levelafC_nat, Nat.cast_mul] at e
  rw [map_mul]
  linear_combination (ιA (m : E)⁻¹) * e + ((D : 𝒜) * t - x) * h1

theorem val_nat (w : HeightOneSpectrum (𝓞 F)) (p : ℕ) :
    Valued.v (p : w.adicCompletion F) = w.valuation F (algebraMap (𝓞 F) F p) := by
  rw [← levelaf_valued_algebraMap, map_natCast (algebraMap (𝓞 F) F), map_natCast (algebraMap F _)]

theorem unit_intAd (v : HeightOneSpectrum (𝓞 F)) (p : ℕ) (hp : (p : 𝓞 F) ∈ v.asIdeal)
    (a : intAd F) (ha : (a : 𝔸) = afsplitI v p) (c : intAd F) : IsUnit (1 + a * c) := by
  have h1 : Valued.v (1 + (p : v.adicCompletion F) * (c : 𝔸) v) = 1 := by
    apply Valuation.map_one_add_of_lt
    rw [Valuation.map_mul, val_nat]
    exact mul_lt_one_of_lt_of_le ((v.valuation_lt_one_iff_mem _).2 hp)
      ((HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).1 (c.2 v))
  have h0 : 1 + (p : v.adicCompletion F) * (c : 𝔸) v ≠ 0 := fun h => by
    rw [h, map_zero] at h1; exact zero_ne_one h1
  refine IsUnit.of_mul_eq_one ⟨1 - afsplitI v 1 + afsplitI v (1 + (p : v.adicCompletion F) * (c : 𝔸) v)⁻¹,
    add_mem (sub_mem (one_mem _) (afsplitI_mem_intAd v _ (one_mem _))) (afsplitI_mem_intAd v _ ?_)⟩ ?_
  · rw [HeightOneSpectrum.mem_adicCompletionIntegers, map_inv₀, h1, inv_one]
  · apply Subtype.ext
    change (1 + (a : 𝔸) * (c : 𝔸)) * _ = 1
    rw [ha]
    ext w
    by_cases h : w = v
    · subst h
      simp only [afsplit_add_apply, afsplit_mul_apply, afsplit_sub_apply, afsplit_one_apply, afsplitI_self,
        sub_self, zero_add, mul_inv_cancel₀ h0]
    · simp only [afsplit_add_apply, afsplit_mul_apply, afsplit_sub_apply, afsplit_one_apply, afsplitI_ne v w h,
        zero_mul, add_zero, sub_zero, mul_one]

def incInt : intAd F →+* 𝒮 :=
  (((Algebra.TensorProduct.includeRight : 𝔸 →ₐ[F] 𝒜) : 𝔸 →+* 𝒜).comp (intAd F).subtype).codRestrict _
    fun y => Subring.subset_closure (Or.inr ⟨y, rfl⟩)

theorem incInt_integral : (incInt (F := F) (E := E)).IsIntegral := by
  rintro ⟨x, hx⟩
  refine Subring.closure_induction
    (p := fun x hx => (incInt (F := F) (E := E)).IsIntegralElem ⟨x, hx⟩) ?_ ?_ ?_ ?_ ?_ ?_ hx
  · rintro x (⟨⟨e, ⟨b, rfl⟩⟩, rfl⟩ | ⟨y, rfl⟩)
    · let ψ : 𝓞 E →+* 𝒮 := (RingHom.comp ιA (algebraMap (𝓞 E) E)).codRestrict _
        fun y => Subring.subset_closure (Or.inl ⟨⟨_, ⟨y, rfl⟩⟩, rfl⟩)
      have h : IsIntegral ℤ (ψ b) := map_isIntegral_int ψ (Algebra.IsIntegral.isIntegral b)
      letI := (incInt (F := F) (E := E)).toAlgebra
      exact h.tower_top (A := intAd F)
    · exact RingHom.isIntegralElem_map (incInt (F := F) (E := E)) (x := y)
  · exact RingHom.isIntegralElem_zero _
  · exact RingHom.isIntegralElem_one _
  · intro x y _ _ hx hy; exact hx.add _ hy
  · intro x _ hx; exact hx.neg _
  · intro x y _ _ hx hy; exact hx.mul _ hy

theorem eps_mul_nat (v : HeightOneSpectrum (𝓞 F)) (p : ℕ) :
    afsplitEps E v * (p : 𝒜) = (1 : E) ⊗ₜ[F] afsplitI v p := by
  rw [← afsplit_decomp, map_natCast, ← afsplitIE_tmul]
  congr 1
  exact (map_natCast (Algebra.TensorProduct.includeRight :
    v.adicCompletion F →ₐ[F] E ⊗[F] v.adicCompletion F) p).symm

theorem one_sub_eps (v : HeightOneSpectrum (𝓞 F)) (p : ℕ) (hp : p ≠ 0)
    (hv : ∀ w : HeightOneSpectrum (𝓞 F), (p : 𝓞 F) ∈ w.asIdeal → w = v) (k : ℕ) :
    ∃ t ∈ 𝒮, 1 - afsplitEps E v = (p : 𝒜) ^ k * t := by
  have h1 : (1 - afsplitI v 1) * algebraMap F 𝔸 (p : F)⁻¹ ∈ intAd F := by
    intro w
    by_cases h : w = v
    · subst h
      simp only [afsplit_mul_apply, afsplit_sub_apply, afsplit_one_apply, afsplitI_self, sub_self, zero_mul]
      exact zero_mem _
    · simp only [afsplit_mul_apply, afsplit_sub_apply, afsplit_one_apply, afsplitI_ne v w h, sub_zero, one_mul]
      change algebraMap F (w.adicCompletion F) (p : F)⁻¹ ∈ _
      have : w.valuation F (algebraMap (𝓞 F) F p) = 1 :=
        le_antisymm (w.valuation_le_one _) (not_lt.1 fun h' => h (hv w ((w.valuation_lt_one_iff_mem _).1 h')))
      rw [HeightOneSpectrum.mem_adicCompletionIntegers, map_inv₀, map_inv₀, map_natCast (algebraMap F _), val_nat, this,
        inv_one]
  have h2 : (p : 𝒜) * (incInt (E := E) ⟨_, h1⟩ : 𝒜) = 1 - afsplitEps E v := by
    change (p : 𝒜) * (Algebra.TensorProduct.includeRight : 𝔸 →ₐ[F] 𝒜) _ = _
    rw [← map_natCast (Algebra.TensorProduct.includeRight : 𝔸 →ₐ[F] 𝒜), ← map_mul]
    change (Algebra.TensorProduct.includeRight : 𝔸 →ₐ[F] 𝒜)
      ((p : 𝔸) * ((1 - afsplitI v 1) * algebraMap F 𝔸 (p : F)⁻¹)) = _
    rw [mul_left_comm, ← map_natCast (algebraMap F 𝔸), ← map_mul, mul_inv_cancel₀ (Nat.cast_ne_zero.2 hp),
      map_one (algebraMap F 𝔸), mul_one, map_sub, map_one]
    rfl
  refine ⟨(incInt (E := E) ⟨_, h1⟩ : 𝒜) ^ k * (1 - afsplitEps E v),
    mul_mem (pow_mem (Subtype.property _) _) (sub_mem (one_mem _) (afsplit_eps_int v)), ?_⟩
  rw [← mul_assoc, ← mul_pow, h2, ← pow_succ]
  exact (IsIdempotentElem.pow_succ_eq k (afsplit_om_idem v)).symm

theorem zero_at (v : HeightOneSpectrum (𝓞 F)) (p : ℕ) (hp : p.Prime)
    (hv : ∀ w : HeightOneSpectrum (𝓞 F), (p : 𝓞 F) ∈ w.asIdeal → w = v) (x : 𝒜) (k : ℕ) :
    ∃ m : ℕ, 0 < m ∧ Nat.Coprime m p ∧ ∃ s ∈ 𝒮, (m : 𝒜) * ((1 - afsplitEps E v) * x) = (p : 𝒜) ^ k * s := by
  obtain ⟨M, hM, h⟩ := denom x
  obtain ⟨a, m, hm, rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd hM.ne' p hp.ne_one
  obtain ⟨t, ht, e⟩ := one_sub_eps (E := E) v p hp.ne_zero hv (k + a)
  refine ⟨m, Nat.pos_of_ne_zero (by rintro rfl; exact hm (dvd_zero _)),
    ((Nat.Prime.coprime_iff_not_dvd hp).2 hm).symm, t * _, mul_mem ht h, ?_⟩
  rw [e]; push_cast; ring

theorem exists_rat (c : E →ₐ[F] E) (hc : ∀ x, c (c x) = x) (hne : ∃ z, c z ≠ z)
    (v : HeightOneSpectrum (𝓞 F)) (p : ℕ) (hp : 0 < p) (hpv : (p : 𝓞 F) ∈ v.asIdeal) {n : ℕ}
    (g : Matrix (Fin n) (Fin n) 𝒜) (hg : (g.map (sigR c 𝔸))ᵀ * g = 1) :
    ∃ γ : Matrix (Fin n) (Fin n) E, γ * (γ.map c)ᵀ = 1 ∧
      ∀ i j, afsplitEps E v * (γ.map ιA * g) i j ∈ 𝒮 := by
  have hσσ : ∀ x, sigR c 𝔸 (sigR c 𝔸 x) = x := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul a y => simp [sigR, hc]
    | add x y hx hy => rw [map_add, map_add, hx, hy]
  have h1 : (1 : Matrix (Fin n) (Fin n) E).map ιA = 1 := Matrix.map_one _ (map_zero _) (map_one _)
  haveI : Nontrivial (E ⊗[F] v.adicCompletion F) :=
    (Algebra.TensorProduct.includeRight_injective (R := F) (A := E) (B := v.adicCompletion F)
      (algebraMap F E).injective).nontrivial
  haveI : IsArtinianRing (E ⊗[F] v.adicCompletion F) := by
    haveI : IsArtinianRing (v.adicCompletion F ⊗[F] E) := IsArtinianRing.of_finite (v.adicCompletion F) _
    exact (Algebra.TensorProduct.comm F (v.adicCompletion F) E).surjective.isArtinianRing
  set h := (g.map (sigR c 𝔸))ᵀ with hh
  obtain ⟨lam, ⟨hl1, hl2⟩, hu⟩ := exists_unit_det (inclE (F := F) (E := E) (v.adicCompletion F))
    (h.map (prV (E := E) v)) _ (normOne_infinite (c : E →+* E) hc hne)
  have hu' : IsUnit (1 + ιA lam • (afsplitEps E v • h +
      (1 - afsplitEps E v) • (1 : Matrix (Fin n) (Fin n) 𝒜))).det := by
    have e : 1 + ιA lam • (afsplitEps E v • h + (1 - afsplitEps E v) • (1 : Matrix (Fin n) (Fin n) 𝒜)) =
        afsplitC v (1 + inclE (F := F) (E := E) (v.adicCompletion F) lam • h.map (prV (E := E) v))
          (ιA (1 + lam) • 1) := by
      have e1 : 1 + inclE (F := F) (E := E) (v.adicCompletion F) lam • h.map (prV (E := E) v) =
          (1 + ιA lam • h).map (prV (E := E) v) := by
        rw [Matrix.map_add _ (map_add _), Matrix.map_one _ (map_zero _) (map_one _),
          GlobalTheory.UnRep.WeakApprox.map_smul'', afsplit_prV_inclE]
      ext i j
      rw [e1, afsplitC_apply, Matrix.map_apply, afsplit_decomp, map_add, map_one]
      simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
      ring
    rw [e]
    refine Matrix.isUnit_det_of_right_inverse (B := afsplitC v
      (1 + inclE (F := F) (E := E) (v.adicCompletion F) lam • h.map (prV (E := E) v))⁻¹ (ιA (1 + lam)⁻¹ • 1)) ?_
    rw [afsplitC_mul, Matrix.mul_nonsing_inv _ hu, Matrix.smul_mul, Matrix.mul_smul, smul_smul, ← map_mul,
      mul_inv_cancel₀ hl2, map_one, one_smul, mul_one, afsplitC_one]
  obtain ⟨γ, hγ, X, hX, e⟩ := GlobalTheory.UnRep.WeakApprox.core ιA (c : E →+* E) (sigR c 𝔸) (csScale_sigR_incl c) hc hσσ
    (1 : Matrix (Fin n) (Fin n) E)
    (by rw [Matrix.map_one _ (map_zero _) (map_one _), Matrix.transpose_one]) (by simp) two_ne_zero
    (matIn 𝒮 n)
    (fun M => by
      choose m hm0 hm using fun ij : Fin n × Fin n => denom (M ij.1 ij.2)
      refine ⟨∏ ij, m ij, Finset.prod_pos fun ij _ => hm0 ij, fun i j => ?_⟩
      rw [Matrix.smul_apply, nsmul_eq_mul, ← Finset.prod_erase_mul _ _ (Finset.mem_univ (i, j)), Nat.cast_mul,
        mul_assoc]
      exact mul_mem (natCast_mem _ _) (hm (i, j)))
    (afsplitEps E v) (afsplit_eps_idem v) (afsplit_sigR_eps c v)
    (fun h0 => by
      have := afsplit_prV_eps (E := E) v
      rw [h0, map_zero] at this
      exact zero_ne_one this)
    (fun X hX i j => mul_mem (afsplit_eps_int v) (hX i j)) p hp
    (fun X hX => by
      let a : intAd F := ⟨afsplitI v p, afsplitI_mem_intAd v _ (natCast_mem _ _)⟩
      obtain ⟨W, hW, e⟩ := mat_inv 𝒮 (incInt a)
        (unit_of_integral _ incInt_integral a (unit_intAd v p hpv a rfl)) X hX
      refine ⟨W, hW, ?_⟩
      rw [← Nat.cast_smul_eq_nsmul 𝒜, smul_smul, eps_mul_nat]
      exact e)
    (fun M D hD => by
      choose y o ho hyo using fun i j => approx (M i j) D hD
      refine ⟨Matrix.of y, Matrix.of o - ((Matrix.of o).map (sigR c 𝔸))ᵀ,
        fun i j => sub_mem (ho i j) (csScale_sigR_mem c (ho j i)), ?_⟩
      rw [h1, inv_one, one_mul, mul_one, one_mul, mul_one]
      ext i j
      simp only [Matrix.sub_apply, Matrix.transpose_apply, Matrix.map_apply, Matrix.of_apply,
        Matrix.smul_apply, nsmul_eq_mul]
      rw [hyo i j, hyo j i, map_add, map_mul, map_natCast]
      ring)
    g h hg
    (by
      have e2 : h.map (sigR c 𝔸) = gᵀ := by ext i j; exact hσσ _
      rw [h1, mul_one, e2, ← Matrix.transpose_mul, mul_eq_one_comm.1 hg, Matrix.transpose_one])
    lam hl1 hu' 1 one_pos
  refine ⟨γ, ?_, fun i j => ?_⟩
  · rw [mul_one] at hγ
    have := congrArg Matrix.transpose (mul_eq_one_comm.1 hγ)
    rw [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.transpose_one] at this
    exact this
  · have e1 := congrFun (congrFun e i) j
    rw [one_smul, Matrix.smul_apply, Matrix.sub_apply, smul_eq_mul, mul_sub, sub_eq_iff_eq_add] at e1
    rw [e1]
    exact add_mem (hX i j) (mul_mem (afsplit_eps_int v) (afsplit_one_mem _ i j))

theorem exists_int (c : E →ₐ[F] E) (v : HeightOneSpectrum (𝓞 F)) {n : ℕ} (h : GL (Fin n) 𝒜)
    (hh : h ∈ UPts c (1 : Matrix (Fin n) (Fin n) E) 𝔸)
    (hinv : ((h⁻¹ : GL (Fin n) 𝒜) : Matrix (Fin n) (Fin n) 𝒜) = ((h : Matrix (Fin n) (Fin n) 𝒜).map (sigR c 𝔸))ᵀ)
    (hi : ∀ i j, afsplitEps E v * (h : Matrix (Fin n) (Fin n) 𝒜) i j ∈ 𝒮) :
    ∃ k ∈ UPts c (1 : Matrix (Fin n) (Fin n) E) 𝔸,
      (∀ i j, (k : Matrix (Fin n) (Fin n) 𝒜) i j ∈ 𝒮 ∧
        ((k⁻¹ : GL (Fin n) 𝒜) : Matrix (Fin n) (Fin n) 𝒜) i j ∈ 𝒮) ∧
      ∀ i j, ((h * k : GL (Fin n) 𝒜) : Matrix (Fin n) (Fin n) 𝒜) i j - (1 : Matrix (Fin n) (Fin n) 𝒜) i j =
        (1 - afsplitEps E v) * ((h : Matrix (Fin n) (Fin n) 𝒜) i j - (1 : Matrix (Fin n) (Fin n) 𝒜) i j) := by
  have ho : ∀ i j, (1 - afsplitEps E v) * (1 : Matrix (Fin n) (Fin n) 𝒜) i j ∈ 𝒮 := fun i j =>
    mul_mem (sub_mem (one_mem _) (afsplit_eps_int v)) (afsplit_one_mem _ i j)
  refine ⟨afsplitU v (bc (prV (E := E) v) h⁻¹) 1,
    afsplitU_mem v c _ _ _ (afsplit_bc_mem c _ v _ (inv_mem hh)) (one_mem _), fun i j => ⟨?_, ?_⟩, fun i j => ?_⟩
  · rw [afsplitU_coe, afsplitC_apply, afsplit_coe_bc_prV, Matrix.map_apply, afsplit_decomp, hinv,
      Matrix.transpose_apply, Matrix.map_apply]
    refine add_mem ?_ (ho i j)
    have := csScale_sigR_mem c (hi j i)
    rwa [map_mul, afsplit_sigR_eps] at this
  · rw [afsplitU_inv_coe, ← map_inv, inv_inv, inv_one, afsplitC_apply, afsplit_coe_bc_prV, Matrix.map_apply,
      afsplit_decomp]
    exact add_mem (hi i j) (ho i j)
  · have : h * afsplitU v (bc (prV (E := E) v) h⁻¹) 1 = afsplitU v 1 h := by
      have e := afsplitU_mul v (bc (prV (E := E) v) h) (bc (prV (E := E) v) h⁻¹) h 1
      rw [← map_mul, mul_inv_cancel, map_one, mul_one] at e
      rw [e]
      congr 1
      exact (Units.ext (afsplitC_decomp v (h : Matrix (Fin n) (Fin n) 𝒜))).symm
    rw [this, afsplitU_coe, afsplitC_apply, Units.val_one, ← Matrix.map_apply (f := afsplitIE v),
      afsplit_one_map, Matrix.smul_apply, smul_eq_mul]
    ring

end Ad

theorem exists_place (p : ℕ) (hp : p.Prime) : ∃ v : HeightOneSpectrum (𝓞 ℚ), (p : 𝓞 ℚ) ∈ v.asIdeal ∧
    ∀ w : HeightOneSpectrum (𝓞 ℚ), (p : 𝓞 ℚ) ∈ w.asIdeal → w = v := by
  have h1 : Prime (p : 𝓞 ℚ) := by
    rw [← MulEquiv.prime_iff Rat.ringOfIntegersEquiv, map_natCast]
    exact Nat.prime_iff_prime_int.1 hp
  let v : HeightOneSpectrum (𝓞 ℚ) := ⟨Ideal.span {(p : 𝓞 ℚ)}, (Ideal.span_singleton_prime h1.ne_zero).2 h1,
    by rw [Ne, Ideal.span_singleton_eq_bot]; exact h1.ne_zero⟩
  refine ⟨v, Ideal.mem_span_singleton_self _, fun w hw => HeightOneSpectrum.ext ?_⟩
  exact (v.isMaximal.eq_of_le w.isPrime.ne_top ((Ideal.span_singleton_le_iff_mem _).2 hw)).symm

end GlobalTheory.NormSum.RepAt

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators

open GlobalTheory.NormSum.RepAt GlobalTheory.NormSum.PtsMem in

theorem GlobalTheory.NormSum.exists_rep_trivial_at : ∀ D : D7, oddRep D := by
  intro D N p hp g
  obtain ⟨v, hv, hw⟩ := exists_place p hp
  have hcc : ∀ x, D.host.conj (D.host.conj x) = x := fun x =>
    D.host.φ₀.injective (by
      have h1 := D.host.conjE_apply D.host.φ₀ (D.host.conj x)
      have h2 := D.host.conjE_apply D.host.φ₀ x
      exact h1.trans (by rw [show D.host.φ₀ (D.host.conj x) = _ from h2, Complex.conj_conj]))
  obtain ⟨γ, hγ, hi⟩ := exists_rat (F := ℚ) (D.host.conj : D.host.E →ₐ[ℚ] D.host.E) hcc
    (Formalism.MainNotions.ModuliIntegralCharts.H1.ConjugateMinimaInstance.conj_ne D) v p hp.pos hv _ ((mem_GA D _).1 g.2)
  obtain ⟨γA, hγA⟩ := exists_isRat D γ hγ
  obtain ⟨k, hk, hint, htriv⟩ := exists_int (F := ℚ) (D.host.conj : D.host.E →ₐ[ℚ] D.host.E) v
    ((γA * g : GA D N) : GL (Fin N) (AE D)) (γA * g).2
    (Units.inv_eq_of_mul_eq_one_left ((mem_GA D _).1 (γA * g).2))
    (fun i j => by
      rw [Subgroup.coe_mul, Units.val_mul, show ((γA : GL (Fin N) (AE D)) : Matrix (Fin N) (Fin N) (AE D)) = _ from hγA]
      exact hi i j)
  refine ⟨γA, ⟨k, hk⟩, γ, hγA, hint, fun i j l => ?_⟩
  have := zero_at (F := ℚ) v p hp hw
    ((((γA * g : GA D N) : GL (Fin N) (AE D)) : Matrix (Fin N) (Fin N) (AE D)) i j -
      (1 : Matrix (Fin N) (Fin N) (AE D)) i j) l
  rw [← htriv i j] at this
  exact this
