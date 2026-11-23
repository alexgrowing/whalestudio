import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Landherr₂.ExistsNormTensor
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.MemIffForallMemLocalizeRingOfIntegers
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsEqTransposeMulMapOfIdempotent
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsUniqueIdeleOfLinearEquivQuotientLocal
import Development.AbelianVarietyTheory.Proofs.HermitianTraceForms.TraceFormDualOneTraceFormDual
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsAbsoluteValueOfIsDiscreteValuationRing

open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum IsLocalRing
open scoped Matrix TensorProduct nonZeroDivisors ComplexConjugate
open ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.LocalLattice

noncomputable section

namespace GlobalTheory.SelfDualGenus

section Completion

variable {K : Type} [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))

theorem isAdicComplete_adicCompletionIntegers :
    IsAdicComplete (maximalIdeal (v.adicCompletionIntegers K)) (v.adicCompletionIntegers K) := by
  refine NormIntegers.isAdicComplete_of_fg (C := v.adicCompletion K) ⟨?_, ?_, ?_⟩
    (IsNoetherian.noetherian _) (maximalIdeal.isMaximal _).ne_top
  · exact FaithfulSMul.algebraMap_injective _ _
  · intro x
    have : ‖(x : v.adicCompletion K)‖ ≤ 1 := Valued.toNormedField.norm_le_one_iff.2 x.2
    exact_mod_cast this
  · intro x hx
    have : ‖x‖ ≤ 1 := by exact_mod_cast hx
    exact ⟨⟨x, Valued.toNormedField.norm_le_one_iff.1 this⟩, rfl⟩

theorem isUnit_algebraMap_iff (s : 𝓞 K) :
    IsUnit (algebraMap (𝓞 K) (v.adicCompletionIntegers K) s) ↔ s ∉ v.asIdeal := by
  rw [adicCompletionIntegers.isUnit_iff_valued_eq_one, algebraMap_adicCompletionIntegers_apply,
    valuedAdicCompletion_eq_valuation', valuation_eq_one_iff_notMem]

theorem finite_residueField_adicCompletionIntegers :
    Finite (ResidueField (v.adicCompletionIntegers K)) := by
  let f : 𝓞 K →+* ResidueField (v.adicCompletionIntegers K) :=
    (residue _).comp (algebraMap (𝓞 K) (v.adicCompletionIntegers K))
  have hker : ∀ s ∈ v.asIdeal, f s = 0 := fun s hs => by
    change residue _ _ = 0
    rw [residue_eq_zero_iff, mem_maximalIdeal, mem_nonunits_iff, isUnit_algebraMap_iff]
    exact fun h => h hs
  haveI : Finite (𝓞 K ⧸ v.asIdeal) := v.asIdeal.finiteQuotientOfFreeOfNeBot v.ne_bot
  refine Finite.of_surjective (Ideal.Quotient.lift v.asIdeal f hker) fun y => ?_
  obtain ⟨y, rfl⟩ := residue_surjective y
  obtain ⟨s, hs⟩ := Idele.exists_valued_sub_le v (a := (y : v.adicCompletion K)) y.2 1
  refine ⟨Ideal.Quotient.mk _ s, ?_⟩
  rw [Ideal.Quotient.lift_mk]
  change residue _ _ = _
  rw [eq_comm, ← sub_eq_zero, ← map_sub, residue_eq_zero_iff, mem_maximalIdeal, mem_nonunits_iff,
    adicCompletionIntegers.isUnit_iff_valued_eq_one]
  intro h
  have h' : Valued.v ((y : v.adicCompletion K) -
      algebraMap K (v.adicCompletion K) (algebraMap (𝓞 K) K s)) = 1 := h
  rw [h', ← WithZero.exp_zero, WithZero.exp_le_exp] at hs
  omega

end Completion

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

section LocalAlgebra

variable (v : HeightOneSpectrum (𝓞 (maximalRealSubfield E)))

abbrev LocAlg : Type := v.adicCompletion (maximalRealSubfield E) ⊗[(maximalRealSubfield E)] E

def locEmb : E →+* LocAlg v :=
  (Algebra.TensorProduct.includeRight : E →ₐ[(maximalRealSubfield E)] LocAlg v)

def locConj : LocAlg v →+* LocAlg v :=
  (Algebra.TensorProduct.map (AlgHom.id (v.adicCompletion (maximalRealSubfield E)) (v.adicCompletion (maximalRealSubfield E)))
    (IsCMField.complexConj E).toAlgHom : LocAlg v →ₐ[v.adicCompletion (maximalRealSubfield E)] LocAlg v)

theorem locEmb_apply (x : E) : locEmb v x = 1 ⊗ₜ x := rfl

theorem locConj_tmul (a : v.adicCompletion (maximalRealSubfield E)) (x : E) : locConj v (a ⊗ₜ x) = a ⊗ₜ cc x := rfl

theorem locConj_locEmb (x : E) : locConj v (locEmb v x) = locEmb v (cc x) := rfl

theorem locConj_algebraMap (a : v.adicCompletion (maximalRealSubfield E)) :
    locConj v (algebraMap _ (LocAlg v) a) = algebraMap _ (LocAlg v) a :=
  AlgHom.commutes (Algebra.TensorProduct.map (AlgHom.id (v.adicCompletion (maximalRealSubfield E)) (v.adicCompletion (maximalRealSubfield E)))
    (IsCMField.complexConj E).toAlgHom) a

theorem locConj_locConj (z : LocAlg v) : locConj v (locConj v z) = z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a x => simp [locConj_tmul, cc]
  | add x y hx hy => rw [map_add, map_add, hx, hy]

theorem locEmb_coe (a : (maximalRealSubfield E)) :
    locEmb v (a : E) = algebraMap (v.adicCompletion (maximalRealSubfield E)) (LocAlg v) (algebraMap (maximalRealSubfield E) _ a) := by
  rw [← IsScalarTower.algebraMap_apply]
  exact (Algebra.TensorProduct.algebraMap_apply' a).symm

theorem locEmb_algebraMap (s : 𝓞 (maximalRealSubfield E)) :
    locEmb v (algebraMap (𝓞 (maximalRealSubfield E)) (𝓞 E) s : E) = algebraMap (v.adicCompletionIntegers (maximalRealSubfield E)) (LocAlg v)
      (algebraMap (𝓞 (maximalRealSubfield E)) _ s) :=
  locEmb_coe v (s : (maximalRealSubfield E))

theorem algebraMap_locAlg_injective :
    Function.Injective (algebraMap (v.adicCompletion (maximalRealSubfield E)) (LocAlg v)) :=
  (algebraMap (v.adicCompletion (maximalRealSubfield E)) (LocAlg v)).injective

theorem exists_coord {θ : E} (h0 : θ ≠ 0) (hθ : cc θ = -θ) (z : LocAlg v) :
    ∃ p q : v.adicCompletion (maximalRealSubfield E),
      z = algebraMap _ (LocAlg v) p + algebraMap _ (LocAlg v) q * locEmb v θ := by
  obtain ⟨b, hb0, hb1⟩ := Published.exists_basis_one_imaginary h0 hθ
  let B := Algebra.TensorProduct.basis (v.adicCompletion (maximalRealSubfield E)) b
  refine ⟨B.repr z 0, B.repr z 1, ?_⟩
  conv_lhs => rw [← B.sum_repr z, Fin.sum_univ_two]
  rw [Algebra.smul_def, Algebra.smul_def, Algebra.TensorProduct.basis_apply,
    Algebra.TensorProduct.basis_apply, hb0, hb1, ← Algebra.TensorProduct.one_def, mul_one]
  rfl

theorem exists_of_locConj_eq {z : LocAlg v} (hz : locConj v z = z) :
    ∃ a : v.adicCompletion (maximalRealSubfield E), algebraMap _ (LocAlg v) a = z := by
  obtain ⟨θ, h0, hθ⟩ := Published.exists_cc_eq_neg E
  obtain ⟨p, q, rfl⟩ := exists_coord v h0 hθ z
  rw [map_add, map_mul, locConj_algebraMap, locConj_algebraMap, locConj_locEmb, hθ, map_neg] at hz
  have hu : IsUnit (locEmb v (2 * θ)) := (IsUnit.mk0 _ (mul_ne_zero two_ne_zero h0)).map _
  have : algebraMap _ (LocAlg v) q = 0 := by
    rw [← hu.mul_left_eq_zero, map_mul, map_ofNat]
    linear_combination -hz
  exact ⟨p, by rw [this, zero_mul, add_zero]⟩

def locOrder : Subalgebra (v.adicCompletionIntegers (maximalRealSubfield E)) (LocAlg v) :=
  Algebra.adjoin _ (Set.range fun a : 𝓞 E => locEmb v a)

theorem locEmb_mem_locOrder (a : 𝓞 E) : locEmb v a ∈ locOrder v :=
  Algebra.subset_adjoin ⟨a, rfl⟩

theorem locConj_algebraMap' (a : v.adicCompletionIntegers (maximalRealSubfield E)) :
    locConj v (algebraMap _ (LocAlg v) a) = algebraMap _ (LocAlg v) a :=
  locConj_algebraMap v (a : v.adicCompletion (maximalRealSubfield E))

theorem locConj_mem {z : LocAlg v} (hz : z ∈ locOrder v) : locConj v z ∈ locOrder v := by
  induction hz using Algebra.adjoin_induction with
  | mem x hx =>
    obtain ⟨a, rfl⟩ := hx
    exact locEmb_mem_locOrder v (IsCMField.ringOfIntegersComplexConj E a)
  | algebraMap a => rw [locConj_algebraMap']; exact Subalgebra.algebraMap_mem _ a
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | mul x y _ _ hx hy => rw [map_mul]; exact mul_mem hx hy

theorem isIntegral_of_mem_locOrder {z : LocAlg v} (hz : z ∈ locOrder v) :
    IsIntegral (v.adicCompletionIntegers (maximalRealSubfield E)) z := by
  refine (show locOrder v ≤ integralClosure _ _ from Algebra.adjoin_le ?_) hz
  rintro _ ⟨a, rfl⟩
  exact a.isIntegral_coe.map_of_comp_eq (Int.castRingHom _) (locEmb v) (RingHom.ext_int _ _)

def locOrderConj : locOrder v →+* locOrder v :=
  (locConj v).restrict (locOrder v).toSubring (locOrder v).toSubring fun _ => locConj_mem v

theorem coe_locOrderConj (z : locOrder v) : (locOrderConj v z : LocAlg v) = locConj v z := rfl

theorem exists_of_mem_locOrder_of_locConj_eq {z : LocAlg v} (hz : z ∈ locOrder v)
    (hc : locConj v z = z) :
    ∃ a : v.adicCompletionIntegers (maximalRealSubfield E), algebraMap _ (LocAlg v) a = z := by
  obtain ⟨a, rfl⟩ := exists_of_locConj_eq v hc
  have hi : IsIntegral (v.adicCompletionIntegers (maximalRealSubfield E)) a :=
    (isIntegral_algHom_iff (IsScalarTower.toAlgHom (v.adicCompletionIntegers (maximalRealSubfield E))
      (v.adicCompletion (maximalRealSubfield E)) (LocAlg v)) (algebraMap_locAlg_injective v)).1
      (isIntegral_of_mem_locOrder v hz)
  obtain ⟨b, rfl⟩ := IsIntegrallyClosed.isIntegral_iff.1 hi
  exact ⟨b, rfl⟩

theorem exists_sub_conj_notMem [Algebra.Unramified (𝓞 (maximalRealSubfield E)) (𝓞 E)] (w : Ideal (𝓞 E))
    (hw : w ≠ ⊤) : ∃ x : 𝓞 E, x - IsCMField.ringOfIntegersComplexConj E x ∉ w := by
  by_contra h
  push Not at h
  have key : (IsCMField.ringOfIntegersComplexConj E).toAlgHom = AlgHom.id (𝓞 (maximalRealSubfield E)) (𝓞 E) :=
    Algebra.FormallyUnramified.ext_of_iInf w (Ideal.iInf_pow_eq_bot_of_isDomain w hw) fun x => by
      rw [eq_comm, Ideal.Quotient.eq]; exact h x
  refine IsCMField.complexConj_ne_one E (AlgEquiv.ext fun x => ?_)
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := 𝓞 E) x
  have e : ∀ a : 𝓞 E, IsCMField.complexConj E (algebraMap (𝓞 E) E a) = algebraMap (𝓞 E) E a :=
    fun a => congrArg (algebraMap (𝓞 E) E) (DFunLike.congr_fun key a)
  rw [map_div₀, e, e]; rfl

theorem exists_isUnit_sub_locOrderConj [Algebra.Unramified (𝓞 (maximalRealSubfield E)) (𝓞 E)] :
    ∃ ω : locOrder v, IsUnit (ω - locOrderConj v ω) := by
  obtain ⟨w, hw, hwv⟩ := Ideal.exists_ideal_over_prime_of_isIntegral_of_isDomain
    (S := 𝓞 E) v.asIdeal (by
      rw [(RingHom.injective_iff_ker_eq_bot (algebraMap (𝓞 (maximalRealSubfield E)) (𝓞 E))).1
        (FaithfulSMul.algebraMap_injective _ _)]
      exact bot_le)
  obtain ⟨x, hx⟩ := exists_sub_conj_notMem w hw.ne_top
  set δ := x - IsCMField.ringOfIntegersComplexConj E x with hδ
  have hcδ : IsCMField.ringOfIntegersComplexConj E δ = -δ := by
    ext; simp [hδ]
  obtain ⟨s, hs⟩ := (IsCMField.ringOfIntegersComplexConj_eq_self_iff E (δ * δ)).1
    (by rw [map_mul, hcδ]; ring)
  have hsv : s ∉ v.asIdeal := fun h => by
    rw [← hwv, Ideal.mem_comap, hs] at h
    exact hx ((hw.mem_or_mem h).elim id id)
  refine ⟨⟨_, locEmb_mem_locOrder v x⟩, isUnit_of_mul_isUnit_left
    (y := ⟨_, locEmb_mem_locOrder v δ⟩) ?_⟩
  convert ((isUnit_algebraMap_iff v s).2 hsv).map (algebraMap _ (locOrder v))
  apply Subtype.ext
  change (locEmb v x - locEmb v (cc x)) * locEmb v δ = algebraMap _ (LocAlg v) _
  rw [← locEmb_algebraMap, hs, ← map_sub, ← map_mul]
  rfl

end LocalAlgebra

section SemiLocal

variable (v : HeightOneSpectrum (𝓞 (maximalRealSubfield E)))

theorem algebraMapSubmonoid_le :
    Algebra.algebraMapSubmonoid (𝓞 E) v.asIdeal.primeCompl ≤ (𝓞 E)⁰ :=
  algebraMapSubmonoid_le_nonZeroDivisors_of_faithfulSMul _ v.asIdeal.primeCompl_le_nonZeroDivisors

def semiLoc : Subalgebra (𝓞 E) E :=
  Localization.subalgebra.ofField E (Algebra.algebraMapSubmonoid (𝓞 E) v.asIdeal.primeCompl)
    (algebraMapSubmonoid_le v)

instance isLocalization_semiLoc :
    IsLocalization (Algebra.algebraMapSubmonoid (𝓞 E) v.asIdeal.primeCompl) (semiLoc v) :=
  Localization.subalgebra.isLocalization_ofField E _ _

instance isFractionRing_semiLoc : IsFractionRing (semiLoc v) E :=
  Localization.subalgebra.isFractionRing_ofField E _ _

instance isPrincipalIdealRing_semiLoc : IsPrincipalIdealRing (semiLoc v) :=
  haveI : IsDedekindDomain (semiLoc v) :=
    IsLocalization.isDedekindDomain (𝓞 E) (algebraMapSubmonoid_le v) _
  IsDedekindDomain.isPrincipalIdealRing_localization_over_prime (𝓞 E) v.asIdeal v.ne_bot

theorem mem_span_semiLoc_iff {V : Type*} [AddCommGroup V] [Module E V] [Module (𝓞 E) V]
    [IsScalarTower (𝓞 E) E V] (N : Submodule (𝓞 E) V) (x : V) :
    x ∈ Submodule.span (semiLoc v) (N : Set V) ↔
      ∃ s ∉ v.asIdeal, algebraMap (𝓞 (maximalRealSubfield E)) (𝓞 E) s • x ∈ N := by
  rw [mem_span_localization_iff (semiLoc v)
    (Algebra.algebraMapSubmonoid (𝓞 E) v.asIdeal.primeCompl)]
  exact ⟨fun ⟨_, ⟨s, hs, rfl⟩, h⟩ => ⟨s, hs, h⟩, fun ⟨s, hs, h⟩ => ⟨_, ⟨s, hs, rfl⟩, h⟩⟩

theorem mem_semiLoc_iff (z : E) :
    z ∈ semiLoc v ↔ ∃ s ∉ v.asIdeal, IsIntegral ℤ ((algebraMap (𝓞 (maximalRealSubfield E)) (𝓞 E) s : E) * z) := by
  have h := mem_span_semiLoc_iff v (1 : Submodule (𝓞 E) E) z
  simp only [mem_one_ringOfIntegers_iff] at h
  rw [Submodule.one_eq_span, Submodule.span_span_of_tower, Submodule.mem_span_singleton] at h
  refine Iff.trans ⟨fun hz => ⟨⟨z, hz⟩, mul_one z⟩, ?_⟩ h
  rintro ⟨a, rfl⟩
  have : a • (1 : E) = a := mul_one (a : E)
  rw [this]; exact a.2

theorem cc_algebraMap (s : 𝓞 (maximalRealSubfield E)) :
    cc (algebraMap (𝓞 (maximalRealSubfield E)) (𝓞 E) s : E) = algebraMap (𝓞 (maximalRealSubfield E)) (𝓞 E) s :=
  IsCMField.complexConj_apply_eq_self E (s : (maximalRealSubfield E))

theorem cc_mem_semiLoc {z : E} (hz : z ∈ semiLoc v) : cc z ∈ semiLoc v := by
  rw [mem_semiLoc_iff] at hz ⊢
  obtain ⟨s, hs, h⟩ := hz
  refine ⟨s, hs, ?_⟩
  have := isIntegral_cc h
  rwa [HermitianTraceFormVanishing.cc_mul, cc_algebraMap] at this

theorem locEmb_mem_locOrder_iff (z : E) : locEmb v z ∈ locOrder v ↔ z ∈ semiLoc v := by
  rw [mem_semiLoc_iff]
  constructor
  · intro hz
    have real : ∀ y : E, cc y = y → locEmb v y ∈ locOrder v →
        ∃ s ∉ v.asIdeal, IsIntegral ℤ ((algebraMap (𝓞 (maximalRealSubfield E)) (𝓞 E) s : E) * y) := by
      intro y hy hm
      obtain ⟨a, ha⟩ := exists_of_mem_locOrder_of_locConj_eq v hm (by rw [locConj_locEmb, hy])
      let y' : (maximalRealSubfield E) := ⟨y, (IsCMField.complexConj_eq_self_iff E y).1 hy⟩
      have h1 : algebraMap (maximalRealSubfield E) (v.adicCompletion (maximalRealSubfield E)) y' = a :=
        algebraMap_locAlg_injective v ((locEmb_coe v y').symm.trans ha.symm)
      obtain ⟨s, hs, h⟩ := (mem_localRing_iff v y').1
        ((algebraMap_mem_adicCompletionIntegers_iff v y').1 (h1 ▸ a.2))
      exact ⟨s, hs, ((mem_one_ringOfIntegers_iff _).1 h).map_of_comp_eq (RingHom.id ℤ)
        (algebraMap (maximalRealSubfield E) E) (RingHom.ext_int _ _)⟩
    have hc : locEmb v (cc z) ∈ locOrder v := locConj_mem v hz
    have h1 := (mem_semiLoc_iff v _).2 (real (z + cc z) (by simp [cc, add_comm])
      (by rw [map_add]; exact add_mem hz hc))
    have h2 := (mem_semiLoc_iff v _).2 (real (z * cc z) (by simp [cc, mul_comm])
      (by rw [map_mul]; exact mul_mem hz hc))
    have hi : IsIntegral (semiLoc v) z := by
      refine ⟨Polynomial.X ^ 2 - Polynomial.C ⟨_, h1⟩ * Polynomial.X + Polynomial.C ⟨_, h2⟩,
        by monicity!, ?_⟩
      simp only [Polynomial.eval₂_add, Polynomial.eval₂_sub, Polynomial.eval₂_mul,
        Polynomial.eval₂_pow, Polynomial.eval₂_X, Polynomial.eval₂_C]
      change z ^ 2 - (z + cc z) * z + z * cc z = 0
      ring
    obtain ⟨b, hb⟩ := IsIntegrallyClosed.isIntegral_iff.1 hi
    exact (mem_semiLoc_iff v z).1 (hb ▸ b.2)
  · rintro ⟨s, hs, h⟩
    obtain ⟨t, ht⟩ := ((isUnit_algebraMap_iff v s).2 hs).exists_left_inv
    have h1 : locEmb v z = algebraMap _ (LocAlg v) t *
        locEmb v ((algebraMap (𝓞 (maximalRealSubfield E)) (𝓞 E) s : E) * z) := by
      rw [map_mul, locEmb_algebraMap, ← mul_assoc, ← map_mul, ht, map_one, one_mul]
    rw [h1]
    exact mul_mem (Subalgebra.algebraMap_mem _ t) (locEmb_mem_locOrder v ⟨_, h⟩)

theorem exists_frame {L : Submodule (𝓞 E) (Fin r → E)} (hL : ReciprocityTheory.MultiplicativeHeights.IsLattice L) :
    ∃ g : GL (Fin r) E, ∀ x, (∃ s ∉ v.asIdeal, algebraMap (𝓞 (maximalRealSubfield E)) (𝓞 E) s • x ∈ L) ↔
      ∀ i, (((g⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E) *ᵥ x) i ∈ semiLoc v := by
  haveI : Submodule.IsLattice E (Submodule.span (semiLoc v) (L : Set (Fin r → E))) := by
    constructor
    · obtain ⟨s, rfl⟩ := hL.1
      exact ⟨s, (Submodule.span_span_of_tower (𝓞 E) _ _).symm⟩
    · rw [Submodule.span_span_of_tower, hL.2]
  obtain ⟨g, hg⟩ := exists_eq_frameLattice (Submodule.span (semiLoc v) (L : Set (Fin r → E)))
  refine ⟨g, fun x => ?_⟩
  rw [← mem_span_semiLoc_iff, hg, mem_frameLattice_iff_inv]
  exact forall_congr' fun i =>
    Submodule.mem_one.trans ⟨fun ⟨a, ha⟩ => ha ▸ a.2, fun h => ⟨⟨_, h⟩, rfl⟩⟩

theorem exists_generator {𝔟 : FractionalIdeal (𝓞 E)⁰ E} (h𝔟 : 𝔟 ≠ 0) :
    ∃ b : E, b ≠ 0 ∧ ∀ z, (∃ s ∉ v.asIdeal, (algebraMap (𝓞 (maximalRealSubfield E)) (𝓞 E) s : E) * z ∈ 𝔟) ↔
      b⁻¹ * z ∈ semiLoc v := by
  have hfg : (Submodule.span (semiLoc v) ((𝔟 : Submodule (𝓞 E) E) : Set E)).FG := by
    obtain ⟨s, hs⟩ := FractionalIdeal.fg_of_isNoetherianRing le_rfl 𝔟
    exact ⟨s, by rw [← hs, Submodule.span_span_of_tower]⟩
  obtain ⟨b, hb⟩ := (FractionalIdeal.isPrincipal
    (⟨_, FractionalIdeal.isFractional_of_fg hfg⟩ : FractionalIdeal (semiLoc v)⁰ E)).principal
  have hb' : ∀ z, (∃ s ∉ v.asIdeal, (algebraMap (𝓞 (maximalRealSubfield E)) (𝓞 E) s : E) * z ∈ 𝔟) ↔
      ∃ a : semiLoc v, a • b = z := fun z => by
    rw [← Submodule.mem_span_singleton, ← hb]
    exact (mem_span_semiLoc_iff v (𝔟 : Submodule (𝓞 E) E) z).symm
  have hb0 : b ≠ 0 := by
    rintro rfl
    refine h𝔟 (FractionalIdeal.eq_zero_iff.2 fun z hz => ?_)
    obtain ⟨a, ha⟩ := (hb' z).1 ⟨1, (Ideal.ne_top_iff_one _).1 v.isPrime.ne_top, by simpa using hz⟩
    rw [← ha, smul_zero]
  refine ⟨b, hb0, fun z => (hb' z).trans ⟨?_, fun h => ⟨⟨_, h⟩, ?_⟩⟩⟩
  · rintro ⟨a, rfl⟩
    have : b⁻¹ * (a • b) = a := by
      change b⁻¹ * ((a : E) * b) = a
      field_simp
    rw [this]; exact a.2
  · change b⁻¹ * z * b = z
    field_simp

end SemiLocal

section Gram

variable (v : HeightOneSpectrum (𝓞 (maximalRealSubfield E)))

theorem herm_eq_dotProduct (G : Matrix (Fin r) (Fin r) E) (x y : Fin r → E) :
    herm G x y = x ᵥ* G ⬝ᵥ fun i => cc (y i) := by
  simp only [herm, Matrix.vecMul, dotProduct, Finset.sum_mul]
  exact Finset.sum_comm

theorem herm_mulVec (G P : Matrix (Fin r) (Fin r) E) (x y : Fin r → E) :
    herm G (P *ᵥ x) (P *ᵥ y) = herm (Pᵀ * G * P.map cc) x y := by
  have : (fun i => cc ((P *ᵥ y) i)) = P.map cc *ᵥ fun i => cc (y i) :=
    funext fun i => RingHom.map_mulVec (IsCMField.complexConj E : E →+* E) P y i
  rw [herm_eq_dotProduct, herm_eq_dotProduct, this, Matrix.dotProduct_mulVec,
    ← Matrix.vecMul_transpose, Matrix.vecMul_vecMul, Matrix.vecMul_vecMul, Matrix.mul_assoc]

theorem one_notMem : (1 : 𝓞 (maximalRealSubfield E)) ∉ v.asIdeal := (Ideal.ne_top_iff_one _).1 v.isPrime.ne_top

variable {G : Matrix (Fin r) (Fin r) E} {L : Submodule (𝓞 E) (Fin r → E)}
  {𝔟 : FractionalIdeal (𝓞 E)⁰ E} {g : GL (Fin r) E} {b : E}

theorem exists_smul_col_mem
    (hg : ∀ x, (∃ s ∉ v.asIdeal, algebraMap (𝓞 (maximalRealSubfield E)) (𝓞 E) s • x ∈ L) ↔
      ∀ i, (((g⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E) *ᵥ x) i ∈ semiLoc v) (j : Fin r) :
    ∃ s ∉ v.asIdeal, algebraMap (𝓞 (maximalRealSubfield E)) (𝓞 E) s • (fun k => (g : Matrix (Fin r) (Fin r) E) k j) ∈ L := by
  refine (hg _).2 fun i => ?_
  have : (((g⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E) *ᵥ
      (fun k => (g : Matrix (Fin r) (Fin r) E) k j)) i = (1 : Matrix (Fin r) (Fin r) E) i j := by
    rw [← Units.inv_mul g]; rfl
  rw [this, Matrix.one_apply]
  split_ifs
  exacts [one_mem _, zero_mem _]

theorem gram_mem_semiLoc (hmod : ∀ x, x ∈ L ↔ ∀ y ∈ L, herm G x y ∈ 𝔟)
    (hg : ∀ x, (∃ s ∉ v.asIdeal, algebraMap (𝓞 (maximalRealSubfield E)) (𝓞 E) s • x ∈ L) ↔
      ∀ i, (((g⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E) *ᵥ x) i ∈ semiLoc v)
    (hb : ∀ z, (∃ s ∉ v.asIdeal, (algebraMap (𝓞 (maximalRealSubfield E)) (𝓞 E) s : E) * z ∈ 𝔟) ↔ b⁻¹ * z ∈ semiLoc v)
    (i j : Fin r) :
    b⁻¹ * ((g : Matrix (Fin r) (Fin r) E)ᵀ * G * (g : Matrix (Fin r) (Fin r) E).map cc) i j ∈
      semiLoc v := by
  obtain ⟨s, hs, h⟩ := exists_smul_col_mem v hg i
  obtain ⟨s', hs', h'⟩ := exists_smul_col_mem v hg j
  have := (hmod _).1 h _ h'
  rw [← algebraMap_smul E, ← algebraMap_smul E (algebraMap _ (𝓞 E) s'), HermitianTraceFormVanishing.herm_smul_left,
    HermitianTraceFormVanishing.herm_smul_right, Published.herm_col] at this
  refine (hb _).1 ⟨s * s', fun h => (v.isPrime.mem_or_mem h).elim hs hs', ?_⟩
  convert this using 1
  erw [cc_algebraMap]
  simp [mul_assoc]

theorem gram_inv_mem_semiLoc (hd : G.det ≠ 0) (hL : L.FG)
    (hmod : ∀ x, x ∈ L ↔ ∀ y ∈ L, herm G x y ∈ 𝔟)
    (hg : ∀ x, (∃ s ∉ v.asIdeal, algebraMap (𝓞 (maximalRealSubfield E)) (𝓞 E) s • x ∈ L) ↔
      ∀ i, (((g⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E) *ᵥ x) i ∈ semiLoc v) (hb0 : b ≠ 0)
    (hb : ∀ z, (∃ s ∉ v.asIdeal, (algebraMap (𝓞 (maximalRealSubfield E)) (𝓞 E) s : E) * z ∈ 𝔟) ↔ b⁻¹ * z ∈ semiLoc v)
    (i j : Fin r) :
    b * ((g : Matrix (Fin r) (Fin r) E)ᵀ * G * (g : Matrix (Fin r) (Fin r) E).map cc)⁻¹ i j ∈
      semiLoc v := by
  set H := (g : Matrix (Fin r) (Fin r) E)ᵀ * G * (g : Matrix (Fin r) (Fin r) E).map cc with hH
  have hHd : IsUnit H.det := by
    have := g.det_ne_zero
    rw [hH, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, Published.det_map_cc]
    exact (mul_ne_zero (mul_ne_zero this hd) (Published.cc_ne_zero this)).isUnit
  let a : Fin r → E := b • (Pi.single i 1 ᵥ* H⁻¹)
  let x : Fin r → E := (g : Matrix (Fin r) (Fin r) E) *ᵥ a
  have hx : ∀ y, herm G x y =
      b * cc ((((g⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E) *ᵥ y) i) := by
    intro y
    have hy : y = (g : Matrix (Fin r) (Fin r) E) *ᵥ
        (((g⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E) *ᵥ y) := by
      rw [Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec]
    conv_lhs => rw [hy, herm_mulVec, ← hH, HermitianTraceFormVanishing.herm_smul_left, herm_eq_dotProduct,
      Matrix.vecMul_vecMul, Matrix.nonsing_inv_mul _ hHd, Matrix.vecMul_one,
      single_dotProduct, one_mul]
  have hloc : ∀ y ∈ L, ∃ s ∈ v.asIdeal.primeCompl,
      (algebraMap (𝓞 (maximalRealSubfield E)) (𝓞 E) s : E) * herm G x y ∈ 𝔟 := fun y hy => by
    refine (hb _).2 ?_
    rw [hx, inv_mul_cancel_left₀ hb0]
    exact cc_mem_semiLoc v ((hg y).1 ⟨1, one_notMem v, by simpa using hy⟩ i)
  have hmul : ∀ (c : 𝓞 E) {z : E}, z ∈ 𝔟 → (c : E) * z ∈ 𝔟 := fun c z hz =>
    (𝔟 : Submodule (𝓞 E) E).smul_mem c hz
  obtain ⟨t, ht⟩ := hL
  obtain ⟨s, hs, h⟩ := exists_mem_submonoid_forall t.finite_toSet v.asIdeal.primeCompl
    (fun y s => (algebraMap (𝓞 (maximalRealSubfield E)) (𝓞 E) s : E) * herm G x y ∈ 𝔟)
    (fun y s s' h => by
      have := hmul (algebraMap _ (𝓞 E) s') h
      simpa [mul_assoc] using this)
    (fun y hy => hloc y (ht ▸ Submodule.subset_span hy))
  have hsx : algebraMap (𝓞 (maximalRealSubfield E)) (𝓞 E) s • x ∈ L := by
    refine (hmod _).2 fun y hy => ?_
    rw [← algebraMap_smul E, HermitianTraceFormVanishing.herm_smul_left]
    rw [← ht] at hy
    induction hy using Submodule.span_induction with
    | mem y hy => exact h y hy
    | zero => simpa [herm, cc] using 𝔟.zero_mem
    | add y z _ _ hy hz =>
      rw [herm_add_right, mul_add]
      exact (𝔟 : Submodule (𝓞 E) E).add_mem hy hz
    | smul c y _ hy =>
      rw [← algebraMap_smul E, HermitianTraceFormVanishing.herm_smul_right, mul_left_comm]
      exact hmul (IsCMField.ringOfIntegersComplexConj E c) hy
  have := (hg x).1 ⟨s, hs, hsx⟩ j
  rw [Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec] at this
  simpa [a] using this

end Gram

section LocalLattice

variable (v : HeightOneSpectrum (𝓞 (maximalRealSubfield E)))

def locLattice (L : Submodule (𝓞 E) (Fin r → E)) :
    Submodule (v.adicCompletionIntegers (maximalRealSubfield E)) (Fin r → LocAlg v) :=
  Submodule.span _ ((fun x i => locEmb v (x i)) '' (L : Set (Fin r → E)))

variable {L : Submodule (𝓞 E) (Fin r → E)}

theorem mem_locLattice_of_smul_mem {s : 𝓞 (maximalRealSubfield E)} (hs : s ∉ v.asIdeal) {x : Fin r → E}
    (hx : algebraMap (𝓞 (maximalRealSubfield E)) (𝓞 E) s • x ∈ L) : (fun i => locEmb v (x i)) ∈ locLattice v L := by
  obtain ⟨t, ht⟩ := ((isUnit_algebraMap_iff v s).2 hs).exists_left_inv
  have h1 : (fun i => locEmb v (x i)) =
      t • fun i => locEmb v ((algebraMap (𝓞 (maximalRealSubfield E)) (𝓞 E) s • x) i) := by
    funext i
    change _ = t • locEmb v ((algebraMap (𝓞 (maximalRealSubfield E)) (𝓞 E) s : E) * x i)
    rw [map_mul, locEmb_algebraMap, Algebra.smul_def, ← mul_assoc, ← map_mul, ht, map_one, one_mul]
  rw [h1]
  exact Submodule.smul_mem _ t (Submodule.subset_span ⟨_, hx, rfl⟩)

theorem smul_mem_locLattice {z : LocAlg v} (hz : z ∈ locOrder v) {x : Fin r → LocAlg v}
    (hx : x ∈ locLattice v L) : z • x ∈ locLattice v L := by
  induction hz using Algebra.adjoin_induction generalizing x with
  | mem z hz =>
    obtain ⟨a, rfl⟩ := hz
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨y, hy, rfl⟩ := hx
      exact Submodule.subset_span ⟨a • y, L.smul_mem a hy, funext fun i => map_mul (locEmb v) _ _⟩
    | zero => simp
    | add x y _ _ hx hy => rw [smul_add]; exact add_mem hx hy
    | smul c x _ hx => rw [smul_comm]; exact Submodule.smul_mem _ c hx
  | algebraMap a => rw [algebraMap_smul]; exact Submodule.smul_mem _ a hx
  | add y z _ _ hy hz => rw [add_smul]; exact add_mem (hy hx) (hz hx)
  | mul y z _ _ hy hz => rw [mul_smul]; exact hy (hz hx)

theorem mem_locLattice_iff_of_frame {g : GL (Fin r) E}
    (hg : ∀ x, (∃ s ∉ v.asIdeal, algebraMap (𝓞 (maximalRealSubfield E)) (𝓞 E) s • x ∈ L) ↔
      ∀ i, (((g⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E) *ᵥ x) i ∈ semiLoc v)
    (x : Fin r → LocAlg v) :
    x ∈ locLattice v L ↔ ∀ i,
      (((g⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E).map (locEmb v) *ᵥ x) i ∈ locOrder v := by
  constructor
  · intro hx i
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨y, hy, rfl⟩ := hx
      have := (locEmb_mem_locOrder_iff v _).2 ((hg y).1 ⟨1, one_notMem v, by simpa using hy⟩ i)
      rwa [RingHom.map_mulVec] at this
    | zero => simp
    | add x y _ _ hx hy => rw [Matrix.mulVec_add]; exact add_mem hx hy
    | smul c x _ hx => rw [Matrix.mulVec_smul]; exact Subalgebra.smul_mem _ hx c
  · intro hx
    have h1 : x = (g : Matrix (Fin r) (Fin r) E).map (locEmb v) *ᵥ
        (((g⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E).map (locEmb v) *ᵥ x) := by
      rw [Matrix.mulVec_mulVec, ← Matrix.map_mul, Units.mul_inv,
        Matrix.map_one _ (map_zero _) (map_one _), Matrix.one_mulVec]
    rw [h1, Matrix.mulVec_eq_sum]
    refine Submodule.sum_mem _ fun j _ => ?_
    obtain ⟨s, hs, h⟩ := exists_smul_col_mem v hg j
    have := smul_mem_locLattice v (hx j) (mem_locLattice_of_smul_mem v hs h)
    convert this using 1
    funext k
    simp [mul_comm]

theorem locEmb_mem_locLattice_iff (hL : ReciprocityTheory.MultiplicativeHeights.IsLattice L) (x : Fin r → E) :
    (fun i => locEmb v (x i)) ∈ locLattice v L ↔
      ∃ s ∉ v.asIdeal, algebraMap (𝓞 (maximalRealSubfield E)) (𝓞 E) s • x ∈ L := by
  obtain ⟨g, hg⟩ := exists_frame v hL
  rw [mem_locLattice_iff_of_frame v hg, hg]
  refine forall_congr' fun i => ?_
  rw [← locEmb_mem_locOrder_iff, RingHom.map_mulVec]
  rfl

end LocalLattice

theorem mem_iff_forall_mem_locLattice {L : Submodule (𝓞 E) (Fin r → E)}
    (hL : ReciprocityTheory.MultiplicativeHeights.IsLattice L) (x : Fin r → E) :
    x ∈ L ↔ ∀ v : HeightOneSpectrum (𝓞 (maximalRealSubfield E)), (fun i => locEmb v (x i)) ∈ locLattice v L := by
  refine ⟨fun hx v => Submodule.subset_span ⟨x, hx, rfl⟩, fun h => ?_⟩
  refine (mem_iff_forall_mem_localize_ringOfIntegers L x).2 fun w => ?_
  obtain ⟨s, hs, h⟩ := (locEmb_mem_locLattice_iff (w.under (𝓞 (maximalRealSubfield E))) hL x).1 (h _)
  exact (mem_localize_iff w L x).2 ⟨_, hs, h⟩

theorem finite_setOf_locLattice_ne {L L' : Submodule (𝓞 E) (Fin r → E)}
    (hL : ReciprocityTheory.MultiplicativeHeights.IsLattice L) (hL' : ReciprocityTheory.MultiplicativeHeights.IsLattice L') :
    {v : HeightOneSpectrum (𝓞 (maximalRealSubfield E)) | locLattice v L ≠ locLattice v L'}.Finite := by
  have key : ∀ {L L' : Submodule (𝓞 E) (Fin r → E)}, ReciprocityTheory.MultiplicativeHeights.IsLattice L →
      ReciprocityTheory.MultiplicativeHeights.IsLattice L' →
      ∀ᶠ v : HeightOneSpectrum (𝓞 (maximalRealSubfield E)) in Filter.cofinite, locLattice v L ≤ locLattice v L' := by
    intro L L' hL hL'
    obtain ⟨d, hd, h⟩ := exists_smul_le (O := 𝓞 E) hL.1 hL'.2
    have hd0 : d ≠ 0 := nonZeroDivisors.ne_zero hd
    obtain ⟨n, hn⟩ := (IsCMField.ringOfIntegersComplexConj_eq_self_iff E
      (IsCMField.ringOfIntegersComplexConj E d * d)).1 (by ext; simp [mul_comm])
    have hn0 : n ∈ (𝓞 (maximalRealSubfield E))⁰ := mem_nonZeroDivisors_of_ne_zero fun h0 => by
      rw [h0, map_zero, eq_comm, mul_eq_zero, map_eq_zero_iff _ (AlgEquiv.injective _)] at hn
      exact hd0 (hn.elim id id)
    filter_upwards [eventually_notMem hn0] with v hv
    refine Submodule.span_le.2 ?_
    rintro _ ⟨x, hx, rfl⟩
    refine mem_locLattice_of_smul_mem v hv ?_
    rw [hn, mul_smul]
    exact L'.smul_mem _ (h x hx)
  refine Filter.eventually_cofinite.1 ?_
  filter_upwards [key hL hL', key hL' hL] with v h₁ h₂ using le_antisymm h₁ h₂

section NormalForm

variable [Algebra.Unramified (𝓞 (maximalRealSubfield E)) (𝓞 E)] (v : HeightOneSpectrum (𝓞 (maximalRealSubfield E)))

theorem locOrderConj_locOrderConj (z : locOrder v) : locOrderConj v (locOrderConj v z) = z :=
  Subtype.ext (locConj_locConj v z)

theorem mem_range_of_locOrderConj_eq (z : locOrder v) (hz : locOrderConj v z = z) :
    z ∈ (algebraMap (v.adicCompletionIntegers (maximalRealSubfield E)) (locOrder v)).range := by
  obtain ⟨a, ha⟩ := exists_of_mem_locOrder_of_locConj_eq v z.2 (congrArg Subtype.val hz)
  exact ⟨a, Subtype.ext ha⟩

theorem exists_eq_transpose_mul_map_locConj {M N : Matrix (Fin r) (Fin r) (LocAlg v)}
    (hM : ∀ i j, M i j ∈ locOrder v) (hN : ∀ i j, N i j ∈ locOrder v) (hMN : M * N = 1)
    (hh : ∀ i j, locConj v (M i j) = M j i) :
    ∃ P : GL (Fin r) (LocAlg v),
      (∀ i j, (P : Matrix (Fin r) (Fin r) (LocAlg v)) i j ∈ locOrder v) ∧
      (∀ i j, ((P⁻¹ : GL (Fin r) (LocAlg v)) : Matrix (Fin r) (Fin r) (LocAlg v)) i j ∈
        locOrder v) ∧
      M = (P : Matrix (Fin r) (Fin r) (LocAlg v))ᵀ *
        (P : Matrix (Fin r) (Fin r) (LocAlg v)).map (locConj v) := by
  haveI := isAdicComplete_adicCompletionIntegers v
  haveI := finite_residueField_adicCompletionIntegers v
  let φ : locOrder v →+* LocAlg v := (locOrder v).val
  let M' : Matrix (Fin r) (Fin r) (locOrder v) := Matrix.of fun i j => ⟨M i j, hM i j⟩
  let N' : Matrix (Fin r) (Fin r) (locOrder v) := Matrix.of fun i j => ⟨N i j, hN i j⟩
  have h1 : M' * N' = 1 := by
    apply Matrix.map_injective (f := φ) Subtype.val_injective
    change (M' * N').map φ = Matrix.map 1 φ
    rw [Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _)]
    exact hMN
  obtain ⟨P, hP, h⟩ := UnramifiedHermitian.exists_eq_transpose_mul_map_of_henselian
    (R₀ := v.adicCompletionIntegers (maximalRealSubfield E)) (locOrderConj v) (locOrderConj_locOrderConj v)
    (fun a => Subtype.ext (locConj_algebraMap' v a)) (mem_range_of_locOrderConj_eq v)
    (exists_isUnit_sub_locOrderConj v) (G := M') (fun i j => Subtype.ext (hh i j))
    (Matrix.isUnit_det_of_right_inverse h1)
  obtain ⟨P, rfl⟩ := (Matrix.isUnit_iff_isUnit_det P).2 hP
  refine ⟨Matrix.GeneralLinearGroup.map φ P, fun i j => (P.1 i j).2, fun i j => ?_, ?_⟩
  · rw [← map_inv]; exact ((P⁻¹).1 i j).2
  · have := congrArg (fun X => Matrix.map X φ) h
    simp only [Matrix.map_mul] at this
    exact this

theorem exists_unit_locConj_mul_eq {𝔟 : FractionalIdeal (𝓞 E)⁰ E} (hc : ∀ z ∈ 𝔟, cc z ∈ 𝔟)
    {b : E} (hb0 : b ≠ 0)
    (hb : ∀ z, (∃ s ∉ v.asIdeal, (algebraMap (𝓞 (maximalRealSubfield E)) (𝓞 E) s : E) * z ∈ 𝔟) ↔ b⁻¹ * z ∈ semiLoc v) :
    ∃ ε : (locOrder v)ˣ, locConj v (((ε : locOrder v) : LocAlg v) * locEmb v b) =
      ((ε : locOrder v) : LocAlg v) * locEmb v b := by
  have hu : b⁻¹ * cc b ∈ semiLoc v := by
    obtain ⟨s, hs, h⟩ := (hb b).2 (by rw [inv_mul_cancel₀ hb0]; exact one_mem _)
    refine (hb _).1 ⟨s, hs, ?_⟩
    have := hc _ h
    rwa [HermitianTraceFormVanishing.cc_mul, cc_algebraMap] at this
  have hcb := Published.cc_ne_zero hb0
  have hcu : cc (b⁻¹ * cc b) = (cc b)⁻¹ * b := by simp [cc]
  let u : locOrder v := ⟨_, (locEmb_mem_locOrder_iff v _).2 hu⟩
  have hu1 : u * locOrderConj v u = 1 := by
    apply Subtype.ext
    change locEmb v _ * locEmb v (cc _) = 1
    rw [← map_mul, hcu, ← map_one (locEmb v)]
    congr 1
    field_simp
  obtain ⟨a, ha⟩ := QuadraticEtale.exists_isUnit_add_mul (R := v.adicCompletionIntegers (maximalRealSubfield E))
    (locOrderConj v) (locOrderConj_locOrderConj v) (mem_range_of_locOrderConj_eq v)
    (exists_isUnit_sub_locOrderConj v) hu1
  refine ⟨ha.unit, ?_⟩
  have e0 : ((ha.unit : locOrder v) : LocAlg v) = a + locEmb v (b⁻¹ * cc b) * locConj v a := rfl
  have e1 : locEmb v (b⁻¹ * cc b) * locEmb v b = locEmb v (cc b) := by
    rw [← map_mul]; congr 1; field_simp
  have e2 : locEmb v (cc (b⁻¹ * cc b)) * locEmb v (cc b) = locEmb v b := by
    rw [← map_mul, hcu]; congr 1; field_simp
  rw [e0, map_mul, map_add, map_mul, locConj_locConj, locConj_locEmb, locConj_locEmb]
  linear_combination (a : LocAlg v) * e2 - locConj v a * e1

omit [Algebra.Unramified (𝓞 (maximalRealSubfield E)) (𝓞 E)] in
theorem mulVec_mem_locOrder {P : Matrix (Fin r) (Fin r) (LocAlg v)}
    (hP : ∀ i j, P i j ∈ locOrder v) {x : Fin r → LocAlg v} (hx : ∀ i, x i ∈ locOrder v)
    (i : Fin r) : (P *ᵥ x) i ∈ locOrder v := by
  rw [Matrix.mulVec, dotProduct]
  exact Subalgebra.sum_mem _ fun j _ => mul_mem (hP i j) (hx j)

theorem exists_orthogonal_frame {G : Matrix (Fin r) (Fin r) E} (hG : ∀ a b, cc (G a b) = G b a)
    (hd : G.det ≠ 0) {L : Submodule (𝓞 E) (Fin r → E)} (hL : ReciprocityTheory.MultiplicativeHeights.IsLattice L)
    {𝔟 : FractionalIdeal (𝓞 E)⁰ E} (hmod : ∀ x, x ∈ L ↔ ∀ y ∈ L, herm G x y ∈ 𝔟)
    {b : E} (hb0 : b ≠ 0)
    (hb : ∀ z, (∃ s ∉ v.asIdeal, (algebraMap (𝓞 (maximalRealSubfield E)) (𝓞 E) s : E) * z ∈ 𝔟) ↔ b⁻¹ * z ∈ semiLoc v)
    (ε : (locOrder v)ˣ) (hε : locConj v (((ε : locOrder v) : LocAlg v) * locEmb v b) =
      ((ε : locOrder v) : LocAlg v) * locEmb v b) :
    ∃ h : GL (Fin r) (LocAlg v),
      (h : Matrix (Fin r) (Fin r) (LocAlg v))ᵀ * G.map (locEmb v) *
        (h : Matrix (Fin r) (Fin r) (LocAlg v)).map (locConj v) =
          (((ε : locOrder v) : LocAlg v) * locEmb v b) • 1 ∧
      ∀ x, x ∈ locLattice v L ↔
        ∀ i, (((h⁻¹ : GL (Fin r) (LocAlg v)) : Matrix (Fin r) (Fin r) (LocAlg v)) *ᵥ x) i ∈
          locOrder v := by
  obtain ⟨g, hg⟩ := exists_frame v hL
  have h₁ := gram_mem_semiLoc v hmod hg hb
  have h₂ := gram_inv_mem_semiLoc v hd hL.1 hmod hg hb0 hb
  set H := (g : Matrix (Fin r) (Fin r) E)ᵀ * G * (g : Matrix (Fin r) (Fin r) E).map cc with hH
  have hHd : IsUnit H.det := by
    have := g.det_ne_zero
    rw [hH, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, Published.det_map_cc]
    exact (mul_ne_zero (mul_ne_zero this hd) (Published.cc_ne_zero this)).isUnit
  have hHh : ∀ i j, cc (H i j) = H j i := fun i j => by
    rw [hH, ← Published.herm_col, ← Published.herm_col, HermitianTraceFormVanishing.herm_conj G hG]
  set t := ((ε : locOrder v) : LocAlg v) * locEmb v b with ht
  set t' := (((ε⁻¹ : (locOrder v)ˣ) : locOrder v) : LocAlg v) * locEmb v b⁻¹ with ht'
  have htt : t * t' = 1 := by
    have e : ((ε : locOrder v) : LocAlg v) * (((ε⁻¹ : (locOrder v)ˣ) : locOrder v) : LocAlg v) = 1 :=
      congrArg Subtype.val ε.mul_inv
    rw [ht, ht', mul_mul_mul_comm, e, ← map_mul, mul_inv_cancel₀ hb0, map_one, one_mul]
  have hct' : locConj v t' = t' := by
    have := congrArg (locConj v) htt
    rw [map_mul, hε, map_one] at this
    linear_combination t' * this - locConj v t' * htt
  obtain ⟨P, hP, hP', hPP⟩ := exists_eq_transpose_mul_map_locConj v
    (M := t' • H.map (locEmb v)) (N := t • H⁻¹.map (locEmb v))
    (fun i j => by
      have := mul_mem (ε⁻¹).1.2 ((locEmb_mem_locOrder_iff v _).2 (h₁ i j))
      rwa [map_mul, ← mul_assoc] at this)
    (fun i j => by
      have := mul_mem ε.1.2 ((locEmb_mem_locOrder_iff v _).2 (h₂ i j))
      rwa [map_mul, ← mul_assoc] at this)
    (by
      rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, mul_comm t', htt, one_smul, ← Matrix.map_mul,
        Matrix.mul_nonsing_inv _ hHd, Matrix.map_one _ (map_zero _) (map_one _)])
    (fun i j => by
      change locConj v (t' * locEmb v (H i j)) = t' * locEmb v (H j i)
      rw [map_mul, hct', locConj_locEmb, hHh])
  let g' : GL (Fin r) (LocAlg v) := Matrix.GeneralLinearGroup.map (locEmb v) g
  have hHg : (g' : Matrix (Fin r) (Fin r) (LocAlg v))ᵀ * G.map (locEmb v) *
      (g' : Matrix (Fin r) (Fin r) (LocAlg v)).map (locConj v) =
      (P : Matrix (Fin r) (Fin r) (LocAlg v))ᵀ * (t • 1) *
        (P : Matrix (Fin r) (Fin r) (LocAlg v)).map (locConj v) := by
    rw [Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, ← hPP, smul_smul, htt, one_smul, hH,
      Matrix.map_mul, Matrix.map_mul]
    rfl
  refine ⟨g' * P⁻¹, ?_, fun x => ?_⟩
  · rw [Units.val_mul, UnramifiedHermitian.congr_mul, hHg, ← UnramifiedHermitian.congr_mul,
      Units.mul_inv]
    simp
  · rw [mem_locLattice_iff_of_frame v hg, mul_inv_rev, inv_inv, Units.val_mul,
      ← Matrix.mulVec_mulVec]
    refine ⟨fun h => mulVec_mem_locOrder v hP h, fun h i => ?_⟩
    have := mulVec_mem_locOrder v hP' h i
    rwa [Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec] at this

end NormalForm

def IsLocalIsometry (v : HeightOneSpectrum (𝓞 (maximalRealSubfield E)))
    (G : Matrix (Fin r) (Fin r) E) (L : Submodule (𝓞 E) (Fin r → E))
    (G' : Matrix (Fin r) (Fin r) E) (L' : Submodule (𝓞 E) (Fin r → E))
    (γ : GL (Fin r) (LocAlg v)) : Prop :=
  G'.map (locEmb v) = (γ : Matrix (Fin r) (Fin r) (LocAlg v))ᵀ * G.map (locEmb v) *
      (γ : Matrix (Fin r) (Fin r) (LocAlg v)).map (locConj v) ∧
    ∀ x, x ∈ locLattice v L' ↔ (γ : Matrix (Fin r) (Fin r) (LocAlg v)) *ᵥ x ∈ locLattice v L

variable {G G' : Matrix (Fin r) (Fin r) E} {L L' : Submodule (𝓞 E) (Fin r → E)}

theorem isLocalIsometry_one_iff (v : HeightOneSpectrum (𝓞 (maximalRealSubfield E))) :
    IsLocalIsometry v G L G L' 1 ↔ locLattice v L' = locLattice v L := by
  simp [IsLocalIsometry, SetLike.ext_iff]

theorem IsLocalIsometry.det_div_eq_mul_locConj {v : HeightOneSpectrum (𝓞 (maximalRealSubfield E))}
    {γ : GL (Fin r) (LocAlg v)} (h : IsLocalIsometry v G L G' L' γ) (hd' : G'.det ≠ 0) :
    ∃ z : LocAlg v, locEmb v (G.det / G'.det) = z * locConj v z := by
  have h1 := congrArg Matrix.det h.1
  rw [UnramifiedHermitian.det_congr, ← RingHom.mapMatrix_apply, ← RingHom.mapMatrix_apply,
    ← RingHom.map_det, ← RingHom.map_det] at h1
  obtain ⟨z, hz⟩ := ((Matrix.isUnit_iff_isUnit_det _).1 γ.isUnit).exists_left_inv
  have hz' := congrArg (locConj v) hz
  rw [map_mul, map_one] at hz'
  have h2 : locEmb v G'.det * locEmb v G'.det⁻¹ = 1 := by
    rw [← map_mul, mul_inv_cancel₀ hd', map_one]
  refine ⟨z, ?_⟩
  rw [div_eq_mul_inv, map_mul]
  calc locEmb v G.det * locEmb v G'.det⁻¹
      = (z * (γ : Matrix (Fin r) (Fin r) (LocAlg v)).det) *
        (locConj v z * locConj v (γ : Matrix (Fin r) (Fin r) (LocAlg v)).det) *
          locEmb v G.det * locEmb v G'.det⁻¹ := by rw [hz, hz', one_mul, one_mul]
    _ = z * locConj v z * (locEmb v G'.det * locEmb v G'.det⁻¹) := by rw [h1]; ring
    _ = z * locConj v z := by rw [h2, mul_one]

theorem congr_of_local_norm (H : Published.Landherr) (H' : Published.HasseNormSt)
    (hG : ∀ a b, cc (G a b) = G b a) (hG' : ∀ a b, cc (G' a b) = G' b a)
    (hd : G.det ≠ 0) (hd' : G'.det ≠ 0)
    (hs : ∀ τ : E →+* ℂ, ∃ Q : Matrix (Fin r) (Fin r) ℂ, Q.det ≠ 0 ∧
      G'.map τ = Qᵀ * G.map τ * Q.map conj)
    (hf : ∀ v : HeightOneSpectrum (𝓞 (maximalRealSubfield E)), ∃ z : LocAlg v,
      locEmb v (G.det / G'.det) = z * locConj v z) :
    ∃ P : Matrix (Fin r) (Fin r) E, P.det ≠ 0 ∧ G' = Pᵀ * G * P.map cc := by
  have hm : G.det / G'.det ∈ maximalRealSubfield E := by
    rw [← IsCMField.complexConj_eq_self_iff, map_div₀]
    exact congrArg₂ (· / ·) (Published.cc_det_of_herm hG) (Published.cc_det_of_herm hG')
  obtain ⟨θ, h0, hθ⟩ := Published.exists_cc_eq_neg E
  obtain ⟨d, hdθ⟩ := Published.exists_sq_real hθ
  obtain ⟨p, q, hpq⟩ := H' (maximalRealSubfield E) d ⟨_, hm⟩
    (fun h => mul_ne_zero h0 h0 (by rw [← hdθ, h]; rfl))
    (fun h => div_ne_zero hd hd' (congrArg Subtype.val h))
    (fun σ => by
      have h1 := Published.Landherr.re_det_div_pos hd _
        (hs (ComplexEmbedding.lift E (Complex.ofRealHom.comp σ)))
      have h2 : ComplexEmbedding.lift E (Complex.ofRealHom.comp σ) (G.det / G'.det) =
          (σ ⟨_, hm⟩ : ℂ) :=
        ComplexEmbedding.lift_algebraMap_apply E (Complex.ofRealHom.comp σ) ⟨_, hm⟩
      rw [h2, Complex.ofReal_re] at h1
      exact ⟨Real.sqrt (σ ⟨_, hm⟩), 0, by rw [Real.sq_sqrt h1.le]; ring⟩)
    (fun v => by
      obtain ⟨z, hz⟩ := hf v
      obtain ⟨p, q, rfl⟩ := exists_coord v h0 hθ z
      refine ⟨p, q, algebraMap_locAlg_injective v ?_⟩
      rw [← locEmb_coe, map_sub, map_mul, ← locEmb_coe, hdθ, map_pow, map_pow, map_mul]
      rw [map_add, map_mul, locConj_algebraMap, locConj_algebraMap, locConj_locEmb, hθ,
        map_neg] at hz
      exact hz.trans (by ring))
  refine H E r G G' hG hG' hd hd' hs ⟨(p : E) + q * θ, ?_⟩
  have h1 : G.det / G'.det = (p : E) ^ 2 - (d : E) * (q : E) ^ 2 := by
    simpa using congrArg Subtype.val hpq
  have h2 : cc ((p : E) + q * θ) = p - q * θ := by
    change IsCMField.complexConj E _ = _
    rw [map_add, map_mul, IsCMField.complexConj_apply_eq_self, IsCMField.complexConj_apply_eq_self,
      show IsCMField.complexConj E θ = -θ from hθ]
    ring
  rw [h1, h2, hdθ]
  ring

section Modular

variable [Algebra.Unramified (𝓞 (maximalRealSubfield E)) (𝓞 E)] {𝔟 : FractionalIdeal (𝓞 E)⁰ E}

theorem exists_isLocalIsometry_of_modular (h𝔟 : 𝔟 ≠ 0) (hc : ∀ z ∈ 𝔟, cc z ∈ 𝔟)
    (hG : ∀ a b, cc (G a b) = G b a) (hG' : ∀ a b, cc (G' a b) = G' b a)
    (hd : G.det ≠ 0) (hd' : G'.det ≠ 0)
    (hL : ReciprocityTheory.MultiplicativeHeights.IsLattice L) (hL' : ReciprocityTheory.MultiplicativeHeights.IsLattice L')
    (hmod : ∀ x, x ∈ L ↔ ∀ y ∈ L, herm G x y ∈ 𝔟) (hmod' : ∀ x, x ∈ L' ↔ ∀ y ∈ L', herm G' x y ∈ 𝔟)
    (v : HeightOneSpectrum (𝓞 (maximalRealSubfield E))) : ∃ γ, IsLocalIsometry v G L G' L' γ := by
  obtain ⟨b, hb0, hb⟩ := exists_generator v h𝔟
  obtain ⟨ε, hε⟩ := exists_unit_locConj_mul_eq v hc hb0 hb
  obtain ⟨h, h₁, h₂⟩ := exists_orthogonal_frame v hG hd hL hmod hb0 hb ε hε
  obtain ⟨h', h₁', h₂'⟩ := exists_orthogonal_frame v hG' hd' hL' hmod' hb0 hb ε hε
  refine ⟨h * h'⁻¹, ?_, fun x => ?_⟩
  · rw [Units.val_mul, UnramifiedHermitian.congr_mul, h₁, ← h₁', ← UnramifiedHermitian.congr_mul,
      Units.mul_inv]
    simp
  · rw [h₂, h₂', Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel_left]

theorem one_genus_of_modular (h𝔟 : 𝔟 ≠ 0) (hc : ∀ z ∈ 𝔟, cc z ∈ 𝔟)
    (hG : ∀ a b, cc (G a b) = G b a) (hd : G.det ≠ 0)
    (hL : ReciprocityTheory.MultiplicativeHeights.IsLattice L) (hL' : ReciprocityTheory.MultiplicativeHeights.IsLattice L')
    (hmod : ∀ x, x ∈ L ↔ ∀ y ∈ L, herm G x y ∈ 𝔟) (hmod' : ∀ x, x ∈ L' ↔ ∀ y ∈ L', herm G x y ∈ 𝔟) :
    ∃ γ : ∀ v : HeightOneSpectrum (𝓞 (maximalRealSubfield E)), GL (Fin r) (LocAlg v),
      (∀ v, IsLocalIsometry v G L G L' (γ v)) ∧ {v | γ v ≠ 1}.Finite := by
  classical
  choose γ hγ using exists_isLocalIsometry_of_modular h𝔟 hc hG hG hd hd hL hL' hmod hmod'
  refine ⟨fun v => if locLattice v L' = locLattice v L then 1 else γ v, fun v => ?_,
    (finite_setOf_locLattice_ne hL' hL).subset fun v hv h => hv (if_pos h)⟩
  beta_reduce
  split_ifs with h
  exacts [(isLocalIsometry_one_iff v).2 h, hγ v]

theorem congr_of_modular (H : Published.Landherr) (H' : Published.HasseNormSt)
    (h𝔟 : 𝔟 ≠ 0) (hc : ∀ z ∈ 𝔟, cc z ∈ 𝔟)
    (hG : ∀ a b, cc (G a b) = G b a) (hG' : ∀ a b, cc (G' a b) = G' b a)
    (hd : G.det ≠ 0) (hd' : G'.det ≠ 0)
    (hL : ReciprocityTheory.MultiplicativeHeights.IsLattice L) (hL' : ReciprocityTheory.MultiplicativeHeights.IsLattice L')
    (hmod : ∀ x, x ∈ L ↔ ∀ y ∈ L, herm G x y ∈ 𝔟) (hmod' : ∀ x, x ∈ L' ↔ ∀ y ∈ L', herm G' x y ∈ 𝔟)
    (hs : ∀ τ : E →+* ℂ, ∃ Q : Matrix (Fin r) (Fin r) ℂ, Q.det ≠ 0 ∧
      G'.map τ = Qᵀ * G.map τ * Q.map conj) :
    ∃ P : Matrix (Fin r) (Fin r) E, P.det ≠ 0 ∧ G' = Pᵀ * G * P.map cc :=
  congr_of_local_norm H H' hG hG' hd hd' hs fun v => by
    obtain ⟨γ, hγ⟩ := exists_isLocalIsometry_of_modular h𝔟 hc hG hG' hd hd' hL hL' hmod hmod' v
    exact hγ.det_div_eq_mul_locConj hd'

theorem exists_orthonormal_frame (hG : ∀ a b, cc (G a b) = G b a) (hd : G.det ≠ 0)
    (hL : ReciprocityTheory.MultiplicativeHeights.IsLattice L) (hsd : ∀ x, x ∈ L ↔ ∀ y ∈ L, IsIntegral ℤ (herm G x y))
    (v : HeightOneSpectrum (𝓞 (maximalRealSubfield E))) :
    ∃ h : GL (Fin r) (LocAlg v),
      (h : Matrix (Fin r) (Fin r) (LocAlg v))ᵀ * G.map (locEmb v) *
        (h : Matrix (Fin r) (Fin r) (LocAlg v)).map (locConj v) = 1 ∧
      ∀ x, x ∈ locLattice v L ↔
        ∀ i, (((h⁻¹ : GL (Fin r) (LocAlg v)) : Matrix (Fin r) (Fin r) (LocAlg v)) *ᵥ x) i ∈
          locOrder v := by
  simpa using exists_orthogonal_frame v hG hd hL (𝔟 := 1)
    (by simpa only [mem_one_fractionalIdeal_iff] using hsd) one_ne_zero
    (fun z => by simp only [mem_one_fractionalIdeal_iff, inv_one, one_mul, mem_semiLoc_iff]) 1
    (by simp)

end Modular

theorem cc_mem_inv_mul_different {ξ : E} (hξ : cc ξ = -ξ) (z : E)
    (hz : z ∈ ((FractionalIdeal.spanSingleton (𝓞 E)⁰ ξ *
      (differentIdeal ℤ (𝓞 E) : Ideal (𝓞 E)))⁻¹ : FractionalIdeal (𝓞 E)⁰ E)) :
    cc z ∈ ((FractionalIdeal.spanSingleton (𝓞 E)⁰ ξ *
      (differentIdeal ℤ (𝓞 E) : Ideal (𝓞 E)))⁻¹ : FractionalIdeal (𝓞 E)⁰ E) := by
  have h : FractionalIdeal.spanSingleton (𝓞 E)⁰ (-ξ) = FractionalIdeal.spanSingleton (𝓞 E)⁰ ξ :=
    FractionalIdeal.spanSingleton_eq_spanSingleton.2 ⟨-1, by simp⟩
  rwa [← mem_conjFrac, conjFrac_inv, map_mul, conjFrac_spanSingleton, conjFrac_different, hξ, h]

theorem modular_of_perfect {ξ : E} (hξ0 : ξ ≠ 0) (hd : G.det ≠ 0) (hL : ReciprocityTheory.MultiplicativeHeights.IsLattice L)
    (h : (∀ x ∈ L, ∀ y ∈ L, ∃ k : ℤ, EFf ξ G x y = k) ∧
      ∀ φ : L →+ ℤ, ∃ x ∈ L, ∀ y : L, (φ y : ℚ) = EFf ξ G x y) (x : Fin r → E) :
    x ∈ L ↔ ∀ y ∈ L, herm G x y ∈ ((FractionalIdeal.spanSingleton (𝓞 E)⁰ ξ *
      (differentIdeal ℤ (𝓞 E) : Ideal (𝓞 E)))⁻¹ : FractionalIdeal (𝓞 E)⁰ E) := by
  rw [← mem_smul_hermDual_iff (inv_ne_zero (mul_ne_zero
    (FractionalIdeal.spanSingleton_ne_zero_iff.2 hξ0) coe_different_ne_zero)),
    ← traceFormDual_eq hξ0, (perfect_iff_traceFormDual_eq hξ0 hd hL).1 h]

variable (E r) in

def signMatrix (p : ℕ) : Matrix (Fin r) (Fin r) E :=
  Matrix.diagonal fun a => if (a : ℕ) < p then 1 else -1

theorem signMatrix_herm (p : ℕ) (a b : Fin r) :
    cc (signMatrix E r p a b) = signMatrix E r p b a := by
  by_cases h : a = b
  · subst h
    simp only [signMatrix, Matrix.diagonal_apply_eq, cc]
    split_ifs <;> simp
  · simp [signMatrix, cc, h, Ne.symm h]

omit [IsCMField E] in
theorem det_signMatrix_ne_zero (p : ℕ) : (signMatrix E r p).det ≠ 0 := by
  rw [signMatrix, Matrix.det_diagonal]
  refine Finset.prod_ne_zero_iff.2 fun a _ => ?_
  split_ifs <;> simp

omit [NumberField E] [IsCMField E] in
theorem gram_signMatrix (τ : E →+* ℂ) (p : ℕ) :
    gram τ (signMatrix E r p) 1 = Matrix.diagonal fun a : Fin r => ((sgn p (a : ℕ) : ℝ) : ℂ) := by
  rw [Published.gram_eq, Matrix.transpose_one, Matrix.one_mul,
    Matrix.map_one _ (map_zero _) (map_one _), Matrix.mul_one, signMatrix,
    Matrix.diagonal_map (map_zero _)]
  congr 1
  funext a
  simp only [sgn]
  split_ifs <;> simp

omit [IsCMField E] in
theorem mem_frameLattice_one_iff (x : Fin r → E) :
    x ∈ frameLattice (𝓞 E) (1 : GL (Fin r) E) ↔ ∀ i, IsIntegral ℤ (x i) := by
  simp [mem_frameLattice_iff_inv, ← mem_one_ringOfIntegers_iff]

theorem selfDual_signMatrix (p : ℕ) (x : Fin r → E) :
    x ∈ frameLattice (𝓞 E) (1 : GL (Fin r) E) ↔
      ∀ y ∈ frameLattice (𝓞 E) (1 : GL (Fin r) E), IsIntegral ℤ (herm (signMatrix E r p) x y) := by
  simp only [mem_frameLattice_one_iff]
  constructor
  · intro hx y hy
    refine IsIntegral.sum _ fun a _ => IsIntegral.sum _ fun b _ =>
      ((hx a).mul ?_).mul (isIntegral_cc (hy b))
    simp only [signMatrix, Matrix.diagonal_apply]
    split_ifs
    exacts [isIntegral_one, isIntegral_one.neg, isIntegral_zero]
  · intro h i
    have := h (Pi.single i 1) fun j => by
      rw [Pi.single_apply]
      split_ifs
      exacts [isIntegral_one, isIntegral_zero]
    rw [HermitianTraceFormVanishing.herm_single_right, signMatrix, Matrix.vecMul_diagonal] at this
    split_ifs at this
    · simpa using this
    · simpa using this.neg

theorem congr_signMatrix [Algebra.Unramified (𝓞 (maximalRealSubfield E)) (𝓞 E)]
    (H : Published.Landherr) (H' : Published.HasseNormSt)
    (hG : ∀ a b, cc (G a b) = G b a) (hd : G.det ≠ 0) (hL : ReciprocityTheory.MultiplicativeHeights.IsLattice L)
    (hsd : ∀ x, x ∈ L ↔ ∀ y ∈ L, IsIntegral ℤ (herm G x y))
    (Ψ : Set (E →+* ℂ)) (hΨ : ∀ τ : E →+* ℂ, τ ∈ Ψ ∨ ComplexEmbedding.conjugate τ ∈ Ψ) (p : ℕ)
    (hs : ∀ τ ∈ Ψ, ∃ Q : Matrix (Fin r) (Fin r) ℂ, Q.det ≠ 0 ∧
      gram τ G Q = Matrix.diagonal fun a : Fin r => ((sgn p (a : ℕ) : ℝ) : ℂ)) :
    ∃ P : Matrix (Fin r) (Fin r) E, P.det ≠ 0 ∧ G = Pᵀ * signMatrix E r p * P.map cc :=
  congr_of_modular (𝔟 := 1) H H' one_ne_zero
    (fun _ hz => mem_one_fractionalIdeal_iff.2 (isIntegral_cc (mem_one_fractionalIdeal_iff.1 hz)))
    (signMatrix_herm p) hG (det_signMatrix_ne_zero p) hd
    ((isLattice_iff _).2 (isLattice_frameLattice 1)) hL
    (by simpa only [mem_one_fractionalIdeal_iff] using selfDual_signMatrix p)
    (by simpa only [mem_one_fractionalIdeal_iff] using hsd)
    (Published.Landherr.congr_of_signature Ψ hΨ fun τ hτ =>
      ⟨p, ⟨1, by simp, gram_signMatrix τ p⟩, hs τ hτ⟩)

end GlobalTheory.SelfDualGenus

namespace GlobalTheory

open SelfDualGenus

theorem selfDual_lattices_one_genus {E : Type} [Field E] [NumberField E] [IsCMField E]
    [Algebra.Unramified (𝓞 (maximalRealSubfield E)) (𝓞 E)] {r : ℕ}
    {G G' : Matrix (Fin r) (Fin r) E} (hG : ∀ a b, cc (G a b) = G b a)
    (hG' : ∀ a b, cc (G' a b) = G' b a) (hd : G.det ≠ 0) (hd' : G'.det ≠ 0)
    {L L' : Submodule (𝓞 E) (Fin r → E)}
    (hL : ReciprocityTheory.MultiplicativeHeights.IsLattice L) (hL' : ReciprocityTheory.MultiplicativeHeights.IsLattice L')
    (hdual : ((∀ x, x ∈ L ↔ ∀ y ∈ L, IsIntegral ℤ (herm G x y)) ∧
        ∀ x, x ∈ L' ↔ ∀ y ∈ L', IsIntegral ℤ (herm G' x y)) ∨
      ∃ ξ : E, ξ ≠ 0 ∧ cc ξ = -ξ ∧
        ((∀ x ∈ L, ∀ y ∈ L, ∃ k : ℤ, EFf ξ G x y = k) ∧
          ∀ φ : L →+ ℤ, ∃ x ∈ L, ∀ y : L, (φ y : ℚ) = EFf ξ G x y) ∧
        ((∀ x ∈ L', ∀ y ∈ L', ∃ k : ℤ, EFf ξ G' x y = k) ∧
          ∀ φ : L' →+ ℤ, ∃ x ∈ L', ∀ y : L', (φ y : ℚ) = EFf ξ G' x y)) :
    (∀ v : HeightOneSpectrum (𝓞 (maximalRealSubfield E)),
      ∃ γ : GL (Fin r) (LocAlg v), IsLocalIsometry v G L G' L' γ) ∧
    (G' = G → ∃ γ : ∀ v : HeightOneSpectrum (𝓞 (maximalRealSubfield E)), GL (Fin r) (LocAlg v),
      (∀ v, IsLocalIsometry v G L G L' (γ v)) ∧ {v | γ v ≠ 1}.Finite) ∧
    (Published.Landherr → Published.HasseNormSt →
      ∀ Ψ : Set (E →+* ℂ), (∀ τ : E →+* ℂ, τ ∈ Ψ ∨ ComplexEmbedding.conjugate τ ∈ Ψ) →
      (∀ τ ∈ Ψ, ∃ p : ℕ,
        (∃ Q : Matrix (Fin r) (Fin r) ℂ, Q.det ≠ 0 ∧
          gram τ G Q = Matrix.diagonal fun a : Fin r => ((sgn p (a : ℕ) : ℝ) : ℂ)) ∧
        ∃ Q : Matrix (Fin r) (Fin r) ℂ, Q.det ≠ 0 ∧
          gram τ G' Q = Matrix.diagonal fun a : Fin r => ((sgn p (a : ℕ) : ℝ) : ℂ)) →
      ∃ P : Matrix (Fin r) (Fin r) E, P.det ≠ 0 ∧ G' = Pᵀ * G * P.map cc) := by
  obtain ⟨𝔟, h𝔟, hc, hmod, hmod'⟩ : ∃ 𝔟 : FractionalIdeal (𝓞 E)⁰ E, 𝔟 ≠ 0 ∧ (∀ z ∈ 𝔟, cc z ∈ 𝔟) ∧
      (∀ x, x ∈ L ↔ ∀ y ∈ L, herm G x y ∈ 𝔟) ∧ ∀ x, x ∈ L' ↔ ∀ y ∈ L', herm G' x y ∈ 𝔟 := by
    rcases hdual with ⟨h, h'⟩ | ⟨ξ, hξ0, hξ, h, h'⟩
    · refine ⟨1, one_ne_zero, ?_⟩
      simp only [mem_one_fractionalIdeal_iff]
      exact ⟨fun _ => isIntegral_cc, h, h'⟩
    · exact ⟨_, inv_ne_zero (mul_ne_zero (FractionalIdeal.spanSingleton_ne_zero_iff.2 hξ0)
        coe_different_ne_zero), cc_mem_inv_mul_different hξ, modular_of_perfect hξ0 hd hL h,
        modular_of_perfect hξ0 hd' hL' h'⟩
  refine ⟨exists_isLocalIsometry_of_modular h𝔟 hc hG hG' hd hd' hL hL' hmod hmod', ?_,
    fun H H' Ψ hΨ hs => congr_of_modular H H' h𝔟 hc hG hG' hd hd' hL hL' hmod hmod'
      (Published.Landherr.congr_of_signature Ψ hΨ hs)⟩
  rintro rfl
  exact one_genus_of_modular h𝔟 hc hG hd hL hL' hmod hmod'

end GlobalTheory
