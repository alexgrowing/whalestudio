import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.InertiaQuadraticRamification.InertSplitAlt
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FinitePlacesInertiaNotLeOpenSubgroupStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TameKummerInertiaSurjective
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsSolvableCmExtensionSplitPlace
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.QuadraticNormHeckeCharRamifiedBelowRamifiedPrime
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.InfiniteQuadraticCMGoodBaseChangeSplit
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ValPrimeOfLt
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.HeckeGal GlobalTheory.CuspRep UpperTheory.V.Published GlobalTheory.RealGal GlobalTheory.UnitaryBC
open UpperTheory.Gal.UnramifiedFromSplittingCriterion

namespace UpperTheory.Gal.UnramifiedFromSplittingCriterion.WeylLatticeInDetCoeffSpan

private theorem normV_mem' {K : Type} [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K)) :
    ((normV v : ℕ) : 𝓞 K) ∈ v.asIdeal := Ideal.absNorm_mem v.asIdeal

private theorem normV_pos' {K : Type} [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K)) : 0 < normV v := by
  have h : Ideal.absNorm v.asIdeal ≠ 0 := fun h => v.ne_bot (Ideal.absNorm_eq_zero_iff.1 h)
  exact Nat.pos_of_ne_zero h

private theorem val_lt_of_dvd {K Ω : Type} [Field K] [NumberField K] [Field Ω] [Algebra K Ω] (A : ValuationSubring Ω)
    (v : HeightOneSpectrum (𝓞 K)) (hA : IsPlaceOver A v) {c : ℕ} (h : normV v ∣ c) : A.valuation (c : Ω) < 1 := by
  obtain ⟨k, rfl⟩ := h
  refine GlobalTheory.TameCoupledEx.val_g_lt A v hA ?_
  rw [Nat.cast_mul]
  exact v.asIdeal.mul_mem_right _ (normV_mem' v)

private theorem val_prime_of_lt {Ω : Type} [Field Ω] (A : ValuationSubring Ω) (n : ℕ) :
    n ≠ 0 → A.valuation (n : Ω) < 1 → ∃ t : ℕ, t.Prime ∧ t ∣ n ∧ A.valuation (t : Ω) < 1 :=
  _root_.UpperTheory.Reformulated.B.Qi55.val_prime_of_lt A n

private theorem fix_of_val {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] (hS : SqrtFix)
    (A : ValuationSubring Ω) (x : Ω) (a : ℤ) (hx : x ^ 2 = (a : Ω)) (c : ℕ) (hc : c ≠ 0)
    (hd : ((8 * c : ℕ) : ℤ) ∣ a - 1) (hv : A.valuation (c : Ω) < 1) (g : G F Ω) (hg : g ∈ Dec (F := F) A) : g x = x := by
  obtain ⟨t, ht, htc, htv⟩ := val_prime_of_lt A c hc hv
  refine (hS F Ω A x a hx).1 t ht htv (dvd_trans ?_ hd) g hg
  rw [Int.natCast_dvd_natCast]
  exact Nat.mul_dvd_mul_left 8 htc

private theorem moved_at_ram {Y Ω : Type} [Field Y] [NumberField Y] [Field Ω] [Algebra Y Ω] [IsAlgClosure Y Ω]
    (hS : SqrtFix) (A : ValuationSubring Ω) (u : HeightOneSpectrum (𝓞 Y)) (hA : IsPlaceOver A u) (p₁ p₂ : ℕ)
    (h1 : p₁.Prime) (h2 : p₂.Prime) (hodd : 2 < p₁) (hlt : p₁ < p₂) (hu : ((p₁ : ℕ) : 𝓞 Y) ∈ u.asIdeal)
    (hu2 : ((p₁ : ℕ) : 𝓞 Y) ∉ u.asIdeal ^ 2) (x : Ω) (hx : x ^ 2 = ((-((p₁ * p₂ : ℕ) : ℤ) : ℤ) : Ω)) :
    ∃ τ ∈ Ine (F := Y) A, τ x ≠ x := by
  haveI : Fact p₁.Prime := ⟨h1⟩
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap Y Ω).injective
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed Y
  obtain ⟨Y0, hY0⟩ := IsAlgClosed.exists_pow_nat_eq ((p₁ : ℕ) : Ω) two_pos
  have hnd : ¬ p₁ ∣ 2 := fun h => by have := Nat.le_of_dvd two_pos h; omega
  obtain ⟨τ, hτ, hτY⟩ := GlobalTheory.TameKummerInertia.tame_kummer_surj Y Ω A u hA p₁ hu hu2 2 two_pos hnd Y0 (-1) hY0 (by norm_num)
  have hp10 : ((p₁ : ℕ) : Ω) ≠ 0 := Nat.cast_ne_zero.2 h1.ne_zero
  have hY00 : Y0 ≠ 0 := by
    rintro rfl
    rw [zero_pow two_ne_zero] at hY0
    exact hp10 hY0.symm
  have hv1 : A.valuation ((p₁ : ℕ) : Ω) < 1 := GlobalTheory.TameCoupledEx.val_g_lt A u hA hu
  set z : Ω := x / Y0 with hz
  have hz2 : z ^ 2 = ((-(p₂ : ℤ) : ℤ) : Ω) := by
    rw [hz, div_pow, hx, hY0]
    push_cast
    field_simp
  have hcop : IsCoprime (p₁ : ℤ) (2 * (-(p₂ : ℤ))) := by
    have ha : IsCoprime (p₁ : ℤ) 2 := by
      have : Nat.Coprime p₁ 2 := (Nat.Prime.coprime_iff_not_dvd h1).2 (by
        intro h; have := Nat.le_of_dvd two_pos h; omega)
      exact_mod_cast Nat.isCoprime_iff_coprime.2 this
    have hb : IsCoprime (p₁ : ℤ) (p₂ : ℤ) := by
      have : Nat.Coprime p₁ p₂ := (Nat.coprime_primes h1 h2).2 hlt.ne
      exact Nat.isCoprime_iff_coprime.2 this
    exact ha.mul_right hb.neg_right
  have hv2 : A.valuation ((2 * (-(p₂ : ℤ)) : ℤ) : Ω) = 1 := by
    obtain ⟨s, t, hst⟩ := hcop
    refine le_antisymm ((A.valuation_le_one_iff _).2 (intCast_mem A _)) (not_lt.1 fun hlt1 => ?_)
    have h3 : ((s * (p₁ : ℤ) + t * (2 * (-(p₂ : ℤ))) : ℤ) : Ω) = 1 := by rw [hst]; simp
    have hs1 : A.valuation ((s : ℤ) : Ω) ≤ 1 := (A.valuation_le_one_iff _).2 (intCast_mem A _)
    have ht1 : A.valuation ((t : ℤ) : Ω) ≤ 1 := (A.valuation_le_one_iff _).2 (intCast_mem A _)
    have h4 : A.valuation (((s * (p₁ : ℤ) + t * (2 * (-(p₂ : ℤ))) : ℤ)) : Ω) < 1 := by
      rw [Int.cast_add, Int.cast_mul, Int.cast_mul t]
      refine Valuation.map_add_lt _ ?_ ?_
      · rw [map_mul]
        exact lt_of_le_of_lt (mul_le_of_le_one_left' hs1) (by simpa using hv1)
      · rw [map_mul]
        exact lt_of_le_of_lt (mul_le_of_le_one_left' ht1) hlt1
    rw [h3, map_one] at h4
    exact lt_irrefl _ h4
  have hτz : τ z = z := (hS Y Ω A z (-(p₂ : ℤ)) hz2).2 hv2 τ hτ
  have hxz : x = z * Y0 := by rw [hz]; field_simp
  have hx0 : x ≠ 0 := by
    rintro rfl
    rw [zero_pow two_ne_zero] at hx
    have : ((p₁ * p₂ : ℕ) : Ω) = 0 := by
      have h5 := hx.symm
      push_cast at h5 ⊢
      simpa using h5
    exact (Nat.cast_ne_zero.2 (Nat.mul_ne_zero h1.ne_zero h2.ne_zero)) this
  refine ⟨τ, hτ, fun hfix => ?_⟩
  have h6 : τ x = -x := by
    rw [hxz, map_mul, hτz, hτY]
    ring
  rw [hfix] at h6
  have h7 : (2 : Ω) * x = 0 := by linear_combination h6
  exact hx0 ((mul_eq_zero.1 h7).resolve_left two_ne_zero)

private theorem fix_of_real {Z Ω F' : Type} [Field Z] [NumberField Z] [IsCMField Z] [Field Ω] [Algebra Z Ω] [Field F']
    [Algebra F' Ω] (g : G F' Ω) (X : Z) (d : ℕ) (hd : 0 < d) (hX : X ^ 2 = -(d : Z))
    (hreal : Fixes (maximalRealSubfield Z) g) (hgx : g (algebraMap Z Ω X) = algebraMap Z Ω X) : Fixes Z g := by
  have hd0 : (d : Z) ≠ 0 := Nat.cast_ne_zero.2 hd.ne'
  have hX0 : X ≠ 0 := by
    rintro rfl
    rw [zero_pow two_ne_zero] at hX
    exact hd0 (neg_eq_zero.1 hX.symm)
  have hnr : X ∉ maximalRealSubfield Z := by
    intro hr
    obtain ⟨φ⟩ : Nonempty (Z →+* ℂ) := inferInstance
    have h1 := (mem_maximalRealSubfield_iff X).1 hr φ
    have h2 : (φ X) ^ 2 = -(d : ℂ) := by rw [← map_pow, hX, map_neg, map_natCast]
    have h3 : (φ X).im = 0 := Complex.conj_eq_iff_im.1 h1
    have h4 := congrArg Complex.re h2
    simp [pow_two, h3] at h4
    have : (0 : ℝ) < d := by exact_mod_cast hd
    nlinarith [mul_self_nonneg (φ X).re]
  set c := IsCMField.complexConj Z with hc
  have hcX : c X = -X := by
    have h1 : (c X) ^ 2 = X ^ 2 := by rw [← map_pow, hX, map_neg, map_natCast]
    rcases sq_eq_sq_iff_eq_or_eq_neg.1 h1 with h | h
    · exact absurd ((IsCMField.complexConj_eq_self_iff Z X).1 h) hnr
    · exact h
  intro y
  have ha : (y + c y) / 2 ∈ maximalRealSubfield Z := by
    rw [← IsCMField.complexConj_eq_self_iff, map_div₀, map_add, IsCMField.complexConj_apply_apply, map_ofNat]
    ring
  have hb : (y - c y) / (2 * X) ∈ maximalRealSubfield Z := by
    rw [← IsCMField.complexConj_eq_self_iff, map_div₀, map_sub, map_mul, IsCMField.complexConj_apply_apply, map_ofNat, ← hc, hcX]
    field_simp
    ring
  have hy : y = (y + c y) / 2 + X * ((y - c y) / (2 * X)) := by
    field_simp
    ring
  have h1 : g (algebraMap Z Ω ((y + c y) / 2)) = algebraMap Z Ω ((y + c y) / 2) := hreal ⟨_, ha⟩
  have h2 : g (algebraMap Z Ω ((y - c y) / (2 * X))) = algebraMap Z Ω ((y - c y) / (2 * X)) := hreal ⟨_, hb⟩
  rw [hy, map_add, map_mul, map_add, map_mul, h1, h2, hgx]

private theorem conj_of_sq {u : ℂ} {q : ℕ} (hq : 0 < q) (h : u ^ 2 = (q : ℂ)) : star u = u := by
  have h1 := congrArg Complex.re h
  have h2 := congrArg Complex.im h
  simp [pow_two] at h1 h2
  have hq' : (0 : ℝ) < q := by exact_mod_cast hq
  have him : u.im = 0 := by
    have h3 : u.re * u.im = 0 := by linarith
    rcases mul_eq_zero.1 h3 with h | h
    · rw [h] at h1
      nlinarith [mul_self_nonneg u.im]
    · exact h
  exact Complex.conj_eq_iff_im.2 him

section

variable {Y Ω : Type} [Field Y] [NumberField Y] [IsCMField Y] [Field Ω] [Algebra Y Ω] [IsAlgClosure Y Ω]

private theorem algClosure_real (L Ω : Type) [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω]
    [IsAlgClosure L Ω] : IsAlgClosure (maximalRealSubfield L) Ω :=
  ⟨IsAlgClosure.isAlgClosed L, Algebra.IsAlgebraic.trans _ L Ω⟩

private theorem unram_of_fix (L Ω : Type) [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω]
    [IsAlgClosure L Ω] (w : HeightOneSpectrum (𝓞 L)) (A : ValuationSubring Ω) (hA : IsPlaceOver A w)
    (hfix : ∀ σ ∈ Ine (F := maximalRealSubfield L) A, ∀ z : L, σ (algebraMap L Ω z) = algebraMap L Ω z) :
    Algebra.IsUnramifiedAt (𝓞 (maximalRealSubfield L)) w.asIdeal := by
  haveI : IsAlgClosure (maximalRealSubfield L) Ω := algClosure_real L Ω
  have hAv : IsPlaceOver A (w.under (𝓞 (maximalRealSubfield L))) := fun x => by
    rw [IsScalarTower.algebraMap_apply (maximalRealSubfield L) L Ω]
    exact hA (algebraMap (𝓞 (maximalRealSubfield L)) (𝓞 L) x)
  obtain ⟨-, he⟩ := GlobalTheory.InertFixVal.ramificationIdx_eq_one A (w.under (𝓞 (maximalRealSubfield L))) w hAv hA hfix
  exact Ideal.ramificationIdx_eq_one_iff.1 he

private theorem real_of_real (Q : QCM Y Ω) (y : maximalRealSubfield Y) :
    algebraMap Y ↥Q.K (y : Y) ∈ maximalRealSubfield ↥Q.K := by
  refine (mem_maximalRealSubfield_iff _).2 fun φ => ?_
  exact (mem_maximalRealSubfield_iff _).1 y.2 (φ.comp (algebraMap Y ↥Q.K))

private theorem fixes_F (Q : QCM Y Ω) (g : G (maximalRealSubfield ↥Q.K) Ω) (y : maximalRealSubfield Y) :
    g.toRingEquiv (algebraMap (maximalRealSubfield Y) Ω y) = algebraMap (maximalRealSubfield Y) Ω y := by
  have h : g (algebraMap (maximalRealSubfield ↥Q.K) Ω ⟨_, real_of_real Q y⟩) =
      algebraMap (maximalRealSubfield ↥Q.K) Ω ⟨_, real_of_real Q y⟩ := g.commutes _
  exact h

private def down (Q : QCM Y Ω) (g : G (maximalRealSubfield ↥Q.K) Ω) : G (maximalRealSubfield Y) Ω :=
  AlgEquiv.ofRingEquiv (f := g.toRingEquiv) (fixes_F Q g)

private theorem nonsplit_of_sqrt_conductor (hSI : SplitIff) (hRS : RealSpan) (hS : SqrtFix) (Q : QCM Y Ω) (x : Ω) (hx : x ∈ Q.K)
    (p : ℕ) (hp : 0 < p) (hx2 : x ^ 2 = ((-(p : ℤ) : ℤ) : Ω)) (δ : Y) (q : ℕ) (hq : 0 < q) (hδ : δ ^ 2 = (q : Y))
    (c : ℕ) (hc0 : c ≠ 0) (hc2 : 2 ∣ c) (hd : ((8 * c : ℕ) : ℤ) ∣ (-(p : ℤ)) - 1)
    (hTP : ∀ A : ValuationSubring Ω, A.valuation ((p : ℕ) : Ω) < 1 → ∀ h : Ω ≃+* Ω, (∀ z, h z ∈ A ↔ z ∈ A) →
        h (algebraMap Y Ω δ) = algebraMap Y Ω δ → ∀ y : Y, h (algebraMap Y Ω y) = algebraMap Y Ω y)
    (w : HeightOneSpectrum (𝓞 ↥Q.K)) (hw : ¬ IsSplitAt w) (A : ValuationSubring Ω) (hA : IsPlaceOver A w) :
    ¬ A.valuation (c : Ω) < 1 ∧ A.valuation ((2 * (-(p : ℤ)) : ℤ) : Ω) = 1 ∧
      ∃ g ∈ Dec (F := maximalRealSubfield Y) A, ¬ Fixes Y g := by
  have hnot : ¬ ∀ g ∈ Dec (F := maximalRealSubfield ↥Q.K) A, Fixes ↥Q.K g :=
    fun h => hw ((hSI ↥Q.K Ω A w hA).2 h)
  push_neg at hnot
  obtain ⟨g, hg, hng⟩ := hnot
  have hZr : Fixes (maximalRealSubfield ↥Q.K) g := fun y => g.commutes y
  have hgY : ¬ Fixes Y g := fun h => hng (hRS Y ↥Q.K Ω (maximalRealSubfield ↥Q.K) g h hZr)
  have hX2 : (⟨x, hx⟩ : ↥Q.K) ^ 2 = -(p : ↥Q.K) := Subtype.ext (by simpa using hx2)
  have hgx : g x ≠ x := fun h => hng (fix_of_real g ⟨x, hx⟩ p hp hX2 hZr h)
  have hvc : ¬ A.valuation (c : Ω) < 1 := fun h => hgx (fix_of_val hS A x _ hx2 c hc0 hd h g hg)
  have hδZ : algebraMap Y ↥Q.K δ ∈ maximalRealSubfield ↥Q.K := by
    refine (mem_maximalRealSubfield_iff _).2 fun φ => conj_of_sq hq ?_
    rw [← map_pow, ← map_pow, hδ, map_natCast, map_natCast]
  have hgδ : g (algebraMap Y Ω δ) = algebraMap Y Ω δ := by
    have h := hZr ⟨_, hδZ⟩
    exact h
  have hvp : ¬ A.valuation ((p : ℕ) : Ω) < 1 := fun h =>
    hgY (fun y => hTP A h g.toRingEquiv (fun z => apply_mem_iff_of_mem_Dec hg z) hgδ y)
  have hvp1 : A.valuation ((p : ℕ) : Ω) = 1 := le_antisymm (valuation_natCast_le_one A p) (not_lt.1 hvp)
  have hv2 : A.valuation ((2 : ℕ) : Ω) = 1 := by
    refine le_antisymm (valuation_natCast_le_one A 2) (not_lt.1 fun h => hvc ?_)
    obtain ⟨k, rfl⟩ := hc2
    rw [Nat.cast_mul, map_mul]
    exact lt_of_le_of_lt (mul_le_of_le_one_right' (valuation_natCast_le_one A k)) h
  refine ⟨hvc, ?_, down Q g, (GlobalTheory.AboveL.mem_dec_congr A (down Q g) g (fun _ => rfl)).2 hg, fun h => hgY h⟩
  have : ((2 * (-(p : ℤ)) : ℤ) : Ω) = -(((2 : ℕ) : Ω) * ((p : ℕ) : Ω)) := by push_cast; ring
  rw [this, Valuation.map_neg, map_mul, hv2, hvp1, one_mul]

end

end UpperTheory.Gal.UnramifiedFromSplittingCriterion.WeylLatticeInDetCoeffSpan
