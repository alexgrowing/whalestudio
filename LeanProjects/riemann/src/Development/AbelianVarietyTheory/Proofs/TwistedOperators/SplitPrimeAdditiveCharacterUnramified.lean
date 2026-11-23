import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.IteratedLiftChains
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.DualLatticeDifferentIndex
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.StdCharFinitePartRationalEqExpTrace

noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta GlobalTheory.Idele WithZero
open GlobalTheory.StdDual (codiff codiff_ne_zero one_le_codiff char_fin_add)
open scoped nonZeroDivisors

namespace GlobalTheory.SplitUnram

variable {F : Type} [Field F] [NumberField F]

theorem mem_adelicIdeal_codiff_iff {ψ : AddChar (AF F) ℂ} (hc : Continuous ψ)
    (h : ∀ x : F, ψ (pairA F 0 (algebraMap F (Af F) x)) =
      Complex.exp (2 * Real.pi * Complex.I * ((Algebra.trace ℚ F x : ℚ) : ℂ))) (y : Af F) :
    y ∈ adelicIdeal (codiff F) ↔
      ∀ α : Af F, (∀ v, α v ∈ v.adicCompletionIntegers F) → ψ (pairA F 0 (α * y)) = 1 := by
  have h1 : ∀ x : F, ψ (pairA F 0 (algebraMap F (Af F) x)) = 1 ↔
      Algebra.trace ℚ F x ∈ (algebraMap ℤ ℚ).range := fun x => by
    rw [h, mul_comm, Complex.exp_eq_one_iff]
    constructor
    · rintro ⟨n, hn⟩
      refine ⟨n, ?_⟩
      have := mul_right_cancel₀ Complex.two_pi_I_ne_zero hn
      rw [eq_intCast]
      exact_mod_cast this.symm
    · rintro ⟨n, hn⟩
      exact ⟨n, by rw [← hn, eq_intCast, Rat.cast_intCast]⟩
  have h2 : ∀ x : F, x ∈ codiff F ↔
      ∀ a : 𝓞 F, ψ (pairA F 0 (algebraMap F (Af F) ((a : F) * x))) = 1 := fun x => by
    rw [FractionalIdeal.mem_dual (one_ne_zero (α := FractionalIdeal (𝓞 F)⁰ F))]
    simp_rw [h1, Algebra.traceForm_apply]
    constructor
    · intro H a
      rw [mul_comm]
      exact H _ ((FractionalIdeal.mem_one_iff _).2 ⟨a, rfl⟩)
    · intro H a ha
      obtain ⟨a, rfl⟩ := (FractionalIdeal.mem_one_iff _).1 ha
      rw [mul_comm]
      exact H a
  have key : ∀ x : F, x ∈ codiff F ↔ ∀ α : Af F, (∀ v, α v ∈ v.adicCompletionIntegers F) →
      ψ (pairA F 0 (α * algebraMap F (Af F) x)) = 1 := fun x => by
    rw [h2]
    refine ⟨fun H α hα => GlobalTheory.IntDense.addChar_eq_one_of_integral F ψ hc x H α hα,
      fun H a => ?_⟩
    rw [map_mul]
    refine H _ fun v => ?_
    rw [HeightOneSpectrum.mem_adicCompletionIntegers, adele_algebraMap_apply, valued_algebraMap]
    exact v.valuation_le_one a
  have hint : ∀ α : Af F, (∀ v, α v ∈ v.adicCompletionIntegers F) → ψ (pairA F 0 α) = 1 :=
    fun α hα => by
      have := (key 1).1 (one_le_codiff (FractionalIdeal.one_mem_one _)) α hα
      rwa [map_one, mul_one] at this
  obtain ⟨x, hx⟩ := exists_sub_mem_adelicIdeal (one_ne_zero (α := FractionalIdeal (𝓞 F)⁰ F)) y
  have hx1 := mem_adelicIdeal_one_iff.1 hx
  have hx2 : y - algebraMap F (Af F) x ∈ adelicIdeal (codiff F) := by
    refine (mem_adelicIdeal_iff codiff_ne_zero).2 fun v => (hx1 v).trans ?_
    have := FractionalIdeal.count_mono F v (one_ne_zero (α := FractionalIdeal (𝓞 F)⁰ F))
      (one_le_codiff (F := F))
    rw [FractionalIdeal.count_one] at this
    rw [← exp_zero, exp_le_exp]
    omega
  have e : y = algebraMap F (Af F) x + (y - algebraMap F (Af F) x) := by ring
  rw [e, (adelicIdeal (codiff F)).add_mem_iff_left hx2, algebraMap_mem_adelicIdeal codiff_ne_zero, key]
  refine forall_congr' fun α => forall_congr' fun hα => ?_
  rw [mul_add, char_fin_add, hint (α * (y - algebraMap F (Af F) x))
    fun v => mul_mem (hα v) (hx1 v), mul_one]

theorem not_dvd_different {p : ℕ} (hp : p.Prime) (v : HeightOneSpectrum (𝓞 F))
    (hv : (p : 𝓞 F) ∈ v.asIdeal) (h2 : (p : 𝓞 F) ∉ v.asIdeal ^ 2) :
    ¬ v.asIdeal ∣ differentIdeal ℤ (𝓞 F) := by
  have hp' : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  have hmax : (Ideal.span {(p : ℤ)}).IsMaximal :=
    PrincipalIdealRing.isMaximal_of_irreducible hp'.irreducible
  have hmap : Ideal.map (algebraMap ℤ (𝓞 F)) (Ideal.span {(p : ℤ)}) = Ideal.span {((p : ℕ) : 𝓞 F)} := by
    rw [Ideal.map_span]; simp
  have hle : Ideal.map (algebraMap ℤ (𝓞 F)) (Ideal.span {(p : ℤ)}) ≤ v.asIdeal := by
    rw [hmap, Ideal.span_le]; simpa using hv
  have := v.isPrime
  have : v.asIdeal.LiesOver (Ideal.span {(p : ℤ)}) :=
    ⟨hmax.eq_of_le (Ideal.comap_ne_top _ v.isPrime.ne_top) (Ideal.map_le_iff_le_comap.mp hle)⟩
  have hb : Ideal.span {(p : ℤ)} ≠ ⊥ := by simpa using hp.ne_zero
  rw [not_dvd_differentIdeal_iff]
  apply Ideal.ramificationIdx_eq_one_iff.1
  rw [← Ideal.ramificationIdx'_eq_ramificationIdx (Ideal.span {(p : ℤ)}) v.asIdeal hb]
  by_contra hne
  rw [← ne_eq, Ideal.ramificationIdx'_ne_one_iff hle, hmap, Ideal.span_le] at hne
  exact h2 (by simpa using hne)

theorem count_codiff_eq_zero (v : HeightOneSpectrum (𝓞 F)) (h : ¬ v.asIdeal ∣ differentIdeal ℤ (𝓞 F)) :
    FractionalIdeal.count F v (codiff F) = 0 := by
  have hD : ((differentIdeal ℤ (𝓞 F) : Ideal (𝓞 F)) : FractionalIdeal (𝓞 F)⁰ F) = (codiff F)⁻¹ :=
    coeIdeal_differentIdeal ℤ ℚ F (𝓞 F)
  have h0 : differentIdeal ℤ (𝓞 F) ≠ 0 := differentIdeal_ne_bot
  have h1 := FractionalIdeal.count_coe F v h0
  rw [hD, FractionalIdeal.count_inv,
    not_not.1 (mt (Associates.count_ne_zero_iff_dvd h0 v.irreducible).1 h)] at h1
  simpa using h1

theorem not_mem_sq_of_ext {E : Type} [Field E] [NumberField E] [Algebra F E] {p : ℕ}
    (h : ∀ w : HeightOneSpectrum (𝓞 E), (p : 𝓞 E) ∈ w.asIdeal → (p : 𝓞 E) ∉ w.asIdeal ^ 2)
    (v : HeightOneSpectrum (𝓞 F)) : (p : 𝓞 F) ∉ v.asIdeal ^ 2 := by
  intro hv
  have := v.isMaximal
  obtain ⟨Q, hQ, hQv⟩ := Ideal.exists_maximal_ideal_liesOver_of_isIntegral (S := 𝓞 E) v.asIdeal
  have hb : Q ≠ ⊥ := Ideal.ne_bot_of_liesOver_of_ne_bot v.ne_bot Q
  have hle : v.asIdeal.map (algebraMap (𝓞 F) (𝓞 E)) ≤ Q :=
    Ideal.map_le_iff_le_comap.2 hQv.over.le
  have h1 := Ideal.mem_map_of_mem (algebraMap (𝓞 F) (𝓞 E)) hv
  rw [Ideal.map_pow, map_natCast] at h1
  have h2 : (p : 𝓞 E) ∈ Q ^ 2 := Ideal.pow_right_mono hle 2 h1
  exact h ⟨Q, hQ.isPrime, hb⟩ (Ideal.pow_le_self two_ne_zero h2) h2

theorem psiUnramAt_of_splitsCompletely : ∀ (D : D7) (p : ℕ) (ψ : AddChar (AF D.host.F) ℂ),
    GlobalTheory.IndefiniteRowSideFullHecke.IteratedLiftChains.SplitsCompletely D p → IsStdChar D ψ (-1) →
    ∀ v : HeightOneSpectrum (𝓞 D.host.F), (p : 𝓞 D.host.F) ∈ v.asIdeal → GlobalTheory.IndefiniteRowSideFullHecke.IteratedLiftChains.PsiUnramAt ψ v := by
  intro D p ψ hp hψ v hv α hα
  have hc := count_codiff_eq_zero v
    (not_dvd_different hp.1 v hv (not_mem_sq_of_ext (fun w hw => (hp.2 w hw).2) v))
  have h := mem_adelicIdeal_codiff_iff hψ.1.1 (GlobalTheory.StdRat.stdChar_fin_rat D ψ hψ) α
  have h' : (∀ β ∈ Formalism.MainNotions.StandardLattice.intAf D.host.F, ψ (pairA D.host.F 0 (α * β)) = 1) ↔
      α ∈ adelicIdeal (codiff D.host.F) := by
    rw [h]
    exact forall_congr' fun β => by rw [mul_comm]; rfl
  rw [h', mem_adelicIdeal_iff codiff_ne_zero, HeightOneSpectrum.mem_adicCompletionIntegers]
  constructor
  · intro H
    have := H v
    rwa [hc, neg_zero, exp_zero] at this
  · intro H w
    by_cases hw : w = v
    · subst hw
      rw [hc, neg_zero, exp_zero]
      exact H
    · have h0 : α w = 0 := hα w hw
      rw [h0, map_zero]
      exact zero_le

end GlobalTheory.SplitUnram

end
