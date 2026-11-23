import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.CentralInvolutionRing
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ConjTupRefl
import Development.AbelianVarietyTheory.Definitions.Divisors.GenReads
import Development.AbelianVarietyTheory.Definitions.ThetaValues.ExistsRootNotMem
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneMapOfOfExtends
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ThExprUniqOfChartIndep2
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GaussGLZero
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NatCastNotMemOfPrimeNe
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Classical

namespace GlobalTheory.ChiUnit

open GlobalTheory.IndefiniteRowSideFullHecke.CentralInvolutionRing

theorem unitOff_mul {N : ℕ} {u v : ℂ} (hu : UnitOff N u) (hv : UnitOff N v) : UnitOff N (u * v) := by
  obtain ⟨hu0, n, hn1, hn2⟩ := hu
  obtain ⟨hv0, m, hm1, hm2⟩ := hv
  refine ⟨mul_ne_zero hu0 hv0, n + m, ?_, ?_⟩
  · have e : (N : ℂ) ^ (n + m) * (u * v) = ((N : ℂ) ^ n * u) * ((N : ℂ) ^ m * v) := by rw [pow_add]; ring
    rw [e]; exact hn1.mul hm1
  · have e : (N : ℂ) ^ (n + m) * (u * v)⁻¹ = ((N : ℂ) ^ n * u⁻¹) * ((N : ℂ) ^ m * v⁻¹) := by rw [pow_add, mul_inv]; ring
    rw [e]; exact hn2.mul hm2

theorem unitOff_inv {N : ℕ} {u : ℂ} (hu : UnitOff N u) : UnitOff N u⁻¹ := by
  obtain ⟨hu0, n, hn1, hn2⟩ := hu
  exact ⟨inv_ne_zero hu0, n, hn2, by rw [inv_inv]; exact hn1⟩

theorem unitOff_one (N : ℕ) : UnitOff N 1 :=
  ⟨one_ne_zero, 0, by simpa using isIntegral_one, by simpa using isIntegral_one⟩

theorem unitOff_pow {N : ℕ} {u : ℂ} (hu : UnitOff N u) (k : ℕ) : UnitOff N (u ^ k) := by
  induction k with
  | zero => simpa using unitOff_one N
  | succ k ih => rw [pow_succ]; exact unitOff_mul ih hu

theorem unitOff_zpow {N : ℕ} {u : ℂ} (hu : UnitOff N u) (k : ℤ) : UnitOff N (u ^ k) := by
  rcases Int.eq_nat_or_neg k with ⟨m, rfl | rfl⟩
  · rw [zpow_natCast]; exact unitOff_pow hu m
  · rw [_root_.zpow_neg, zpow_natCast]; exact unitOff_inv (unitOff_pow hu m)

theorem unitOff_prod {N : ℕ} {ι : Type*} (s : Finset ι) (f : ι → ℂ) (h : ∀ i ∈ s, UnitOff N (f i)) :
    UnitOff N (∏ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using unitOff_one N
  | insert a s ha ih =>
    rw [Finset.prod_insert ha]
    exact unitOff_mul (h a (Finset.mem_insert_self a s)) (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

theorem unitOff_conj {N : ℕ} {u : ℂ} (hu : UnitOff N u) : UnitOff N (starRingEnd ℂ u) := by
  obtain ⟨hu0, n, hn1, hn2⟩ := hu
  refine ⟨(map_ne_zero _).2 hu0, n, ?_, ?_⟩
  · have := hn1.map (RingHom.toIntAlgHom (starRingEnd ℂ))
    simpa [map_mul, map_pow, map_natCast] using this
  · have := hn2.map (RingHom.toIntAlgHom (starRingEnd ℂ))
    simpa [map_mul, map_pow, map_natCast, map_inv₀] using this

theorem unitOff_of_pow {N : ℕ} {u : ℂ} {k : ℕ} (hk : 0 < k) (hu : UnitOff N (u ^ k)) : UnitOff N u := by
  obtain ⟨hu0, n, hn1, hn2⟩ := hu
  have hN : IsIntegral ℤ ((N : ℂ) ^ (n * (k - 1))) := by
    have : IsIntegral ℤ (N : ℂ) := by simpa using isIntegral_algebraMap (R := ℤ) (A := ℂ) (x := (N : ℤ))
    exact this.pow _
  refine ⟨fun h => hu0 (by rw [h, zero_pow hk.ne']), n, ?_, ?_⟩
  · refine IsIntegral.of_pow hk ?_
    have e : ((N : ℂ) ^ n * u) ^ k = (N : ℂ) ^ (n * (k - 1)) * ((N : ℂ) ^ n * u ^ k) := by
      rw [mul_pow, ← pow_mul, ← mul_assoc, ← pow_add]
      congr 2
      obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_lt hk
      simp only [Nat.add_sub_cancel, zero_add]
      ring
    rw [e]; exact hN.mul hn1
  · refine IsIntegral.of_pow hk ?_
    have e : ((N : ℂ) ^ n * u⁻¹) ^ k = (N : ℂ) ^ (n * (k - 1)) * ((N : ℂ) ^ n * (u ^ k)⁻¹) := by
      rw [mul_pow, ← pow_mul, ← mul_assoc, ← pow_add, inv_pow]
      congr 2
      obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_lt hk
      simp only [Nat.add_sub_cancel, zero_add]
      ring
    rw [e]; exact hN.mul hn2

theorem unitOff_of_pow_eq_one (N : ℕ) {u : ℂ} {k : ℕ} (hk : 0 < k) (hu : u ^ k = 1) : UnitOff N u :=
  unitOff_of_pow hk (by rw [hu]; exact unitOff_one N)

theorem unitOff_of_mul_eq {N m : ℕ} {a b : ℂ} (ha : IsIntegral ℤ a) (hb : IsIntegral ℤ b)
    (hab : a * b = (N : ℂ) ^ m) (hN : N ≠ 0) : UnitOff N a := by
  have hNm : (N : ℂ) ^ m ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.2 hN)
  have ha0 : a ≠ 0 := fun h => hNm (by rw [← hab, h, zero_mul])
  refine ⟨ha0, m, ?_, ?_⟩
  · have : IsIntegral ℤ ((N : ℂ) ^ m) := by
      have : IsIntegral ℤ (N : ℂ) := by simpa using isIntegral_algebraMap (R := ℤ) (A := ℂ) (x := (N : ℤ))
      exact this.pow _
    exact this.mul ha
  · have e : (N : ℂ) ^ m * a⁻¹ = b := by rw [← hab]; field_simp
    rw [e]; exact hb

end GlobalTheory.ChiUnit

namespace GlobalTheory.ChiUnit
open GlobalTheory.IndefiniteRowSideFullHecke.CentralInvolutionRing

theorem LR {L : Type} [Field L] [NumberField L] (χ : Formalism.L2.Host.HChar L) (n : ℕ) (h : χ ^ n = 1)
    (w : IsDedekindDomain.HeightOneSpectrum (𝓞 L)) (k : Lˣ) : (χ.locK w k) ^ n = 1 := by
  have e : (χ ^ n).locK w k = (χ.locK w k) ^ n := by
    simp [Formalism.L2.Host.HChar.locK, Formalism.L2.Host.HChar.loc]
  rw [← e, h]
  simp [Formalism.L2.Host.HChar.locK, Formalism.L2.Host.HChar.loc]

theorem locK_eq_val {L : Type} [Field L] [NumberField L] (χ : Formalism.L2.Host.HChar L)
    {w : IsDedekindDomain.HeightOneSpectrum (𝓞 L)} (hw : χ.UnrAt w) (k : Lˣ) (a : 𝓞 L) (hk : (k : L) = a)
    (h1 : a ∈ w.asIdeal) (h2 : a ∉ w.asIdeal ^ 2) : χ.locK w k = χ.val w :=
  χ.val_eq hw _ (by
    unfold Formalism.L2.Host.IsUnifAt
    rw [GlobalTheory.TypeValues.val_atFin w k a hk, GlobalTheory.TypeValues.intValuation_eq_of_mem h1 h2])

end GlobalTheory.ChiUnit

namespace GlobalTheory.ChiUnit
open GlobalTheory.IndefiniteRowSideFullHecke.CentralInvolutionRing

theorem finite_ramified_places_hecke_character {D : D7} (χ : Formalism.L2.Host.HChar D.host.E)
    (h : ∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 D.host.E), (∀ k : Fin 2, ¬Formalism.L2.Host.OverP D.host (D.host.g k) v) → χ.UnrAt v) :
    {w | ¬ χ.UnrAt w}.Finite := by
  have hm : ((D.host.g 0 * D.host.g 1 : ℕ) : 𝓞 D.host.E) ≠ 0 := by
    exact_mod_cast Nat.mul_ne_zero (D.host.g_prime 0).ne_zero (D.host.g_prime 1).ne_zero
  have hI : Ideal.span {((D.host.g 0 * D.host.g 1 : ℕ) : 𝓞 D.host.E)} ≠ 0 := by
    rwa [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
  refine (Ideal.finite_factors hI).subset fun w hw => ?_
  simp only [Set.mem_setOf_eq] at hw ⊢
  rw [Ideal.dvd_span_singleton]
  by_contra hc
  refine hw (h w fun k hk => hc ?_)
  unfold Formalism.L2.Host.OverP at hk
  rw [Nat.cast_mul]
  fin_cases k
  · exact Ideal.mul_mem_right _ _ hk
  · exact Ideal.mul_mem_left _ _ hk

theorem not_mem_of_prime_ne {L : Type} [Field L] [NumberField L] (w : IsDedekindDomain.HeightOneSpectrum (𝓞 L))
    {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hne : q ≠ p) (hqw : (q : 𝓞 L) ∈ w.asIdeal) : (p : 𝓞 L) ∉ w.asIdeal := by
  first
  | exact @_root_.GlobalTheory.NatCastNotMemPrimeIdeal.natCast_notMem_of_prime_ne
  | exact _root_.GlobalTheory.NatCastNotMemPrimeIdeal.natCast_notMem_of_prime_ne
  | (apply _root_.GlobalTheory.NatCastNotMemPrimeIdeal.natCast_notMem_of_prime_ne <;> assumption)
  | (intros; apply _root_.GlobalTheory.NatCastNotMemPrimeIdeal.natCast_notMem_of_prime_ne <;> assumption)
  | (intros; apply @_root_.GlobalTheory.NatCastNotMemPrimeIdeal.natCast_notMem_of_prime_ne <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.NatCastNotMemPrimeIdeal.natCast_notMem_of_prime_ne ..)

end GlobalTheory.ChiUnit
