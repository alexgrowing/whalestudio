import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HasDivPlace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PowEqPowOfModEqSim
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHarrisTaylorObjectPullbackBis
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsFrobGBaseChange
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AV GlobalTheory.AV.AbVar GlobalTheory.PDivGroup GlobalTheory.Dieu GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKMid GlobalTheory.LKGeo GlobalTheory.LKRes
open ReciprocityTheory.DiscreteGroups.LocalClassField
open scoped TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.LKGeo.LatDiv

variable {p : ℕ} [Fact p.Prime]

def intAf (p : ℕ) : AddSubgroup (AfP p) where
  carrier := {a | IsIntAf a}
  zero_mem' := fun v => by simp
  add_mem' := fun ha hb v => by rw [map_add]; exact add_mem (ha v) (hb v)
  neg_mem' := fun ha v => by rw [map_neg]; exact neg_mem (ha v)

def extF (D : Datum p) (f : D.La →ₗ[ℤ] ℤ) : AfP p ⊗[ℚ] VQ D →ₗ[AfP p] AfP p :=
  LinearMap.liftBaseChange (AfP p)
    ((Algebra.linearMap ℚ (AfP p)) ∘ₗ LinearMap.liftBaseChange ℚ ((Algebra.linearMap ℤ ℚ) ∘ₗ f))

theorem extF_tmul (D : Datum p) (f : D.La →ₗ[ℤ] ℤ) (a : AfP p) (x : D.La) :
    extF D f (a ⊗ₜ ((1 : ℚ) ⊗ₜ x)) = a * ((f x : ℤ) : AfP p) := by
  simp [extF, LinearMap.liftBaseChange_tmul, Algebra.smul_def]

theorem extF_mem (D : Datum p) (f : D.La →ₗ[ℤ] ℤ) {w : AfP p ⊗[ℚ] VQ D} (hw : w ∈ LaHat D) :
    extF D f w ∈ intAf p := by
  induction hw using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨a, x, ha, rfl⟩ := hz
    intro v
    rw [extF_tmul, map_mul, map_intCast]
    exact mul_mem (ha v) (intCast_mem _ _)
  | zero => simpa using (intAf p).zero_mem
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | neg x _ hx => rw [map_neg]; exact neg_mem hx

theorem int_dvd (D : Datum p) (f : D.La →ₗ[ℤ] ℤ) (x : D.La) (n : ℕ) (hn : 0 < n) (hnp : n.Coprime p)
    (w : AfP p ⊗[ℚ] VQ D) (hw : w ∈ LaHat D) (h : inAf D x = n • w) : (n : ℤ) ∣ f x := by
  have hb := extF_mem D f hw
  have e : ((f x : ℤ) : AfP p) = (n : AfP p) * extF D f w := by
    have := congrArg (extF D f) h
    rw [inAf, extF_tmul, _root_.one_mul, _root_.map_nsmul, nsmul_eq_mul] at this
    exact this
  set q : ℚ := (f x : ℚ) / n with hq
  have hn0 : (n : ℚ) ≠ 0 := by exact_mod_cast hn.ne'
  have hval : ∀ v : IsDedekindDomain.HeightOneSpectrum ℤ, v.valuation ℚ q ≤ 1 := by
    intro v
    by_cases hv : v.asIdeal = Ideal.span {(p : ℤ)}
    · have h1 : v.valuation ℚ (n : ℚ) = 1 := by
        have : (n : ℚ) = algebraMap ℤ ℚ (n : ℤ) := by simp
        rw [this, IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap,
          IsDedekindDomain.HeightOneSpectrum.intValuation_eq_one_iff, hv, Ideal.mem_span_singleton]
        intro hd
        have : (p : ℤ) ∣ (n : ℤ) := hd
        have h2 : p ∣ n := by exact_mod_cast this
        have h3 : p ∣ Nat.gcd n p := Nat.dvd_gcd h2 dvd_rfl
        rw [hnp] at h3
        exact (Fact.out : p.Prime).one_lt.ne' (Nat.dvd_one.1 h3)
      have h2 : v.valuation ℚ ((f x : ℤ) : ℚ) ≤ 1 := by
        rw [← eq_intCast (algebraMap ℤ ℚ), IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap]
        exact v.intValuation_le_one _
      rw [hq, map_div₀, h1, div_one]; exact h2
    · let v' : AwayP p := ⟨v, hv⟩
      have hbv := hb v'
      have e2 := congrArg (AfP.eval v') e
      rw [map_intCast, map_mul, map_natCast] at e2
      have hqv : algebraMap ℚ (v.adicCompletion ℚ) q = AfP.eval v' (extF D f w) := by
        have hn' : algebraMap ℚ (v.adicCompletion ℚ) (n : ℚ) ≠ 0 := (map_ne_zero _).2 hn0
        have : algebraMap ℚ (v.adicCompletion ℚ) q * algebraMap ℚ (v.adicCompletion ℚ) (n : ℚ) =
            ((f x : ℤ) : v.adicCompletion ℚ) := by
          rw [← map_mul, hq, div_mul_cancel₀ _ hn0, map_intCast]
        rw [← mul_left_inj' hn', this, e2, map_natCast]
        ring
      have hc : Valued.v (algebraMap ℚ (v.adicCompletion ℚ) q) = v.valuation ℚ q :=
        IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v q
      rw [← hc, hqv]
      exact (IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).1 hbv
  obtain ⟨k, hk⟩ := IsDedekindDomain.HeightOneSpectrum.mem_integers_of_valuation_le_one ℚ q hval
  refine ⟨k, ?_⟩
  have : ((k : ℤ) : ℚ) = (f x : ℚ) / n := by rw [← eq_intCast (algebraMap ℤ ℚ)]; exact hk.trans hq
  have h4 : ((f x : ℤ) : ℚ) = ((n : ℤ) * k : ℤ) := by
    push_cast; rw [this]; field_simp
  exact_mod_cast h4

end GlobalTheory.LKGeo.LatDiv

namespace GlobalTheory.LKGeo.LatDiv

theorem eq_nsmul_of_inAf_eq_nsmul : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (x : D.La) (n : ℕ), 0 < n → n.Coprime p →
    ∀ w ∈ LaHat D, inAf D x = n • w → ∃ z, x = n • z := by
  intro p _ D x n hn hnp w hw h
  haveI := D.freeLa
  haveI := D.finLa
  let b := Module.Free.chooseBasis ℤ D.La
  have hd : ∀ i, (n : ℤ) ∣ b.coord i x := fun i => int_dvd D (b.coord i) x n hn hnp w hw h
  choose c hc using hd
  refine ⟨∑ i, c i • b i, ?_⟩
  conv_lhs => rw [← b.sum_repr x]
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  have : b.repr x i = (n : ℤ) * c i := hc i
  rw [this, mul_smul]
  exact Nat.cast_smul_eq_nsmul ℤ n _

end GlobalTheory.LKGeo.LatDiv
