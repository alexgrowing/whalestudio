import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HasDivPlace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PowEqPowOfModEqSim
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SimilitudeActionAdelicLatticeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeVectorBundlePullback
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ValuedIntCastLeIff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeCompletionEqLatticeVectorAddNsmul
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DualLatticeDegreeNeg
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlatHermUnitConstant
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEqNsmulOfActs
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HopfOrderPullbackAlongHom
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AV GlobalTheory.AV.AbVar GlobalTheory.PDivGroup GlobalTheory.Dieu GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKMid GlobalTheory.LKGeo GlobalTheory.LKRes
open ReciprocityTheory.DiscreteGroups.LocalClassField
open scoped TensorProduct

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.LKGeo.DenEnd

variable {p : ℕ} [Fact p.Prime]

theorem inAf_mem (D : Datum p) (x : D.La) : inAf D x ∈ LaHat D :=
  AddSubgroup.subset_closure ⟨1, x, fun v => by rw [map_one]; exact one_mem _, rfl⟩

theorem smul_mem (D : Datum p) {a : AfP p} (ha : IsIntAf a) {v : AfP p ⊗[ℚ] VQ D} (hv : v ∈ LaHat D) :
    a • v ∈ LaHat D := by
  induction hv using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨c, x, hc, rfl⟩ := hz
    refine AddSubgroup.subset_closure ⟨a * c, x, fun w => ?_, ?_⟩
    · rw [map_mul]; exact mul_mem (ha w) (hc w)
    · rw [TensorProduct.smul_tmul', smul_eq_mul]
  | zero => rw [smul_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [smul_add]; exact add_mem hx hy
  | neg x _ hx => rw [smul_neg]; exact neg_mem hx

theorem exists_nsmul_mem (D : Datum p) (v : AfP p ⊗[ℚ] VQ D) : ∃ d : ℕ, 0 < d ∧ d • v ∈ LaHat D := by
  have hadd : ∀ u w : AfP p ⊗[ℚ] VQ D, (∃ d : ℕ, 0 < d ∧ d • u ∈ LaHat D) → (∃ d : ℕ, 0 < d ∧ d • w ∈ LaHat D) →
      ∃ d : ℕ, 0 < d ∧ d • (u + w) ∈ LaHat D := by
    rintro u w ⟨d, hd, hu⟩ ⟨e, he, hw⟩
    refine ⟨d * e, Nat.mul_pos hd he, ?_⟩
    have : (d * e) • (u + w) = e • (d • u) + d • (e • w) := by
      rw [smul_add, smul_smul, smul_smul, mul_comm e d]
    rw [this]
    exact add_mem (nsmul_mem hu _) (nsmul_mem hw _)
  induction v using TensorProduct.induction_on with
  | zero => exact ⟨1, one_pos, by rw [smul_zero]; exact zero_mem _⟩
  | add u w hu hw => exact hadd u w hu hw
  | tmul a w =>
    induction w using TensorProduct.induction_on with
    | zero => exact ⟨1, one_pos, by rw [TensorProduct.tmul_zero, smul_zero]; exact zero_mem _⟩
    | add u w hu hw => rw [TensorProduct.tmul_add]; exact hadd _ _ hu hw
    | tmul q x =>
      obtain ⟨d, hd, h⟩ := GlobalTheory.DenAway.exists_nat_adele (q • a)
      refine ⟨d, hd, AddSubgroup.subset_closure ⟨(d : AfP p) * (q • a), x, h, ?_⟩⟩
      have e : q ⊗ₜ[ℤ] x = q • ((1 : ℚ) ⊗ₜ[ℤ] x) := by
        rw [TensorProduct.smul_tmul', smul_eq_mul, _root_.mul_one]
      rw [e, ← TensorProduct.smul_tmul, TensorProduct.smul_tmul', nsmul_eq_mul]

theorem isIntAf_inv : IsIntAf (algebraMap ℚ (AfP p) (p : ℚ)⁻¹) := by
  intro v
  rw [AlgHom.commutes, IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers]
  have h1 : v.1.valuation ℚ (algebraMap ℤ ℚ (p : ℤ)) = 1 := by
    refine le_antisymm (v.1.valuation_le_one _) (not_lt.1 fun h => v.2 ?_)
    rw [IsDedekindDomain.HeightOneSpectrum.valuation_lt_one_iff_mem] at h
    have hm : (Ideal.span {(p : ℤ)}).IsMaximal :=
      PrincipalIdealRing.isMaximal_of_irreducible (Nat.prime_iff_prime_int.mp Fact.out).irreducible
    exact (hm.eq_of_le v.1.isPrime.ne_top ((Ideal.span_singleton_le_iff_mem _).2 h)).symm
  have h2 : Valued.v (algebraMap ℚ (v.1.adicCompletion ℚ) (p : ℚ)⁻¹) = v.1.valuation ℚ (p : ℚ)⁻¹ :=
    IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v.1 _
  rw [h2, map_inv₀]
  simp only [eq_intCast, Int.cast_natCast] at h1
  rw [h1, inv_one]

theorem exists_coprime_nsmul_mem (D : Datum p) (v : AfP p ⊗[ℚ] VQ D) :
    ∃ t : ℕ, 0 < t ∧ t.Coprime p ∧ t • v ∈ LaHat D := by
  obtain ⟨d, hd, h⟩ := exists_nsmul_mem D v
  obtain ⟨k, t, ht, hdt⟩ := Nat.exists_eq_pow_mul_and_not_dvd hd.ne' p (Fact.out : p.Prime).ne_one
  have ht0 : 0 < t := Nat.pos_of_ne_zero fun h => ht (h ▸ dvd_zero p)
  refine ⟨t, ht0, ((Nat.Prime.coprime_iff_not_dvd Fact.out).2 ht).symm, ?_⟩
  have hint : IsIntAf (algebraMap ℚ (AfP p) (p : ℚ)⁻¹ ^ k) := fun u => by
    rw [map_pow]; exact pow_mem (isIntAf_inv u) k
  have hm := smul_mem D hint h
  have hp : (p : ℚ) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  convert hm using 1
  rw [hdt, ← map_pow, algebraMap_smul, ← Nat.cast_smul_eq_nsmul ℚ, ← Nat.cast_smul_eq_nsmul ℚ, smul_smul]
  congr 1
  push_cast
  rw [inv_pow, ← _root_.mul_assoc, inv_mul_cancel₀ (pow_ne_zero _ hp), _root_.one_mul]

theorem exists_coprime_nsmul_map_mem : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p)
    (A : Module.End (AfP p) (AfP p ⊗[ℚ] VQ D)), ∃ j : ℕ, 0 < j ∧ j.Coprime p ∧ ∀ v ∈ LaHat D, j • A v ∈ LaHat D := by
  intro p _ D A
  have := D.freeLa
  have := D.finLa
  let b := Module.Free.chooseBasis ℤ D.La
  choose t ht0 htc ht using fun i => exists_coprime_nsmul_mem D (A (inAf D (b i)))
  refine ⟨∏ i, t i, Finset.prod_pos fun i _ => ht0 i, Nat.Coprime.prod_left fun i _ => htc i, ?_⟩
  have hbase : ∀ x : D.La, (∏ i, t i) • A (inAf D x) ∈ LaHat D := by
    intro x
    have hx : x ∈ Submodule.span ℤ (Set.range b) := by rw [b.span_eq]; trivial
    induction hx using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨i, rfl⟩ := hy
      obtain ⟨k, hk⟩ := Finset.dvd_prod_of_mem t (Finset.mem_univ i)
      rw [hk, mul_comm, mul_smul]
      exact nsmul_mem (ht i) k
    | zero =>
      have : inAf D 0 = 0 := by simp [inAf]
      rw [this, map_zero, smul_zero]; exact zero_mem _
    | add y z _ _ hy hz =>
      have : inAf D (y + z) = inAf D y + inAf D z := by simp only [inAf, TensorProduct.tmul_add]
      rw [this, map_add, smul_add]; exact add_mem hy hz
    | smul c y _ hy =>
      have : inAf D (c • y) = c • inAf D y := by
        simp only [inAf, TensorProduct.tmul_smul]
      rw [this, map_zsmul, smul_comm]; exact zsmul_mem hy c
  intro v hv
  induction hv using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨a, x, ha, rfl⟩ := hz
    have e : a ⊗ₜ[ℚ] ((1 : ℚ) ⊗ₜ[ℤ] x) = a • inAf D x := by
      rw [inAf, TensorProduct.smul_tmul', smul_eq_mul, _root_.mul_one]
    rw [e, map_smul, smul_comm]
    exact smul_mem D ha (hbase x)
  | zero => rw [map_zero, smul_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [map_add, smul_add]; exact add_mem hx hy
  | neg x _ hx => rw [map_neg, smul_neg]; exact neg_mem hx

end GlobalTheory.LKGeo.DenEnd
