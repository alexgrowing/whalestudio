import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.CharacterNorms.XgDefs
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.UnramifiedSplitting.SgLaws

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.RankTwoDescent UpperTheory.ConvolutionTheory.RankTwoDescent.Xg
open scoped Classical
open UpperTheory.ConvolutionTheory.R2.G (FS2 Rw nE row)
open UpperTheory.V.Af.Smo (EigAt)
open scoped ComplexOrder

private theorem psi_add (x y : A ℚ) : ψ (x + y) = ψ x * ψ y := by
  simp only [ψ, AddChar.map_add_eq_mul, Circle.coe_mul]

private theorem psi_eq_one_iff (x : A ℚ) : ψ x = 1 ↔ adelicChar ℚ x = 1 := Circle.coe_eq_one

private theorem psi_neg_of_one {x : A ℚ} (h : ψ x = 1) : ψ (-x) = 1 := by
  rw [psi_eq_one_iff] at *
  rw [AddChar.map_neg_eq_inv, h, inv_one]

private theorem psi_zsmul (m : ℤ) {x : A ℚ} (h : ψ x = 1) : ψ (m • x) = 1 := by
  rw [psi_eq_one_iff] at *
  rw [AddChar.map_zsmul_eq_zpow, h, _root_.one_zpow]

private theorem psi_nsmul (a : ℕ) (x : A ℚ) : ψ (a • x) = ψ x ^ a := by
  simp only [ψ, AddChar.map_nsmul_eq_pow, Circle.coe_pow]

private theorem psi_Oh {c : A ℚ} (hc : c ∈ Oh ℚ) : ψ c = 1 := by
  have h : c ∈ invDifferentAdeles ℚ :=
    mem_invDifferentAdeles.2 (mem_finiteInvDifferent.2 fun v =>
      mem_localInvDifferent_of_mem (hc.2 v))
  rw [psi_eq_one_iff, adelicChar_of_mem_invDifferentAdeles h, hc.1]
  simp

private theorem different_rat : differentIdeal ℤ (𝓞 ℚ) = ⊤ := by
  rw [← Ideal.absNorm_eq_one_iff, NumberField.absNorm_differentIdeal (K := ℚ), NumberField.discr_rat]
  rfl

private theorem mem_inv_iff (v : H.P ℚ) (x : H.Kv v) : x ∈ localInvDifferent v ↔ Valued.v x ≤ 1 := by
  rw [mem_localInvDifferent_iff_valued, different_rat]
  simp [FractionalIdeal.count_one]

private theorem psi_sg_eq (v : H.P ℚ) (x : H.Kv v) : ψ (H.sg v x) = (localAdelicChar ℚ v x : ℂ) := rfl

private noncomputable def eA : A ℚ := (0, 1)

private theorem fin_alg_val {K : Type} [Field K] [NumberField K] (v : H.P K) (a : K) :
    Valued.v ((algebraMap K (FiniteAdeleRing (𝓞 K) K) a) v) = v.valuation K a :=
  HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v a

private theorem nat_val (v : H.P ℚ) (n : ℕ) : Valued.v ((n : FiniteAdeleRing (𝓞 ℚ) ℚ) v) ≤ 1 := by
  have e : (n : FiniteAdeleRing (𝓞 ℚ) ℚ) v = (n : H.Kv v) := map_natCast (pLoc ℚ v) n
  rw [e]
  exact natCast_mem (v.adicCompletionIntegers ℚ) n

private theorem decomp (n : ℕ) (hn : 0 < n) {c : A ℚ} (hc : c ∈ Oh ℚ) :
    ∃ (m : ℤ) (c' : A ℚ), c' ∈ Oh ℚ ∧ c = m • eA + (n : A ℚ) * c' := by
  have hn0 : (n : ℚ) ≠ 0 := by exact_mod_cast hn.ne'
  obtain ⟨k, hk⟩ := exists_sub_mem_finiteInvDifferent (K := ℚ)
    (algebraMap ℚ (FiniteAdeleRing (𝓞 ℚ) ℚ) (n : ℚ)⁻¹ * c.2)
  obtain ⟨f, hf⟩ : ∃ f, f = algebraMap ℚ (FiniteAdeleRing (𝓞 ℚ) ℚ) (n : ℚ)⁻¹ * c.2 -
      algebraMap ℚ (FiniteAdeleRing (𝓞 ℚ) ℚ) k := ⟨_, rfl⟩
  rw [← hf] at hk
  have hfv : ∀ v : H.P ℚ, Valued.v (f v) ≤ 1 := fun v =>
    (mem_inv_iff v _).1 (mem_finiteInvDifferent.1 hk v)
  have hnn : (n : FiniteAdeleRing (𝓞 ℚ) ℚ) * algebraMap ℚ (FiniteAdeleRing (𝓞 ℚ) ℚ) (n : ℚ)⁻¹ = 1 := by
    rw [← map_natCast (algebraMap ℚ (FiniteAdeleRing (𝓞 ℚ) ℚ)) n, ← map_mul, mul_inv_cancel₀ hn0, map_one]
  have key : c.2 = (n : FiniteAdeleRing (𝓞 ℚ) ℚ) * f + algebraMap ℚ (FiniteAdeleRing (𝓞 ℚ) ℚ) ((n : ℚ) * k) := by
    rw [hf, map_mul, map_natCast, mul_sub, ← mul_assoc, hnn, one_mul, sub_add_cancel]
  have hint : ∀ v : H.P ℚ, v.valuation ℚ ((n : ℚ) * k) ≤ 1 := by
    intro v
    have e : (algebraMap ℚ (FiniteAdeleRing (𝓞 ℚ) ℚ) ((n : ℚ) * k)) v = c.2 v - (n : FiniteAdeleRing (𝓞 ℚ) ℚ) v * f v := by
      have h2 : c.2 v = (n : FiniteAdeleRing (𝓞 ℚ) ℚ) v * f v + (algebraMap ℚ (FiniteAdeleRing (𝓞 ℚ) ℚ) ((n : ℚ) * k)) v :=
        congrArg (fun x : FiniteAdeleRing (𝓞 ℚ) ℚ => x v) key
      rw [h2]
      ring
    rw [← fin_alg_val, e]
    refine (Valuation.map_sub _ _ _).trans (max_le (hc.2 v) ?_)
    rw [map_mul]
    exact mul_le_one' (nat_val v n) (hfv v)
  obtain ⟨r, hr⟩ := HeightOneSpectrum.mem_integers_of_valuation_le_one ℚ _ hint
  obtain ⟨m, hm⟩ := IsIntegrallyClosed.isIntegral_iff.1 (r.2 : IsIntegral ℤ (r : ℚ))
  have hmk : (n : ℚ) * k = (m : ℚ) := by
    exact hr.symm.trans (hm.symm.trans (eq_intCast (algebraMap ℤ ℚ) m))
  refine ⟨m, ((0, f) : InfiniteAdeleRing ℚ × FiniteAdeleRing (𝓞 ℚ) ℚ), ⟨rfl, hfv⟩, ?_⟩
  refine Prod.ext ?_ ?_
  · change c.1 = m • (0 : InfiniteAdeleRing ℚ) + (n : A ℚ).1 * 0
    rw [hc.1]
    simp
  · change c.2 = m • (1 : FiniteAdeleRing (𝓞 ℚ) ℚ) + (n : FiniteAdeleRing (𝓞 ℚ) ℚ) * f
    rw [key, hmk, map_intCast, zsmul_one, add_comm]

private theorem local_good (v : H.P ℚ) (x : H.Kv v)
    (h : ∀ c : H.Kv v, Valued.v c ≤ 1 → ψ (H.sg v (c * x)) = 1) : Valued.v x ≤ 1 := by
  refine (mem_inv_iff v x).1 ((forall_localAdelicChar_mul_eq_one_iff v x).1 fun a ha => ?_)
  have := h a ha
  rw [psi_sg_eq] at this
  exact Circle.coe_eq_one.1 this

private theorem sg_oh (v : H.P ℚ) (c : H.Kv v) (hc : Valued.v c ≤ 1) : H.sg v c ∈ Oh ℚ := by
  obtain ⟨-, -, hcp, -, -, -, -, hs, -, -⟩ := H.sgLaws ℚ v
  refine ⟨(hs c).1, fun w => ?_⟩
  by_cases h : w = v
  · subst h
    have : (H.sg w c).2 w = c := hcp c
    rw [this]
    exact hc
  · rw [(hs c).2 w h, map_zero]
    exact zero_le'

private theorem oh_nat_mul (n : ℕ) {c : A ℚ} (hc : c ∈ Oh ℚ) : (n : A ℚ) * c ∈ Oh ℚ := by
  refine ⟨?_, fun v => ?_⟩
  · change (n : A ℚ).1 * c.1 = 0
    rw [hc.1, mul_zero]
  · change Valued.v ((n : FiniteAdeleRing (𝓞 ℚ) ℚ) v * c.2 v) ≤ 1
    rw [map_mul]
    exact mul_le_one' (nat_val v n) (hc.2 v)

private theorem eA_mem : eA ∈ Oh ℚ := by
  refine ⟨rfl, fun v => ?_⟩
  change Valued.v (1 : H.Kv v) ≤ 1
  rw [map_one]

private theorem eA_mul {c : A ℚ} (hc : c.1 = 0) : eA * c = c := by
  refine Prod.ext ?_ ?_
  · change 0 * c.1 = c.1
    rw [hc, mul_zero]
  · change 1 * c.2 = c.2
    rw [one_mul]

private theorem L_iota (L : ℕ) (hL : 0 < L) : (L : A ℚ) * iota L = eA := by
  have hL0 : (L : ℚ) ≠ 0 := by exact_mod_cast hL.ne'
  refine Prod.ext ?_ ?_
  · change (L : A ℚ).1 * 0 = 0
    rw [mul_zero]
  · change (L : FiniteAdeleRing (𝓞 ℚ) ℚ) * algebraMap ℚ (FiniteAdeleRing (𝓞 ℚ) ℚ) (L : ℚ)⁻¹ = 1
    rw [← map_natCast (algebraMap ℚ (FiniteAdeleRing (𝓞 ℚ) ℚ)) L, ← map_mul, mul_inv_cancel₀ hL0, map_one]

private theorem psi_mul_of_one (L M : ℕ) (hL : 0 < L) (hM : 0 < M) (y : A ℚ)
    (hy : ∀ c ∈ Oh ℚ, ψ (y * ((M : A ℚ) * c)) = 1) (hz : ψ (iota L * (1 - y)) = 1)
    {c : A ℚ} (hc : c ∈ Oh ℚ) : ψ (c * (iota L * (1 - y))) = 1 := by
  obtain ⟨m, c', hc', e⟩ := decomp (L * M) (Nat.mul_pos hL hM) hc
  have hw : (iota L * (1 - y)).1 = 0 := by
    change (0 : InfiniteAdeleRing ℚ) * (1 - y).1 = 0
    rw [zero_mul]
  have e2 : c * (iota L * (1 - y)) =
      m • (iota L * (1 - y)) + ((M : A ℚ) * c' + -(y * ((M : A ℚ) * c'))) := by
    have h1 : ((L * M : ℕ) : A ℚ) * c' * (iota L * (1 - y)) = (M : A ℚ) * c' - y * ((M : A ℚ) * c') := by
      have h2 : ((L * M : ℕ) : A ℚ) * c' * (iota L * (1 - y)) = (M : A ℚ) * (eA * c') * (1 - y) := by
        rw [← L_iota L hL]
        push_cast
        ring
      rw [h2, eA_mul hc'.1]
      ring
    rw [e, add_mul, h1, zsmul_eq_mul, mul_assoc, ← zsmul_eq_mul, eA_mul hw, sub_eq_add_neg ((M : A ℚ) * c')]
  rw [e2, psi_add, psi_add, psi_zsmul m hz, psi_Oh (oh_nat_mul M hc'), psi_neg_of_one (hy c' hc')]
  simp

private theorem val_iff (L : ℕ) (hL : 0 < L) (y : A ℚ) (v : H.P ℚ) :
    Dv L v (y - 1) ↔ Valued.v (H.cp v (iota L * (1 - y))) ≤ 1 := by
  have hab : Valued.v (L : H.Kv v) * Valued.v (H.cp v (iota L)) = 1 := by
    have e : (L : H.Kv v) * H.cp v (iota L) = 1 := by
      have h1 : H.cp v ((L : A ℚ) * iota L) = 1 := by
        rw [L_iota L hL]
        rfl
      rwa [map_mul, map_natCast] at h1
    rw [← map_mul, e, map_one]
  have hx : Valued.v (H.cp v (iota L * (1 - y))) =
      Valued.v (H.cp v (iota L)) * Valued.v (H.cp v (y - 1)) := by
    rw [map_mul, map_mul, ← neg_sub y 1, map_neg, Valuation.map_neg]
  rw [hx]
  unfold Dv
  constructor
  · intro h
    calc _ ≤ Valued.v (H.cp v (iota L)) * Valued.v (L : H.Kv v) := mul_le_mul' le_rfl h
      _ = 1 := by rw [mul_comm, hab]
  · intro h
    calc Valued.v (H.cp v (y - 1)) =
        Valued.v (L : H.Kv v) * (Valued.v (H.cp v (iota L)) * Valued.v (H.cp v (y - 1))) := by
          rw [← mul_assoc, hab, one_mul]
      _ ≤ Valued.v (L : H.Kv v) * 1 := mul_le_mul' le_rfl h
      _ = _ := mul_one _

theorem UpperTheory.sum_range_ratAdeleChar_iota_mul_one_sub_eq_ite :
    ∀ (L M : ℕ), 0 < L → 0 < M → ∀ y : A ℚ, (∀ c ∈ Oh ℚ, ψ (y * ((M : A ℚ) * c)) = 1) → ∑ a ∈ Finset.range (L * M), ψ ((a : A ℚ) * iota L * (1 - y)) = if ∀ v : H.P ℚ, Dv L v (y - 1) then ((L * M : ℕ) : ℂ) else 0 := by
  intro L M hL hM y hy
  have hsum : ∀ a : ℕ, ψ ((a : A ℚ) * iota L * (1 - y)) = ψ (iota L * (1 - y)) ^ a := by
    intro a
    rw [mul_assoc, ← nsmul_eq_mul, psi_nsmul]
  simp only [hsum]
  have hzn : ψ (iota L * (1 - y)) ^ (L * M) = 1 := by
    rw [← psi_nsmul, nsmul_eq_mul]
    have e : ((L * M : ℕ) : A ℚ) * (iota L * (1 - y)) =
        (M : A ℚ) * eA + -(y * ((M : A ℚ) * eA)) := by
      have h1 : ((L * M : ℕ) : A ℚ) * (iota L * (1 - y)) =
          (M : A ℚ) * ((L : A ℚ) * iota L) * (1 - y) := by
        push_cast
        ring
      rw [h1, L_iota L hL]
      ring
    rw [e, psi_add, psi_Oh (oh_nat_mul M eA_mem), psi_neg_of_one (hy eA eA_mem), one_mul]
  have hw1 : (iota L * (1 - y)).1 = 0 := by
    change (0 : InfiniteAdeleRing ℚ) * (1 - y).1 = 0
    rw [zero_mul]
  split_ifs with h
  · have hz : ψ (iota L * (1 - y)) = 1 :=
      psi_Oh ⟨hw1, fun v => (val_iff L hL y v).1 (h v)⟩
    simp [hz]
  · have hz : ψ (iota L * (1 - y)) ≠ 1 := by
      intro hz
      refine h fun v => (val_iff L hL y v).2 (local_good v _ fun c hc => ?_)
      obtain ⟨-, hm, -⟩ := H.sgLaws ℚ v
      rw [mul_comm c, ← hm, mul_comm]
      exact psi_mul_of_one L M hL hM y hy hz (sg_oh v c hc)
    rw [geom_sum_eq hz, hzn]
    simp
