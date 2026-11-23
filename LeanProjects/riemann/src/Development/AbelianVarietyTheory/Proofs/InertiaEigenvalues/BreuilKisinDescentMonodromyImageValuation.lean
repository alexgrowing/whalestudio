import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.ImagePolynomialAction
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CoeffZeroSmulMemMapOfAevalMulEqZero
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TameDescentConnectionSemisimpleEigenvaluesStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinDescentOperatorPreservesLatticeStatement

open PowerSeries GlobalTheory.BK

namespace GlobalTheory.LcImage

open GlobalTheory.IndefiniteRowSideFullHecke.ImagePolynomialAction

theorem eval_zero_polyR (l e : ℕ) (U : Finset ℤ) (η : ℕ) :
    (polyR l e U η).eval 0 = ∏ n ∈ (shifts U η).erase 0, (-(n * e * l)) := by
  simp [polyR, Polynomial.eval_prod]

theorem abs_lt_of_mem_shifts {l : ℕ} {U : Finset ℤ} {η H : ℕ} (hU : U ⊆ Finset.Icc (-(η : ℤ)) H)
    (hl : H + η < l) {n : ℤ} (hn : n ∈ shifts U η) : |n| < l := by
  obtain ⟨i, hi, k, ⟨hk1, hk2⟩, rfl⟩ := mem_shifts.1 hn
  have := Finset.mem_Icc.1 (hU hi)
  rw [abs_lt]; constructor <;> omega

theorem not_dvd_of_abs_lt {l : ℕ} {n : ℤ} (hn : n ≠ 0) (h : |n| < l) : ¬ (l : ℤ) ∣ n := by
  intro hd
  have h1 := Nat.le_of_dvd (Int.natAbs_pos.2 hn) (Int.ofNat_dvd_left.1 hd)
  have h2 : (n.natAbs : ℤ) = |n| := Int.natCast_natAbs n
  omega

theorem padicValInt_prod {p : ℕ} [Fact p.Prime] (S : Finset ℤ) (f : ℤ → ℤ)
    (hf : ∀ n ∈ S, f n ≠ 0 ∧ padicValInt p (f n) = 1) :
    (∏ n ∈ S, f n) ≠ 0 ∧ padicValInt p (∏ n ∈ S, f n) = S.card := by
  induction S using Finset.induction_on with
  | empty => simp
  | insert x S hx ih =>
    have ih' := ih fun n hn => hf n (Finset.mem_insert_of_mem hn)
    have hx' := hf x (Finset.mem_insert_self x S)
    rw [Finset.prod_insert hx, Finset.card_insert_of_notMem hx]
    refine ⟨mul_ne_zero hx'.1 ih'.1, ?_⟩
    rw [padicValInt.mul hx'.1 ih'.1, hx'.2, ih'.2]; ring

theorem valuation {l e a : ℕ} [Fact l.Prime] (hsucc : e + 1 = l ^ a) (ha : a ≠ 0) (he : e ≠ 0)
    (U : Finset ℤ) (η H N : ℕ) (hU : U ⊆ Finset.Icc (-(η : ℤ)) H) (hN : U.card ≤ N + 1)
    (hl : H + η < l) : Valuation l e U η N := by
  have hp : l.Prime := Fact.out
  have hle : ¬ (l : ℤ) ∣ (e : ℤ) := by
    intro hd
    have hd' : l ∣ e := Int.natCast_dvd_natCast.1 hd
    have h1 : l ∣ l ^ a := dvd_pow_self l ha
    rw [← hsucc] at h1
    exact hp.one_lt.ne' (Nat.dvd_one.1 ((Nat.dvd_add_right hd').1 h1))
  have key : ∀ n ∈ (shifts U η).erase 0, (-(n * e * l) : ℤ) ≠ 0 ∧ padicValInt l (-(n * e * l)) = 1 := by
    intro n hn
    obtain ⟨hn0, hnS⟩ := Finset.mem_erase.1 hn
    have hnl := not_dvd_of_abs_lt hn0 (abs_lt_of_mem_shifts hU hl hnS)
    have he0 : (e : ℤ) ≠ 0 := by exact_mod_cast he
    have hl0 : (l : ℤ) ≠ 0 := by exact_mod_cast hp.ne_zero
    refine ⟨neg_ne_zero.2 (mul_ne_zero (mul_ne_zero hn0 he0) hl0), ?_⟩
    have hneg : padicValInt l (-(n * e * l)) = padicValInt l (n * e * l) := by simp [padicValInt]
    rw [hneg, padicValInt.mul (mul_ne_zero hn0 he0) hl0, padicValInt.mul hn0 he0,
      padicValInt.eq_zero_of_not_dvd hnl, padicValInt.eq_zero_of_not_dvd hle, padicValInt.self hp.one_lt]
  obtain ⟨h1, h2⟩ := padicValInt_prod _ _ key
  refine ⟨fun n hn => abs_lt_of_mem_shifts hU hl hn, ?_, ?_, ?_, Nat.mul_le_mul_right _ hN⟩
  · rw [eval_zero_polyR]; exact h1
  · rw [eval_zero_polyR]; exact h2
  · calc ((shifts U η).erase 0).card ≤ (shifts U η).card := Finset.card_erase_le
      _ ≤ U.card * (Finset.Icc (1 : ℤ) η).card := Finset.card_image₂_le _ _ _
      _ = U.card * η := by rw [Int.card_Icc]; simp

end GlobalTheory.LcImage

namespace GlobalTheory.LcImage

open GlobalTheory.IndefiniteRowSideFullHecke.ImagePolynomialAction

section Lin

variable {O K : Type} [CommRing O] [NormedField K] [IsUltrametricDist K] [CompleteSpace K] [Algebra O K]
  [IsUnitBall O K] {l e a : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι]
  [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero e] [NeZero a] [TameDescentExponentData K l e a]
  {η H : ℕ} (D : BKDat O K l e a ι η H)

theorem aeval_map_intCast {V : Type} [AddCommGroup V] [Module K V] (T : Module.End K V) (q : Polynomial ℤ) :
    Polynomial.aeval T (q.map (Int.castRingHom K)) = Polynomial.aeval T q := by
  rw [← Polynomial.aeval_map_algebraMap K T q]; rfl

theorem eval_polyRK_root {U : Finset ℤ} {n : ℤ} (hn : n ∈ shifts U η) (hn0 : n ≠ 0) :
    ((polyR l e U η).map (Int.castRingHom K)).eval (((n * e * l : ℤ) : K)) = 0 := by
  rw [polyR, Polynomial.map_prod, Polynomial.eval_prod]
  refine Finset.prod_eq_zero (Finset.mem_erase.2 ⟨hn0, hn⟩) ?_
  simp

theorem polyRK_mul_eq_zero (U : Finset ℤ) (hS : D.jumps ⊆ U) :
    Polynomial.aeval D.LcZ ((polyR l e U η).map (Int.castRingHom K)) * D.LcZ = 0 := by
  obtain ⟨-, -, htop⟩ := GlobalTheory.T.tameDescent_connection_semisimple_eigenvalues O K l e a ι η H D U hS
  have hle : ⨆ n ∈ shifts U η, D.LcZ.eigenspace ((n * e * l : ℤ) : K) ≤
      LinearMap.ker (Polynomial.aeval D.LcZ ((polyR l e U η).map (Int.castRingHom K)) * D.LcZ) := by
    refine iSup₂_le fun n hn x hx => ?_
    rw [Module.End.mem_eigenspace_iff] at hx
    rw [LinearMap.mem_ker, Module.End.mul_apply, hx, map_smul]
    by_cases hn0 : n = 0
    · simp [hn0]
    by_cases hx0 : x = 0
    · simp [hx0]
    rw [Module.End.aeval_apply_of_hasEigenvector ⟨Module.End.mem_eigenspace_iff.2 hx, hx0⟩,
      eval_polyRK_root hn hn0, zero_smul, smul_zero]
  ext x
  have : x ∈ LinearMap.ker (Polynomial.aeval D.LcZ ((polyR l e U η).map (Int.castRingHom K)) * D.LcZ) := hle (htop ▸ Submodule.mem_top)
  simpa using this

end Lin

end GlobalTheory.LcImage

namespace GlobalTheory.LcImage

open GlobalTheory.IndefiniteRowSideFullHecke.ImagePolynomialAction

theorem eval_zero_polyR_ne_zero {l e : ℕ} (hl : l ≠ 0) (he : e ≠ 0) (U : Finset ℤ) (η : ℕ) :
    (polyR l e U η).eval 0 ≠ 0 := by
  rw [eval_zero_polyR, Finset.prod_ne_zero_iff]
  intro n hn
  have hn0 := (Finset.mem_erase.1 hn).1
  have he0 : (e : ℤ) ≠ 0 := by exact_mod_cast he
  have hl0 : (l : ℤ) ≠ 0 := by exact_mod_cast hl
  exact neg_ne_zero.2 (mul_ne_zero (mul_ne_zero hn0 he0) hl0)

section Lin2

variable {O K : Type} [CommRing O] [NormedField K] [IsUltrametricDist K] [CompleteSpace K] [Algebra O K]
  [IsUnitBall O K] {l e a : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι]
  [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero e] [NeZero a] [TameDescentExponentData K l e a]
  {η H : ℕ} (D : BKDat O K l e a ι η H)

theorem LcZ_aeval_polyR₁ (U : Finset ℤ) (w : D.Zl) :
    D.LcZ (Polynomial.aeval D.LcZ (polyR₁ l e U η) w) =
      Polynomial.aeval D.LcZ (polyR l e U η) w - (((polyR l e U η).eval 0 : ℤ) : K) • w := by
  have := congrArg (fun q => Polynomial.aeval D.LcZ q w) (X_mul_polyR₁ l e U η)
  simpa [Module.End.mul_apply, Int.cast_smul_eq_zsmul] using this

theorem castK_ne_zero (U : Finset ℤ) : ((((polyR l e U η).eval 0 : ℤ)) : K) ≠ 0 := by
  have hr := eval_zero_polyR_ne_zero (Fact.out : l.Prime).ne_zero (NeZero.ne e) U η
  rw [← map_intCast (algebraMap ℚ_[l] K)]
  exact (map_ne_zero _).2 (Int.cast_ne_zero.2 hr)

theorem image (U : Finset ℤ) (hS : D.jumps ⊆ U) : Image D U := by
  have h0 := polyRK_mul_eq_zero D U hS
  rw [aeval_map_intCast] at h0
  refine ⟨fun w hw => ?_, fun W hW => ?_⟩
  · have hR : Polynomial.aeval D.LcZ (polyR l e U η) w = 0 := by
      obtain ⟨u, rfl⟩ := hw
      rw [← Module.End.mul_apply, h0, LinearMap.zero_apply]
    refine ⟨hR, ?_⟩
    rw [LcZ_aeval_polyR₁, hR, zero_sub, neg_neg]
  · apply le_antisymm
    · intro w hw
      obtain ⟨hwR, hwW⟩ := Submodule.mem_inf.1 hw
      have h := GlobalTheory.coeff_zero_smul_mem_map_of_aeval_mul_eq_zero D.LcZ ((polyR l e U η).map (Int.castRingHom K))
        (polyRK_mul_eq_zero D U hS) W (fun z hz => hW hz) w hwW hwR
      rw [Polynomial.coeff_map, Polynomial.coeff_zero_eq_eval_zero] at h
      have hne := castK_ne_zero (K := K) (l := l) (e := e) (η := η) U
      have : w = ((((polyR l e U η).eval 0 : ℤ)) : K)⁻¹ • ((Int.castRingHom K) ((polyR l e U η).eval 0) • w) := by
        rw [eq_intCast, smul_smul, inv_mul_cancel₀ hne, one_smul]
      rw [this]
      exact Submodule.smul_mem _ _ h
    · rintro _ ⟨x, hx, rfl⟩
      exact Submodule.mem_inf.2 ⟨LinearMap.mem_range_self _ _, hW hx⟩

theorem mem_Z_aeval (hI : Integral D) (q : Polynomial ℤ) (x : D.Zl) (hx : (x : D.Pol) ∈ D.Z) :
    ((Polynomial.aeval D.LcZ q x : D.Zl) : D.Pol) ∈ D.Z := by
  have hpow : ∀ (n : ℕ) (y : D.Zl), (y : D.Pol) ∈ D.Z → (((D.LcZ ^ n) y : D.Zl) : D.Pol) ∈ D.Z := by
    intro n
    induction n with
    | zero => intro y hy; simpa using hy
    | succ n ih =>
      intro y hy
      rw [pow_succ', Module.End.mul_apply]
      exact hI _ (ih y hy)
  induction q using Polynomial.induction_on' with
  | add p q hp hq =>
    rw [map_add, LinearMap.add_apply, Submodule.coe_add]; exact D.Z.add_mem hp hq
  | monomial n c =>
    rw [Polynomial.aeval_monomial, Module.End.mul_apply, Module.algebraMap_end_apply]
    have := hpow n x hx
    simpa using zsmul_mem this c

theorem integralImage (U : Finset ℤ) (hS : D.jumps ⊆ U) (hI : Integral D) : IntegralImage D U := by
  intro c w hw hcw
  refine ⟨-(Polynomial.aeval D.LcZ (polyR₁ l e U η) w), ?_, ?_⟩
  · have := mem_Z_aeval D hI (polyR₁ l e U η) ((l : K) ^ c • w) (by simpa using hcw)
    rw [map_smul] at this
    rw [Submodule.coe_neg, smul_neg]
    exact D.Z.neg_mem (by simpa using this)
  · rw [map_neg]; exact ((image D U hS).1 w hw).2

end Lin2

end GlobalTheory.LcImage

theorem GlobalTheory.LcImage.image_valuation_integralImage : ∀ (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K] [CompleteSpace K] [Algebra O K] [IsUnitBall O K] (l e a : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι] [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero e] [NeZero a] [TameDescentExponentData K l e a] (η H : ℕ) (D : BKDat O K l e a ι η H), ∀ (U : Finset ℤ) (N : ℕ), D.jumps ⊆ U → U ⊆ Finset.Icc (-(η : ℤ)) H → U.card ≤ N + 1 → η < H → GlobalTheory.IndefiniteRowSideFullHecke.ImagePolynomialAction.Image D U ∧ (H + η < l → GlobalTheory.IndefiniteRowSideFullHecke.ImagePolynomialAction.Valuation l e U η N) ∧ (10 * H + 2 ≤ l → GlobalTheory.IndefiniteRowSideFullHecke.ImagePolynomialAction.IntegralImage D U) := by
  intro O K _ _ _ _ _ _ l e a ι _ _ _ _ _ _ _ η H D U N hS hU hN hηH
  refine ⟨GlobalTheory.LcImage.image D U hS, fun hl => ?_, fun hl => ?_⟩
  · exact GlobalTheory.LcImage.valuation (TameDescentExponentData.succ_eq (K := K)) (NeZero.ne a) (NeZero.ne e) U η H N hU hN hl
  · exact GlobalTheory.LcImage.integralImage D U hS (GlobalTheory.T.breuilKisin_descent_operator_preserves_lattice O K l e a ι η H D hηH hl)
