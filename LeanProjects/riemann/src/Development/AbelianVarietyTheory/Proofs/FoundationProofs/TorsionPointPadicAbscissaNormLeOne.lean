import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Formalism.PairingDivisors.StatementH
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DifferentiableSqTh
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Cval
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IntegralJAndAlgebraicData
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.InducedTypeThetaGenusOnePermutes
import Development.AbelianVarietyTheory.Proofs.HeightProofs.WeierstrassPTorsionIntegralAndDistinctMod
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators

noncomputable section

namespace GlobalTheory.TorsionAbscissa

def prodF {K : Type*} [CommRing K] (W : WeierstrassCurve K) (X₁ Z₁ X₂ Z₂ : K) : K :=
  X₁ ^ 2 * X₂ ^ 2 - W.b₄ * X₁ * X₂ * Z₁ * Z₂ - W.b₆ * (X₁ * Z₂ + X₂ * Z₁) * Z₁ * Z₂ -
    W.b₈ * Z₁ ^ 2 * Z₂ ^ 2

def sumF {K : Type*} [CommRing K] (W : WeierstrassCurve K) (X₁ Z₁ X₂ Z₂ : K) : K :=
  2 * X₁ * X₂ * (X₁ * Z₂ + X₂ * Z₁) + W.b₂ * X₁ * X₂ * Z₁ * Z₂ +
    W.b₄ * (X₁ * Z₂ + X₂ * Z₁) * Z₁ * Z₂ + W.b₆ * Z₁ ^ 2 * Z₂ ^ 2

def Rel {K : Type*} [CommRing K] (W : WeierstrassCurve K) (X₁ Z₁ X₂ Z₂ X₃ Z₃ X₄ Z₄ : K) : Prop :=
  (X₃ * Z₄ + X₄ * Z₃) * prodF W X₁ Z₁ X₂ Z₂ = X₃ * X₄ * sumF W X₁ Z₁ X₂ Z₂ ∧
  Z₃ * Z₄ * prodF W X₁ Z₁ X₂ Z₂ = X₃ * X₄ * (X₁ * Z₂ - X₂ * Z₁) ^ 2 ∧
  Z₃ * Z₄ * sumF W X₁ Z₁ X₂ Z₂ = (X₃ * Z₄ + X₄ * Z₃) * (X₁ * Z₂ - X₂ * Z₁) ^ 2

theorem Rel.map_iff {K L : Type*} [CommRing K] [CommRing L] {f : K →+* L} (hf : Function.Injective f)
    (W : WeierstrassCurve K) (X₁ Z₁ X₂ Z₂ X₃ Z₃ X₄ Z₄ : K) :
    Rel (W.map f) (f X₁) (f Z₁) (f X₂) (f Z₂) (f X₃) (f Z₃) (f X₄) (f Z₄) ↔
      Rel W X₁ Z₁ X₂ Z₂ X₃ Z₃ X₄ Z₄ := by
  simp only [Rel, prodF, sumF, ← hf.eq_iff, map_mul, map_add, map_sub, map_pow, map_ofNat,
    WeierstrassCurve.map_b₂, WeierstrassCurve.map_b₄, WeierstrassCurve.map_b₆, WeierstrassCurve.map_b₈]

theorem Rel.variableChange {K : Type*} [CommRing K] {W : WeierstrassCurve K}
    (C : WeierstrassCurve.VariableChange K) {X₁ Z₁ X₂ Z₂ X₃ Z₃ X₄ Z₄ : K}
    (h : Rel W X₁ Z₁ X₂ Z₂ X₃ Z₃ X₄ Z₄) :
    ((C.u⁻¹ : Kˣ) ^ 2 * (X₃ - C.r * Z₃) * Z₄ + (C.u⁻¹ : Kˣ) ^ 2 * (X₄ - C.r * Z₄) * Z₃) *
        prodF (C • W) ((C.u⁻¹ : Kˣ) ^ 2 * (X₁ - C.r * Z₁)) Z₁ ((C.u⁻¹ : Kˣ) ^ 2 * (X₂ - C.r * Z₂)) Z₂ =
      (C.u⁻¹ : Kˣ) ^ 2 * (X₃ - C.r * Z₃) * ((C.u⁻¹ : Kˣ) ^ 2 * (X₄ - C.r * Z₄)) *
        sumF (C • W) ((C.u⁻¹ : Kˣ) ^ 2 * (X₁ - C.r * Z₁)) Z₁ ((C.u⁻¹ : Kˣ) ^ 2 * (X₂ - C.r * Z₂)) Z₂ := by
  obtain ⟨h1, h2, h3⟩ := h
  have hp : prodF (C • W) ((C.u⁻¹ : Kˣ) ^ 2 * (X₁ - C.r * Z₁)) Z₁ ((C.u⁻¹ : Kˣ) ^ 2 * (X₂ - C.r * Z₂)) Z₂ =
      ((C.u⁻¹ : Kˣ) : K) ^ 8 * (prodF W X₁ Z₁ X₂ Z₂ - C.r * sumF W X₁ Z₁ X₂ Z₂ +
        C.r ^ 2 * (X₁ * Z₂ - X₂ * Z₁) ^ 2) := by
    simp only [prodF, sumF, WeierstrassCurve.variableChange_b₄, WeierstrassCurve.variableChange_b₆,
      WeierstrassCurve.variableChange_b₈]
    ring
  have hs : sumF (C • W) ((C.u⁻¹ : Kˣ) ^ 2 * (X₁ - C.r * Z₁)) Z₁ ((C.u⁻¹ : Kˣ) ^ 2 * (X₂ - C.r * Z₂)) Z₂ =
      ((C.u⁻¹ : Kˣ) : K) ^ 6 * (sumF W X₁ Z₁ X₂ Z₂ - 2 * C.r * (X₁ * Z₂ - X₂ * Z₁) ^ 2) := by
    simp only [prodF, sumF, WeierstrassCurve.variableChange_b₄, WeierstrassCurve.variableChange_b₆,
      WeierstrassCurve.variableChange_b₂]
    ring
  rw [hp, hs]
  linear_combination ((C.u⁻¹ : Kˣ) : K) ^ 10 * (h1 - 2 * C.r * h2 + C.r ^ 2 * h3)

open IsLocalRing in

theorem multiples {K : Type*} [Field K] (O : ValuationSubring K) (W : WeierstrassCurve K)
    (h2 : W.b₂ ∈ O) (h4 : W.b₄ ∈ O) (h6 : W.b₆ ∈ O) (h8 : W.b₈ ∈ O) (X Z : ℕ → K)
    (hne : ∀ k, X k = 0 → Z k ≠ 0) (hZ : Z 0 = 0)
    (hrel : ∀ k, (X (k + 2) * Z k + X k * Z (k + 2)) * prodF W (X (k + 1)) (Z (k + 1)) (X 1) (Z 1) =
      X (k + 2) * X k * sumF W (X (k + 1)) (Z (k + 1)) (X 1) (Z 1))
    (s : O) (hs : Z 1 = s * X 1) (hs0 : residue O s = 0) (k : ℕ) :
    (∃ a : O, residue O a = (k : ResidueField O) ^ 2 ∧ Z k = a * s * X k) ∧
    (∃ a : O, residue O a = ((k + 1 : ℕ) : ResidueField O) ^ 2 ∧ Z (k + 1) = a * s * X (k + 1)) := by
  induction k with
  | zero => exact ⟨⟨0, by simp, by simp [hZ]⟩, ⟨1, by simp, by simp [hs]⟩⟩
  | succ k ih =>
    obtain ⟨⟨b, hb, rb⟩, ⟨a, ha, ra⟩⟩ := ih
    refine ⟨⟨a, ha, ra⟩, ?_⟩
    have x0 : X k ≠ 0 := fun h => hne _ h (by rw [rb, h, mul_zero])
    have x1 : X (k + 1) ≠ 0 := fun h => hne _ h (by rw [ra, h, mul_zero])
    have x2 : X 1 ≠ 0 := fun h => hne _ h (by rw [hs, h, mul_zero])
    let b2 : O := ⟨_, h2⟩
    let b4 : O := ⟨_, h4⟩
    let b6 : O := ⟨_, h6⟩
    let b8 : O := ⟨_, h8⟩
    let D : O := 1 - b4 * a * s ^ 2 - b6 * (1 + a) * a * s ^ 3 - b8 * a ^ 2 * s ^ 4
    let N : O := 2 * (1 + a) + b2 * a * s + b4 * (1 + a) * a * s ^ 2 + b6 * a ^ 2 * s ^ 3
    have hD1 : residue O D = 1 := by simp [D, hs0]
    have hN1 : residue O N = 2 * (1 + residue O a) := by simp [N, hs0, map_ofNat]
    have hDu : IsUnit D := (residue_ne_zero_iff_isUnit D).1 (by rw [hD1]; exact one_ne_zero)
    obtain ⟨d, hd⟩ := hDu.exists_right_inv
    have hd1 : residue O d = 1 := by
      have := congrArg (residue O) hd
      rwa [map_mul, hD1, one_mul, map_one] at this
    have hdC : (D : K) * d = 1 := by exact_mod_cast congrArg (fun x : O => (x : K)) hd
    have c2 : ((2 : O) : K) = 2 := rfl
    have eD : prodF W (X (k + 1)) (Z (k + 1)) (X 1) (Z 1) = X (k + 1) ^ 2 * X 1 ^ 2 * (D : K) := by
      rw [ra, hs]; simp [D, prodF, b4, b6, b8]; ring
    have eN : sumF W (X (k + 1)) (Z (k + 1)) (X 1) (Z 1) = X (k + 1) ^ 2 * X 1 ^ 2 * ((N : K) * s) := by
      rw [ra, hs]; simp [N, sumF, b2, b4, b6, c2]; ring
    have key := hrel k
    rw [eD, eN, rb] at key
    refine ⟨N * d - b, ?_, ?_⟩
    · rw [map_sub, map_mul, hN1, hd1, ha, hb]; push_cast; ring
    · apply mul_left_cancel₀ (mul_ne_zero x0 (mul_ne_zero (pow_ne_zero 2 x1) (pow_ne_zero 2 x2)))
      push_cast
      linear_combination (d : K) * key - (X (k + 2) * (b * s * X k) + X k * Z (k + 2)) *
        X (k + 1) ^ 2 * X 1 ^ 2 * hdC

def hX (L : PeriodPair) (z : ℂ) : ℂ := if z ∈ L.lattice then 1 else L.weierstrassP z

def hZ (L : PeriodPair) (z : ℂ) : ℂ := if z ∈ L.lattice then 0 else 1

theorem rel_of_smul {K : Type*} [CommRing K] {W : WeierstrassCurve K} {X₁ Z₁ X₂ Z₂ X₃ Z₃ X₄ Z₄ : K} (c : K)
    (h1 : prodF W X₁ Z₁ X₂ Z₂ = c * (X₃ * X₄)) (h2 : sumF W X₁ Z₁ X₂ Z₂ = c * (X₃ * Z₄ + X₄ * Z₃))
    (h3 : (X₁ * Z₂ - X₂ * Z₁) ^ 2 = c * (Z₃ * Z₄)) : Rel W X₁ Z₁ X₂ Z₂ X₃ Z₃ X₄ Z₄ := by
  rw [Rel, h1, h2, h3]
  refine ⟨?_, ?_, ?_⟩ <;> ring

theorem rel_lattice (L : PeriodPair) (z : ℂ) {w : ℂ} (hw : w ∉ L.lattice) :
    Rel (⟨0, 0, 0, -L.g₂ / 4, -L.g₃ / 4⟩ : WeierstrassCurve ℂ) (hX L z) (hZ L z) (hX L w) (hZ L w)
      (hX L (z + w)) (hZ L (z + w)) (hX L (z - w)) (hZ L (z - w)) := by
  by_cases hz : z ∈ L.lattice
  · have a : z + w ∉ L.lattice := fun h => hw (by simpa using sub_mem h hz)
    have b : z - w ∉ L.lattice := fun h => hw (by simpa using sub_mem hz h)
    have c : L.weierstrassP (z + w) = L.weierstrassP w :=
      (GlobalTheory.weierstrassP_eq_iff L a hw).2 (Or.inl (by simpa using hz))
    have d : L.weierstrassP (z - w) = L.weierstrassP w :=
      (GlobalTheory.weierstrassP_eq_iff L b hw).2 (Or.inr (by simpa using hz))
    refine rel_of_smul 1 ?_ ?_ ?_ <;> simp only [hX, hZ, hz, hw, a, b, c, d, prodF, sumF, if_true, if_false] <;>
      ring
  by_cases hm : z - w ∈ L.lattice
  · have e := (GlobalTheory.weierstrassP_eq_iff L hz hw).2 (Or.inl hm)
    by_cases hp : z + w ∈ L.lattice
    · have hww : w + w ∈ L.lattice := by
        have := sub_mem hp hm
        rwa [show z + w - (z - w) = w + w by ring] at this
      have hy := (GlobalTheory.derivWeierstrassP_eq_zero_iff L hw).2 hww
      have hsq := L.derivWeierstrassP_sq w hw
      rw [hy] at hsq
      refine rel_of_smul (prodF (⟨0, 0, 0, -L.g₂ / 4, -L.g₃ / 4⟩ : WeierstrassCurve ℂ)
        (hX L z) (hZ L z) (hX L w) (hZ L w)) ?_ ?_ ?_ <;>
        simp only [hX, hZ, hz, hw, hm, hp, e, prodF, sumF, if_true, if_false, WeierstrassCurve.b₂,
          WeierstrassCurve.b₄, WeierstrassCurve.b₆, WeierstrassCurve.b₈]
      · ring
      · linear_combination -hsq
      · ring
    · have hww : w + w ∉ L.lattice := fun h => hp (by
        have := add_mem hm h
        rwa [show z - w + (w + w) = z + w by ring] at this)
      have c : L.weierstrassP (z + w) = L.weierstrassP (w + w) :=
        (GlobalTheory.weierstrassP_eq_iff L hp hww).2 (Or.inl (by simpa using hm))
      have hd := GlobalTheory.TorsionIntegral.dbl L hw hww
      refine rel_of_smul (4 * L.weierstrassP w ^ 3 - L.g₂ * L.weierstrassP w - L.g₃) ?_ ?_ ?_ <;>
        simp only [hX, hZ, hz, hw, hm, hp, e, c, prodF, sumF, if_true, if_false, WeierstrassCurve.b₂,
          WeierstrassCurve.b₄, WeierstrassCurve.b₆, WeierstrassCurve.b₈]
      · linear_combination -hd
      · ring
      · ring
  by_cases hp : z + w ∈ L.lattice
  · have e := (GlobalTheory.weierstrassP_eq_iff L hz hw).2 (Or.inr hp)
    have hww : w + w ∉ L.lattice := fun h => hm (by
      have := sub_mem hp h
      rwa [show z + w - (w + w) = z - w by ring] at this)
    have c : L.weierstrassP (z - w) = L.weierstrassP (w + w) :=
      (GlobalTheory.weierstrassP_eq_iff L hm hww).2 (Or.inr (by
        rwa [show z - w + (w + w) = z + w by ring]))
    have hd := GlobalTheory.TorsionIntegral.dbl L hw hww
    refine rel_of_smul (4 * L.weierstrassP w ^ 3 - L.g₂ * L.weierstrassP w - L.g₃) ?_ ?_ ?_ <;>
      simp only [hX, hZ, hz, hw, hm, hp, e, c, prodF, sumF, if_true, if_false, WeierstrassCurve.b₂,
        WeierstrassCurve.b₄, WeierstrassCurve.b₆, WeierstrassCurve.b₈]
    · linear_combination -hd
    · ring
    · ring
  · have hne : L.weierstrassP z ≠ L.weierstrassP w := fun h =>
      ((GlobalTheory.weierstrassP_eq_iff L hz hw).1 h).elim hm hp
    obtain ⟨hs, hq⟩ := GlobalTheory.TorsionIntegral.sum_prod L hz hw hne
    refine rel_of_smul ((L.weierstrassP z - L.weierstrassP w) ^ 2) ?_ ?_ ?_ <;>
      simp only [hX, hZ, hz, hw, hm, hp, prodF, sumF, if_true, if_false, WeierstrassCurve.b₂,
        WeierstrassCurve.b₄, WeierstrassCurve.b₆, WeierstrassCurve.b₈]
    · linear_combination -hq
    · linear_combination -hs
    · ring

theorem norm_abscissa_le (p : ℕ) [Fact p.Prime] (lam : Qbar →+* ℂ_[p]) (L : PeriodPair)
    (h2 : L.g₂ ∈ Qbar) (h3 : L.g₃ ∈ Qbar) (C : WeierstrassCurve.VariableChange ℂ_[p])
    (W : WeierstrassCurve ℂ_[p])
    (hW : W = C • (⟨0, 0, 0, lamC lam (-L.g₂ / 4), lamC lam (-L.g₃ / 4)⟩ : WeierstrassCurve ℂ_[p]))
    (a1 : ‖W.a₁‖ ≤ 1) (a2 : ‖W.a₂‖ ≤ 1) (a3 : ‖W.a₃‖ ≤ 1) (a4 : ‖W.a₄‖ ≤ 1) (a6 : ‖W.a₆‖ ≤ 1)
    {n : ℕ} (hn : 0 < n) (hnp : Nat.Coprime n p) {t : ℂ} (ht : t ∉ L.lattice)
    (hnt : (n : ℂ) * t ∈ L.lattice) :
    ‖((C.u⁻¹ : ℂ_[p]ˣ) : ℂ_[p]) ^ 2 * (lamC lam (L.weierstrassP t) - C.r)‖ ≤ 1 := by
  let O : ValuationSubring ℂ_[p] := (NormedField.valuation (K := ℂ_[p])).valuationSubring
  have hO : ∀ x : ℂ_[p], x ∈ O ↔ ‖x‖ ≤ 1 := fun x => by
    simp only [O, Valuation.mem_valuationSubring_iff, NormedField.valuation_apply]
    exact_mod_cast Iff.rfl
  rw [← hO] at a1 a2 a3 a4 a6 ⊢
  have hXQ : ∀ k : ℕ, hX L (k * t) ∈ Qbar := fun k => by
    unfold hX
    split_ifs with h
    · exact one_mem _
    · refine (GlobalTheory.CurveAlgebraic.weierstrassP_mem L h2 h3 hn h ?_).1
      rw [mul_left_comm, ← nsmul_eq_mul]
      exact nsmul_mem hnt k
  have hZQ : ∀ k : ℕ, hZ L (k * t) ∈ Qbar := fun k => by
    unfold hZ
    split_ifs
    exacts [zero_mem _, one_mem _]
  let XQ : ℕ → Qbar := fun k => ⟨_, hXQ k⟩
  let ZQ : ℕ → Qbar := fun k => ⟨_, hZQ k⟩
  have q2 : -L.g₂ / 4 ∈ Qbar := div_mem (neg_mem h2) (ofNat_mem _ 4)
  have q3 : -L.g₃ / 4 ∈ Qbar := div_mem (neg_mem h3) (ofNat_mem _ 4)
  let V : WeierstrassCurve Qbar := ⟨0, 0, 0, ⟨_, q2⟩, ⟨_, q3⟩⟩
  have hV : V.map lam = ⟨0, 0, 0, lamC lam (-L.g₂ / 4), lamC lam (-L.g₃ / 4)⟩ := by
    ext <;> simp [V, lamC, q2, q3]
  have hrQ : ∀ k, Rel V (XQ (k + 1)) (ZQ (k + 1)) (XQ 1) (ZQ 1) (XQ (k + 2)) (ZQ (k + 2))
      (XQ k) (ZQ k) := fun k => by
    rw [← Rel.map_iff (f := (Qbar.val : Qbar →+* ℂ)) (RingHom.injective _)]
    have := rel_lattice L (((k + 1 : ℕ) : ℂ) * t) (w := ((1 : ℕ) : ℂ) * t) (by simpa using ht)
    rw [show ((k + 1 : ℕ) : ℂ) * t + ((1 : ℕ) : ℂ) * t = ((k + 2 : ℕ) : ℂ) * t by push_cast; ring,
      show ((k + 1 : ℕ) : ℂ) * t - ((1 : ℕ) : ℂ) * t = (k : ℂ) * t by push_cast; ring] at this
    exact this
  let X : ℕ → ℂ_[p] := fun k => ((C.u⁻¹ : ℂ_[p]ˣ) : ℂ_[p]) ^ 2 * (lam (XQ k) - C.r * lam (ZQ k))
  let Z : ℕ → ℂ_[p] := fun k => lam (ZQ k)
  have hin : ∀ k : ℕ, (k : ℂ) * t ∈ L.lattice → Z k = 0 ∧ X k ≠ 0 := fun k h => by
    have e1 : XQ k = 1 := Subtype.ext (if_pos h)
    have e2 : ZQ k = 0 := Subtype.ext (if_pos h)
    simp [X, Z, e1, e2]
  have hout : ∀ k : ℕ, (k : ℂ) * t ∉ L.lattice → Z k = 1 := fun k h => by
    have e2 : ZQ k = 1 := Subtype.ext (if_neg h)
    simp [Z, e2]
  have ht1 : ((1 : ℕ) : ℂ) * t ∉ L.lattice := by simpa using ht
  have hX1 : ((C.u⁻¹ : ℂ_[p]ˣ) : ℂ_[p]) ^ 2 * (lamC lam (L.weierstrassP t) - C.r) = X 1 := by
    have e1 : (XQ 1 : ℂ) = L.weierstrassP t := (if_neg ht1).trans (by simp)
    have e2 : lam (ZQ 1) = 1 := hout 1 ht1
    simp only [X, e2, mul_one, ← e1, lamC, dif_pos (XQ 1).2]
  rw [hX1]
  by_contra hx
  have hx0 : X 1 ≠ 0 := fun h => hx (h ▸ O.zero_mem)
  obtain ⟨hs, hs0⟩ := ValuationSubring.mem_nonunits_iff_exists_mem_maximalIdeal.1
    ((O.inv_mem_nonunits_iff).2 (Or.inr hx))
  have c2 : (2 : ℂ_[p]) ∈ O := ofNat_mem O 2
  have c4 : (4 : ℂ_[p]) ∈ O := ofNat_mem O 4
  obtain ⟨a, ha, ra⟩ := (multiples O W
    (add_mem (pow_mem a1 2) (mul_mem c4 a2)) (add_mem (mul_mem c2 a4) (mul_mem a1 a3))
    (add_mem (pow_mem a3 2) (mul_mem c4 a6))
    (sub_mem (add_mem (sub_mem (add_mem (mul_mem (pow_mem a1 2) a6) (mul_mem (mul_mem c4 a2) a6))
      (mul_mem (mul_mem a1 a3) a4)) (mul_mem a2 (pow_mem a3 2))) (pow_mem a4 2))
    X Z (fun k hk => by
      by_cases h : (k : ℂ) * t ∈ L.lattice
      · exact absurd hk (hin k h).2
      · rw [hout k h]; exact one_ne_zero)
    (hin 0 (by simp)).1
    (fun k => by
      rw [hW, ← hV]
      exact ((Rel.map_iff lam.injective V ..).2 (hrQ k)).variableChange C)
    ⟨_, hs⟩ (by rw [hout 1 ht1]; exact (inv_mul_cancel₀ hx0).symm)
    ((IsLocalRing.residue_eq_zero_iff _).2 hs0) n).1
  rw [(hin n hnt).1] at ra
  have ha0 : a = 0 := by simpa [hx0, (hin n hnt).2] using ra
  have hn1 : ‖(n : ℂ_[p])‖ = 1 := by
    rw [← map_natCast (algebraMap ℚ_[p] ℂ_[p]), norm_algebraMap']
    exact Padic.norm_natCast_eq_one_iff.2 hnp.symm
  have hm : (n : ℂ_[p])⁻¹ ∈ O := by rw [hO, norm_inv, hn1, inv_one]
  have hu : (n : O) * ⟨_, hm⟩ = 1 := by
    apply Subtype.ext
    simp [hn.ne']
  have := congrArg (IsLocalRing.residue O) hu
  rw [ha0, map_zero] at ha
  rw [map_mul, map_natCast, pow_eq_zero_iff two_ne_zero |>.1 ha.symm, zero_mul, map_one] at this
  exact zero_ne_one this

theorem norm_xAt_le : ∀ (D : D7) (p : ℕ) [Fact p.Prime] (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (g : GL3Theta.G1 p),
    GL3Theta.At D cc δ g → ∀ t : ℂ, GL3Theta.Tors1 p g.abelian₂ t → ‖GlobalTheory.EvenTheta.xAt g t‖ ≤ 1 := by
  rintro D p _ cc δ g ⟨hcc, -, hδ, hΛ, hok⟩ t ⟨ht, n, hn, hnp, hnt⟩
  have hcrv : Crv D cc δ := ⟨hcc, hδ⟩
  have hG := (GlobalTheory.InducedType.induced_type D).1
  obtain ⟨⟨-, h2, h3⟩, -⟩ := (GlobalTheory.CurveAlgebraic.integral_j_and_algebraic_data D hG).2 cc δ hcrv
  obtain ⟨L, hL, -⟩ := GlobalTheory.CurveAlgebraic.exists_periodPair D hG cc δ hcrv
  simp only [tor0] at h2 h3
  rw [← hΛ] at hL h2 h3
  obtain ⟨e2, e3, -, -, hp, -⟩ := GlobalTheory.LatticeInvariants.invariants_dictionary L _ hL
  obtain ⟨a1, a2, a3, a4, a6, -⟩ := hok.1
  rw [GlobalTheory.EvenTheta.xAt, (hp t ht).1]
  exact norm_abscissa_le p g.lam L (e2 ▸ h2) (e3 ▸ h3) g.C _ (by rw [wModel, e2, e3]) a1 a2 a3 a4 a6 hn hnp
    (fun h => ht ((hL _).2 h)) ((hL _).1 hnt)

end GlobalTheory.TorsionAbscissa
