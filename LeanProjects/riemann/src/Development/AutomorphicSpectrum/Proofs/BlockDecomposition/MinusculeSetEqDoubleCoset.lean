import Mathlib
import Development.WeilBound.CoreStatements.PublishedTheorems.JacquetShalikaBound.lift_levelP_alt₂
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.NormSatakeLeOfUnitarySphericalGL

noncomputable section

open NumberField IsDedekindDomain GlobalTheory.LFun GroundTheory.Automorphic GroundTheory.Automorphic.Spherical
  GroundTheory.Automorphic.GLnLocal PositivityTheory.JacquetShalikaLocal Matrix
open ValuativeRel (valuation)
open scoped ValuativeRel

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.CompanionTheory.SatakeTyping

section Local

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] {n : ℕ}

theorem sum_ite_val_lt {m : ℕ} (hm : m ≤ n) :
    ∑ l : Fin n, (if (l : ℕ) < m then (1 : ℤ) else 0) = m := by
  rw [Fin.sum_univ_eq_sum_range (fun l => if l < m then (1 : ℤ) else 0) n, Finset.sum_boole]
  have : (Finset.range n).filter (fun l => l < m) = Finset.range m := by
    ext l
    simp only [Finset.mem_filter, Finset.mem_range]
    omega
  rw [this, Finset.card_range]

theorem eq_ite_of_antitone {μ : Fin n → ℤ} (hμ : Antitone μ) (h0 : ∀ i, 0 ≤ μ i) (h1 : ∀ i, μ i ≤ 1)
    {j : ℕ} (hs : ∑ i, μ i = j) (i : Fin n) : μ i = if (i : ℕ) < j then 1 else 0 := by
  split_ifs with h
  · by_contra hne
    have hi : μ i = 0 := by have := h0 i; have := h1 i; omega
    have hle : ∑ l : Fin n, μ l ≤ ∑ l : Fin n, (if (l : ℕ) < (i : ℕ) then (1 : ℤ) else 0) := by
      refine Finset.sum_le_sum fun l _ => ?_
      split_ifs with hl
      · exact h1 l
      · exact (hμ (show i ≤ l from Fin.le_def.2 (by omega))).trans hi.le
    rw [hs, sum_ite_val_lt i.2.le] at hle
    omega
  · by_contra hne
    have hi : μ i = 1 := by have := h0 i; have := h1 i; omega
    have hle : ∑ l : Fin n, (if (l : ℕ) < (i : ℕ) + 1 then (1 : ℤ) else 0) ≤ ∑ l : Fin n, μ l := by
      refine Finset.sum_le_sum fun l _ => ?_
      split_ifs with hl
      · exact hi.symm.le.trans (hμ (show l ≤ i from Fin.le_def.2 (by omega)))
      · exact h0 l
    rw [hs, sum_ite_val_lt (show (i : ℕ) + 1 ≤ n from i.2)] at hle
    omega

theorem exponent_nonneg {m : ℤ} (h : (uniformizer F : F) ^ m ∈ 𝒪[F]) : 0 ≤ m := by
  by_contra hm
  obtain ⟨k, rfl⟩ : ∃ k : ℕ, m = -((k : ℤ) + 1) := ⟨(-m - 1).toNat, by omega⟩
  have h1 : (uniformizer F) ^ (k + 1) * (⟨_, h⟩ : 𝒪[F]) = 1 := by
    refine Subtype.ext ?_
    have h2 : ((uniformizer F : F)) ≠ 0 := Cartan.uniformizer_ne_zero F
    simp only [Subring.coe_mul, Subring.coe_pow, Subring.coe_one]
    rw [_root_.zpow_neg, ← Nat.cast_succ, zpow_natCast, mul_inv_cancel₀ (pow_ne_zero _ h2)]
  exact (irreducible_uniformizer F).not_isUnit
    ((isUnit_pow_succ_iff).1 (IsUnit.of_mul_eq_one _ h1))

theorem valuation_det_diagPow (μ : Fin n → ℤ) :
    valuation F ((Cartan.diagPow F n μ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F).det =
      valuation F (uniformizer F : F) ^ (∑ i, μ i) := by
  have hv : valuation F (uniformizer F : F) ≠ 0 := valuation_uniformizer_ne_zero F
  rw [Cartan.coe_diagPow, det_diagonal, map_prod]
  simp only [map_zpow₀]
  classical
  induction (Finset.univ : Finset (Fin n)) using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [Finset.prod_insert ha, Finset.sum_insert ha, zpow_add₀ hv, ih]

theorem diagPow_mem_minusculeSet {j : ℕ} (hj : j ≤ n) :
    Cartan.diagPow F n (fun i => if (i : ℕ) < j then 1 else 0) ∈ minusculeSet F n j := by
  have hπ : (uniformizer F : F) ∈ 𝒪[F] := (uniformizer F).2
  refine ⟨fun a b => ?_, fun a b => ?_, ?_⟩
  · change ((Cartan.diagPow F n (fun i => if (i : ℕ) < j then 1 else 0) : GL (Fin n) F) :
      Matrix (Fin n) (Fin n) F) a b ∈ 𝒪[F]
    rw [Cartan.coe_diagPow, diagonal_apply]
    split_ifs <;> simp [hπ, (𝒪[F]).one_mem, (𝒪[F]).zero_mem]
  · have : ((Cartan.diagPow F n (fun i => if (i : ℕ) < j then 1 else 0))⁻¹ : GL (Fin n) F) a b =
        (diagonal fun i : Fin n => (uniformizer F : F) ^ (-(if (i : ℕ) < j then (1 : ℤ) else 0))) a b := rfl
    rw [this, diagonal_apply]
    have h2 : ((uniformizer F : F)) ≠ 0 := Cartan.uniformizer_ne_zero F
    split_ifs <;> simp [hπ, h2, (𝒪[F]).one_mem, (𝒪[F]).zero_mem]
  · rw [valuation_det_diagPow, sum_ite_val_lt hj, zpow_natCast]

theorem minusculeSet_eq_doubleCoset {j : ℕ} (hj : j ≤ n) :
    {g : GL (Fin n) F | ∃ a ∈ Formalism.UG.GLint (Fin n) 𝒪[F], ∃ b ∈ Formalism.UG.GLint (Fin n) 𝒪[F],
      (g : Matrix (Fin n) (Fin n) F) = (a : Matrix (Fin n) (Fin n) F) *
        Formalism.UG.diagJ n (uniformizer F : F) j * (b : Matrix (Fin n) (Fin n) F)} = minusculeSet F n j := by
  have hK : Formalism.UG.GLint (Fin n) 𝒪[F] = integralGL F n := rfl
  have hd : Formalism.UG.diagJ n (uniformizer F : F) j =
      ((Cartan.diagPow F n (fun i => if (i : ℕ) < j then 1 else 0) : GL (Fin n) F) :
        Matrix (Fin n) (Fin n) F) := by
    rw [Cartan.coe_diagPow, Formalism.UG.diagJ]
    congr 1
    funext i
    split_ifs <;> simp
  rw [hK]
  ext g
  constructor
  · rintro ⟨a, ha, b, hb, hg⟩
    rw [hd] at hg
    have : g = a * Cartan.diagPow F n (fun i => if (i : ℕ) < j then 1 else 0) * b :=
      Units.ext (by rw [hg]; rfl)
    rw [this]
    exact mul_mem_minusculeSet (diagPow_mem_minusculeSet hj) ha hb
  · intro hg
    obtain ⟨μ, hdom, k₁, hk₁, k₂, hk₂, rfl⟩ := Cartan.exists_eq_mul_diagPow_mul F n g
    have hm : Cartan.diagPow F n μ ∈ minusculeSet F n j := by
      have := mul_mem_minusculeSet hg (inv_mem hk₁) (inv_mem hk₂)
      simpa [mul_assoc] using this
    obtain ⟨m1, m2, m3⟩ := hm
    have h0 : ∀ i, 0 ≤ μ i := fun i => exponent_nonneg (by
      have := m1 i i
      rwa [show (Cartan.diagPow F n μ) i i = (uniformizer F : F) ^ μ i by
        change ((Cartan.diagPow F n μ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) i i = _
        rw [Cartan.coe_diagPow, diagonal_apply_eq]] at this)
    have h1 : ∀ i, μ i ≤ 1 := fun i => by
      have h2 : ((uniformizer F : F)) ≠ 0 := Cartan.uniformizer_ne_zero F
      have e : (uniformizer F : F) * ((Cartan.diagPow F n μ)⁻¹ : GL (Fin n) F) i i =
          (uniformizer F : F) ^ (1 - μ i) := by
        have : ((Cartan.diagPow F n μ)⁻¹ : GL (Fin n) F) i i =
          (diagonal fun i : Fin n => (uniformizer F : F) ^ (-μ i)) i i := rfl
        rw [this, diagonal_apply_eq, sub_eq_add_neg, zpow_add₀ h2, zpow_one]
      have := exponent_nonneg (F := F) (e ▸ m2 i i)
      omega
    have hs : ∑ i, μ i = j := by
      have hv : valuation F (uniformizer F : F) ≠ 0 := valuation_uniformizer_ne_zero F
      rw [valuation_det_diagPow, ← zpow_natCast] at m3
      exact (zpow_right_strictAnti₀ (zero_lt_iff.2 hv) (valuation_uniformizer_lt_one F)).injective m3
    have hμ : μ = fun i : Fin n => if (i : ℕ) < j then (1 : ℤ) else 0 := funext (eq_ite_of_antitone hdom h0 h1 hs)
    refine ⟨k₁, hk₁, k₂, hk₂, ?_⟩
    rw [hd, ← hμ]
    rfl

end Local

section Global

variable {E : Type} [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E))

theorem val_eq_of_mul {a c : WithZero (Multiplicative ℤ)} (ha : a < 1) (hc : c ≤ 1)
    (h : a * c = ((Multiplicative.ofAdd (-1 : ℤ) : Multiplicative ℤ) : WithZero (Multiplicative ℤ))) :
    a = ((Multiplicative.ofAdd (-1 : ℤ) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) := by
  have ha0 : a ≠ 0 := fun e => by simp [e] at h
  have hc0 : c ≠ 0 := fun e => by simp [e] at h
  obtain ⟨x, rfl⟩ := WithZero.ne_zero_iff_exists.1 ha0
  obtain ⟨y, rfl⟩ := WithZero.ne_zero_iff_exists.1 hc0
  have h1 : x < 1 := by exact_mod_cast ha
  have h2 : y ≤ 1 := by exact_mod_cast hc
  have h3 : x * y = Multiplicative.ofAdd (-1 : ℤ) := by exact_mod_cast h
  have h1' : Multiplicative.toAdd x < 0 := h1
  have h2' : Multiplicative.toAdd y ≤ 0 := h2
  have h3' : Multiplicative.toAdd x + Multiplicative.toAdd y = -1 := congrArg Multiplicative.toAdd h3
  have : x = Multiplicative.ofAdd (-1 : ℤ) := Multiplicative.toAdd.injective (by
    show Multiplicative.toAdd x = -1
    omega)
  rw [this]

theorem integer_eq : 𝒪[w.adicCompletion E] = Formalism.UG.Ov E w := by
  haveI : (Valued.v : Valuation (w.adicCompletion E) (WithZero (Multiplicative ℤ))).Compatible :=
    Valuation.Compatible.ofValuation _
  have he := ValuativeRel.isEquiv (valuation (w.adicCompletion E))
    (Valued.v : Valuation (w.adicCompletion E) (WithZero (Multiplicative ℤ)))
  ext y
  rw [Valuation.mem_integer_iff, he.le_one_iff_le_one]
  exact Iff.rfl

theorem integralGL_eq_KGL (n : ℕ) : integralGL (w.adicCompletion E) n = KGL w n := by
  have : ∀ O : Subring (w.adicCompletion E), O = 𝒪[w.adicCompletion E] →
      Formalism.UG.GLint (Fin n) O = integralGL (w.adicCompletion E) n := by
    rintro _ rfl
    rfl
  exact (this _ (integer_eq w).symm).symm

theorem isUnifV_uniformizer :
    Formalism.UG.IsUnifV E w (uniformizer (w.adicCompletion E) : w.adicCompletion E) := by
  obtain ⟨ϖ, hϖ⟩ := exists_isUnifV w
  have hmem : ∀ x : w.adicCompletion E, x ∈ 𝒪[w.adicCompletion E] ↔ Valued.v x ≤ 1 := fun x => by
    rw [integer_eq w]
    exact Iff.rfl
  have hϖ1 : Valued.v ϖ ≤ 1 := by
    rw [hϖ]
    exact (by decide : ((Multiplicative.ofAdd (-1 : ℤ) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) ≤ 1)
  let t : 𝒪[w.adicCompletion E] := ⟨ϖ, (hmem ϖ).2 hϖ1⟩
  have hπ1 : Valued.v (uniformizer (w.adicCompletion E) : w.adicCompletion E) ≤ 1 :=
    (hmem _).1 (uniformizer _).2
  have hlt : Valued.v (uniformizer (w.adicCompletion E) : w.adicCompletion E) < 1 := by
    haveI : (Valued.v : Valuation (w.adicCompletion E) (WithZero (Multiplicative ℤ))).Compatible :=
      Valuation.Compatible.ofValuation _
    exact (ValuativeRel.isEquiv (valuation (w.adicCompletion E))
      (Valued.v : Valuation (w.adicCompletion E) (WithZero (Multiplicative ℤ)))).lt_one_iff_lt_one.1
        (valuation_uniformizer_lt_one _)
  have hne : ¬ IsUnit t := fun hu => by
    obtain ⟨u, hu⟩ := hu.exists_right_inv
    have h1 : ϖ * (u : w.adicCompletion E) = 1 := congrArg Subtype.val hu
    have h2 : Valued.v ϖ * Valued.v (u : w.adicCompletion E) = 1 := by
      rw [← map_mul, h1, map_one]
    have h3 : Valued.v ϖ * Valued.v (u : w.adicCompletion E) ≤ Valued.v ϖ * 1 :=
      mul_le_mul_right ((hmem _).1 u.2) _
    rw [h2, mul_one, hϖ] at h3
    exact absurd h3 (by decide)
  have hm : t ∈ IsLocalRing.maximalIdeal 𝒪[w.adicCompletion E] := hne
  rw [(IsDiscreteValuationRing.irreducible_iff_uniformizer _).1
    (irreducible_uniformizer (w.adicCompletion E)), Ideal.mem_span_singleton] at hm
  obtain ⟨c, hc⟩ := hm
  have h4 : Valued.v (uniformizer (w.adicCompletion E) : w.adicCompletion E) *
      Valued.v (c : w.adicCompletion E) = ((Multiplicative.ofAdd (-1 : ℤ) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) := by
    rw [← map_mul, ← hϖ]
    exact congrArg Valued.v (congrArg Subtype.val hc).symm
  exact val_eq_of_mul hlt ((hmem _).1 c.2) h4

theorem esymm_eq_evalAt {n : ℕ} (z : Fin n → ℂˣ) (r : ℕ) :
    ((Finset.univ.val.map z).map fun b : ℂˣ => (b : ℂ)).esymm r = evalAt z (esymmL n r) := by
  rw [Multiset.map_map, evalAt_esymmL]
  refine (Finset.esymm_map_val (fun i => (z i : ℂ)) Finset.univ r).trans
    (Finset.sum_congr rfl fun S _ => ?_)
  rw [monomialChar_apply]
  have : ∀ i, ((z i ^ lamS S i : ℂˣ) : ℂ) = if i ∈ S then (z i : ℂ) else 1 := fun i => by
    by_cases h : i ∈ S <;> simp [lamS, h]
  simp only [this, Finset.prod_ite_mem, Finset.univ_inter]

theorem cpow_eq_sqrt_pow (q : ℕ) {n r : ℕ} (hr : r ≤ n) :
    (q : ℂ) ^ (((r : ℂ) * ((n : ℂ) - r)) / 2) =
      ((NNReal.sqrt (q : NNReal) : ℝ) : ℂ) ^ (r * (n - r)) := by
  have e : ((r : ℂ) * ((n : ℂ) - r)) / 2 = ((r * (n - r) : ℕ) : ℂ) * (1 / 2) := by
    push_cast [Nat.cast_sub hr]
    ring
  rw [e, Complex.cpow_nat_mul]
  congr 1
  rw [Real.coe_sqrt, Real.sqrt_eq_rpow, Complex.ofReal_cpow (by positivity)]
  simp

end Global

theorem l12 : lift_levelP_alt₂ := by
  intro E _ _ w
  have hq : qF (w.adicCompletion E) = Ideal.absNorm w.asIdeal := GlobalTheory.LFun.SatBoundGL.resCard_completion w
  refine ⟨hq, ?_⟩
  intro n V _ _ ρ v z h
  obtain ⟨-, hfix, -, hT⟩ := h
  have hK := integralGL_eq_KGL w n
  refine ⟨fun g hg => GlobalTheory.LGrp.mem_fixed.1 hfix g (hK ▸ hg), fun r hr => ?_⟩
  have h1 := hT _ (isUnifV_uniformizer w) r hr
  have hS : satEig (Formalism.UG.qV E w) n (Finset.univ.val.map z) r =
      sqrtQ (w.adicCompletion E) ^ (r * (n - r)) * evalAt z (esymmL n r) := by
    rw [satEig, esymm_eq_evalAt, cpow_eq_sqrt_pow _ hr, sqrtQ, hq]
    rfl
  have hTj : Formalism.UG.Tj ℂ n (Formalism.UG.Ov E w) (uniformizer (w.adicCompletion E) : w.adicCompletion E) r =
      (minusculeSet (w.adicCompletion E) n r).indicator fun _ => (1 : ℂ) := by
    rw [Formalism.UG.Tj, ← integer_eq w, minusculeSet_eq_doubleCoset hr]
    rfl
  rw [hS, hTj, heckeVec] at h1
  rw [← h1, hK]

end GlobalTheory.CompanionTheory.SatakeTyping

end
