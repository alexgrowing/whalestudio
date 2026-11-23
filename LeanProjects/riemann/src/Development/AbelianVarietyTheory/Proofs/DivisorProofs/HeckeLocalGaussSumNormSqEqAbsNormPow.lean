import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HeckeTateFunctionalEquationCM
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GaussUnitsNormSq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemPowOfPsiAtTrivial
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIntWitness
open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.IndefiniteRowSideFullHecke.CompletedLStripBounds GlobalTheory.HeckeEps
open Formalism.L2.Host (atFin IsUnitAt)

noncomputable section

namespace GlobalTheory.GaussMod

variable {E : Type} [Field E] [NumberField E]

theorem locK_congr {χ : HChar E} {w : HeightOneSpectrum (𝓞 E)} {a : ℕ} (hχ : χ.LevelLe w a) {x y : 𝓞 E}
    (hx : x ∉ w.asIdeal) (hy : y ∉ w.asIdeal) (hx0 : (x : E) ≠ 0) (hy0 : (y : E) ≠ 0) (h : x - y ∈ w.asIdeal ^ a) :
    χ.locK w (Units.mk0 (x : E) hx0) = χ.locK w (Units.mk0 (y : E) hy0) := by
  have hval : ∀ z : E, Valued.v (algebraMap E (w.adicCompletion E) z) = w.valuation E z := fun z =>
    HeightOneSpectrum.valuedAdicCompletion_eq_valuation' w z
  have hx1 := (w.valuation_eq_one_iff_notMem (K := E)).2 hx
  have hy1 := (w.valuation_eq_one_iff_notMem (K := E)).2 hy
  have h1 : χ.loc w (atFin w (Units.mk0 _ hx0 * (Units.mk0 _ hy0)⁻¹)) = 1 := by
    have e : ((atFin w (Units.mk0 _ hx0 * (Units.mk0 _ hy0)⁻¹) : (w.adicCompletion E)ˣ) : w.adicCompletion E) =
        algebraMap E (w.adicCompletion E) ((x : E) / y) := by
      simp [atFin, div_eq_mul_inv]
    refine hχ _ ?_ ?_
    · rw [IsUnitAt, e, hval, map_div₀, hx1, hy1, div_one]
    · rw [e, ← map_one (algebraMap E (w.adicCompletion E)), ← map_sub, hval, div_sub_one hy0, map_div₀, hy1, div_one]
      exact valuation_sub_le h
  rw [map_mul, map_inv, map_mul, map_inv, mul_inv_eq_one] at h1
  exact h1

theorem gaussSumAt_normSq (χ : HChar E) (w : HeightOneSpectrum (𝓞 E)) (a : ℕ) (c : Eˣ) (ha : a ≠ 0) (hE : ExpAt χ w a)
    (hu : IsUnitary χ) (hc : w.valuation E (c : E) = WithZero.exp (-((a + diffExp w : ℕ) : ℤ))) :
    ‖gaussSumAt χ w a c‖ ^ 2 = (Ideal.absNorm w.asIdeal : ℝ) ^ a := by
  classical
  have hχ : χ.LevelLe w a := (hE a).2 le_rfl
  have := w.isMaximal
  set P := w.asIdeal with hP
  have hfin : Finite (𝓞 E ⧸ P ^ a) := Ideal.finiteQuotientOfFreeOfNeBot _ (pow_ne_zero _ w.ne_bot)
  haveI : Fintype (𝓞 E ⧸ P ^ a) := Fintype.ofFinite _
  have hval : ∀ z : E, Valued.v (algebraMap E (w.adicCompletion E) z) = w.valuation E z := fun z =>
    HeightOneSpectrum.valuedAdicCompletion_eq_valuation' w z
  have hne0 : ∀ x : 𝓞 E, x ∉ P → (x : E) ≠ 0 := fun x hx h0 => hx (by
    have : x = 0 := RingOfIntegers.coe_eq_zero_iff.1 h0
    rw [this]; exact P.zero_mem)
  let f : 𝓞 E → ℂ := fun x => psiAt w (algebraMap E (w.adicCompletion E) ((x : E) / c))
  have f_add : ∀ x y, f (x + y) = f x * f y := fun x y => by
    have e : ((x + y : 𝓞 E) : E) / c = (x : E) / c + (y : E) / c := by push_cast; ring
    show psiAt w _ = psiAt w _ * psiAt w _
    rw [e, map_add, psiAt_add]
  have f_zero : ∀ x ∈ P ^ a, f x = 1 := fun x hx => by
    apply psiAt_eq_one
    have h1 := valuation_sub_le (w := w) (y := x) (y' := 0) (by simpa using hx)
    rw [hval, map_div₀, hc, div_le_iff₀ (zero_lt_iff.2 WithZero.exp_ne_zero), ← WithZero.exp_add]
    convert h1 using 2 <;> (push_cast; ring)
  have f_congr : ∀ x y, x - y ∈ P ^ a → f x = f y := fun x y h => by
    rw [show x = y + (x - y) by ring, f_add, f_zero _ h, mul_one]
  let ψb : AddChar (𝓞 E ⧸ P ^ a) ℂ :=
    { toFun := fun q => f (Quotient.out q)
      map_zero_eq_one' := f_zero _ (by rw [← Ideal.Quotient.eq_zero_iff_mem, Ideal.Quotient.mk_out])
      map_add_eq_mul' := fun q r => by
        rw [← f_add]
        apply f_congr
        rw [← Ideal.Quotient.eq, map_add, Ideal.Quotient.mk_out, Ideal.Quotient.mk_out, Ideal.Quotient.mk_out] }
  have ψb_mk : ∀ x, ψb (Ideal.Quotient.mk _ x) = f x := fun x =>
    f_congr _ _ (by rw [← Ideal.Quotient.eq, Ideal.Quotient.mk_out])
  have hout : ∀ u : (𝓞 E ⧸ P ^ a)ˣ, (Quotient.out (u : 𝓞 E ⧸ P ^ a) : 𝓞 E) ∉ P := out_notMem w ha
  have h1P : (1 : 𝓞 E) ∉ P := (Ideal.ne_top_iff_one _).1 w.isPrime.ne_top
  let χb : (𝓞 E ⧸ P ^ a)ˣ →* ℂˣ :=
    { toFun := fun u => χ.locK w (Units.mk0 _ (hne0 _ (hout u)))
      map_one' := by
        rw [locK_congr hχ (hout 1) h1P _ (hne0 _ h1P)
          (by rw [← Ideal.Quotient.eq, Ideal.Quotient.mk_out, map_one, Units.val_one])]
        rw [show (Units.mk0 (((1 : 𝓞 E)) : E) (hne0 _ h1P)) = 1 by ext; simp, map_one]
      map_mul' := fun u v => by
        have hm : (Quotient.out ((u * v : (𝓞 E ⧸ P ^ a)ˣ) : 𝓞 E ⧸ P ^ a) : 𝓞 E) -
            Quotient.out (u : 𝓞 E ⧸ P ^ a) * Quotient.out (v : 𝓞 E ⧸ P ^ a) ∈ P ^ a := by
          rw [← Ideal.Quotient.eq, map_mul, Ideal.Quotient.mk_out, Ideal.Quotient.mk_out, Ideal.Quotient.mk_out,
            Units.val_mul]
        have hp : Quotient.out (u : 𝓞 E ⧸ P ^ a) * Quotient.out (v : 𝓞 E ⧸ P ^ a) ∉ P := fun h =>
          (w.isPrime.mem_or_mem h).elim (hout u) (hout v)
        rw [locK_congr hχ (hout _) hp _ (hne0 _ hp) hm, ← map_mul]
        congr 1
        ext
        simp }
  have hG : gaussSumAt χ w a c = ∑ u : (𝓞 E ⧸ P ^ a)ˣ, (((χb u)⁻¹ : ℂˣ) : ℂ) * ψb (u : 𝓞 E ⧸ P ^ a) := by
    rw [gaussSumAt, finsum_eq_sum_of_fintype]
    refine Finset.sum_congr rfl fun u _ => ?_
    rw [gaussTerm, dif_neg (hne0 _ (hout u))]
    rfl
  have hM : ∀ q : 𝓞 E ⧸ P ^ a, IsUnit q ↔ q ∉ P.map (Ideal.Quotient.mk (P ^ a)) := fun q => by
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective q
    rw [Ideal.mem_quotient_iff_mem (Ideal.pow_le_self ha)]
    constructor
    · intro hu hx
      have h1 := hu.map (Ideal.Quotient.factor (Ideal.pow_le_self ha : P ^ a ≤ P))
      rw [Ideal.Quotient.factor_mk, Ideal.Quotient.eq_zero_iff_mem.2 hx] at h1
      have := Ideal.Quotient.nontrivial_iff.2 w.isPrime.ne_top
      exact not_isUnit_zero h1
    · exact Ideal.Quotient.isUnit_mk_pow_of_notMem P
  have hψ : ∀ d : 𝓞 E ⧸ P ^ a, (∀ x, ψb (d * x) = 1) → d = 0 := fun d hd => by
    obtain ⟨d, rfl⟩ := Ideal.Quotient.mk_surjective d
    rw [Ideal.Quotient.eq_zero_iff_mem]
    refine GlobalTheory.GaussModulus.mem_pow_of_psiAt_trivial w a c hc d fun x => ?_
    have := hd (Ideal.Quotient.mk _ x)
    rw [← map_mul, ψb_mk] at this
    simpa [f] using this
  obtain ⟨r, ur, hur, hrP, hr1, hrχ⟩ := GlobalTheory.GaussModulus.exists_int_witness χ w a ha hE
  have hr0 : (r : E) ≠ 0 := hne0 r hrP
  have hur' : ur = Units.mk0 (r : E) hr0 := Units.ext hur
  rw [hur'] at hrχ
  obtain ⟨t, ht⟩ := Ideal.Quotient.isUnit_mk_pow_of_notMem P (n := a) hrP
  have hχt : ∃ t : (𝓞 E ⧸ P ^ a)ˣ, (∀ m ∈ P.map (Ideal.Quotient.mk (P ^ a)), ((t : 𝓞 E ⧸ P ^ a) - 1) * m = 0) ∧
      χb t ≠ 1 := by
    refine ⟨t, fun m hm => ?_, ?_⟩
    · obtain ⟨m, rfl⟩ := Ideal.Quotient.mk_surjective m
      rw [Ideal.mem_quotient_iff_mem (Ideal.pow_le_self ha)] at hm
      rw [ht, ← map_one (Ideal.Quotient.mk (P ^ a)), ← map_sub, ← map_mul, Ideal.Quotient.eq_zero_iff_mem]
      have e : P ^ (a - 1) * P = P ^ a := by rw [← pow_succ, Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.2 ha)]
      rw [← e]
      exact Ideal.mul_mem_mul hr1 hm
    · show χ.locK w _ ≠ 1
      rwa [locK_congr hχ (hout t) hrP _ hr0 (by rw [← Ideal.Quotient.eq, Ideal.Quotient.mk_out, ht])]
  obtain ⟨t0, ht0, hχ0⟩ := hχt
  have hnorm : ∀ u : (𝓞 E ⧸ P ^ a)ˣ, ‖((χb u : ℂˣ) : ℂ)‖ = 1 := fun u => hu _
  have hG' : gaussSumAt χ w a c = ∑ u : (𝓞 E ⧸ P ^ a)ˣ, (((χb u : ℂˣ) : ℂ))⁻¹ * ψb (u : 𝓞 E ⧸ P ^ a) := by
    rw [hG]
    simp only [Units.val_inv_eq_inv_val]
  rw [hG', GlobalTheory.gauss_units_norm_sq _ hM ψb hψ (fun u => ((χb u : ℂˣ) : ℂ)) (fun u v => by rw [map_mul, Units.val_mul])
    hnorm t0 ht0 (fun h => hχ0 (Units.ext h)), Fintype.card_eq_nat_card, ← Submodule.cardQuot_apply, ← Ideal.absNorm_apply,
    map_pow]
  push_cast
  rfl

end GlobalTheory.GaussMod
