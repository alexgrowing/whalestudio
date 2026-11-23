import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CoeffOfW
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MulMemCrystallinePrismDividedPowerFamiliesStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnramifiedWittEmbeddingTwistedAlgebraMapInjectivStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ConstantCoeffFamilyFrobeniusCongrPowStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UniformizerFamilyFrobeniusCongrPowStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DividedUniformizerPowerFrobeniusCongrPowStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DividedVariablePowerFrobeniusCongrPowStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DividedPowerFamilySingleEqMulStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CoeffFrobeniusDoublePowerSeriesCongrBoxStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CoeffCoeffPowEqOfBoxStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FrobeniusPowMemFiniteSupportDoublePowerSeriesStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FrobeniusCongrOfFiniteOfLocalDividedPowerStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FrobeniusPreservesLadicDecayDividedPowerStatement

noncomputable section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Filter
open scoped Formalism.Per

namespace GlobalTheory.CrysPrism

namespace FrobPP

section Main

variable {l : ℕ} [hl : Fact l.Prime] {a e : ℕ} [NeZero a] [NeZero e] {O K : Type} [CommRing O] [Algebra ℤ_[l] O]
  [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K]
  (t : Wq l a →ₐ[ℤ_[l]] O)

theorem coeff_natCast_mul_double {R : Type} [CommRing R] (m : ℕ) (G : R⟦X⟧⟦X⟧) (i n : ℕ) :
    coeff n (coeff i ((m : R⟦X⟧⟦X⟧) * G)) = (m : R) * coeff n (coeff i G) := by
  rw [← map_natCast (C : R⟦X⟧ →+* R⟦X⟧⟦X⟧), coeff_C_mul, ← map_natCast (C : R →+* R⟦X⟧), coeff_C_mul]

theorem ofW_add (w w' : ℕ × ℕ → Wq l a) : ofW t K e (w + w') = ofW t K e w + ofW t K e w' := by
  funext τ; ext i n; simp [coeff_ofW, add_div]

theorem ofW_zero : ofW t K e (0 : ℕ × ℕ → Wq l a) = 0 := by
  funext τ; ext i n; simp [coeff_ofW]

theorem ofW_neg (w : ℕ × ℕ → Wq l a) : ofW t K e (-w) = -ofW t K e w := by
  funext τ; ext i n; simp [coeff_ofW, neg_div]

variable (K e) in

def ofWHom : (ℕ × ℕ → Wq l a) →+ (ZMod a → K⟦X⟧⟦X⟧) where
  toFun := ofW t K e
  map_zero' := ofW_zero t
  map_add' := ofW_add t

theorem Q_add {x y : ZMod a → K⟦X⟧⟦X⟧} (hx : x ∈ QSet t K e) (hy : y ∈ QSet t K e) : x + y ∈ QSet t K e := by
  obtain ⟨w, rfl⟩ := hx; obtain ⟨w', rfl⟩ := hy; exact ⟨w + w', ofW_add t w w'⟩

theorem Q_neg {x : ZMod a → K⟦X⟧⟦X⟧} (hx : x ∈ QSet t K e) : -x ∈ QSet t K e := by
  obtain ⟨w, rfl⟩ := hx; exact ⟨-w, ofW_neg t w⟩

theorem Q_sub {x y : ZMod a → K⟦X⟧⟦X⟧} (hx : x ∈ QSet t K e) (hy : y ∈ QSet t K e) : x - y ∈ QSet t K e := by
  rw [sub_eq_add_neg]; exact Q_add t hx (Q_neg t hy)

theorem Q_zero : (0 : ZMod a → K⟦X⟧⟦X⟧) ∈ QSet t K e := ⟨0, ofW_zero t⟩

theorem Q_natCast (m : ℕ) : (m : ZMod a → K⟦X⟧⟦X⟧) ∈ QSet t K e := by
  refine ⟨Pi.single (0, 0) (m : Wq l a), funext fun τ => ?_⟩
  ext i n
  rw [coeff_ofW, Pi.natCast_apply, ← mul_one ((m : K⟦X⟧⟦X⟧)), coeff_natCast_mul_double]
  rcases i with _ | i <;> rcases n with _ | n <;> simp [dpDen, Pi.single_apply, coeff_one]

theorem Q_mul {x y : ZMod a → K⟦X⟧⟦X⟧} (hx : x ∈ QSet t K e) (hy : y ∈ QSet t K e) : x * y ∈ QSet t K e :=
  GlobalTheory.T.mul_mem_crystallinePrismDividedPowerFamilies l a e O K t x hx y hy

theorem Q_pow {x : ZMod a → K⟦X⟧⟦X⟧} (hx : x ∈ QSet t K e) (k : ℕ) : x ^ k ∈ QSet t K e := by
  induction k with
  | zero => simpa using Q_natCast t (K := K) (e := e) 1
  | succ k ih => rw [pow_succ]; exact Q_mul t ih hx

theorem Q_sum {ι : Type} (s : Finset ι) (f : ι → ZMod a → K⟦X⟧⟦X⟧) (h : ∀ i ∈ s, f i ∈ QSet t K e) :
    ∑ i ∈ s, f i ∈ QSet t K e :=
  Finset.sum_induction f (· ∈ QSet t K e) (fun _ _ => Q_add t) (Q_zero t) h

variable {φ₂ : K⟦X⟧⟦X⟧ →+* K⟦X⟧⟦X⟧}

theorem good_add {x y : ZMod a → K⟦X⟧⟦X⟧} (hx : x ∈ GoodSet t e φ₂) (hy : y ∈ GoodSet t e φ₂) :
    x + y ∈ GoodSet t e φ₂ := by
  obtain ⟨hxQ, hfxQ, A, hA, hxA⟩ := hx
  obtain ⟨hyQ, hfyQ, B, hB, hyB⟩ := hy
  refine ⟨Q_add t hxQ hyQ, by rw [map_add]; exact Q_add t hfxQ hfyQ,
    A + B - x * y * ∑ k ∈ Finset.Ioo 0 l, x ^ (k - 1) * y ^ (l - k - 1) * ((l.choose k / l : ℕ) : ZMod a → K⟦X⟧⟦X⟧),
    ?_, ?_⟩
  · exact Q_sub t (Q_add t hA hB) (Q_mul t (Q_mul t hxQ hyQ) (Q_sum t _ _ fun k _ =>
      Q_mul t (Q_mul t (Q_pow t hxQ _) (Q_pow t hyQ _)) (Q_natCast t _)))
  · rw [map_add, hxA, hyB, add_pow_prime_eq hl.out]; ring

theorem good_mul {x y : ZMod a → K⟦X⟧⟦X⟧} (hx : x ∈ GoodSet t e φ₂) (hy : y ∈ GoodSet t e φ₂) :
    x * y ∈ GoodSet t e φ₂ := by
  obtain ⟨hxQ, hfxQ, A, hA, hxA⟩ := hx
  obtain ⟨hyQ, hfyQ, B, hB, hyB⟩ := hy
  refine ⟨Q_mul t hxQ hyQ, by rw [map_mul]; exact Q_mul t hfxQ hfyQ,
    A * y ^ l + B * x ^ l + (l : ZMod a → K⟦X⟧⟦X⟧) * A * B, ?_, ?_⟩
  · exact Q_add t (Q_add t (Q_mul t hA (Q_pow t hyQ _)) (Q_mul t hB (Q_pow t hxQ _)))
      (Q_mul t (Q_mul t (Q_natCast t _) hA) hB)
  · rw [map_mul, hxA, hyB]; ring

theorem good_zero : (0 : ZMod a → K⟦X⟧⟦X⟧) ∈ GoodSet t e φ₂ :=
  ⟨Q_zero t, by rw [map_zero]; exact Q_zero t, 0, Q_zero t, by simp [zero_pow hl.out.ne_zero]⟩

theorem good_one : (1 : ZMod a → K⟦X⟧⟦X⟧) ∈ GoodSet t e φ₂ :=
  ⟨by simpa using Q_natCast t (K := K) (e := e) 1, by rw [map_one]; simpa using Q_natCast t (K := K) (e := e) 1,
    0, Q_zero t, by simp⟩

theorem good_pow {x : ZMod a → K⟦X⟧⟦X⟧} (hx : x ∈ GoodSet t e φ₂) (k : ℕ) : x ^ k ∈ GoodSet t e φ₂ := by
  induction k with
  | zero => rw [pow_zero]; exact good_one t
  | succ k ih => rw [pow_succ]; exact good_mul t ih hx

theorem good_fin (hφC : ∀ f : K⟦X⟧, φ₂ (C f) = C (frob K l f)) (hφX : φ₂ X = (C X + X) ^ l - C (X ^ l))
    (w : ℕ × ℕ → Wq l a) (s : Finset (ℕ × ℕ)) :
    ofW t K e (fun p => if p ∈ s then w p else 0) ∈ GoodSet t e φ₂ := by
  have h : (fun p => if p ∈ s then w p else 0) = ∑ p ∈ s, Pi.single p (w p) := by
    funext q; rw [Finset.sum_apply]; simp [Pi.single_apply, Finset.sum_ite_eq']
  have h2 : ofW t K e (fun p => if p ∈ s then w p else 0) = ∑ p ∈ s, ofW t K e (Pi.single p (w p)) := by
    rw [h]; exact map_sum (ofWHom (K := K) (e := e) t) _ s
  rw [h2]
  refine Finset.sum_induction _ (· ∈ GoodSet t e φ₂) (fun _ _ => good_add t) (good_zero t) fun p _ => ?_
  rw [GlobalTheory.T.dividedPowerFamily_single_eq_mul l a e O K t p.1 p.2 (w p)]
  exact good_mul t (good_mul t (good_mul t (GlobalTheory.T.constantCoeffFamily_frobenius_congr_pow l a e O K t φ₂ hφC hφX _)
    (good_pow t (GlobalTheory.T.uniformizerFamily_frobenius_congr_pow l a e O K t φ₂ hφC hφX) _)) (GlobalTheory.T.dividedUniformizerPower_frobenius_congr_pow l a e O K t φ₂ hφC hφX _))
    (GlobalTheory.T.dividedVariablePower_frobenius_congr_pow l a e O K t φ₂ hφC hφX (fun x hx y hy => Q_mul t hx hy) _)

theorem ofW_mem_PPSet {w : ℕ × ℕ → Wq l a} (hw : LTo0 l w) : ofW t K e w ∈ PPSet t K e := by
  haveI : CharZero K := charZero_of_injective_algebraMap (algebraMap ℚ_[l] K).injective
  refine ⟨w, hw, fun τ i n => ?_⟩
  rw [coeff_ofW]
  have : ((i.factorial * (n / e).factorial : ℕ) : K) ≠ 0 := Nat.cast_ne_zero.2 (dpDen_pos e i n).ne'
  exact mul_div_cancel₀ _ this

end Main

theorem frob_mem_PPSet_congr : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] (t : Wq l a →ₐ[ℤ_[l]] O), ∀ (sh : K⟦X⟧ →+* K⟦X⟧⟦X⟧), (∀ (f : K⟦X⟧) (i : ℕ), (i.factorial : K⟦X⟧) * coeff i (sh f) = (PowerSeries.derivative K)^[i] f) → ∀ (φ₂ : K⟦X⟧⟦X⟧ →+* K⟦X⟧⟦X⟧), (∀ f : K⟦X⟧, φ₂ (PowerSeries.C f) = PowerSeries.C (frob K l f)) → (∀ f : K⟦X⟧, φ₂ (sh f) = sh (frob K l f)) → ∀ F ∈ PPSet t K e, frob2 φ₂ F ∈ PPSet t K e ∧ ∃ B ∈ PPSet t K e, frob2 φ₂ F = F ^ l + (l : ZMod a → K⟦X⟧⟦X⟧) * B := by
  intro l _ a e _ _ O K _ _ _ _ _ _ _ _ _ t sh hsh φ₂ hφC hφsh F hF
  haveI : CharZero K := charZero_of_injective_algebraMap (algebraMap ℚ_[l] K).injective
  have hφX : φ₂ X = (C X + X) ^ l - C (X ^ l) := by
    have h : (X : K⟦X⟧⟦X⟧) = sh X - C X := by rw [sh_X sh hsh]; ring
    have h2 : φ₂ X = sh (X ^ l) - C (X ^ l) := by rw [h, map_sub, hφsh, hφC, frob_X]
    rw [h2, map_pow, sh_X sh hsh]
  obtain ⟨w, hw, hFw⟩ := hF
  have hF' : F = ofW t K e w := funext fun τ => by
    ext i n
    have h0 : ((dpDen e i n : ℕ) : K) ≠ 0 := Nat.cast_ne_zero.2 (dpDen_pos e i n).ne'
    rw [coeff_ofW, eq_div_iff h0, mul_comm]
    exact hFw τ i n
  have hQ := GlobalTheory.T.frobenius_congr_of_finite_of_local_dividedPower l a e O K t φ₂ (good_fin t hφC hφX) (GlobalTheory.T.coeff_frobeniusDoublePowerSeries_congr_box l K φ₂ hφC hφX) (fun i n G H => GlobalTheory.T.coeff_coeff_pow_eq_of_coeff_coeff_eq_le K l i n G H)
  obtain ⟨-, ⟨v, hv⟩, B, ⟨b, rfl⟩, hB⟩ := hQ F ⟨w, hF'.symm⟩
  rw [hF'] at hv hB ⊢
  obtain ⟨hv0, hb0⟩ := GlobalTheory.T.frobenius_preserves_ladic_decay_dividedPower l a e O K t φ₂ (GlobalTheory.T.unramifiedWittEmbeddingTwisted_algebraMap_injective l a e O K t) (fun x hx y hy => Q_mul t hx hy) hQ
    (GlobalTheory.T.frobenius_pow_mem_finiteSupportDoublePowerSeries l a e O K t φ₂ hφC hφX) w hw v b hv.symm hB
  exact ⟨hv ▸ ofW_mem_PPSet t hv0, ofW t K e b, ofW_mem_PPSet t hb0, hB⟩

end FrobPP

end GlobalTheory.CrysPrism
