import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsPotential
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.OneSubPhiOntoOfFilZero
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BhattScholzeCrystallineLattices
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.ConductorExponents

noncomputable section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Filter
open scoped Formalism.Per

namespace GlobalTheory.CrysPrism

section Defs

variable {l : ℕ} [hl : Fact l.Prime] {a : ℕ} [NeZero a] {O : Type} [CommRing O] [Algebra ℤ_[l] O]

variable (l) in

def LTo0 {ι : Type} (w : ι → Wq l a) : Prop := ∀ r : ℕ, ∀ᶠ n in cofinite, (l : Wq l a) ^ r ∣ w n

variable (t : Wq l a →ₐ[ℤ_[l]] O) (K : Type) [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K]
  (e : ℕ)

def SdSet : Set (ZMod a → K⟦X⟧) :=
  {F | ∃ w : ℕ → Wq l a, LTo0 l w ∧
    ∀ τ n, ((n / e).factorial : K) * coeff n (F τ) = algebraMap O K (emb t τ (w n))}

def Sd : Subring (ZMod a → K⟦X⟧) := Subring.closure (SdSet t K e)

def PPSet : Set (ZMod a → K⟦X⟧⟦X⟧) :=
  {F | ∃ w : ℕ × ℕ → Wq l a, LTo0 l w ∧
    ∀ τ i n, ((i.factorial * (n / e).factorial : ℕ) : K) * coeff n (coeff i (F τ)) =
      algebraMap O K (emb t τ (w (i, n)))}

def PPd : Subring (ZMod a → K⟦X⟧⟦X⟧) := Subring.closure (PPSet t K e)

def inclS : (Wq l a)⟦X⟧ →+* (ZMod a → K⟦X⟧) :=
  Pi.ringHom fun τ => (A O K).val.toRingHom.comp ((Pi.evalRingHom (fun _ : ZMod a => A O K) τ).comp (toAc t K))

theorem inclS_apply (x : (Wq l a)⟦X⟧) (τ : ZMod a) : inclS t K x τ = (toAc t K x τ : K⟦X⟧) := rfl

variable {K}

def frob2 (φ₂ : K⟦X⟧⟦X⟧ →+* K⟦X⟧⟦X⟧) : (ZMod a → K⟦X⟧⟦X⟧) →+* (ZMod a → K⟦X⟧⟦X⟧) :=
  Pi.ringHom fun τ => φ₂.comp (Pi.evalRingHom (fun _ : ZMod a => K⟦X⟧⟦X⟧) (τ - 1))

variable (a K) in

def constP : (ZMod a → K⟦X⟧) →+* (ZMod a → K⟦X⟧⟦X⟧) :=
  Pi.ringHom fun τ => (C : K⟦X⟧ →+* K⟦X⟧⟦X⟧).comp (Pi.evalRingHom (fun _ : ZMod a => K⟦X⟧) τ)

variable (a) in

def shP (sh : K⟦X⟧ →+* K⟦X⟧⟦X⟧) : (ZMod a → K⟦X⟧) →+* (ZMod a → K⟦X⟧⟦X⟧) :=
  Pi.ringHom fun τ => sh.comp (Pi.evalRingHom (fun _ : ZMod a => K⟦X⟧) τ)

variable (a K) in

def diag : (ZMod a → K⟦X⟧⟦X⟧) →+* (ZMod a → K⟦X⟧) :=
  Pi.ringHom fun τ => (constantCoeff : K⟦X⟧⟦X⟧ →+* K⟦X⟧).comp (Pi.evalRingHom (fun _ : ZMod a => K⟦X⟧⟦X⟧) τ)

end Defs

theorem tf_pi {R : Type} [CommRing R] [IsDomain R] {n a : ℕ} (hn : (n : R) ≠ 0) (x : ZMod a → R)
    (h : (n : ZMod a → R) * x = 0) : x = 0 := funext fun τ => by
  have h1 := congrFun h τ
  simp only [Pi.mul_apply, Pi.natCast_apply, Pi.zero_apply] at h1
  exact (mul_eq_zero.1 h1).resolve_left hn

theorem natCast_ne_zero_ps {R : Type} [CommRing R] {n : ℕ} (h : (n : R) ≠ 0) : (n : R⟦X⟧) ≠ 0 := fun h' =>
  h (by simpa using congrArg (constantCoeff : R⟦X⟧ →+* R) h')

theorem tf_sub {R : Type} [CommRing R] {n : ℕ} (s : Subring R) (htf : ∀ x : R, (n : R) * x = 0 → x = 0)
    (x : ↥s) (h : (n : ↥s) * x = 0) : x = 0 := Subtype.ext (htf _ (by simpa using congrArg Subtype.val h))

theorem nzd_of_tf {R : Type} [CommRing R] {n : ℕ} (htf : ∀ x : R, (n : R) * x = 0 → x = 0) :
    (n : R) ∈ nonZeroDivisors R :=
  mem_nonZeroDivisors_iff.2 ⟨htf, fun x hx => htf x (by rw [mul_comm]; exact hx)⟩

theorem bdd_self {R : Type} [CommRing R] (n : ℕ) : ∃ m : ℕ, ∀ x : R ⧸ Ideal.span {(n : R)},
    (∃ k : ℕ, (n : R ⧸ Ideal.span {(n : R)}) ^ k * x = 0) → (n : R ⧸ Ideal.span {(n : R)}) ^ m * x = 0 := by
  refine ⟨1, fun x _ => ?_⟩
  have h : (n : R ⧸ Ideal.span {(n : R)}) = 0 := by
    rw [← map_natCast (Ideal.Quotient.mk (Ideal.span {(n : R)})), Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.mem_span_singleton_self _
  rw [h, pow_one, zero_mul]

variable {l : ℕ} [hl : Fact l.Prime]

theorem isUnit_delta_l {A : Type} [CommRing A] (D : Delta l A) (htf : ∀ x : A, (l : A) * x = 0 → x = 0)
    [IsAdicComplete (Ideal.span {(l : A)}) A] : IsUnit (D.δ l) := by
  have h1 : D.δ l = 1 - (l : A) ^ (l - 1) := by
    rw [← sub_eq_zero]
    apply htf
    have h := D.φ_eq (l : A)
    rw [map_natCast] at h
    have h2 : (l : A) ^ l = (l : A) * (l : A) ^ (l - 1) := by
      rw [← pow_succ']; congr 1; have := hl.out.one_lt; omega
    linear_combination -h - h2
  rw [h1]
  have hm : -(l : A) ^ (l - 1) ∈ Ideal.span {(l : A)} := (Ideal.neg_mem_iff _).2
    (Ideal.pow_mem_of_mem _ (Ideal.mem_span_singleton_self _) _ (by have := hl.out.one_lt; omega))
  have := Ideal.mem_jacobson_bot.1 (IsAdicComplete.le_jacobson_bot _ hm) 1
  rwa [mul_one, neg_add_eq_sub] at this

section Sh

variable {K : Type} [NormedField K] [CharZero K] (sh : K⟦X⟧ →+* K⟦X⟧⟦X⟧)
  (hsh : ∀ (f : K⟦X⟧) (i : ℕ), (i.factorial : K⟦X⟧) * coeff i (sh f) = (PowerSeries.derivative K)^[i] f)
include hsh

theorem constantCoeff_sh (f : K⟦X⟧) : constantCoeff (sh f) = f := by
  simpa using hsh f 0

theorem sh_X : sh X = C X + X := by
  ext i : 1
  have h := hsh X i
  rcases i with _ | _ | i
  · simpa using h
  · simp [coeff_C, coeff_X]
    simpa [derivative_X] using h
  · have h3 : ((i + 2).factorial : K⟦X⟧) ≠ 0 := natCast_ne_zero_ps (Nat.cast_ne_zero.2 (Nat.factorial_ne_zero _))
    have h4 : (PowerSeries.derivative K)^[i + 2] X = 0 := by
      rw [Function.iterate_succ_apply, Function.iterate_succ_apply, derivative_X]
      have : PowerSeries.derivative K (1 : K⟦X⟧) = 0 := (PowerSeries.derivative K).map_one_eq_zero
      rw [this]; exact Function.iterate_fixed (map_zero _) i
    rw [h4] at h
    rw [(mul_eq_zero.1 h).resolve_left h3]
    simp [coeff_C, coeff_X]

theorem constantCoeff_φ₂ (l : ℕ) [Fact l.Prime] (φ₂ : K⟦X⟧⟦X⟧ →+* K⟦X⟧⟦X⟧)
    (hφC : ∀ f : K⟦X⟧, φ₂ (PowerSeries.C f) = PowerSeries.C (frob K l f))
    (hφsh : ∀ f : K⟦X⟧, φ₂ (sh f) = sh (frob K l f)) (G : K⟦X⟧⟦X⟧) :
    constantCoeff (φ₂ G) = frob K l (constantCoeff G) := by
  have hX : φ₂ X = sh (X ^ l) - C (X ^ l) := by
    have h : (X : K⟦X⟧⟦X⟧) = sh X - C X := by rw [sh_X sh hsh]; ring
    rw [h, map_sub, hφsh, hφC, frob_X]
  conv_lhs => rw [eq_shift_mul_X_add_const G]
  rw [map_add, map_mul, hX, hφC, map_add, map_mul, map_sub, constantCoeff_sh sh hsh, constantCoeff_C,
    constantCoeff_C, sub_self, mul_zero, zero_add]

end Sh

section Maps

variable {a : ℕ} [NeZero a] {O K : Type} [CommRing O] [Algebra ℤ_[l] O]
  [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] (t : Wq l a →ₐ[ℤ_[l]] O) (e : ℕ)

theorem frob_toAc (x : (Wq l a)⟦X⟧) (τ : ZMod a) :
    frob K l (toAc t K x (τ - 1) : K⟦X⟧) = (toAc t K (frobS l a x) τ : K⟦X⟧) := by
  ext n
  have : coeff n (frobS l a x) = if l ∣ n then sigma l a (coeff (n / l) x) else 0 := by
    simp only [frobS, RingHom.comp_apply, coeff_map, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, coeff_expand]
    split_ifs <;> simp
  rw [coeff_frob, coeff_toAc, coeff_toAc, this]
  split_ifs
  · rw [emb_sigma]
  · simp

theorem constP_mem {F : ZMod a → K⟦X⟧} (hF : F ∈ SdSet t K e) : constP a K F ∈ PPSet t K e := by
  obtain ⟨w, hw, hF⟩ := hF
  refine ⟨fun p => if p.1 = 0 then w p.2 else 0, fun r => ?_, fun τ i n => ?_⟩
  · have h := hw r
    rw [Filter.eventually_cofinite] at h ⊢
    refine (h.image fun n => ((0 : ℕ), n)).subset ?_
    rintro ⟨i, n⟩ hin
    by_cases hi : i = 0
    · subst hi; exact ⟨n, by simpa using hin, rfl⟩
    · simp [hi] at hin
  · change ((i.factorial * (n / e).factorial : ℕ) : K) * coeff n (coeff i (C (F τ))) = _
    rw [coeff_C]
    by_cases hi : i = 0
    · subst hi; simpa using hF τ n
    · simp [hi]

theorem diag_mem {F : ZMod a → K⟦X⟧⟦X⟧} (hF : F ∈ PPSet t K e) : diag a K F ∈ SdSet t K e := by
  obtain ⟨w, hw, hF⟩ := hF
  refine ⟨fun n => w (0, n), fun r => ?_, fun τ n => ?_⟩
  · have h := hw r
    rw [Filter.eventually_cofinite] at h ⊢
    exact h.preimage (fun _ _ _ _ h => by simpa using h)
  · have h := hF τ 0 n
    simp only [Nat.factorial_zero, one_mul, coeff_zero_eq_constantCoeff] at h
    exact h

end Maps

end GlobalTheory.CrysPrism
