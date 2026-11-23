import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NatCastNeZeroPs

noncomputable section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Filter
  GlobalTheory.CrysPrism
open scoped Formalism.Per

namespace GlobalTheory.CrysPrism.Compl

theorem smodEq_span_pow {R : Type} [CommRing R] (r x y : R) (n : ℕ) :
    x ≡ y [SMOD (Ideal.span {r} ^ n • ⊤ : Submodule R R)] ↔ ∃ z, x - y = r ^ n * z := by
  rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow, Ideal.mem_span_singleton']
  exact ⟨fun ⟨z, hz⟩ => ⟨z, by rw [← hz, mul_comm]⟩, fun ⟨z, hz⟩ => ⟨z, by rw [hz, mul_comm]⟩⟩

theorem natCast_ne_zero_K (l : ℕ) [Fact l.Prime] {K : Type} [NormedField K] [NormedAlgebra ℚ_[l] K] {n : ℕ}
    (hn : n ≠ 0) : (n : K) ≠ 0 := by
  rw [← map_natCast (algebraMap ℚ_[l] K) n]
  exact (map_ne_zero _).2 (Nat.cast_ne_zero.2 hn)

variable {l : ℕ} [hl : Fact l.Prime] {a : ℕ} [NeZero a] {O : Type} [CommRing O] [Algebra ℤ_[l] O]
  (t : Wq l a →ₐ[ℤ_[l]] O) (K : Type)
  [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] (e : ℕ)

def iota (τ : ZMod a) : Wq l a →+* K := (algebraMap O K).comp (emb t τ).toRingHom

variable {K}

theorem iota_injective (τ : ZMod a) : Function.Injective (iota t K τ) := by
  have := Fintype.ofFinite (Fq l a)
  rw [injective_iff_map_eq_zero]
  intro w hw
  by_contra h0
  obtain ⟨m, b, hb, rfl⟩ := WittVector.exists_eq_pow_p_mul w h0
  have hu : IsUnit b := WittVector.isUnit_of_coeff_zero_ne_zero b hb
  rw [map_mul, map_pow, map_natCast] at hw
  exact mul_ne_zero (pow_ne_zero _ (natCast_ne_zero_K l (K := K) hl.out.ne_zero)) (hu.map (iota t K τ)).ne_zero hw

include t K in
theorem prime_natCast_ne_zero_wittOfTiltFiniteField : (l : Wq l a) ≠ 0 := fun h => by
  have h1 := congrArg (iota t K 0) h
  rw [map_natCast, map_zero] at h1
  exact natCast_ne_zero_K l (K := K) hl.out.ne_zero h1

variable (K) in

def Rep (F : ZMod a → K⟦X⟧) (w : ℕ → Wq l a) : Prop :=
  ∀ τ n, ((n / e).factorial : K) * coeff n (F τ) = iota t K τ (w n)

variable {t e}

theorem rep_unique {F : ZMod a → K⟦X⟧} {w v : ℕ → Wq l a} (hw : Rep t K e F w) (hv : Rep t K e F v) : w = v :=
  funext fun n => iota_injective t 0 (by rw [← hw 0 n, ← hv 0 n])

theorem eq_of_rep {F G : ZMod a → K⟦X⟧} {w : ℕ → Wq l a} (hF : Rep t K e F w) (hG : Rep t K e G w) : F = G := by
  funext τ
  ext n
  exact mul_left_cancel₀ (natCast_ne_zero_K l (K := K) (Nat.factorial_ne_zero _)) ((hF τ n).trans (hG τ n).symm)

theorem rep_sub {F G : ZMod a → K⟦X⟧} {w v : ℕ → Wq l a} (hF : Rep t K e F w) (hG : Rep t K e G v) :
    Rep t K e (F - G) (w - v) := fun τ n => by
  simp only [Pi.sub_apply, map_sub, mul_sub, hF τ n, hG τ n]

theorem rep_pow_mul (m : ℕ) {F : ZMod a → K⟦X⟧} {w : ℕ → Wq l a} (hF : Rep t K e F w) :
    Rep t K e ((l : ZMod a → K⟦X⟧) ^ m * F) (fun n => (l : Wq l a) ^ m * w n) := fun τ n => by
  have h1 : ((l : ZMod a → K⟦X⟧) ^ m * F) τ = C ((l : K) ^ m) * F τ := by
    simp only [Pi.mul_apply, Pi.pow_apply, Pi.natCast_apply, map_pow, map_natCast]
  rw [h1, coeff_C_mul, map_mul, map_pow, map_natCast, ← hF τ n]
  ring

variable (t e) in

def ofRep (w : ℕ → Wq l a) : ZMod a → K⟦X⟧ :=
  fun τ => PowerSeries.mk fun n => iota t K τ (w n) / ((n / e).factorial : K)

theorem rep_ofRep (w : ℕ → Wq l a) : Rep t K e (ofRep (K := K) t e w) w := fun τ n => by
  rw [ofRep, coeff_mk]
  exact mul_div_cancel₀ _ (natCast_ne_zero_K l (K := K) (Nat.factorial_ne_zero _))

variable (t e) in
theorem isHausdorff_of (hsd : ∀ F ∈ Sd t K e, F ∈ SdSet t K e) :
    IsHausdorff (Ideal.span {(l : ↥(Sd t K e))}) ↥(Sd t K e) := by
  have := Fintype.ofFinite (Fq l a)
  refine ⟨fun x hx => ?_⟩
  obtain ⟨w, -, hw⟩ := hsd x.1 x.2
  have hdiv : ∀ m k, ∃ q, w k = (l : Wq l a) ^ m * q := by
    intro m k
    obtain ⟨z, hz⟩ := (smodEq_span_pow _ _ _ m).1 (hx m)
    rw [sub_zero] at hz
    obtain ⟨v, -, hv⟩ := hsd z.1 z.2
    have h1 : x.1 = (l : ZMod a → K⟦X⟧) ^ m * z.1 := by rw [hz]; push_cast; rfl
    have h2 := rep_pow_mul m hv
    rw [← h1] at h2
    exact ⟨v k, congrFun (rep_unique hw h2) k⟩
  have hw0 : w = 0 := funext fun k => IsHausdorff.haus' (I := Ideal.span {(l : Wq l a)}) (w k) fun m => by
    obtain ⟨q, hq⟩ := hdiv m k
    exact (smodEq_span_pow _ _ _ m).2 ⟨q, by rw [sub_zero, hq]⟩
  apply Subtype.ext
  refine eq_of_rep (F := x.1) (G := 0) hw ?_
  rw [hw0]
  intro τ n
  simp

variable (t e) in
theorem isPrecomplete_of (hsd : ∀ F ∈ Sd t K e, F ∈ SdSet t K e) :
    IsPrecomplete (Ideal.span {(l : ↥(Sd t K e))}) ↥(Sd t K e) := by
  have := Fintype.ofFinite (Fq l a)
  refine ⟨fun f hf => ?_⟩
  choose w hw0 hw using fun j => hsd (f j).1 (f j).2
  have hc : ∀ {m j : ℕ}, m ≤ j → ∀ k,
      w m k ≡ w j k [SMOD (Ideal.span {(l : Wq l a)} ^ m • ⊤ : Submodule (Wq l a) (Wq l a))] := by
    intro m j hmj k
    obtain ⟨z, hz⟩ := (smodEq_span_pow _ _ _ m).1 (hf hmj)
    obtain ⟨v, -, hv⟩ := hsd z.1 z.2
    have h1 : (f m).1 - (f j).1 = (l : ZMod a → K⟦X⟧) ^ m * z.1 := by
      have h0 := congrArg Subtype.val hz
      push_cast at h0
      exact h0
    have h2 := rep_pow_mul m hv
    rw [← h1] at h2
    have h3 := congrFun (rep_unique (rep_sub (hw m) (hw j)) h2) k
    exact (smodEq_span_pow _ _ _ m).2 ⟨v k, by simpa using h3⟩
  choose W hW using fun k => IsPrecomplete.prec' (I := Ideal.span {(l : Wq l a)}) (fun j => w j k)
    (fun {m j} h => hc h k)
  have hW0 : LTo0 l W := fun r => (hw0 r r).mono fun k hk => by
    obtain ⟨q, hq⟩ := (smodEq_span_pow _ _ _ r).1 (hW k r)
    have h1 : W k = w r k - (l : Wq l a) ^ r * q := by rw [← hq]; ring
    rw [h1]
    exact dvd_sub hk (dvd_mul_right _ _)
  have hLmem : ofRep (K := K) t e W ∈ Sd t K e := Subring.subset_closure ⟨W, hW0, rep_ofRep W⟩
  refine ⟨⟨_, hLmem⟩, fun n => ?_⟩
  choose v hv using fun k => (smodEq_span_pow _ _ _ n).1 (hW k n)
  have hl0 : (l : Wq l a) ^ n ≠ 0 := pow_ne_zero _ (prime_natCast_ne_zero_wittOfTiltFiniteField t (K := K))
  have hv0 : LTo0 l v := fun r => ((hw0 n (r + n)).and (hW0 (r + n))).mono fun k hk => by
    have h1 : (l : Wq l a) ^ n * (l : Wq l a) ^ r ∣ (l : Wq l a) ^ n * v k := by
      rw [← hv k, ← pow_add, add_comm]
      exact dvd_sub hk.1 hk.2
    exact (mul_dvd_mul_iff_left hl0).1 h1
  have hymem : ofRep (K := K) t e v ∈ Sd t K e := Subring.subset_closure ⟨v, hv0, rep_ofRep v⟩
  refine (smodEq_span_pow _ _ _ n).2 ⟨⟨_, hymem⟩, Subtype.ext ?_⟩
  have h1 := rep_sub (hw n) (rep_ofRep (K := K) (t := t) (e := e) W)
  have h2 := rep_pow_mul n (rep_ofRep (K := K) (t := t) (e := e) v)
  have h3 : (fun k => (l : Wq l a) ^ n * v k) = w n - W := funext fun k => by rw [Pi.sub_apply, hv k]
  rw [h3] at h2
  have h4 := eq_of_rep h1 h2
  push_cast
  exact h4

variable (t e) in

theorem isAdicComplete_of (hsd : ∀ F ∈ Sd t K e, F ∈ SdSet t K e) :
    IsAdicComplete (Ideal.span {(l : ↥(Sd t K e))}) ↥(Sd t K e) :=
  { toIsHausdorff := isHausdorff_of t e hsd, toIsPrecomplete := isPrecomplete_of t e hsd }

end GlobalTheory.CrysPrism.Compl
