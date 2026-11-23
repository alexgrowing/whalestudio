import Mathlib
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PhiFree
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IntegersCompleteDVR
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RingsCyclotomic

noncomputable section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module

namespace GlobalTheory.NL.FreeEE

section Abstract

variable {A E : Type} [CommRing A] [CommRing E] (ι : A →+* E) (φE : E →+* E) {N : ℕ} (e : Fin N → A)

def comb (c : Fin N → E) : E := ∑ j, ι (e j) * φE (c j)

theorem comb_add_mul (c d : Fin N → E) (r : E) (hr : φE r = r) :
    comb ι φE e (fun j => c j + r * d j) = comb ι φE e c + r * comb ι φE e d := by
  simp only [comb, map_add, map_mul, hr, mul_add, Finset.sum_add_distrib, Finset.mul_sum]
  congr 1
  exact Finset.sum_congr rfl fun j _ => by ring

theorem comb_zero : comb ι φE e 0 = 0 := by simp [comb]

theorem comb_sub (c d : Fin N → E) : comb ι φE e (c - d) = comb ι φE e c - comb ι φE e d := by
  simp [comb, mul_sub, Finset.sum_sub_distrib]

theorem eq_zero_of_dvd (p : ℕ) [hH : IsHausdorff (Ideal.span {(p : E)}) E] (x : E)
    (h : ∀ k, (p : E) ^ k ∣ x) : x = 0 := by
  refine hH.haus' x fun k => ?_
  rw [SModEq.zero, Ideal.span_singleton_pow, smul_eq_mul, Ideal.mul_top, Ideal.mem_span_singleton]
  exact h k

theorem torsionFree (p : ℕ) [IsHausdorff (Ideal.span {(p : E)}) E] (π : A) (hπ : IsUnit (ι π))
    (hd : ∀ (x : E) (k : ℕ), ∃ (a : A) (m : ℕ), x * ι (π ^ m) - ι a ∈ Ideal.span {(p : E) ^ k})
    (hs : ∀ (a : A) (k : ℕ), ι a ∈ Ideal.span {(p : E) ^ k} → ∃ b : A, a = (p : A) ^ k * b)
    (hA : ∀ a : A, (p : A) * a = 0 → a = 0) (x : E) (hx : (p : E) * x = 0) : x = 0 := by
  refine eq_zero_of_dvd p x fun k => ?_
  obtain ⟨a, m, ham⟩ := hd x (k + 1)
  obtain ⟨y, hy⟩ := Ideal.mem_span_singleton.1 ham
  have h1 : ι ((p : A) * a) ∈ Ideal.span {(p : E) ^ (k + 2)} :=
    Ideal.mem_span_singleton.2 ⟨-y, by
      rw [map_mul, map_natCast]; linear_combination (-(p : E)) * hy + ι (π ^ m) * hx⟩
  obtain ⟨b, hb⟩ := hs _ _ h1
  have ha : a = (p : A) ^ (k + 1) * b := sub_eq_zero.1 (hA _ (by linear_combination hb))
  simp only [ha, map_mul, map_pow, map_natCast] at hy
  obtain ⟨u, hu⟩ := hπ
  have e1 : x = x * ι π ^ m * ((u⁻¹ : Eˣ) : E) ^ m := by
    rw [mul_assoc, ← mul_pow, ← hu, Units.mul_inv, one_pow, mul_one]
  refine ⟨(p : E) * (ι b + y) * ((u⁻¹ : Eˣ) : E) ^ m, ?_⟩
  rw [e1]
  linear_combination ((u⁻¹ : Eˣ) : E) ^ m * hy

theorem step_surj (p : ℕ) (π : A) (hπ : IsUnit (ι π)) (φA : A →+* A)
    (hφ : ∀ a, φE (ι a) = ι (φA a)) (Q : A) (hQ : φA π = π * Q)
    (hd : ∀ (x : E) (k : ℕ), ∃ (a : A) (m : ℕ), x * ι (π ^ m) - ι a ∈ Ideal.span {(p : E) ^ k})
    (hb : ∀ y : A, ∃ c : Fin N → A, y = ∑ j, e j * φA (c j)) (x : E) :
    ∃ (c : Fin N → E) (y : E), x = comb ι φE e c + (p : E) * y := by
  obtain ⟨a, m, ham⟩ := hd x 1
  obtain ⟨y, hy⟩ := Ideal.mem_span_singleton.1 ham
  obtain ⟨u, hu⟩ := hπ
  set v : E := ((u⁻¹ : Eˣ) : E) with hvdef
  have hv : ι π * v = 1 := by rw [← hu]; exact u.mul_inv
  have hvQ : v = ι Q * φE v := by
    have h1 : φE (ι π) * φE v = 1 := by rw [← map_mul, hv, map_one]
    rw [hφ, hQ, map_mul] at h1
    calc v = v * (ι π * ι Q * φE v) := by rw [h1, mul_one]
      _ = (ι π * v) * (ι Q * φE v) := by ring
      _ = _ := by rw [hv, one_mul]
  have hvm : v ^ m = ι (Q ^ m) * φE (v ^ m) := by rw [map_pow, map_pow, ← mul_pow, ← hvQ]
  obtain ⟨c, hc⟩ := hb (a * Q ^ m)
  refine ⟨fun j => ι (c j) * v ^ m, y * v ^ m, ?_⟩
  have hx : x = ι a * v ^ m + (p : E) * (y * v ^ m) := by
    calc x = x * ι (π ^ m) * v ^ m := by rw [map_pow, mul_assoc, ← mul_pow, hv, one_pow, mul_one]
      _ = _ := by linear_combination v ^ m * hy
  have h2 : ι a * v ^ m = comb ι φE e (fun j => ι (c j) * v ^ m) := by
    calc ι a * v ^ m = ι (a * Q ^ m) * φE (v ^ m) := by rw [map_mul, mul_assoc, ← hvm]
      _ = _ := by
        rw [hc]
        simp only [comb, map_sum, map_mul, hφ, Finset.sum_mul]
        exact Finset.sum_congr rfl fun j _ => by ring
  rw [← h2]
  exact hx

theorem surj (p : ℕ) [IsAdicComplete (Ideal.span {(p : E)}) E]
    (step : ∀ x : E, ∃ (c : Fin N → E) (y : E), x = comb ι φE e c + (p : E) * y) (x : E) :
    ∃ c, x = comb ι φE e c := by
  choose C Y hCY using step
  let sq : ℕ → E := fun k => Nat.rec x (fun _ z => Y z) k
  let S : ℕ → Fin N → E := fun n j => ∑ k ∈ Finset.range n, (p : E) ^ k * C (sq k) j
  have hS : ∀ n, x = comb ι φE e (S n) + (p : E) ^ n * sq n := by
    intro n
    induction n with
    | zero => simp [S, sq, comb]
    | succ n ih =>
      have h1 : S (n + 1) = fun j => S n j + (p : E) ^ n * C (sq n) j := by
        funext j; simp [S, Finset.sum_range_succ]
      have h2 : sq (n + 1) = Y (sq n) := rfl
      rw [h1, comb_add_mul ι φE e _ _ _ (by simp), h2]
      linear_combination ih + (p : E) ^ n * hCY (sq n)
  have hcau : ∀ j, ∃ L : E, ∀ n, S n j ≡ L [SMOD (Ideal.span {(p : E)} ^ n • ⊤ : Submodule E E)] := by
    intro j
    refine IsPrecomplete.prec' (I := Ideal.span {(p : E)}) (fun n => S n j) fun {m n} hmn => ?_
    rw [SModEq.sub_mem, Ideal.span_singleton_pow, smul_eq_mul, Ideal.mul_top, Ideal.mem_span_singleton]
    have : S n j = S m j + ∑ k ∈ Finset.Ico m n, (p : E) ^ k * C (sq k) j := by
      simp only [S]; rw [Finset.sum_range_add_sum_Ico _ hmn]
    rw [this, sub_add_cancel_left]
    exact dvd_neg.2 (Finset.dvd_sum fun k hk => (pow_dvd_pow _ (Finset.mem_Ico.1 hk).1).mul_right _)
  choose L hL using hcau
  refine ⟨L, sub_eq_zero.1 (eq_zero_of_dvd p _ fun n => ?_)⟩
  have hd : ∀ j, ∃ d, S n j = L j + (p : E) ^ n * d := fun j => by
    have := hL j n
    rw [SModEq.sub_mem, Ideal.span_singleton_pow, smul_eq_mul, Ideal.mul_top,
      Ideal.mem_span_singleton] at this
    obtain ⟨d, hd⟩ := this
    exact ⟨d, by linear_combination hd⟩
  choose d hd using hd
  have h1 : S n = fun j => L j + (p : E) ^ n * d j := funext hd
  have h2 := hS n
  rw [h1, comb_add_mul ι φE e _ _ _ (by simp)] at h2
  exact ⟨comb ι φE e d + sq n, by linear_combination h2⟩

theorem step_inj (p : ℕ) (π : A) (hπ : IsUnit (ι π)) (φA : A →+* A)
    (hφ : ∀ a, φE (ι a) = ι (φA a))
    (hd : ∀ (x : E) (k : ℕ), ∃ (a : A) (m : ℕ), x * ι (π ^ m) - ι a ∈ Ideal.span {(p : E) ^ k})
    (hs : ∀ (a : A) (k : ℕ), ι a ∈ Ideal.span {(p : E) ^ k} → ∃ b : A, a = (p : A) ^ k * b)
    (hb : ∀ y : A, ∃! c : Fin N → A, y = ∑ j, e j * φA (c j)) (c : Fin N → E)
    (hc : (p : E) ∣ comb ι φE e c) : ∀ j, (p : E) ∣ c j := by
  obtain ⟨u, hu⟩ := hπ
  set v : E := ((u⁻¹ : Eˣ) : E) with hvdef
  have hv : ι π * v = 1 := by rw [← hu]; exact u.mul_inv
  choose a m ham using fun j => hd (c j) 1
  choose y hy using fun j => Ideal.mem_span_singleton.1 (ham j)
  set M := ∑ j, m j with hM
  have hmM : ∀ j, m j ≤ M := fun j =>
    Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)
  let a' : Fin N → A := fun j => a j * π ^ (M - m j)
  let y' : Fin N → E := fun j => y j * ι (π ^ (M - m j)) * v ^ M
  have hca : ∀ j, c j = ι (a' j) * v ^ M + (p : E) * y' j := by
    intro j
    have e2 : ι (π ^ M) = ι (π ^ m j) * ι (π ^ (M - m j)) := by
      rw [← map_mul, ← pow_add, Nat.add_sub_cancel' (hmM j)]
    calc c j = c j * ι (π ^ M) * v ^ M := by
          rw [map_pow, mul_assoc, ← mul_pow, hv, one_pow, mul_one]
      _ = _ := by
        rw [e2]
        simp only [a', y', map_mul]
        linear_combination (ι (π ^ (M - m j)) * v ^ M) * hy j
  have hsum : ι (∑ j, e j * φA (a' j)) * φE (v ^ M) =
      comb ι φE e c - (p : E) * comb ι φE e y' := by
    have : c = fun j => ι (a' j) * v ^ M + (p : E) * y' j := funext hca
    rw [this, comb_add_mul ι φE e _ _ _ (by simp), add_sub_cancel_right]
    simp only [comb, map_sum, map_mul, hφ, Finset.sum_mul]
    exact Finset.sum_congr rfl fun j _ => by ring
  have hdv : ι (∑ j, e j * φA (a' j)) ∈ Ideal.span {(p : E) ^ 1} := by
    rw [pow_one, Ideal.mem_span_singleton]
    have hw : φE (v ^ M) * φE (ι (π ^ M)) = 1 := by
      rw [← map_mul, map_pow, ← mul_pow, mul_comm v, hv, one_pow, map_one]
    have : ι (∑ j, e j * φA (a' j)) =
        (comb ι φE e c - (p : E) * comb ι φE e y') * φE (ι (π ^ M)) := by
      rw [← hsum, mul_assoc, hw, mul_one]
    rw [this]
    exact (dvd_sub hc (dvd_mul_right _ _)).mul_right _
  obtain ⟨b, hb'⟩ := hs _ 1 hdv
  obtain ⟨bc, hbc, -⟩ := hb b
  have huniq : a' = fun j => (p : A) * bc j := by
    apply (hb (∑ j, e j * φA (a' j))).unique rfl
    rw [hb', hbc, pow_one, Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by simp only [map_mul, map_natCast]; ring
  intro j
  rw [hca j, show a' j = (p : A) * bc j from congrFun huniq j, map_mul, map_natCast]
  exact ⟨ι (bc j) * v ^ M + y' j, by ring⟩

theorem inj (p : ℕ) [IsHausdorff (Ideal.span {(p : E)}) E]
    (tf : ∀ x : E, (p : E) * x = 0 → x = 0)
    (sinj : ∀ c : Fin N → E, (p : E) ∣ comb ι φE e c → ∀ j, (p : E) ∣ c j) :
    ∀ c, comb ι φE e c = 0 → c = 0 := by
  have key : ∀ (k : ℕ) (c : Fin N → E), comb ι φE e c = 0 → ∀ j, (p : E) ^ k ∣ c j := by
    intro k
    induction k with
    | zero => intro c _ j; simp
    | succ k ih =>
      intro c hc
      choose c' hc' using sinj c (hc ▸ dvd_zero _)
      have h1 : c = fun j => (0 : Fin N → E) j + (p : E) * c' j :=
        funext fun j => by rw [hc' j, Pi.zero_apply, zero_add]
      have h2 : comb ι φE e c' = 0 := by
        apply tf
        rw [h1, comb_add_mul ι φE e _ _ _ (by simp), comb_zero, zero_add] at hc
        exact hc
      intro j
      rw [hc' j, pow_succ']
      exact mul_dvd_mul_left _ (ih c' h2 j)
  intro c hc
  funext j
  exact eq_zero_of_dvd p _ fun k => key k c hc j

theorem free (p : ℕ) [IsAdicComplete (Ideal.span {(p : E)}) E] (π : A) (φA : A →+* A)
    (hπ : IsUnit (ι π)) (hφ : ∀ a, φE (ι a) = ι (φA a)) (Q : A) (hQ : φA π = π * Q)
    (hd : ∀ (x : E) (k : ℕ), ∃ (a : A) (m : ℕ), x * ι (π ^ m) - ι a ∈ Ideal.span {(p : E) ^ k})
    (hs : ∀ (a : A) (k : ℕ), ι a ∈ Ideal.span {(p : E) ^ k} → ∃ b : A, a = (p : A) ^ k * b)
    (hA : ∀ a : A, (p : A) * a = 0 → a = 0)
    (hb : ∀ y : A, ∃! c : Fin N → A, y = ∑ j, e j * φA (c j)) :
    ∀ x : E, ∃! c : Fin N → E, x = ∑ j, ι (e j) * φE (c j) := by
  intro x
  obtain ⟨c, hc⟩ := surj ι φE e p
    (step_surj ι φE e p π hπ φA hφ Q hQ hd fun y => (hb y).exists) x
  refine ⟨c, hc, fun c' hc' => ?_⟩
  have h0 := inj ι φE e p (torsionFree ι p π hπ hd hs hA)
    (step_inj ι φE e p π hπ φA hφ hd hs hb) (c' - c)
    (by rw [comb_sub]; exact sub_eq_zero.2 (hc'.symm.trans hc))
  exact sub_eq_zero.1 h0

end Abstract

set_option maxHeartbeats 1000000 in

theorem ee_free : ∀ (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL), let W := (HW l).W K s LL h; ∀ x : W.EE, ∃! c : Fin l → W.EE, x = ∑ j : Fin l, algebraMap (LetA ↥(OL LL) (Module.finrank ℚ_[l] ↥(K0 K))) W.EE ((1 : (LetA ↥(OL LL) (Module.finrank ℚ_[l] ↥(K0 K)))) + (letπ : (LetA ↥(OL LL) (Module.finrank ℚ_[l] ↥(K0 K))))) ^ (j : ℕ) * W.φE (c j) := by
  intro D HW F l _ K s LL h W
  obtain ⟨hdvr, hcomp, hl0, hlu, -⟩ := GlobalTheory.Per.integers_completeDVR l LL
  have hφ : W.φ₀ = GlobalTheory.Cyc.phi l ↥(OL LL) :=
    (GlobalTheory.NL.CycRing.rings_cyclotomic D HW l K s LL h).choose_spec.2.1
  have hp : ((D.loc l).PD K).p = l := (D.loc l).PD_p K
  haveI := W.EE_complete
  have hl0' : ((l : ℕ) : PowerSeries ↥(OL LL)) ≠ 0 := by
    intro h0
    apply hl0
    have := congrArg PowerSeries.constantCoeff h0
    simpa using this
  have hA : ∀ a : LetA ↥(OL LL) (Module.finrank ℚ_[l] ↥(K0 K)),
      (((D.loc l).PD K).p : LetA ↥(OL LL) (Module.finrank ℚ_[l] ↥(K0 K))) * a = 0 → a = 0 := by
    intro a ha
    funext i
    have := congrFun ha i
    simp only [Pi.mul_apply, Pi.natCast_apply, Pi.zero_apply, hp] at this ⊢
    exact (mul_eq_zero.1 this).resolve_left hl0'
  have hQ : letφ W.φ₀ (letπ : LetA ↥(OL LL) (Module.finrank ℚ_[l] ↥(K0 K))) =
      letπ * fun _ => W.q₀ := by
    funext i
    simp only [letφ, AlgHom.pi_apply, AlgHom.comp_apply, Pi.evalAlgHom_apply, letπ, Pi.mul_apply]
    exact W.φ₀_X
  have key : ∀ (c : Fin l → LetA ↥(OL LL) (Module.finrank ℚ_[l] ↥(K0 K)))
      (i : ZMod (Module.finrank ℚ_[l] ↥(K0 K))),
      (∑ j : Fin l, ((1 + letπ) ^ (j : ℕ) * letφ W.φ₀ (c j) :
        LetA ↥(OL LL) (Module.finrank ℚ_[l] ↥(K0 K)))) i =
        ∑ j : Fin l, (1 + PowerSeries.X) ^ (j : ℕ) * GlobalTheory.Cyc.phi l ↥(OL LL) (c j (i - 1)) := by
    intro c i
    rw [Finset.sum_apply]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [Pi.mul_apply, Pi.pow_apply, Pi.add_apply, Pi.one_apply, letπ, letφ, AlgHom.pi_apply,
      AlgHom.comp_apply, Pi.evalAlgHom_apply, hφ]
  have hb : ∀ y : LetA ↥(OL LL) (Module.finrank ℚ_[l] ↥(K0 K)), ∃! c : Fin l → LetA ↥(OL LL) (Module.finrank ℚ_[l] ↥(K0 K)),
      y = ∑ j : Fin l, (1 + letπ) ^ (j : ℕ) * letφ W.φ₀ (c j) := by
    intro y
    choose z hz using fun i => (GlobalTheory.Cyc.phi_free l ↥(OL LL) hl0 hlu (y i)).exists
    refine ⟨fun j i => z (i + 1) j, ?_, fun c hc => ?_⟩
    · funext i
      rw [key]
      simp only [sub_add_cancel]
      exact hz i
    · funext j i
      have h2 := congrFun hc (i + 1)
      rw [key] at h2
      have h3 := (GlobalTheory.Cyc.phi_free l ↥(OL LL) hl0 hlu (y (i + 1))).unique
        (y₁ := fun j => c j (i + 1 - 1)) h2 (hz (i + 1))
      simpa using congrFun h3 j
  intro x
  have hfree := free (algebraMap (LetA ↥(OL LL) (Module.finrank ℚ_[l] ↥(K0 K))) W.EE) W.φE.toRingHom
    (fun j : Fin l => (1 + letπ) ^ (j : ℕ)) ((D.loc l).PD K).p letπ
    (letφ W.φ₀).toRingHom
    W.EE_π (fun a => W.φE_ext a) (fun _ => W.q₀) hQ W.EE_dense W.EE_sat hA hb x
  simp only [map_pow] at hfree
  exact hfree

end GlobalTheory.NL.FreeEE
