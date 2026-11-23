import Mathlib
import Development.AbelianVarietyTheory.Definitions.Jets.CmLatticeCommutatorPairingPowEqOneOfGoodLift
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.CpTransportedTaylorSeriesInChartRingHomLaws
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.CmLatticeHeisenbergRelationsOneVariableStatement
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.TranslateCoprimeOrderNotIncreaseThetaCombNormStatement

open PowerSeries GlobalTheory.MomOne
open scoped ComplexConjugate BigOperators Topology

namespace GlobalTheory.MomOne.TranslNorm

theorem even_of_inOK_half {d : ℕ} (hd : 0 < d) {s : ℕ} (h : InOK d ((s : ℂ) / 2)) : 2 ∣ s := by
  obtain ⟨u, v, h⟩ := h
  have hs : Real.sqrt d ≠ 0 := by
    have : (0 : ℝ) < d := by exact_mod_cast hd
    exact (Real.sqrt_pos.mpr this).ne'
  have him := congrArg Complex.im h
  have hre := congrArg Complex.re h
  simp [wK] at him hre
  have hv : v = 0 := by
    rcases him with h | h
    · exact h
    · exfalso
      first | exact hs h | omega
  subst hv
  have h2 : (s : ℝ) = 2 * u := by
    simp at hre
    linarith
  have h3 : (s : ℤ) = 2 * u := by exact_mod_cast h2
  omega

theorem inOK_add {d : ℕ} {x y : ℂ} (hx : InOK d x) (hy : InOK d y) : InOK d (x + y) := by
  obtain ⟨u, v, rfl⟩ := hx
  obtain ⟨u', v', rfl⟩ := hy
  exact ⟨u + u', v + v', by push_cast; ring⟩

theorem inOK_int_mul {d : ℕ} (k : ℤ) {x : ℂ} (hx : InOK d x) : InOK d ((k : ℂ) * x) := by
  obtain ⟨u, v, rfl⟩ := hx
  exact ⟨k * u, k * v, by push_cast; ring⟩

theorem primeTo_add {d q : ℕ} {x y : ℂ} (hx : PrimeTo d q x) (hy : PrimeTo d q y) :
    PrimeTo d q (x + y) := by
  obtain ⟨s, hs, hsq, hx⟩ := hx
  obtain ⟨r, hr, hrq, hy⟩ := hy
  refine ⟨s * r, Nat.mul_pos hs hr, Nat.Coprime.mul_left hsq hrq, ?_⟩
  have := inOK_add (inOK_int_mul (r : ℤ) hx) (inOK_int_mul (s : ℤ) hy)
  convert this using 1
  push_cast
  ring

theorem norm_law : ∀ (d q : ℕ) [Fact q.Prime] (M : Mdl q) (ω : ℂ_[q]) (θ : ℂ → ℂ), d.Prime → d % 16 = 7 → Split d q → IsOK d M.L → M.MChart ω → IsTh d θ → ∀ (a m : ℕ) (c : Fin m → ℂ_[q]) (s : Fin m → ℂ) (t : ℂ) (B : ℝ), (∀ j, PrimeTo d q (s j)) → PrimeTo d q t → Bd B (∑ j, C (c j) * hat M.ι (C ω * logS) (U1 d (s j) θ) ^ a) → Bd B (∑ j, C (c j) * hat M.ι (C ω * logS) (U1 d t (U1 d (s j) θ)) ^ a) := by
  intro d q hq M ω θ hd hd16 hsp hL hM hθ a m c s t B hs ht hB
  have law0 := GlobalTheory.T.translate_coprime_order_not_increase_theta_comb_norm d q M ω θ hd hd16 hsp hL hM hθ a m
  by_cases hhalf : InOK d (t - 1 / 2)
  swap
  · exact law0 c s t B hs ht hhalf hB
  have hd0 : 0 < d := hd.pos
  obtain ⟨hUU, -, hdiff, -⟩ := GlobalTheory.T.cmLattice_heisenberg_relations_one_variable d hd0
  obtain ⟨hlaws, hconst, -⟩ := GlobalTheory.MomOne.TaylorRead.hat_laws q M.ι (C ω * logS) hM.2.1
  have hcm : ∀ (r : ℂ) (F : ℂ → ℂ), Differentiable ℂ F →
      hat M.ι (C ω * logS) (fun z => r * F z) = C (M.ι r) * hat M.ι (C ω * logS) F := by
    intro r F hF
    rw [← hconst r]
    exact (hlaws (fun _ => r) F analyticAt_const (hF.analyticAt 0)).2.1
  have hτ : PrimeTo d q (t / 2) := by
    obtain ⟨n, hn, hnq, hnt⟩ := ht
    have h2 : 2 ∣ n := by
      apply even_of_inOK_half hd0
      have := inOK_add hnt (inOK_int_mul (-(n : ℤ)) hhalf)
      convert this using 1
      push_cast
      ring
    refine ⟨n * n, Nat.mul_pos hn hn, Nat.Coprime.mul_left hnq hnq, ?_⟩
    obtain ⟨k, hk⟩ := h2
    have := inOK_int_mul (k : ℤ) hnt
    convert this using 1
    have hk' : (n : ℂ) = 2 * k := by exact_mod_cast hk
    push_cast
    rw [hk']
    ring
  have hτ' : ¬ InOK d (t / 2 - 1 / 2) := by
    intro h
    have h1 : InOK d 1 := ⟨1, 0, by simp⟩
    have h2 : 2 ∣ 1 := by
      apply even_of_inOK_half hd0
      have := inOK_add (inOK_add (inOK_int_mul 2 h) h1) (inOK_int_mul (-1) hhalf)
      convert this using 1
      push_cast
      ring
    omega
  have hdouble : ∀ F : ℂ → ℂ, U1 d (t / 2) (U1 d (t / 2) F) = U1 d t F := by
    intro F
    rw [hUU]
    have him : (h1 d (t / 2) (t / 2)).im = 0 := by
      rw [h1, Complex.mul_conj, ← Complex.ofReal_mul, Complex.ofReal_im]
    funext z
    rw [him, add_halves]
    simp
  set r : Fin m → ℂ := fun j =>
    Complex.exp (-(Real.pi : ℂ) * Complex.I * (((h1 d (t / 2) (s j)).im : ℝ) : ℂ)) with hr
  have hstep : ∀ j, U1 d (t / 2) (U1 d (s j) θ) = fun z => r j * U1 d (t / 2 + s j) θ z :=
    fun j => hUU _ _ _
  have hD : ∀ j, Differentiable ℂ (U1 d (t / 2 + s j) θ) := fun j => (hdiff _ _ hθ.1).1
  have h1 := law0 c s (t / 2) B hs hτ hτ' hB
  have h2 : Bd B (∑ j, C (c j * M.ι (r j) ^ a) *
      hat M.ι (C ω * logS) (U1 d (t / 2 + s j) θ) ^ a) := by
    convert h1 using 2 with j
    rw [hstep j, hcm _ _ (hD j), mul_pow, map_mul, map_pow, mul_assoc]
  have h3 := law0 _ _ (t / 2) B (fun j => primeTo_add hτ (hs j)) hτ hτ' h2
  convert h3 using 2 with j
  have : U1 d t (U1 d (s j) θ) = fun z => r j * U1 d (t / 2) (U1 d (t / 2 + s j) θ) z := by
    rw [← hdouble, hstep j]
    funext z
    simp only [U1]
    ring
  rw [this, hcm _ _ (hdiff _ _ (hD j)).1, mul_pow, map_mul, map_pow, mul_assoc]

end GlobalTheory.MomOne.TranslNorm
