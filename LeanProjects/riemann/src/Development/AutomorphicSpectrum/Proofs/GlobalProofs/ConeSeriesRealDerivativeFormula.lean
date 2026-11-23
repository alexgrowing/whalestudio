import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.SiegelKlingenDeligneRibet
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.AbelContinuation
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.PartialSum

set_option autoImplicit false

noncomputable section

open NumberField Formalism.MainNotions.ShortIntervalPrimes GlobalTheory.RayZeta GlobalTheory.CompanionTheory.Hypotheses₂.Shintani GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel

namespace GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel.DerivDLR

variable {ι : Type} [Fintype ι] [DecidableEq ι] {r : ℕ}

lemma linF_line (a : ι → Fin r → ℝ) (b : ι → ℝ) (j : ι) (x : Fin r → ℝ) (i : Fin r) (t : ℝ) :
    linF a b j (x + t • (Pi.single i 1 : Fin r → ℝ)) = linF a b j x + t * a j i := by
  have h : ∀ k, a j k * (x + t • (Pi.single i 1 : Fin r → ℝ)) k
      = a j k * x k + (if k = i then t * a j i else 0) := by
    intro k
    by_cases hk : k = i
    · subst hk; simp; ring
    · simp [Pi.single_apply, hk]
  simp only [linF, h, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  ring

lemma linF_pos (a : ι → Fin r → ℝ) (b : ι → ℝ) (ha : ∀ j i, 0 < a j i) (hb : ∀ j, 0 < b j)
    (j : ι) (y : Fin r → ℝ) (hy : ∀ k, 0 ≤ y k) : 0 < linF a b j y := by
  have : 0 ≤ ∑ i, a j i * y i :=
    Finset.sum_nonneg fun i _ => mul_nonneg (ha j i).le (hy i)
  have := hb j
  unfold linF
  linarith

lemma hasDerivAt_factor (a : ι → Fin r → ℝ) (b : ι → ℝ) (w : ℂ) (j : ι) (i : Fin r)
    (x : Fin r → ℝ) (τ : ℝ)
    (hpos : 0 < linF a b j (x + τ • (Pi.single i 1 : Fin r → ℝ))) :
    HasDerivAt (fun t : ℝ => ((linF a b j (x + t • (Pi.single i 1 : Fin r → ℝ)) : ℝ) : ℂ) ^ w)
      ((a j i : ℂ) * (w * ((linF a b j (x + τ • (Pi.single i 1 : Fin r → ℝ)) : ℝ) : ℂ) ^ (w - 1))) τ := by
  have hlin : HasDerivAt (fun t : ℝ => linF a b j (x + t • (Pi.single i 1 : Fin r → ℝ))) (a j i) τ := by
    have : (fun t : ℝ => linF a b j (x + t • (Pi.single i 1 : Fin r → ℝ)))
        = fun t : ℝ => linF a b j x + t * a j i := by
      funext t; exact linF_line a b j x i t
    rw [this]
    simpa using ((hasDerivAt_id τ).mul_const (a j i)).const_add (linF a b j x)
  have hC := hlin.ofReal_comp
  have hslit : ((linF a b j (x + τ • (Pi.single i 1 : Fin r → ℝ)) : ℝ) : ℂ) ∈ Complex.slitPlane :=
    Complex.ofReal_mem_slitPlane.2 hpos
  have hpow := ((hasDerivAt_id _).cpow_const (c := w) hslit)
  refine (HasDerivAt.scomp τ hpow hC).congr_deriv ?_
  simp only [id, mul_one, smul_eq_mul]
  rfl

lemma hasDerivAt_Fr (a : ι → Fin r → ℝ) (b : ι → ℝ) (ha : ∀ j i, 0 < a j i) (hb : ∀ j, 0 < b j)
    (s : ℂ) (β : ι → ℕ) (i : Fin r) (x : Fin r → ℝ) (τ : ℝ)
    (hy : ∀ k, 0 ≤ (x + τ • (Pi.single i 1 : Fin r → ℝ)) k) :
    HasDerivAt (fun t : ℝ => Fr a b s β (x + t • (Pi.single i 1 : Fin r → ℝ)))
      (∑ j, (-s - (β j : ℂ)) * (a j i : ℂ) *
        Fr a b s (β + Pi.single j 1) (x + τ • (Pi.single i 1 : Fin r → ℝ))) τ := by
  have hprod := HasDerivAt.fun_finset_prod (u := Finset.univ)
    (f := fun j (t : ℝ) => ((linF a b j (x + t • (Pi.single i 1 : Fin r → ℝ)) : ℝ) : ℂ) ^ (-s - (β j : ℂ)))
    (x := τ)
    (fun j _ => hasDerivAt_factor a b (-s - (β j : ℂ)) j i x τ (linF_pos a b ha hb j _ hy))
  refine hprod.congr_deriv ?_
  refine Finset.sum_congr rfl fun j _ => ?_
  have hF : Fr a b s (β + Pi.single j 1) (x + τ • (Pi.single i 1 : Fin r → ℝ))
      = ((linF a b j (x + τ • (Pi.single i 1 : Fin r → ℝ)) : ℝ) : ℂ) ^ (-s - (β j : ℂ) - 1) *
        ∏ k ∈ Finset.univ.erase j,
          ((linF a b k (x + τ • (Pi.single i 1 : Fin r → ℝ)) : ℝ) : ℂ) ^ (-s - (β k : ℂ)) := by
    unfold Fr
    rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ j)]
    congr 1
    · congr 1
      simp only [Pi.add_apply, Pi.single_eq_same]
      push_cast
      ring
    · refine Finset.prod_congr rfl fun k hk => ?_
      have hkj : k ≠ j := Finset.ne_of_mem_erase hk
      simp [Pi.single_apply, hkj]
  rw [hF, smul_eq_mul]
  ring

theorem hasDerivAt_DLR_Fr (ι : Type) [Fintype ι] [DecidableEq ι] (r : ℕ) (a : ι → Fin r → ℝ)
    (b : ι → ℝ) (ha : ∀ j i, 0 < a j i) (hb : ∀ j, 0 < b j)
    (s : ℂ) (β : ι → ℕ) (cs : List (Fin r)) (i : Fin r) (x : Fin r → ℝ) (τ : ℝ)
    (hx : ∀ k, 0 ≤ x k) (hτ : 0 ≤ τ) :
    HasDerivAt (fun t : ℝ => DLR cs (Fr a b s β) (x + t • (Pi.single i 1 : Fin r → ℝ)))
      (∑ j, (-s - (β j : ℂ)) * (a j i : ℂ) *
        DLR cs (Fr a b s (β + Pi.single j 1)) (x + τ • (Pi.single i 1 : Fin r → ℝ))) τ := by
  induction cs generalizing x with
  | nil =>
    have hy : ∀ k, 0 ≤ (x + τ • (Pi.single i 1 : Fin r → ℝ)) k := by
      intro k
      have : 0 ≤ τ * (Pi.single i 1 : Fin r → ℝ) k := by
        refine mul_nonneg hτ ?_
        by_cases hk : k = i
        · subst hk; simp
        · simp [Pi.single_apply, hk]
      simpa using add_nonneg (hx k) this
    simpa [DLR] using hasDerivAt_Fr a b ha hb s β i x τ hy
  | cons c cs ih =>
    have hxc : ∀ k, 0 ≤ (x + (Pi.single c 1 : Fin r → ℝ)) k := by
      intro k
      have : 0 ≤ (Pi.single c 1 : Fin r → ℝ) k := by
        by_cases hk : k = c
        · subst hk; simp
        · simp [Pi.single_apply, hk]
      simpa using add_nonneg (hx k) this
    have hsw : ∀ (G : (Fin r → ℝ) → ℂ) (t : ℝ),
        DLR (c :: cs) G (x + t • (Pi.single i 1 : Fin r → ℝ))
          = DLR cs G ((x + (Pi.single c 1 : Fin r → ℝ)) + t • (Pi.single i 1 : Fin r → ℝ))
            - DLR cs G (x + t • (Pi.single i 1 : Fin r → ℝ)) := by
      intro G t
      have : x + t • (Pi.single i 1 : Fin r → ℝ) + (Pi.single c 1 : Fin r → ℝ)
          = (x + (Pi.single c 1 : Fin r → ℝ)) + t • (Pi.single i 1 : Fin r → ℝ) := by abel
      change fdR c (DLR cs G) _ = _
      simp only [fdR, this]
    have h := (ih (x + Pi.single c 1) hxc).sub (ih x hx)
    refine (h.congr_deriv ?_).congr_of_eventuallyEq (Filter.Eventually.of_forall fun t => hsw _ t)
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hsw, mul_sub]

end GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel.DerivDLR
