import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.EeProd
import Development.AbelianVarietyTheory.Definitions.Foundations.AdmissibleTwistIffAdmissibleUntwisted
import Development.AbelianVarietyTheory.Definitions.Foundations.KumValUnique

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open GlobalTheory.KZ GlobalTheory.Glue

namespace GlobalTheory.KummerEisensteinGalois

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ} {l : ℕ} [Fact l.Prime]

def seqN (N : ℕ) (j : Ω →+* Qbar l) (φ : HahnSeries ℚ Ω) : ℕ → Qbar l := fun s => j (φ.coeff ((s : ℚ) / N))

def FinSupp (lam : (ℕ → Qbar l) →ₗ[Qbar l] Qbar l) : Prop :=
  ∃ S : Finset ℕ, ∀ f : ℕ → Qbar l, (∀ s ∈ S, f s = 0) → lam f = 0

def IsLamOf (X : Tower Ω ε) (A : ValuationSubring Ω) (N w : ℕ) (j : Ω →+* Qbar l) (pr : X.Fn l → Fin 2 → Qbar l)
    (lam : (ℕ → Qbar l) →ₗ[Qbar l] Qbar l) : Prop :=
  FinSupp lam ∧ ∃ (c : ℕ) (per : ℕ → Qbar l), (∀ n, ‖per n‖ = 1 ∧ Cg n (per (n + 1)) (per n)) ∧
    ∀ (n : ℕ) (b : X.Fn l), b ∈ X.B N l w → ∀ φ : HahnSeries ℚ Ω, IsThB X A N l n b φ →
      Cg (n - c) (lam (seqN N j φ)) (per n * pr b 1)

open Classical in

def lamOf (X : Tower Ω ε) (A : ValuationSubring Ω) (N w : ℕ) (j : Ω →+* Qbar l) (pr : X.Fn l → Fin 2 → Qbar l) :
    (ℕ → Qbar l) →ₗ[Qbar l] Qbar l :=
  if h : ∃ lam, IsLamOf X A N w j pr lam then h.choose else 0

def IsLamOfL (X : Tower Ω ε) (A : ValuationSubring Ω) (N w : ℕ) (j : Ω →+* Qbar l) (pr : X.Fn l → Fin 2 → Qbar l)
    (lam : (ℕ → Qbar l) →ₗ[Qbar l] Qbar l) : Prop :=
  FinSupp lam ∧ ∃ (c : ℕ) (per : ℕ → Qbar l), (∀ n, ‖per n‖ = 1 ∧ Cg n (per (n + 1)) (per n)) ∧
    ∀ (n : ℕ), c ≤ n → ∀ (b : X.Fn l), b ∈ X.B N l w → ∀ φ : HahnSeries ℚ Ω, IsThB X A N l n b φ →
      Cg (n - c) (lam (seqN N j φ)) (per n * pr b 1)

open Classical in

def lamOfL (X : Tower Ω ε) (A : ValuationSubring Ω) (N w : ℕ) (j : Ω →+* Qbar l) (pr : X.Fn l → Fin 2 → Qbar l) :
    (ℕ → Qbar l) →ₗ[Qbar l] Qbar l :=
  if h : ∃ lam, IsLamOfL X A N w j pr lam then h.choose else 0

theorem norm_l_pow (n : ℕ) : ‖((l : ℕ) : Qbar l) ^ n‖ = ((l : ℝ)⁻¹) ^ n := by
  have : ((l : ℕ) : Qbar l) = algebraMap ℚ_[l] (Qbar l) (l : ℚ_[l]) := by simp
  rw [norm_pow, this, norm_algebraMap', Padic.norm_p]

theorem cg_mono {m n : ℕ} (h : m ≤ n) {x y : Qbar l} (hxy : Cg n x y) : Cg m x y := by
  unfold Cg at *
  refine hxy.trans ?_
  rw [norm_l_pow, norm_l_pow]
  have h1 : (1 : ℝ) ≤ l := by exact_mod_cast (Fact.out : l.Prime).one_le
  exact pow_le_pow_of_le_one (by positivity) (inv_le_one_of_one_le₀ h1) h

theorem exists_le_l_pow (l : ℕ) [Fact l.Prime] (t : ℝ) : ∃ k : ℕ, t ≤ (l : ℝ) ^ k := by
  have h1 : (1 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).one_lt
  obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt t h1
  exact ⟨k, hk.le⟩

theorem l_pow_mul_norm {k m : ℕ} (h : k ≤ m) :
    (l : ℝ) ^ k * ‖((l : ℕ) : Qbar l) ^ m‖ = ‖((l : ℕ) : Qbar l) ^ (m - k)‖ := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
  have h0 : (l : ℝ) ≠ 0 := by exact_mod_cast (Fact.out : l.Prime).ne_zero
  rw [norm_l_pow, norm_l_pow, Nat.add_sub_cancel_left, pow_add, ← mul_assoc, ← mul_pow, mul_inv_cancel₀ h0, one_pow, one_mul]

theorem cg_sub_iff {c n : ℕ} (h : c ≤ n) (x y : Qbar l) :
    Cg (n - c) x y ↔ ‖x - y‖ ≤ (l : ℝ) ^ c * ‖((l : ℕ) : Qbar l) ^ n‖ := by
  rw [l_pow_mul_norm h]; rfl

theorem cg_mul_left {k m : ℕ} (h : k ≤ m) {a x y : Qbar l} (ha : ‖a‖ ≤ (l : ℝ) ^ k) (hxy : Cg m x y) :
    Cg (m - k) (a * x) (a * y) := by
  rw [cg_sub_iff h, ← mul_sub, norm_mul]
  exact mul_le_mul ha hxy (norm_nonneg _) (by positivity)

theorem seqN_single {N : ℕ} (hN : N ≠ 0) (j : Ω →+* Qbar l) (s : ℕ) (a : Ω) :
    seqN N j (HahnSeries.single ((s : ℚ) / N) a) = Pi.single s (j a) := by
  funext t
  have hN' : (N : ℚ) ≠ 0 := by exact_mod_cast hN
  by_cases h : t = s
  · subst h; simp [seqN]
  · have : (t : ℚ) / N ≠ (s : ℚ) / N := fun e => h (by exact_mod_cast (div_left_inj' hN').1 e)
    simp [seqN, HahnSeries.coeff_single_of_ne this, h]

theorem finSupp_proj (s : ℕ) : FinSupp (LinearMap.proj (R := Qbar l) (φ := fun _ : ℕ => Qbar l) s) :=
  ⟨{s}, fun f hf => hf s (Finset.mem_singleton_self s)⟩

theorem FinSupp.smul {lam : (ℕ → Qbar l) →ₗ[Qbar l] Qbar l} (h : FinSupp lam) (a : Qbar l) : FinSupp (a • lam) := by
  obtain ⟨S, hS⟩ := h
  exact ⟨S, fun f hf => by simp [hS f hf]⟩

theorem FinSupp.add {lam lam' : (ℕ → Qbar l) →ₗ[Qbar l] Qbar l} (h : FinSupp lam) (h' : FinSupp lam') :
    FinSupp (lam + lam') := by
  obtain ⟨S, hS⟩ := h
  obtain ⟨T, hT⟩ := h'
  exact ⟨S ∪ T, fun f hf => by
    simp [hS f fun s hs => hf s (Finset.mem_union_left _ hs), hT f fun s hs => hf s (Finset.mem_union_right _ hs)]⟩

theorem FinSupp.exists_sum {lam : (ℕ → Qbar l) →ₗ[Qbar l] Qbar l} (h : FinSupp lam) :
    ∃ S : Finset ℕ, ∀ f : ℕ → Qbar l, lam f = ∑ s ∈ S, lam (Pi.single s 1) * f s := by
  obtain ⟨S, hS⟩ := h
  refine ⟨S, fun f => ?_⟩
  have h0 := hS (f - ∑ s ∈ S, f s • (Pi.single s 1 : ℕ → Qbar l)) (fun t ht => by
    simp [Finset.sum_apply, Pi.single_apply, ht])
  rw [map_sub, map_sum, sub_eq_zero] at h0
  rw [h0]
  exact Finset.sum_congr rfl fun s _ => by rw [map_smul, smul_eq_mul, mul_comm]

theorem FinSupp.exists_loss {lam : (ℕ → Qbar l) →ₗ[Qbar l] Qbar l} (h : FinSupp lam) :
    ∃ c : ℕ, ∀ n, c ≤ n → ∀ f g : ℕ → Qbar l, (∀ s, Cg n (f s) (g s)) → Cg (n - c) (lam f) (lam g) := by
  obtain ⟨S, hS⟩ := h.exists_sum
  obtain ⟨c, hc⟩ := exists_le_l_pow l (∑ s ∈ S, ‖lam (Pi.single s 1)‖)
  refine ⟨c, fun n hn f g hfg => ?_⟩
  rw [cg_sub_iff hn, hS f, hS g, ← Finset.sum_sub_distrib]
  refine (norm_sum_le _ _).trans ?_
  refine le_trans ?_ (mul_le_mul_of_nonneg_right hc (norm_nonneg _))
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum fun s _ => ?_
  rw [← mul_sub, norm_mul]
  exact mul_le_mul_of_nonneg_left (hfg s) (norm_nonneg _)

section Induced

variable {X : Tower Ω ε} {A : ValuationSubring Ω} {N w : ℕ} {j : Ω →+* Qbar l} {pr : X.Fn l → Fin 2 → Qbar l}
  {lam : (ℕ → Qbar l) →ₗ[Qbar l] Qbar l}

theorem IsLamOfL.smul (h : IsLamOfL X A N w j pr lam) (a : Qbar l) : IsLamOfL X A N w j (a • pr) (a • lam) := by
  obtain ⟨hf, c, per, hper, hc⟩ := h
  obtain ⟨k, hk⟩ := exists_le_l_pow l ‖a‖
  refine ⟨hf.smul a, c + k, per, hper, fun n hn b hb φ hφ => ?_⟩
  have h1 := cg_mul_left (k := k) (m := n - c) (by omega) hk (hc n (by omega) b hb φ hφ)
  rw [Nat.sub_sub] at h1
  simpa [mul_left_comm] using h1

theorem IsLamOfL.congr (h : IsLamOfL X A N w j pr lam) {pr' : X.Fn l → Fin 2 → Qbar l}
    (hp : ∀ b ∈ X.B N l w, pr' b 1 = pr b 1) : IsLamOfL X A N w j pr' lam := by
  obtain ⟨hf, c, per, hper, hc⟩ := h
  exact ⟨hf, c, per, hper, fun n hn b hb φ hφ => by rw [hp b hb]; exact hc n hn b hb φ hφ⟩

end Induced

example (j : Ω →+* Qbar l) : seqN 2 j (HahnSeries.single (((3 : ℕ) : ℚ) / (2 : ℕ)) (1 : Ω)) 3 = 1 := by
  rw [seqN_single two_ne_zero]; simp

example : FinSupp (((l : ℕ) : Qbar l)⁻¹ • LinearMap.proj (R := Qbar l) (φ := fun _ : ℕ => Qbar l) 1 +
    LinearMap.proj (R := Qbar l) (φ := fun _ : ℕ => Qbar l) 5) :=
  ((finSupp_proj 1).smul _).add (finSupp_proj 5)

example (X : Tower Ω ε) (A : ValuationSubring Ω) (N w : ℕ) (j : Ω →+* Qbar l) (pr : X.Fn l → Fin 2 → Qbar l)
    (lam : (ℕ → Qbar l) →ₗ[Qbar l] Qbar l) (h : IsLamOfL X A N w j pr lam) :
    IsLamOfL X A N w j (((l : ℕ) : Qbar l)⁻¹ • pr) (((l : ℕ) : Qbar l)⁻¹ • lam) := h.smul _

end GlobalTheory.KummerEisensteinGalois

end
