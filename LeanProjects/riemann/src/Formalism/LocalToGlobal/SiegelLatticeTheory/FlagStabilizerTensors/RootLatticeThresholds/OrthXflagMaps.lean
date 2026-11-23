import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.SubMemOfIndQ

noncomputable section

open scoped Classical
open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat

namespace Formalism.L2.SG.Pf.FibreCounting

section Nilp

variable {E : Type} [Field E] [NumberField E] [StarRing E] {S : HSpace E} {r : ℕ}
  {Λ : Submodule (𝓞 E) S.V} {T : E} {F : LFlag S r T} {n : S.V ≃ₗ[E] S.V}

theorem orth_xflag_maps (hn : n ∈ NLam Λ F) (j : ℕ) : ∀ x ∈ orth S (Xflag F j), n x ∈ orth S (Xflag F j) := by
  intro x hx
  rw [Formalism.L2.SG.Pf.mem_orth_iff_td] at hx ⊢
  intro y hy
  have hy' : y ∈ (Xflag F j).map (n : S.V →ₗ[E] S.V) := by
    rw [Formalism.L2.SG.Pf.nlam_map_eq hn j]; exact hy
  obtain ⟨y', hy'X, rfl⟩ := hy'
  have hiso := ((Formalism.L2.SG.Pf.isAutLam_iff Λ n).1 hn.1).1
  simp only [LinearEquiv.coe_coe]
  rw [hiso]
  exact hx y' hy'X

theorem orth_step (hn : n ∈ NLam Λ F) (j : ℕ) : ∀ x ∈ orth S (Xflag F j), n x - x ∈ orth S (Xflag F (j + 1)) := by
  intro x hx
  have hnx := orth_xflag_maps hn j x hx
  rw [Formalism.L2.SG.Pf.mem_orth_iff_td] at hx hnx ⊢
  intro y hy
  have hiso := ((Formalism.L2.SG.Pf.isAutLam_iff Λ n).1 hn.1).1
  have h1 : n y - y ∈ Xflag F j := hn.2.1 j y hy
  have e : S.hT y (n x - x) = - S.hT (n y - y) (n x) := by
    rw [map_sub, map_sub, LinearMap.sub_apply, ← hiso y x]
    ring
  rw [e, hnx _ h1, neg_zero]

def chainC (F : LFlag S r T) (i : ℕ) : Submodule E S.V :=
  if i ≤ r then Xflag F i else orth S (Xflag F (2 * r + 1 - i))

theorem chain_step (hn : n ∈ NLam Λ F) (i : ℕ) : ∀ x ∈ chainC F (i + 1), n x - x ∈ chainC F i := by
  intro x hx
  unfold chainC at hx ⊢
  by_cases h1 : i + 1 ≤ r
  · rw [if_pos h1] at hx
    rw [if_pos (by omega)]
    exact hn.2.1 i x hx
  · rw [if_neg h1] at hx
    by_cases h2 : i = r
    · subst h2
      rw [if_pos le_rfl]
      have e : 2 * i + 1 - (i + 1) = i := by omega
      rw [e, Formalism.L2.SG.Pf.xflag_r] at hx
      rw [Formalism.L2.SG.Pf.xflag_r]
      exact hn.2.2 x hx
    · rw [if_neg (by omega)]
      by_cases h3 : i ≤ 2 * r
      · have e1 : 2 * r + 1 - (i + 1) = 2 * r - i := by omega
        have e2 : 2 * r + 1 - i = (2 * r - i) + 1 := by omega
        rw [e1] at hx
        rw [e2]
        exact orth_step hn _ x hx
      · have e2 : 2 * r + 1 - i = 0 := by omega
        rw [e2, Formalism.L2.SG.Pf.mem_orth_iff_td]
        intro y hy
        rw [Formalism.L2.SG.Pf.xflag_zero_td, Submodule.mem_bot] at hy
        rw [hy, map_zero, LinearMap.zero_apply]

theorem chain_pow (hn : n ∈ NLam Λ F) (j : ℕ) :
    ∀ i, ∀ x ∈ chainC F (i + j), (((n : S.V →ₗ[E] S.V) - 1) ^ j) x ∈ chainC F i := by
  induction j with
  | zero => intro i x hx; simpa using hx
  | succ j ih =>
    intro i x hx
    rw [pow_succ, Module.End.mul_apply]
    apply ih
    have : ((n : S.V →ₗ[E] S.V) - 1) x = n x - x := by simp
    rw [this]
    exact chain_step hn (i + j) x (by rwa [← add_assoc] at hx)

theorem nlam_nilp (hn : n ∈ NLam Λ F) : ((n : S.V →ₗ[E] S.V) - 1) ^ (2 * r + 1) = 0 := by
  ext x
  have hx : x ∈ chainC F (0 + (2 * r + 1)) := by
    unfold chainC
    rw [if_neg (by omega), Formalism.L2.SG.Pf.mem_orth_iff_td]
    intro y hy
    have e : 2 * r + 1 - (0 + (2 * r + 1)) = 0 := by omega
    rw [e, Formalism.L2.SG.Pf.xflag_zero_td, Submodule.mem_bot] at hy
    rw [hy, map_zero, LinearMap.zero_apply]
  have h := chain_pow hn (2 * r + 1) 0 x hx
  unfold chainC at h
  rw [if_pos (Nat.zero_le _), Formalism.L2.SG.Pf.xflag_zero_td, Submodule.mem_bot] at h
  rw [h, LinearMap.zero_apply]

theorem conj_nilp (hn : n ∈ NLam Λ F) (γ : S.V ≃ₗ[E] S.V) :
    (((γ⁻¹ * n * γ : S.V ≃ₗ[E] S.V) : S.V →ₗ[E] S.V) - 1) ^ (2 * r + 1) = 0 := by
  have key : ∀ (N : ℕ) (x : S.V), ((((γ⁻¹ * n * γ : S.V ≃ₗ[E] S.V) : S.V →ₗ[E] S.V) - 1) ^ N :
      Module.End E S.V) x = γ⁻¹ ((((n : S.V →ₗ[E] S.V) - 1) ^ N : Module.End E S.V) (γ x)) := by
    intro N
    induction N with
    | zero => intro x; simp [LinearEquiv.coe_inv]
    | succ N ih =>
      intro x
      rw [pow_succ, Module.End.mul_apply, ih, pow_succ, Module.End.mul_apply]
      congr 2
      simp [LinearEquiv.coe_inv, map_sub]
  ext x
  rw [key, nlam_nilp hn, LinearMap.zero_apply, map_zero, LinearMap.zero_apply]

end Nilp

section Unip

variable {K M : Type*} [Field K] [CharZero K] [AddCommGroup M] [Module K M]

open Polynomial in

theorem unip_fin (A : Module.End K M) {k N : ℕ} (hk : 0 < k) (h1 : A ^ k = 1) (h2 : (A - 1) ^ N = 0) : A = 1 := by
  set B := A - 1 with hB
  have hA : A = B + 1 := by rw [hB]; abel

  have hd : X ∣ ((X + 1 : K[X]) ^ k - 1) := by
    rw [X_dvd_iff, coeff_sub, coeff_X_add_one_pow, coeff_one_zero, Nat.choose_zero_right, Nat.cast_one, sub_self]
  obtain ⟨q, hq⟩ := hd
  have hq0 : q.coeff 0 = (k : K) := by
    have := congrArg (fun p : K[X] => p.coeff 1) hq
    simp only [coeff_sub, coeff_X_add_one_pow, Nat.choose_one_right, coeff_one, coeff_X_mul] at this
    simpa using this.symm
  have hd2 : X ∣ q - C (k : K) := by
    rw [X_dvd_iff, coeff_sub, coeff_C_zero, hq0, sub_self]
  obtain ⟨r0, hr0⟩ := hd2
  have hq' : q = C (k : K) + X * r0 := by rw [← hr0]; ring
  have hev : aeval B ((X + 1 : K[X]) ^ k - 1) = 0 := by
    rw [map_sub, map_pow, map_add, aeval_X, map_one, ← hA, h1, sub_self]
  rw [hq, hq', map_mul, map_add, map_mul, aeval_X, aeval_C] at hev

  have step : ∀ i, B ^ (i + 1 + 1) = 0 → B ^ (i + 1) = 0 := by
    intro i hi
    have e : B ^ i * (B * (algebraMap K (Module.End K M) (k : K) + B * aeval B r0)) = 0 := by
      rw [hev, mul_zero]
    have e3 : B ^ i * (B * (algebraMap K (Module.End K M) (k : K) + B * aeval B r0)) =
        (k : K) • B ^ (i + 1) + B ^ (i + 1 + 1) * aeval B r0 := by
      rw [Algebra.smul_def, mul_add, mul_add, ← mul_assoc, ← pow_succ, ← Algebra.commutes, ← mul_assoc,
        ← mul_assoc, ← pow_succ, ← pow_succ]
    rw [e3, hi, zero_mul, add_zero] at e
    rcases smul_eq_zero.1 e with h | h
    · exact absurd h (Nat.cast_ne_zero.2 hk.ne')
    · exact h
  have down : ∀ j, B ^ (j + 1) = 0 → B ^ 1 = 0 := by
    intro j
    induction j with
    | zero => exact id
    | succ j ih => intro h; exact ih (step j h)
  have hB1 : B = 0 := by
    rcases N with _ | N
    · rw [pow_zero] at h2
      have : (1 : Module.End K M) = 0 := h2
      calc B = 1 * B := (one_mul B).symm
        _ = 0 := by rw [this, zero_mul]
    · simpa using down N h2
  rw [hA, hB1, zero_add]

end Unip

section Ind

variable {D : D7} {T : D.host.E} (F0 : FlagG (VS D) D.R.rS T)

def indL (f : (VS D).V →ₗ[D.host.E] (VS D).V) (hP : ∀ y ∈ perpS (VS D) F0.X, f y ∈ perpS (VS D) F0.X)
    (hX : ∀ y ∈ F0.X, f y ∈ F0.X) : Module.End D.host.E (WbQ D F0) :=
  Submodule.mapQ _ _ (f.restrict hP) (by
    intro y hy
    simp only [Submodule.mem_comap, Submodule.coe_subtype] at hy ⊢
    rw [LinearMap.restrict_coe_apply]
    exact hX _ hy)

theorem indL_mk (f : (VS D).V →ₗ[D.host.E] (VS D).V) (hP : ∀ y ∈ perpS (VS D) F0.X, f y ∈ perpS (VS D) F0.X)
    (hX : ∀ y ∈ F0.X, f y ∈ F0.X) (x : perpS (VS D) F0.X) :
    indL F0 f hP hX (Submodule.Quotient.mk x) = Submodule.Quotient.mk ⟨f x, hP _ x.2⟩ := by
  unfold indL
  rw [Submodule.mapQ_apply]
  rfl

theorem pow_maps {p : Submodule D.host.E (VS D).V} (f : (VS D).V →ₗ[D.host.E] (VS D).V) (h : ∀ y ∈ p, f y ∈ p) (N : ℕ) :
    ∀ y ∈ p, (f ^ N) y ∈ p := by
  induction N with
  | zero => intro y hy; simpa using hy
  | succ N ih => intro y hy; rw [pow_succ, Module.End.mul_apply]; exact ih _ (h y hy)

theorem indL_pow (f : (VS D).V →ₗ[D.host.E] (VS D).V) (hP : ∀ y ∈ perpS (VS D) F0.X, f y ∈ perpS (VS D) F0.X)
    (hX : ∀ y ∈ F0.X, f y ∈ F0.X) (N : ℕ) :
    indL F0 f hP hX ^ N = indL F0 (f ^ N) (pow_maps f hP N) (pow_maps f hX N) := by
  induction N with
  | zero =>
    refine LinearMap.ext fun w => ?_
    induction w using Submodule.Quotient.induction_on with
    | H x => rw [pow_zero, indL_mk]; rfl
  | succ N ih =>
    refine LinearMap.ext fun w => ?_
    induction w using Submodule.Quotient.induction_on with
    | H x =>
      rw [pow_succ, Module.End.mul_apply, indL_mk, ih, indL_mk, indL_mk]
      congr 1

end Ind

end Formalism.L2.SG.Pf.FibreCounting
