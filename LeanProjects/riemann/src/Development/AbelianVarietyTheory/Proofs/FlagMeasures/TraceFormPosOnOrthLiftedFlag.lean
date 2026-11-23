import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.RowMinor
import Formalism.SharpRestriction.CuspSpanNormBounds.CongruenceAtSplitFrobeniusHolds
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CardLeOfDiag
open NumberField Module Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.Cnt GlobalTheory.LoopC
open scoped ENNReal Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LoopC.PerpPos

theorem re_pos {E : Type} [Field E] [NumberField E] [StarRing E] {S : Formalism.BasicNotions.HSpace E} {k r : ℕ}
    (hA : GlobalTheory.SA.Amb S k r) {T : ℕ} (hT : 0 < T) (F : FlagG S r (T : E)) {x : S.V}
    (hx : x ∈ orth S F.Xplus) (hxX : x ∉ F.X) (τ : E →+* ℂ) : 0 < (τ (S.hT x x)).re := by
  have hsym : ∀ a b : S.V, S.hT a b = 0 → S.hT b a = 0 := fun a b h => by
    rw [← S.herm.eq a b, h, map_zero]
  have hx' : ∀ y ∈ F.Xplus, S.hT y x = 0 := fun y hy => by
    simp only [orth, Submodule.mem_iInf, LinearMap.mem_ker] at hx
    exact hx y hy
  have hzP : F.z ∈ F.Xplus := Submodule.mem_sup_right (Submodule.mem_span_singleton_self _)
  have hXP : ∀ y ∈ F.X, y ∈ F.Xplus := fun y hy => Submodule.mem_sup_left hy
  have hspan : ∀ w : S.V, (∀ a, S.hT (F.e a) w = 0) → ∀ y ∈ F.X, S.hT y w = 0 := by
    intro w hw y hy
    induction hy using Submodule.span_induction with
    | mem y hy => obtain ⟨a, rfl⟩ := hy; exact hw a
    | zero => simp
    | add a b _ _ ha hb => rw [map_add, LinearMap.add_apply, ha, hb, add_zero]
    | smul c a _ ha => rw [LinearMap.map_smulₛₗ, LinearMap.smul_apply, ha, smul_zero]
  have hXz : ∀ y ∈ F.X, S.hT y F.z = 0 := hspan _ F.z_orth
  have hXX : ∀ y ∈ F.X, ∀ y' ∈ F.X, S.hT y y' = 0 := fun y hy y' hy' =>
    hspan y' (fun a => hsym _ _ (hspan _ (fun b => F.e_iso b a) y' hy')) y hy
  have hTne : (T : E) ≠ 0 := Nat.cast_ne_zero.2 hT.ne'
  have hzX : F.z ∉ F.X := fun h => by
    have := hXz _ h
    rw [F.z_norm, neg_eq_zero] at this
    exact hTne this
  have hxP : x ∉ F.Xplus := fun h => by
    obtain ⟨ξ, hξ, w, hw, hsum⟩ := Submodule.mem_sup.1 h
    obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.1 hw
    have h1 := hx' _ hzP
    rw [← hsum, map_add, map_smul, hsym _ _ (hXz _ hξ), F.z_norm, zero_add, smul_eq_mul, mul_eq_zero,
      neg_eq_zero] at h1
    rcases h1 with h1 | h1
    · apply hxX
      rw [← hsum, h1, zero_smul, add_zero]
      exact hξ
    · exact hTne h1
  have hdX : finrank E F.X = r := by
    have := finrank_span_eq_card F.e_indep
    rwa [Fintype.card_fin] at this
  have hdP : finrank E F.Xplus = r + 1 := by
    have := Submodule.finrank_sup_span_singleton hzX
    rwa [hdX] at this
  have hdU : finrank E (F.Xplus ⊔ Submodule.span E {x} : Submodule E S.V) = r + 2 := by
    have := Submodule.finrank_sup_span_singleton hxP
    rwa [hdP] at this
  by_contra hle
  rw [not_lt] at hle
  have := hA.neg τ (F.Xplus ⊔ Submodule.span E {x}) (by
    intro y hy
    obtain ⟨p, hp, w, hw, rfl⟩ := Submodule.mem_sup.1 hy
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hw
    obtain ⟨ξ, hξ, w, hw, rfl⟩ := Submodule.mem_sup.1 hp
    obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.1 hw
    have e : S.hT (ξ + a • F.z + c • x) (ξ + a • F.z + c • x) =
        (star a * a) * (-(T : E)) + (star c * c) * S.hT x x := by
      simp only [map_add, LinearMap.add_apply, LinearMap.map_smulₛₗ, LinearMap.smul_apply, map_smul,
        smul_eq_mul, hXX _ hξ _ hξ, hXz _ hξ, hsym _ _ (hXz _ hξ), hx' _ (hXP _ hξ),
        hsym _ _ (hx' _ (hXP _ hξ)), hx' _ hzP, hsym _ _ (hx' _ hzP), F.z_norm,
        starRingEnd_apply]
      ring
    have n : ∀ b : E, τ (star b * b) = (Complex.normSq (τ b) : ℂ) := fun b => by
      rw [map_mul, hA.cm, Complex.normSq_eq_conj_mul_self]
    rw [e, map_add, map_mul τ (star a * a), map_mul τ (star c * c), n, n, Complex.add_re,
      Complex.re_ofReal_mul, Complex.re_ofReal_mul, map_neg, map_natCast, Complex.neg_re, Complex.natCast_re]
    have h1 := Complex.normSq_nonneg (τ a)
    have h2 := Complex.normSq_nonneg (τ c)
    have h3 : (0 : ℝ) ≤ T := Nat.cast_nonneg _
    nlinarith [mul_nonneg h1 h3, mul_nonneg h2 (neg_nonneg.2 hle)])
  omega

theorem trace_pos {K : Type} [Field K] [NumberField K] (y : K) (hp : ∀ τ : K →+* ℂ, 0 < (τ y).re) :
    0 < Algebra.trace ℚ K y := by
  have e := trace_eq_sum_embeddings ℂ (K := ℚ) (L := K) (x := y)
  have e2 : ((Algebra.trace ℚ K y : ℚ) : ℝ) = ∑ σ : K →ₐ[ℚ] ℂ, (σ y).re := by
    rw [← Complex.re_sum, ← e]
    simp
  have hne : Nonempty (K →ₐ[ℚ] ℂ) := ⟨IsAlgClosed.lift⟩
  have : (0 : ℝ) < ((Algebra.trace ℚ K y : ℚ) : ℝ) := by
    rw [e2]
    exact Finset.sum_pos (fun σ _ => hp (σ : K →+* ℂ)) Finset.univ_nonempty
  exact_mod_cast this

theorem trace_pos_perp : ∀ (D : D7) (T' : ℕ) (F' : Fg D ((T' : ℕ) : D.host.E)), 0 < T' →
    ∀ x ∈ orth (hS D) (Xplus F'), x ∉ Xsp F' → 0 < Algebra.trace ℚ D.host.E ((hS D).hT x x) := by
  intro D T' F' hT x hx hxX
  have hA : GlobalTheory.SA.Amb (hS D) D.R.k D.R.rS :=
    GlobalTheory.SA.AmbSig.amb_of_sig _ _ _ _ D.sp.cm.cmUnram.2.1 (D.sp.Y_sig 0) D.sp.baseSpace_signature_eq
  exact trace_pos _ (re_pos hA hT F'.fl hx hxX)

end GlobalTheory.LoopC.PerpPos
