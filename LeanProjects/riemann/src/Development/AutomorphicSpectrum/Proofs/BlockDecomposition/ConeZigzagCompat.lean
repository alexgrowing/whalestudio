import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.ConeSectionRestriction.CechDefs
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.TotPairing
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DvMemOf

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory CrystallineSemistableComparison CrystallineSemistableComparison.Pb

namespace GlobalTheory.CompanionTheory.ConeZig

universe w

variable {R : Type} [CommRing R]

def shift {K : DCx.{w} R} (B : ∀ p q, K.X p q →ₗ[R] K.X (p + 1) (q + 1)) (x : ∀ p q, K.X p q) : ∀ p q, K.X p q
  | 0, _ => 0
  | _ + 1, 0 => 0
  | p + 1, q + 1 => (-1 : ℤ) ^ q • B p q (x p q)

variable {K : DCx.{w} R} (B : ∀ p q, K.X p q →ₗ[R] K.X (p + 1) (q + 1))

theorem shift_sub (x y : ∀ p q, K.X p q) : shift B (x - y) = shift B x - shift B y := by
  funext p q
  rcases p with _ | p <;> rcases q with _ | q <;> simp [shift, smul_sub]

theorem shift_zero : shift B (0 : ∀ p q, K.X p q) = 0 := by
  funext p q
  rcases p with _ | p <;> rcases q with _ | q <;> simp [shift]

theorem shift_add (x y : ∀ p q, K.X p q) : shift B (x + y) = shift B x + shift B y := by
  funext p q
  rcases p with _ | p <;> rcases q with _ | q <;> simp [shift, smul_add]

theorem shift_sgl (p q : ℕ) (x : K.X p q) :
    shift B (K.sgl p q x) = (-1 : ℤ) ^ q • K.sgl (p + 1) (q + 1) (B p q x) := by
  funext a b
  rcases a with _ | a
  · rw [Pi.smul_apply, Pi.smul_apply, K.sgl_ne _ (Or.inl (by omega))]
    simp [shift]
  · rcases b with _ | b
    · rw [Pi.smul_apply, Pi.smul_apply, K.sgl_ne _ (Or.inr (by omega))]
      simp [shift]
    · by_cases h : a = p ∧ b = q
      · obtain ⟨rfl, rfl⟩ := h
        simp only [shift, Pi.smul_apply, K.sgl_self]
      · rw [Pi.smul_apply, Pi.smul_apply, K.sgl_ne _ (by omega)]
        simp only [shift]
        rw [K.sgl_ne _ (by omega)]
        simp

theorem shift_mem (m : ℕ) (x : ∀ p q, K.X p q) (hx : x ∈ K.T m) : shift B x ∈ K.T (m + 2) := by
  intro p q h
  rcases p with _ | p
  · rfl
  · rcases q with _ | q
    · rfl
    · simp only [shift]
      rw [hx p q (by omega)]
      simp

theorem D_shift (hh : ∀ p q x, K.dh (p + 1) (q + 1) (B p q x) = B (p + 1) q (K.dh p q x))
    (hv : ∀ p q x, K.dv (p + 1) (q + 1) (B p q x) = B p (q + 1) (K.dv p q x)) (x : ∀ p q, K.X p q) :
    K.D (shift B x) = shift B (K.D x) := by
  funext p q
  rw [K.D_apply]
  rcases p with _ | p
  · rcases q with _ | q <;> simp [DCx.Dh, DCx.Dv, shift]
  · rcases q with _ | q
    · rcases p with _ | p <;> simp [DCx.Dh, DCx.Dv, shift]
    · have h1 : K.Dh (shift B x) (p + 1) (q + 1) = (-1 : ℤ) ^ q • B p q (K.Dh x p q) := by
        rcases p with _ | p
        · simp [DCx.Dh, shift]
        · simp [DCx.Dh, shift, hh]
      have h2 : K.Dv (shift B x) (p + 1) (q + 1) = (-1 : ℤ) ^ (q + 1) • B p q (K.Dv x p q) := by
        rcases q with _ | q
        · simp [DCx.Dv, shift]
        · simp only [DCx.Dv, shift, map_zsmul, hv]
          rw [pow_succ, pow_succ]
          simp
      rw [h1, h2]
      show _ = (-1 : ℤ) ^ q • B p q (K.D x p q)
      rw [K.D_apply, map_add, map_zsmul, smul_add, smul_smul, smul_smul, pow_succ, pow_succ]
      congr 2
      ring

theorem cone_zigzag_compat (hh : ∀ p q x, K.dh (p + 1) (q + 1) (B p q x) = B (p + 1) q (K.dh p q x))
    (hv : ∀ p q x, K.dv (p + 1) (q + 1) (B p q x) = B p (q + 1) (K.dv p q x))
    (a : ∀ k, K.X 0 (2 * k)) (g : ∀ k, K.X 0 (2 * k + 1)) (P : ∀ k, K.X k k)
    (hg1 : ∀ k, K.dv 0 (2 * k + 1) (g k) = a (k + 1))
    (hg2 : ∀ k, K.dh 0 (2 * k + 1) (g k) = - B 0 (2 * k) (a k))
    (hP0 : P 0 = a 0) (hPs : ∀ k, P (k + 1) = (-1 : ℤ) ^ k • B k k (P k)) (k : ℕ) :
    ∃ U : ∀ p q, K.X p q, (∀ p q, p + q + 1 ≠ 2 * k → U p q = 0) ∧
      K.D U = K.sgl 0 (2 * k) (a k) - K.sgl k k (P k) := by
  induction k with
  | zero =>
    refine ⟨0, fun _ _ _ => rfl, ?_⟩
    rw [map_zero, hP0]
    exact (sub_self _).symm
  | succ k ih =>
    obtain ⟨U, hU, hDU⟩ := ih
    refine ⟨shift B U + K.sgl 0 (2 * k + 1) (g k), fun p q h => ?_, ?_⟩
    · rw [Pi.add_apply, Pi.add_apply, K.sgl_ne _ (by omega), add_zero]
      rcases p with _ | p
      · rfl
      · rcases q with _ | q
        · rfl
        · simp only [shift]
          rw [hU p q (by omega)]
          simp
    · rw [map_add, D_shift B hh hv, hDU, shift_sub, shift_sgl, shift_sgl, K.D_sgl, hg1, hg2, hPs, map_neg, map_zsmul]
      have e : ((-1 : ℤ) ^ (2 * k)) = 1 := by rw [pow_mul]; simp
      rw [e, one_smul, pow_zero, one_smul]
      have e2 : K.sgl 0 (2 * k + 1 + 1) (a (k + 1)) = K.sgl 0 (2 * (k + 1)) (a (k + 1)) := rfl
      rw [e2]
      abel

theorem zig_stair (F : GlobalTheory.CompanionTheory.ConeCech.DFil K) (n : ℕ) (hTop : ∀ p q, F.L 0 p q = ⊤)
    (hV : ∀ p q, n + 1 < p → Subsingleton (K.X p q)) (hE : ∀ (r : ℕ) p q, q ≠ r → F.Ex (r : ℤ) p q)
    (hh : ∀ p q x, K.dh (p + 1) (q + 1) (B p q x) = B (p + 1) q (K.dh p q x))
    (hv : ∀ p q x, K.dv (p + 1) (q + 1) (B p q x) = B p (q + 1) (K.dv p q x))
    (a : ∀ k, K.X 0 (2 * k)) (g : ∀ k, K.X 0 (2 * k + 1)) (P : ∀ k, K.X k k)
    (hg1 : ∀ k, K.dv 0 (2 * k + 1) (g k) = a (k + 1))
    (hg2 : ∀ k, K.dh 0 (2 * k + 1) (g k) = - B 0 (2 * k) (a k))
    (hP0 : P 0 = a 0) (hPs : ∀ k, P (k + 1) = (-1 : ℤ) ^ k • B k k (P k))
    (hP : P (n + 1) ∈ F.L ((n : ℤ) + 1) (n + 1) (n + 1))
    (v : K.X 0 (2 * n + 1)) (hv1 : K.dv 0 (2 * n + 1) v = a (n + 1)) (hv2 : K.dh 0 (2 * n + 1) v = 0) :
    ∃ (ω : K.X n (n + 1)) (f : K.X (n + 1) n), ω ∈ F.L ((n : ℤ) + 1) n (n + 1) ∧
      K.dv n (n + 1) ω ∈ F.L ((n : ℤ) + 1 + 1) n (n + 2) ∧ f ∈ F.L (n : ℤ) (n + 1) n ∧
      P (n + 1) = K.dh n (n + 1) ω + (-1 : ℤ) ^ (n + 1) • K.dv (n + 1) n f := by
  obtain ⟨U, hU, hDU⟩ := cone_zigzag_compat B hh hv a g P hg1 hg2 hP0 hPs (n + 1)
  refine GlobalTheory.CompanionTheory.ConeCech.stair F n hTop hV hE (P (n + 1)) hP (K.sgl 0 (2 * n + 1) v - U) ?_ ?_
  · refine sub_mem (fun p q h => K.sgl_ne _ (by omega)) (fun p q h => hU p q (by omega))
  · rw [map_sub, hDU, K.D_sgl, hv1, hv2, map_zero, zero_add, pow_zero, one_smul]
    have e2 : K.sgl 0 (2 * n + 1 + 1) (a (n + 1)) = K.sgl 0 (2 * (n + 1)) (a (n + 1)) := rfl
    rw [e2]
    abel

end GlobalTheory.CompanionTheory.ConeZig
