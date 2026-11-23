import Mathlib
import Development.WeilBound.CoreStatements.AbelianHeightsDuality.ZarhinTrick.QiCoreDefs
import Development.WeilBound.CoreStatements.AbelianHeightsDuality.ZarhinTrick.CompLmulMapId

set_option autoImplicit false

noncomputable section

open TensorProduct

namespace PositivityTheory.PrwZar.Qi

variable {K H : Type} [Field K] [CommRing H] [Algebra K H]

theorem pw_charP (p : ℕ) [Fact p.Prime] [CharP K p] (Δ : H →ₐ[K] H ⊗[K] H) (ε : H →ₐ[K] K)
    (hL : CounitL Δ ε) (hR : CounitR Δ ε) (hmul : ∀ a b : ℕ, pw Δ ε (a * b) = (pw Δ ε a).comp (pw Δ ε b))
    (r : ℕ) {x : H} (hx : x ∈ RingHom.ker ε) : pw Δ ε (p ^ r) x ∈ RingHom.ker ε ^ (2 ^ r) := by
  induction r generalizing x with
  | zero =>
    rw [pow_zero, pow_zero, pow_one, RingHom.mem_ker]
    have h := AlgHom.congr_fun (counit_pw Δ ε hL hR 1) x
    rw [AlgHom.comp_apply] at h
    rw [h]
    exact RingHom.mem_ker.1 hx
  | succ r ih =>
    have hp : (p : H) = 0 := by
      rw [← map_natCast (algebraMap K H), CharP.cast_eq_zero K p, map_zero]
    have h2 : pw Δ ε p x ∈ RingHom.ker ε ^ 2 := by
      have := pw_sub_mem Δ ε hL hR p hx
      rwa [hp, zero_mul, sub_zero] at this
    have hcomp : pw Δ ε (p ^ (r + 1)) = (pw Δ ε (p ^ r)).comp (pw Δ ε p) := by
      rw [pow_succ]
      exact hmul _ _
    rw [hcomp, AlgHom.comp_apply]
    have hmap : Ideal.map (pw Δ ε (p ^ r)) (RingHom.ker ε) ≤ RingHom.ker ε ^ (2 ^ r) :=
      Ideal.map_le_iff_le_comap.2 fun z hz => ih hz
    have hy : pw Δ ε (p ^ r) (pw Δ ε p x) ∈ Ideal.map (pw Δ ε (p ^ r)) (RingHom.ker ε ^ 2) :=
      Ideal.mem_map_of_mem _ h2
    rw [Ideal.map_pow] at hy
    have h3 := Ideal.pow_right_mono hmap 2 hy
    rwa [← pow_mul, ← pow_succ] at h3

end PositivityTheory.PrwZar.Qi
