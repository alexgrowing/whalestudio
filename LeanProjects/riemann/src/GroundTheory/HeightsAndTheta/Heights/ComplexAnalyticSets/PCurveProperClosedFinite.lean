import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StCurveProperClosedFinite
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial ComplexSets Filter Topology

theorem CurveProperClosedFinite.no_chain_two {R : Type*} [CommRing R] {W P Q : Ideal R}
    (hW : W.IsPrime) (hP : P.IsPrime) (hQ : Q.IsPrime) (hdim : ringKrullDim (R ⧸ W) = 1)
    (hWP : W < P) (hPQ : P < Q) : False := by
  let a : PrimeSpectrum.zeroLocus (R := R) (W : Set R) :=
    ⟨⟨W, hW⟩, (PrimeSpectrum.mem_zeroLocus _ _).2 le_rfl⟩
  let b : PrimeSpectrum.zeroLocus (R := R) (W : Set R) :=
    ⟨⟨P, hP⟩, (PrimeSpectrum.mem_zeroLocus _ _).2 hWP.le⟩
  let c : PrimeSpectrum.zeroLocus (R := R) (W : Set R) :=
    ⟨⟨Q, hQ⟩, (PrimeSpectrum.mem_zeroLocus _ _).2 (hWP.trans hPQ).le⟩
  have hab : a < b := hWP
  have hbc : b < c := hPQ
  let p0 : LTSeries (PrimeSpectrum.zeroLocus (R := R) (W : Set R)) := RelSeries.singleton _ a
  have h2 := Order.LTSeries.length_le_krullDim ((p0.snoc b hab).snoc c hbc)
  rw [← ringKrullDim_quotient, hdim] at h2
  have hl : ((p0.snoc b hab).snoc c hbc).length = 2 := by
    rfl
  rw [hl] at h2
  norm_num at h2

theorem CurveProperClosedFinite.proof : CurveProperClosedFinite.Statement := by
  intro n W K hW hdim hK
  let m : (Fin n → ℂ) → Ideal (MvPolynomial (Fin n) ℂ) := fun x => RingHom.ker (eval x)
  have hinj : Function.Injective m := by
    intro x y hxy
    funext i
    have hx : X i - C (x i) ∈ m x := by simp [m, RingHom.mem_ker]
    have hy : X i - C (x i) ∈ m y := hxy ▸ hx
    have hy' : y i - x i = 0 := by simpa [m, RingHom.mem_ker] using hy
    exact (sub_eq_zero.1 hy').symm
  have hsub : m '' (zeroSet W ∩ zeroSet K) ⊆ (W ⊔ K).minimalPrimes := by
    rintro _ ⟨x, ⟨hxW, hxK⟩, rfl⟩
    have hmax : (m x).IsMaximal :=
      RingHom.ker_isMaximal_of_surjective (eval x) (fun c => ⟨C c, by simp⟩)
    have hle : W ⊔ K ≤ m x := sup_le (fun q hq => hxW q hq) (fun q hq => hxK q hq)
    refine ⟨⟨hmax.isPrime, hle⟩, fun Q ⟨hQ, hJQ⟩ hQm => ?_⟩
    by_contra hmQ
    have hWQ : W < Q := by
      refine lt_of_le_of_ne (le_sup_left.trans hJQ) ?_
      rintro rfl
      exact hK (le_sup_right.trans hJQ)
    exact CurveProperClosedFinite.no_chain_two hW hQ hmax.isPrime hdim hWQ (lt_of_le_of_ne hQm
      (fun h => hmQ (h ▸ le_rfl)))
  exact Set.Finite.of_finite_image
    ((Ideal.finite_minimalPrimes_of_isNoetherianRing _ _).subset hsub) hinj.injOn

end GroundTheory.Heights₂.Heights
