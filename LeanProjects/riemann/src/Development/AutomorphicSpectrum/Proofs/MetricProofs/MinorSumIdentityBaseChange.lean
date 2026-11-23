import Mathlib
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.Pull1
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.IsPeriodOn

open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.MinorAny

theorem minorIJ_map {R S : Type} [CommRing R] [CommRing S] {N : ℕ} (f : R →+* S)
    (A : Matrix (Fin N) (Fin N) R) (I J : Finset (Fin N)) :
    minorIJ (A.map f) I J = f (minorIJ A I J) := by
  unfold minorIJ
  split_ifs with e
  · rw [RingHom.map_det]
    rfl
  · exact (map_zero f).symm

def gap {N : ℕ} {Ω : Type} [Field Ω] (T : Matrix (Fin N) (Fin N) Ω) (c₀ c₁ : Ω)
    (coef u : Finset (Fin N) → Ω) (J : Finset (Fin N)) (S : Type) [CommRing S] [Algebra Ω S]
    (h : Matrix (Fin N) (Fin N) S) : S :=
  algebraMap Ω S c₀ * ∑ I, algebraMap Ω S (coef I) * minorIJ (T.map (algebraMap Ω S) * h) I J -
    algebraMap Ω S c₁ * ∑ I, algebraMap Ω S (u I) * minorIJ h I J

theorem gap_map {N : ℕ} {Ω : Type} [Field Ω] (T : Matrix (Fin N) (Fin N) Ω) (c₀ c₁ : Ω)
    (coef u : Finset (Fin N) → Ω) (J : Finset (Fin N)) {S S' : Type} [CommRing S] [Algebra Ω S]
    [CommRing S'] [Algebra Ω S'] (f : S →ₐ[Ω] S') (h : Matrix (Fin N) (Fin N) S) :
    f (gap T c₀ c₁ coef u J S h) = gap T c₀ c₁ coef u J S' (h.map f.toRingHom) := by
  have hm : ∀ (M : Matrix (Fin N) (Fin N) S) (I J : Finset (Fin N)),
      f (minorIJ M I J) = minorIJ (M.map f.toRingHom) I J :=
    fun M I J => (minorIJ_map f.toRingHom M I J).symm
  have hT : (T.map (algebraMap Ω S) * h).map f.toRingHom = T.map (algebraMap Ω S') * h.map f.toRingHom := by
    rw [Matrix.map_mul, Matrix.map_map]
    congr 1
    congr 1
    funext x
    exact f.commutes x
  simp only [gap, map_sub, map_mul, map_sum, AlgHom.commutes, hm, hT]

theorem minor_any : ∀ (Ω : Type) [Field Ω] [Infinite Ω] (N j : ℕ) (T : Matrix (Fin N) (Fin N) Ω) (c₀ c₁ : Ω) (coef u : Finset (Fin N) → Ω) (J : Finset (Fin N)), (∀ h : Matrix (Fin N) (Fin N) Ω, IsBlockDiag j h → c₀ * ∑ I, coef I * minorIJ (T * h) I J = c₁ * ∑ I, u I * minorIJ h I J) → ∀ (S : Type) [CommRing S] [Algebra Ω S] (h : Matrix (Fin N) (Fin N) S), IsBlockDiag j h → algebraMap Ω S c₀ * ∑ I, algebraMap Ω S (coef I) * minorIJ (T.map (algebraMap Ω S) * h) I J = algebraMap Ω S c₁ * ∑ I, algebraMap Ω S (u I) * minorIJ h I J := by
  intro Ω _ _ N j T c₀ c₁ coef u J hyp S _ _ h hh
  have hT : T.map (algebraMap Ω Ω) = T := Matrix.ext fun _ _ => rfl
  have key : ∀ M : Matrix (Fin N) (Fin N) Ω, IsBlockDiag j M → gap T c₀ c₁ coef u J Ω M = 0 := by
    intro M hM
    simp only [gap, hT]
    exact sub_eq_zero.mpr (hyp M hM)
  let G : Matrix (Fin N) (Fin N) (MvPolynomial (Fin N × Fin N) Ω) :=
    Matrix.of fun a b => if ((a : ℕ) < N - j ↔ (b : ℕ) < N - j) then X (a, b) else 0
  have hP : gap T c₀ c₁ coef u J (MvPolynomial (Fin N × Fin N) Ω) G = 0 := by
    apply MvPolynomial.funext
    intro x
    show aeval x (gap T c₀ c₁ coef u J (MvPolynomial (Fin N × Fin N) Ω) G) = aeval x 0
    rw [map_zero, gap_map]
    apply key
    intro a b hab
    simp only [G, Matrix.map_apply, Matrix.of_apply, if_neg hab, map_zero]
  have hG : G.map (aeval (fun p : Fin N × Fin N => h p.1 p.2)).toRingHom = h := by
    ext a b
    simp only [G, Matrix.map_apply, Matrix.of_apply]
    split_ifs with hab
    · simp [aeval_X]
    · rw [map_zero]
      exact (hh a b hab).symm
  have hz := congrArg (aeval (fun p : Fin N × Fin N => h p.1 p.2)) hP
  rw [gap_map, hG, map_zero] at hz
  simp only [gap] at hz
  exact sub_eq_zero.mp hz

end GlobalTheory.CompanionTheory.Ar.PB.MinorAny
