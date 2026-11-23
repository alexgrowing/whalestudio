import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PermMMulTranspose
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TangentHaarRealSUOfMap
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RiemannianHaarIndependentOfOrthonormalFrame
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrincipalCongruenceConjMemArithmeticGroup
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UpqLocallyCompactGroup
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LocallyCompactSecondCountableBorelCountable
import Formalism.FrobeniusOrbits.FrobeniusOrbitsProofs.MuCardLeTwo
open NumberField IsDedekindDomain MeasureTheory Matrix GlobalTheory.AdLat GlobalTheory.UCls GlobalTheory.SUVol ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.CovTop.VolUp
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.StandardLattice Formalism.IndefR.Lev Formalism.IndefR.Datum GlobalTheory.AdelicScalar
open scoped ENNReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SUVol.Degenerate

theorem realSU_subsingleton {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
    (Ψ : Finset (E →+* ℂ)) (G : Matrix (Fin r) (Fin r) E) (h : Ψ.card = 0 ∨ r = 1) :
    Subsingleton (realSU Ψ G) := by
  refine ⟨fun g g' => ?_⟩
  have key : ∀ g : realSU Ψ G, g = 1 := by
    intro g
    apply Subtype.ext
    funext τ
    rcases h with h | h
    · exact absurd (Finset.card_pos.2 ⟨τ.1, τ.2⟩) (by omega)
    · subst h
      apply Units.ext
      have hd := (g.2 τ).1
      rw [Matrix.det_unique] at hd
      ext a b
      rw [Subsingleton.elim a default, Subsingleton.elim b default]
      simpa using hd
  rw [key g, key g']

theorem realLie_eq_zero {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
    (Ψ : Finset (E →+* ℂ)) (G : Matrix (Fin r) (Fin r) E) (h : Ψ.card = 0 ∨ r = 1)
    (X : Ψ → Fin r → Fin r → ℂ) (hX : X ∈ realLie Ψ G) : X = 0 := by
  funext τ
  rcases h with h | h
  · exact absurd (Finset.card_pos.2 ⟨τ.1, τ.2⟩) (by omega)
  · subst h
    have ht := (hX τ).1
    rw [Matrix.trace_fin_one] at ht
    funext a b
    rw [Subsingleton.elim a 0, Subsingleton.elim b 0]
    simpa using ht

theorem fromFrame_eq_zero {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
    {Ψ : Finset (E →+* ℂ)} (x : Frame Ψ r) (hdet : ∀ τ, (mat x τ).det ≠ 0)
    (Y : EuclideanSpace ℂ (Ψ × Fin r × Fin r)) (hY : fromFrame x Y = 0) : Y = 0 := by
  ext ⟨τ, a, b⟩
  have h1 := congrFun hY τ
  have hu : IsUnit (mat x τ).det := isUnit_iff_ne_zero.2 (hdet τ)
  have h2 : Matrix.of (fun a b => Y (τ, a, b)) = 0 := by
    have e : (mat x τ)⁻¹ * (mat x τ * Matrix.of (fun a b => Y (τ, a, b)) * (mat x τ)⁻¹) * mat x τ =
        Matrix.of (fun a b => Y (τ, a, b)) := by
      rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hu, Matrix.one_mul,
        Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hu, Matrix.mul_one]
    rw [← e]
    have h1' : (mat x τ * Matrix.of (fun a b => Y (τ, a, b)) * (mat x τ)⁻¹ : Matrix (Fin r) (Fin r) ℂ) = 0 := h1
    rw [h1', Matrix.mul_zero, Matrix.zero_mul]
  have := congrFun (congrFun h2 a) b
  simpa using this

end GlobalTheory.SUVol.Degenerate

open GlobalTheory.SUVol.Degenerate in

theorem GlobalTheory.SUVol.Degenerate.riemHaar_le_one : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (Ψ : Finset (E →+* ℂ)) (G : Matrix (Fin r) (Fin r) E) (x : Frame Ψ r), 1 ≤ r → (∀ τ, (mat x τ).det ≠ 0) → Ψ.card * (r ^ 2 - 1) = 0 → ∀ S : Set (realSU Ψ G), riemHaar Ψ G x S ≤ 1 := by
  intro E _ _ _ r Ψ G x hr hdet hc S
  have h : Ψ.card = 0 ∨ r = 1 := by
    rcases Nat.mul_eq_zero.1 hc with h | h
    · exact Or.inl h
    · right
      have : r ^ 2 ≤ 1 := by omega
      nlinarith
  haveI := realSU_subsingleton Ψ G h
  haveI : CompactSpace (realSU Ψ G) := Finite.compactSpace
  set K := (realLie Ψ G).comap (fromFrame x) with hK
  haveI hKs : Subsingleton K := by
    refine ⟨fun Y Y' => ?_⟩
    have hz : ∀ Y : K, Y = 0 := fun Y => by
      apply Subtype.ext
      exact fromFrame_eq_zero x hdet Y.1 (realLie_eq_zero Ψ G h _ Y.2)
    rw [hz Y, hz Y']

  have hν : ∀ s, riemLie Ψ G x s ≤ 1 := by
    intro s
    set b := (stdOrthonormalBasis ℝ K).toBasis
    have hb : b.addHaar Set.univ = 1 := by
      rw [Module.Basis.addHaar, ← Set.Nonempty.eq_univ (b.parallelepiped).nonempty]
      exact Measure.addHaarMeasure_self
    calc riemLie Ψ G x s ≤ riemLie Ψ G x Set.univ := measure_mono (Set.subset_univ _)
      _ ≤ 1 := by
        unfold riemLie
        by_cases hm : AEMeasurable (fun Y : K => fromFrame x Y.1) b.addHaar
        · rw [Measure.map_apply_of_aemeasurable hm MeasurableSet.univ, Set.preimage_univ, hb]
        · rw [Measure.map_of_not_aemeasurable hm]; simp
  set μ := (Measure.haar : Measure (realSU Ψ G))
  have hu0 : μ Set.univ ≠ 0 := (isOpen_univ.measure_ne_zero μ Set.univ_nonempty)
  have hut : μ Set.univ ≠ ⊤ := (isCompact_univ.measure_lt_top).ne
  have hball : ∀ ε : ℝ, 0 < ε → grpBall (realSU Ψ G) ε = Set.univ := by
    intro ε hε
    ext g
    simp only [Set.mem_univ, iff_true]
    rw [Subsingleton.elim g 1]
    intro τ a b
    simpa using hε
  have hlim : Filter.limsup (fun ε : ℝ => riemLie Ψ G x (tanBall Ψ r ε) / μ (grpBall (realSU Ψ G) ε))
      (nhdsWithin 0 (Set.Ioi 0)) ≤ 1 / μ Set.univ := by
    refine Filter.limsup_le_of_le (h := ?_)
    filter_upwards [self_mem_nhdsWithin] with ε hε
    rw [hball ε hε]
    exact ENNReal.div_le_div_right (hν _) _
  show riemHaar Ψ G x S ≤ 1
  unfold riemHaar tangentHaar
  rw [Measure.smul_apply, smul_eq_mul]
  calc _ ≤ (1 / μ Set.univ) * μ Set.univ :=
        mul_le_mul' hlim (measure_mono (Set.subset_univ S))
    _ = 1 := ENNReal.div_mul_cancel hu0 hut
