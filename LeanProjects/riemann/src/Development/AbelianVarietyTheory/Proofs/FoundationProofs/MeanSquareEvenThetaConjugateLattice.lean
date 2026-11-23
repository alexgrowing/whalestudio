import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Formalism.PairingDivisors.StatementH
import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.OddThetaFunctionExistenceUniqueness
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SigmaStarValueLeMeanSquareGenusOne
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators
open MeasureTheory

noncomputable section

namespace GlobalTheory.MeanSquareConj

theorem mem_conj (Λ : AddSubgroup ℂ) (z : ℂ) :
    z ∈ Λ.map (starRingEnd ℂ).toAddMonoidHom ↔ (starRingEnd ℂ) z ∈ Λ := by
  rw [AddSubgroup.mem_map]
  constructor
  · rintro ⟨y, hy, rfl⟩
    simpa using hy
  · intro h
    exact ⟨_, h, by simp⟩

theorem area_conj (Λ : AddSubgroup ℂ) : area (Λ.map (starRingEnd ℂ).toAddMonoidHom) = area Λ := by
  unfold area
  congr 1
  ext a
  have e : ∀ x y : ℂ, |((starRingEnd ℂ) ((starRingEnd ℂ) x) * (starRingEnd ℂ) y).im| =
      |((starRingEnd ℂ) x * y).im| := by
    intro x y
    rw [← map_mul, Complex.conj_im, abs_neg]
  simp only [Set.mem_setOf_eq, mem_conj]
  constructor
  · rintro ⟨ha, x, hx, y, hy, rfl⟩
    exact ⟨ha, _, hx, _, hy, (e x y).symm⟩
  · rintro ⟨ha, x, hx, y, hy, rfl⟩
    exact ⟨ha, (starRingEnd ℂ) x, by simpa using hx, (starRingEnd ℂ) y, by simpa using hy, (e x y).symm⟩

theorem lattice_conj (Λ : AddSubgroup ℂ)
    (hΛ : ∃ w₁ w₂ : ℂ, LinearIndependent ℝ ![w₁, w₂] ∧ Λ = AddSubgroup.closure {w₁, w₂}) :
    ∃ w₁ w₂ : ℂ, LinearIndependent ℝ ![w₁, w₂] ∧
      Λ.map (starRingEnd ℂ).toAddMonoidHom = AddSubgroup.closure {w₁, w₂} := by
  obtain ⟨w₁, w₂, hli, rfl⟩ := hΛ
  refine ⟨(starRingEnd ℂ) w₁, (starRingEnd ℂ) w₂, ?_, ?_⟩
  · rw [LinearIndependent.pair_iff] at hli ⊢
    intro s t h
    refine hli s t ?_
    have := congrArg (starRingEnd ℂ) h
    simpa using this
  · rw [AddMonoidHom.map_closure, Set.image_pair]
    rfl

theorem thetaTranslate_conjugateLattice (Λ : AddSubgroup ℂ) (G : ℂ → ℂ) (t z : ℂ) :
    U1 (Λ.map (starRingEnd ℂ).toAddMonoidHom) t (fun z => (starRingEnd ℂ) (G ((starRingEnd ℂ) z))) z =
      (starRingEnd ℂ) (U1 Λ ((starRingEnd ℂ) t) G ((starRingEnd ℂ) z)) := by
  unfold U1
  rw [area_conj, map_mul, ← Complex.exp_conj]
  simp only [map_add, map_sub, map_div₀, map_mul, map_neg, Complex.conj_ofReal, Complex.conj_conj, map_ofNat]

theorem sgStar_conj (Λ : AddSubgroup ℂ)
    (hΛ : ∃ w₁ w₂ : ℂ, LinearIndependent ℝ ![w₁, w₂] ∧ Λ = AddSubgroup.closure {w₁, w₂}) :
    sgStar (Λ.map (starRingEnd ℂ).toAddMonoidHom) =
      fun z => (starRingEnd ℂ) (sgStar Λ ((starRingEnd ℂ) z)) := by
  obtain ⟨⟨hd, h1, -, hU⟩, -⟩ := GlobalTheory.OddTheta.sgStar_laws Λ hΛ
  obtain ⟨-, -, huniq, -⟩ := GlobalTheory.OddTheta.sgStar_laws _ (lattice_conj Λ hΛ)
  have hder : ∀ z, HasDerivAt (fun z => (starRingEnd ℂ) (sgStar Λ ((starRingEnd ℂ) z)))
      ((starRingEnd ℂ) (deriv (sgStar Λ) ((starRingEnd ℂ) z))) z := by
    intro z
    have := (hd ((starRingEnd ℂ) z)).hasDerivAt.conj_conj
    rw [Complex.conj_conj] at this
    exact this
  funext z
  have := huniq _ (fun z => (hder z).differentiableAt) (by
    intro ω hω z
    rw [thetaTranslate_conjugateLattice, hU _ ((mem_conj Λ ω).1 hω), map_mul]
    congr 1
    have e : (starRingEnd ℂ) (ω / 2) = (starRingEnd ℂ) ω / 2 := by
      rw [map_div₀, map_ofNat]
    simp only [mem_conj, e]
    split_ifs <;> simp) z
  rw [(hder 0).deriv, map_zero, h1, map_one, one_mul] at this
  exact this.symm

theorem evenTheta_conjugateLattice (Λ : AddSubgroup ℂ)
    (hΛ : ∃ w₁ w₂ : ℂ, LinearIndependent ℝ ![w₁, w₂] ∧ Λ = AddSubgroup.closure {w₁, w₂}) (t z : ℂ) :
    GL3Theta.th0 (Λ.map (starRingEnd ℂ).toAddMonoidHom) ((starRingEnd ℂ) t) z =
      (starRingEnd ℂ) (GL3Theta.th0 Λ t ((starRingEnd ℂ) z)) := by
  unfold GL3Theta.th0
  rw [sgStar_conj Λ hΛ, thetaTranslate_conjugateLattice, thetaTranslate_conjugateLattice, map_div₀, map_zero, Complex.conj_conj]

theorem evenTheta_weightedNormSq_periodic (Λ : AddSubgroup ℂ)
    (hΛ : ∃ w₁ w₂ : ℂ, LinearIndependent ℝ ![w₁, w₂] ∧ Λ = AddSubgroup.closure {w₁, w₂}) (t : ℂ)
    (x : ℂ) (hx : x ∈ Λ) (z : ℂ) :
    ‖GL3Theta.th0 Λ t (x + z)‖ ^ 2 * Real.exp (-Real.pi * ‖x + z‖ ^ 2 / area Λ) =
      ‖GL3Theta.th0 Λ t z‖ ^ 2 * Real.exp (-Real.pi * ‖z‖ ^ 2 / area Λ) := by
  obtain ⟨⟨-, -, -, hU⟩, -⟩ := GlobalTheory.OddTheta.sgStar_laws Λ hΛ
  have hper : ∀ z, ‖sgStar Λ (z + x)‖ ^ 2 * Real.exp (-Real.pi * ‖z + x‖ ^ 2 / area Λ) =
      ‖sgStar Λ z‖ ^ 2 * Real.exp (-Real.pi * ‖z‖ ^ 2 / area Λ) := by
    intro z
    rw [← GlobalTheory.GenusOneSup.thetaTranslation_weighted_normSq, hU x hx, norm_mul]
    split_ifs <;> simp
  unfold GL3Theta.th0
  simp only [norm_div, div_pow, div_mul_eq_mul_div]
  rw [GlobalTheory.GenusOneSup.thetaTranslation_weighted_normSq, GlobalTheory.GenusOneSup.thetaTranslation_weighted_normSq,
    show x + z + t = z + t + x by ring, hper]

theorem nrm1Sq_th0_map_conj_eq : ∀ (Λ : AddSubgroup ℂ), (∃ w₁ w₂ : ℂ, LinearIndependent ℝ ![w₁, w₂] ∧ Λ = AddSubgroup.closure {w₁, w₂}) → ∀ t : ℂ, nrm1Sq (Λ.map (starRingEnd ℂ).toAddMonoidHom) (GL3Theta.th0 (Λ.map (starRingEnd ℂ).toAddMonoidHom) ((starRingEnd ℂ) t)) = nrm1Sq Λ (GL3Theta.th0 Λ t) := by
  intro Λ hΛ t
  have hex : ∀ A : AddSubgroup ℂ,
      (∃ w₁ w₂ : ℂ, LinearIndependent ℝ ![w₁, w₂] ∧ A = AddSubgroup.closure {w₁, w₂}) →
      IsAddFundamentalDomain A
        (Classical.epsilon fun Fd : Set ℂ => IsAddFundamentalDomain A Fd volume) volume := by
    rintro A ⟨w₁, w₂, hli, rfl⟩
    obtain ⟨F, hF, -⟩ := GlobalTheory.GenusOneSup.exists_domain hli
    exact Classical.epsilon_spec (p := fun Fd : Set ℂ => IsAddFundamentalDomain _ Fd volume) ⟨F, hF⟩
  have hF := hex Λ hΛ
  have hF' := hex _ (lattice_conj Λ hΛ)
  have hcount : Countable Λ := by
    obtain ⟨w₁, w₂, -, h⟩ := hΛ
    have : (Λ : Set ℂ) ⊆ Set.range (fun p : ℤ × ℤ => p.1 • w₁ + p.2 • w₂) := by
      intro x hx
      rw [h] at hx
      obtain ⟨m, n, rfl⟩ := AddSubgroup.mem_closure_pair.1 hx
      exact ⟨(m, n), rfl⟩
    exact ((Set.countable_range _).mono this).to_subtype
  have : VAddInvariantMeasure Λ ℂ volume := ⟨fun γ s _ => measure_preimage_add volume (γ : ℂ) s⟩
  unfold nrm1Sq
  simp only
  set F := Classical.epsilon fun Fd : Set ℂ => IsAddFundamentalDomain Λ Fd volume
  set F' := Classical.epsilon fun Fd : Set ℂ =>
    IsAddFundamentalDomain (Λ.map (starRingEnd ℂ).toAddMonoidHom) Fd volume
  have hmp : MeasurePreserving (starRingEnd ℂ) volume volume := Complex.conjLIE.measurePreserving
  have hemb : MeasurableEmbedding (starRingEnd ℂ) := Complex.conjLIE.toHomeomorph.measurableEmbedding
  have hF2 : IsAddFundamentalDomain Λ ((starRingEnd ℂ) ⁻¹' F') volume := by
    refine hF'.preimage_of_equiv (f := starRingEnd ℂ)
      (e := fun y => (⟨(starRingEnd ℂ) y, (mem_conj Λ _).1 y.2⟩ : Λ))
      hmp.quasiMeasurePreserving ⟨?_, ?_⟩ ?_
    · intro x y h
      exact Subtype.ext (star_injective (congrArg Subtype.val h))
    · intro x
      exact ⟨⟨(starRingEnd ℂ) x, (mem_conj Λ _).2 (by simp)⟩, Subtype.ext (by simp)⟩
    · intro y x
      show (starRingEnd ℂ) ((starRingEnd ℂ) y + x) = (y : ℂ) + (starRingEnd ℂ) x
      simp
  rw [setAverage_eq, setAverage_eq, measureReal_def, measureReal_def, hF.measure_eq hF2,
    hF.setIntegral_eq hF2 (fun γ z => evenTheta_weightedNormSq_periodic Λ hΛ t γ γ.2 z), hmp.measure_preimage_emb hemb,
    ← hmp.setIntegral_preimage_emb hemb]
  simp only [evenTheta_conjugateLattice Λ hΛ, area_conj, Complex.conj_conj, Complex.norm_conj]

end GlobalTheory.MeanSquareConj
