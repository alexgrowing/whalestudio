import Mathlib
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.Pull1
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.IsPeriodOn
import Development.AutomorphicSpectrum.Proofs.MetricProofs.IsImg
import Development.AutomorphicSpectrum.Proofs.MetricProofs.AevalNeZeroOfNotMem
import Development.AutomorphicSpectrum.Proofs.MetricProofs.IsValueAtOfTorus
import Development.AutomorphicSpectrum.Proofs.MetricProofs.ExistsBlkCover
import Development.AutomorphicSpectrum.Proofs.MetricProofs.MinorIJMap
import Development.AutomorphicSpectrum.Proofs.MetricProofs.BlockDiagonalMinorVanishingStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagModelBaseProjectionPointsStatement
import GroundTheory.HeightsAndTheta.Heights.Intersections.PtsOverPt
import Development.AutomorphicSpectrum.Proofs.MetricProofs.FrameChangeScalarFactorStatement
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical

noncomputable section
namespace GlobalTheory.CompanionTheory.Ar.PB.CovMap.LocImg.FV

theorem isStepRows_stepCols {N j : ℕ} (i : Fin N) : IsStepRows N j i (stepCols N j i) := by
  refine ⟨rfl, ?_⟩
  intro a ha
  have hi := i.2
  simp only [stepCols, Finset.mem_filter, Finset.mem_univ, true_and] at ha
  split_ifs at ha ⊢ with h
  · simp only [wIdx, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ha.1
  · simp only [omIdx, Finset.mem_filter, Finset.mem_univ, true_and]
    omega

theorem stepCols_ne_empty {N j : ℕ} (i : Fin N) : stepCols N j i ≠ ∅ := by
  intro e
  have hi := i.2
  by_cases h : (i : ℕ) + 1 ≤ j
  · have : (⟨N - j, by omega⟩ : Fin N) ∈ stepCols N j i := by
      simp only [stepCols, Finset.mem_filter, Finset.mem_univ, true_and, if_pos h]
      omega
    simp [e] at this
  · have : (⟨0, by omega⟩ : Fin N) ∈ stepCols N j i := by
      simp only [stepCols, Finset.mem_filter, Finset.mem_univ, true_and, if_neg h]
      omega
    simp [e] at this

theorem minorIJ_one_ne {N : ℕ} {I J : Finset (Fin N)} (h : I ≠ J) :
    minorIJ (1 : Matrix (Fin N) (Fin N) ℂ) I J = 0 := by
  unfold minorIJ
  split_ifs with e
  · obtain ⟨a, ha, hb⟩ : ∃ a ∈ I, a ∉ J := by
      by_contra hc
      push_neg at hc
      exact h (Finset.eq_of_subset_of_card_le hc e.ge)
    obtain ⟨r, hr⟩ : ∃ r, I.orderEmbOfFin e r = a := by
      have h2 : a ∈ Set.range (I.orderEmbOfFin e) := by
        rw [Finset.range_orderEmbOfFin]
        exact ha
      exact h2
    refine Matrix.det_eq_zero_of_row_eq_zero r fun c => ?_
    rw [Matrix.submatrix_apply, hr]
    exact Matrix.one_apply_ne fun q => hb (q ▸ Finset.orderEmbOfFin_mem _ _ _)
  · rfl

theorem minorIJ_one_same {N : ℕ} (I : Finset (Fin N)) :
    minorIJ (1 : Matrix (Fin N) (Fin N) ℂ) I I = 1 := by
  unfold minorIJ
  rw [dif_pos rfl, Matrix.submatrix_one _ (I.orderEmbOfFin rfl).injective, Matrix.det_one]

theorem sum_minor_one {N : ℕ} (a : Finset (Fin N) → ℂ) (C : Finset (Fin N)) :
    ∑ I, a I * minorIJ (1 : Matrix (Fin N) (Fin N) ℂ) I C = a C := by
  rw [Finset.sum_eq_single C (fun I _ h => by rw [minorIJ_one_ne h, mul_zero])
    (fun h => absurd (Finset.mem_univ C) h), minorIJ_one_same, mul_one]

theorem sum_minor_mul {N j : ℕ} (hj : j ≤ N) (i : Fin N) {μ : Type} (a₁ a₂ : μ → Finset (Fin N) → ℂ)
    (S : Matrix (Fin N) (Fin N) ℂ) (c : ℂ)
    (hS : ∀ m I', IsStepRows N j i I' → ∑ I, a₁ m I * minorIJ S I I' = c * a₂ m I')
    (h : Matrix (Fin N) (Fin N) ℂ) (hh : IsBlockDiag j h) (m : μ) :
    ∑ I, a₁ m I * minorIJ (S * h) I (stepCols N j i) = c * ∑ I, a₂ m I * minorIJ h I (stepCols N j i) := by
  obtain ⟨cb, off, -, -⟩ := GlobalTheory.T.block_diagonal_minor_vanishing ℂ N j i hj
  have off' : ∀ I', ¬ IsStepRows N j i I' → minorIJ h I' (stepCols N j i) = 0 := fun I' hI =>
    (off h I' hh hI).resolve_right (stepCols_ne_empty i)
  simp only [cb, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun I' _ => ?_
  by_cases hI : IsStepRows N j i I'
  · rw [← mul_assoc, ← hS m I' hI, Finset.sum_mul]
    exact Finset.sum_congr rfl fun I _ => by ring
  · simp [off' I' hI]

theorem coef_ne_zero {N j : ℕ} (hj : j ≤ N) (i : Fin N) {μ : Type} [Fintype μ] (a₁ a₂ : μ → Finset (Fin N) → ℂ)
    (b : μ → ℂ) (S S' : Matrix (Fin N) (Fin N) ℂ) (c : ℂ)
    (hS : ∀ m I', IsStepRows N j i I' → ∑ I, a₁ m I * minorIJ S I I' = c * a₂ m I')
    (hd : IsBlockDiag j S') (hSS : S * S' = 1) (hb : ∑ m, b m * a₁ m (stepCols N j i) = 1) : c ≠ 0 := by
  intro hc
  have h0 : ∀ m, a₁ m (stepCols N j i) = 0 := fun m => by
    have e1 := sum_minor_mul hj i a₁ a₂ S c hS S' hd m
    rw [hSS, hc, zero_mul, sum_minor_one (a₁ m)] at e1
    exact e1
  simp [h0] at hb

theorem map_inv_eq {Ω Ω₂ : Type} [Field Ω] [Field Ω₂] (φ : Ω →+* Ω₂) {N : ℕ} (T : Matrix (Fin N) (Fin N) Ω)
    (hd : T.det ≠ 0) : T⁻¹.map φ = (T.map φ)⁻¹ := by
  symm
  apply Matrix.inv_eq_right_inv
  rw [← Matrix.map_mul, Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.2 hd)]
  exact Matrix.map_one _ (map_zero φ) (map_one φ)

theorem map_rel {Ω Ω₂ : Type} [Field Ω] [Field Ω₂] (φ : Ω →+* Ω₂) {N : ℕ} {μ : Type}
    (u₁ u₂ : μ → Finset (Fin N) → Ω) (T₁ T₂ : Matrix (Fin N) (Fin N) Ω) (h₁ : T₁.det ≠ 0) (ρ : Ω)
    (P : Finset (Fin N) → Prop)
    (h : ∀ m I', P I' → ∑ I, u₁ m I * minorIJ (T₁⁻¹ * T₂) I I' = ρ * u₂ m I') :
    ∀ m I', P I' → ∑ I, φ (u₁ m I) * minorIJ ((T₁.map φ)⁻¹ * T₂.map φ) I I' = φ ρ * φ (u₂ m I') :=
  fun m I' hI' => by
    rw [← map_inv_eq φ T₁ h₁, ← Matrix.map_mul, ← map_mul, ← h m I' hI', map_sum]
    exact Finset.sum_congr rfl fun I _ => by rw [map_mul, minorIJ_map]

section Values

variable {K₂ : Type} [Fintype K₂] {ι₂ : K₂ → Type} [∀ k, Fintype (ι₂ k)] {Ω₂ : Type} [Field Ω₂]
  {x₂ : (Σ k, ι₂ k) → Ω₂} {zb : (Σ k, ι₂ k) → ℂ}

theorem reg_values (hz : zb ∈ mcPts (mCoordIdeal x₂)) {N j : ℕ} (i : Fin N) {μ : Type} [Fintype μ]
    (U₁ U₂ : μ → Finset (Fin N) → Ω₂) (V : μ → Ω₂) (A : Matrix (Fin N) (Fin N) Ω₂) (r : Ω₂)
    (I₀ : Finset (Fin N)) (hI₀ : IsStepRows N j i I₀)
    (hU₁ : ∀ m I, RegAt x₂ (mCoordIdeal zb) (U₁ m I)) (hU₂ : ∀ m I, RegAt x₂ (mCoordIdeal zb) (U₂ m I))
    (hV : ∀ m, RegAt x₂ (mCoordIdeal zb) (V m)) (hA : ∀ a b, RegAt x₂ (mCoordIdeal zb) (A a b))
    (hrel : ∀ m I', IsStepRows N j i I' → ∑ I, U₁ m I * minorIJ A I I' = r * U₂ m I')
    (hinv : ∑ m, V m * U₂ m I₀ = 1) :
    RegAt x₂ (mCoordIdeal zb) r ∧ ∀ m I', IsStepRows N j i I' →
      ∑ I, valAt x₂ (U₁ m I) zb * minorIJ (valMat x₂ zb A) I I' = valAt x₂ r zb * valAt x₂ (U₂ m I') zb := by
  have hsum : ∀ m I', RegAt x₂ (mCoordIdeal zb) (∑ I, U₁ m I * minorIJ A I I') ∧
      valAt x₂ (∑ I, U₁ m I * minorIJ A I I') zb =
        ∑ I, valAt x₂ (U₁ m I) zb * minorIJ (valMat x₂ zb A) I I' := fun m I' => by
    obtain ⟨h1, h2⟩ := reg_sum hz Finset.univ (fun I => U₁ m I * minorIJ A I I') fun I _ =>
      ValRing.regAt_mul (hU₁ m I) (reg_minor hz hA I I').1
    refine ⟨h1, h2.trans (Finset.sum_congr rfl fun I _ => ?_)⟩
    rw [(reg_mul hz (hU₁ m I) (reg_minor hz hA I I').1).2, (reg_minor hz hA I I').2]
  have hr : RegAt x₂ (mCoordIdeal zb) r := by
    have e : r = ∑ m, V m * ∑ I, U₁ m I * minorIJ A I I₀ := by
      simp only [hrel _ I₀ hI₀]
      calc r = r * ∑ m, V m * U₂ m I₀ := by rw [hinv, mul_one]
        _ = _ := by rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun m _ => by ring
    rw [e]
    exact (reg_sum hz _ _ fun m _ => ValRing.regAt_mul (hV m) (hsum m I₀).1).1
  refine ⟨hr, fun m I' hI' => ?_⟩
  rw [← (hsum m I').2, hrel m I' hI']
  exact (reg_mul hz hr (hU₂ m I')).2

theorem valAt_one' (hz : zb ∈ mcPts (mCoordIdeal x₂)) : valAt x₂ (1 : Ω₂) zb = 1 :=
  (ValRing.regAt_valAt_ring K₂ ι₂ Ω₂ x₂ zb hz).2.2.2.1

theorem valAt_zero' (hz : zb ∈ mcPts (mCoordIdeal x₂)) : valAt x₂ (0 : Ω₂) zb = 0 :=
  (ValRing.regAt_valAt_ring K₂ ι₂ Ω₂ x₂ zb hz).2.2.1

theorem valMat_one (hz : zb ∈ mcPts (mCoordIdeal x₂)) {N : ℕ} :
    valMat x₂ zb (1 : Matrix (Fin N) (Fin N) Ω₂) = 1 := by
  ext a b
  show valAt x₂ ((1 : Matrix (Fin N) (Fin N) Ω₂) a b) zb = _
  by_cases e : a = b
  · subst e
    rw [Matrix.one_apply_eq, Matrix.one_apply_eq, valAt_one' hz]
  · rw [Matrix.one_apply_ne e, Matrix.one_apply_ne e, valAt_zero' hz]

theorem valMat_blockDiag (hz : zb ∈ mcPts (mCoordIdeal x₂)) {N j : ℕ} {A : Matrix (Fin N) (Fin N) Ω₂}
    (hA : IsBlockDiag j A) : IsBlockDiag j (valMat x₂ zb A) := fun a b h => by
  show valAt x₂ (A a b) zb = 0
  rw [hA a b h, valAt_zero' hz]

end Values

theorem main : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (K₂ : Type) [Fintype K₂] (ι₂ : K₂ → Type) [∀ k, Fintype (ι₂ k)] (Ω₂ : Type) [Field Ω₂] (x₂ : (Σ k, ι₂ k) → Ω₂) (φ : M.Ω →+* Ω₂) (zb : (Σ k, ι₂ k) → ℂ) (F₁ F₂ : FrameData ι Ψ N M.Ω M.blk), zb ∈ mcPts (mCoordIdeal x₂) → M.IsFrame F₁ → M.IsFrame F₂ → (∀ k, M.x ⟨k, F₁.c k⟩ ≠ 0) → (∀ k, M.x ⟨k, F₂.c k⟩ ≠ 0) → ∀ (p : Ψ × Fin N) (k : K), M.blk p = some k → (∀ (m : ι k) (I : Finset (Fin N)), RegAt x₂ (mCoordIdeal zb) (φ (F₁.u ⟨k, m⟩ I)) ∧ RegAt x₂ (mCoordIdeal zb) (φ (F₂.u ⟨k, m⟩ I)) ∧ RegAt x₂ (mCoordIdeal zb) (φ (F₁.u' I ⟨k, m⟩)) ∧ RegAt x₂ (mCoordIdeal zb) (φ (F₂.u' I ⟨k, m⟩))) → (∀ a b, RegAt x₂ (mCoordIdeal zb) ((((F₁.T p.1).map φ)⁻¹ * (F₂.T p.1).map φ) a b) ∧ RegAt x₂ (mCoordIdeal zb) ((((F₂.T p.1).map φ)⁻¹ * (F₁.T p.1).map φ) a b)) → ∃ c : ℂ, c ≠ 0 ∧ ∀ h : Matrix (Fin N) (Fin N) ℂ, IsBlockDiag j h → ∀ m : ι k, ∑ I, valAt x₂ (φ (F₁.u ⟨k, m⟩ I)) zb * minorIJ (CovMap.LocImg.valMat x₂ zb (((F₁.T p.1).map φ)⁻¹ * (F₂.T p.1).map φ) * h) I (stepCols N j p.2) = c * ∑ I, valAt x₂ (φ (F₂.u ⟨k, m⟩ I)) zb * minorIJ h I (stepCols N j p.2) := by
  intro K _ ι _ Φ _ y Ψ _ _ N j M K₂ _ ι₂ _ Ω₂ _ x₂ φ zb F₁ F₂ hz hF₁ hF₂ hc₁ hc₂ p k hp hu hS
  obtain ⟨ρ, -, hρ⟩ := GlobalTheory.T.frame_change_scalar_factor K ι Φ y Ψ N j M F₁ F₂ hF₁ hF₂ hc₁ hc₂ p k hp
  have hd₁ := (hF₁.1 p.1).2
  have hd₂ := (hF₂.1 p.1).2
  have hstep : IsStepRows N j p.2 (stepCols N j p.2) := isStepRows_stepCols p.2
  have hinv : ∀ F : FrameData ι Ψ N M.Ω M.blk, M.IsFrame F →
      ∑ m : ι k, φ (F.u' (stepCols N j p.2) ⟨k, m⟩) * φ (F.u ⟨k, m⟩ (stepCols N j p.2)) = 1 := fun F hF => by
    have e := hF.2.2.1 p k hp _ _ hstep hstep
    rw [if_pos rfl] at e
    rw [← map_one φ, ← e, map_sum]
    exact Finset.sum_congr rfl fun m _ => (map_mul φ _ _).symm
  have hrel := map_rel φ (fun (m : ι k) I => F₁.u ⟨k, m⟩ I) (fun (m : ι k) I => F₂.u ⟨k, m⟩ I) _ _ hd₁ ρ
    (IsStepRows N j p.2) hρ
  obtain ⟨hr, hval⟩ := reg_values hz p.2 (fun (m : ι k) I => φ (F₁.u ⟨k, m⟩ I))
    (fun (m : ι k) I => φ (F₂.u ⟨k, m⟩ I)) (fun m : ι k => φ (F₂.u' (stepCols N j p.2) ⟨k, m⟩)) _ (φ ρ) _ hstep
    (fun m I => (hu m I).1) (fun m I => (hu m I).2.1) (fun m => (hu m _).2.2.2) (fun a b => (hS a b).1) hrel
    (hinv F₂ hF₂)
  refine ⟨valAt x₂ (φ ρ) zb, ?_, fun h hh m => sum_minor_mul M.j_le p.2 _ _ _ _ hval h hh m⟩
  have hu₂ : IsUnit (F₂.T p.1).det := isUnit_iff_ne_zero.2 hd₂
  have hu₁ : IsUnit (F₁.T p.1).det := isUnit_iff_ne_zero.2 hd₁
  have e21 : ((F₂.T p.1).map φ)⁻¹ * (F₁.T p.1).map φ = ((F₂.T p.1)⁻¹ * F₁.T p.1).map φ := by
    rw [Matrix.map_mul, map_inv_eq φ _ hd₂]
  have e12 : ((F₁.T p.1).map φ)⁻¹ * (F₂.T p.1).map φ = ((F₁.T p.1)⁻¹ * F₂.T p.1).map φ := by
    rw [Matrix.map_mul, map_inv_eq φ _ hd₁]
  have hprod : (((F₁.T p.1).map φ)⁻¹ * (F₂.T p.1).map φ) * (((F₂.T p.1).map φ)⁻¹ * (F₁.T p.1).map φ) = 1 := by
    rw [e12, e21, ← Matrix.map_mul, Matrix.mul_assoc, Matrix.mul_nonsing_inv_cancel_left _ _ hu₂,
      Matrix.nonsing_inv_mul _ hu₁]
    exact Matrix.map_one _ (map_zero φ) (map_one φ)
  have hbd : IsBlockDiag j (((F₂.T p.1).map φ)⁻¹ * (F₁.T p.1).map φ) := by
    rw [e21]
    exact ((((hF₂.1 p.1).1.inv hu₂).mul (hF₁.1 p.1).1).map φ)
  have hSS := (regMat_mul hz (fun a b => (hS a b).1) (fun a b => (hS a b).2)).2
  rw [hprod, valMat_one hz] at hSS
  refine coef_ne_zero M.j_le p.2 _ _ (fun m : ι k => valAt x₂ (φ (F₁.u' (stepCols N j p.2) ⟨k, m⟩)) zb) _ _ _ hval
    (valMat_blockDiag hz hbd) hSS.symm ?_
  have e := (reg_sum hz Finset.univ
    (fun m : ι k => φ (F₁.u' (stepCols N j p.2) ⟨k, m⟩) * φ (F₁.u ⟨k, m⟩ (stepCols N j p.2)))
    fun m _ => ValRing.regAt_mul (hu m _).2.2.1 (hu m _).1).2
  rw [hinv F₁ hF₁, valAt_one' hz] at e
  rw [e]
  exact Finset.sum_congr rfl fun m _ => (reg_mul hz (hu m _).2.2.1 (hu m _).1).2.symm

end GlobalTheory.CompanionTheory.Ar.PB.CovMap.LocImg.FV
