import Mathlib
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.ConvolutionSmoothL2
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.DiscreteSpectrumKFiniteDecomposition
import Formalism.HarderNarasimhan.ShiftInvariance
import Formalism.RealPlaceAnalysis.FinalF
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.LamXEquivariant
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.UnipotentOfTracePowEqSize
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RingOfIntegersEqZeroOfNatCastDvdOfNormEmbeddingL
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.NormExpSubOneLeExpNorm
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.NormPosOfIsUnit
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.AutPointLatticeIntersectionSelfDualProperties
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsIntegralOfLeftEigenvectorOfLattice
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LatUnipMapMulVec

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec
open scoped InnerProductSpace ComplexOrder ContDiff

noncomputable section

namespace GlobalTheory.NearElement

theorem conj_pow_of_mul_eq_one {A n : Type} [CommRing A] [Fintype n] [DecidableEq n]
    (X Y G : Matrix n n A) (h : X * Y = 1) (m : ℕ) : (Y * G * X) ^ m = Y * G ^ m * X := by
  induction m with
  | zero => simp [mul_eq_one_comm.1 h]
  | succ m ih =>
    rw [pow_succ, ih, pow_succ]
    calc Y * G ^ m * X * (Y * G * X) = Y * G ^ m * (X * Y) * G * X := by simp only [mul_assoc]
      _ = _ := by rw [h]; simp only [mul_assoc, mul_one, one_mul]

theorem trace_conj_pow {A n : Type} [CommRing A] [Fintype n] [DecidableEq n]
    (X Y G : Matrix n n A) (h : X * Y = 1) (m : ℕ) : ((Y * G * X) ^ m).trace = (G ^ m).trace := by
  rw [conj_pow_of_mul_eq_one X Y G h, Matrix.trace_mul_cycle, h, one_mul]

theorem trace_pow_cong (E : Type) [Field E] [NumberField E] (n g : ℕ) (Λ : Submodule (𝓞 E) (Fin n → E))
    (G : Matrix (Fin n) (Fin n) E) (hfg : Λ.FG) (hsp : Submodule.span E (Λ : Set (Fin n → E)) = ⊤)
    (hrad : (Ideal.span {(g : 𝓞 E)}).IsRadical) (hg : 1 ≤ g) (hG : ∀ y ∈ Λ, G *ᵥ y ∈ Λ)
    (hU : ∀ y ∈ Λ, ∃ z ∈ Λ, ((G - 1) ^ n) *ᵥ y = (g : E) • z) (j : ℕ) :
    ∃ t : 𝓞 E, (G ^ j).trace - n = (g : E) * (t : E) := by
  have hpow : ∀ (M : Matrix (Fin n) (Fin n) E), (∀ y ∈ Λ, M *ᵥ y ∈ Λ) → ∀ m : ℕ, ∀ y ∈ Λ, (M ^ m) *ᵥ y ∈ Λ := by
    intro M hM m
    induction m with
    | zero => intro y hy; simpa using hy
    | succ m ih => intro y hy; rw [pow_succ, ← mulVec_mulVec]; exact ih _ (hM y hy)
  set S := ∑ i ∈ Finset.range j, G ^ i with hS
  have hSΛ : ∀ y ∈ Λ, S *ᵥ y ∈ Λ := by
    intro y hy
    rw [hS, Matrix.sum_mulVec]
    exact Λ.sum_mem fun i _ => hpow G hG i y hy
  have e : G ^ j - 1 = (G - 1) * S := (mul_geom_sum G j).symm
  have hc : Commute (G - 1) S := by
    show (G - 1) * S = S * (G - 1)
    rw [hS, mul_geom_sum, geom_sum_mul]
  obtain ⟨t, ht⟩ := GlobalTheory.trace_mem_of_nilpotent_mod_radical E n n g Λ (G ^ j - 1) hfg hsp hrad hg
    (fun y hy => by rw [sub_mulVec, one_mulVec]; exact Λ.sub_mem (hpow G hG j y hy) hy)
    (fun y hy => by rw [e, hc.mul_pow, ← mulVec_mulVec]; exact hU _ (hpow S hSΛ n y hy))
  exact ⟨t, by rw [← ht]; simp⟩

theorem embedding_eq_or_conj (I : AutInst) (ι : I.E →+* ℂ) :
    ∃ v, ι = I.φ v ∨ ι = ComplexEmbedding.conjugate (I.φ v) := by
  refine ⟨(InfinitePlace.mk ι).comap (algebraMap I.F I.E), ?_⟩
  rcases GlobalTheory.Count.Test.embedding_cases I (InfinitePlace.mk ι) with h | h <;>
    rcases InfinitePlace.embedding_mk_eq ι with h' | h'
  · exact Or.inl (h'.symm.trans h)
  · right
    rw [← h, h']; simp
  · exact Or.inr (h'.symm.trans h)
  · left
    exact star_injective (h'.symm.trans h)

theorem radius_bounds (c : ℝ) (hc : 0 < c) (hc' : c ≤ 1 / 10 ^ 5) (n f : ℝ) (hn : 1 ≤ n) (hf : 1 ≤ f) :
    n * (c / (n ^ 8 * f ^ 2)) ≤ 1 / 4 ∧ 3 * Real.sqrt (n * (c / (n ^ 8 * f ^ 2))) < 1 / 4 ∧
      ∀ q : ℝ, 0 ≤ q → q ^ 2 ≤ n → 3 * Real.sqrt (n * (c / (n ^ 8 * f ^ 2))) * q * n * f ≤ 1 / 100 := by
  have key : n * (c / (n ^ 8 * f ^ 2)) * (n ^ 3 * f ^ 2) ≤ c := by
    have e : n * (c / (n ^ 8 * f ^ 2)) * (n ^ 3 * f ^ 2) = c / n ^ 4 := by field_simp
    rw [e]
    exact div_le_self hc.le (one_le_pow₀ hn)
  have h0 : 0 ≤ n * (c / (n ^ 8 * f ^ 2)) := by positivity
  generalize n * (c / (n ^ 8 * f ^ 2)) = a at key h0
  have h1 : 1 ≤ n ^ 3 * f ^ 2 := one_le_mul_of_one_le_of_one_le (one_le_pow₀ hn) (one_le_pow₀ hf)
  have ha : a ≤ c := le_trans (le_mul_of_one_le_right h0 h1) key
  refine ⟨by linarith, ?_, fun q hq hqn => ?_⟩
  · have : Real.sqrt a < 1 / 12 := by
      rw [Real.sqrt_lt' (by norm_num)]; linarith
    linarith
  · refine (pow_le_pow_iff_left₀ (by positivity) (by norm_num) two_ne_zero).1 ?_
    have e : (3 * Real.sqrt a * q * n * f) ^ 2 = 9 * (a * (q ^ 2 * n ^ 2 * f ^ 2)) := by
      rw [mul_pow, mul_pow, mul_pow, mul_pow, Real.sq_sqrt h0]; ring
    have h2 : a * (q ^ 2 * n ^ 2 * f ^ 2) ≤ a * (n ^ 3 * f ^ 2) := by
      rw [pow_succ' n 2]; gcongr
    rw [e]; linarith

theorem near_unipotent : NearUnip := by
  intro B d c hc hc' hn hg hrad ep δ hep hδ
  have hf : 1 ≤ B.I.f := Module.finrank_pos
  obtain ⟨r1, r2, r3⟩ := radius_bounds c hc hc' B.I.n B.I.f (by exact_mod_cast hn) (by exact_mod_cast hf)
  rw [← hep] at r1 r2 r3
  rw [← hδ] at r2 r3
  refine ⟨?_, r2, fun q hq => r3 q (Nat.cast_nonneg q) (by exact_mod_cast hq)⟩
  rintro x a ⟨ha, hne, hd⟩
  have hep0 : 0 ≤ ep := by rw [hep]; positivity
  have he : B.e (x⁻¹ * a * x).2 ≠ 0 := right_ne_zero_of_mul hne
  have hK := B.e_adm.2.2.2.2.1 _ he
  have hU := B.e_adm.2.2.2.2.2.2 _ he
  obtain ⟨γ, -, hinf, hfin⟩ := id ha
  have hg1 : 1 ≤ B.g₀ := by omega
  obtain ⟨hG, hGU⟩ := GlobalTheory.PointLattice.lamX_unipMod B.I x a γ B.g₀ hg1 hfin hK hU
  obtain ⟨-, hfg, hsp, -⟩ := GlobalTheory.PointLattice.lamX_selfDual B.I x
  generalize (γ : Matrix (Fin B.I.n) (Fin B.I.n) B.I.E) = G at hinf hfin hG hGU
  have hP : ∀ v, B.I.P v * (B.I.P v)⁻¹ = 1 := fun v =>
    Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).1 (B.I.P_unit v))
  have htr : ∀ v j, (uMat ((x⁻¹ * a * x).1 v) ^ j).trace = B.I.φ v (G ^ j).trace := by
    intro v j
    have e : uMat ((x⁻¹ * a * x).1 v) = uMat (x.1 v)⁻¹ * uMat (a.1 v) * uMat (x.1 v) := rfl
    rw [e, trace_conj_pow _ _ _ (Units.mul_inv _), hinf, trace_conj_pow _ _ _ (hP v), AddMonoidHom.map_trace]
    congr 1
    exact (map_pow (B.I.φ v).mapMatrix G j).symm
  have harch : ∀ v, (∀ j : ℕ, j ≤ B.I.n → ‖(uMat ((x⁻¹ * a * x).1 v) ^ j).trace - B.I.n‖ ≤ 3 * B.I.n) ∧
      ((uMat ((x⁻¹ * a * x).1 v)).trace = B.I.n →
        Real.sqrt (hs (uMat ((x⁻¹ * a * x).1 v) - 1)) ≤ 3 * Real.sqrt (B.I.n * ep)) := by
    intro v
    obtain ⟨k, X, hk, hX, e⟩ := (polar B.I.n (B.I.ε v)).1 (uMat ((x⁻¹ * a * x).1 v)) ((x⁻¹ * a * x).1 v).2
    have h1 := hd v
    rw [e, (GlobalTheory.Count.Cartan.cartan_distances _ _).1 k X hk hX] at h1
    rw [e]
    exact GlobalTheory.NearUnitaryExp.near_arch _ k X ep hk.1 ((pChar _ _ X).1.1 hX).1 hep0 h1 r1
  have htn : ∀ j, j ≤ B.I.n → (G ^ j).trace = B.I.n := by
    intro j hj
    obtain ⟨t, ht⟩ := trace_pow_cong B.I.E B.I.n B.g₀ _ G hfg hsp hrad hg1 hG hGU j
    have e : (((B.g₀ : 𝓞 B.I.E) * t : 𝓞 B.I.E) : B.I.E) = (G ^ j).trace - B.I.n := by rw [ht]; simp
    have h0 := GlobalTheory.ringOfIntegers_eq_zero_of_natCast_dvd_of_norm_embedding_le B.I.E B.g₀ (3 * B.I.n)
      ((B.g₀ : 𝓞 B.I.E) * t) (dvd_mul_right _ _) (fun ι => ?_) ?_
    · rw [h0] at e
      exact sub_eq_zero.1 (by simpa using e.symm)
    · obtain ⟨v, hv⟩ := embedding_eq_or_conj B.I ι
      have h2 := (harch v).1 j hj
      rw [htr, ← map_natCast (B.I.φ v), ← map_sub, ← e] at h2
      rcases hv with rfl | rfl
      · exact h2
      · rwa [ComplexEmbedding.conjugate_coe_eq, Complex.norm_conj]
    · have : 3 * B.I.n < B.g₀ := by omega
      exact_mod_cast this
  have hnil := (GlobalTheory.unipotent_of_trace_pow_eq_size B.I.E B.I.n G fun j _ hj => htn j hj).2
  have hmap : ∀ {A : Type} [CommRing A] (ι : B.I.E →+* A), (G.map ι - 1) ^ B.I.n = 0 := by
    intro A _ ι
    have := congrArg ι.mapMatrix hnil
    rw [map_pow, map_sub, map_one, map_zero] at this
    exact this
  refine ⟨by rw [hfin]; exact hmap _, fun v => ?_, ha, hK, fun v => ?_⟩
  · have e : uMat (a.1 v) - 1 = (B.I.P v)⁻¹ * (G.map (B.I.φ v) - 1) * B.I.P v := by
      rw [hinf, mul_sub, sub_mul, mul_one, mul_eq_one_comm.1 (hP v)]
    rw [e, conj_pow_of_mul_eq_one _ _ _ (hP v), hmap, mul_zero, zero_mul]
  · rw [hδ]
    apply (harch v).2
    have := htr v 1
    rw [htn 1 hn, pow_one, map_natCast] at this
    exact this

end GlobalTheory.NearElement
