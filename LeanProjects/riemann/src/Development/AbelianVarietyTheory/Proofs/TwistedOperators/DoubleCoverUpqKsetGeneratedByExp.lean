import Mathlib
import Formalism.SharpRestriction.Divisibility.SchurIrreducible
import Formalism.LocalToGlobal.BesselHermitianTheta.DefsReal
import Development.AbelianVarietyTheory.Proofs.HeightProofs.FiniteDimKStableSubspaceKFiniteLie
import Development.AbelianVarietyTheory.Proofs.HeightProofs.TorusWeightVectorIffCartanWeightVector

open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible

noncomputable section

namespace GlobalTheory.CoverKGen

open GlobalTheory.RealPar GlobalTheory.RealPar.KStabLie GlobalTheory.RealPar.TorusWt Matrix

variable {p q : ℕ}

theorem blockOrd_std (p q : ℕ) :
    BlockOrd (p := p) (q := q) finSumFinEquiv (fun i => (finSumFinEquiv.symm i).isLeft) := by
  refine ⟨fun i => by simp, fun j => by simp, ?_⟩
  rintro (a | a) (b | b) hab
  · have hlt : a < b := hab
    simp only [finSumFinEquiv_apply_left, Fin.lt_def, Fin.val_castAdd]
    exact Fin.lt_def.mp hlt
  · simp [posC] at hab
  · simp [posC] at hab
  · have hlt : a < b := hab
    have := Fin.lt_def.mp hlt
    simp only [finSumFinEquiv_apply_right, Fin.lt_def, Fin.val_natAdd]
    omega

theorem exists_log (T : GrpData p q) {k : T.G} (hk : k ∈ T.Kset) :
    ∃ X, X ∈ upq p q ∧ IsKC X ∧ T.cov (T.expt X) = T.cov k := by
  have hB := blockOrd_std p q
  obtain ⟨Y, hY, hexp, -⟩ := Formalism.REAL.compact_exponential_surjective _ _ _ (mem_Kset hB T hk)
  letI : NormedRing (Mat p q) := Matrix.linftyOpNormedRing
  letI : NormedAlgebra ℚ (Mat p q) := Matrix.linftyOpNormedAlgebra
  letI : NormedSpace ℂ (Mat p q) := Matrix.linftyOpNormedSpace
  letI : CompleteSpace (Mat p q) := FiniteDimensional.complete ℂ (Mat p q)
  letI : NormedRing (Matrix (Fin (p + q)) (Fin (p + q)) ℂ) := Matrix.linftyOpNormedRing
  letI : NormedAlgebra ℚ (Matrix (Fin (p + q)) (Fin (p + q)) ℂ) := Matrix.linftyOpNormedAlgebra
  letI : NormedSpace ℂ (Matrix (Fin (p + q)) (Fin (p + q)) ℂ) := Matrix.linftyOpNormedSpace
  letI : CompleteSpace (Matrix (Fin (p + q)) (Fin (p + q)) ℂ) :=
    FiniteDimensional.complete ℂ (Matrix (Fin (p + q)) (Fin (p + q)) ℂ)
  let φ := Matrix.reindexAlgEquiv ℂ ℂ (finSumFinEquiv (m := p) (n := q))
  have hφc : Continuous φ := by
    rw [Matrix.coe_reindexAlgEquiv]
    exact continuous_id.matrix_reindex _ _
  have hφX : φ (φ.symm Y) = Y := φ.apply_symm_apply Y
  have hJ : φ (Jm p q) = Formalism.REAL.Jm (fun i => (finSumFinEquiv.symm i).isLeft) := by
    rw [Matrix.coe_reindexAlgEquiv]
    exact hB.reindex_Jm
  have hstar : ∀ M : Mat p q, φ Mᴴ = (φ M)ᴴ := fun M =>
    (Matrix.conjTranspose_reindex _ _ M).symm
  have hX : φ.symm Y ∈ upq p q := by
    show (φ.symm Y)ᴴ * Jm p q + Jm p q * φ.symm Y = 0
    apply φ.injective
    rw [map_add, map_mul, map_mul, hstar, hJ, hφX, map_zero]
    exact hY.1
  refine ⟨φ.symm Y, hX, ?_, ?_⟩
  · rw [isKC_iff]
    apply φ.injective
    rw [map_mul, map_mul, hJ, hφX]
    exact hY.2
  · apply Units.ext
    rw [T.expt_cov _ hX]
    apply φ.injective
    have hm : φ (NormedSpace.exp (φ.symm Y)) = NormedSpace.exp (φ (φ.symm Y)) :=
      NormedSpace.map_exp φ hφc _
    rw [hm, hφX, hexp]
    rfl

theorem torX_isKC (θ : Ix p q → ℝ) : IsKC (torX θ) := by
  intro a b hab
  have hne : a ≠ b := by
    rintro rfl
    exact hab (by cases a <;> trivial)
  simp [torX, Matrix.diagonal_apply_ne _ hne]

theorem cov_expt_torX (T : GrpData p q) (θ : Ix p q → ℝ) :
    ((T.cov (T.expt (torX θ)) : GL (Ix p q) ℂ) : Mat p q) =
      Matrix.diagonal fun a => Complex.exp ((θ a : ℂ) * Complex.I) := by
  rw [T.expt_cov _ (torX_mem θ)]
  unfold torX
  rw [Matrix.exp_diagonal, Pi.exp_def, Complex.exp_eq_exp_ℂ]

private theorem sq_expt_torX_sq_eq_exp (T : GrpData p q) (θ : Ix p q → ℝ) :
    ((T.sq (T.expt (torX θ)) : ℂˣ) : ℂ) ^ 2 =
      Complex.exp ((∑ a, (θ a : ℂ)) * Complex.I / 2) ^ 2 := by
  rw [T.sq_sq, cov_expt_torX, Matrix.det_diagonal, ← Complex.exp_sum, ← Complex.exp_nat_mul]
  congr 1
  rw [← Finset.sum_mul]
  push_cast
  ring

theorem sq_expt_torX (T : GrpData p q) (θ : Ix p q → ℝ) :
    ((T.sq (T.expt (torX θ)) : ℂˣ) : ℂ) = Complex.exp ((∑ a, (θ a : ℂ)) * Complex.I / 2) := by
  let f : ℝ → ℂ := fun t => ((T.sq (T.expt (t • torX θ)) : ℂˣ) : ℂ)
  let g : ℝ → ℂ := fun t => Complex.exp ((∑ a, ((t * θ a : ℝ) : ℂ)) * Complex.I / 2)
  have hsq : ∀ t, f t ^ 2 = g t ^ 2 := fun t => by
    simp only [f, g]
    rw [smul_torX]
    exact sq_expt_torX_sq_eq_exp T _
  have hg : ∀ t, g t ≠ 0 := fun t => Complex.exp_ne_zero _
  have hfc : Continuous f := by
    have h1 : Continuous fun t : ℝ => T.expt (t • torX θ) :=
      T.expt_cont.comp_continuous (continuous_id.smul continuous_const)
        (fun t => smul_mem_upq (torX_mem θ) t)
    have h2 : Continuous fun x : T.G => T.sq x := continuous_snd.comp T.emb.continuous
    exact Units.continuous_val.comp (h2.comp h1)
  have hgc : Continuous g := by fun_prop
  have hh : ∀ t, f t / g t = 1 ∨ f t / g t = -1 := fun t => by
    have h2 : (f t / g t) ^ 2 = 1 := by
      rw [div_pow, hsq t, div_self (pow_ne_zero 2 (hg t))]
    exact mul_self_eq_one_iff.mp (by rw [← sq]; exact h2)
  have h0 : f 0 / g 0 = 1 := by
    simp [f, g, T.expt_zero]
  have hcont : Continuous fun t => f t / g t := hfc.div hgc hg
  have h1 : f 1 / g 1 = 1 := by
    rcases hh 1 with h1 | h1
    · exact h1
    exfalso
    have hre : Continuous fun t => (f t / g t).re := Complex.continuous_re.comp hcont
    have hmem : (0 : ℝ) ∈ Set.Icc ((f 1 / g 1).re) ((f 0 / g 0).re) := by
      rw [h0, h1]
      norm_num
    obtain ⟨t, -, ht⟩ := intermediate_value_Icc' zero_le_one hre.continuousOn hmem
    rcases hh t with h2 | h2 <;> simp only [h2] at ht <;> norm_num at ht
  have hfg : f 1 = g 1 := (div_eq_one_iff_eq (hg 1)).mp h1
  simpa [f, g] using hfg

theorem kset_gen : ∀ (p q : ℕ), 1 ≤ p + q → ∀ (T : GrpData p q), ∀ k ∈ T.Kset,
    k ∈ Subgroup.closure (T.expt '' {Y | Y ∈ upq p q ∧ IsKC Y}) := by
  intro p q hpq T k hk
  have mem : ∀ X, X ∈ upq p q → IsKC X →
      T.expt X ∈ Subgroup.closure (T.expt '' {Y | Y ∈ upq p q ∧ IsKC Y}) :=
    fun X h1 h2 => Subgroup.subset_closure ⟨X, ⟨h1, h2⟩, rfl⟩
  obtain ⟨a0⟩ : Nonempty (Ix p q) := by
    rcases Nat.eq_zero_or_pos p with hp | hp
    · exact ⟨Sum.inr ⟨0, by omega⟩⟩
    · exact ⟨Sum.inl ⟨0, hp⟩⟩
  have hc := mem _ (torX_mem (Pi.single a0 (2 * Real.pi))) (torX_isKC (Pi.single a0 (2 * Real.pi)))
  have hcov : T.cov (T.expt (torX (Pi.single a0 (2 * Real.pi)))) = 1 := by
    apply Units.ext
    rw [cov_expt_torX, Units.val_one, ← Matrix.diagonal_one]
    congr 1
    funext a
    by_cases ha : a = a0
    · subst ha
      simp only [Pi.single_eq_same]
      push_cast
      exact Complex.exp_two_pi_mul_I
    · simp [Pi.single_eq_of_ne ha]
  have hsqc : T.sq (T.expt (torX (Pi.single a0 (2 * Real.pi)))) = -1 := by
    apply Units.ext
    rw [sq_expt_torX]
    have hs : (∑ a, (((Pi.single a0 (2 * Real.pi) : Ix p q → ℝ) a : ℝ) : ℂ)) = 2 * (Real.pi : ℂ) := by
      rw [Finset.sum_eq_single a0 (fun b _ hb => by simp [Pi.single_eq_of_ne hb]) (by simp)]
      simp
    have hpi : 2 * (Real.pi : ℂ) * Complex.I / 2 = Real.pi * Complex.I := by ring
    rw [hs, hpi, Complex.exp_pi_mul_I]
    simp
  obtain ⟨X, hX, hXK, hcovX⟩ := exists_log T hk
  have hy := mem X hX hXK
  have huniq : ∀ x : T.G, T.cov x = T.cov k → T.sq x = T.sq k → x = k := fun x h1 h2 =>
    (T.bij (T.cov k) (T.cov_mem k) (T.sq k) (T.sq_sq k)).unique ⟨h1, h2⟩ ⟨rfl, rfl⟩
  have hsq2 : ((T.sq (T.expt X) : ℂˣ) : ℂ) ^ 2 = ((T.sq k : ℂˣ) : ℂ) ^ 2 := by
    rw [T.sq_sq, T.sq_sq, hcovX]
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp hsq2 with h | h
  · rw [← huniq _ hcovX (Units.ext h)]
    exact hy
  · have hk' : T.expt X * T.expt (torX (Pi.single a0 (2 * Real.pi))) = k := by
      apply huniq
      · rw [map_mul, hcov, mul_one, hcovX]
      · apply Units.ext
        rw [map_mul, hsqc]
        simp [h]
    rw [← hk']
    exact Subgroup.mul_mem _ hy hc

end GlobalTheory.CoverKGen

end
