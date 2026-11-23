import Formalism.HermitianCurvature.HermitianCurvatureProofs.PointStep
import Formalism.HermitianCurvature.HermitianCurvatureProofs.UnipotentCoordinatesMeasurePreserving
import Formalism.HermitianCurvature.HermitianCurvatureProofs.IsOpenAdelicUnipotentTimesIntegralOutsideSet
import Formalism.HermitianCurvature.HermitianCurvatureProofs.NormDiagonalEntryDilationGeneratorLeOne
import Formalism.HermitianCurvature.HermitianCurvatureProofs.HermitianFormFactor
import Formalism.HermitianCurvature.HermitianCurvatureProofs.LevelsOfBuiltSetting
import Formalism.HermitianCurvature.HermitianCurvatureProofs.ConjugationContinuousOnInvertible
import Formalism.HermitianCurvature.HermitianCurvatureProofs.OrbitalIntegralAeConvergenceContinuity

open Matrix MeasureTheory
open scoped ComplexConjugate

noncomputable section

namespace Formalism.FourierDecayAlt.P.PBH

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants

variable {k : ℕ}

theorem castM_inv' {a b : ℕ} (h : a = b) (g : B.Mat k a) : D.castM h g⁻¹ = (D.castM h g)⁻¹ := by
  subst h
  simp [D.castM]

private theorem castV_rfl' {a : ℕ} (h : a = a) (v : Fin (2 * a + k + 1) → ℂ) : D.castV h v = v := by
  funext i
  rfl

theorem psi_castM {a b : ℕ} (h : a = b) (v : Fin (2 * a + k + 1) → ℂ) (c : ℂ) (g : B.Mat k a) :
    psi k b (D.castV h v) c (D.castM h g) = psi k a v c g := by
  subst h
  simp [D.castM, castV_rfl']

theorem castM_UH {a b : ℕ} (h : a = b) {g : B.Mat k a} (hg : g ∈ UH (Hpk k a)) : D.castM h g ∈ UH (Hpk k b) := by
  subst h
  simpa [D.castM] using hg

theorem castM_N {a b : ℕ} (h : a = b) {g : B.Mat k a} (hg : g ∈ Nset k a) : D.castM h g ∈ Nset k b := by
  subst h
  simpa [D.castM] using hg

theorem castM_UWv {a b : ℕ} (h : a = b) {v : Fin (2 * a + k + 1) → ℂ} {g : B.Mat k a} (hg : g ∈ UWset k a v) :
    D.castM h g ∈ UWset k b (D.castV h v) := by
  subst h
  simpa [D.castM, castV_rfl'] using hg

theorem castM_inj {a b : ℕ} (h : a = b) {g g' : B.Mat k a} (e : D.castM h g = D.castM h g') : g = g' := by
  subst h
  simpa [D.castM] using e

theorem castM_cont {a b : ℕ} (h : a = b) : Continuous (D.castM (k := k) h) := by
  subst h
  have e : (D.castM (k := k) (rfl : a = a)) = fun g => g := by
    funext g
    simp [D.castM]
  rw [e]
  exact continuous_id

theorem inWb_castV {a b : ℕ} (h : a = b) {v : Fin (2 * a + k + 1) → ℂ} (hv : inWb k a v) : inWb k b (D.castV h v) := by
  subst h
  rw [castV_rfl']
  exact hv

theorem uw_closedSubgroup (r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) : B2.IsClosedSubgroup (UWset k r z) :=
  ⟨Dx2.Rad.one_UW z, fun _ ha _ hb => WeylGroupFacts.uw_mul ha hb, fun _ ha => WeylGroupFacts.uw_inv ha,
    fun _ ha => HermitianFormFactor.UH_unit (Ux3.hpk_det k r) ha.1, B6.isClosed_UWset k r z⟩

def levA (ρ : ℕ) (x : Mt k ρ) : Mt k (ρ + 1) :=
  Matrix.of.symm (D.castM (Nat.add_comm 1 ρ) (ιLev k 1 ρ (Matrix.of x)))

private theorem continuous_ιLev_apply (ρ : ℕ) (p q : Fin (2 * (1 + ρ) + k + 1)) :
    Continuous fun x : Mt k ρ => ιLev k 1 ρ (Matrix.of x) p q := by
  simp only [Formalism.QuantumDeterminants.ιLev]
  by_cases hp : 1 ≤ p.val ∧ p.val < 2 * ρ + k + 1 + 1
  · by_cases hq : 1 ≤ q.val ∧ q.val < 2 * ρ + k + 1 + 1
    · simp only [dif_pos hp, dif_pos hq, Matrix.of_apply]
      exact (continuous_apply _).comp (continuous_apply _)
    · simp only [dif_pos hp, dif_neg hq]
      exact continuous_const
  · simp only [dif_neg hp]
    exact continuous_const

theorem levA_cont (ρ : ℕ) : Continuous (levA (k := k) ρ) := by
  apply continuous_pi
  intro p
  apply continuous_pi
  intro q
  simp only [levA, Matrix.of_symm_apply, D.castM, Matrix.reindex_apply, Matrix.submatrix_apply]
  exact continuous_ιLev_apply ρ _ _

private theorem castM_mul_hermitian_curvature {a b : ℕ} (h : a = b) (g g' : B.Mat k a) :
    D.castM h (g * g') = D.castM h g * D.castM h g' := by
  subst h
  simp [D.castM]

theorem lev_mul' (ρ : ℕ) (a b : B.Mat k ρ) :
    D.castM (Nat.add_comm 1 ρ) (ιLev k 1 ρ (a * b)) =
      D.castM (Nat.add_comm 1 ρ) (ιLev k 1 ρ a) * D.castM (Nat.add_comm 1 ρ) (ιLev k 1 ρ b) := by
  have hL := PI.QnLevBasicsW.level_group_homomorphism
  unfold Formalism.QuantumDeterminants.LevHom at hL
  rw [(hL k 1 ρ).2 a b]
  exact castM_mul_hermitian_curvature _ _ _

theorem castM_back {a b : ℕ} (h : a = b) (g : B.Mat k b) : D.castM h (D.castM h.symm g) = g := by
  subst h
  simp [D.castM]

theorem castV_back {a b : ℕ} (h : a = b) (v : Fin (2 * b + k + 1) → ℂ) : D.castV h (D.castV h.symm v) = v := by
  subst h
  rw [castV_rfl', castV_rfl']

theorem levA_apply (ρ : ℕ) (x : Mt k ρ) :
    (Matrix.of (levA ρ x) : B.Mat k (ρ + 1)) = D.castM (Nat.add_comm 1 ρ) (ιLev k 1 ρ (Matrix.of x)) := rfl

theorem lev_onto {ρ : ℕ} (z0 : Fin (2 * ρ + k + 1) → ℂ) (a : B.Mat k (ρ + 1))
    (ha : a ∈ UWset k (ρ + 1) (D.castV (Nat.add_comm 1 ρ) (liftVec k 1 ρ z0))) :
    ∃ a0 ∈ UWset k ρ z0, D.castM (Nat.add_comm 1 ρ) (ιLev k 1 ρ a0) = a := by
  have ha' : D.castM (Nat.add_comm 1 ρ).symm a ∈ UWset k (1 + ρ) (liftVec k 1 ρ z0) := by
    have := castM_UWv (Nat.add_comm 1 ρ).symm ha
    have e : D.castV (Nat.add_comm 1 ρ).symm (D.castV (Nat.add_comm 1 ρ) (liftVec k 1 ρ z0)) = liftVec k 1 ρ z0 := by
      have := castV_back (k := k) (Nat.add_comm 1 ρ).symm (liftVec k 1 ρ z0)
      simpa using this
    rwa [e] at this
  obtain ⟨y, hy, hy'⟩ := JCTx5.uw_onto (k := k) (i := 1) (r' := ρ) z0 _ ha'
  exact ⟨y, hy, by rw [hy']; exact castM_back _ a⟩

theorem muW_lev {ρ : ℕ} (z0 : Fin (2 * ρ + k + 1) → ℂ)
    (μ0 : Measure (Mt k ρ)) (μ1 : Measure (Mt k (ρ + 1)))
    (h0 : B.IsHaarOn (UWset k ρ z0) μ0)
    (h1 : B.IsHaarOn (UWset k (ρ + 1) (D.castV (Nat.add_comm 1 ρ) (liftVec k 1 ρ z0))) μ1)
    (n0 : μ0 Set.univ = 1) (n1 : μ1 Set.univ = 1) :
    μ1 = μ0.map (levA ρ) := by
  set U1 := UWset k (ρ + 1) (D.castV (Nat.add_comm 1 ρ) (liftVec k 1 ρ z0)) with hU1
  have hm : Measurable (levA (k := k) ρ) := (levA_cont ρ).measurable
  have hmem : ∀ y ∈ UWset k ρ z0, (Matrix.of (levA ρ y) : B.Mat k (ρ + 1)) ∈ U1 := fun y hy =>
    castM_UWv _ (Dx2.Tower.lev_UW 1 ρ z0 (Matrix.of y) hy)
  set ν := μ0.map (levA (k := k) ρ) with hν
  have hνu : ν Set.univ = 1 := by rw [hν, Measure.map_apply hm MeasurableSet.univ, Set.preimage_univ, n0]
  have hconc : ν U1ᶜ = 0 := by
    have hcl : IsClosed {x : Mt k (ρ + 1) | Matrix.of x ∈ U1} := B7.isClosed_UW _
    show ν {x : Mt k (ρ + 1) | Matrix.of x ∈ U1}ᶜ = 0
    rw [hν, Measure.map_apply hm hcl.measurableSet.compl]
    apply measure_mono_null _ h0.conc
    intro y hy hyU
    exact hy (hmem y hyU)
  have hleft : ∀ a ∈ U1, ν.map (lmulM a) = ν := by
    intro a ha
    obtain ⟨a0, ha0, rfl⟩ := lev_onto z0 a ha
    have hl : Measurable (lmulM (k := k) (r := ρ + 1) (D.castM (Nat.add_comm 1 ρ) (ιLev k 1 ρ a0))) :=
      B2x5.measurable_lmulM _
    have hl0 : Measurable (lmulM (k := k) (r := ρ) a0) := B2x5.measurable_lmulM _
    have e : lmulM (D.castM (Nat.add_comm 1 ρ) (ιLev k 1 ρ a0)) ∘ levA (k := k) ρ = levA ρ ∘ lmulM a0 := by
      funext x
      show (D.castM (Nat.add_comm 1 ρ) (ιLev k 1 ρ a0) * D.castM (Nat.add_comm 1 ρ) (ιLev k 1 ρ (Matrix.of x)) :
          B.Mat k (ρ + 1)) = D.castM (Nat.add_comm 1 ρ) (ιLev k 1 ρ (a0 * Matrix.of x))
      rw [lev_mul']
    rw [hν, Measure.map_map hl hm, e, ← Measure.map_map hm hl0, h0.left a0 ha0]
  have hfin : ∀ K : Set (Mt k (ρ + 1)), IsCompact K → ν K < ⊤ := by
    intro K _
    calc ν K ≤ ν Set.univ := measure_mono (Set.subset_univ _)
      _ = 1 := hνu
      _ < ⊤ := ENNReal.one_lt_top
  obtain ⟨c, hc⟩ := Formalism.FourierDecayAlt.P.haar_measure_unique_up_to_scalar k (ρ + 1) U1 μ1 ν (uw_closedSubgroup (ρ + 1) _) h1 hconc hleft hfin
  have hc1 : (c : ENNReal) = 1 := by
    have := congrArg (fun μ : Measure (Mt k (ρ + 1)) => μ Set.univ) hc
    simp only [Measure.smul_apply, n1, hνu, smul_eq_mul, mul_one, ENNReal.smul_def] at this
    exact this.symm
  have hc1' : c = 1 := by exact_mod_cast hc1
  rw [hc, hc1', one_smul]

def Qm (ρ : ℕ) (p : Mt k (1 + ρ) × Mt k ρ) : Mt k (ρ + 1) :=
  Matrix.of.symm (D.castM (Nat.add_comm 1 ρ) (Matrix.of p.1 * ιLev k 1 ρ (Matrix.of p.2)))

theorem Qm_cont (ρ : ℕ) : Continuous (Qm (k := k) ρ) := by
  have hI : Continuous fun p : Mt k (1 + ρ) × Mt k ρ => ιLev k 1 ρ (Matrix.of p.2) :=
    continuous_pi fun a => continuous_pi fun b => (continuous_ιLev_apply ρ a b).comp continuous_snd
  have h1 : Continuous fun p : Mt k (1 + ρ) × Mt k ρ => (Matrix.of p.1 : B.Mat k (1 + ρ)) := continuous_fst
  apply continuous_pi
  intro i
  apply continuous_pi
  intro j
  simp only [Qm, Matrix.of_symm_apply, D.castM, Matrix.reindex_apply, Matrix.submatrix_apply]
  exact (continuous_apply _).comp ((continuous_apply _).comp (h1.matrix_mul hI))

theorem sf_heis (ρ : ℕ) : SigmaFinite (B2.μHeis k ρ) :=
  Dx2.MN.sigma_of_haar (Formalism.FourierDecayAlt.P.heisenberg_haar_measure k ρ)

theorem sf_muN (ρ : ℕ) : SigmaFinite (D.muN k ρ) := Dx2.MN.sigma_of_haar (Dx2.MN.haar ρ)

theorem muN_succ' (ρ : ℕ) : D.muN k (ρ + 1) = ((B2.μHeis k ρ).prod (D.muN k ρ)).map (Qm ρ) := by
  have := sf_heis (k := k) ρ
  have := sf_muN (k := k) ρ
  have hl : Measurable (B2.levM k ρ) := (B2x2.levM_cont k ρ).measurable
  have hmu : Measurable (B2.mulM : Mt k (1 + ρ) × Mt k (1 + ρ) → Mt k (1 + ρ)) := B2x2.mulM_cont.measurable
  have hc : Measurable (Dx2.MN.castMt (k := k) (Nat.add_comm 1 ρ)) := (Dx2.MN.castMt_cont _).measurable
  have e1 : (B2.μHeis k ρ).prod ((D.muN k ρ).map (B2.levM k ρ)) =
      ((B2.μHeis k ρ).prod (D.muN k ρ)).map (Prod.map id (B2.levM k ρ)) := by
    rw [← Measure.map_prod_map _ _ measurable_id hl, Measure.map_id]
  rw [Dx2.MN.muN_succ, e1, Measure.map_map hmu (measurable_id.prodMap hl), Measure.map_map hc (hmu.comp (measurable_id.prodMap hl))]
  rfl

end Formalism.FourierDecayAlt.P.PBH
