import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.RealDescent.RealLeviDescent.HighestVectorsRegularLine
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WtRInjective
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DifferentiableCoeffRowAct
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HasDerivAtMulVec
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LineInverse
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WeylCharEqGtChar
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SecondCountableUnitary
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GelfandInfinitesimalCharacter
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SumMemOfStable
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteDimTranslationRepUnitaryModel
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.HwIrred

noncomputable section

open Matrix Finset Filter Topology
open scoped InnerProductSpace
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD GlobalTheory.CompanionTheory.RealCount GlobalTheory.CompanionTheory.RealCountG GlobalTheory.CompanionTheory.RmHol
open PositivityTheory.RgTw (Mat)

namespace GlobalTheory.CompanionTheory.RmModel

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ}

theorem exists_frame (ν : Fin n → ℤ) :
    ∃ (d : ℕ) (e : (Jd n ν → ℂ) ≃ₗ[ℂ] EuclideanSpace ℂ (Fin d)),
      ∀ (k : Matrix.unitaryGroup (Fin n) ℂ) (x y : Jd n ν → ℂ),
        ⟪e (Rm ν k.1 *ᵥ x), e (Rm ν k.1 *ᵥ y)⟫_ℂ = ⟪e x, e y⟫_ℂ := by
  let ρ : Representation ℂ (Matrix.unitaryGroup (Fin n) ℂ) (Jd n ν → ℂ) :=
    { toFun := fun k => Matrix.mulVecLin (Rm ν k.1)
      map_one' := by
        show Matrix.mulVecLin (Rm ν (1 : Matrix.unitaryGroup (Fin n) ℂ).1) = 1
        rw [GlobalTheory.CompanionTheory.CxAvg.Rm_one, Matrix.mulVecLin_one]
        rfl
      map_mul' := fun a b => by
        show Matrix.mulVecLin (Rm ν (a * b).1) = _
        rw [GlobalTheory.CompanionTheory.CxAvg.Rm_mul, Matrix.mulVecLin_mul]
        rfl }
  have hρc : ∀ v, Continuous fun k => ρ k v := fun v =>
    (GlobalTheory.CompanionTheory.CxAvg.continuous_Rm ν).matrix_mulVec continuous_const
  obtain ⟨c, hc⟩ := GlobalTheory.exists_invariant_core ρ hρc
  obtain ⟨d, τ, e, hτ, he⟩ := GlobalTheory.ThetaCplV.UnitaryTrick.exists_isURep_of_core ρ
    (fun φ v => (LinearMap.continuous_of_finiteDimensional φ).comp (hρc v)) c hc
  refine ⟨d, e, fun k x y => ?_⟩
  have h1 : ∀ z, e (Rm ν k.1 *ᵥ z) = τ k (e z) := fun z => he k z
  rw [h1, h1]
  exact (LinearIsometry.mk (τ k).toLinearMap (hτ.2.2.1 k)).inner_map_map _ _

theorem hasDerivAt_Rm (ν : Fin n → ℤ) (X : Mat n) (γ : ℝ → Matrix.unitaryGroup (Fin n) ℂ)
    (hγ : ∀ t : ℝ, (γ t).1 = NormedSpace.exp ((t : ℂ) • X)) (c : Jd n ν → ℂ) :
    HasDerivAt (fun t : ℝ => Rm ν (γ t).1 *ᵥ c) (XA ν X *ᵥ c) 0 := by
  have hp : HasDerivAt (fun t : ℝ => NormedSpace.exp ((t : ℂ) • X)) X 0 := by
    refine hasDerivAt_pi.2 fun a => hasDerivAt_pi.2 fun b => ?_
    exact GlobalTheory.CompanionTheory.GelfAct.hasDerivAt_exp_entry X a b
  have hentry : ∀ i j, HasDerivAt (fun t : ℝ => Rm ν (NormedSpace.exp ((t : ℂ) • X)) i j) (XA ν X i j) 0 := by
    intro i j
    have h1 := (holRm n ν i j 1 one_mem_GLs).hasFDerivAt.restrictScalars ℝ
    have h0 : NormedSpace.exp (((0 : ℝ) : ℂ) • X) = 1 := by simp
    exact h1.comp_hasDerivAt_of_eq (0 : ℝ) hp h0.symm
  simp only [hγ]
  refine hasDerivAt_pi.2 fun i => ?_
  simp only [Matrix.mulVec, dotProduct]
  exact HasDerivAt.fun_sum fun j _ => (hentry i j).mul_const _

theorem XA_eq_sum (ν : Fin n → ℤ) (X : Mat n) : XA ν X = ∑ a, ∑ b, X a b • Xu ν a b := by
  have h : XA ν X = XA ν (∑ a, ∑ b, Matrix.single a b (X a b)) := congrArg (XA ν) (Matrix.matrix_eq_sum_single X)
  rw [h, XA_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [XA_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  have h2 : (Matrix.single a b (X a b) : Mat n) = X a b • Matrix.single a b (1 : ℂ) := by simp
  rw [h2, XA_smul]
  rfl

theorem strict_kill (ν : Fin n → ℤ) (c : Jd n ν → ℂ) (hc : ∀ a b, a < b → Xu ν a b *ᵥ c = 0) (B : Mat n)
    (hB : ∀ i j, j ≤ i → B i j = 0) : XA ν B *ᵥ c = 0 := by
  rw [XA_eq_sum]
  have h : (∑ a, ∑ b, B a b • Xu ν a b) *ᵥ c = ∑ a, ∑ b, B a b • (Xu ν a b *ᵥ c) := by
    simp only [← Matrix.toLin'_apply, map_sum, LinearMap.sum_apply, map_smul, LinearMap.smul_apply]
  rw [h]
  refine Finset.sum_eq_zero fun a _ => Finset.sum_eq_zero fun b _ => ?_
  rcases lt_or_ge a b with h | h
  · rw [hc a b h, smul_zero]
  · rw [hB a b h, zero_smul]

theorem fix_of_killed (ν : Fin n → ℤ) (c : Jd n ν → ℂ) (hc : ∀ a b, a < b → Xu ν a b *ᵥ c = 0) (g : Mat n)
    (h1 : ∀ i j, j < i → g i j = 0) (h2 : ∀ i, g i i = 1) : Rm ν g *ᵥ c = c := by
  classical
  obtain ⟨N, hN⟩ : ∃ N : Mat n, N = g - 1 := ⟨_, rfl⟩
  have hNs : ∀ i j, j ≤ i → N i j = 0 := by
    intro i j hji
    rcases hji.eq_or_lt with rfl | h
    · simp [hN, h2]
    · simp [hN, h1 i j h, Matrix.one_apply_ne h.ne']
  let G : ℂ → Mat n := fun t => 1 + t • N
  have hGt : ∀ t, (G t).BlockTriangular id := fun t i j hij => by
    have hij' : j < i := hij
    simp [G, Matrix.one_apply_ne hij'.ne', hNs i j hij'.le]
  have hGd : ∀ t, (G t).det = 1 := by
    intro t
    rw [Matrix.det_of_upperTriangular (hGt t)]
    simp [G, hNs _ _ le_rfl]
  have hGu : ∀ t, IsUnit (G t).det := fun t => by rw [hGd]; exact isUnit_one
  have hGm : ∀ t, G t ∈ GLs n := fun t => mem_GLs_of_isUnit (hGu t)
  have hinv : ∀ t i j, j < i → (G t)⁻¹ i j = 0 := by
    intro t i j hij
    haveI := Matrix.invertibleOfIsUnitDet (G t) (hGu t)
    exact Matrix.blockTriangular_inv_of_blockTriangular (hGt t) hij
  let B : ℂ → Mat n := fun t => (G t)⁻¹ * N
  have hB : ∀ t i j, j ≤ i → B t i j = 0 := by
    intro t i j hji
    simp only [B, Matrix.mul_apply]
    refine Finset.sum_eq_zero fun k _ => ?_
    rcases lt_or_ge k i with h | h
    · rw [hinv t i k h, zero_mul]
    · rw [hNs k j (hji.trans h), mul_zero]
  have hGB : ∀ t, G t * B t = N := fun t => by
    simp only [B]
    rw [← mul_assoc, Matrix.mul_nonsing_inv _ (hGu t), one_mul]
  have hline : ∀ t, HasDerivAt G N t := fun t => by
    have h := ((hasDerivAt_id t).smul_const N).const_add (1 : Mat n)
    rw [one_smul] at h
    exact h
  have hdi : ∀ i t, HasDerivAt (fun s => (Rm ν (G s) *ᵥ c) i) 0 t := by
    intro i t
    have hij : ∀ j, HasDerivAt (fun s => Rm ν (G s) i j) ((Rm ν (G t) * XA ν (B t)) i j) t := by
      intro j
      have h0 := (holRm n ν i j (G t) (hGm t)).hasFDerivAt.comp_hasDerivAt t (hline t)
      rw [← fderiv_Rm (holRm n ν) (hGm t) (B t) i j, hGB]
      exact h0
    have hs : HasDerivAt (fun s => (Rm ν (G s) *ᵥ c) i) (∑ j, (Rm ν (G t) * XA ν (B t)) i j * c j) t := by
      simp only [Matrix.mulVec, dotProduct]
      exact HasDerivAt.fun_sum fun j _ => (hij j).mul_const _
    have hz : ∑ j, (Rm ν (G t) * XA ν (B t)) i j * c j = 0 := by
      have h3 : (Rm ν (G t) * XA ν (B t)) *ᵥ c = 0 := by
        rw [← Matrix.mulVec_mulVec, strict_kill ν c hc (B t) (hB t), Matrix.mulVec_zero]
      simpa [Matrix.mulVec, dotProduct] using congrFun h3 i
    rwa [hz] at hs
  funext i
  have h3 := is_const_of_deriv_eq_zero (fun t => (hdi i t).differentiableAt) (fun t => (hdi i t).deriv) 1 0
  have e1 : G 1 = g := by simp [G, hN]
  have e0 : G 0 = 1 := by simp [G]
  simp only [e1, e0, GlobalTheory.CompanionTheory.RmHol.Rm_one, Matrix.one_mulVec] at h3
  exact h3

theorem line_of_killed (ν : Fin n → ℤ) (c : Jd n ν → ℂ) (hc : ∀ a b, a < b → Xu ν a b *ᵥ c = 0) :
    ∃ s : ℂ, c = s • ((wb ν).repr (HW.hv ν) : Jd n ν → ℂ) := by
  classical
  obtain ⟨u, hu⟩ : ∃ u, ((wb ν).repr u : Jd n ν → ℂ) = c :=
    ⟨(wb ν).equivFun.symm c, by
      have h := (wb ν).equivFun.apply_symm_apply c
      rw [Module.Basis.equivFun_apply] at h
      exact h⟩
  have hfix : ∀ g : GL (Fin n) ℂ, (∀ i j, j < i → g i j = 0) → (∀ i, g i i = 1) →
      Formalism.BasicNotions.sqAct ℂ n (dw ν) g u.1 = u.1 := by
    intro g h1 h2
    have hdet : IsUnit (g.1).det := (Matrix.isUnit_iff_isUnit_det _).1 g.isUnit
    have e := HW.Rm_mulVec ν hdet u
    have e1 : Matrix.nonsingInvUnit g.1 hdet = g := Units.ext rfl
    rw [e1, hu, fix_of_killed ν c hc g.1 h1 h2] at e
    have e2 : (wb ν).repr (GlobalTheory.Branching.sqRep ℂ n (dw ν) g u) = (wb ν).repr u :=
      DFunLike.coe_injective (e.symm.trans hu.symm)
    exact congrArg Subtype.val ((wb ν).repr.injective e2)
  obtain ⟨s, hs⟩ := (highest_weight_irreducible n (dw ν)).2.2 u.1 u.2 hfix
  refine ⟨s, ?_⟩
  have h3 : u = s • HW.hv ν := Subtype.ext hs
  rw [← hu, h3, map_smul]
  rfl

section Frame

variable {ν : Fin n → ℤ} {L : Type} [NormedAddCommGroup L] [InnerProductSpace ℂ L] [FiniteDimensional ℂ L]
  (e : (Jd n ν → ℂ) ≃ₗ[ℂ] L)

def frameL : Matrix (Jd n ν) (Jd n ν) ℂ →ₗ[ℂ] Module.End ℂ L :=
  e.conj.toLinearMap ∘ₗ (Matrix.toLin' : _ ≃ₗ[ℂ] _).toLinearMap

theorem frameL_apply (A : Matrix (Jd n ν) (Jd n ν) ℂ) (x : Jd n ν → ℂ) : frameL e A (e x) = e (A *ᵥ x) := by
  simp [frameL, LinearEquiv.conj_apply]

theorem frameL_one : frameL e 1 = 1 := by
  refine LinearMap.ext fun w => ?_
  obtain ⟨x, rfl⟩ := e.surjective w
  simp [frameL_apply]

theorem frameL_mul (A B : Matrix (Jd n ν) (Jd n ν) ℂ) : frameL e (A * B) = frameL e A * frameL e B := by
  refine LinearMap.ext fun w => ?_
  obtain ⟨x, rfl⟩ := e.surjective w
  simp [frameL_apply, Module.End.mul_apply]

theorem frameL_XA (X : Mat n) (w : L) :
    ∑ a, ∑ b, X a b • frameL e (Xu ν a b) w = frameL e (XA ν X) w := by
  rw [XA_eq_sum]
  simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply]

theorem glRel_frame : Formalism.REAL.GlRel fun a b => frameL e (Xu ν a b) := by
  intro a b c d
  have h := congrArg (frameL e) (xu_glRel n ν (holRm n ν) a b c d)
  rw [map_sub, map_sub, frameL_mul, frameL_mul] at h
  rw [h]
  split_ifs <;> simp

theorem deriv_frame (X : Mat n) (γ : ℝ → Matrix.unitaryGroup (Fin n) ℂ)
    (hγ : ∀ t : ℝ, (γ t).1 = NormedSpace.exp ((t : ℂ) • X)) (x : Jd n ν → ℂ) :
    HasDerivAt (fun t : ℝ => e (Rm ν (γ t).1 *ᵥ x)) (e (XA ν X *ᵥ x)) 0 := by
  let E : (Jd n ν → ℂ) →L[ℂ] L := e.toLinearMap.toContinuousLinearMap
  exact (E.restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt (0 : ℝ) (hasDerivAt_Rm ν X γ hγ x)

variable (he : ∀ (k : Matrix.unitaryGroup (Fin n) ℂ) (x y : Jd n ν → ℂ),
  ⟪e (Rm ν k.1 *ᵥ x), e (Rm ν k.1 *ᵥ y)⟫_ℂ = ⟪e x, e y⟫_ℂ)

include he in

theorem skew_frame (X : Mat n) (hX : Xᴴ = -X) (x y : Jd n ν → ℂ) :
    ⟪e (XA ν X *ᵥ x), e y⟫_ℂ + ⟪e x, e (XA ν X *ᵥ y)⟫_ℂ = 0 := by
  let γ : ℝ → Matrix.unitaryGroup (Fin n) ℂ := GlobalTheory.CompanionTheory.RealCount.InjHw.expU X hX
  have hγ : ∀ t : ℝ, (γ t).1 = NormedSpace.exp ((t : ℂ) • X) := fun _ => rfl
  have h0 : (γ 0).1 = 1 := by simp [hγ]
  have d3 := (deriv_frame e X γ hγ x).inner ℂ (deriv_frame e X γ hγ y)
  have hc : (fun t : ℝ => ⟪e (Rm ν (γ t).1 *ᵥ x), e (Rm ν (γ t).1 *ᵥ y)⟫_ℂ) = fun _ => ⟪e x, e y⟫_ℂ :=
    funext fun t => he _ x y
  rw [hc] at d3
  have h := d3.unique (hasDerivAt_const _ _)
  rw [h0, GlobalTheory.CompanionTheory.RmHol.Rm_one, Matrix.one_mulVec, Matrix.one_mulVec] at h
  rw [add_comm]
  exact h

include he in
theorem herm_frame (a b : Fin n) (x y : Jd n ν → ℂ) :
    ⟪e (Xu ν a b *ᵥ x), e y⟫_ℂ = ⟪e x, e (Xu ν b a *ᵥ y)⟫_ℂ := by
  have s1 : (Matrix.single a b (1 : ℂ) + (-1 : ℂ) • Matrix.single b a (1 : ℂ) : Mat n)ᴴ =
      -(Matrix.single a b (1 : ℂ) + (-1 : ℂ) • Matrix.single b a (1 : ℂ)) := by
    rw [conjTranspose_add, conjTranspose_smul, InjHw.single_conjT, InjHw.single_conjT]
    simp [add_comm]
  have s2 : (Complex.I • (Matrix.single a b (1 : ℂ) + Matrix.single b a (1 : ℂ)) : Mat n)ᴴ =
      -(Complex.I • (Matrix.single a b (1 : ℂ) + Matrix.single b a (1 : ℂ))) := by
    rw [conjTranspose_smul, conjTranspose_add, InjHw.single_conjT, InjHw.single_conjT]
    simp [add_comm]
  have h1 := skew_frame e he _ s1 x y
  have h2 := skew_frame e he _ s2 x y
  unfold Xu
  simp only [XA_add, XA_smul, Matrix.add_mulVec, Matrix.smul_mulVec, map_add, map_smul,
    inner_add_left, inner_add_right, inner_smul_left, inner_smul_right] at h1 h2
  simp only [map_neg, map_one, Complex.conj_I] at h1 h2
  generalize ⟪e (XA ν (Matrix.single a b 1) *ᵥ x), e y⟫_ℂ = p at h1 h2 ⊢
  generalize ⟪e (XA ν (Matrix.single b a 1) *ᵥ x), e y⟫_ℂ = q at h1 h2
  generalize ⟪e x, e (XA ν (Matrix.single a b 1) *ᵥ y)⟫_ℂ = r at h1 h2
  generalize ⟪e x, e (XA ν (Matrix.single b a 1) *ᵥ y)⟫_ℂ = s at h1 h2 ⊢
  linear_combination (1 / 2 : ℂ) * h1 + (Complex.I / 2) * h2 + (1 / 2 : ℂ) * (p + q - r - s) * Complex.I_sq

include he in

theorem frame_model (hν : Antitone ν) :
    ∃ (σ : Matrix.unitaryGroup (Fin n) ℂ →* (L →ₗ[ℂ] L)) (K : Fin n → Fin n → Module.End ℂ L) (v : L),
      Formalism.REAL.GlRel K ∧ (∀ a b (x y : L), ⟪K a b x, y⟫_ℂ = ⟪x, K b a y⟫_ℂ) ∧ IsDerivK σ K ∧ v ≠ 0 ∧
        Formalism.REAL.KHighest (fun _ => true) K (wtR ν) v ∧
        (∀ w : L, (∀ a b, a < b → K a b w = 0) → ∃ c : ℂ, w = c • v) ∧
        ∀ (k : Matrix.unitaryGroup (Fin n) ℂ) (z : Fin n → ℂ), k.1 = diagonal z → Function.Injective z →
          LinearMap.trace ℂ L (σ k) = weylChar ν z := by
  obtain ⟨v0, hv0, hup, hwt⟩ := HW.exists_hw n ν (holRm n ν) hν
  generalize hc : ((wb ν).repr v0 : Jd n ν → ℂ) = c0 at hup hwt
  have hc0 : c0 ≠ 0 := fun h => hv0 ((wb ν).repr.map_eq_zero_iff.1 (DFunLike.coe_injective (hc.trans h)))
  let σ : Matrix.unitaryGroup (Fin n) ℂ →* (L →ₗ[ℂ] L) :=
    { toFun := fun k => frameL e (Rm ν k.1)
      map_one' := by
        show frameL e (Rm ν (1 : Matrix.unitaryGroup (Fin n) ℂ).1) = 1
        rw [GlobalTheory.CompanionTheory.CxAvg.Rm_one, frameL_one]
      map_mul' := fun a b => by
        show frameL e (Rm ν (a * b).1) = _
        rw [GlobalTheory.CompanionTheory.CxAvg.Rm_mul, frameL_mul] }
  have hσ : ∀ k x, σ k (e x) = e (Rm ν k.1 *ᵥ x) := fun k x => frameL_apply e _ x
  refine ⟨σ, fun a b => frameL e (Xu ν a b), e c0, glRel_frame e, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro a b x y
    obtain ⟨x, rfl⟩ := e.surjective x
    obtain ⟨y, rfl⟩ := e.surjective y
    show ⟪frameL e (Xu ν a b) (e x), e y⟫_ℂ = ⟪e x, frameL e (Xu ν b a) (e y)⟫_ℂ
    rw [frameL_apply, frameL_apply]
    exact herm_frame e he a b x y
  · refine ⟨fun k x y => ?_, fun w => ⟨⊤, inferInstance, Submodule.mem_top, fun _ _ _ => Submodule.mem_top,
      fun _ _ _ _ => Submodule.mem_top, fun X γ hγ w' _ => ?_⟩⟩
    · obtain ⟨x, rfl⟩ := e.surjective x
      obtain ⟨y, rfl⟩ := e.surjective y
      rw [hσ, hσ]
      exact he k x y
    · obtain ⟨x, rfl⟩ := e.surjective w'
      have h := deriv_frame e X γ hγ x
      have e1 : (∑ a, ∑ b, X a b • frameL e (Xu ν a b) (e x)) = e (XA ν X *ᵥ x) := by
        rw [frameL_XA, frameL_apply]
      show HasDerivAt (fun t : ℝ => σ (γ t) (e x)) (∑ a, ∑ b, X a b • frameL e (Xu ν a b) (e x)) 0
      rw [e1]
      simpa only [hσ] using h
  · exact e.map_ne_zero_iff.2 hc0
  · refine ⟨fun a => ?_, fun a b hab _ => ?_⟩
    · show frameL e (Xu ν a a) (e c0) = ((wtR ν a : ℝ) : ℂ) • e c0
      rw [frameL_apply, hwt a, map_smul]
      simp [wtR]
    · show frameL e (Xu ν a b) (e c0) = 0
      rw [frameL_apply, hup a b hab, map_zero]
  · intro w hw
    obtain ⟨x, rfl⟩ := e.surjective w
    have hx : ∀ a b, a < b → Xu ν a b *ᵥ x = 0 := fun a b hab =>
      e.map_eq_zero_iff.1 (by rw [← frameL_apply]; exact hw a b hab)
    obtain ⟨s, hs⟩ := line_of_killed ν x hx
    obtain ⟨s0, hs0⟩ := line_of_killed ν c0 hup
    have hs00 : s0 ≠ 0 := by
      rintro rfl
      exact hc0 (by simpa using hs0)
    refine ⟨s / s0, ?_⟩
    have hxc : x = (s / s0) • c0 := by
      rw [hs]
      conv_rhs => rw [hs0]
      rw [smul_smul, div_mul_cancel₀ _ hs00]
    rw [hxc, map_smul]
  · intro k z hk hz
    have hu : IsUnit (k.1).det := (Matrix.isUnit_iff_isUnit_det _).1 (GlobalTheory.Branching.unitaryIncl n k).isUnit
    have h0 : ∀ a, z a ≠ 0 := by
      rw [hk, Matrix.det_diagonal] at hu
      exact fun a => (Finset.prod_ne_zero_iff.1 hu.ne_zero) a (Finset.mem_univ a)
    show LinearMap.trace ℂ L (frameL e (Rm ν k.1)) = _
    have h1 : frameL e (Rm ν k.1) = e.conj (Matrix.toLin' (Rm ν k.1)) := rfl
    rw [h1, LinearMap.trace_conj', Matrix.trace_toLin'_eq, hk]
    exact GlobalTheory.CompanionTheory.RmCharacter.rmChar n ν hν z h0 hz

end Frame

theorem rmModel : ∀ {n : ℕ} (ν : Fin n → ℤ), Antitone ν → ∃ (L : Type) (_ : NormedAddCommGroup L)
    (_ : InnerProductSpace ℂ L) (_ : FiniteDimensional ℂ L) (σ : Matrix.unitaryGroup (Fin n) ℂ →* (L →ₗ[ℂ] L))
    (K : Fin n → Fin n → Module.End ℂ L) (v : L), Formalism.REAL.GlRel K ∧
      (∀ a b (x y : L), ⟪K a b x, y⟫_ℂ = ⟪x, K b a y⟫_ℂ) ∧ IsDerivK σ K ∧ v ≠ 0 ∧
      Formalism.REAL.KHighest (fun _ => true) K (wtR ν) v ∧
      (∀ w : L, (∀ a b, a < b → K a b w = 0) → ∃ c : ℂ, w = c • v) ∧
      ∀ (k : Matrix.unitaryGroup (Fin n) ℂ) (z : Fin n → ℂ), k.1 = diagonal z → Function.Injective z →
        LinearMap.trace ℂ L (σ k) = weylChar ν z := by
  intro n ν hν
  obtain ⟨d, e, he⟩ := exists_frame ν
  exact ⟨EuclideanSpace ℂ (Fin d), inferInstance, inferInstance, inferInstance, frame_model e he hν⟩

end GlobalTheory.CompanionTheory.RmModel
