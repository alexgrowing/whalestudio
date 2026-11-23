import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GL4GeometricSide.InnerEq
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GL4GeometricSide.HasDerivAtOfDual
import Development.AutomorphicArithmetic.Foundations.BaseChangeIdentities.RealTraceClifford.ActEig
import Development.AutomorphicArithmetic.Foundations.BaseChangeIdentities.RealTraceClifford.KerReg
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.InfinitesimalCharacterGL.HasInfCharGLIff
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.HeckeFubiniCompatibility.PActLoc
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsMulRightInvariantOfCenter

open UpperTheory.V.Z.GSp4Splitting PositivityTheory.RgBcC PositivityTheory.RgBcC.RealD PositivityTheory.Rg.BcB.Desc

noncomputable section

namespace UpperTheory.V.Z.GSp4Splitting

open MeasureTheory Matrix Finset NumberField
open PositivityTheory.RgTw (Mat G)
open PositivityTheory.RgBcC.Bridge (along)
open scoped InnerProductSpace ContDiff

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ}

private theorem val_mem (y : G n) : y.val ∈ GLs n := ((UpperTheory.RealTr.basic n).2.1 y.val).2 y.isUnit

private theorem mul_mem {x y : Mat n} (hx : x ∈ GLs n) (hy : y ∈ GLs n) : x * y ∈ GLs n := by
  show (x * y).det ≠ 0
  rw [Matrix.det_mul]
  exact mul_ne_zero hx hy

private def trR (M : KMod n) (T : M.V →L[ℂ] M.V) : (M.V →L[ℂ] M.V) →L[ℂ] ℂ :=
  LinearMap.toContinuousLinearMap
    (((LinearMap.trace ℂ M.V).comp (ContinuousLinearMap.coeLM ℂ)).comp (LinearMap.mulRight ℂ T))

private theorem trR_apply (M : KMod n) (T X : M.V →L[ℂ] M.V) :
    trR M T X = LinearMap.trace ℂ M.V ((X * T : M.V →L[ℂ] M.V) : M.V →ₗ[ℂ] M.V) := rfl

section Abs

variable [MeasurableSpace (Un n)] [BorelSpace (Un n)] (ν : Measure (Un n)) [ν.IsHaarMeasure] (M : KMod n)
  {ι : Type} [Fintype ι] {c : ι → Un n → ℂ} {F : ι → Mat n → ℂ} {F0 : Mat n → ℂ}

private theorem integrable_c (hc : ∀ j, Continuous (c j)) (j : ι) : Integrable (fun κ => c j κ • M.ρ κ) ν := by
  haveI : CompactSpace (Un n) := GlobalTheory.compactSpace_unitaryGroup (Fin n) ℂ
  exact ((hc j).smul M.cont).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

private theorem sec_eq (hc : ∀ j, Continuous (c j))
    (hF : ∀ y ∈ GLs n, ∀ κ : Un n, F0 (y * κ.1) = ∑ j, c j κ * F j y) {y : Mat n} (hy : y ∈ GLs n) :
    ∑ j, F j y • ∫ κ, c j κ • M.ρ κ ∂ν = ∫ κ, F0 (y * κ.1) • M.ρ κ ∂ν := by
  have h1 : ∀ κ : Un n, F0 (y * κ.1) • M.ρ κ = ∑ j, F j y • (c j κ • M.ρ κ) := by
    intro κ
    rw [hF y hy κ, Finset.sum_smul]
    exact Finset.sum_congr rfl fun j _ => by rw [smul_smul, mul_comm]
  simp only [h1]
  rw [integral_finset_sum (f := fun j κ => F j y • (c j κ • M.ρ κ)) _ fun j _ => (integrable_c ν M hc j).smul (F j y)]
  simp only [integral_smul]

private theorem sec_equiv (hc : ∀ j, Continuous (c j))
    (hF : ∀ y ∈ GLs n, ∀ κ : Un n, F0 (y * κ.1) = ∑ j, c j κ * F j y) {y : Mat n} (hy : y ∈ GLs n) (a : Un n) :
    ∑ j, F j (y * a.1) • ∫ κ, c j κ • M.ρ κ ∂ν = M.ρ a⁻¹ * ∑ j, F j y • ∫ κ, c j κ • M.ρ κ ∂ν := by
  haveI := FiniteDimensional.complete ℂ M.V
  have ha : a.1 ∈ GLs n := val_mem (Unitary.toUnits a)
  rw [sec_eq ν M hc hF (mul_mem hy ha), sec_eq ν M hc hF hy]
  have hint : Integrable (fun κ : Un n => F0 (y * κ.1) • M.ρ κ) ν := by
    have h1 : (fun κ : Un n => F0 (y * κ.1) • M.ρ κ) = fun κ => ∑ j, F j y • (c j κ • M.ρ κ) := by
      funext κ
      rw [hF y hy κ, Finset.sum_smul]
      exact Finset.sum_congr rfl fun j _ => by rw [smul_smul, mul_comm]
    rw [h1]
    exact integrable_finset_sum _ fun j _ => (integrable_c ν M hc j).smul (F j y)
  have h2 := (ContinuousLinearMap.mul ℂ (M.V →L[ℂ] M.V) (M.ρ a⁻¹)).integral_comp_comm hint
  simp only [ContinuousLinearMap.mul_apply'] at h2
  rw [← h2, ← integral_mul_left_eq_self (fun κ : Un n => M.ρ a⁻¹ * (F0 (y * κ.1) • M.ρ κ)) a]
  refine integral_congr_ae (Filter.Eventually.of_forall fun κ => ?_)
  simp only [mul_smul_comm, ← map_mul, inv_mul_cancel_left, Submonoid.coe_mul, mul_assoc]

variable [MeasurableSpace (G n)] [BorelSpace (G n)] (μ : Measure (G n)) [μ.IsHaarMeasure]
  {k : Mat n → (M.V →L[ℂ] M.V)} {val : Inf n → ℂ} {T' : ℝ}

omit [MeasurableSpace (Un n)] [BorelSpace (Un n)] in
private theorem integrable_k (hk : IsMult μ M k val T') {f : Mat n → ℂ} (hf : ContinuousOn f (GLs n)) :
    Integrable (fun y : G n => f y.val • k y.val) μ := by
  obtain ⟨h1, h2, -⟩ := UpperTheory.RealTr.kerReg n μ M k val T' hk
  have h3 : Continuous fun y : G n => f y.val := hf.comp_continuous Units.continuous_val val_mem
  exact (h3.smul h1).integrable_of_hasCompactSupport (h2.mono fun y hy h0 => hy (by simp [h0]))

private theorem ker_avg (hν : ν Set.univ = 1) (hk : IsMult μ M k val T') (hc : ∀ j, Continuous (c j))
    (hs : ∀ j, ContinuousOn (F j) (GLs n))
    (hF : ∀ y ∈ GLs n, ∀ κ : Un n, F0 (y * κ.1) = ∑ j, c j κ * F j y) :
    ∫ y : G n, F0 y.val • k y.val ∂μ = ∑ j, (∫ y : G n, F j y.val • k y.val ∂μ) * ∫ κ, c j κ • M.ρ κ ∂ν := by
  haveI := FiniteDimensional.complete ℂ M.V
  haveI := GlobalTheory.CompanionTheory.QuotVan.isMulRightInvariant_GL n μ
  have he := (UpperTheory.RealTr.kerReg n μ M k val T' hk).2.2
  have h1 : ∀ κ : Un n, ∫ y : G n, F0 y.val • k y.val ∂μ =
      ∑ j, (∫ y : G n, F j y.val • k y.val ∂μ) * (c j κ • M.ρ κ) := by
    intro κ
    rw [← integral_mul_right_eq_self (fun y : G n => F0 y.val • k y.val) (Unitary.toUnits κ)]
    have h2 : ∀ y : G n, F0 (y * Unitary.toUnits κ : G n).val • k (y * Unitary.toUnits κ : G n).val =
        ∑ j, (F j y.val • k y.val) * (c j κ • M.ρ κ) := by
      intro y
      have h3 := he y.val (val_mem y) 1 κ
      simp only [OneMemClass.coe_one, one_mul, map_one] at h3
      show F0 (y.val * κ.1) • k (y.val * κ.1) = _
      rw [hF _ (val_mem y) κ, h3, Finset.sum_smul]
      exact Finset.sum_congr rfl fun j _ => by rw [smul_mul_smul_comm, mul_comm (c j κ)]
    simp only [h2]
    have h4 := fun j => ((ContinuousLinearMap.mul ℂ (M.V →L[ℂ] M.V)).flip (c j κ • M.ρ κ)).integral_comp_comm
      (integrable_k M μ hk (hs j))
    simp only [ContinuousLinearMap.flip_apply, ContinuousLinearMap.mul_apply'] at h4
    rw [integral_finset_sum _ fun j _ => (integrable_k M μ hk (hs j)).mul_const _]
    exact Finset.sum_congr rfl fun j _ => h4 j
  have h5 : ∫ y : G n, F0 y.val • k y.val ∂μ = ∫ _κ : Un n, (∫ y : G n, F0 y.val • k y.val ∂μ) ∂ν := by
    simp [Measure.real, hν]
  rw [h5, integral_congr_ae (Filter.Eventually.of_forall h1),
    integral_finset_sum _ fun j _ => (integrable_c ν M hc j).const_mul _]
  refine Finset.sum_congr rfl fun j _ => ?_
  have h6 := (ContinuousLinearMap.mul ℂ (M.V →L[ℂ] M.V) (∫ y : G n, F j y.val • k y.val ∂μ)).integral_comp_comm
    (integrable_c ν M hc j)
  simpa only [ContinuousLinearMap.mul_apply'] using h6

private theorem ker_val (hk : IsMult μ M k val T') (hc : ∀ j, Continuous (c j)) (χ : Inf n)
    (hs : ∀ j, ContDiffOn ℝ ∞ (F j) (GLs n)) (he : ∀ j, IsEig χ (F j))
    (hF : ∀ y ∈ GLs n, ∀ κ : Un n, F0 (y * κ.1) = ∑ j, c j κ * F j y) :
    ∑ j, (∫ y : G n, F j y.val • k y.val ∂μ) * ∫ κ, c j κ • M.ρ κ ∂ν =
      val χ • ∑ j, F j 1 • ∫ κ, c j κ • M.ρ κ ∂ν := by
  haveI := FiniteDimensional.complete ℂ M.V
  ext e
  set B : ι → (M.V →L[ℂ] M.V) := fun j => ∫ κ, c j κ • M.ρ κ ∂ν with hB
  have hCE : (fun x => ∑ j, F j x • B j e) ∈ CE M := by
    refine ⟨ContDiffOn.sum fun j _ => (hs j).smul contDiffOn_const, fun y hy a => ?_⟩
    have h := congrArg (fun X : M.V →L[ℂ] M.V => X e) (sec_equiv ν M hc hF hy a)
    simpa only [ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply, ContinuousLinearMap.mul_apply] using h
  have h := UpperTheory.RealTr.actEig n μ M k val T' hk χ _ hCE
    (PositivityTheory.Rg.BcB.CG.isEig_sum χ F (fun j => B j e) hs he) 1 (val_mem 1)
  have hI := fun j => integrable_k M μ hk (hs j).continuousOn
  simp only [ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply, ContinuousLinearMap.mul_apply]
  rw [← h]
  simp only [act, one_mul, map_sum, map_smul]
  rw [integral_finset_sum (f := fun j (y : PositivityTheory.RgTw.G n) => F j y.val • k y.val (B j e)) _
    fun j _ => (hI j).apply_continuousLinearMap (B j e)]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [ContinuousLinearMap.integral_apply (hI j)]
  rfl

private theorem abs_act (hν : ν Set.univ = 1) (hk : IsMult μ M k val T') (T : M.V →L[ℂ] M.V)
    (hc : ∀ j, Continuous (c j)) (χ : Inf n) (h0 : ContinuousOn F0 (GLs n))
    (hs : ∀ j, ContDiffOn ℝ ∞ (F j) (GLs n)) (he : ∀ j, IsEig χ (F j))
    (hF : ∀ y ∈ GLs n, ∀ κ : Un n, F0 (y * κ.1) = ∑ j, c j κ * F j y) :
    ∫ y : G n, phiOf M T k y * F0 y.val ∂μ = val χ * ∑ j,
      (∫ κ, LinearMap.trace ℂ M.V ((M.ρ κ * T : M.V →L[ℂ] M.V) : M.V →ₗ[ℂ] M.V) * c j κ ∂ν) * F j 1 := by
  haveI := FiniteDimensional.complete ℂ M.V
  have h1 := (trR M T).integral_comp_comm (integrable_k M μ hk h0)
  rw [ker_avg ν M μ hν hk hc (fun j => (hs j).continuousOn) hF, ker_val ν M μ hk hc χ hs he hF] at h1
  have h2 : ∀ y : G n, phiOf M T k y * F0 y.val = trR M T (F0 y.val • k y.val) := by
    intro y
    rw [map_smul, smul_eq_mul, mul_comm]
    rfl
  simp only [h2]
  rw [h1, map_smul, map_sum, smul_eq_mul]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_smul, smul_eq_mul, mul_comm, ← (trR M T).integral_comp_comm (integrable_c ν M hc j)]
  congr 1
  refine integral_congr_ae (Filter.Eventually.of_forall fun κ => ?_)
  simp only [map_smul, smul_eq_mul, trR_apply, mul_comm]

end Abs

private theorem along_right {E : Type} [Field E] [NumberField E] [IsCMField E] (w : InfinitePlace E)
    (g : GlobalTheory.CuspRep.GA E n) (φ ψ : GlobalTheory.CuspRep.GA E n → ℂ) (κ : Un n) (h : ∀ x, ψ x = along w x φ κ.1) {y : Mat n}
    (hy : y ∈ GLs n) : along w g φ (y * κ.1) = along w g ψ y := by
  classical
  obtain ⟨t, rfl⟩ := ((UpperTheory.RealTr.basic n).2.1 y).1 hy
  have e1 : t.val * κ.1 = (t * Unitary.toUnits κ : G n).val := rfl
  have e2 : κ.1 = (Unitary.toUnits κ : G n).val := rfl
  rw [e1, PositivityTheory.Rg.BcB.CG.along_val, PositivityTheory.Rg.BcB.CG.along_val, h, e2, PositivityTheory.Rg.BcB.CG.along_val, Pi.mulSingle_mul,
    PositivityTheory.Rg.BcB.CG.infinitePart_mul, mul_assoc]

end UpperTheory.V.Z.GSp4Splitting

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

open MeasureTheory PositivityTheory.RgBcC.Bridge in
open scoped InnerProductSpace in
theorem UpperTheory.V.Z.GSp4Splitting.locAct :
    LocAct := by
  intro E _ _ _ n hn π hθ K hKo hKc hKθ _ _ μf _ D w lam hch _ _ ν _ hν _ _ μC _ M T P hP k val T' hk u g
  have hK := (rlK E n hn π hθ K hKo hKc hKθ μf D w).1
  obtain ⟨S, hfd, hu, hS⟩ := hK.fin u
  let b := stdOrthonormalBasis ℂ S
  have hexp : ∀ x ∈ S, x = ∑ j, ⟪((b j : S) : D.U), x⟫_ℂ • ((b j : S) : D.U) := by
    intro x hx
    have h := congrArg Subtype.val (b.sum_repr' (⟨x, hx⟩ : S))
    simpa [Submodule.coe_sum, Submodule.coe_inner] using h.symm
  have hPu : P u ∈ S := by
    rw [← S.orthogonal_orthogonal, Submodule.mem_orthogonal]
    intro v hv
    rw [hP u v]
    have h0 : ∀ κ, ⟪v, D.σ w κ u⟫_ℂ = 0 := fun κ => (Submodule.mem_orthogonal' _ _).1 hv _ (hS κ u hu)
    simp [h0]
  have hev : ∀ x ∈ S, (D.i x).1.1 = ∑ j, ⟪((b j : S) : D.U), x⟫_ℂ • (D.i (b j : S)).1.1 := by
    intro x hx
    conv_lhs => rw [hexp x hx]
    simp only [map_sum, map_smul, Submodule.coe_sum, Submodule.coe_smul]
  have heig := (bridge E n π.V w (infOf lam)).2 hch
  have h := abs_act ν M μC (c := fun j κ => ⟪((b j : S) : D.U), D.σ w κ u⟫_ℂ)
    (F := fun j => along w g (D.i (b j : S)).1.1) (F0 := along w g (D.i u).1.1) hν hk T (fun j => hK.cont _ _) (infOf lam)
    (PositivityTheory.Rg.BcB.CG.contDiffOn_along w g (D.i u).1.2).continuousOn
    (fun j => PositivityTheory.Rg.BcB.CG.contDiffOn_along w g (D.i _).1.2) (fun j => heig _ (D.i _).2 g)
    (fun y hy κ => by
      rw [along_right w g _ _ κ (D.hσ w κ u) hy, hev _ (hS κ u hu), along_sum, Finset.sum_apply]
      simp only [along_smul, Pi.smul_apply, smul_eq_mul])
  rw [h, hev _ hPu, Finset.sum_apply]
  simp only [along_one, Pi.smul_apply, smul_eq_mul, hP u]
