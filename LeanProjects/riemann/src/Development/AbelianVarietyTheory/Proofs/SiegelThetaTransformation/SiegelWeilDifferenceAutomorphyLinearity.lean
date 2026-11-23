import Mathlib
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsHeatZero
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.GCauchyStatement
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.EisAutomorphyLinear
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.HermitianThetaSummableAndDeterminesTestFn
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.FiniteClsAndStab
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.HermitianWeilActionUnitaryGroupTestFunctionsStatement
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.HermitianWeilActionSiegelParabolicExplicitStatement
open Matrix Complex NumberField GlobalTheory.SW Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (cc herm)
open scoped ComplexConjugate ComplexOrder Real Classical

namespace GlobalTheory.SW.SwdAut

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n N : ℕ}

theorem classSum_mul {M : ℕ} (hM : 0 < M) (c : ℂ) (f : Lt E n → ℂ) :
    classSum M (fun Λ => c * f Λ) = c * classSum M f := by
  haveI := (finite_cls_and_stab E n M hM).1
  haveI := Fintype.ofFinite (Cls E n M)
  simp only [classSum, finsum_eq_sum_of_fintype, Finset.mul_sum, mul_left_comm]

theorem classSum_add {M : ℕ} (hM : 0 < M) (f g : Lt E n → ℂ) :
    classSum M (fun Λ => f Λ + g Λ) = classSum M f + classSum M g := by
  haveI := (finite_cls_and_stab E n M hM).1
  haveI := Fintype.ofFinite (Cls E n M)
  simp only [classSum, finsum_eq_sum_of_fintype, mul_add, Finset.sum_add_distrib]

theorem transl_mem {β : Matrix (Fin N) (Fin N) E} (hβ : ccT β = β) :
    (fromBlocks 1 β 0 1 : M2 E N) ∈ UU E N := by
  have h : ccT (fromBlocks 1 β 0 1 : M2 E N) = fromBlocks 1 0 β 1 := by
    have h1 := Base.ccT_one (E := E) (α := Fin N)
    ext (i | i) (j | j)
    · exact congrFun (congrFun h1 i) j
    · simp [ccT, cc]
    · exact congrFun (congrFun hβ i) j
    · exact congrFun (congrFun h1 i) j
  change ccT _ * _ * _ = _
  rw [h, Matrix.J, fromBlocks_multiply, fromBlocks_multiply]
  simp

theorem add_mem_Hn (Ψ : Finset (E →+* ℂ)) {β : Matrix (Fin N) (Fin N) E} (hβ : ccT β = β)
    {Z : CM Ψ N N} (hZ : Z ∈ Hn Ψ N) : (fun τ => Z τ + β.map τ.1 : CM Ψ N N) ∈ Hn Ψ N := by
  intro τ
  have : imH (Z τ + β.map τ.1) = imH (Z τ) := by
    unfold imH
    rw [conjTranspose_add, ← Base.ccT_map, hβ, add_sub_add_right_eq_sub]
  change (imH (Z τ + β.map τ.1)).PosDef
  rw [this]; exact hZ τ

end GlobalTheory.SW.SwdAut

open GlobalTheory.SW.SwdAut in

theorem GlobalTheory.SW.swd_automorphy_linear : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Ψ : Finset (E →+* ℂ)), IsType Ψ → ∀ (n N : ℕ), Even n → 4 * N < n → ∀ (M : ℕ) (φ : Fam E n N), 0 < M → (∀ Λ ∈ Vset E n M, IsSB (φ Λ)) → ∀ Z ∈ Hn Ψ N, (∀ γ ∈ UU E N, swd Ψ M (fun Λ => weil Ψ γ (φ Λ)) (hAct Ψ γ Z) 0 0 = hFac Ψ γ Z (0 : CM Ψ n N) 0 * swd Ψ M φ Z 0 0) ∧ (∀ β : Matrix (Fin N) (Fin N) E, ccT β = β → swd Ψ M (fun Λ x => chiH Ψ β x * φ Λ x) Z 0 0 = swd Ψ M φ (fun τ => Z τ + β.map τ.1) 0 0) ∧ (∀ ψ : Fam E n N, (∀ Λ ∈ Vset E n M, IsSB (ψ Λ)) → swd Ψ M (φ + ψ) Z 0 0 = swd Ψ M φ Z 0 0 + swd Ψ M ψ Z 0 0) ∧ (∀ c : ℂ, swd Ψ M (c • φ) Z 0 0 = c * swd Ψ M φ Z 0 0) ∧ ∀ ψ : Fam E n N, (∀ Λ ∈ Vset E n M, ψ Λ = φ Λ) → swd Ψ M ψ Z 0 0 = swd Ψ M φ Z 0 0 := by
  intro E _ _ _ Ψ hΨ n N hn hN M φ hM hφ
  have h5 : ∀ (Z : CM Ψ N N) (φ ψ : Fam E n N), (∀ Λ ∈ Vset E n M, ψ Λ = φ Λ) →
      swd Ψ M ψ Z 0 0 = swd Ψ M φ Z 0 0 := fun Z φ ψ h =>
    Base.classSum_congr fun Λ hΛ => by rw [h Λ hΛ]
  have h1 : ∀ Z ∈ Hn Ψ N, ∀ γ ∈ UU E N, swd Ψ M (fun Λ => weil Ψ γ (φ Λ)) (hAct Ψ γ Z) 0 0 =
      hFac Ψ γ Z (0 : CM Ψ n N) 0 * swd Ψ M φ Z 0 0 := by
    intro Z hZ γ hγ
    unfold swd
    rw [← classSum_mul hM]
    refine Base.classSum_congr fun Λ hΛ => ?_
    have ht := (GlobalTheory.T.hermitianWeilAction_unitaryGroup_testFunctions E Ψ hΨ n N hn γ hγ _ (hφ Λ hΛ)).2.1 Z hZ 0 0
    rw [(eis_automorphy_linear E Ψ hΨ n N hn hN _ (hφ Λ hΛ) Z hZ).2.1 γ hγ, mul_sub, ← ht]
    congr 2
    · funext τ; ext k a
      exact (congrFun (Matrix.mulVec_zero (hDen' Ψ γ Z τ)⁻¹) a).symm
    · funext τ; ext k a
      exact (congrFun (Matrix.zero_vecMul (hDen Ψ γ Z τ)⁻¹) a).symm
  intro Z hZ
  refine ⟨h1 Z hZ, fun β hβ => ?_, fun ψ hψ => ?_, fun c => ?_, fun ψ h => h5 Z φ ψ h⟩
  · have hβ' : ccT (-β) = -β := by
      conv_rhs => rw [← hβ]
      ext i j; simp [ccT, cc]
    have hγ := transl_mem hβ'
    have h := h1 _ (add_mem_Hn Ψ hβ hZ) _ hγ
    have hd : ∀ (W : CM Ψ N N) τ, hDen Ψ (fromBlocks 1 (-β) 0 1 : M2 E N) W τ = 1 := by
      intro W τ; simp [hDen]
    have ha : hAct Ψ (fromBlocks 1 (-β) 0 1 : M2 E N) (fun τ => Z τ + β.map τ.1) = Z := by
      funext τ
      ext i j
      simp [hAct, hd]
    rw [ha, EisTrans.hFac_zero] at h
    simp only [hd, det_one, one_pow, Finset.prod_const_one, one_mul] at h
    rw [← h]
    refine h5 _ _ _ fun Λ hΛ => funext fun x => ?_
    rw [(GlobalTheory.T.hermitianWeilAction_siegelParabolic_explicit E Ψ hΨ n N hn _ (hφ Λ hΛ)).1 _ hγ (toBlocks_fromBlocks₂₁ _ _ _ _) x]
    simp [Base.ccT_one]
  · unfold swd
    rw [← classSum_add hM]
    refine Base.classSum_congr fun Λ hΛ => ?_
    have ht : thH Ψ (φ Λ + ψ Λ) Z 0 0 = thH Ψ (φ Λ) Z 0 0 + thH Ψ (ψ Λ) Z 0 0 := by
      unfold thH
      rw [← ((thH_summable_and_inj E Ψ hΨ n N _ (hφ Λ hΛ) Z hZ).1 0 0).of_norm.tsum_add
        ((thH_summable_and_inj E Ψ hΨ n N _ (hψ Λ hΛ) Z hZ).1 0 0).of_norm]
      exact tsum_congr fun x => by rw [Pi.add_apply, add_mul]
    rw [Pi.add_apply, ht,
      (eis_automorphy_linear E Ψ hΨ n N hn hN _ (hφ Λ hΛ) Z hZ).2.2.1 _ (hψ Λ hΛ)]
    ring
  · unfold swd
    rw [← classSum_mul hM]
    refine Base.classSum_congr fun Λ hΛ => ?_
    have ht : thH Ψ (c • φ Λ) Z 0 0 = c * thH Ψ (φ Λ) Z 0 0 := by
      unfold thH
      rw [← tsum_mul_left]
      exact tsum_congr fun x => by rw [Pi.smul_apply, smul_eq_mul, mul_assoc]
    rw [Pi.smul_apply, ht, (eis_automorphy_linear E Ψ hΨ n N hn hN _ (hφ Λ hΛ) Z hZ).2.2.2 c,
      mul_sub]
