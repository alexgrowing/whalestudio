import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TwoMulRankWLt
import Development.AbelianVarietyTheory.Definitions.Foundations.ForallEventuallyFinLocIff
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContDiffDerivSnoc
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RawLift

noncomputable section

namespace GlobalTheory.RawLift.Pointwise

theorem thetaInner_swap {D : D7} {S T' : HSp D} (μ : Measure (WO S T')) (𝓕 : Set (WO S T')) (f g : WO S T' → ℂ) :
    thetaIP μ 𝓕 g f = star (thetaIP μ 𝓕 f g) := by
  unfold thetaIP
  rw [Complex.star_def, ← integral_conj]
  congr 1
  funext w
  rw [map_mul, Complex.conj_conj, ← Complex.star_def, mul_comm]

theorem rallisF_point : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), Laws R F → ∀ (i : Fin D.R.m) (t : T), LevFix R i t → FactInf R i t → RealLow R i t → LevProd R i → ∀ (μ : Measure (WO (Vc D i) (Wc D i))) (𝓕 : Set (WO (Vc D i) (Wc D i))), IsCovolOne (ratL (Wc D i) (Vc D i)) μ 𝓕 → ∀ v, IsUnitVec R i v → ∀ (w : (R.cV i).W) (x y : (R.HW i (sg0 D A)).H), (∀ u ∈ GinfC (Wc D i), ∀ γ ∈ GfC (Wc D i), dimProd A i * ∫ z in R.fdW i, star (val R i v x z) * val R i v y (z * (u * γ)) ∂(R.νW i) = trPair R i γ x y * ∏ ρ, ⟪((v ρ : (R.MW i (sg0 D A)).sm ρ) : (R.MW i (sg0 D A)).H ρ), (R.MW i (sg0 D A)).rep ρ (infMat D.sp.cm.sig (Wc D i).gram (R.θ ρ) u) ((v ρ : (R.MW i (sg0 D A)).sm ρ) : (R.MW i (sg0 D A)).H ρ)⟫_ℂ) → ∀ γ ∈ GfC (Wc D i), ∀ h ∈ realLev R i, dimProd A i * rallisF R i t μ 𝓕 v (jointVec R i t v w) x y (γ * h) = thetaIP μ 𝓕 (jointVec R i t v w) (jointVec R i t v w) * coef R i t μ 𝓕 γ * trPair R i γ x y * (lowCoefSq R i v h : ℂ) := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F hL i t hLF hFI hRL hLP μ 𝓕 hμ v hv w x y hS γ hγ h hh
  obtain ⟨u, hu, k, hk, rfl⟩ := hh
  have hkf : k ∈ GfC (Wc D i) := hLP.1 hk
  have hcomm : u * γ = γ * u := (GlobalTheory.AutMult.commute_inf_fin ⟨u, hu⟩ ⟨γ, hγ⟩).eq

  obtain ⟨Pc, hPc⟩ : ∃ Pc, (∏ ρ, ⟪((v ρ : (R.MW i (sg0 D A)).sm ρ) : (R.MW i (sg0 D A)).H ρ),
      (R.MW i (sg0 D A)).rep ρ (infMat D.sp.cm.sig (Wc D i).gram (R.θ ρ) u)
        ((v ρ : (R.MW i (sg0 D A)).sm ρ) : (R.MW i (sg0 D A)).H ρ)⟫_ℂ) = Pc := ⟨_, rfl⟩

  have hω : R.ωP i t (1, γ * (u * k)) (jointVec R i t v w) = R.ωP i t (1, u * γ) (jointVec R i t v w) := by
    have e : ((1 : GA D (Vc D i)), γ * (u * k)) = (1, u * γ) * (1, k) := by
      rw [Prod.mk_mul_mk, one_mul, hcomm, mul_assoc]
    rw [e, map_mul, Module.End.mul_apply]
    congr 1
    exact hLF k hk _

  have h1 : thetaIP μ 𝓕 (R.ωP i t (1, γ * (u * k)) (jointVec R i t v w)) (jointVec R i t v w) =
      thetaIP μ 𝓕 (jointVec R i t v w) (jointVec R i t v w) * star Pc * coef R i t μ 𝓕 γ := by
    rw [hω]
    have hF := hFI μ 𝓕 hμ u hu γ hγ (R.ioP i (PiTensorProduct.tprod ℂ v) w) (R.ioP i (PiTensorProduct.tprod ℂ v) w)
    have hR := hRL μ 𝓕 hμ v hv w u hu
    rw [hPc] at hR
    unfold jointVec at hR ⊢
    rw [hF, thetaInner_swap, hR, star_mul', ← thetaInner_swap]

  have hval : ∀ z, val R i v y (z * (γ * (u * k))) = val R i v y (z * (u * γ)) := by
    intro z
    have hmem : (R.HW i (sg0 D A)).e y ∈ R.Wall i (sg0 D A) := by
      rw [← (hL.models.HW i (sg0 D A)).2.1]
      exact LinearMap.mem_range_self _ y
    have hm := (GlobalTheory.MultMem.mem_mult_iff _ _ _ _ _ _ _ _).1 hmem
    have hl := hm.lev (fun ρ => v ρ) k hk (z * (u * γ))
    unfold val
    rw [hLP.2.1 k hk, one_mul] at hl
    rw [← hl, hcomm]
    simp only [mul_assoc]
  have h2 := hS u hu γ hγ
  rw [hPc] at h2
  simp only [← hval] at h2

  have hinf : ∀ ρ, infMat D.sp.cm.sig (Wc D i).gram (R.θ ρ) (u * k) = infMat D.sp.cm.sig (Wc D i).gram (R.θ ρ) u := by
    intro ρ
    rw [Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.infMat_mul]
    have hk1 : infHom (Wc D i) k = 1 := hkf
    have e : infMat D.sp.cm.sig (Wc D i).gram (R.θ ρ) k = 1 := by
      show ((infHom (Wc D i) k).1).map (R.θ ρ) = 1
      rw [hk1, Units.val_one, Matrix.map_one _ (map_zero _) (map_one _)]
    rw [e, Matrix.mul_one]
  have h3 : ((lowCoefSq R i v (u * k) : ℝ) : ℂ) = star Pc * Pc := by
    unfold lowCoefSq
    simp only [hinf]
    rw [hPc]
    push_cast
    rw [Complex.star_def, Complex.conj_mul']
  unfold rallisF
  rw [h1, h3]
  linear_combination (thetaIP μ 𝓕 (jointVec R i t v w) (jointVec R i t v w) * star Pc * coef R i t μ 𝓕 γ) * h2

end GlobalTheory.RawLift.Pointwise

end
