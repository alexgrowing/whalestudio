import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.PPrAut
import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.LintegralMulRight
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AutomorphicFormEqOwnRealLieSmoothing
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GrowthOfTame
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DiscreteLeOfClosureClasses
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CasimirEigenOrthogonal
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LieSkewAdjointMatrix
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsFiniteMeasureQuotMeasure
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousOfIsOpenStab

noncomputable section

open NumberField MeasureTheory GlobalTheory.AutomorphicL2Unitary GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.CuspRep.CuspidalL2GL

namespace PositivityTheory.Rg.Rs.PrSt

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {N : ℕ}

theorem splitInv_act (o : Op E N) {φ : Sm E N} (h : ∀ t g, φ.1 (splitCentre E N t * g) = φ.1 g) (t : ℝ)
    (g : GA E N) : (act o φ).1 (splitCentre E N t * g) = (act o φ).1 g := by
  cases o with
  | fin k =>
    change φ.1 (splitCentre E N t * g * finGL E N k) = φ.1 (g * finGL E N k)
    rw [mul_assoc, h]
  | cpt k =>
    change φ.1 (splitCentre E N t * g * infGL E N (Unitary.toUnits k)) = φ.1 (g * infGL E N (Unitary.toUnits k))
    rw [mul_assoc, h]
  | lie X =>
    change lieD X φ.1 (splitCentre E N t * g) = lieD X φ.1 g
    have e : chart φ.1 (splitCentre E N t * g) = chart φ.1 g := by
      funext x
      unfold chart
      split_ifs
      · rw [mul_assoc, h]
      · rfl
    unfold lieD
    rw [e]

theorem isSqInt_act (hF : GlobalTheory.Published.AutomorphicFormsFiniteGL) (o : Op E N) {φ : Sm E N} (h : IsAutForm φ)
    (h' : IsSqInt φ.1) : IsSqInt (act o φ).1 := by
  let μ : Measure (GA E N) := Measure.haar
  have : μ.IsMulRightInvariant := GlobalTheory.CovolGL.isMulRightInvariant E N μ
  have hA := PrAut.isAutForm_act hF o h
  rw [← memL2_iff_isSqInt (μ := μ) (ContAut.continuous_of_isOpen_stab E N _ hA.level) hA.left
    (splitInv_act o h'.1)]
  have hm : MemL2Quotient (latticeGL E N) μ φ.1 := memL2_of_isAutForm h h'
  cases o with
  | fin k => exact hm.mul_right (finGL E N k)
  | cpt k => exact hm.mul_right (infGL E N (Unitary.toUnits k))
  | lie X =>
    let ν : Measure (Lie E N) := Measure.addHaar
    obtain ⟨α, hα, e⟩ := GlobalTheory.AutGrowth.SelfSmoothing.exists_smoothing_eq_self hF E N ν φ h
    have e' : (act (.lie X) φ).1 = GlobalTheory.CuspQuot.smoothing ν (GlobalTheory.AutGrowth.dens X α) φ.1 := by
      funext g
      change lieD X φ.1 g = _
      conv_lhs => rw [← e]
      exact GlobalTheory.AutGrowth.lieD_smoothing_eq_dens E N ν α hα φ.1 φ.2 X g
    rw [e']
    exact SmoothingSquareIntegrable.memL2_of_smoothing μ ν (GlobalTheory.AutGrowth.isTest_dens X hα)
      (ContAut.continuous_of_isOpen_stab E N φ h.level) hm

variable (E N) in

def ainv : Submodule ℂ (Sm E N) where
  carrier := {φ | ∀ t g, φ.1 (splitCentre E N t * g) = φ.1 g}
  add_mem' := fun {φ ψ} ha hb t g => by
    change φ.1 _ + ψ.1 _ = φ.1 g + ψ.1 g
    rw [ha t g, hb t g]
  zero_mem' := fun _ _ => rfl
  smul_mem' := fun c φ ha t g => by
    change c * φ.1 _ = c * φ.1 g
    rw [ha t g]

theorem mem_square_integrable_forms {φ : Sm E N} (hφ : φ ∈ A2 E N) : IsAutForm φ ∧ IsSqInt φ.1 := by
  let μ : Measure (GA E N) := Measure.haar
  have hle : A2 E N ≤ GlobalTheory.DiscClosure.autSub E N ⊓ GlobalTheory.DiscClosure.squareIntegrableSmoothSubmoduleGL μ ⊓ ainv E N :=
    Submodule.span_le.2 fun ψ hψ => ⟨⟨hψ.1, memL2_of_isAutForm hψ.1 hψ.2⟩, hψ.2.1⟩
  obtain ⟨⟨h1, h2⟩, h3⟩ := hle hφ
  exact ⟨h1, (memL2_iff_isSqInt (ContAut.continuous_of_isOpen_stab E N φ h1.level) h1.left h3).1 h2⟩

theorem isStable_square_integrable_forms (hF : GlobalTheory.Published.AutomorphicFormsFiniteGL) : IsStable (A2 E N) := by
  intro o φ hφ
  induction hφ using Submodule.span_induction with
  | mem ψ hψ => exact Submodule.subset_span ⟨PrAut.isAutForm_act hF o hψ.1, isSqInt_act hF o hψ.1 hψ.2⟩
  | zero => rw [map_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | smul c x _ hx => rw [map_smul]; exact Submodule.smul_mem _ c hx

section Adj

open GlobalTheory.CapOrth

variable {μ : Measure (GA E N)} [μ.IsHaarMeasure] [μ.IsMulRightInvariant] {W : Submodule ℂ (Sm E N)}
  (h : ∀ φ ∈ W, MemL2Quotient (latticeGL E N) μ φ.1)

theorem inner_rt {g : GA E N} (hg : ∀ φ ∈ W, rt E N g φ ∈ W) (hg' : ∀ φ ∈ W, rt E N g⁻¹ φ ∈ W) {φ ψ : Sm E N}
    (hφ : φ ∈ W) (hψ : ψ ∈ W) :
    inner ℂ (cls h (rt E N g φ)) (cls h ψ) = inner ℂ (cls h φ) (cls h (rt E N g⁻¹ ψ)) := by
  have hrr : rt E N g (rt E N g⁻¹ ψ) = ψ := by
    rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
  have e : toL2ₗ μ W h ⟨ψ, hψ⟩ = R (latticeGL E N) μ g (toL2ₗ μ W h ⟨rt E N g⁻¹ ψ, hg' ψ hψ⟩) := by
    rw [R_toL2ₗ h ⟨_, hg' ψ hψ⟩ (by rw [hrr]; exact hψ)]
    exact congrArg _ (Subtype.ext hrr.symm)
  rw [cls_mk h (hg φ hφ), cls_mk h hψ, cls_mk h hφ, cls_mk h (hg' ψ hψ), ← R_toL2ₗ h ⟨φ, hφ⟩ (hg φ hφ), e]
  let Ui : L2 (latticeGL E N) μ →ₗᵢ[ℂ] L2 (latticeGL E N) μ := ⟨(R (latticeGL E N) μ g).toLinearMap, norm_R g⟩
  exact Ui.inner_map_map _ _

theorem exists_adj (hW : IsStable W) (hA : ∀ φ ∈ W, IsAutForm φ) (o : Op E N) :
    ∃ B : Module.End ℂ (Sm E N), (∀ U : Submodule ℂ (Sm E N), IsStable U → ∀ u ∈ U, B u ∈ U) ∧
      ∀ φ ∈ W, ∀ ψ ∈ W, inner ℂ (cls h (act o φ)) (cls h ψ) = inner ℂ (cls h φ) (cls h (B ψ)) := by
  cases o with
  | fin k =>
    refine ⟨act (.fin k⁻¹), fun U hU u hu => hU _ u hu, fun φ hφ ψ hψ => ?_⟩
    have e : (finGL E N k)⁻¹ = finGL E N k⁻¹ := (map_inv _ k).symm
    have := inner_rt h (g := finGL E N k) (fun x hx => hW (.fin k) x hx)
      (fun x hx => by rw [e]; exact hW (.fin k⁻¹) x hx) hφ hψ
    rw [e] at this
    exact this
  | cpt k =>
    refine ⟨act (.cpt k⁻¹), fun U hU u hu => hU _ u hu, fun φ hφ ψ hψ => ?_⟩
    have e : (infGL E N (Unitary.toUnits k))⁻¹ = infGL E N (Unitary.toUnits k⁻¹) := by
      rw [map_inv, map_inv]
    have := inner_rt h (g := infGL E N (Unitary.toUnits k)) (fun x hx => hW (.cpt k) x hx)
      (fun x hx => by rw [e]; exact hW (.cpt k⁻¹) x hx) hφ hψ
    rw [e] at this
    exact this
  | lie X =>
    refine ⟨-act (.lie X), fun U hU u hu => U.neg_mem (hU _ u hu), fun φ hφ ψ hψ => ?_⟩
    have e := GlobalTheory.LieSkew.lie_skew E N μ W h hW hA X ⟨φ, hφ⟩ ⟨ψ, hψ⟩
    rw [LinearMap.neg_apply, show -(act (.lie X) ψ) = (-1 : ℂ) • act (.lie X) ψ by simp,
      cls_smul h (-1 : ℂ) (hW (.lie X) ψ hψ), inner_smul_right, cls_mk h (hW (.lie X) φ hφ), cls_mk h hψ,
      cls_mk h hφ, cls_mk h (hW (.lie X) ψ hψ), neg_one_mul]
    exact e

end Adj

end PositivityTheory.Rg.Rs.PrSt

end
