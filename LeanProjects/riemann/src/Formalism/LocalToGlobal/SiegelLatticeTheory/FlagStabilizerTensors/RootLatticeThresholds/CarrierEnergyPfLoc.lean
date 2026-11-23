import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.CarrierEnergyPf
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.HermitianZZEqNeg

noncomputable section

open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S
open scoped InnerProductSpace ComplexConjugate ENNReal

namespace Formalism.L2.SG.Pf.Carrier.EnergyPfLoc

open Formalism.L2.SG.RealObj Formalism.L2.SG.RealObj.EnergyCut Formalism.L2.SG.Pf.Carrier Formalism.L2.SG.Pf.Carrier.EnergyPf
open Formalism.L2.SG.HidaSetting

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Gram

variable {α V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]

theorem inner_lc (f g : α → V) (h : ∀ a b, ⟪f a, f b⟫_ℂ = ⟪g a, g b⟫_ℂ) (c d : α →₀ ℂ) :
    ⟪Finsupp.linearCombination ℂ f c, Finsupp.linearCombination ℂ f d⟫_ℂ =
      ⟪Finsupp.linearCombination ℂ g c, Finsupp.linearCombination ℂ g d⟫_ℂ := by
  simp only [Finsupp.linearCombination_apply, Finsupp.sum, sum_inner, inner_sum,
    inner_smul_left, inner_smul_right, h]

theorem norm_lc (f g : α → V) (h : ∀ a b, ⟪f a, f b⟫_ℂ = ⟪g a, g b⟫_ℂ) (c : α →₀ ℂ) :
    ‖Finsupp.linearCombination ℂ f c‖ = ‖Finsupp.linearCombination ℂ g c‖ := by
  have hsq : ‖Finsupp.linearCombination ℂ f c‖ ^ 2 = ‖Finsupp.linearCombination ℂ g c‖ ^ 2 := by
    rw [@norm_sq_eq_re_inner ℂ, @norm_sq_eq_re_inner ℂ, inner_lc f g h c c]
  have := congrArg Real.sqrt hsq
  simpa [Real.sqrt_sq (norm_nonneg _)] using this

theorem exists_linearIsometryEquiv_of_inner_eq (f g : α → V) (h : ∀ a b, ⟪f a, f b⟫_ℂ = ⟪g a, g b⟫_ℂ) :
    ∃ U : V ≃ₗᵢ[ℂ] V, ∀ a, U (f a) = g a := by
  classical
  set F := Finsupp.linearCombination ℂ f with hF
  set G := Finsupp.linearCombination ℂ g with hG
  have hker : LinearMap.ker F ≤ LinearMap.ker G := by
    intro c hc
    rw [LinearMap.mem_ker] at hc ⊢
    have := norm_lc f g h c
    rw [← hF, ← hG, hc, norm_zero] at this
    exact norm_eq_zero.1 this.symm
  let φ : LinearMap.range F →ₗ[ℂ] V :=
    ((LinearMap.ker F).liftQ G hker).comp F.quotKerEquivRange.symm.toLinearMap
  have hφ : ∀ c, φ ⟨F c, LinearMap.mem_range_self F c⟩ = G c := by
    intro c
    simp only [φ, LinearMap.comp_apply, LinearEquiv.coe_coe,
      LinearMap.quotKerEquivRange_symm_apply_image, Submodule.mkQ_apply, Submodule.liftQ_apply]
  have hφn : ∀ x, ‖φ x‖ = ‖x‖ := by
    rintro ⟨_, c, rfl⟩
    rw [hφ c]
    show ‖G c‖ = ‖F c‖
    exact (norm_lc f g h c).symm
  let L : LinearMap.range F →ₗᵢ[ℂ] V := { φ with norm_map' := hφn }
  refine ⟨L.extend.toLinearIsometryEquiv rfl, fun a => ?_⟩
  have hfa : f a ∈ LinearMap.range F := ⟨Finsupp.single a 1, by simp [hF]⟩
  have e1 : (L.extend.toLinearIsometryEquiv rfl) (f a) = L.extend (f a) := rfl
  rw [e1, show f a = ((⟨f a, hfa⟩ : LinearMap.range F) : V) from rfl, LinearIsometry.extend_apply]
  have e2 : (⟨f a, hfa⟩ : LinearMap.range F) =
      ⟨F (Finsupp.single a 1), LinearMap.mem_range_self F _⟩ := by
    ext; simp [hF]
  rw [e2]
  show φ _ = g a
  rw [hφ]
  simp [hG]

end Gram

section Loc

variable {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D)

theorem wu_ne (u : D.what₂.Word) : ∃ x0, X.Wu u x0 ≠ 0 := by
  by_contra hc
  push Not at hc
  have h1 := (X.Wu_spec u).2.2.2.2
  simp [hc] at h1

open Classical in
theorem inner_upd (u : D.what₂.Word) (v : InfinitePlace X.B.I.F) (x0 : X.B.I.Ginf)
    (y y' : Formalism.REAL.UJ (X.B.I.ε v)) :
    ⟪X.Wu u (Function.update x0 v y), X.Wu u (Function.update x0 v y')⟫_ℂ =
      ⟪X.Wloc u v y, X.Wloc u v y'⟫_ℂ * ∏ w ∈ Finset.univ.erase v, ⟪X.Wloc u w (x0 w), X.Wloc u w (x0 w)⟫_ℂ := by
  rw [X.Wu_tens, X.Wu_tens, X.tensU_inner, ← Finset.mul_prod_erase _ _ (Finset.mem_univ v)]
  simp only [Function.update_self]
  congr 1
  refine Finset.prod_congr rfl fun w hw => ?_
  rw [Function.update_of_ne (Finset.ne_of_mem_erase hw), Function.update_of_ne (Finset.ne_of_mem_erase hw)]

open Classical in

theorem wloc_gram (u : D.what₂.Word) (v : InfinitePlace X.B.I.F) (s : Formalism.REAL.UJ (X.B.I.ε v))
    (hs : InS (fun a => rv X.B.I v (X.eR a)) (rv X.B.I v (X.zR u)) (uMat s)) (a b : Formalism.REAL.UJ (X.B.I.ε v)) :
    ⟪X.Wloc u v (s * a), X.Wloc u v (s * b)⟫_ℂ = ⟪X.Wloc u v a, X.Wloc u v b⟫_ℂ := by
  obtain ⟨x0, hx0⟩ := wu_ne X u
  set S : X.B.I.Ginf := Function.update 1 v s with hSdef
  have hS : S ∈ X.SinfU u := by
    intro w
    by_cases hw : w = v
    · subst hw
      simpa [S] using hs
    · simp only [S, Function.update_of_ne hw, Pi.one_apply]
      refine ⟨fun a => ?_, ?_⟩ <;> simp [uMat]
  have hmul : ∀ y, S * Function.update x0 v y = Function.update x0 v (s * y) := by
    intro y
    funext w
    by_cases hw : w = v
    · subst hw
      simp [S]
    · simp [S, Function.update_of_ne hw]
  have hW : ∀ x, X.Wu u (S * x) = X.psiInfU u S • X.piU u S (X.Wu u x) := fun x => (X.Wu_spec u).1 S hS x
  have hU : ∀ x y, ⟪X.piU u S x, X.piU u S y⟫_ℂ = ⟪x, y⟫_ℂ := (X.piU_rep u).2.2.1 S hS
  have hψ : conj (X.psiInfU u S) * X.psiInfU u S = 1 := by
    rw [Complex.conj_mul', Formalism.L2.SG.RealObj.InfCut.norm_psiInfU X u S]
    simp
  have key : ∀ y y', ⟪X.Wu u (S * Function.update x0 v y), X.Wu u (S * Function.update x0 v y')⟫_ℂ =
      ⟪X.Wu u (Function.update x0 v y), X.Wu u (Function.update x0 v y')⟫_ℂ := by
    intro y y'
    rw [hW, hW, inner_smul_left, inner_smul_right, hU, ← mul_assoc, hψ, one_mul]
  have hK : (∏ w ∈ Finset.univ.erase v, ⟪X.Wloc u w (x0 w), X.Wloc u w (x0 w)⟫_ℂ) ≠ 0 := by
    have h0 := inner_upd X u v x0 (x0 v) (x0 v)
    rw [Function.update_eq_self] at h0
    have hne : ⟪X.Wu u x0, X.Wu u x0⟫_ℂ ≠ 0 := inner_self_ne_zero.2 hx0
    rw [h0] at hne
    exact right_ne_zero_of_mul hne
  have h2 := key a b
  rw [hmul, hmul, inner_upd, inner_upd] at h2
  exact mul_right_cancel₀ hK h2

theorem wloc_unit (u : D.what₂.Word) (v : InfinitePlace X.B.I.F) (s : Formalism.REAL.UJ (X.B.I.ε v))
    (hs : InS (fun a => rv X.B.I v (X.eR a)) (rv X.B.I v (X.zR u)) (uMat s)) :
    ∃ A : X.Vloc u v ≃ₗᵢ[ℂ] X.Vloc u v, ∀ x, X.Wloc u v (s * x) = (1 : ℂ) • A (X.Wloc u v x) := by
  obtain ⟨A, hA⟩ := exists_linearIsometryEquiv_of_inner_eq (fun x => X.Wloc u v x) (fun x => X.Wloc u v (s * x))
    (fun a b => (wloc_gram X u v s hs a b).symm)
  exact ⟨A, fun x => by rw [one_smul, hA x]⟩

theorem hilbertSchmidt_sq_nonneg {V V' : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    [NormedAddCommGroup V'] [InnerProductSpace ℂ V'] [FiniteDimensional ℂ V'] (A : V' →L[ℂ] V) : 0 ≤ hs2 A := by
  unfold Formalism.L2.SG.RealObj.hs2
  exact Finset.sum_nonneg fun i _ => sq_nonneg _

theorem hilbertSchmidt_double_coset_invariant (u u' : D.what₂.Word) (v : InfinitePlace X.B.I.F) (g s s' : Formalism.REAL.UJ (X.B.I.ε v))
    (hs : InS (fun a => rv X.B.I v (X.eR a)) (rv X.B.I v (X.zR u)) (uMat s))
    (hs' : InS (fun a => rv X.B.I v (X.eR a)) (rv X.B.I v (X.zR u')) (uMat s')) :
    hs2 (JvX X u u' v (s * g * s'⁻¹)) = hs2 (JvX X u u' v g) := by
  haveI := FiniteDimensional.complete ℂ (X.Vloc u v)
  haveI := FiniteDimensional.complete ℂ (X.Vloc u' v)
  obtain ⟨A, hA⟩ := wloc_unit X u v s hs
  obtain ⟨B, hB⟩ := wloc_unit X u' v s' hs'
  unfold JvX Formalism.L2.SG.RealObj.Jv
  rw [Formalism.L2.SG.RealObj.InfCut.OO_equiv (Formalism.REAL.muG (X.B.I.ε v)) (X.Wloc u v) (X.Wloc u' v) g s s' 1 1 A B hA hB,
    Formalism.L2.SG.RealObj.InfCut.hilbert_schmidt_smul, Formalism.L2.SG.RealObj.InfCut.hilbert_schmidt_comp_left _ _ (fun x => A.norm_map x),
    Formalism.L2.SG.RealObj.InfCut.hilbert_schmidt_comp_right]
  simp

theorem jvX_meas (u u' : D.what₂.Word) (v : InfinitePlace X.B.I.F) :
    Measurable (fun g => hs2 (JvX X u u' v g)) := by
  haveI := FiniteDimensional.complete ℂ (X.Vloc u v)
  have hF : Continuous (fun p : Formalism.REAL.UJ (X.B.I.ε v) × Formalism.REAL.UJ (X.B.I.ε v) =>
      Formalism.L2.SG.TermOp.rk1 (X.Wloc u v p.2) (X.Wloc u' v (p.1⁻¹ * p.2))) :=
    Formalism.L2.SG.RealObj.RankOneTensors.continuous_rankOneOperator ((X.Wloc_cont u v).comp continuous_snd)
      ((X.Wloc_cont u' v).comp ((continuous_fst.inv).mul continuous_snd))
  have hJ : StronglyMeasurable (fun g => JvX X u u' v g) := by
    have := hF.stronglyMeasurable.integral_prod_right' (ν := Formalism.REAL.muG (X.B.I.ε v))
    unfold JvX Formalism.L2.SG.RealObj.Jv Formalism.L2.SG.TermOp.OO
    simpa [Measure.restrict_univ] using this
  have hc : Continuous (fun A : X.Vloc u' v →L[ℂ] X.Vloc u v => hs2 A) := by
    unfold hs2
    exact continuous_finsetSum _ fun i _ =>
      ((ContinuousLinearMap.apply ℂ (X.Vloc u v) (stdOrthonormalBasis ℂ (X.Vloc u' v) i)).continuous.norm.pow 2)
  exact hc.measurable.comp hJ.measurable

end Loc

def StepSecX : Prop :=
  ∀ (D : D7) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (u u' : D.what₂.Word) (v : InfinitePlace X.B.I.F),
    ∃ h : (Fin (D.R.rS + 1) → ℂ) → Formalism.REAL.UJ (X.B.I.ε v), Measurable h ∧
      ∀ cv ∈ GoodV (D := D) u u', Zhat (X.B.I.ε v) (frm X u 1 v) (frm X u' 1 v) (uMat (h cv)) = Matrix.diagonal cv

theorem locRep_of_sec (hS : StepSecX) {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (u u' : D.what₂.Word) :
    ∃ L, LocRep X u u' L := by
  classical
  choose h hm hsec using hS D X u u'
  refine ⟨fun v cv => hs2 (JvX X u u' v (h v cv)),
    ⟨fun v => ⟨(jvX_meas X u u' v).comp (hm v), fun cv => hilbertSchmidt_sq_nonneg _⟩, ?_⟩⟩
  intro c hc v
  have hex : ∃ γ, HasDiag X u u' 1 c γ := ⟨fun w => h w (c w), fun w => hsec w (c w) (hc w)⟩
  have hh : HasDiag X u u' 1 c (hOf X u u' 1 c) := by
    unfold hOf; rw [dif_pos hex]; exact hex.choose_spec
  have hee : ∀ a b, hJ (X.B.I.ε v) (rv X.B.I v (X.eR a)) (rv X.B.I v (X.eR b)) = 0 := fun a b => by
    rw [show X.eR a = X.crd (X.eX a) from rfl, show X.eR b = X.crd (X.eX b) from rfl,
      Formalism.L2.SG.RealObj.InfCut.UnitaryIsometries.hJ_rvX, X.ee, map_zero]
  have hez : ∀ (w : D.what₂.Word) a, hJ (X.B.I.ε v) (rv X.B.I v (X.eR a)) (rv X.B.I v (X.zR w)) = 0 :=
    fun w a => by
      rw [show X.eR a = X.crd (X.eX a) from rfl, show X.zR w = X.crd (X.zu w) from rfl,
        Formalism.L2.SG.RealObj.InfCut.UnitaryIsometries.hJ_rvX, (X.zu_orth w a).1, map_zero]
  obtain ⟨s, s', hs, hs', heq⟩ := Formalism.L2.SG.RealObj.InfCut.UnitaryIsometries.diagDC_pair (X.B.I.ε v) 1 _ _ _ (Tw u) (Tw u')
    hee (hez u) (hez u') (Formalism.L2.SG.RealObj.InfCut.UnitaryIsometries.hermitian_z_z_eq_neg X v u) (Formalism.L2.SG.RealObj.InfCut.UnitaryIsometries.hermitian_z_z_eq_neg X v u')
    (c v) (hc v).1 (hc v).2 (h v (c v)) ((hOf X u u' 1 c) v) (hsec v (c v) (hc v)) (hh v)
  show hs2 (JvX X u u' v ((hOf X u u' 1 c) v)) = hs2 (JvX X u u' v (h v (c v)))
  rw [heq]
  exact hilbertSchmidt_double_coset_invariant X u u' v _ s s' hs hs'

end Formalism.L2.SG.Pf.Carrier.EnergyPfLoc
