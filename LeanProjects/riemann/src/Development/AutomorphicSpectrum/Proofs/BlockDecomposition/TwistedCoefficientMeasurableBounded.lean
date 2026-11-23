import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.KFiniteVectors.KFiniteThetaLifts.PureThetaTransfer.ConstantTermModerateGrowth
open NumberField IsDedekindDomain MeasureTheory GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic Ad3 Ad3.K Ad3.K.QuadraticBaseChangeGL3 Ad3.K.QuadraticBaseChangeGL3.Th
open GroundTheory.Automorphic.GodementSection (localChar)
open GroundTheory.Automorphic.Reduction (finAt infAt maxCompact)
open GroundTheory.Automorphic.GLnLocal (integralGL)
open Ad3.R (G2 Jd md KA LInv IsLoc2 pt pri dia2)
open scoped NumberField.AdeleRing ValuativeRel

open GroundTheory.Global.AdicLiesOver

namespace GlobalTheory.CompanionTheory.CtMeas

theorem norm_cAt {K : Type} [Field K] [NumberField K] (c : HeckeCharacter K) (v : Pl) (w : PlK K)
    [w.asIdeal.LiesOver v.asIdeal] (u : (Qv v)ˣ) : ‖((cAt c v w u : ℂˣ) : ℂ)‖ = 1 := by
  change ‖((localChar c w (Units.map (algebraMap (Qv v) (Kv K w) : Qv v →* Kv K w) u) : ℂˣ) : ℂ)‖ = 1
  rw [GroundTheory.Automorphic.GodementSection.coe_localChar]
  exact Circle.norm_coe _

theorem continuous_cAt {K : Type} [Field K] [NumberField K] (c : HeckeCharacter K) (v : Pl) (w : PlK K)
    [w.asIdeal.LiesOver v.asIdeal] : Continuous (cAt c v w) :=
  (GroundTheory.Automorphic.GodementSection.continuous_localChar c w).comp
    (Continuous.units_map _ (_root_.continuous_algebraMap (Qv v) (Kv K w)))

theorem continuous_ct {K : Type} [Field K] [NumberField K] {c : HeckeCharacter K} {v : Pl} (D : LM c v) :
    Continuous D.ct := by
  cases D with
  | @sp w₁ w₂ h₁ h₂ Φ =>
    exact Units.continuous_val.comp ((continuous_cAt c v w₁).mul (continuous_cAt c v w₂).inv)
  | @ns w h σ η Φ => exact continuous_const

theorem norm_ct {K : Type} [Field K] [NumberField K] {c : HeckeCharacter K} {v : Pl} (D : LM c v)
    (u : (Qv v)ˣ) : ‖D.ct u‖ = 1 := by
  cases D with
  | @sp w₁ w₂ h₁ h₂ Φ =>
    change ‖((cAt c v w₁ u * (cAt c v w₂ u)⁻¹ : ℂˣ) : ℂ)‖ = 1
    rw [Units.val_mul, Units.val_inv_eq_inv_val, norm_mul, norm_inv, norm_cAt, norm_cAt]
    simp
  | @ns w h σ η Φ =>
    change ‖(1 : ℂ)‖ = 1
    simp

theorem measurable_ct_tu {K : Type} [Field K] [NumberField K] {c : HeckeCharacter K} {v : Pl} (D : LM c v)
    (Sv : Finset Pl) (m : Pl →₀ ℤ) : Measurable (fun u => D.ct (tu Sv m u v)) := by
  by_cases h : v ∈ Sv
  · have e : (fun u => D.ct (tu Sv m u v)) =
        (fun x : (Qv v)ˣ => D.ct (unifUnit (Qv v) ^ (m v) * x)) ∘ (fun u : ∀ v : Sv, (Qv v.1)ˣ => u ⟨v, h⟩) := by
      funext u
      simp [tu, h]
    rw [e]
    exact ((continuous_ct D).comp (continuous_const.mul continuous_id)).measurable.comp
      (measurable_pi_apply _)
  · have e : (fun u => D.ct (tu Sv m u v)) = fun _ => D.ct (unifUnit (Qv v) ^ (m v)) := by
      funext u
      simp [tu, h]
    rw [e]
    exact measurable_const

theorem measurable_ctM_norm_le : ∀ (K : Type) [Field K] [NumberField K] (c : HeckeCharacter K) (M : ∀ v : Pl, LM c v) (Sv : Finset Pl) (m : Pl →₀ ℤ),
  Measurable (fun u => ctM M Sv m u) ∧ ∀ u, ‖ctM M Sv m u‖ ≤ 1 := by
  intro K _ _ c M Sv m
  refine ⟨?_, fun u => ?_⟩
  · unfold ctM
    exact Finset.measurable_fun_prod _ fun v _ => measurable_ct_tu (M v) Sv m
  · unfold ctM
    rw [norm_prod]
    simp [norm_ct]

end GlobalTheory.CompanionTheory.CtMeas
