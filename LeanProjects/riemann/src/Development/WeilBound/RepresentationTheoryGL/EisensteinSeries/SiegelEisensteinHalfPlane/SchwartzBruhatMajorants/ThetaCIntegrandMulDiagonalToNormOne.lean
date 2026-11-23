import Mathlib
import Development.WeilBound.CoreStatements.AutomorphicKernels.EisensteinSeriesG2.HeisenbergTheta.HeisenbergThetaConstant.ThetaC
import Development.WeilBound.RepresentationTheoryGL.EisensteinSeries.SiegelEisensteinHalfPlane.SchwartzBruhatMajorants.ThetaCScalCEq

open NumberField Matrix MeasureTheory Filter Topology
open scoped NumberField.AdeleRing
open PositivityTheory.He2M1 GroundTheory.Global GroundTheory.Automorphic GroundTheory.Automorphic.GJMatrix IdeleGroup PositivityTheory.RgEis

namespace GlobalTheory.CompanionTheory.AdelicThetaSeries.Hd

variable {k : Type} [Field k] [NumberField k] {ι : Type} [Fintype ι] [DecidableEq ι]

theorem thetaC_scalC_diagonal_mul (F : (ι → 𝔸[k]) → ℂ) (δ : kˣ) (a : IdeleGroup k) :
    thetaC F (scalC (diagonal k δ * a)) = thetaC F (scalC a) := by
  unfold thetaC
  have hv : ∀ ξ : ι → k, ((scalC (IdeleGroup.diagonal k δ * a) : GL ι 𝔸[k]) : Matrix ι ι 𝔸[k]) *ᵥ ratV ξ
      = ((scalC a : GL ι 𝔸[k]) : Matrix ι ι 𝔸[k]) *ᵥ ratV (δ • ξ) := by
    intro ξ
    funext i
    simp [scalC, ratV, Matrix.mulVec, dotProduct, Matrix.diagonal_apply, IdeleGroup.diagonal,
      Units.smul_def, mul_comm, mul_left_comm]
  simp_rw [hv]
  exact (MulAction.toPerm δ).tsum_eq (fun ξ => F (((scalC a : GL ι 𝔸[k]) : Matrix ι ι 𝔸[k]) *ᵥ ratV ξ))

noncomputable def thetaCIntegrand (w : InfinitePlace k) (F : (ι → 𝔸[k]) → ℂ)
    (ω : HeckeCharacter k) (t : {r : ℝ // 0 < r}) (u : normOneSubgroup k) : ℂ :=
  thetaC F (scalC (moduleSection w t * (u : IdeleGroup k))) * (ω.toIdele (u : IdeleGroup k) : ℂ)

theorem thetaCIntegrand_mul_diagonalToNormOne (w : InfinitePlace k) (F : (ι → 𝔸[k]) → ℂ)
    (ω : HeckeCharacter k) (t : {r : ℝ // 0 < r}) (ξ : kˣ) (u : normOneSubgroup k) :
    thetaCIntegrand w F ω t (u * diagonalToNormOne k ξ) = thetaCIntegrand w F ω t u := by
  unfold thetaCIntegrand
  have hc : ((u * diagonalToNormOne k ξ : normOneSubgroup k) : IdeleGroup k) =
      IdeleGroup.diagonal k ξ * (u : IdeleGroup k) := by
    rw [Subgroup.coe_mul, mul_comm]
    rfl
  rw [hc, ← mul_assoc, mul_comm (moduleSection w t), mul_assoc, thetaC_scalC_diagonal_mul, map_mul,
    HeckeCharacter.toIdele_diagonal, one_mul]

theorem thetaCIntegrand_inv (w : InfinitePlace k) {F : (ι → 𝔸[k]) → ℂ}
    (hF : F ∈ schwartzBruhatPi k ι) (ω : HeckeCharacter k) (t : {r : ℝ // 0 < r})
    (u : normOneSubgroup k) :
    thetaCIntegrand w F ω t⁻¹ u =
      ((t : ℝ) : ℂ) ^ Fintype.card ι * thetaCIntegrand w (adelicFourierPi k F) ω⁻¹ t u⁻¹ := by
  unfold thetaCIntegrand
  rw [EpsteinRankN.Hd.thetaC_scalC_eq hF]
  have e1 : (moduleSection w t⁻¹ * (u : IdeleGroup k))⁻¹ =
      moduleSection w t * ((u⁻¹ : normOneSubgroup k) : IdeleGroup k) := by
    rw [map_inv, mul_inv, inv_inv, Subgroup.coe_inv, mul_comm]
  have e2 : ideleModule k (moduleSection w t⁻¹ * (u : IdeleGroup k)) = t⁻¹ := by
    rw [map_mul, ideleModule_moduleSection, MonoidHom.mem_ker.mp u.2, mul_one]
  have e3 : (((ω⁻¹).toIdele ((u⁻¹ : normOneSubgroup k) : IdeleGroup k) : ℂ)) =
      ((ω.toIdele (u : IdeleGroup k) : ℂ)) := by
    have h : ∀ x, (ω⁻¹) x = (ω x)⁻¹ := fun x => rfl
    simp [HeckeCharacter.toIdele, h]
  rw [e1, e2, e3]
  have e4 : ((t⁻¹ : {r : ℝ // 0 < r}) : ℝ) = (t : ℝ)⁻¹ := by simp
  rw [e4]
  push_cast
  rw [inv_pow, inv_inv]
  ring

theorem theta_integral_functional_equation (w : InfinitePlace k) {F : (ι → 𝔸[k]) → ℂ}
    (hF : F ∈ schwartzBruhatPi k ι) (ω : HeckeCharacter k) (t : {r : ℝ // 0 < r}) :
    thetaCInt w F ω t⁻¹ =
      ((t : ℝ) : ℂ) ^ Fintype.card ι * thetaCInt w (adelicFourierPi k F) ω⁻¹ t := by
  have hD := isFundamentalDomain_normOneFundamentalDomain k (normOneMeasure k)
  have hDinv : IsFundamentalDomain (↥(diagonalNormOne k).op)
      ((fun x => x⁻¹) ⁻¹' normOneFundamentalDomain k) (normOneMeasure k) := by
    refine hD.preimage_of_equiv
      (Measure.measurePreserving_inv (normOneMeasure k)).quasiMeasurePreserving
      inv_involutive.bijective (fun g x => ?_)
    show (g⁻¹ • x)⁻¹ = g • x⁻¹
    rw [Subgroup.smul_def, Subgroup.smul_def, MulOpposite.smul_eq_mul_unop,
      MulOpposite.smul_eq_mul_unop, Subgroup.coe_inv, MulOpposite.unop_inv, _root_.mul_inv_rev,
      inv_inv]
    exact mul_comm _ _
  have hinvar : ∀ (g : ↥(diagonalNormOne k).op) (x : normOneSubgroup k),
      thetaCIntegrand w (adelicFourierPi k F) ω⁻¹ t (g • x) =
        thetaCIntegrand w (adelicFourierPi k F) ω⁻¹ t x := by
    intro g x
    have hm : MulOpposite.unop (g : (normOneSubgroup k)ᵐᵒᵖ) ∈ diagonalNormOne k := g.2
    obtain ⟨ξ, hξ⟩ := MonoidHom.mem_range.mp (Subgroup.mem_subgroupOf.mp hm)
    have hg : MulOpposite.unop (g : (normOneSubgroup k)ᵐᵒᵖ) = diagonalToNormOne k ξ :=
      Subtype.ext hξ.symm
    rw [Subgroup.smul_def, MulOpposite.smul_eq_mul_unop, hg, thetaCIntegrand_mul_diagonalToNormOne]
  have hms := measurableSet_normOneFundamentalDomain (K := k)
  have step1 : thetaCInt w F ω t⁻¹ = ((t : ℝ) : ℂ) ^ Fintype.card ι *
      ∫ u in normOneFundamentalDomain k,
        thetaCIntegrand w (adelicFourierPi k F) ω⁻¹ t u⁻¹ ∂normOneMeasure k := by
    show ∫ u in normOneFundamentalDomain k, thetaCIntegrand w F ω t⁻¹ u ∂normOneMeasure k = _
    rw [← integral_const_mul]
    refine setIntegral_congr_fun hms (fun u _ => ?_)
    exact thetaCIntegrand_inv w hF ω t u
  have step2 : ∫ u in normOneFundamentalDomain k,
        thetaCIntegrand w (adelicFourierPi k F) ω⁻¹ t u⁻¹ ∂normOneMeasure k =
      ∫ u in (fun x => x⁻¹) ⁻¹' normOneFundamentalDomain k,
        thetaCIntegrand w (adelicFourierPi k F) ω⁻¹ t u ∂normOneMeasure k := by
    rw [← integral_indicator hms, ← integral_indicator (hms.preimage measurable_inv),
      ← integral_inv_eq_self (fun u => ((fun x => x⁻¹) ⁻¹' normOneFundamentalDomain k).indicator
        (thetaCIntegrand w (adelicFourierPi k F) ω⁻¹ t) u) (normOneMeasure k)]
    congr 1
  rw [step1, step2, hDinv.setIntegral_eq hD hinvar]
  rfl

theorem thetaCInt_inv : ∀ {k : Type} [Field k] [NumberField k], ∀ {ι : Type} [Fintype ι]
    [DecidableEq ι], ∀ (w : InfinitePlace k) {F : (ι → 𝔸[k]) → ℂ} (hF : F ∈ schwartzBruhatPi k ι)
    (ω : HeckeCharacter k) (t : {r : ℝ // 0 < r}), thetaCInt w F ω t⁻¹ =
      ((t : ℝ) : ℂ) ^ Fintype.card ι * thetaCInt w (adelicFourierPi k F) ω⁻¹ t :=
  fun w _ hF ω t ↦ theta_integral_functional_equation w hF ω t

end GlobalTheory.CompanionTheory.AdelicThetaSeries.Hd
