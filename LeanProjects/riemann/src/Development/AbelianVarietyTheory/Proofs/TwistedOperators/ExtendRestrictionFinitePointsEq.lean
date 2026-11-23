import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ConjScalarAtOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ReadingsExistRow
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.RealLowestKTypeCoeffSquareIntegrable
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLinearSection
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.NormLiftFormsFiniteGroupAction
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.AdelicLiftDatumOfConjugateLiftDatumStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsMultIPOfModel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLinearLift
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormOfClassSums
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.SqNormIntegralFundamentalDomainEqL2NormSq
open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.AdelicRestrict

theorem ext_restrict {D : D7} {V : HSp D} (c : CoefA V) (hc : c.Is) (β : GL (Fin V.rank) (Lev.EAf D))
    (L : LevDat D.host.E ℂ V.rank) (Ψ : GA D V → c.W)
    (hΨ : ∀ γ ∈ GQ V, ∀ k, Lev.finE V k ∈ lev D.sp.cm V.gram β L → ∀ h,
      Ψ (γ * h * k) = Lev.levChi V β L k • c.ρ k⁻¹ (Ψ h)) (h : GA D V) :
    c.ext (fun u => Ψ (GlobalTheory.AdelicScalar.finLift V u)) h = Ψ h := by
  set h₀ := GlobalTheory.AdelicScalar.finLift V ((finHom V).rangeRestrict h) with eh₀
  have m₀ : h₀ ∈ GfC V := GlobalTheory.AdelicScalar.finLift_mem V _
  have s₀ : finHom V h₀ = finHom V h :=
    congrArg Subtype.val (GlobalTheory.AdelicScalar.finLift_spec V ((finHom V).rangeRestrict h))
  set k := h₀⁻¹ * h with ek
  have hk1 : finHom V k = 1 := by rw [ek, map_mul, map_inv, s₀, inv_mul_cancel]
  have hkE : Lev.finE V k = 1 := by
    unfold Lev.finE
    rw [MonoidHom.comp_apply, hk1, map_one]
  have hkL : Lev.finE V k ∈ lev D.sp.cm V.gram β L := by rw [hkE]; exact Subgroup.one_mem _
  have hχ : Lev.levChi V β L k = 1 := by
    unfold Lev.levChi
    rw [hkE]
    have := map_one (levChar D.sp.cm V.gram β L)
    have e : levFn β L 1 = (levChar D.sp.cm V.gram β L 1 : ℂˣ) := rfl
    rw [e, this]
    rfl
  have hlaw := hΨ 1 (Subgroup.one_mem _) k hkL h₀
  have eh : 1 * h₀ * k = h := by rw [ek, one_mul, mul_inv_cancel_left]
  rw [eh, hχ, one_smul] at hlaw
  change c.ρ h⁻¹ (Ψ (GlobalTheory.AdelicScalar.finLift V ((finHom V).rangeRestrict h))) = Ψ h
  rw [← eh₀, hlaw]
  have hρ : c.ρ h⁻¹ = c.ρ k⁻¹ := by
    rw [← eh, one_mul, _root_.mul_inv_rev, map_mul, hc.1 _ (inv_mem m₀), mul_one]
  rw [hρ]

end GlobalTheory.AdelicRestrict

end
