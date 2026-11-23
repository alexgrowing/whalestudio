import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousPhaseAt
import Development.AbelianVarietyTheory.Proofs.HeightProofs.IsFundamentalDomainOfHaar
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsIntEqExponentAddHalfIndex
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsEtaTildeUnramified
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SplittingHeckeCharExistsArchimedeanExponent
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsInverseChart

open NumberField MeasureTheory
open scoped Classical
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum
open Formalism.MainNotions.TaylorLogMetric (VC embT tor0 Hf lamOf area Th U)
open Formalism.MainNotions.StandardLatticesGL3 (WeilO HeckeU TT stdL pt oddE0)
open GlobalTheory.NormExact

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.HeckeSignEta

theorem idF_ratF (D : D7) (a : D.host.Fˣ) :
    idF D (Units.map (algebraMap D.host.F (AF D.host.F)).toMonoidHom a) =
      Units.map (incA D).toMonoidHom (Units.map (algebraMap D.host.F D.host.E).toMonoidHom a) := by
  refine Units.ext ?_
  show algebraMap (AF D.host.F) (AE D) (algebraMap D.host.F (AF D.host.F) (a : D.host.F)) =
    incA D (algebraMap D.host.F D.host.E (a : D.host.F))
  show _ = Algebra.TensorProduct.includeRight (algebraMap D.host.F D.host.E (a : D.host.F))
  rw [AlgHom.commutes, IsScalarTower.algebraMap_apply D.host.F (AF D.host.F) (AE D)]

theorem resEta_of_sign : ∀ (D : D7) (χ : (AE D)ˣ →* Circle) (N : ℕ), IsHeckeChar D χ →
    (∀ x y : (AE D)ˣ, (y : AE D) = x * cA D x → χ y = 1) →
    ∀ θ : InfFam D, IsInfFam θ →
    (∀ (τ : D.what₂.Tau) (x : (AE D)ˣ), finPart D (x : AE D) = 1 → θ τ (infPart D (x : AE D)) = -1 →
      (∀ τ', τ' ≠ τ → θ τ' (infPart D (x : AE D)) = 1) → ((χ x : Circle) : ℂ) = (-1) ^ N) →
    ResEta D χ N := by
  intro D χ N hχ hnorm θ hθ hsign
  refine ⟨GlobalTheory.VolHeckeCompare.exists_isEta D, fun ε hε => ?_⟩

  set ψ : (AF D.host.F)ˣ →* Circle := χ.comp (idF D) * (ε ^ N)⁻¹ with hψ
  have hψa : ∀ a, ψ a = χ (idF D a) * (ε a ^ N)⁻¹ := fun a => rfl
  have hker : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryVolumePairs.normGroup D ≤ ψ.ker := by
    rw [GlobalTheory.VolHeckeCompare.normGroup_eq]
    refine sup_le ?_ ?_
    · rintro _ ⟨a, rfl⟩
      show ψ (Units.map (algebraMap D.host.F (AF D.host.F)).toMonoidHom a) = 1
      rw [hψa, idF_ratF, hχ.2, hε.2.1 a, one_pow, inv_one, mul_one]
    · rintro _ ⟨x, rfl⟩
      obtain ⟨-, -, hN, -⟩ := GlobalTheory.VolHeckeCompare.exists_form D
      have e : (idF D (GlobalTheory.VolHeckeCompare.normU D x) : AE D) = (x : AE D) * cA D (x : AE D) := by
        have e0 : idF D (GlobalTheory.VolHeckeCompare.normU D x) = GlobalTheory.IndefiniteRowSideFullHecke.UnitaryVolumePairs.normId D x := hN x
        rw [e0]; rfl
      show ψ (GlobalTheory.VolHeckeCompare.normU D x) = 1
      rw [hψa, hnorm x _ e, hε.2.2.1 x, one_pow, inv_one, mul_one]

  obtain ⟨τ⟩ : Nonempty D.what₂.Tau := ⟨D.eTau.symm (Classical.arbitrary _)⟩
  obtain ⟨η, -, -, hη1, hη2⟩ := GlobalTheory.WeilParts.exists_isEtaTilde_unramified D
  obtain ⟨N1, hN1, -, hηx⟩ := hη2 τ
  obtain ⟨σ, h⟩ := GlobalTheory.RealLineAt.exists_inverse_chart hθ
  obtain ⟨e, -, e1, e2⟩ := GlobalTheory.SplitCharExp.exists_real_hom h
  set w : D.what₂.Tau → ℂ := Pi.mulSingle τ (-1) with hw
  have wτ : w τ = -1 := by simp [w]
  have wo : ∀ τ', τ' ≠ τ → w τ' = 1 := fun τ' ht => by simp [w, Pi.mulSingle_eq_of_ne ht]
  have ww : w * w = 1 := by
    funext τ'
    by_cases ht : τ' = τ
    · subst ht; simp [wτ]
    · simp [wo τ' ht]
  let x : (AE D)ˣ := ⟨e w, e w, by rw [← map_mul, ww, map_one], by rw [← map_mul, ww, map_one]⟩
  have x1 : finPart D (x : AE D) = 1 := e1 w
  have x2 : ∀ τ', θ τ' (infPart D (x : AE D)) = w τ' := e2 w
  have xτ : θ τ (infPart D (x : AE D)) = -1 := by rw [x2, wτ]
  have xo : ∀ τ', τ' ≠ τ → θ τ' (infPart D (x : AE D)) = 1 := fun τ' ht => by rw [x2, wo τ' ht]
  have hcx : ((χ x : Circle) : ℂ) = (-1 : ℂ) ^ N := hsign τ x x1 xτ xo
  have hN1' : N1 = 1 := by
    have : (N1 : ℚ) = 1 := by rw [hN1]; norm_num
    exact_mod_cast this
  have hηc : ((η x : Circle) : ℂ) = -1 := by rw [hηx θ hθ x x1 xo, xτ, hN1']; simp
  have hfix : cA D (x : AE D) = x := by
    refine GlobalTheory.SplitCharExp.ext_of_chart h ?_ fun τ' => ?_
    · have e3 : finPart D (cA D (x : AE D)) = sigR (Af D.host.F) D.sp.cm.sig (finPart D (x : AE D)) :=
        GlobalTheory.FockCompare.LiftUnitary.snd_sigR D.sp.cm.sig (x : AE D)
      rw [e3, x1, RingHom.map_one]
    · rw [GlobalTheory.FockCompare.comp_cA hθ, x2]
      by_cases ht : τ' = τ
      · rw [ht, wτ]; simp
      · rw [wo τ' ht]; simp
  obtain ⟨y, hy⟩ := GlobalTheory.SplitParity.exists_idF_of_fixed D x hfix

  have hneg : ∀ ε', IsEta D ε' → ((ε' y : Circle) : ℂ) = -1 := fun ε' hε' => by
    have c2 := hη1.2 ε' hε' y
    rw [hy, pow_one] at c2
    rw [← c2, hηc]
  have hψy : ψ y = 1 := by
    refine Circle.ext ?_
    rw [hψa, hy, Circle.coe_mul, Circle.coe_inv, Circle.coe_pow, hcx, hneg ε hε, Circle.coe_one]
    exact mul_inv_cancel₀ (pow_ne_zero _ (by norm_num))
  have hψ1 : ψ = 1 := by
    by_contra hne
    have hψE : IsEta D ψ := (GlobalTheory.VolHeckeCompare.isEta_iff_normGroup D ψ).2 ⟨hker, hne⟩
    have := hneg ψ hψE
    rw [hψy, Circle.coe_one] at this
    norm_num at this
  intro a
  have ha : ψ a = 1 := by rw [hψ1]; rfl
  rw [hψa, mul_inv_eq_one] at ha
  exact ha

end GlobalTheory.HeckeSignEta
