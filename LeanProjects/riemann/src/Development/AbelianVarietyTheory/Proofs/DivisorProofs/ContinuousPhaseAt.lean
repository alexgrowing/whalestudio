import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormPeriodSq
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsFiniteAdeleBaseChangeEquiv
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteAdelicPointUnitaryGroupGramOne
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DefiniteUnitaryClassSetFinite
import Development.AbelianVarietyTheory.Proofs.HeightProofs.IsTopologicalRingAE
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.LatHatOpenAndContinuous
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsIntEqExponentAddHalfIndex
import Development.AbelianVarietyTheory.Proofs.HeightProofs.IsFundamentalDomainOfHaar
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HeckeCharacterIdeleCharacterMatchUnique
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsArchEquivEq

open NumberField MeasureTheory
open scoped Classical
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum
open Formalism.MainNotions.TaylorLogMetric (VC embT tor0 Hf lamOf area Th U)
open Formalism.MainNotions.StandardLatticesGL3 (WeilO HeckeU TT stdL pt oddE0)
open GlobalTheory.NormSum (Pair Tup minorPol ratG intG Cls gam)
open GlobalTheory.NormDict GlobalTheory.NormExact
open GlobalTheory.BotFormula (IsFinPt)
open GlobalTheory.IndefiniteRowSideFullHecke.ClassFunctionSumIntegral (IsDefiniteSpace IsOpenCompactLevel)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.HeckeUChar

open IsDedekindDomain

variable {D : D7}

def finIdl (D : D7) : (AE D)ˣ →* (FiniteAdeleRing (𝓞 D.host.E) D.host.E)ˣ :=
  Units.map ((GlobalTheory.LFun.finAdEquiv D.host.F D.host.E).toRingHom.comp (finPart D)).toMonoidHom

def finY (D : D7) : (AE D)ˣ →* (Formalism.MainNotions.StandardLatticesGL3.AE D)ˣ :=
  (Units.map (GlobalTheory.BotFormula.toFinE D).symm.toRingHom.toMonoidHom).comp (finIdl D)

theorem coe_finIdl (x : (AE D)ˣ) : ((finIdl D x : (FiniteAdeleRing (𝓞 D.host.E) D.host.E)ˣ) :
    FiniteAdeleRing (𝓞 D.host.E) D.host.E) = GlobalTheory.LFun.finAdEquiv D.host.F D.host.E (finPart D (x : AE D)) := rfl

theorem coe_finY (x : (AE D)ˣ) : ((finY D x : (Formalism.MainNotions.StandardLatticesGL3.AE D)ˣ) : Formalism.MainNotions.StandardLatticesGL3.AE D) =
    (GlobalTheory.BotFormula.toFinE D).symm (GlobalTheory.LFun.finAdEquiv D.host.F D.host.E (finPart D (x : AE D))) := rfl

def finChar {N : ℕ} (c : HeckeU D N) : (AE D)ˣ →* Circle where
  toFun x := ⟨((c.f (finY D x) : ℂˣ) : ℂ), mem_sphere_zero_iff_norm.2 (c.unitary _)⟩
  map_one' := Circle.ext (by
    change ((c.f (finY D 1) : ℂˣ) : ℂ) = 1
    rw [map_one, map_one, Units.val_one])
  map_mul' x y := Circle.ext (by
    change ((c.f (finY D (x * y)) : ℂˣ) : ℂ) = ((c.f (finY D x) : ℂˣ) : ℂ) * ((c.f (finY D y) : ℂˣ) : ℂ)
    rw [map_mul, map_mul, Units.val_mul])

theorem coe_finChar {N : ℕ} (c : HeckeU D N) (x : (AE D)ˣ) :
    ((finChar c x : Circle) : ℂ) = ((c.f (finY D x) : ℂˣ) : ℂ) := rfl

def phaseAt (θ : InfFam D) (τ : D.what₂.Tau) : (AE D)ˣ →* Circle :=
  GlobalTheory.ChrEqUnique.phase.comp (Units.map ((θ τ).comp (infPart D)).toMonoidHom)

def infChar (θ : InfFam D) (n : D.what₂.Tau → ℤ) : (AE D)ˣ →* Circle := ∏ τ, phaseAt θ τ ^ n τ

theorem coe_infChar (θ : InfFam D) (n : D.what₂.Tau → ℤ) (x : (AE D)ˣ) :
    ((infChar θ n x : Circle) : ℂ) =
      ∏ τ, (θ τ (infPart D (x : AE D)) / (‖θ τ (infPart D (x : AE D))‖ : ℂ)) ^ n τ := by
  have h : ∀ s : Finset D.what₂.Tau, (((∏ τ ∈ s, phaseAt θ τ ^ n τ : (AE D)ˣ →* Circle) x : Circle) : ℂ) =
      ∏ τ ∈ s, ((phaseAt θ τ x : Circle) : ℂ) ^ n τ := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp
    | insert a s ha ih =>
      rw [Finset.prod_insert ha, Finset.prod_insert ha, MonoidHom.mul_apply, Circle.coe_mul, ih,
        MonoidHom.zpow_apply, Circle.coe_zpow]
  exact h Finset.univ

def chi {N : ℕ} (c : HeckeU D N) (θ : InfFam D) (e : ℤ) : (AE D)ˣ →* Circle := (finChar c * infChar θ c.n) ^ e

theorem continuous_phaseAt {θ : InfFam D} (hθ : IsInfFam θ) (τ : D.what₂.Tau) : Continuous (phaseAt θ τ) :=
  GlobalTheory.ChrEqUnique.continuous_phase.comp (Continuous.units_map _ (GlobalTheory.FockCompare.continuous_comp hθ τ))

theorem continuous_infChar {θ : InfFam D} (hθ : IsInfFam θ) (n : D.what₂.Tau → ℤ) : Continuous (infChar θ n) := by
  have e : ((infChar θ n : (AE D)ˣ →* Circle) : (AE D)ˣ → Circle) = fun x => ∏ τ, phaseAt θ τ x ^ n τ := by
    funext x; simp only [infChar, MonoidHom.finset_prod_apply, MonoidHom.zpow_apply]
  rw [e]
  exact continuous_finset_prod _ fun τ _ => (continuous_phaseAt hθ τ).zpow (n τ)

theorem finY_incA (a : D.host.Eˣ) :
    finY D (Units.map (incA D).toMonoidHom a) = Units.map (Formalism.MainNotions.StandardLatticesGL3.inc D).toMonoidHom a := by
  refine Units.ext ?_
  rw [coe_finY, RingEquiv.symm_apply_eq]
  change GlobalTheory.LFun.toFinAd D.host.F D.host.E ((1 : Af D.host.F) ⊗ₜ (a : D.host.E)) =
    GlobalTheory.LFun.toFinAd ℚ D.host.E ((1 : IsDedekindDomain.FiniteAdeleRing (𝓞 ℚ) ℚ) ⊗ₜ (a : D.host.E))
  rw [GlobalTheory.LFun.toFinAd_tmul, GlobalTheory.LFun.toFinAd_tmul, map_one, map_one]

theorem finY_mul_conj (x y : (AE D)ˣ) (h : (y : AE D) = x * cA D x) :
    finY D y = finY D x * Formalism.MainNotions.StandardLatticesGL3.sgU D (finY D x) := by
  refine Units.ext ?_
  apply (GlobalTheory.BotFormula.toFinE D).injective
  rw [Units.val_mul, map_mul]
  change GlobalTheory.BotFormula.toFinE D ((GlobalTheory.BotFormula.toFinE D).symm _) = GlobalTheory.BotFormula.toFinE D ((GlobalTheory.BotFormula.toFinE D).symm _) *
    GlobalTheory.BotFormula.toFinE D (Formalism.MainNotions.StandardLatticesGL3.sgA D ((GlobalTheory.BotFormula.toFinE D).symm _))
  rw [GlobalTheory.BotFormula.toFinE_sgA, RingEquiv.apply_symm_apply, RingEquiv.apply_symm_apply, coe_finIdl, coe_finIdl, h,
    RingHom.map_mul, map_mul]
  congr 1
  have e1 : finPart D (cA D (x : AE D)) = sigR (Af D.host.F) D.sp.cm.sig (finPart D (x : AE D)) :=
    GlobalTheory.FockCompare.LiftUnitary.snd_sigR D.sp.cm.sig (x : AE D)
  rw [e1, GlobalTheory.DefU.ClassFin.finAdEquiv_sigR D.sp.cm.sig (D.host.conj : D.host.E ≃+* D.host.E)
    (fun z => Formalism.MainNotions.GlobalTheoryTheory.jnt_sig_eq_conj D z)]

end GlobalTheory.HeckeUChar
