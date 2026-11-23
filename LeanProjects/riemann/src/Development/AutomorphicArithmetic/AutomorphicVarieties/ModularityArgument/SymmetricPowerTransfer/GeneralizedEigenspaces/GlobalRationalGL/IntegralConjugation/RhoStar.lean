import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.GlobalRationalGL.EStar
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteAdelicUnitaryPointEqOfSectionComponentsEq

open NumberField IsDedekindDomain ValuativeRel GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.SplitWeil Formalism.BasicNotions Matrix
open UpperTheory.V UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Dict UpperTheory.V.Z.Sym.Dict.Br UpperTheory.V.Z.Sym.Loc UpperTheory.V.Z.Sym.Glob
open UpperTheory.V.W (Plc Lp)

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem UpperTheory.V.Z.Sym.Dict.Br.rhoStar :
    ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (P : Pre L), ∀ v (x : Lsq (Kv v) (cv v P.Δ)) (a : Af L), (∀ w h, P.rho v w h x = pLoc L w a) → ∀ w h, P.rho v w h (star x) = pLoc L w (cjF a) := by
  intro L _ _ _ P v x a hx w h
  have hu : un (conjSrc (IsCMField.complexConj L).toRingEquiv w) = v := by
    rw [← h]; exact GlobalTheory.LocInj.under_conjSrc w
  have hφ : ∀ y : Kv v, conjLoc (IsCMField.complexConj L).toRingEquiv w
      (P.φ v _ hu y) = P.φ v w h y := by
    intro y
    refine congrFun ((HeightOneSpectrum.denseRange_algebraMap (Lp L) v).equalizer
      ((conjLoc_spec _ w).1.comp (P.φ_cont v _ hu)) (P.φ_cont v w h) (funext fun b => ?_)) y
    simp only [Function.comp_apply]
    rw [P.φ_alg, P.φ_alg, (conjLoc_spec _ w).2.1]
    congr 1
    exact AlgEquiv.commutes (IsCMField.complexConj L) b
  have hrt : conjLoc (IsCMField.complexConj L).toRingEquiv w (P.rt (conjSrc (IsCMField.complexConj L).toRingEquiv w)) = - P.rt w := by
    rw [Pre.rt, (conjLoc_spec _ w).2.1, Pre.rt, ← map_neg, ← map_neg]
    congr 1
    have hs : star (QuadraticAlgebra.omega : Lsq (Lp L) P.Δ) = - QuadraticAlgebra.omega := by
      ext <;> simp
    change IsCMField.complexConj L (P.e QuadraticAlgebra.omega) = _
    rw [← P.e_star, hs]
  rw [cjF, pLoc_conjFin, ← hx _ hu]
  change P.φ v w h (star x).re + P.φ v w h (star x).im * P.rt w =
    conjLoc (IsCMField.complexConj L).toRingEquiv w (P.φ v _ hu x.re + P.φ v _ hu x.im * P.rt _)
  rw [map_add, map_mul, hφ, hφ, hrt]
  simp
