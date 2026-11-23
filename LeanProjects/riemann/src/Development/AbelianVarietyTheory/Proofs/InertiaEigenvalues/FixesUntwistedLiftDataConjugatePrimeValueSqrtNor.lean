import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ConjTupRefl
import Development.AbelianVarietyTheory.Definitions.Divisors.GenReads
import Development.AbelianVarietyTheory.Definitions.ThetaValues.ExistsRootNotMem
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneMapOfOfExtends
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ThExprUniqOfChartIndep2
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GaussGLZero
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ProdVal
import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.FinPartDetAtInvInt
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.CompletedLatticeIntegralityFacts
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsDecompChainSpaceDefiniteAddNormalFrame
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.ConjTwist GlobalTheory.GalTw ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Classical

namespace GlobalTheory.ConjFix

variable {D : D7}

noncomputable def starOEquiv : 𝓞 D.host.E ≃+* 𝓞 D.host.E :=
  { Formalism.L2.DIV.starOHom (E := D.host.E) with
    invFun := Formalism.L2.DIV.starOHom (E := D.host.E)
    left_inv := fun a => Formalism.L2.DIV.starO_starO a
    right_inv := fun a => Formalism.L2.DIV.starO_starO a }

theorem natCast_mem_conjPl_iff (PP : Pl D.host.E) (N : ℕ) :
    ((N : 𝓞 D.host.E)) ∈ (Formalism.L2.DIV.conjPl PP).asIdeal ↔ ((N : 𝓞 D.host.E)) ∈ PP.asIdeal := by
  show Formalism.L2.DIV.starOHom (N : 𝓞 D.host.E) ∈ PP.asIdeal ↔ _
  rw [map_natCast]

theorem absNorm_conjPl (PP : Pl D.host.E) :
    Ideal.absNorm (Formalism.L2.DIV.conjPl PP).asIdeal = Ideal.absNorm PP.asIdeal := by
  have h : (Formalism.L2.DIV.conjPl PP).asIdeal = PP.asIdeal.map (starOEquiv (D := D)) := by
    rw [← Ideal.comap_symm]; rfl
  rw [Ideal.absNorm_apply, Ideal.absNorm_apply, Submodule.cardQuot_apply, Submodule.cardQuot_apply]
  exact (Nat.card_congr (Ideal.quotientEquiv PP.asIdeal (Formalism.L2.DIV.conjPl PP).asIdeal (starOEquiv (D := D)) h).toEquiv).symm

theorem fixBase_split_conj {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} (T : CoreJ D)
    [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (i : Fin D.R.m) (τ : ℂ ≃+* ℂ) (PP : Pl D.host.E) :
    FixBase T R i τ → ((D.host.g 0 * D.host.g 1 : ℕ) : 𝓞 D.host.E) ∉ PP.asIdeal →
      τ ((((R.C.mu0 i * R.C.eta⁻¹).val (Formalism.L2.DIV.conjPl PP) : ℂˣ) : ℂ) * ((Real.sqrt (Ideal.absNorm PP.asIdeal : ℝ) : ℝ) : ℂ)) =
        (((R.C.mu0 i * R.C.eta⁻¹).val (Formalism.L2.DIV.conjPl PP) : ℂˣ) : ℂ) * ((Real.sqrt (Ideal.absNorm PP.asIdeal : ℝ) : ℝ) : ℂ) := by
  intro hF hN
  have hN' : ((D.host.g 0 * D.host.g 1 : ℕ) : 𝓞 D.host.E) ∉ (Formalism.L2.DIV.conjPl PP).asIdeal := by
    rwa [natCast_mem_conjPl_iff]
  have := hF.split (Formalism.L2.DIV.conjPl PP) hN'
  rwa [absNorm_conjPl] at this

end GlobalTheory.ConjFix
