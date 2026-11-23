import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.CyclicStrongAtCusp
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RamificationTowerCompatible
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsLocCompAndIsLocLoc
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AutomorphicFormsFiniteGL
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.CuspidalBaseChangeTransTowerStatement
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.GLq
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.GalCut GlobalTheory.RoadU GlobalTheory.AboveL
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.RoadU

theorem chars_congr {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : ℕ}
    {ξ ξ' : Fin n → (kˣ →* ℂˣ)} (hξ : ∀ j, IsSmoothChar (ξ j)) (hξ' : ∀ j, IsSmoothChar (ξ' j)) (e : ξ = ξ') :
    chars ξ hξ = chars ξ' hξ' := by
  subst e; rfl

theorem charLift_trans : ∀ (K M N : Type) [Field K] [NumberField K] [IsTotallyComplex K] [Field M] [NumberField M] [IsTotallyComplex M] [Field N] [NumberField N] [IsTotallyComplex N] [Algebra K M] [Algebra M N] [Algebra K N] [IsScalarTower K M N] (a : ℕ) (π : CuspSub K a) (P : CuspSub M a) (Q : CuspSub N a), CharLift π P → CharLift P Q → CharLift π Q := by
  intro K M N _ _ _ _ _ _ _ _ _ _ _ _ _ a π P Q h1 h2
  refine ⟨GlobalTheory.T.cuspidal_baseChange_trans_tower K M N a π P Q h1.1 h2.1, ?_⟩
  intro v w _ τ T hτ hT ξ hξ hs
  let u : HeightOneSpectrum (𝓞 M) := w.under (𝓞 M)
  haveI hwu : w.asIdeal.LiesOver u.asIdeal := ⟨rfl⟩
  haveI huv : u.asIdeal.LiesOver v.asIdeal := Ideal.LiesOver.tower_bot w.asIdeal u.asIdeal v.asIdeal
  obtain ⟨σ, hσ, -⟩ := GlobalTheory.CuspRep.LocEx.exists_isLocComp GlobalTheory.automorphicFormsFiniteGL M a P u
  have h3 := h1.2 v u τ σ hτ hσ ξ hξ hs
  have h4 := h2.2 u w σ T hσ hT _ _ h3
  have e := GlobalTheory.BCChar.normU_comp_normU v u w
  refine (congrArg (HasSupport T.ρ) (chars_congr _ _ ?_)).mp h4
  funext j
  rw [MonoidHom.comp_assoc, e]

end GlobalTheory.RoadU
