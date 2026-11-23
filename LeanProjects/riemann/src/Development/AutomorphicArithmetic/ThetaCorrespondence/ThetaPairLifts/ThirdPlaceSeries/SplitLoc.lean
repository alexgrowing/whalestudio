import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsTypeGroupBlockLift
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CharacterChoiceData
import Development.AutomorphicArithmetic.Foundations.LocalLanglands.IsRecTOfIsRec

set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
namespace GlobalTheory.PendOf
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField
  IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.NPin ValuativeRel
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
section Local
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
end Local
def localLabelPolynomial (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7) (k : Fin 2) (v : D.nd.PlG k) {n : ℕ}
    (π : Irr ((D.naut.plGw k v).adicCompletion D.host.E) n) : (ZMod (D.host.g k))[X] :=
  haveI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩
  GlobalTheory.WeilDeligne.WD.lab (D.ntypes.teichC k) (D.ntypes.tg k v) (_root_.GlobalTheory.NPin.weilDeligneOfLocalIrrep hL D (D.naut.plGw k v) n π)
def RegularLocalCondition (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7) : Prop :=
  ∀ (k : Fin 2) (v : D.nd.PlG k) (π : Irr ((D.naut.plGw k v).adicCompletion D.host.E) D.R.r) ρ f, InSeries D k ρ f →
    Squarefree f → (∃ x, IsLevelOne π.π x ∧ NotKilled π.π (idemOf D k ρ) x) →
    (_root_.GlobalTheory.NPin.weilDeligneOfLocalIrrep hL D (D.naut.plGw k v) D.R.r π).mono0 ∧ _root_.GlobalTheory.PendOf.localLabelPolynomial hL D k v π = f
def SplitLocalCondition (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7) : Prop :=
  ∀ (k : Fin 2) (v : D.nd.PlG k) (χ : ((D.naut.plGw k v).adicCompletion D.host.E)ˣ →* ℂˣ) (hχ : IsSmoothChar χ)
    (u : ZMod (D.host.g k)) (π : Irr ((D.naut.plGw k v).adicCompletion D.host.E) (D.R.r + D.R.t)) ρ f,
    IsTame χ → _root_.GlobalTheory.PendOf.localLabelPolynomial hL D k v (Irr.ofDet 1 χ hχ) = X - C u → InSeries D k ρ f → ¬ f.IsRoot u →
    (∃ x, IsBlockVec χ π.π x ∧ NotKilled π.π (idemOf D k ρ) x) →
    ∃ (π₁ : Irr ((D.naut.plGw k v).adicCompletion D.host.E) D.R.r)
      (π₂ : Irr ((D.naut.plGw k v).adicCompletion D.host.E) D.R.t), IsSpherical π₂.π ∧
      Nonempty (π.π.Equiv (prod₂ π₁.π (twist π₂.π (detChar (Fin D.R.t) χ)))) ∧
      ∃ y, IsLevelOne π₁.π y ∧ NotKilled π₁.π (idemOf D k ρ) y
def LocalDatumCondition (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7) : Prop :=
  ∀ (k : Fin 2) (v : D.nd.PlG k) (χ : ((D.naut.plGw k v).adicCompletion D.host.E)ˣ →* ℂˣ) (hχ : IsSmoothChar χ)
    (u : ZMod (D.host.g k)) (π : Irr ((D.naut.plGw k v).adicCompletion D.host.E) (D.R.r + D.R.t)) ρ f,
    IsTame χ → _root_.GlobalTheory.PendOf.localLabelPolynomial hL D k v (Irr.ofDet 1 χ hχ) = X - C u → InSeries D k ρ f → Squarefree f → ¬ f.IsRoot u →
    (∃ x, IsBlockVec χ π.π x ∧ NotKilled π.π (idemOf D k ρ) x) →
    (_root_.GlobalTheory.NPin.weilDeligneOfLocalIrrep hL D (D.naut.plGw k v) _ π).mono0 ∧ _root_.GlobalTheory.PendOf.localLabelPolynomial hL D k v π = f * (X - C u) ^ D.R.t
end GlobalTheory.PendOf
end
end
