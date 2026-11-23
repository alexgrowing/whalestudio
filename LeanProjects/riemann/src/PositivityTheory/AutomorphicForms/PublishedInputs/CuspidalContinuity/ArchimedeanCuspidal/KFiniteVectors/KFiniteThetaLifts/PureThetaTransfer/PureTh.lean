import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.KFiniteVectors.KFiniteThetaLifts.DualWhittakerAdelicGL3

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Filter Topology
open GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.GodementSection (localChar)
open GroundTheory.Automorphic.Reduction (finAt infAt maxCompact)
open GroundTheory.Automorphic.GLnLocal (integralGL)
open GroundTheory.Global.AdicLiesOver
open scoped NumberField.AdeleRing ValuativeRel

namespace Ad3.K.QuadraticBaseChangeGL3.Th

variable {K : Type} [Field K] [NumberField K]

def Unr (c : HeckeCharacter K) (v : Pl) : Prop :=
  ∀ (w : PlK K) [w.asIdeal.LiesOver v.asIdeal], IsUnramifiedChar (localChar c w) ∧ w.asIdeal.ramificationIdx (𝓞 ℚ) = 1

def PureTh (c : HeckeCharacter K) (v : Pl) (W' : GL (Fin 2) (Qv v) → ℂ) : Prop :=
  (∃ (w₁ w₂ : PlK K) (_ : w₁.asIdeal.LiesOver v.asIdeal) (_ : w₂.asIdeal.LiesOver v.asIdeal), w₁ ≠ w₂ ∧
    ∃ Φ : Qv v × Qv v → ℂ, IsLocallyConstant Φ ∧ HasCompactSupport Φ ∧
      W' = GL2LocalData.WcS (GP.psiF v)⁻¹ (cAt c v w₁) (cAt c v w₂) Φ) ∨
  (∃ (w : PlK K) (_ : w.asIdeal.LiesOver v.asIdeal), (∀ w' : PlK K, w'.asIdeal.LiesOver v.asIdeal → w' = w) ∧
    ∃ (σ : Kv K w ≃ₐ[Qv v] Kv K w) (η : (Qv v)ˣ →* ℂˣ), σ ≠ AlgEquiv.refl ∧
      (∀ a, ((η a : ℂˣ) : ℂ) = GL2LocalData.nsg (Kv K w) (a : Qv v)) ∧
      ∃ Φ ∈ GL2LocalData.SBc (Qv v) (Kv K w) (localChar c w),
        W' = GL2LocalData.Wc (GP.psiF v)⁻¹ σ (selfDualMeasure (GL2LocalData.chE (Kv K w) (GP.psiF v)⁻¹))
          (GL2LocalData.lamE (Kv K w) (GP.psiF v)⁻¹ η) (localChar c w) Φ)

def StdTh (c : HeckeCharacter K) (v : Pl) (W' : GL (Fin 2) (Qv v) → ℂ) : Prop :=
  (∃ (w₁ w₂ : PlK K) (_ : w₁.asIdeal.LiesOver v.asIdeal) (_ : w₂.asIdeal.LiesOver v.asIdeal), w₁ ≠ w₂ ∧
      W' = GL2LocalData.WcS (GP.psiF v)⁻¹ (cAt c v w₁) (cAt c v w₂)
        (Set.indicator {x : Qv v × Qv v | x.1 ∈ 𝒪[Qv v] ∧ x.2 ∈ 𝒪[Qv v]} 1)) ∨
  (∃ (w : PlK K) (_ : w.asIdeal.LiesOver v.asIdeal), (∀ w' : PlK K, w'.asIdeal.LiesOver v.asIdeal → w' = w) ∧
    ∃ (σ : Kv K w ≃ₐ[Qv v] Kv K w) (η : (Qv v)ˣ →* ℂˣ), σ ≠ AlgEquiv.refl ∧
      (∀ a, ((η a : ℂˣ) : ℂ) = GL2LocalData.nsg (Kv K w) (a : Qv v)) ∧
        W' = GL2LocalData.Wc (GP.psiF v)⁻¹ σ (selfDualMeasure (GL2LocalData.chE (Kv K w) (GP.psiF v)⁻¹))
          (GL2LocalData.lamE (Kv K w) (GP.psiF v)⁻¹ η) (localChar c w) (Set.indicator {x : Kv K w | x ∈ 𝒪[Kv K w]} 1))

def SphAE (Wtf : ∀ v : Pl, GL (Fin 2) (Qv v) → ℂ) : Prop := ∃ S1 : Finset Pl, ∀ v ∉ S1, SphN (Wtf v)

variable (K) in

def STDSPH : Prop := Module.finrank ℚ K = 2 → ∀ (c : HeckeCharacter K) (v : Pl), Unr c v → ∀ W', StdTh c v W' →
  SphN W' ∧ InThE c v W' 1

end Ad3.K.QuadraticBaseChangeGL3.Th
