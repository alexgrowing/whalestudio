import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.DiscreteSpectrumResidualClassification
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SignatureRigidifications
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.BernsteinUnitaryProductIrreducible
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SignatureRigidificationsStatement

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset
open Formalism.DivisionValues (vw)
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.CMVal (IsHeckeL)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.SqTop
open GlobalTheory.ConstRatio (NegIdx Factor)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section
namespace GlobalTheory.SqTower.StageExists
set_option maxHeartbeats 1000000 in
open GlobalTheory.Grid GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle GlobalTheory.HeckeCharsOfSquare in
theorem exists_quadratic_tower_stage : _root_.GlobalTheory.FunPr.ThetaLocalInputs → GBig fun {D} T _ _ G _ _ _ _ => ∀ (W : G.Weil), IsStdChar D W.ψ (-1) → ∀ (i j : Fin D.R.m) (p q : ℕ)
    (A A' WW : HSp D) (ΛA : Submodule (𝓞 D.host.E) (Fin A.rank → D.host.E)) (ΛA' : Submodule (𝓞 D.host.E) (Fin A'.rank → D.host.E))
    (ΛW : Submodule (𝓞 D.host.E) (Fin WW.rank → D.host.E)), IsSelfDualC A ΛA → IsSelfDualC A' ΛA' → IsSelfDualC WW ΛW →
    p ≤ pp D j → q ≤ qq D j → A.rank + 2 * pp D j = rankV D (i + 1) (j + 1) + 2 * p →
    A'.rank + 2 * qq D j = rankV D i j + 2 * q → NegIdx A p → NegIdx A' q → NegIdx WW (p + q) → A.rank + A'.rank = WW.rank →
      ∃ X : Tri T A A' WW, GlobalTheory.SqTower.IsStageC W i j p q X ∧ X.rA.Λ = ΛA ∧ X.rA'.Λ = ΛA' ∧ X.rW.Λ = ΛW := by
  intro _
  refine ⟨0, fun _ _ _ => ⟨0, 0, fun C _ D large₂ _ _ _ T Lc μ₀ hL G W hψ i j p q A A' WW ΛA ΛA' ΛW sA sA' sW hp hq kA kA'
    nA nA' nW hrk => ?_⟩⟩
  obtain ⟨rA, eA, hA⟩ := rig_exists nA _ sA
  obtain ⟨rA', eA', hA'⟩ := rig_exists nA' _ sA'
  obtain ⟨rW, eW, hW⟩ := rig_exists nW _ sW
  have ch := TopExists.chars G hL W i j
  have hθ := W.θ_is
  have hη := GlobalTheory.WeilParts.exists_isEtaTilde_unramified D
  choose ω hω using fun t => GlobalTheory.ConstRatio.exists_isWeil hψ hη true A WW (ch t).2.1
    (ch t).2.2.2.1 (resEta_of_mod (ch t).2.2.2.2.2.1 (by omega)) (resEta_of_mod (ch t).2.2.2.2.2.2.2 (by omega))
  choose ω' hω' using fun t => GlobalTheory.ConstRatio.exists_isWeil hψ hη false A' WW (ch t).1
    (ch t).2.2.1 (resEta_of_mod (ch t).2.2.2.2.1 (by omega)) (resEta_of_mod (ch t).2.2.2.2.2.2.1 (by omega))
  obtain ⟨vac, hv⟩ := (vac_exists hψ hθ nA nW hA hW).1
  obtain ⟨vac', hv'⟩ := (vac_exists hψ hθ nA' nW hA' hW).2
  choose e he using TopExists.idem_exists G hL W
  choose c hc using fun t w => GlobalTheory.ConstRatio.exists_expAt (nuH G t i j) w
  have hI : ∀ t, (∏ w ∈ locPl G t, w.asIdeal ^ c t w) ≠ ⊥ := fun t =>
    Finset.prod_ne_zero_iff.2 fun w _ => pow_ne_zero _ w.ne_bot
  choose f hf _ using fun t => GlobalTheory.T.first_standard_pair_member_has_theta_function D W.ψ W.θ _ WW rA rW _ _ _ _ _ hA hW (ch t).2.2.1 (he t) (hI t) hv
  choose f' hf' _ using fun t =>
    GlobalTheory.T.exists_thetaFunction_standardPairSecond D W.ψ W.θ _ WW rA' rW _ _ _ _ A.rank _ hA' hW (ch t).2.2.1 (he t) (hI t) hv'
  obtain ⟨m, fd, hm⟩ := GlobalTheory.ConstRatio.exists_meas A
  obtain ⟨m', fd', hm'⟩ := GlobalTheory.ConstRatio.exists_meas A'
  exact ⟨⟨rA, rA', rW, ω, ω', vac, vac', e, c, f, f', m, fd, m', fd'⟩,
    ⟨hp, hq, kA, kA', nA, nA', nW,
      ⟨hrk, hA, hA', hW, hω, hω', hv, hv', he, fun t w _ => hc t w, hf, hf', hm, hm'⟩⟩, eA, eA', eW⟩
end GlobalTheory.SqTower.StageExists
end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset
open Formalism.DivisionValues (vw)
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.CMVal (IsHeckeL)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.SqTop
open GlobalTheory.ConstRatio (NegIdx Factor)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.quadratic_tower_exists : _root_.GlobalTheory.FunPr.ThetaLocalInputs → GBig fun {D} T _ _ G _ _ _ _ => ∀ (W : G.Weil), IsStdChar D W.ψ (-1) → ∀ (i j : Fin D.R.m) (p q : ℕ)
    (A A' WW : HSp D) (ΛA : Submodule (𝓞 D.host.E) (Fin A.rank → D.host.E)) (ΛA' : Submodule (𝓞 D.host.E) (Fin A'.rank → D.host.E))
    (ΛW : Submodule (𝓞 D.host.E) (Fin WW.rank → D.host.E)), IsSelfDualC A ΛA → IsSelfDualC A' ΛA' → IsSelfDualC WW ΛW →
    p ≤ pp D j → q ≤ qq D j → A.rank + 2 * pp D j = rankV D (i + 1) (j + 1) + 2 * p →
    A'.rank + 2 * qq D j = rankV D i j + 2 * q → NegIdx A p → NegIdx A' q → NegIdx WW (p + q) → A.rank + A'.rank = WW.rank →
      ∃ X : Tri T A A' WW, GlobalTheory.SqTower.IsStageC W i j p q X ∧ X.rA.Λ = ΛA ∧ X.rA'.Λ = ΛA' ∧ X.rW.Λ = ΛW := by
  first | exact @_root_.GlobalTheory.SqTower.StageExists.exists_quadratic_tower_stage | exact _root_.GlobalTheory.SqTower.StageExists.exists_quadratic_tower_stage | (intros; apply _root_.GlobalTheory.SqTower.StageExists.exists_quadratic_tower_stage <;> assumption)
end
