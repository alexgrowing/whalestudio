import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.TwistPlacesOffPrimeQZero
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.NormSmall
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.DictAt
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CuspAlongSmoothRows
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ToricSymbols
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx

open GlobalTheory.SplitWeil GlobalTheory.SplitFlip MeasureTheory
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField GlobalTheory.FunObj.borelKw GlobalTheory.FunObj.borelSpaceKw

noncomputable section

namespace GlobalTheory.RowEx.PhaseCarry

section Loc

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k]
  [BorelSpace k] {K : Type} [Field K] (σ : K →+* ℂ)

def PhW (Γ : Grid k) (hs : 1 ≤ Γ.s) (J : Γ.Level) (ψ : AddChar k Circle) (ν : Measure k) (keep : Bool) (ϖ : kˣ) (c : ℕ)
    (T : Γ.Args → ℂ) (β : Cosets hs J) : Prop :=
  ∀ x y e, (unfTerm ψ ν keep (Reps.through hs J (stair Γ ϖ c)) T β).datum x y ≠ 0 →
    moved Γ keep ((Reps.through hs J (stair Γ ϖ c)).elt β) T (fill hs x y e) ≠ 0 → (ψ (phase x e) : ℂ) ∈ Set.range σ

def SuW (Γ : Grid k) (hs : 1 ≤ Γ.s) (J : Γ.Level) (ψ : AddChar k Circle) (ν : Measure k) (keep : Bool) (ϖ : kˣ) (c : ℕ)
    (T : Γ.Args → ℂ) (β : Cosets hs J) : Prop :=
  β ∈ unfSupport ψ ν keep (Reps.through hs J (stair Γ ϖ c)) T

end Loc

section Loc2

variable {k : Type} {_ : Field k} {_ : ValuativeRel k} {_ : TopologicalSpace k} {_ : IsNonarchimedeanLocalField k}
  {_ : MeasurableSpace k} {_ : BorelSpace k} {K : Type} [Field K] (σ : K →+* ℂ)

theorem congrW {Γ Γ' : Grid k} (hΓ : Γ = Γ') {hs : 1 ≤ Γ.s} {hs' : 1 ≤ Γ'.s} {J : Γ.Level} {J' : Γ'.Level} (hJ : HEq J J')
    {ψ ψ' : AddChar k Circle} (hψ : ψ = ψ') {ν ν' : Measure k} (hν : ν = ν') {keep keep' : Bool} (hk : keep = keep')
    (ϖ : kˣ) {c c' : ℕ} (hc : c = c') {T : Γ.Args → ℂ} {T' : Γ'.Args → ℂ} (hT : HEq T T') {β : Cosets hs J}
    {β' : Cosets hs' J'} (hβ : HEq β β') :
    (PhW σ Γ hs J ψ ν keep ϖ c T β ↔ PhW σ Γ' hs' J' ψ' ν' keep' ϖ c' T' β') ∧
      (SuW Γ hs J ψ ν keep ϖ c T β ↔ SuW Γ' hs' J' ψ' ν' keep' ϖ c' T' β') := by
  subst hΓ hψ hν hk hc
  obtain rfl := eq_of_heq hJ
  obtain rfl := eq_of_heq hT
  obtain rfl := eq_of_heq hβ
  exact ⟨Iff.rfl, Iff.rfl⟩

def castCos {Γ Γ' : Grid k} (hΓ : Γ = Γ') {hs : 1 ≤ Γ.s} {hs' : 1 ≤ Γ'.s} {J : Γ.Level} {J' : Γ'.Level} (hJ : HEq J J')
    (β : Cosets hs J) : Cosets hs' J' := by
  subst hΓ
  obtain rfl := eq_of_heq hJ
  exact β

theorem castCos_heq {Γ Γ' : Grid k} (hΓ : Γ = Γ') {hs : 1 ≤ Γ.s} {hs' : 1 ≤ Γ'.s} {J : Γ.Level} {J' : Γ'.Level}
    (hJ : HEq J J') (β : Cosets hs J) : HEq (castCos hΓ (hs' := hs') hJ β) β := by
  subst hΓ
  obtain rfl := eq_of_heq hJ
  rfl

end Loc2

set_option maxHeartbeats 4000000 in

theorem trPhase_of_trFlip : TrFlip → TrPhase := by
  intro hF X X' T T' L L' sc G G' W W' S S' μ₀ μ₀' ι hA M σ hS t' Φ' β' hβ'
  obtain ⟨Φ, hΦ⟩ := hF X X' T T' L L' sc G G' W W' S S' μ₀ μ₀' ι hA Φ'
  have hpre := hA.l.pre
  have hv0 := hA.g.v0
  have hw := hA.g.w
  have hQ := hA.l.Q t'
  have hψ := hA.w.ψ
  clear hF hA
  rcases X with ⟨⟨P⟩, _, _, _, _, _, _⟩
  rcases X' with ⟨⟨P'⟩, _, _, _, _, _, _⟩
  dsimp only at hpre
  subst hpre
  replace hv0 := eq_of_heq hv0
  replace hw := eq_of_heq hw
  replace hQ := eq_of_heq hQ
  replace hψ := eq_of_heq hψ
  have hW0 : G'.pl.W0 = G.pl.W0 := by
    unfold Places.W0 Places.S0
    rw [hv0, hw]
    rfl
  have hloc : locPl G' t' = locPl G (ι t') := by
    unfold locPl
    rw [hW0, hQ]
    rfl
  have hcos : ∀ w, cosExp G' w = cosExp G w := fun w => by
    unfold cosExp Places.depth
    rw [hW0, hv0]
    rfl
  have hkeep : ∀ w, keepAt G' w = keepAt G w := fun w => by
    unfold keepAt
    rw [hW0]
    rfl
  have hpsi : ∀ w, psiAt W' w = psiAt W w := fun w => by
    ext x
    show (W'.ψ _ : ℂ) = W.ψ _
    rw [hψ]
    rfl
  have hmem : ∀ w, w ∈ locPl G (ι t') → w ∈ locPl G' t' := fun w h => hloc ▸ h
  have hF3 := fun w (h : w ∈ locPl G' t') => hΦ t' w w HEq.rfl h
  have hΓ : ∀ w (h : w ∈ locPl G' t'), locGrid G' t' w = locGrid G (ι t') w := fun w h => eq_of_heq (hF3 w h).1
  let β : CosFam G (ι t') := fun w => castCos (hΓ w.1 (hmem _ w.2)) (hF3 w.1 (hmem _ w.2)).2.1 (β' ⟨w.1, hmem _ w.2⟩)
  have hβh : ∀ w : locPl G (ι t'), HEq (β' ⟨w.1, hmem _ w.2⟩) (β w) := fun w => (castCos_heq _ _ _).symm
  have hβ : β ∈ S.supp (ι t') Φ := fun w =>
    ((congrW σ (hΓ w.1 (hmem _ w.2)) (hF3 w.1 (hmem _ w.2)).2.1 (hpsi w.1) rfl (hkeep w.1) (unifAt w.1)
      (hcos w.1) (hF3 w.1 (hmem _ w.2)).2.2 (hβh w)).2).mp (hβ' ⟨w.1, hmem _ w.2⟩)
  intro w'
  have hw' : w'.1 ∈ locPl G (ι t') := hloc ▸ w'.2
  exact ((congrW σ (hΓ w'.1 w'.2) (hF3 w'.1 w'.2).2.1 (hpsi w'.1) rfl (hkeep w'.1) (unifAt w'.1)
      (hcos w'.1) (hF3 w'.1 w'.2).2.2 (hβh ⟨w'.1, hw'⟩)).1).mpr (hS (ι t') Φ β hβ ⟨w'.1, hw'⟩)

end GlobalTheory.RowEx.PhaseCarry
