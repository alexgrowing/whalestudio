import Mathlib
import Formalism.LocalRingCardinality.SpanPowerMembership.Spaces
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelWeilUnitaryConvergent
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.FirstClauseRankZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeOfIsotropicSignature
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsWeilDatumOfSplittingCharacters
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AdelicIwasawaDoubledGroupSelfDualLattice
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DoubledCartanInvolutionCommuteMaximalCompact
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsAdelicMajorantFrameForCartanInvolutions
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsThetaFunNeZero
import Development.AbelianVarietyTheory.Proofs.HeightProofs.AdelicUnitaryRealPointsStructureRealPlaces
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.BoundedCommutantVacua

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Doubling GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero GlobalTheory.ThetaMean GlobalTheory.SiegelFormula.Model

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SiegelWeilMiddle.Model

variable {D : D7}

abbrev iso9 (D : D7) : HSp D := Examples₂.lorentzSpace (E := D.host.E) Examples₂.star_isIntegral

theorem wittIndex_eq_one (D : D7) : Formalism.MainNotions.SchurIrreducible.wittIdx (iso9 D) = 1 := by
  have h1 : Formalism.MainNotions.SchurIrreducible.wittIdx (iso9 D) ≤ 1 :=
    (GlobalTheory.WittSignature.wittIdx_le_signature D.host.E (iso9 D) (Examples₂.lorentzSpace_signature_ok _) D.host.φ₀
      (D.sp.cm.cmUnram.2.1 D.host.φ₀)).2
  let v : Fin (8 + 1) → D.host.E := Pi.single 0 1 + Pi.single 8 1
  have hv : v ≠ 0 := fun h => by simpa [v] using congrFun h 0
  have h0 : Examples₂.diagForm (E := D.host.E) (8 + 1) Examples₂.negLast v v = 0 := by
    simp [Examples₂.diagForm_apply, v, Fin.sum_univ_succ, Examples₂.sgn, Examples₂.negLast, Pi.single_apply]
  have h2 : 1 ≤ Formalism.MainNotions.SchurIrreducible.wittIdx (iso9 D) := le_csSup (bddAbove_witt _)
    ⟨Submodule.span D.host.E {(v : (iso9 D).V)}, finrank_span_singleton hv, by
      intro x hx y hy
      obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.1 hx
      obtain ⟨b, rfl⟩ := Submodule.mem_span_singleton.1 hy
      change Examples₂.diagForm (E := D.host.E) (8 + 1) Examples₂.negLast (a • v) (b • v) = 0
      simp [h0]⟩
  omega

theorem range_inhabited (D : D7) :
    (∃ A B : HSp D, 0 < Formalism.MainNotions.SchurIrreducible.wittIdx B ∧ A.rank < B.rank ∧ B.rank ≤ 2 * A.rank ∧
      A.rank + Formalism.MainNotions.SchurIrreducible.wittIdx B < B.rank) ∧
    (∃ A B : HSp D, B.rank = 2 * A.rank ∧ A.rank < B.rank ∧ A.rank + Formalism.MainNotions.SchurIrreducible.wittIdx B < B.rank) :=
  ⟨⟨pos D 5, iso9 D, by rw [wittIndex_eq_one]; decide, show 5 < 8 + 1 by decide, show 8 + 1 ≤ 2 * 5 by decide,
    by rw [wittIndex_eq_one]; exact show 5 + 1 < 8 + 1 by decide⟩,
   ⟨pos D 1, pos D 2, rfl, show 1 < 2 by decide, by rw [wittIdx_pos]; exact show 1 + 0 < 2 by decide⟩⟩

theorem split_excluded (A V : HSp D) (h : V.rank = A.rank) :
    ¬ A.rank + Formalism.MainNotions.SchurIrreducible.wittIdx (dblSp V) < (dblSp V).rank := by
  rw [wittIdx_dblSp]
  change ¬ A.rank + V.rank < V.rank + V.rank
  omega

theorem hypotheses_inhabited (H : GlobalTheory.Published.WeilRepresentationUnitaryPair) (D : D7) :
    ∃ (ψ : AddChar (AF D.host.F) ℂ) (A B : HSp D) (χB : (AE D)ˣ →* Circle)
      (ω : GA D (dblSp A) × GA D B →* Module.End ℂ (WO (dblSp A) B → ℂ)) (a : GL (Fin A.rank) (AE D))
      (μ : Measure (WO A B)) (𝓨 : Set (WO A B)) (ν : Measure (GA D B)),
      0 < Formalism.MainNotions.SchurIrreducible.wittIdx B ∧ A.rank < B.rank ∧ B.rank ≤ 2 * A.rank ∧ A.rank + Formalism.MainNotions.SchurIrreducible.wittIdx B < B.rank ∧
        IsWeilDatumO ψ (dblSp A) B 1 χB ω ∧ IsMaj A a ∧ IsCovolOne (ratL B A) μ 𝓨 ∧ ν.IsHaarMeasure ∧
        (∃ f, IsThetaFunO ψ (dblSp A) B f ∧ f ≠ 0) ∧ ∃ f, IsThetaFunO ψ (dblSp A) B f ∧ IsKFinVec ω (Khat A a) f := by
  obtain ⟨A, B, h0, h1, h2, h3⟩ := (range_inhabited D).1
  obtain ⟨m, ψ, χ, ω, f, μ, 𝓨, hm, hω, hf, hf0, hμ⟩ := data_exist H A B
  obtain ⟨a, ha⟩ := exists_isMaj A
  exact ⟨ψ, A, B, χ, ω, a, μ, 𝓨, m, h0, h1, h2, h3, hω, ha, hμ, hm, ⟨f, hf, hf0⟩,
    0, GlobalTheory.ThetaMean.Model.zero_vec ψ _ B ω _⟩

theorem conclusion_zero (A B : HSp D) (h : A.rank < B.rank)
    (ω : GA D (dblSp A) × GA D B →* Module.End ℂ (WO (dblSp A) B → ℂ))
    (a : GL (Fin A.rank) (AE D)) (μ : Measure (WO A B)) (𝓨 : Set (WO A B)) (ν : Measure (GA D B)) :
    Eis.EisValueAt A (flat A a (swSec A B ω μ 𝓨 0) (sZero A B)) (sZero A B) (thetaMean ω ν 0) := by
  simpa only [if_pos h, one_smul] using GlobalTheory.ThetaMean.Model.conclusion_zero A B ω a μ 𝓨 ν

theorem integrable_of_weil (H : GlobalTheory.Published.WeilSiegelFormulaUnitary) {ψ : AddChar (AF D.host.F) ℂ} {A B : HSp D}
    (h1 : A.rank < B.rank) (h2 : B.rank ≤ 2 * A.rank) (h3 : A.rank + Formalism.MainNotions.SchurIrreducible.wittIdx B < B.rank) {χ ω f}
    (hω : IsWeilDatumO ψ (dblSp A) B 1 χ ω) (hf : IsThetaFunO ψ (dblSp A) B f) (ν : Measure (GA D B)) [ν.IsHaarMeasure]
    (g : GA D (dblSp A)) : Integrable (AutomorphicL2Unitary.descend (GQ B) fun h => thetaKO ω g h f) (autMeasure B ν) :=
  ((H D A B ν inferInstance (GlobalTheory.Published.one_le_of_range h1 h2) (.inr h3)).2 ψ χ ω hω f hf).1 g

theorem conclusion_of_aniso (H : GlobalTheory.Published.SiegelWeilAnisotropicUnitary) {ψ : AddChar (AF D.host.F) ℂ} {A B : HSp D}
    (h1 : A.rank < B.rank) (h2 : B.rank ≤ 2 * A.rank) (hB : IsAniso B) {χ ω f}
    (hω : IsWeilDatumO ψ (dblSp A) B 1 χ ω) {a : GL (Fin A.rank) (AE D)} (ha : IsMaj A a)
    (hI : HasIwasawa D.sp.cm.sig (dblSp A).gram (Khat A a)) {μ : Measure (WO A B)} {𝓨 : Set (WO A B)}
    (hμ : IsCovolOne (ratL B A) μ 𝓨) (ν : Measure (GA D B)) [ν.IsHaarMeasure]
    (hf : IsThetaFunO ψ (dblSp A) B f) (hK : IsKFinVec ω (Khat A a) f) :
    Eis.EisValueAt A (flat A a (swSec A B ω μ 𝓨 f) (sZero A B)) (sZero A B) (thetaMean ω ν f) := by
  have hA := GlobalTheory.Published.one_le_of_range h1 h2
  simpa only [if_pos h1, one_smul] using
    (H D ψ A B hA (hA.trans h1.le) hB χ ω hω a ha hI μ 𝓨 hμ ν inferInstance f hf hK).2

theorem weilPair : GlobalTheory.Published.WeilRepresentationUnitaryPair := fun D ψ S T χS χT hψ h1 h2 h3 h4 =>
  GlobalTheory.WeilExist.exists_isWeilDatumO D ψ hψ S T χS χT
    ((GlobalTheory.WeilParts.exists_isEtaTilde_unramified D).imp fun _ h => h) h1 h2 h3 h4

theorem all_hypotheses_inhabited (D : D7) (A B : HSp D) :
    ∃ (ψ : AddChar (AF D.host.F) ℂ) (χB : (AE D)ˣ →* Circle)
      (ω : GA D (dblSp A) × GA D B →* Module.End ℂ (WO (dblSp A) B → ℂ)) (a : GL (Fin A.rank) (AE D))
      (θ : InfFam D) (sS : GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift.RealMat (dblSp A)) (sB : GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift.RealMat B)
      (μ : Measure (WO A B)) (𝓨 : Set (WO A B)) (ν : Measure (GA D B)) (f : WO (dblSp A) B → ℂ),
      IsWeilDatumO ψ (dblSp A) B 1 χB ω ∧ IsMaj A a ∧ HasIwasawa D.sp.cm.sig (dblSp A).gram (Khat A a) ∧ IsInfFam θ ∧
        (∀ τ, IsCartanInv (gramAt D (dblSp A) τ) (sS τ)) ∧ (∀ τ, IsCartanInv (gramAt D B τ) (sB τ)) ∧
        (∀ k ∈ Khat A a, ∀ τ, compAt θ τ (Formalism.L2.Theta.mt (dblSp A) k) * sS τ =
          sS τ * compAt θ τ (Formalism.L2.Theta.mt (dblSp A) k)) ∧
        IsCovolOne (ratL B A) μ 𝓨 ∧ ν.IsHaarMeasure ∧ GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift.IsFockVec ψ θ (dblSp A) B sS sB f ∧ f ≠ 0 := by
  obtain ⟨m, ψ, χ, ω, -, μ, 𝓨, hm, hω, -, -, hμ⟩ := data_exist weilPair A B
  obtain ⟨θ, hθ⟩ := hω.std.2.1
  have hc : ∀ (V : HSp D) τ, ∃ s, IsCartanInv (gramAt D V τ) s := fun V τ =>
    GlobalTheory.Mem.ThetaNonzero.exists_isCartanInv (GlobalTheory.SmoothForms.RealPts.gramAt_herm V τ)
      (GlobalTheory.SmoothForms.RealPts.gramAt_unit V τ)
  choose s hs using hc
  obtain ⟨a, ha, hfr⟩ := GlobalTheory.Core.Rk.MajFrame.exists_maj_cart D θ A (s A) hθ (hs A)
  obtain ⟨h1, h2⟩ := GlobalTheory.Core.Rk.IP.Cartan.cartan_dbl D θ A (s A) a hθ (hs A) hfr
  obtain ⟨f, hf, f0⟩ := GlobalTheory.IndefiniteRowSideFullHecke.BoundedCommutantVacua.exists_isVac_ne_zero hω.std hθ h1 (hs B)
  refine ⟨ψ, χ, ω, a, θ, _, s B, μ, 𝓨, m, f, hω, ha, GlobalTheory.Core.Rk.IP.hasIwasawa_Khat D A a ha, hθ, h1, hs B, h2, hμ, hm,
    ⟨hf.1, 1, fun l hl => ?_⟩, f0⟩
  obtain ⟨p, rfl⟩ := List.length_eq_one_iff.1 hl
  exact hf.2 p.1 p.2

end GlobalTheory.SiegelWeilMiddle.Model

end
