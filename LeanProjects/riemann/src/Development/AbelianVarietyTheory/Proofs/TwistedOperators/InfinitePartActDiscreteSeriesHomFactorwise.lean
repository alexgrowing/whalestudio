import Development.AbelianVarietyTheory.Definitions.Divisors.IsSmoothVector
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.Definitions.Divisors.HasTypeVec
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ExponentSeparation
open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.MainNotions.S

namespace GlobalTheory.TrAct

open Classical in

noncomputable def partAt {D : D7} (V : HSp D) (g : GA D V) (s : Finset D.what₂.Tau) : GA D V :=
  ofInf D.sp.cm.sig V.gram (embArchPi D.sp.cm.sig V.gram fun w =>
    if w ∈ s.image (placeOf D) then projArch D.sp.cm.sig V.gram w g else 1)

open Classical in
theorem projArch_partAt {D : D7} (V : HSp D) (g : GA D V) (s : Finset D.what₂.Tau) (w : InfinitePlace D.host.F) :
    projArch D.sp.cm.sig V.gram w (partAt V g s) =
      if w ∈ s.image (placeOf D) then projArch D.sp.cm.sig V.gram w g else 1 := by
  rw [partAt, projArch_ofInf, projInfArch_embArchPi]

theorem proj_partAt {D : D7} (V : HSp D) (g : GA D V) (s : Finset D.what₂.Tau) (v : HeightOneSpectrum (𝓞 D.host.F)) :
    proj D.sp.cm.sig V.gram v (partAt V g s) = 1 := by
  rw [partAt, proj_ofInf]

open Classical in
theorem partAt_insert {D : D7} (V : HSp D) (g : GA D V) {s : Finset D.what₂.Tau} {τ : D.what₂.Tau} (hτ : τ ∉ s) :
    partAt V g (insert τ s) =
      embW V (placeOf D τ) (projArch D.sp.cm.sig V.gram (placeOf D τ) g) * partAt V g s := by
  refine GAd_ext D.sp.cm.sig V.gram (fun w => ?_) (fun v => ?_)
  · rw [map_mul, projArch_partAt, projArch_partAt]
    by_cases hw : w = placeOf D τ
    · subst hw
      have h1 : placeOf D τ ∈ (insert τ s).image (placeOf D) := Finset.mem_image_of_mem _ (Finset.mem_insert_self τ s)
      have h2 : placeOf D τ ∉ s.image (placeOf D) := fun h => by
        obtain ⟨ρ, hρ, e⟩ := Finset.mem_image.1 h
        exact hτ ((placeOf_bijective D).1 e ▸ hρ)
      rw [if_pos h1, if_neg h2, mul_one]
      exact (projArch_embArch_self _ _ _ _).symm
    · rw [projArch_embArch_ne _ _ hw, one_mul]
      congr 1
      simp only [Finset.image_insert, Finset.mem_insert, hw, false_or]
  · rw [map_mul, proj_partAt, proj_partAt, proj_embArch, one_mul]

theorem partAt_univ {D : D7} (V : HSp D) (g : GA D V) [Fintype D.what₂.Tau] :
    partAt V g Finset.univ = (toInf V g : GA D V) := by
  classical
  refine GAd_ext D.sp.cm.sig V.gram (fun w => ?_) (fun v => ?_)
  · rw [projArch_partAt, if_pos]
    · show _ = projArch D.sp.cm.sig V.gram w (ofInf D.sp.cm.sig V.gram (projInf D.sp.cm.sig V.gram g))
      rw [projArch_ofInf, projInfArch_projInf]
    · obtain ⟨τ, rfl⟩ := (placeOf_bijective D).2 w
      exact Finset.mem_image_of_mem _ (Finset.mem_univ τ)
  · rw [proj_partAt]
    show _ = proj D.sp.cm.sig V.gram v (ofInf D.sp.cm.sig V.gram (projInf D.sp.cm.sig V.gram g))
    rw [proj_ofInf]

end GlobalTheory.TrAct

open GlobalTheory.TrAct in

theorem GlobalTheory.TrAct.toInf_apply_homDS : ∀ (D : D7) (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (ρ : GA D V →* (H →L[ℂ] H)) (U : Submodule ℂ H), ∀ Φ ∈ homDS M ρ U, ∀ (g : GA D V) y, ρ (toInf V g : GA D V) (Φ y) = Φ fun τ => dsRep M τ (projArch D.sp.cm.sig V.gram (placeOf D τ) g) (y τ) := by
  intro D V S M H _ _ _ ρ U Φ hΦ g y
  classical
  haveI : Finite D.what₂.Tau := Finite.of_injective _ (placeOf_bijective D).1
  haveI : Fintype D.what₂.Tau := Fintype.ofFinite _
  have key : ∀ s : Finset D.what₂.Tau, ρ (partAt V g s) (Φ y) = Φ fun τ =>
      if τ ∈ s then dsRep M τ (projArch D.sp.cm.sig V.gram (placeOf D τ) g) (y τ) else y τ := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      have : partAt V g ∅ = 1 := by
        rw [partAt]
        have : (fun w => if w ∈ (∅ : Finset D.what₂.Tau).image (placeOf D) then
            projArch D.sp.cm.sig V.gram w g else (1 : GArch D.sp.cm.sig V.gram w)) = 1 := by
          funext w; simp
        rw [this, map_one, map_one]
      simp [this]
    | insert τ s hτ ih =>
      rw [partAt_insert V g hτ, map_mul, ContinuousLinearMap.mul_apply, ih, ← (mem_homPi.1 hΦ).2 τ]
      congr 1
      funext τ'
      by_cases e : τ' = τ
      · subst e
        simp [hτ]
      · rw [Function.update_of_ne e]
        simp [e]
  have := key Finset.univ
  rw [partAt_univ] at this
  simpa using this
