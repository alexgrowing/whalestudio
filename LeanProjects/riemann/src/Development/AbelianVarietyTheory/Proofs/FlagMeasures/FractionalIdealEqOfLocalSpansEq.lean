import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.NGData
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.TermLoc
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.LocClosed
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.LocFacts
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.SaturatedPf
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Ia

open scoped Classical ENNReal
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.Unfold
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section

namespace GlobalTheory.Sloc.OneDim

theorem nV_pos (D : D7) : 0 < nV D := by
  have h := D.sp.Y_rank 0 (Nat.zero_le _)
  have hk := D.R.m_add_three_le_k
  have hm := D.R.two_le_m
  show 0 < (D.sp.Y 0).rank
  rw [h]
  simp only [Formalism.BasicNotions.Ranks.rankY, Formalism.BasicNotions.Ranks.r, zero_mul, add_zero]
  omega

def lineMap (D : D7) : D.host.E →ₗ[𝓞 D.host.E] (VS D).V :=
  (LinearMap.toSpanSingleton D.host.E (VS D).V ((VS D).frame ⟨0, nV_pos D⟩)).restrictScalars (𝓞 D.host.E)

theorem lineMap_injective (D : D7) : Function.Injective (lineMap D) := by
  intro a b h
  have h' : a • (VS D).frame ⟨0, nV_pos D⟩ = b • (VS D).frame ⟨0, nV_pos D⟩ := h
  exact smul_left_injective D.host.E ((VS D).frame.ne_zero _) h'

theorem localLattice_map (D : D7) (Z : LocDat D) (p : PlF D) (K : Submodule (𝓞 D.host.E) D.host.E) :
    lattice₂ D Z.M p (K.map (lineMap D)) =
      (Submodule.span (Z.M p).L.O ((D.s.atP p).ιE '' (K : Set D.host.E))).map
        ((LinearMap.toSpanSingleton (D.s.atP p).Ep (Vp D p) (Pi.single ⟨0, nV_pos D⟩ 1)).restrictScalars (Z.M p).L.O) := by
  have key : ∀ k : D.host.E, baseChange₂ D p (lineMap D k) =
      LinearMap.toSpanSingleton (D.s.atP p).Ep (Vp D p) (Pi.single ⟨0, nV_pos D⟩ 1) ((D.s.atP p).ιE k) := by
    intro k
    have h1 : lineMap D k = k • (VS D).frame ⟨0, nV_pos D⟩ := rfl
    rw [h1, baseChange_smul₂, baseChangeAt_frame, LinearMap.toSpanSingleton_apply]
  unfold Formalism.L2.SG.TermLoc.lattice₂
  rw [Submodule.map_span]
  congr 1
  ext v
  simp only [Submodule.map_coe, Set.mem_image, SetLike.mem_coe, LinearMap.coe_restrictScalars]
  constructor
  · rintro ⟨x, ⟨k, hk, rfl⟩, rfl⟩
    exact ⟨(D.s.atP p).ιE k, ⟨k, hk, rfl⟩, (key k).symm⟩
  · rintro ⟨y, ⟨k, hk, rfl⟩, rfl⟩
    exact ⟨lineMap D k, ⟨k, hk, rfl⟩, key k⟩

private theorem le_of_locP_eq_forall_heightOneSpectrum {D : D7} {A B : Submodule (𝓞 D.host.E) (VS D).V}
    (h : ∀ P : IsDedekindDomain.HeightOneSpectrum (𝓞 D.host.E),
      Formalism.HermitianLatticesTheory.localization₂ P.asIdeal A = Formalism.HermitianLatticesTheory.localization₂ P.asIdeal B) : A ≤ B := by
  intro x hx
  by_contra hxB
  let c : Ideal (𝓞 D.host.E) := B.comap (LinearMap.toSpanSingleton (𝓞 D.host.E) (VS D).V x)
  have hc : c ≠ ⊤ := by
    intro htop
    have h1 : (1 : 𝓞 D.host.E) ∈ c := htop ▸ Submodule.mem_top
    apply hxB
    simpa [c, LinearMap.toSpanSingleton_apply] using h1
  obtain ⟨M, hM, hcM⟩ := Ideal.exists_le_maximal c hc
  let P : IsDedekindDomain.HeightOneSpectrum (𝓞 D.host.E) :=
    ⟨M, hM.isPrime, (Ideal.bot_lt_of_maximal M (NumberField.RingOfIntegers.not_isField D.host.E)).ne'⟩
  have hxA : x ∈ Formalism.HermitianLatticesTheory.localization₂ P.asIdeal A :=
    show ∃ s ∈ P.asIdeal.primeCompl, s • x ∈ A from ⟨1, P.asIdeal.primeCompl.one_mem, by rwa [one_smul]⟩
  rw [h P] at hxA
  obtain ⟨s, hs, hsx⟩ : ∃ s ∈ P.asIdeal.primeCompl, s • x ∈ B := hxA
  exact hs (hcM (show s ∈ c by simpa [c, LinearMap.toSpanSingleton_apply] using hsx))

end GlobalTheory.Sloc.OneDim

open GlobalTheory.Sloc.OneDim in

theorem GlobalTheory.Sloc.fg_eq_of_completions : ∀ (D : D7) (Z : LocDat D) (I J : Submodule (𝓞 D.host.E) D.host.E), I.FG → J.FG → (∀ p : PlF D, Submodule.span (Z.M p).L.O ((D.s.atP p).ιE '' (I : Set D.host.E)) = Submodule.span (Z.M p).L.O ((D.s.atP p).ιE '' (J : Set D.host.E))) → I = J := by
  intro D Z I J hI hJ hloc
  have hlat : ∀ p : PlF D, lattice₂ D Z.M p (I.map (lineMap D)) = lattice₂ D Z.M p (J.map (lineMap D)) := by
    intro p
    rw [localLattice_map, localLattice_map, hloc p]
  have hEq := Formalism.L2.SG.Pf.locEqC_holds D Z
  unfold Formalism.L2.SG.Pf.LocEqC at hEq
  have hP : ∀ P : IsDedekindDomain.HeightOneSpectrum (𝓞 D.host.E),
      Formalism.HermitianLatticesTheory.localization₂ P.asIdeal (I.map (lineMap D)) = Formalism.HermitianLatticesTheory.localization₂ P.asIdeal (J.map (lineMap D)) := by
    intro P
    let p : PlF D := ⟨P.asIdeal.comap (algebraMap (𝓞 D.host.F) (𝓞 D.host.E)), Ideal.comap_isPrime _ _,
      fun h => P.ne_bot (Ideal.eq_bot_of_comap_eq_bot h)⟩
    exact (hEq p _ _ (hI.map _) (hJ.map _)).1 (hlat p) P rfl
  have hAB : I.map (lineMap D) = J.map (lineMap D) :=
    le_antisymm (OneDim.le_of_locP_eq_forall_heightOneSpectrum hP) (OneDim.le_of_locP_eq_forall_heightOneSpectrum fun P => (hP P).symm)
  exact Submodule.map_injective_of_injective (lineMap_injective D) hAB
