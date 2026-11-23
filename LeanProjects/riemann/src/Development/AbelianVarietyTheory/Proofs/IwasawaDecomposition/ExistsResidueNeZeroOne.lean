import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.ExistenceTori.HalfLevelCoefficients
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CenLocOfCenReal
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.CoreEq
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NoFormsOff
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsRhoPtOfSplitting
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsComp
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.DepthZeroWild
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.DepthZeroSupport
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalGlobalAboveL
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsXdAllIff
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.JumpsCardOfBuilt
import Formalism.LocalToGlobal.Divisibility.ProjLemmas
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CenterEqSum
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsCompOfOne
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsBlockDiagonalWithIdentity
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG
open Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev
namespace GlobalTheory.ResThree

theorem two_ne_zero_one (g : ℕ) (hg : 3 ≤ g) : (2 : ZMod g) ≠ 0 ∧ (2 : ZMod g) ≠ 1 := by
  constructor
  · intro h
    have h' : ((2 : ℕ) : ZMod g) = 0 := by exact_mod_cast h
    rw [ZMod.natCast_eq_zero_iff] at h'
    have := Nat.le_of_dvd (by norm_num) h'
    omega
  · intro h
    have h' : ((2 : ℕ) : ZMod g) = ((1 : ℕ) : ZMod g) := by exact_mod_cast h
    rw [ZMod.natCast_eq_natCast_iff'] at h'
    rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at h'
    omega

theorem main : ∀ hL : GlobalTheory.Published.LocalLanglandsGL, AtMem hL fun _ _ _ _ w Z _ _ t _ _ c =>
    ∀ PP ∈ t.r.z.R.Pg, ∃ x : Formalism.L2.DIV.kP PP, x ≠ 0 ∧ x ≠ 1 := by
  intro hL
  refine GlobalTheory.HeightCounting.JumpsAt.evLgG_of_forall fun K B f T _ w Z Wt p0 t nch n xd c hE hR hP => ?_
  intro PP hPP
  obtain ⟨plg, iso, -, -, -, -⟩ := t.r.z.pins.keep.grp
  obtain ⟨h0, h1⟩ := two_ne_zero_one _ (GlobalTheory.IndefiniteRowSideFullHecke.HalfLevelCoefficients.three_le_g (w.st Z).toD7 (plg.symm ⟨PP, hPP⟩).1)
  have e := iso (plg.symm ⟨PP, hPP⟩)
  rw [Equiv.apply_symm_apply] at e
  exact ⟨e 2, fun h => h0 (e.injective (by rw [h, map_zero])),
    fun h => h1 (e.injective (by rw [h, map_one]))⟩

end GlobalTheory.ResThree
