import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsAuxiliaryVectorWittDec
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceHermitianFrameProperties
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SplitLocalFrameDiagonalStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FramedCongruenceElementMemPrincipalCongruenceStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SplitPlaceTuplesOneOrbitModUniformizerPowerStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin
open ValuativeRel

namespace GlobalTheory.CosetFJ

theorem besselOrbit_at_badPlace_eq_congruenceTranslate : OnStd fun {D} _ _ {sc} {G} W F => ∀ σ (h : 2 * (σ + 1) + 2 ≤ D.R.m) (h' : 2 * σ + 2 ≤ D.R.m), ∀ v ∈ G.pl.S0, ∀ g ∈ grpAt (G.V (.grid (2 * σ + 2) 0)) (· = v), ∀ (u : UX D (σ + 1)), ∀ a ∈ (pcFB W F σ h h').A₁, MxOff (· = v) (mt (G.V (.grid (2 * σ + 2) 0)) g⁻¹ ⬝ (xFB F σ h' ⬝ u.1.1) - xFB F σ h' - a) → ∃ k ∈ lev G (.grid (2 * σ + 2) 0), k ∈ grpAt (G.V (.grid (2 * σ + 2) 0)) (· = v) ∧ MxOff (· = v) (mt (G.V (.grid (2 * σ + 2) 0)) k ⬝ xFB F σ h' - mt (G.V (.grid (2 * σ + 2) 0)) g⁻¹ ⬝ (xFB F σ h' ⬝ u.1.1)) := by
  intro D hQ T L μ0 hL sc G W M hM F hF σ h h' v hv g hg u a ha hoff
  obtain ⟨k, _, _, _, _, p, β, ι, ι', s, t, hpv, hidem, hlat, hι, hι', hιι, hX, hΦ, hA⟩ :=
    GlobalTheory.T.split_local_frame_diagonal D hQ T L μ0 hL sc G W M hM F hF σ h h' v hv
  obtain ⟨ha1, ha2⟩ := hA a ha
  subst hpv
  obtain ⟨k₀, hk₀, hoff'⟩ := GlobalTheory.T.splitPlace_tuples_one_orbit_mod_uniformizer_power D k p _ σ β (xFB F σ h') ι ι' s t (G.pl.depth sc p.v) (G.pl.depth_pos sc _) hι hι' hιι
    hX hΦ g hg u a ha1 ha2 hoff
  have hsd : IsSelfDualC (G.V (.grid (2 * σ + 2) 0)) (G.Λ (.grid (2 * σ + 2) 0)) :=
    (G.sp.V_is (2 * σ + 2) 0 (by omega) h' (Nat.zero_le _)).sd
  refine ⟨β.gl _, GlobalTheory.T.framedCongruenceElement_mem_principalCongruence D hQ T L μ0 hL sc G W M hM (.grid (2 * σ + 2) 0) hsd p.v hv k p rfl hidem _ β hlat k₀ hk₀, ?_, hoff'⟩
  exact ((GlobalTheory.FrameAt.frame_facts D k p _ _ β).1 _).2 ⟨_, rfl⟩

end GlobalTheory.CosetFJ
