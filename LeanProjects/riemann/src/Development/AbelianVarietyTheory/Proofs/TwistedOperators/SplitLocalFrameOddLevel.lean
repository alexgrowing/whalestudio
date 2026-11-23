import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsAuxiliaryVectorWittDec
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceHermitianFrameProperties
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsSplitPointBesselStaircaseLatticeFrameStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.BesselStepBasePointScaledCoordinatesStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SplitFrameOddLatticeLeftStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SplitFrameOddLatticeRightStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin
open ValuativeRel

namespace GlobalTheory.AscFin.FrameBF

theorem frame_bf : OnStd fun {D} _ _ {sc} {G} W F => ∀ σ (h : 2 * (σ + 1) + 2 ≤ D.R.m), ∀ v ∈ G.pl.S0,
  ∃ (k : Type) (_ : Field k) (_ : ValuativeRel k) (_ : TopologicalSpace k) (_ : IsNonarchimedeanLocalField k)
    (p : GlobalTheory.FinPl.SplitPt D k) (β : GlobalTheory.FinPl.Frame p (G.V (.grid (2 * (σ + 1) + 1) 0)) (Fin (G.V (.grid (2 * (σ + 1) + 1) 0)).rank))
    (ι ι' : Fin (σ + 1) → Fin (G.V (.grid (2 * (σ + 1) + 1) 0)).rank) (s t : Fin (σ + 1) → k),
  p.v = v ∧ Formalism.L2.NTheta.IsIdemAt p.e (G.pl.w v) ∧
  β.IsLat (G.Λ (.grid (2 * (σ + 1) + 1) 0)) (Submodule.pi Set.univ fun _ => (1 : Submodule 𝒪[k] k)) ∧
  Function.Injective ι ∧ Function.Injective ι' ∧ (∀ a b, ι' b ≠ ι a) ∧
  (∀ q, s q • (β.b' *ᵥ fun i => p.pr (xZero (F.dJ (σ + 1) h) i q)) = Pi.single (ι q) 1) ∧
  (∀ q, t q • ((fun i => p.pr (cA D (xZero (F.dJ (σ + 1) h) i q))) ᵥ*
    ((G.V (.grid (2 * (σ + 1) + 1) 0)).gram.map (fun c => p.pr (incA D c)) * β.b)) = Pi.single (ι' q) 1) ∧
  ∀ a ∈ (pcBF W F (σ + 1) h).A₁,
    (∀ q i, ∃ z ∈ IsLocalRing.maximalIdeal 𝒪[k] ^ G.pl.depth sc v, (z : k) = s q * (β.b' *ᵥ fun j => p.pr (a j q)) i) ∧
    (∀ q i, ∃ z ∈ IsLocalRing.maximalIdeal 𝒪[k] ^ G.pl.depth sc v, (z : k) = t q * ((fun j => p.pr (cA D (a j q))) ᵥ*
      ((G.V (.grid (2 * (σ + 1) + 1) 0)).gram.map (fun c => p.pr (incA D c)) * β.b)) i) := by
  intro D hq T L μ0 hL sc G W M hM F hF σ h v hv
  obtain ⟨k, i1, i2, i3, i4, p, β, ϖ, κ, h1, h2, h3, h4, h5, h6, h7⟩ := GlobalTheory.T.exists_splitPoint_besselStaircaseLattice_frame D hq T L μ0 hL sc G W M hM F hF σ h v hv
  obtain ⟨s, t, hs, ht⟩ := GlobalTheory.T.besselStep_basePoint_scaled_coordinates D hq T L μ0 hL sc G W M hM F hF σ h v hv k p β ϖ κ h1 h2 h3 h4 h5 h6 h7
  refine ⟨k, i1, i2, i3, i4, p, β, fun q => κ ⟨q.1, by omega⟩, fun q => κ ⟨2 * (σ + 1) - 1 - q.1, by omega⟩, s, t,
    h1, h2, h3, ?_, ?_, ?_, hs, ht, fun a ha =>
      ⟨GlobalTheory.T.split_frame_odd_lattice_left D hq T L μ0 hL sc G W M hM F hF σ h v hv k p β ϖ κ h1 h2 h3 h4 h5 h6 h7 s hs a ha,
       GlobalTheory.T.split_frame_odd_lattice_right D hq T L μ0 hL sc G W M hM F hF σ h v hv k p β ϖ κ h1 h2 h3 h4 h5 h6 h7 t ht a ha⟩⟩
  · intro a b e
    exact Fin.ext (Fin.mk.inj (h5 e))
  · intro a b e
    have := Fin.mk.inj (h5 e)
    have ha := a.2; have hb := b.2
    exact Fin.ext (by omega)
  · intro a b e
    have := Fin.mk.inj (h5 e)
    have ha := a.2; have hb := b.2
    omega

end GlobalTheory.AscFin.FrameBF
