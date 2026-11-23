import Mathlib
import Development.WeilBound.RepresentationTheoryGL.TubeMeasures.DisjointTubes.MassLev2
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PermMMulTranspose
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.OneMeasureSizes
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Definitions.Divisors.UnifOfSpaceEq
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.DefiniteBound
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EmbGLMemRealSU
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.CoeSelfDualLatticeInFrameCoordinatesEq
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GapAtLeast
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.VolUFactProdMulLe

open NumberField IsDedekindDomain MeasureTheory Matrix GlobalTheory.AdLat GlobalTheory.UCls GlobalTheory.SUVol ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.StandardLattice Formalism.IndefR.Lev Formalism.IndefR.Datum GlobalTheory.AdelicScalar
open GlobalTheory.CovTop.VolUp
open scoped ENNReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace MainStatements.Tam

def Stab {D : D7} (V : HSp D) : Set (GA D V) :=
  {h | ∀ y, y ∈ latHat D.host.F D.host.E (L0c D V) ↔
    (finMat D.sp.cm.sig V.gram h).mulVec y ∈ latHat D.host.F D.host.E (L0c D V)}

def KM {D : D7} (V : HSp D) (M : ℕ) : Set (GA D V) :=
  {h | IsKM (IsCMField.complexConj D.host.E) (-(V.gram)ᵀ) (GlobalTheory.Member.latC V : Set (Fin V.rank → D.host.E)) M
    ((finHom V h).1 : Matrix (Fin V.rank) (Fin V.rank) (RA (maximalRealSubfield D.host.E) D.host.E))}

def VolSt : Prop :=
  ∀ (D : D7) (V : HSp D) (P Q : ℕ), V.SigOK → (∀ τ, V.sig τ = (P, Q)) →
    ∀ (μ : Measure (GA D V)) [μ.IsHaarMeasure] (𝓕 : Set (GA D V)), IsFundamentalDomain (GQ V) 𝓕 μ →
    ∀ (θ : InfFam D) (A : Frames V) (m : ∀ ρ, Measure (Upq V ρ)) (rp : GA D V →* (∀ ρ, Upq V ρ)),
      IsInfFam θ → IsFrames V A → (∀ ρ, IsMinf (m ρ)) → Continuous rp → IsRealPart V θ A rp →
    ∀ B : Set (∀ ρ, Upq V ρ), MeasurableSet B →
      μ 𝓕 * Measure.pi m B = μ {h | h ∈ Stab V ∧ rp h ∈ B} *
        ENNReal.ofReal (ReciprocityTheory.ChartRestriction.DS.volU V.rank ^ D.R.f * massI D V.rank)

def StabSt : Prop :=
  (∀ (D : D7) (V : HSp D), Stab V = KM V 1 ∧ ∀ M, 1 ≤ M → IsOpen (KM V M)) ∧
  ∀ (D : D7) (Tu : Type) (C : Formalism.IndefR.Links.LevCh D Tu) (t0 : Tu), C.Is t0 → ∀ (i : Fin D.R.m)
    (P : Formalism.L2.DIV.LevelP C.Pg D.R.r ℂ) (h : GA D (Formalism.IndefR.Links.Wc D i)),
    finE (Formalism.IndefR.Links.Wc D i) h ∈ GlobalTheory.IndefiniteRowSideFullHecke.OneMeasureSizes.levW C i P → h ∈ Stab (Formalism.IndefR.Links.Wc D i)

def NumSt : Prop :=
  ∀ r : ℕ, 2 ≤ r → ((r : ℝ) ^ (r ^ 2))⁻¹ ≤ ReciprocityTheory.ChartRestriction.DS.volU r ∧ ReciprocityTheory.ChartRestriction.DS.volU r ≤ 13 ^ (r ^ 2)

def IdxSt : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r M : ℕ) (G : Matrix (Fin r) (Fin r) E)
    (Λ : Submodule (𝓞 E) (Fin r → E)), 1 ≤ M → SelfDualLat G Λ →
    ∃ S : Finset (Matrix (Fin r) (Fin r) (RA (maximalRealSubfield E) E)), S.card ≤ M ^ (2 * fdeg E * r ^ 2) ∧
      ∀ g, IsKM (IsCMField.complexConj E) G (Λ : Set (Fin r → E)) 1 g →
        ∃ s ∈ S, IsKM (IsCMField.complexConj E) G (Λ : Set (Fin r → E)) 1 s ∧
          ∃ k, IsKM (IsCMField.complexConj E) G (Λ : Set (Fin r → E)) M k ∧ g = s * k

def TubeSt : Prop :=
  ∀ (D : D7) (V : HSp D) (P Q : ℕ), V.SigOK → (∀ τ, V.sig τ = (P, Q)) → 2 ≤ V.rank → ∀ (M : ℕ), 3 ≤ M →
    ∀ (ι : Type) [Fintype ι] (X : ι → Data D.host.E V.rank) (g : ι → GA D V) (x0 : ∀ k, Frame (X k).Ψ V.rank),
      (∀ k k', UEquiv (IsCMField.complexConj D.host.E) (-(V.gram)ᵀ) (GlobalTheory.Member.latC V : Set (Fin V.rank → D.host.E)) M
        ((finHom V (g k)).1 : Matrix (Fin V.rank) (Fin V.rank) (RA (maximalRealSubfield D.host.E) D.host.E))
        ((finHom V (g k')).1 : Matrix (Fin V.rank) (Fin V.rank) (RA (maximalRealSubfield D.host.E) D.host.E)) → k = k') →
      (∀ k, (X k).Gm = -(V.gram)ᵀ ∧ (∀ τ, τ ∈ (X k).Ψ ↔ ∃ ρ, τ = tauE D ρ) ∧
        ((X k).Λ : Set (Fin V.rank → D.host.E)) = latOf (maximalRealSubfield D.host.E)
          ((finHom V (g k)).1 : Matrix (Fin V.rank) (Fin V.rank) (RA (maximalRealSubfield D.host.E) D.host.E))
          (GlobalTheory.Member.latC V : Set (Fin V.rank → D.host.E)) ∧
        (∀ γ, γ ∈ (X k).Γ ↔ IsUStab (X k).Gm (X k).Λ γ ∧ ∀ x ∈ (X k).Λ, ∃ y ∈ (X k).Λ,
          (γ : Matrix (Fin V.rank) (Fin V.rank) D.host.E) *ᵥ x - x = M • y) ∧ IsOrth (X k) (x0 k)) →
      ∑ k, covolume (inReal (X k).Ψ (X k).Gm (X k).Γ) (realSU (X k).Ψ (X k).Gm) (riemHaar (X k).Ψ (X k).Gm (x0 k)) ≤
        ENNReal.ofReal ((16 : ℝ) ^ (D.R.f * V.rank ^ 2) * (M : ℝ) ^ (2 * D.R.f * V.rank ^ 2) *
          (ReciprocityTheory.ChartRestriction.DS.volU V.rank ^ D.R.f * massI D V.rank))

def SizeSt : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r M : ℕ) (L : ℝ), 2 ≤ r → 1 ≤ M → 1 ≤ L →
    Real.log (fdeg E * r) ≤ L → Real.log M ≤ 30 * L → Real.log (dE E) ≤ 4 * fdeg E * L →
    1 ≤ massLev2 E r M ∧ Real.log (massLev2 E r M) ≤ 130 * (fdeg E : ℝ) * (r : ℝ) ^ 2 * L

end MainStatements.Tam

end
