import Formalism.LocalToGlobal.ClassRec
import Formalism.LocalToGlobal.GaloisLevelStructure.DefsAut
import Formalism.LocalToGlobal.UnitaryNorms.CharTransport

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions NumberField IsDedekindDomain
open scoped TensorProduct

namespace Formalism.L2

namespace SelJ

variable {D : D7} {X : Col.Fields}

def oEq (s : Ker.Seam D X) : 𝓞 X.E ≃+* 𝓞 D.host.E := RingOfIntegers.mapRingEquiv s.iE

def Carried (s : Ker.Seam D X) (P : HeightOneSpectrum (𝓞 X.E)) (P' : HeightOneSpectrum (𝓞 D.host.E)) : Prop :=
  P'.asIdeal = P.asIdeal.map (oEq s)

def IsPlIdemX (e : DIV.AfE X.F X.E) (P : HeightOneSpectrum (𝓞 X.E)) : Prop :=
  e * e = e ∧ ∀ x : 𝓞 X.E, x ≠ 0 →
    (x ∈ P.asIdeal ↔ e * (((x : X.E)⁻¹) ⊗ₜ[X.F] (1 : FiniteAdeleRing (𝓞 X.F) X.F)) ∉ DIV.RInt X.F X.E)

def locX (e : DIV.AfE X.F X.E) (k : X.E) : DIV.AfE X.F X.E :=
  1 + e * (k ⊗ₜ[X.F] (1 : FiniteAdeleRing (𝓞 X.F) X.F) - 1)

end SelJ

section

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : MainNotions.G.Inst D L} {Gl : MainNotions.G.LatInst D} {K : MainNotions.G.Consts} {Y : DivX D}
  {cX : ExtraC} {ex : Extra D L hT Gi Gl K Y cX}

def SelIn (R : RecT ex) (Side : Set (HeightOneSpectrum (𝓞 D.host.E))) : Prop :=
  ∀ μ, ∀ P ∈ Col.QE R.T.ker.sel (R.T.ker.tup μ : DIV.Chr R.T.ker.X.F R.T.ker.X.E R.T.ker.X.K),
    ∀ P', SelJ.Carried R.T.ker.seam P P' → P' ∈ Side

def GSide (R : RecT ex) : Prop :=
  ∀ (i : Fin 2) (P' : HeightOneSpectrum (𝓞 D.host.E)),
    (∃ P ∈ R.T.ker.Pr.vG i, SelJ.Carried R.T.ker.seam P P') ↔ P' ∈ Set.range (D.naut.plGw i)

def SelSidePq (R : RecT ex)
    (Pq : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E)) → HeightOneSpectrum (𝓞 D.host.E)) : Prop :=
  (∀ v, NG.OverPl (Pq v) v) ∧ SelIn R (Set.range Pq)

def SelSideQ (R : RecT ex) : Prop :=
  ∃ Pq : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E)) → HeightOneSpectrum (𝓞 D.host.E), SelSidePq R Pq

def SelSide (R : RecT ex) : Prop := SelSideQ R ∧ GSide R

def KerTupTie (R : RecT ex) : Prop :=
  ∀ (μ : D.what₂.Tup) (P : HeightOneSpectrum (𝓞 R.T.ker.X.E)) (P' : HeightOneSpectrum (𝓞 D.host.E)),
    SelJ.Carried R.T.ker.seam P P' → ∀ e, SelJ.IsPlIdemX e P →
      ∀ (k : R.T.ker.X.Eˣ) (x : (DIV.AfE R.T.ker.X.F R.T.ker.X.E)ˣ), (x : DIV.AfE R.T.ker.X.F R.T.ker.X.E) = SelJ.locX e (k : R.T.ker.X.E) →
        R.T.ker.seam.σ₀ (((R.T.ker.tup μ : DIV.Chr R.T.ker.X.F R.T.ker.X.E R.T.ker.X.K) x : R.T.ker.X.Kˣ) : R.T.ker.X.K) =
          (((R.T.n.tp.xi μ).locK P' (Units.map R.T.ker.seam.iE.toRingHom.toMonoidHom k) : ℂˣ) : ℂ)

def KerMu0Tie (R : RecT ex) : Prop :=
  ∀ j : Fin D.R.m, R.T.ker.glob.mu0 j = Host.CT.transport R.T.ker.seam.iE (R.T.n.cf.mu0 j)

end

end Formalism.L2
