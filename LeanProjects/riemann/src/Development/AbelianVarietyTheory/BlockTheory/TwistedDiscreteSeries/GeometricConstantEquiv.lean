import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.FWTie
import Formalism.LocalToGlobal.ProjectiveLattices.ThClassPins

noncomputable section

open NumberField IsDedekindDomain

namespace GlobalTheory.IndefiniteRowSideFullHecke.GeometricConstantEquiv

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT Formalism.L2.Pj

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
  (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (i : Fin D.R.m) (w : WeightFamilies.Wt D ((i : ℕ) + 1))

abbrev Cusp : Type := T.cuspA ((i : ℕ) + 1) (wtA w) w.n

abbrev res (σ : D.what₂.LL →+* ℂ) : T.Q.c.F →+* ℂ := σ.comp (algebraMap T.Q.c.F D.what₂.LL)

def iotaW : (T.Q.Dw ((i : ℕ) + 1)).La →ₗ[𝓞 D.host.E] (Fin (Wc D i).rank → D.host.E) :=
  LinearMap.funLeft (𝓞 D.host.E) D.host.E (Fin.cast (rank_Wc i)) ∘ₗ T.iota ((i : ℕ) + 1)

def IsLift (g : G) (κ : GA D (Wc D i)) : Prop :=
  Lev.IsLevelLift (Wc D i) (R.βW i) (R.datWp i R.triv) (R.eG g) κ

def IsGeo (ρ : G →* Module.End T.Q.c.F (Cusp T i w)) : Prop :=
  ∃ lev : G → (T.Q.Dw ((i : ℕ) + 1)).La →ₗ[𝓞 D.host.E] (T.Q.Dw ((i : ℕ) + 1)).La,
    LevIs R i (iotaW T i) T.Q.l.M (T.Q.l.Mb.map (T.Q.H.bar : 𝓞 D.host.E →+* 𝓞 D.host.E)) lev ∧
    ActLev (Xo := T.Q.Xo ((i : ℕ) + 1)) T.Q.c (fun g => (lev g, LinearMap.id)) ∧
    ∀ g (f : Cusp T i w), ((ρ g f : Cusp T i w) : T.R ((i : ℕ) + 1)) =
      actLev (Xo := T.Q.Xo ((i : ℕ) + 1)) T.Q.c (fun g => (lev g, LinearMap.id)) g (f : T.R ((i : ℕ) + 1))

def ReadTwist (ρ : G →* Module.End T.Q.c.F (Cusp T i w)) : Prop :=
  ∀ σ : D.what₂.LL →+* ℂ, GoodEmb T.Q.c (res T σ) → ∀ hV : T.V ((i : ℕ) + 1) (res T σ) = Wc D i,
    ∀ (g : G) (κ : GA D (T.V ((i : ℕ) + 1) (res T σ))), IsLift T R i g (cast (congrArg (GA D) hV) κ) →
      ∀ (f : Cusp T i w) (x : GA D (T.V ((i : ℕ) + 1) (res T σ))),
        T.phiJ ((i : ℕ) + 1) (res T σ) (wtA w) ((ρ g f : Cusp T i w) : T.R ((i : ℕ) + 1)) x =
          σ (((R.FW i).chi g : D.what₂.LLˣ) : D.what₂.LL) *
            T.phiJ ((i : ℕ) + 1) (res T σ) (wtA w) (f : T.R ((i : ℕ) + 1)) (x * κ)

def IsIntegralForm (f : Cusp T i w) : Prop :=
  ∀ (la : HeightOneSpectrum (𝓞 T.Q.c.F)) (y : T.PtM ((i : ℕ) + 1) la),
    T.nrmM ((i : ℕ) + 1) la y (f : T.R ((i : ℕ) + 1)) ≤ 1

def KeepsIntegral (ρ : G →* Module.End T.Q.c.F (Cusp T i w)) : Prop :=
  ∀ g f, IsIntegralForm T i w f → IsIntegralForm T i w (ρ g f)

def ConstEquiv : Prop :=
  ∀ σ : D.what₂.LL →+* ℂ, GoodEmb T.Q.c (res T σ) → ∀ hV : T.V ((i : ℕ) + 1) (res T σ) = Wc D i,
    ∀ ρ : G →* Module.End T.Q.c.F (Cusp T i w), IsGeo T R i w ρ →
    ∀ chi : G →* (T.Q.c.F)ˣ,
      (∀ g, algebraMap T.Q.c.F D.what₂.LL (chi g : T.Q.c.F) = (((R.FW i).chi g : D.what₂.LLˣ) : D.what₂.LL)) →
    ∀ ℓ : G → GA D (T.V ((i : ℕ) + 1) (res T σ)), (∀ g, IsLift T R i g (cast (congrArg (GA D) hV) (ℓ g))) →
      CEquiv (T.V ((i : ℕ) + 1) (res T σ)) (res T σ)
        ((rdU (T.U ((i : ℕ) + 1) (res T σ))).comp (T.cuspA ((i : ℕ) + 1) (wtA w) w.n).subtype)
        (T.dict ((i : ℕ) + 1) (res T σ)) (T.mu ((i : ℕ) + 1) (res T σ)) (T.cE ((i : ℕ) + 1) (res T σ)) ρ chi ℓ

omit [Algebra T.Q.c.F D.what₂.LL] in

def IsKappa : Prop :=
  ∀ τ : D.what₂.Tau,
    (∀ k : Fin (D.R.sigW ((i : ℕ) + 1)).1, w.aP τ k = aPl D i ((Wc D i).sig (tauE D τ)).1 τ k) ∧
    (∀ k : Fin (D.R.sigW ((i : ℕ) + 1)).2,
      w.aM τ k = aMi D i ((Wc D i).sig (tauE D τ)).1 ((Wc D i).sig (tauE D τ)).2 τ k) ∧ w.n = D.R.nV

def GeoActAt : Prop :=
  ∃ ρ : G →* Module.End T.Q.c.F (Cusp T i w), IsGeo T R i w ρ ∧ ReadTwist T R i w ρ ∧ KeepsIntegral T i w ρ

def GeoAct : Prop :=
  ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m)
    (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F),
    LawsJ T →
    (∀ x : 𝓞 T.Q.c.F, algebraMap T.Q.c.F D.what₂.LL (x : T.Q.c.F) = D.what₂.OtoLL (T.Q.eO x)) →
    R.toLevCh.Is A.μ0 → R.grp_chiW → ChiR T R →
    ∀ (i : Fin D.R.m) (w : WeightFamilies.Wt D ((i : ℕ) + 1)), IsKappa i w → ConstEquiv T R i w → GeoActAt T R i w

theorem IsGeo.exists_lift {ρ : G →* Module.End T.Q.c.F (Cusp T i w)} (h : IsGeo T R i w ρ) (g : G) :
    ∃ κ, IsLift T R i g κ := by
  obtain ⟨lev, hl, -⟩ := h
  obtain ⟨κ, hκ, -⟩ := hl g
  exact ⟨κ, hκ⟩

end GlobalTheory.IndefiniteRowSideFullHecke.GeometricConstantEquiv
