import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsBaseEnlargementFixedCoefFieldOfCoeffEnlargemen
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CrdOver
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsReferenceTupleThetaComparisonNormalisedDat
import Formalism.LocalToGlobal.IndefiniteReal.LinksW

set_option autoImplicit false

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr
open Formalism.IndefR.FWT Formalism.L2.Pj GlobalTheory.RealGeo

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.R3.Rw.OmExt

section Generic

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}

set_option maxHeartbeats 1000000 in

theorem exists_omPins_lev (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F)
    (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec)
    (hR : PreChar R) (hv : Formalism.L2.Host.ValLL D R.C) (ht : TieIn T R κ v₀) (hpb : T.pb = R.C.P.pb) (hG : QGuard R)
    (hV : ∀ i, VStd D i)
    (lev : ∀ i : Fin D.R.m, G → (T.Q.Dw ((i : ℕ) + 1)).La →ₗ[𝓞 D.host.E] (T.Q.Dw ((i : ℕ) + 1)).La)
    (hlev : ∀ i, LevIs R i (iotaW T i) T.Q.l.M (Mfr T.Q.l) (lev i)) :
    ∃ O : ∀ i, OMDat T.toCore R i Unit (fun _ => A.μ0), (∀ i, OMPins T R κ v₀ O i) ∧ ∀ i, (O i).lev = lev i := by
  choose O hF hO using fun i => GlobalTheory.RefPins.exists_pins_ref T R κ v₀ hR hv ht hpb hG i (hV i)
  refine ⟨fun i => { O i with lev := lev i }, fun i => ⟨hF i, ?_⟩, fun _ => rfl⟩
  have hact := fun c => GlobalTheory.LevelActFromLevel.actLev_of_levIs D G Pl0 T0 A T R hR.lev ht.laws hpb i c (lev i) (hlev i)
  have h := hO i
  exact ⟨⟨h.lift.field, h.lift.std, h.lift.v0, h.lift.c0, hlev i⟩, h.tuple, ⟨hact _, hact _⟩, h.bad, h.reps, h.ep, h.io, h.w,
    h.cov, h.cxi, h.model₂⟩

variable (D) in

def LevOver (i : Fin D.R.m) (Pg : Finset (Formalism.L2.DIV.Pl D.host.E)) (βW : ∀ i, GL (Fin (Wc D i).rank) (EAf D)) {G : Type}
    (eG : G → G0 Pg D.R.r) {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E} (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H)
    (Dw : ℕ → ReciprocityTheory.ChartRestriction.G.Geo.Tor.Datum H) (iota : ∀ j : ℕ, (Dw j).La →ₗ[𝓞 D.host.E] (Fin D.R.r → D.host.E))
    (lev : G → (Dw ((i : ℕ) + 1)).La →ₗ[𝓞 D.host.E] (Dw ((i : ℕ) + 1)).La) : Prop :=
  ∀ g, ∃ κ, Lev.IsLevelLift (Wc D i) (βW i)
      (datY _ D.R.r D.R.t 0 (r_le_rank_Wc i) Pg ∅ (LevelP.triv _ _ _) (fun _ _ => 1) (fun _ => 1) Frm.B) (eG g) κ ∧
    ∀ a ∈ Mfr l • (⊤ : Submodule (𝓞 D.host.E) (Dw ((i : ℕ) + 1)).La), ∃ w ∈ latGHat (Wc D i) 1,
      finVec (Wc D i) ((LinearMap.funLeft (𝓞 D.host.E) D.host.E (Fin.cast (rank_Wc i)) ∘ₗ iota ((i : ℕ) + 1)) (lev g a)) -
        (finHom (Wc D i) κ).1.mulVec
          (finVec (Wc D i) ((LinearMap.funLeft (𝓞 D.host.E) D.host.E (Fin.cast (rank_Wc i)) ∘ₗ iota ((i : ℕ) + 1)) a)) = l.M • w

theorem levOver_iff (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (i : Fin D.R.m)
    (lev : G → (T.Q.Dw ((i : ℕ) + 1)).La →ₗ[𝓞 D.host.E] (T.Q.Dw ((i : ℕ) + 1)).La) :
    LevOver D i R.Pg R.βW R.eG T.Q.l T.Q.Dw T.iota lev ↔ LevIs R i (iotaW T i) T.Q.l.M (Mfr T.Q.l) lev := Iff.rfl

theorem levOver_cast {S₁ S₂ : Finset (HeightOneSpectrum (𝓞 D.host.E))} {Pg₁ Pg₂ : Finset (Formalism.L2.DIV.Pl D.host.E)}
    {β₁ β₂ : ∀ i, GL (Fin (Wc D i).rank) (EAf D)}
    {e₁ : Formalism.L2.Col.G0 D.host.E S₁ D.R.r ≃* G0 Pg₁ D.R.r} {e₂ : Formalism.L2.Col.G0 D.host.E S₂ D.R.r ≃* G0 Pg₂ D.R.r}
    {H₁ H₂ : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E} {l₁ : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H₁} {l₂ : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H₂}
    {Dw₁ : ℕ → ReciprocityTheory.ChartRestriction.G.Geo.Tor.Datum H₁} {Dw₂ : ℕ → ReciprocityTheory.ChartRestriction.G.Geo.Tor.Datum H₂}
    {ι₁ : ∀ j : ℕ, (Dw₁ j).La →ₗ[𝓞 D.host.E] (Fin D.R.r → D.host.E)}
    {ι₂ : ∀ j : ℕ, (Dw₂ j).La →ₗ[𝓞 D.host.E] (Fin D.R.r → D.host.E)}
    (hS : S₂ = S₁) (hP : HEq Pg₂ Pg₁) (hβ : HEq β₂ β₁) (he : HEq e₂ e₁) (hH : HEq H₂ H₁) (hl : HEq l₂ l₁) (hD : HEq Dw₂ Dw₁)
    (hι : HEq ι₂ ι₁)
    (lev₁ : ∀ i : Fin D.R.m, Formalism.L2.Col.G0 D.host.E S₁ D.R.r → (Dw₁ ((i : ℕ) + 1)).La →ₗ[𝓞 D.host.E] (Dw₁ ((i : ℕ) + 1)).La)
    (h : ∀ i, LevOver D i Pg₁ β₁ e₁ l₁ Dw₁ ι₁ (lev₁ i)) :
    ∃ lev₂ : ∀ i : Fin D.R.m, Formalism.L2.Col.G0 D.host.E S₂ D.R.r → (Dw₂ ((i : ℕ) + 1)).La →ₗ[𝓞 D.host.E] (Dw₂ ((i : ℕ) + 1)).La,
      (∀ i, LevOver D i Pg₂ β₂ e₂ l₂ Dw₂ ι₂ (lev₂ i)) ∧ ∀ i i' : Fin D.R.m, (i : ℕ) = i' → HEq (lev₂ i') (lev₁ i) := by
  subst hS
  cases hP; cases hβ; cases he; cases hH; cases hl; cases hD; cases hι
  exact ⟨lev₁, h, fun i i' e => by obtain rfl := Fin.ext e; exact HEq.rfl⟩

def CoefFam {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks)
    (c0L : ∀ i : Fin D.R.m, VsV D i D.what₂.LL →ₛₗ[D.what₂.embLL] (R.cV i).W) : Prop :=
  ∃ gramR c0R, Bridge.FamTie R.B R.pl (R.Sb : Set (Formalism.L2.DIV.Pl D.host.E)) R.Q (labLL D) (fun τ => Bridge.lamRdef (Ptw D) τ)
    (fun i τ => Bridge.lamLdef (Vc D i).rank ((i : ℕ) + 1) τ) gramR c0R c0L

end Generic

end GlobalTheory.Mem.R3.Rw.OmExt

end
