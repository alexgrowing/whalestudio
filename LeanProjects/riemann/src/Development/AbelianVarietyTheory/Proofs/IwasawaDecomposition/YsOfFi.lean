import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CenUsedOfCenReal
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SettingsFormsExistList
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.OmPinsTr
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SideTw
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdmissibleTwistOfTwistingCharacter
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.KeepSideBMtVPlaces
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SideBTies

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.StandardLattice Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2 Formalism.L2.Host Formalism.L2.DIV Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.TwInputs GlobalTheory.SeriesTie GlobalTheory.ExportSeries NumberField IsDedekindDomain
open Formalism.MainNotions.IntegralHeckeForms (TwOK HkIdx)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000

namespace GlobalTheory.HeightCounting.SerCopy

def NoOff (D : D7) : Prop := ∀ i j b, ¬ (1 ≤ j ∧ j ≤ D.R.m) → Subsingleton (D.nexp.Fm i j b)

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type}
  [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

def HkAd (R : RealDat3 D A3 Ks) (Sb : Finset (PlE D.host))
    (hL : ∀ j, ℕ → PlE D.host → Module.End D.what₂.LL (Fin (R.nW (idxOf D j)) → D.what₂.LL)) : Prop :=
  ∀ j k P α Rr, 1 ≤ j → j ≤ D.R.m → HkDat R Sb (idxOf D j) k P α Rr → ∀ x : Fin (R.nW (idxOf D j)) → D.what₂.LL,
    (R.HW (idxOf D j) (sg0 D A3.A)).e ((R.FW (idxOf D j)).j (sg0 D A3.A) (hL j k P x)) =
      hkNorm R (idxOf D j) k P • Mult.heckeOn (R.MW (idxOf D j) (sg0 D A3.A)) Rr
        ((R.HW (idxOf D j) (sg0 D A3.A)).e ((R.FW (idxOf D j)).j (sg0 D A3.A) x))

variable {R : RealDat3 D A3 Ks} {cG : G0 R.Pg D.R.r ≃* G0g D.nd}

def ysOf {kKs : Ks →+* ↥D.LL0} {hk : ∀ x : Ks, ((kKs x : ↥D.LL0) : D.what₂.LL) = algebraMap Ks D.what₂.LL x} {cf Rw low Pq hL eig θ}
    (Bs : SideB D cf Rw low Pq (ratDatR R cG kKs hk) hL eig θ) : NExpRealS R cG (ratDatR R cG kKs hk) where
  fi := fun i => SideTies.fiOf R (idxOf D ((i : ℕ) + 1)) i (idxOf_succ D i)
  geq := fun i g => congrArg (fun y => cG (R.eG y)) (SideTies.fiOf_eG R _ i (idxOf_succ D i) g)
  rho := Bs.rho
  chi := Bs.chiL
  eF := Bs.eF
  bsup := fun i j b h1 h2 => ⟨1, one_ne_zero, fun x hx => by
    rw [one_smul]; exact (Bs.bsup i j b h1 h2 x).1 hx, fun x hx => by
    rw [one_smul]; exact (Bs.bsup i j b h1 h2 x).2 hx⟩
  act := Bs.act

theorem ysOf_fi {kKs : Ks →+* ↥D.LL0} {hk : ∀ x : Ks, ((kKs x : ↥D.LL0) : D.what₂.LL) = algebraMap Ks D.what₂.LL x}
    {cf Rw low Pq hL eig θ} (Bs : SideB D cf Rw low Pq (ratDatR R cG kKs hk) hL eig θ) (i x) : HEq (((ysOf Bs).fi i).e x) x :=
  SideTies.fiOf_heq _ _ _ _ x

variable {S : RatDat D.ntw}

set_option genInjectivity false in
set_option genSizeOfSpec false in

structure PreTie (YS : NExpRealS R cG S) (v₀ : ∀ (j : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW j σ).Vec) (X : NExpTied D)
    (hF : D.host.F = maximalRealSubfield D.host.E)
    (Pq : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E)) → PlE D.host) : Type 1 where
  Dat : D.ntw.Tw → ℕ → Bool → Type
  th : ∀ i j b, Dat i j b → D.nexp.Fm i j b
  lev : ∀ i j b, Dat i j b → Finset (PlE D.host)
  thPsi : ∀ i j b k (_ : Finset (PlE D.host)) (_ : Formalism.ConjugateSelfDual.G D.host.E D.nd.Om →* (D.ntw.Ok i k)ˣ), Dat i j b →
    Set (D.ntw.Ok i k ⊗[D.ntw.O i] D.nexp.Fm i j b)
  h1 : ∀ i j b k (d : Dat i j b), thPsi i j b k ∅ 1 d = {(1 : D.ntw.Ok i k) ⊗ₜ[D.ntw.O i] th i j b d}
  thU : ∀ i j b (Q : Finset (PlE D.host)) (M : ℕ), Dat i j b →
    D.nexp.Fm i j b ⊗[D.ntw.O i] AddMonoidAlgebra (D.ntw.O i) (DelQM D.host (D.ntw.l i) Q M)
  thP : ∀ i j b k Q ψ, D.nexp.MtV i j b k Q ψ →ₗ[D.ntw.Ok i k] (D.ntw.Ok i k ⊗[D.ntw.O i] D.nexp.Fm i j b)
  MtLat : ∀ i j b k Q ψ, Submodule (D.ntw.Ok i k) (D.nexp.MtV i j b k Q ψ)
  h2 : ∀ i j b k Q ψ, (MtLat i j b k Q ψ).FG
  h3 : ∀ i j b k Q ψ,
    Submodule.span (FractionRing (D.ntw.Ok i k)) (MtLat i j b k Q ψ : Set (D.nexp.MtV i j b k Q ψ)) = ⊤
  ρ : Setup D.ntw
  good : ρ.Good
  pin : RealPin R cG ρ
  vec : ∀ j, FWT.IsChosenExtremalVector R.toRealDat j (sg0 D A3.A) (v₀ j _)
  ν : D.ntw.Tw → Fin D.R.m → Bool → ℂ
  scalar : ∀ i j b, IsScalar YS v₀ good i j b (ν i j b)
  tie : Comparison₂ good (Y := keepEx D Dat th lev thPsi h1 thU thP MtLat h2 h3) fun i j b => realRd YS v₀ good i j b (ν i j b)
  hecke : ∀ i j b, HeckeTie (realRd YS v₀ good i j b (ν i j b))
  bad : ∀ i, ρ.bad i = normProd (D.ntw.S0 i)
  ch : ∀ i P, IsSplitPl D.host P → (P ∈ ρ.ch i ↔ P ∈ Set.range Pq)
  join : ∀ PV : ∀ j : Fin D.R.m, principalLevelFrame.RowPsi (Vc D j) D.R.nV, (∀ j, GlobalTheory.MtRead.IdFrame hF (PV j)) →
    ∀ i (j : Fin D.R.m) b k Q ψ (hA : NX.AdmTw D i k Q ψ), TwOK i k Q ψ →
      ∃ ω : (X.mtV i (j.1 + 1) b k Q ψ (by omega) (by omega) hA).W →ₛₗ[ρ.ek i b k] PolF D (Wc D j).rank (Vc D j).rank,
        Function.Injective ω ∧ ∀ f g, (tie i j b).rdV k Q ψ f ((finHom _).rangeRestrict ((PV j).ψ g)) =
          ω (((X.mtV i (j.1 + 1) b k Q ψ (by omega) (by omega) hA).real f).1 g)

namespace PreTie

variable {YS : NExpRealS R cG S} {v₀ : ∀ (j : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW j σ).Vec} {X : NExpTied D} {hF Pq}
  (p : PreTie YS v₀ X hF Pq)

abbrev ex : NExp D.R D.host D.what₂ D.LL0 D.nd D.ntw := keepEx D p.Dat p.th p.lev p.thPsi p.h1 p.thU p.thP p.MtLat p.h2 p.h3

theorem hU : ∀ i j b M (d : p.Dat i j b), 1 ≤ j → j ≤ D.R.m →
    p.thU i j b ∅ M d = p.th i j b d ⊗ₜ[D.ntw.O i] (1 : AddMonoidAlgebra (D.ntw.O i) (DelQM D.host (D.ntw.l i) ∅ M)) := by
  intro i j b M d h1 h2
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le' h1
  exact (p.tie i ⟨n, h2⟩ b).thU_empty M d

def nth : NTh D.R D.host D.what₂ D.LL0 D.nd D.ntw p.ex :=
  { D.nth with datPhi := fun _ _ _ _ => 0, datP := fun _ _ _ _ => 0 }

end PreTie

end GlobalTheory.HeightCounting.SerCopy

end
