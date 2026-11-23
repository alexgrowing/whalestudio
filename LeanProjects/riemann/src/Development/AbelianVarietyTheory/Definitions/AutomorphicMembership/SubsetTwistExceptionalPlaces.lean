import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NonemptyAllIff
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StableIffCarrierEq
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExistsIsScalar
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NotTeichTrivOfIsDelta
import Formalism.LocalToGlobal.IndefiniteReal.DoubleCosetOperators.NHkRow

noncomputable section

namespace GlobalTheory.HeightCounting

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2 Formalism.L2.Host Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev
  Formalism.IndefR.Mult Formalism.IndefR.RecTie Formalism.IndefR.NX Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP NumberField IsDedekindDomain GlobalTheory.Mem
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option synthInstance.maxHeartbeats 400000

def TauTrue {D : D7} (X : NExpTied D) : Prop :=
  ∃ τ : ℕ → ∀ kv : (Σ k : Fin 2, D.nd.PlG k), (ZMod (D.host.g kv.1))ˣ →* (↥D.LL0)ˣ, ∀ i j b kv x, 1 ≤ j → j ≤ D.R.m →
    ((X.tauG i j b kv x : (FractionRing (D.ntw.O i))ˣ) : FractionRing (D.ntw.O i)) =
      GlobalTheory.SeriesTie.sideEmb D.ntw i b ((τ j kv x : (↥D.LL0)ˣ) : ↥D.LL0)

def lowAll (D : D7) : Finset ℕ := lowPr D ∪ {D.host.g 0, D.host.g 1, D.host.pde, D.host.pde'}

def OverSet (D : D7) (S : Finset (PlE D.host)) (s : Finset ℕ) : Prop := ∀ P ∈ S, ∃ p ∈ s, P ∈ placesOver D.host.E p

theorem OverSet.mono {D : D7} {S : Finset (PlE D.host)} {s s' : Finset ℕ} (h : OverSet D S s) (hs : s ⊆ s') : OverSet D S s' :=
  fun P hP => (h P hP).imp fun _ hp => ⟨hs hp.1, hp.2⟩

theorem OverSet.subset {D : D7} {S S' : Finset (PlE D.host)} {s : Finset ℕ} (h : OverSet D S s)
    (hs : ∀ p ∈ s, placesOver D.host.E p ⊆ ↑S') : S ⊆ S' :=
  fun P hP => (h P hP).elim fun p hp => hs p hp.1 hp.2

theorem OverSet.subset_twistExceptionalPlaces {D : D7} {S : Finset (PlE D.host)} {s low : Finset ℕ} (h : OverSet D S s) (hs : s ⊆ low)
    {F : TwFrameC D} (T : TwistFrameLowIndexCompatibility D F low) (i : D.ntw.Tw) : S ⊆ D.ntw.S0 i :=
  h.subset fun p hp P hP => by
    rw [T.ringSpec_excludedPlaces_eq i]
    exact Or.inr (T.concreteTwistFrame_extraExcluded_over_smallPrimes i p (hs hp) hP)

example (D : D7) : D.host.pde ∈ lowAll D := by simp [lowAll]

example (D : D7) : 2 ∈ lowAll D := by simp [lowAll, lowPr]

example (D : D7) (s : Finset ℕ) : OverSet D ∅ s := fun _ h => absurd h (Finset.notMem_empty _)

structure Elem (D : D7) : Prop where
  star : ∀ x : D.LL0, star (x : D.what₂.LL) ∈ D.LL0
  int : ∀ j g, ∃ z : ℤ, eExp D j g = z
  split : ∀ v, v ∈ placesOver D.host.E D.host.pde ∨ v ∈ placesOver D.host.E D.host.pde' → IsSplitPl D.host v

section Rows

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type}
  [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat3 D A3 Ks} {F : Face3 D A3} {X0 : BaseLevelRowSide D}

set_option genInjectivity false in
set_option genSizeOfSpec false in

structure MtAd (Y : R3.Read (A3 := A3) R.toRealDat F.lv2 X0) (M : MtFam D) where
  PV : ∀ i : Fin D.R.m, principalLevelFrame.RowPsi (Vc D i) D.R.nV
  std : ∀ i, R3.StdFrame Y.hF (PV i)
  eW : ∀ μ, Used0 D μ → ∀ i : Fin D.R.m, (M μ (i.1 + 1) (by omega) (by omega)).wt.W ≃ₗ[ℂ] (R.cV i).W
  read : ∀ μ (h : Used0 D μ) (i : Fin D.R.m) (x : D.what₂.Mt μ (i.1 + 1)) (g : GAf D.host.E D.R.nV),
    eW μ h i ((M μ (i.1 + 1) (by omega) (by omega)).real x g) = (Y.IL.jMt μ h i x).1 ((PV i).ψ g)
  rat : ∀ (i : Fin D.R.m) (g : GAf D.host.E D.R.nV), g ∈ ReciprocityTheory.Aut.GQ D.host.E D.R.nV ↔
    ∃ γ ∈ Formalism.L2.Theta.GQ (Vc D i), finHom (Vc D i) γ = finHom (Vc D i) ((PV i).ψ g)
  wt : ∀ μ (h : Used0 D μ) (i : Fin D.R.m) (g : ReciprocityTheory.Aut.GQ D.host.E D.R.nV), ∀ γ ∈ Formalism.L2.Theta.GQ (Vc D i),
    finHom (Vc D i) γ = finHom (Vc D i) ((PV i).ψ g) → ∀ v,
      eW μ h i ((M μ (i.1 + 1) (by omega) (by omega)).wt.ρ g v) = (R.cV i).ρ γ (eW μ h i v)
  id : ∀ i : Fin D.R.m, ∃ hn : (Vc D i).rank = D.R.nV, ∀ κ a b, finMat D.sp.cm.sig (Vc D i).gram ((PV i).ψ κ) a b =
    (GlobalTheory.Mem.R3.swapCast Y.hF).symm ((κ.1 : Matrix (Fin D.R.nV) (Fin D.R.nV) (ReciprocityTheory.Aut.AL D.host.E)) (Fin.cast hn a) (Fin.cast hn b))

variable (R) in

def hkNorm (i : Fin D.R.m) (k : ℕ) (P : PlE D.host) : ℂ :=
  (((R.C.mu0 i).val P : ℂˣ) : ℂ)⁻¹ ^ k * (((Nat.card (kP P) : ℕ) : ℂ) ^ (k * (D.R.nV / 2)))⁻¹

example (i : Fin D.R.m) (P : PlE D.host) : hkNorm R i 0 P = 1 := by simp [hkNorm]

variable (R) in

structure HkDat (Sb : Finset (PlE D.host)) (i : Fin D.R.m) (k : ℕ) (P : PlE D.host) (α : GA D (Wc D i))
    (Rr : Finset (GA D (Wc D i))) : Prop where
  split : IsSplitPl D.host P
  offS : P ∉ Sb
  odd : ((2 : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal
  le : k ≤ D.R.r
  elt : IsHeckeAt (Wc D i) P k α
  reps : Bridge.IsDC (levG (Wc D i) (R.βW i) (R.datWp i R.triv)) α Rr

def EigAd (Y : R3.Read (A3 := A3) R.toRealDat F.lv2 X0) (Sb : Finset (PlE D.host))
    (eig : ℕ → D.what₂.FT → ℕ → PlE D.host → ↥D.LL0) : Prop :=
  ∀ (i : Fin D.R.m) σ k P α Rr, HkDat R Sb i k P α Rr → D.nd.goodRow σ → ∀ x ∈ D.what₂.isot (i.1 + 1) σ,
    hkNorm R i k P • heckeOn (R.MW i (sg0 D A3.A)) Rr ((R.HW i (sg0 D A3.A)).e (Y.mj.eW i x)) =
      D.what₂.embLL ((eig (i.1 + 1) σ k P : ↥D.LL0) : D.what₂.LL) • (R.HW i (sg0 D A3.A)).e (Y.mj.eW i x)

structure RatAd (Y : R3.Read (A3 := A3) R.toRealDat F.lv2 X0) (cG : G0 R.Pg D.R.r ≃* G0g D.nd) (kKs : Ks →+* ↥D.LL0)
    (hk : ∀ x : Ks, ((kKs x : ↥D.LL0) : D.what₂.LL) = algebraMap Ks D.what₂.LL x) (In : RatIn D (ratDatR R cG kKs hk)) : Prop where
  hecke : ∀ j k P α Rr, 1 ≤ j → j ≤ D.R.m → HkDat R In.Sb (idxOf D j) k P α Rr → ∀ x : Fin (R.nW (idxOf D j)) → D.what₂.LL,
    (R.HW (idxOf D j) (sg0 D A3.A)).e ((R.FW (idxOf D j)).j (sg0 D A3.A) (In.hL j k P x)) =
      hkNorm R (idxOf D j) k P • heckeOn (R.MW (idxOf D j) (sg0 D A3.A)) Rr
        ((R.HW (idxOf D j) (sg0 D A3.A)).e ((R.FW (idxOf D j)).j (sg0 D A3.A) x))
  eig : EigAd Y In.Sb In.eig
  Sb_le : OverSet D In.Sb (lowAll D)
  lvl : ∀ g : G, g ∈ F.P0 ↔ (R.eG.trans cG) g ∈ Formalism.IndefR.NX.U D.nd
  psi : ∀ (u : F.P0) (hu : (R.eG.trans cG) u ∈ Formalism.IndefR.NX.U D.nd),
    (((psiUOf D.nd (NX.xiRed D) In.θ ⟨_, hu⟩ : (↥D.LL0)ˣ) : ↥D.LL0) : D.what₂.LL) = (((F.ψ0 u)⁻¹ : D.what₂.LLˣ) : D.what₂.LL)

variable {cG : G0 R.Pg D.R.r ≃* G0g D.nd} {S : RatDat D.ntw}

set_option genInjectivity false in
set_option genSizeOfSpec false in
set_option maxHeartbeats 1000000 in

structure SerAt (YS : NExpRealS R cG S) (v₀ : ∀ (j : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW j σ).Vec) (X : NExpTied D)
    (PV : ∀ i : Fin D.R.m, principalLevelFrame.RowPsi (Vc D i) D.R.nV) (cf : CharFrame D)
    (Pq : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E)) → PlE D.host) : Type 1 where
  ex : GlobalTheory.SeriesTie.ExportTie YS v₀
  bad : ∀ i, ex.ρ.bad i = GlobalTheory.SeriesTie.normProd (D.ntw.S0 i)
  ch : ∀ i P, IsSplitPl D.host P → (P ∈ ex.ρ.ch i ↔ P ∈ Set.range Pq)
  join : ∀ i (j : Fin D.R.m) b k Q ψ (hA : NX.AdmTw D i k Q ψ), IntegralHeckeForms.TwOK i k Q ψ →
    ∃ ω : (X.mtV i (j.1 + 1) b k Q ψ (by omega) (by omega) hA).W →ₛₗ[ex.ρ.ek i b k] PolF D (Wc D j).rank (Vc D j).rank,
      Function.Injective ω ∧ ∀ f g, (ex.tie i j b).rdV k Q ψ f ((finHom _).rangeRestrict ((PV j).ψ g)) =
        ω (((X.mtV i (j.1 + 1) b k Q ψ (by omega) (by omega) hA).real f).1 g)
  sup : ∀ i j b (h1 : 1 ≤ j) (h2 : j ≤ D.R.m) (x : D.nexp.Fm i j b), x ∈ D.nexp.Bsup i j b ↔ YS.eF i j b h1 h2 x ∈ Bsup S i j b
  off : ∀ i j b, ¬ (1 ≤ j ∧ j ≤ D.R.m) → Subsingleton (D.nexp.Fm i j b)
  lam : GlobalTheory.LamTie.LamDat D
  lam_ok : lam.Ok
  lam_teich : lam.Teich
  lam_C : lam.C = cf
  lam_q : lam.q0 = AbsolutelyIrreducibleSpan.q0 D
  lam_tie : GlobalTheory.LamTie.IsLamTieFull D.ntw lam

def EMtTheta (Y : R3.Read (A3 := A3) R.toRealDat F.lv2 X0) (YS : NExpRealS R cG S) (c : NChoice D) : Prop :=
  ∀ (w : D.what₂.places.Pl) (i : Fin D.R.m), D.what₂.muAt w ≠ D.what₂.mu0 →
    ∀ x ∈ Idx.TjV D (D.what₂.muTw w) (i.1 + 1), ∀ (n : ℕ) (a : Fin n → D.what₂.LL) (f : Fin n → FmK S (i.1 + 1)),
      (R.FW i).j (sg0 D A3.A) ((YS.fi i).e (∑ k, a k • (show ↥(S.A (i.1 + 1)).WK from f k).1)) =
        Y.mj.eW i (D.what₂.thetaP (D.what₂.muTw w) (i.1 + 1) (D.what₂.jMt (D.what₂.muTw w) (i.1 + 1) x)) →
      NChoice.thPe D c w (i.1 + 1) (c.eMt w (i.1 + 1) x) =
        ∑ k, c.embW w (a k) ⊗ₜ[D.ntw.O (c.twI w)]
          (YS.eF (c.twI w) (i.1 + 1) (c.sd w) (by omega) (by omega)).symm ((1 : KB S (c.twI w) (c.sd w)) ⊗ₜ[S.Ks] f k)

end Rows

def XdAll {D : D7} (xd : ThData D) : Prop := ∀ i j b, 1 ≤ j → j ≤ D.R.m → xd.xd0 i j b = Set.univ

end GlobalTheory.HeightCounting

end
