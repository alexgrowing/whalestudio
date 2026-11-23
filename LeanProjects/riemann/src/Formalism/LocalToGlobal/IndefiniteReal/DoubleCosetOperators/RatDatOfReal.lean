import Formalism.LocalToGlobal.IndefiniteReal.DoubleCosetOperators.Objects
import Formalism.LocalToGlobal.IndefiniteReal.ZeroPartEigenvalueConvention
import Formalism.LocalRingCardinality.DataIdx

noncomputable section

open NumberField Formalism.BasicNotions
open scoped TensorProduct

namespace Formalism.IndefR.NX

section Iso

variable {LL Ks Ks' WL WL' G G' : Type} [Field LL] [NumberField LL] [Field Ks] [NumberField Ks] [Algebra Ks LL]
  [Field Ks'] [NumberField Ks'] [Algebra Ks' LL]
  [AddCommGroup WL] [Module LL WL] [Module Ks WL] [IsScalarTower Ks LL WL] [Module (𝓞 LL) WL] [IsScalarTower (𝓞 LL) LL WL]
  [Module (𝓞 Ks) WL] [IsScalarTower (𝓞 Ks) Ks WL]
  [AddCommGroup WL'] [Module LL WL'] [Module Ks' WL'] [IsScalarTower Ks' LL WL'] [Module (𝓞 LL) WL']
  [IsScalarTower (𝓞 LL) LL WL'] [Module (𝓞 Ks') WL'] [IsScalarTower (𝓞 Ks') Ks' WL']
  {W W' : (LL →+* ℂ) → Type} [∀ σ, NormedAddCommGroup (W σ)] [∀ σ, InnerProductSpace ℂ (W σ)]
  [∀ σ, NormedAddCommGroup (W' σ)] [∀ σ, InnerProductSpace ℂ (W' σ)] [Group G] [Group G']

structure FormsIso (A : Arith.FormsL LL Ks WL W G) (A' : Arith.FormsL LL Ks' WL' W' G') where
  eK : Ks ≃+* Ks'
  eK_LL : ∀ a : Ks, algebraMap Ks' LL (eK a) = algebraMap Ks LL a
  e : WL ≃ₗ[LL] WL'
  eG : G ≃* G'
  eW : ∀ σ, W σ ≃ₗᵢ[ℂ] W' σ
  wk : ∀ x, x ∈ A.WK ↔ e x ∈ A'.WK
  mkK : ∀ x, x ∈ A.MK ↔ e x ∈ A'.MK
  rho : ∀ g x, e (A.ρ g x) = A'.ρ (eG g) (e x)
  chi : ∀ g, A'.chi (eG g) = A.chi g
  j : ∀ σ x, A'.j σ (e x) = eW σ (A.j σ x)

end Iso

section Real

open Formalism.IndefR.Links

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type}
  {A3 : Formalism.L2.DIV.FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

def idxOf (D : D7) (j : ℕ) : Fin D.R.m := ⟨min (j - 1) (D.R.m - 1), by have := D.R.two_le_m; omega⟩

theorem idxOf_succ (D : D7) (i : Fin D.R.m) : idxOf D ((i : ℕ) + 1) = i := by
  apply Fin.ext
  simp only [idxOf, Nat.add_sub_cancel]
  have := i.2
  omega

def ratDatOfReal (Rl : RealDat3 D A3 Ks) (eG0 : G ≃* G0g D.nd) (kKs : Ks →+* ↥D.LL0)
    (hk : ∀ x : Ks, ((kKs x : ↥D.LL0) : D.what₂.LL) = algebraMap Ks D.what₂.LL x) : RatDat D.ntw where
  Ks := Ks
  WL j := Fin (Rl.nW (idxOf D j)) → D.what₂.LL
  W j σ := (Rl.HW (idxOf D j) σ).H
  G := G
  eG := eG0
  A j := Rl.FW (idxOf D j)
  kKs := kKs
  kKs_spec := hk

abbrev ratDatR (Rl : RealDat3 D A3 Ks) (cG : Formalism.L2.DIV.G0 Rl.Pg D.R.r ≃* G0g D.nd) (kKs : Ks →+* ↥D.LL0)
    (hk : ∀ x : Ks, ((kKs x : ↥D.LL0) : D.what₂.LL) = algebraMap Ks D.what₂.LL x) : RatDat D.ntw :=
  ratDatOfReal Rl (Rl.eG.trans cG) kKs hk

set_option synthInstance.maxHeartbeats 400000 in

theorem bsupOfIff {O M N : Type} [CommRing O] [IsDomain O] [AddCommGroup M] [AddCommGroup N] [Module O M] [Module O N]
    (e : M →+ N) (B : Submodule O M) (B' : Submodule O N) (h : ∀ x, x ∈ B ↔ e x ∈ B') :
    ∃ c : O, c ≠ 0 ∧ (∀ x, x ∈ B → c • e x ∈ B') ∧ (∀ x, e x ∈ B' → c • x ∈ B) :=
  ⟨1, one_ne_zero, fun x hx => by rw [one_smul]; exact (h x).1 hx, fun x hx => by rw [one_smul]; exact (h x).2 hx⟩

structure NExpRealS (Rl : RealDat3 D A3 Ks) (cG : Formalism.L2.DIV.G0 Rl.Pg D.R.r ≃* G0g D.nd) (S : RatDat D.ntw) where
  fi : ∀ i : Fin D.R.m, FormsIso (S.A ((i : ℕ) + 1)) (Rl.FW i)

  geq : ∀ (i : Fin D.R.m) (g : S.G), cG (Rl.eG ((fi i).eG g)) = S.eG g
  rho : ∀ j, 1 ≤ j → j ≤ D.R.m → RhoStab S j
  chi : ∀ j, 1 ≤ j → j ≤ D.R.m → ChiInLL0 S j
  eF : ∀ i j b, 1 ≤ j → j ≤ D.R.m → D.nexp.Fm i j b ≃ₗ[FractionRing (D.ntw.O i)] Fm S i j b

  bsup : ∀ i j b (h1 : 1 ≤ j) (h2 : j ≤ D.R.m), ∃ c : D.ntw.O i, c ≠ 0 ∧
    (∀ x : D.nexp.Fm i j b, x ∈ D.nexp.Bsup i j b → c • eF i j b h1 h2 x ∈ Bsup S i j b) ∧
    (∀ x : D.nexp.Fm i j b, eF i j b h1 h2 x ∈ Bsup S i j b → c • x ∈ D.nexp.Bsup i j b)
  act : ∀ i j b (h1 : 1 ≤ j) (h2 : j ≤ D.R.m) (g : G0g D.nd) (x : D.nexp.Fm i j b),
    eF i j b h1 h2 (D.nexp.actG i j b g x) = actG S i j b (rho j h1 h2) (chi j h1 h2) g (eF i j b h1 h2 x)

def NExpThRowT (D : D7) (T : ThData D) : Prop :=
  ∀ i j b (d : D.nexp.Dat i j b), d ∈ T.xd0 i j b → 1 ≤ j → j ≤ D.R.m →
    ∃ f ∈ D.nexp.MtLat i j b 0 ∅ 1,
      ((1 : D.ntw.Ok i 0) ⊗ₜ[D.ntw.O i] D.nexp.th i j b d : D.ntw.Ok i 0 ⊗[D.ntw.O i] D.nexp.Fm i j b) =
        D.nexp.thP i j b 0 ∅ 1 f

def NExpReal (Rl : RealDat3 D A3 Ks) (cG : Formalism.L2.DIV.G0 Rl.Pg D.R.r ≃* G0g D.nd) (S : RatDat D.ntw) : Prop :=
  Nonempty (NExpRealS Rl cG S)

set_option synthInstance.maxHeartbeats 400000 in

structure NExpThRow (D : D7) where
  thTr : ∀ i j b (d : D.nexp.Dat i j b), 1 ≤ j → j ≤ D.R.m →
    ∃ f ∈ D.nexp.MtLat i j b 0 ∅ 1,
      ((1 : D.ntw.Ok i 0) ⊗ₜ[D.ntw.O i] D.nexp.th i j b d : D.ntw.Ok i 0 ⊗[D.ntw.O i] D.nexp.Fm i j b) =
        D.nexp.thP i j b 0 ∅ 1 f

section Hecke

variable {tw : NTw D.R D.host D.what₂ D.LL0 D.nd} (S : RatDat tw)

def HeckeStabR (j : ℕ) (hL : ℕ → PlE D.host → Module.End D.what₂.LL (S.WL j)) : Prop :=
  ∀ k P (x : S.WL j), x ∈ (S.A j).WK → hL k P x ∈ (S.A j).WK

def hkFR (i : tw.Tw) (j : ℕ) (b : Bool) (hL : ℕ → PlE D.host → Module.End D.what₂.LL (S.WL j))
    (hs : HeckeStabR S j hL) (k : ℕ) (P : PlE D.host) : Module.End (FractionRing (tw.O i)) (Fm S i j b) :=
  (Module.End.baseChangeHom S.Ks (KB S i b) (FmK S j)
      (((hL k P).restrictScalars S.Ks).restrict (p := (S.A j).WK) (q := (S.A j).WK) fun x hx => hs k P x hx) :
    Module.End (KB S i b) (KB S i b ⊗[S.Ks] FmK S j))

end Hecke

set_option synthInstance.maxHeartbeats 400000 in

structure NExpRealH (Rl : RealDat3 D A3 Ks) (cG : Formalism.L2.DIV.G0 Rl.Pg D.R.r ≃* G0g D.nd) (S : RatDat D.ntw)
    (Y : NExpRealS Rl cG S) where
  hL : ∀ j, ℕ → PlE D.host → Module.End D.what₂.LL (S.WL j)
  hs : ∀ j, 1 ≤ j → j ≤ D.R.m → HeckeStabR S j (hL j)

  cHk : ∀ i (_b : Bool) (_k : ℕ) (_P : PlE D.host), FractionRing (D.ntw.O i)
  cHk_zero : ∀ i b P, cHk i b 0 P = 1
  cHk_unit : ∀ i b P, IsUnit (cHk i b 1 P)
  cHk_pow : ∀ i b k P, cHk i b k P = cHk i b 1 P ^ k
  hkEq : ∀ i j b (h1 : 1 ≤ j) (h2 : j ≤ D.R.m) (k : ℕ) (P : PlE D.host) (x : D.nexp.Fm i j b), P ∉ D.ntw.S0 i →
    Formalism.BasicNotions.IsSplitPl D.host P → k ≤ D.R.r →
    Y.eF i j b h1 h2 (D.nexp.hkF i j b k P x) =
      cHk i b k P • hkFR S i j b (hL j) (hs j h1 h2) k P (Y.eF i j b h1 h2 x)

end Real

section NMjR

variable {D : D7}

set_option synthInstance.maxHeartbeats 400000 in

structure NMjR (X : DivX D) (c : NChoice D) where
  eMj : ∀ w j, (X.MjH j).V →ₛₗ[c.embW w]
    FractionRing (c.Oe w) ⊗[D.ntw.O (c.twI w)] D.nexp.Fm (c.twI w) j (c.sd w)
  eMj_li : ∀ w j, D.what₂.muAt w ≠ D.what₂.mu0 → 1 ≤ j → j ≤ D.R.m →
    LinearIndependent (FractionRing (c.Oe w)) (fun a => eMj w j ((X.MjH j).b a))

  eMj_lat : ∀ w j, D.what₂.muAt w ≠ D.what₂.mu0 → 1 ≤ j → j ≤ D.R.m →
    NForms.IsLatIn (Submodule.span (c.Oe w) (eMj w j '' ((X.MjH j).L : Set (X.MjH j).V)))
      ((((NForms.V0 D (c.twI w) j (c.sd w)).restrictScalars (D.ntw.O (c.twI w))).baseChange
        (FractionRing (c.Oe w))).restrictScalars (c.Oe w))
  eMj_th : ∀ w j, D.what₂.muAt w ≠ D.what₂.mu0 → 1 ≤ j → j ≤ D.R.m → ∀ x ∈ Idx.TjV D (D.what₂.muTw w) j,
    ∀ y : (X.MjH j).V, X.jM j y = D.what₂.thetaP (D.what₂.muTw w) j (D.what₂.jMt (D.what₂.muTw w) j x) →
      eMj w j y = NChoice.thPe D c w j (c.eMt w j x)

section Real2

open Formalism.IndefR.Links

variable {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type}
  {A3 : Formalism.L2.DIV.FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

set_option synthInstance.maxHeartbeats 400000 in

structure NMjRR (Rl : RealDat3 D A3 Ks) (cG : Formalism.L2.DIV.G0 Rl.Pg D.R.r ≃* G0g D.nd) (S : RatDat D.ntw)
    (Y : NExpRealS Rl cG S)
    (X : DivX D) (c : NChoice D) (jD : ∀ j, (X.MjH j).V →ₗ[D.what₂.LL] S.WL j)
    extends NMjR X c where

  ks : ∀ j, 1 ≤ j → j ≤ D.R.m → (S.A j).IsKsForm
  eMj_sum : ∀ w j (h1 : 1 ≤ j) (h2 : j ≤ D.R.m) (x : (X.MjH j).V) (n : ℕ) (a : Fin n → D.what₂.LL)
    (f : Fin n → FmK S j),
    jD j x = ∑ k, a k • (show ↥(S.A j).WK from f k).1 →
      eMj w j x = ∑ k, c.embW w (a k) ⊗ₜ[D.ntw.O (c.twI w)]
        (Y.eF (c.twI w) j (c.sd w) h1 h2).symm
          ((1 : KB S (c.twI w) (c.sd w)) ⊗ₜ[S.Ks] f k)

  embW_Ks : ∀ w j (a : S.Ks) (m : D.nexp.Fm (c.twI w) j (c.sd w)),
    (c.embW w (algebraMap S.Ks D.what₂.LL a) ⊗ₜ[D.ntw.O (c.twI w)] m :
        FractionRing (c.Oe w) ⊗[D.ntw.O (c.twI w)] D.nexp.Fm (c.twI w) j (c.sd w)) =
      (1 : FractionRing (c.Oe w)) ⊗ₜ[D.ntw.O (c.twI w)]
        ((show FractionRing (D.ntw.O (c.twI w)) from ιK S (c.twI w) (c.sd w) a) • m)

def jDL (Rl : RealDat3 D A3 Ks) (F : Face D A3.A) (i : Fin D.R.m) :
    (Fin (Module.finrank D.what₂.LL (Rl.toRealDat.WL F false i)) → D.what₂.LL) →ₗ[D.what₂.LL] (Fin (Rl.nW i) → D.what₂.LL) :=
  Fintype.linearCombination D.what₂.LL (Rl.toRealDat.bL F false i)

end Real2

end NMjR

end Formalism.IndefR.NX
