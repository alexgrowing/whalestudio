import Mathlib
import Formalism.LocalToGlobal.Divisibility.LiftLat
import Formalism.LocalRingCardinality.PrincipalHermitianLattice
import Formalism.LocalRingCardinality.DataIdx
import Formalism.LocalToGlobal.Divisibility.DefGroup

open Module NumberField IsDedekindDomain

noncomputable section

namespace Formalism.L2.DIV

open Formalism.DivisionValues Formalism.L2.Indef

section Generic

variable {K : Type} [Field K] [NumberField K] [StarRing K]

structure HLatTie (A : Formalism.BasicNotions.HLat K) {d : ℕ} (L : Submodule (𝓞 K) (Fin d → K))
    (X : InfinitePlace K → Matrix (Fin d) (Fin d) ℂ) (φ : (Fin d → K) ≃ₗ[K] A.V) : Prop where

  lat : A.L = L.map ((φ : (Fin d → K) →ₗ[K] A.V).restrictScalars (𝓞 K))

  metric : ∀ v x y, Formalism.HermitianLatticesTheory.majAt A.b A.X v (φ x) (φ y) =
    Formalism.HermitianLatticesTheory.majAt (Pi.basisFun K (Fin d)) X v x y

def HLat.ofCoord {d : ℕ} (L : Submodule (𝓞 K) (Fin d → K)) (X : InfinitePlace K → Matrix (Fin d) (Fin d) ℂ) :
    Formalism.BasicNotions.HLat K where
  V := Fin d → K
  ι := Fin d
  b := Pi.basisFun K (Fin d)
  X := X
  L := L

structure FormsTie {n : ℕ} (σ : K →+* ℂ) {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℂ W]
    (j : (Fin n → K) →ₛₗ[σ] W) (H E : Matrix (Fin n) (Fin n) K) (op : W →ₗ[ℂ] W) : Prop where

  li : LinearIndependent ℂ fun i => j (Pi.single i 1)

  span : Submodule.span ℂ (Set.range fun i => j (Pi.single i 1)) = ⊤

  inner : ∀ x y, inner ℂ (j x) (j y) = σ (hform H x y)

  op_eq : ∀ x, op (j x) = j (E.mulVec x)

def OLatTie {n : ℕ} {O : Type} [CommRing O] {φO : O →+* ℂ} (σ : K →+* ℂ) {W : Type} [AddCommGroup W] [Module ℂ W]
    (M : Formalism.BasicNotions.Rows.OLat O φO W) (j : (Fin n → K) →ₛₗ[σ] W) (N : Submodule (𝓞 K) (Fin n → K)) : Prop :=
  (∀ v ∈ M.gen, v ∈ Set.range j) ∧
    ∀ x, x ∈ N ↔ ∃ c : W → 𝓞 K, j x = ∑ v ∈ M.gen, σ (c v : K) • v

end Generic

section Fam

variable (D : Formalism.BasicNotions.D7) {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {m : ℕ}
  (A : FamIn D.what₂.LL G Pl0 T m)

abbrev rDim (P : Subgroup G) (ψ : P →* D.what₂.LLˣ) (t : T) : ℕ :=
  (A.fam.R t).S.lvlDim (A.fam.R t).r (A.fam.lvl P ψ).P (A.fam.lvl P ψ).ψ

abbrev lDim (P : Subgroup G) (ψ : P →* D.what₂.LLˣ) (i : Fin m) (t : T) : ℕ :=
  (A.fam.L i t).S.lvlDim (A.fam.L i t).r (A.fam.lvlA P ψ).P (A.fam.lvlA P ψ).ψ

def rH (P : Subgroup G) (ψ : P →* D.what₂.LLˣ) (t : T) :
    Matrix (Fin (rDim D A P ψ t)) (Fin (rDim D A P ψ t)) D.what₂.LL :=
  (A.fam.R t).S.lvlH (A.fam.R t).r (A.fam.lvl P ψ).P (A.fam.lvl P ψ).ψ

def rE (P : Subgroup G) (ψ : P →* D.what₂.LLˣ) (t : T) :
    Matrix (Fin (rDim D A P ψ t)) (Fin (rDim D A P ψ t)) D.what₂.LL :=
  (A.fam.R t).S.lvlOp (A.fam.R t).r (A.fam.lvl P ψ).P (A.fam.lvl P ψ).ψ (idemOf A.X)

def rNab (P : Subgroup G) (ψ : P →* D.what₂.LLˣ) (t : T) :
    Submodule (𝓞 D.what₂.LL) (Fin (rDim D A P ψ t) → D.what₂.LL) :=
  (A.fam.R t).S.lvlNab (A.fam.R t).r (A.fam.lvl P ψ).P (A.fam.lvl P ψ).ψ

def rV0 (P : Subgroup G) (ψ : P →* D.what₂.LLˣ) (t : T) :
    Matrix (Fin (rDim D A P ψ t)) (Fin ((A.fam.R t).nV (A.fam.lvl P ψ))) D.what₂.LL :=
  (A.fam.R t).S.lvlPr (A.fam.R t).r (A.fam.lvl P ψ).P (A.fam.lvl P ψ).ψ * (A.fam.R t).vE (A.fam.lvl P ψ)

def lH (P : Subgroup G) (ψ : P →* D.what₂.LLˣ) (i : Fin m) (t : T) :
    Matrix (Fin (lDim D A P ψ i t)) (Fin (lDim D A P ψ i t)) D.what₂.LL :=
  (A.fam.L i t).S.lvlH (A.fam.L i t).r (A.fam.lvlA P ψ).P (A.fam.lvlA P ψ).ψ

def lE (P : Subgroup G) (ψ : P →* D.what₂.LLˣ) (i : Fin m) (t : T) :
    Matrix (Fin (lDim D A P ψ i t)) (Fin (lDim D A P ψ i t)) D.what₂.LL :=
  (A.fam.L i t).S.lvlOp (A.fam.L i t).r (A.fam.lvlA P ψ).P (A.fam.lvlA P ψ).ψ (idemOf A.X)

def lNab (P : Subgroup G) (ψ : P →* D.what₂.LLˣ) (i : Fin m) (t : T) :
    Submodule (𝓞 D.what₂.LL) (Fin (lDim D A P ψ i t) → D.what₂.LL) :=
  (A.fam.L i t).S.lvlNab (A.fam.L i t).r (A.fam.lvlA P ψ).P (A.fam.lvlA P ψ).ψ

def lZ0 (P : Subgroup G) (ψ : P →* D.what₂.LLˣ) (Zs : DefSub A.fam.amb) (i : Fin m) (t : T) :
    Matrix (Fin (lDim D A P ψ i t)) (Fin ((A.fam.L i t).dZ (A.fam.lvlA P ψ) (Zs.Zl i t))) D.what₂.LL :=
  (A.fam.L i t).lE (A.fam.lvlA P ψ) (Zs.Zl i t)

def lPrj (P : Subgroup G) (ψ : P →* D.what₂.LLˣ) (Zs : DefSub A.fam.amb) (i : Fin m) (t : T) :
    Matrix (Fin ((A.side P ψ Zs).dZ i t)) (Fin (lDim D A P ψ i t)) D.what₂.LL :=
  (A.fam.L i t).lPr (A.fam.lvlA P ψ) (Zs.Zl i t)

structure DivisionCompatibilityData (P0 : Subgroup G) (ψ0 : P0 →* D.what₂.LLˣ) (Ps : Subgroup G) (ψs : Ps →* D.what₂.LLˣ)
    (Zs : DefSub A.fam.amb) (S0 : IndefData (A.side P0 ψ0 Zs)) (S1 : IndefData (A.side Ps ψs Zs))
    (X0 : Formalism.BasicNotions.BaseLevelRowSide D) (Dc : DefCols (A.side Ps ψs Zs)) where

  eG : G ≃* Formalism.BasicNotions.G0g D.nd

  tup : T → D.what₂.Tup

  eRR : (Fin S1.D → D.what₂.LL) ≃ₗ[D.what₂.LL] D.div.RR.V

  eRR0 : (Fin S0.D → D.what₂.LL) ≃ₗ[D.what₂.LL] X0.s.RR.V

  jA : ∀ t, (Fin (rDim D A Ps ψs t) → D.what₂.LL) →ₛₗ[D.what₂.embLL] D.what₂.Amb (tup t)

  jA0 : ∀ t, (Fin (rDim D A P0 ψ0 t) → D.what₂.LL) →ₛₗ[D.what₂.embLL] X0.s.Amb (tup t)

  eMt : ∀ (i : Fin m) (t : T),
    (Fin (lDim D A P0 ψ0 i t) → D.what₂.LL) ≃ₗ[D.what₂.LL] D.what₂.MtL (tup t) ((i : ℕ) + 1)

  jW : ∀ i : Fin m, (Fin (S0.dW i) → D.what₂.LL) →ₛₗ[D.what₂.embLL] D.what₂.Mj ((i : ℕ) + 1)

  wU : D.what₂.Word → Dc.Mem

  eNu : ∀ u, (Fin (Dc.a (wU u)) → D.what₂.LL) ≃ₗ[D.what₂.LL] (D.div.Nu u).V

def symPos (r ρ k : ℕ) (i : Fin r) : Fin r :=
  ⟨(if i.val < ρ then k + i.val else if i.val < ρ + k then i.val - ρ else i.val) % r, Nat.mod_lt _ i.pos⟩

structure LvlTie (P0 : Subgroup G) (ψ0 : P0 →* D.what₂.LLˣ) (Ps : Subgroup G) (ψs : Ps →* D.what₂.LLˣ)
    (eG : G ≃* Formalism.BasicNotions.G0g D.nd) (Pg : Finset (Pl D.host.E)) (pl : (Σ k : Fin 2, D.nd.PlG k) ≃ ↥Pg)
    (res : ∀ kv : (Σ k : Fin 2, D.nd.PlG k), kP (pl kv).1 ≃+* ZMod (D.host.g kv.1))
    (ψ : ∀ PP : Pl D.host.E, AddChar (kP PP) D.what₂.LL) (eC : G ≃* G0 Pg D.R.r) : Prop where

  place : ∀ kv, (pl kv).1 = D.naut.plGw kv.1 kv.2

  comp : ∀ (g : G) (kv : Σ k : Fin 2, D.nd.PlG k),
    eG g kv = Matrix.GeneralLinearGroup.map (res kv).toRingHom (eC g (pl kv))

  gen : IsGenericPsi Pg ψ

  p0 : ∀ g : G, g ∈ P0 ↔ eC g ∈ (_root_.Formalism.L2.DIV.P0 Pg D.R.r ψ).H

  chi0 : ∀ (g : P0) (h : eC g ∈ (_root_.Formalism.L2.DIV.P0 Pg D.R.r ψ).H),
    ψ0 g = (_root_.Formalism.L2.DIV.P0 Pg D.R.r ψ).chi ⟨eC g, h⟩

  ps : ∀ g : G, g ∈ Ps ↔ ∃ y ∈ (PsharpSym Pg D.R.r D.R.rS D.R.k ψ).H, ∀ (PP : ↥Pg) (i j : Fin D.R.r),
    ((eC g PP : GL (Fin D.R.r) (kP PP.1)) : Matrix (Fin D.R.r) (Fin D.R.r) (kP PP.1))
        (symPos D.R.r D.R.rS D.R.k i) (symPos D.R.r D.R.rS D.R.k j) =
      ((y PP : GL (Fin D.R.r) (kP PP.1)) : Matrix (Fin D.R.r) (Fin D.R.r) (kP PP.1)) i j

  chis : ∀ (g : Ps) (y : (PsharpSym Pg D.R.r D.R.rS D.R.k ψ).H), (∀ (PP : ↥Pg) (i j : Fin D.R.r),
    ((eC g PP : GL (Fin D.R.r) (kP PP.1)) : Matrix (Fin D.R.r) (Fin D.R.r) (kP PP.1))
        (symPos D.R.r D.R.rS D.R.k i) (symPos D.R.r D.R.rS D.R.k j) =
      (((y : G0 Pg D.R.r) PP : GL (Fin D.R.r) (kP PP.1)) : Matrix (Fin D.R.r) (Fin D.R.r) (kP PP.1)) i j) →
    ψs g = (PsharpSym Pg D.R.r D.R.rS D.R.k ψ).chi y

structure GrpTie (P0 : Subgroup G) (ψ0 : P0 →* D.what₂.LLˣ) (Ps : Subgroup G) (ψs : Ps →* D.what₂.LLˣ)
    (eG : G ≃* Formalism.BasicNotions.G0g D.nd) : Prop where

  card : Fintype.card G = D.what₂.restRowsFiniteGroupCard

  e0 : ∀ g : G, D.what₂.embLL ((idemOf A.X).coeff g) = D.ntypes.e0.coeff (eG g)

  lvl0 : ∀ g : G, g ∈ P0 ↔ eG g ∈ D.nexp.U

  psi0 : ∀ (u : P0) (hu : eG u ∈ D.nexp.U) (i : D.ntw.Tw) (b : Bool), ∃ x : D.LL0,
    (x : D.what₂.LL) = (((ψ0 u)⁻¹ : D.what₂.LLˣ) : D.what₂.LL) ∧
    ((D.nexp.psiU i b ⟨eG u, hu⟩ : (FractionRing (D.ntw.O i))ˣ) : FractionRing (D.ntw.O i)) =
      IsFractionRing.map (A := D.ntw.O0 i) (B := D.ntw.O i) (K := FractionRing (D.ntw.O0 i))
        (L := FractionRing (D.ntw.O i)) (D.ntw.O_inj i) ((if b then D.ntw.emb0 i else D.ntw.emb0b i) x)

  idxSharp : Nat.card P0 = Nat.card Ps * (D.host.g 0 * D.host.g 1) ^ (D.R.k * D.R.f)

  lvl : ∃ (Pg : Finset (Pl D.host.E)) (pl : (Σ k : Fin 2, D.nd.PlG k) ≃ ↥Pg)
    (res : ∀ kv : (Σ k : Fin 2, D.nd.PlG k), kP (pl kv).1 ≃+* ZMod (D.host.g kv.1))
    (ψ : ∀ PP : Pl D.host.E, AddChar (kP PP) D.what₂.LL) (eC : G ≃* G0 Pg D.R.r),
    LvlTie D P0 ψ0 Ps ψs eG Pg pl res ψ eC

structure TupTie {P0 : Subgroup G} {ψ0 : P0 →* D.what₂.LLˣ} {Zs : DefSub A.fam.amb}
    (S0 : IndefData (A.side P0 ψ0 Zs)) (tup : T → D.what₂.Tup) : Prop where

  mu0 : tup A.μ0 = D.what₂.mu0

  muAt : ∀ w, D.what₂.muAt w = tup (S0.μ (D.plEq w))

  v0 : A.v0 = InfinitePlace.mk D.what₂.embLL

  inj : Function.Injective tup

structure RowSideTie {EE : Type} [NormedAddCommGroup EE] [InnerProductSpace ℂ EE] [FiniteDimensional ℂ EE]
    (X : Formalism.BasicNotions.RowSide D EE) (P : Subgroup G) (ψ : P →* D.what₂.LLˣ) (Zs : DefSub A.fam.amb)
    (S : IndefData (A.side P ψ Zs)) (tup : T → D.what₂.Tup) (eRR : (Fin S.D → D.what₂.LL) ≃ₗ[D.what₂.LL] X.RR.V)
    (jA : ∀ t, (Fin (rDim D A P ψ t) → D.what₂.LL) →ₛₗ[D.what₂.embLL] X.Amb (tup t)) : Prop where

  RR : HLatTie X.RR S.RR S.XE eRR

  forms : ∀ t, FormsTie D.what₂.embLL (jA t) (rH D A P ψ t) (rE D A P ψ t) (X.eOp (tup t))

  Mtilde : ∀ t, OLatTie D.what₂.embLL (X.Mtilde (tup t)) (jA t) (rNab D A P ψ t)

  iota : ∀ t (F : Fin ((A.fam.R t).nV (A.fam.lvl P ψ)) → D.what₂.LL),
    X.iota (tup t) (jA t ((rV0 D A P ψ t).mulVec F)) =
      X.jEE (eRR ((S.ι t).mulVec (((A.side P ψ Zs).Pq t).mulVec F)))

structure MtTie (P : Subgroup G) (ψ : P →* D.what₂.LLˣ) (Zs : DefSub A.fam.amb) (tup : T → D.what₂.Tup)
    (eMt : ∀ (i : Fin m) (t : T),
      (Fin (lDim D A P ψ i t) → D.what₂.LL) ≃ₗ[D.what₂.LL] D.what₂.MtL (tup t) ((i : ℕ) + 1)) : Prop where

  forms : ∀ (i : Fin m) (t : T), FormsTie D.what₂.embLL ((D.what₂.jMt (tup t) ((i : ℕ) + 1)).comp (eMt i t).toLinearMap)
    (lH D A P ψ i t) (lE D A P ψ i t) (D.what₂.eMt (tup t) ((i : ℕ) + 1))

  lat : ∀ (i : Fin m) (t : T), OLatTie D.what₂.embLL (D.what₂.MtLat (tup t) ((i : ℕ) + 1))
    ((D.what₂.jMt (tup t) ((i : ℕ) + 1)).comp (eMt i t).toLinearMap) (lNab D A P ψ i t)

  Z0 : ∀ (i : Fin m) (t : T), Formalism.BasicNotions.Idx.Z0 D (tup t) ((i : ℕ) + 1) =
    Submodule.span ℂ (Set.range fun k =>
      (D.what₂.jMt (tup t) ((i : ℕ) + 1)) (eMt i t ((lZ0 D A P ψ Zs i t).mulVec (Pi.single k 1))))

structure ThTie {P0 : Subgroup G} {ψ0 : P0 →* D.what₂.LLˣ} {Zs : DefSub A.fam.amb}
    (S0 : IndefData (A.side P0 ψ0 Zs)) (tup : T → D.what₂.Tup)
    (eMt : ∀ (i : Fin m) (t : T),
      (Fin (lDim D A P0 ψ0 i t) → D.what₂.LL) ≃ₗ[D.what₂.LL] D.what₂.MtL (tup t) ((i : ℕ) + 1))
    (jW : ∀ i : Fin m, (Fin (S0.dW i) → D.what₂.LL) →ₛₗ[D.what₂.embLL] D.what₂.Mj ((i : ℕ) + 1)) : Prop where

  li : ∀ i : Fin m, LinearIndependent ℂ fun k => jW i (Pi.single k 1)

  span : ∀ i : Fin m, Submodule.span ℂ (Set.range fun k => jW i (Pi.single k 1)) = ⊤

  lat : ∀ i : Fin m, OLatTie D.what₂.embLL (D.what₂.MjLat ((i : ℕ) + 1)) (jW i) (S0.M i)

  theta : ∀ (i : Fin m) (t : T) x,
    D.what₂.thetaP (tup t) ((i : ℕ) + 1) (D.what₂.jMt (tup t) ((i : ℕ) + 1) (eMt i t x)) =
      jW i ((S0.θ i t).mulVec ((lPrj D A P0 ψ0 Zs i t).mulVec x))

open Classical in

structure NumTie {P0 : Subgroup G} {ψ0 : P0 →* D.what₂.LLˣ} {Zs : DefSub A.fam.amb}
    (S0 : IndefData (A.side P0 ψ0 Zs)) (tup : T → D.what₂.Tup) : Prop where

  Ij : ∀ (i : Fin m) t w, D.what₂.Ij (tup t) ((i : ℕ) + 1) w = S0.Iw i t (D.plEq w)

  jw : ∀ (i : Fin m) t w, D.what₂.jw (tup t) ((i : ℕ) + 1) w =
    Formalism.DivisionValues.jw ((A.side P0 ψ0 Zs).HT i t) (D.plEq w) ((A.side P0 ψ0 Zs).Tl i t)

  etaJ : ∀ (i : Fin m) w, D.what₂.etaJ ((i : ℕ) + 1) w =
    if D.plEq w ∈ S0.Tw then A.fam.etaJ P0 ψ0 Zs i (S0.μ (D.plEq w)) (D.plEq w) else 0

structure ColTie {Ps : Subgroup G} {ψs : Ps →* D.what₂.LLˣ} {Zs : DefSub A.fam.amb}
    {S1 : IndefData (A.side Ps ψs Zs)} {Dc : DefCols (A.side Ps ψs Zs)} {Sp : SPer Dc} (C : ColData Dc Sp S1)
    (NuC : ∀ u, Submodule (𝓞 D.what₂.LL) (Fin (Dc.a u) → D.what₂.LL)) (wU : D.what₂.Word → Dc.Mem)
    (eNu : ∀ u, (Fin (Dc.a (wU u)) → D.what₂.LL) ≃ₗ[D.what₂.LL] (D.div.Nu u).V)
    (eRR : (Fin S1.D → D.what₂.LL) ≃ₗ[D.what₂.LL] D.div.RR.V) : Prop where

  wU_bij : Function.Bijective wU

  Nu : ∀ u, HLatTie (D.div.Nu u) (NuC (wU u)) (Dc.Xc (wU u)) (eNu u)

  Bk : ∀ u x y, D.div.Bk u (eNu u x) (eRR y) = C.B (wU u) x y

structure DivisionCompatible (P0 : Subgroup G) (ψ0 : P0 →* D.what₂.LLˣ) (Ps : Subgroup G) (ψs : Ps →* D.what₂.LLˣ)
    (Zs : DefSub A.fam.amb) (S0 : IndefData (A.side P0 ψ0 Zs)) (S1 : IndefData (A.side Ps ψs Zs))
    (X0 : Formalism.BasicNotions.BaseLevelRowSide D) {Dc : DefCols (A.side Ps ψs Zs)} {Sp : SPer Dc} (C : ColData Dc Sp S1)
    (NuC : ∀ u, Submodule (𝓞 D.what₂.LL) (Fin (Dc.a u) → D.what₂.LL))
    (I : DivisionCompatibilityData D A P0 ψ0 Ps ψs Zs S0 S1 X0 Dc) : Prop where

  ranks : m = D.R.m ∧ A.r = D.R.r ∧ A.t = D.R.t

  grp : GrpTie D A P0 ψ0 Ps ψs I.eG

  tup : TupTie D A S0 I.tup

  mu1 : S1.μ = S0.μ

  sharp : RowSideTie D A (Formalism.BasicNotions.RowSide.sharp D) Ps ψs Zs S1 I.tup I.eRR I.jA

  base : RowSideTie D A X0.s P0 ψ0 Zs S0 I.tup I.eRR0 I.jA0

  mt : MtTie D A P0 ψ0 Zs I.tup I.eMt

  th : ThTie D A S0 I.tup I.eMt I.jW

  num : NumTie D A S0 I.tup

  cols : ColTie D A C NuC I.wU I.eNu I.eRR

end Fam

end Formalism.L2.DIV
