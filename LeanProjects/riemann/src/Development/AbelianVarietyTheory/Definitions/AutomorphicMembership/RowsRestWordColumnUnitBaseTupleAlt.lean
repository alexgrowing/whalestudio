import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StableIffCarrierEq
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.AssembleLattice
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SemilinearBasisImageIndepOfBasis
import Formalism.LocalRingCardinality.DataIdx

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder

namespace GlobalTheory.Mem.R3.Rw

attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI

structure Hs : Type 1 where
  T : Type
  [nacg : NormedAddCommGroup T]
  [ips : InnerProductSpace ℂ T]
  [fd : FiniteDimensional ℂ T]

attribute [instance] Hs.nacg Hs.ips Hs.fd

section Gen

variable (K : Type) [Field K] [NumberField K] [StarRing K] (G : Type) [Group G]

structure Mat1 where
  n : ℕ
  H : Matrix (Fin n) (Fin n) K
  E : Matrix (Fin n) (Fin n) K
  N : Submodule (𝓞 K) (Fin n → K)
  op : MonoidAlgebra K G → Matrix (Fin n) (Fin n) K

def Mat1.zero : Mat1 K G := ⟨0, 0, 0, ⊤, fun _ => 0⟩

variable {K G}

structure Mat1.Laws (m : Mat1 K G) (σ : K →+* ℂ) (e : MonoidAlgebra K G) : Prop where
  pos : (m.H.map σ).PosDef
  lat : Submodule.IsLattice K m.N
  add : ∀ a b, m.op (a + b) = m.op a + m.op b
  smul : ∀ (c : K) a, m.op (c • a) = c • m.op a
  one : m.op 1 = 1
  mul : ∀ a ∈ Subalgebra.center K (MonoidAlgebra K G), ∀ b ∈ Subalgebra.center K (MonoidAlgebra K G),
    m.op (a * b) = m.op a * m.op b
  E_eq : m.E = m.op e
  cen : e ∈ Subalgebra.center K (MonoidAlgebra K G)
  idem : IsIdempotentElem e
  sa : ∀ x y, Formalism.DivisionValues.hform m.H (m.E.mulVec x) y = Formalism.DivisionValues.hform m.H x (m.E.mulVec y)

structure Sp1 (O : Type) [CommRing O] (φ : O →+* ℂ) (G : Type) [Group G] : Type 1 where
  A : Hs
  lat : Rows.OLat O φ A.T
  e : A.T →ₗ[ℂ] A.T
  idem : e ∘ₗ e = e
  sa : e.IsSymmetric
  act : Subalgebra.center ℂ (MonoidAlgebra ℂ G) →ₐ[ℂ] Module.End ℂ A.T

structure Tie1 {O : Type} [CommRing O] {φ : O →+* ℂ} (σ : K →+* ℂ) (m : Mat1 K G) (s : Sp1 O φ G) where
  j : (Fin m.n → K) →ₛₗ[σ] s.A.T
  forms : FormsTie σ j m.H m.E s.e
  latT : OLatTie σ s.lat j m.N
  stable : ∀ (a : 𝓞 K), ∀ y ∈ s.lat.carrier, σ (a : K) • y ∈ s.lat.carrier
  cen : ∀ (z : Subalgebra.center ℂ (MonoidAlgebra ℂ G)) (a : MonoidAlgebra K G),
    (∀ g, σ (a.coeff g) = (z : MonoidAlgebra ℂ G).coeff g) → ∀ x, s.act z (j x) = j ((m.op a).mulVec x)

def Tie1.cast {O : Type} [CommRing O] {φ : O →+* ℂ} {σ : K →+* ℂ} {m m' : Mat1 K G} {s : Sp1 O φ G} (h : m = m')
    (t : Tie1 σ m s) : Tie1 σ m' s := h ▸ t

structure ChD (τ Φ : Type) (m : ℕ) (Top : τ → Hs) : Type 1 where
  EE : Hs
  Mult : τ → ℕ → Hs
  multZero : ∀ μ, (Mult μ 0).T ≃ₗᵢ[ℂ] EE.T
  multTop : ∀ μ, (Mult μ m).T ≃ₗᵢ[ℂ] (Top μ).T
  io : ∀ μ j, (Mult μ (j + 1)).T →ₗ[ℂ] (Mult μ j).T
  n : ℕ
  bs : OrthonormalBasis (Fin n) ℂ EE.T
  ty : Fin n → Φ

structure LfD (O : Type) [CommRing O] (φ : O →+* ℂ) (τ Φ : Type) (Mt : τ → ℕ → Hs) : Type 1 where
  Mj : ℕ → Hs
  lat : ∀ j, Rows.OLat O φ (Mj j).T
  th : ∀ μ j, (Mt μ j).T →ₗ[ℂ] (Mj j).T
  isot : ∀ j, Φ → Submodule ℂ (Mj j).T

end Gen

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type}

def rMat (A : FamIn D.what₂.LL G Pl0 T D.R.m) (P : Subgroup G) (ψ : P →* D.what₂.LLˣ) (t : T) : Mat1 D.what₂.LL G :=
  ⟨rDim D A P ψ t, rH D A P ψ t, rE D A P ψ t, rNab D A P ψ t, rOp D A P ψ t⟩

def lMat (A : FamIn D.what₂.LL G Pl0 T D.R.m) (P : Subgroup G) (ψ : P →* D.what₂.LLˣ) (i : Fin D.R.m) (t : T) : Mat1 D.what₂.LL G :=
  ⟨lDim D A P ψ i t, lH D A P ψ i t, lE D A P ψ i t, lNab D A P ψ i t,
    fun a => (A.fam.L i t).S.lvlOp (A.fam.L i t).r (A.fam.lvlA P ψ).P (A.fam.lvlA P ψ).ψ a⟩

variable {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

set_option genInjectivity false in
set_option genSizeOfSpec false in

structure Hd (R : RealDat D A Ks) : Type where
  tup : T → D.what₂.Tup
  tupT : D.what₂.Tup → T
  tupT_tup : ∀ t, tupT (tup t) = t
  tup0 : tup A.μ0 = D.what₂.mu0
  hm : 0 < D.R.m
  hTop : TopMultH R
  hinj : ∀ i t, Function.Injective (R.extV i t)
  PY : principalLevelFrame.RowPsi (Yc D 0) D.R.r
  PW : ∀ i, principalLevelFrame.RowPsi (Wc D i) D.R.r
  ιW : ∀ i, ↥(GfC (Yc D 0)) →* ↥(GfC (Wc D i))
  isomFin : ∀ i, principalLevelFrame.IsIsomFin (ιW i)
  frameMatch : ∀ i, principalLevelFrame.FrameMatch PY (PW i) (ιW i)
  hF : D.host.F = maximalRealSubfield D.host.E
  stdPsi : StdFrame hF PY ∧ ∀ i, StdFrame hF (PW i)

namespace Hd

variable {R : RealDat D A Ks} (y : Hd R) (F : Face D A)

def Us (μ : D.what₂.Tup) : Prop := μ = D.what₂.mu0 ∨ ∃ w : D.what₂.places.Pl, μ = y.tup (R.mu (D.plEq w))

abbrev C : ChainReal D := toChainReal R F y.tupT y.hm y.hTop

abbrev L : LiftReal D (y.C F) := toLiftReal R F y.tupT y.hm y.hTop y.hinj

def occ : Set (Formalism.L2.NG.FinTyp D.host.E D.R.r) :=
  principalLevelFrame.OccRows R.θ y.PY (R.MY 0) (fun b => levS _ (R.βY 0) (R.dat0 (R.levR F b)))
    (fun b => levChi _ (R.βY 0) (R.dat0 (R.levR F b))) (fun _ => R.e0)

def prtE (b : Bool) (π : Formalism.L2.NG.FinTyp D.host.E D.R.r) : Submodule ℂ ((y.C F).Amb 0) :=
  (principalLevelFrame.isotE R.θ y.PY (R.MY 0) (levS _ (R.βY 0) (R.dat0 (R.levR F b))) (levChi _ (R.βY 0) (R.dat0 (R.levR F b))) R.e0 π).map
    (PiTensorProduct.lift : Mult.MMap (R.MY 0) ≃ₗ[ℂ] _).toLinearMap

def prtW (i : Fin D.R.m) (π : Formalism.L2.NG.FinTyp D.host.E D.R.r) : Submodule ℂ ((y.L F).AmbW i) :=
  (principalLevelFrame.isotL R.θ (y.PW i) (R.MW i (sg0 D A)) (levS _ (R.βW i) (R.datWp i (R.levL F false (sg0 D A))))
    (levChi _ (R.βW i) (R.datWp i (R.levL F false (sg0 D A)))) (R.eWf i (sg0 D A)) π).map
    (PiTensorProduct.lift : Mult.MMap (R.MW i (sg0 D A)) ≃ₗ[ℂ] _).toLinearMap

end Hd

structure Reps {R : RealDat D A Ks} (y : Hd R) (F : Face D A) {Φ : Type} (rep : Φ → Formalism.L2.NG.FinTyp D.host.E D.R.r) : Prop where
  fin : Finite Φ
  mem : ∀ π, rep π ∈ y.occ F
  inj : ∀ π π', (rep π).Iso (rep π') → π = π'
  all : ∀ ρ ∈ y.occ F, ∃ π, (rep π).Iso ρ

def levP (F : Face D A) : Bool → Σ P : Subgroup G, P →* D.what₂.LLˣ
  | true => ⟨F.P1, F.ψ1⟩
  | false => ⟨F.P0, F.ψ0⟩

set_option genInjectivity false in
set_option genSizeOfSpec false in
set_option maxHeartbeats 2000000 in

structure ChT {R : RealDat D A Ks} (y : Hd R) (F : Face D A) (b : Bool) {Φ : Type} (rep : Φ → Formalism.L2.NG.FinTyp D.host.E D.R.r)
    {Top : D.what₂.Tup → Hs} (jA : ∀ t, (Fin (rDim D A (levP F b).1 (levP F b).2 t) → D.what₂.LL) → (Top (y.tup t)).T)
    (c : ChD D.what₂.Tup Φ D.R.m Top) : Type where
  jE : c.EE.T →ₗ[ℂ] (y.C F).Amb 0
  jM : ∀ μ j, (c.Mult μ j).T →ₗ[ℂ] (y.C F).Amb j
  jX : ∀ μ, (Top μ).T →ₗ[ℂ] (y.C F).AmbX
  jE_inj : Function.Injective jE
  jE_range : LinearMap.range jE = (y.C F).EEc b
  jE_ip : ∀ x x', ⟪x, x'⟫_ℂ = (y.C F).ipE b (jE x) (jE x')
  jM_inj : ∀ μ, y.Us μ → ∀ j, 1 ≤ j → j ≤ D.R.m - 1 → Function.Injective (jM μ j)
  jM_range : ∀ μ, y.Us μ → ∀ j, 1 ≤ j → j ≤ D.R.m - 1 → LinearMap.range (jM μ j) = (y.C F).CCP b μ j
  jM_ip : ∀ μ, y.Us μ → ∀ j, 1 ≤ j → j ≤ D.R.m - 1 → ∀ x x', ⟪x, x'⟫_ℂ = (y.C F).ipP b μ j (jM μ j x) (jM μ j x')
  jX_inj : ∀ μ, y.Us μ → Function.Injective (jX μ)
  jX_range : ∀ μ, y.Us μ → LinearMap.range (jX μ) = (y.C F).CCXP b μ
  jX_ip : ∀ μ, y.Us μ → ∀ x x', ⟪x, x'⟫_ℂ = (y.C F).ipXP b μ (jX μ x) (jX μ x')
  io0 : ∀ μ, y.Us μ → ∀ x (v : (c.Mult μ 1).T) (h : jM μ 1 v ∈ (y.C F).CC b μ 1),
    ⟪x, c.multZero μ (c.io μ 0 v)⟫_ℂ = (y.C F).ipE b (jE x) ((y.C F).ioC b μ 0 ⟨jM μ 1 v, h⟩ : (y.C F).Amb 0)
  io : ∀ μ, y.Us μ → ∀ j, 1 ≤ j → j + 1 ≤ D.R.m - 1 → ∀ x (v : (c.Mult μ (j + 1)).T) (h : jM μ (j + 1) v ∈ (y.C F).CC b μ (j + 1)),
    ⟪x, c.io μ j v⟫_ℂ = (y.C F).ipP b μ j (jM μ j x) ((y.C F).ioC b μ j ⟨jM μ (j + 1) v, h⟩ : (y.C F).Amb j)
  ioTop : ∀ μ, y.Us μ → ∀ x (v : (c.Mult μ D.R.m).T) (v' : (c.Mult μ (D.R.m - 1 + 1)).T), HEq v' v →
    ∀ h : jX μ (c.multTop μ v) ∈ (y.C F).CCX b μ,
    ⟪x, c.io μ (D.R.m - 1) v'⟫_ℂ = (y.C F).ipP b μ (D.R.m - 1) (jM μ (D.R.m - 1) x)
      ((y.C F).ioX b μ ⟨jX μ (c.multTop μ v), h⟩ : (y.C F).Amb (D.R.m - 1))
  junk : ∀ μ, ¬ y.Us μ → ∀ j, c.io μ j = 0
  ft : ∀ π, Submodule.span ℂ (c.bs '' {σ | c.ty σ = π}) = (y.prtE F b (rep π)).comap jE
  disj : ∀ π π', π ≠ π' → y.prtE F b (rep π) ⊓ y.prtE F b (rep π') = ⊥
  top : ∀ t, y.Us (y.tup t) → ∀ x,
    jX (y.tup t) (jA t x) = R.cX.toMap R.prX ((R.HX t).e (R.jX t (rowForm A (levP F b).1 (levP F b).2 t x)))

set_option genInjectivity false in
set_option genSizeOfSpec false in
set_option maxHeartbeats 2000000 in

structure LfT {R : RealDat D A Ks} (y : Hd R) (F : Face D A) {Φ : Type} (rep : Φ → Formalism.L2.NG.FinTyp D.host.E D.R.r)
    {Mt : D.what₂.Tup → ℕ → Hs}
    (jL : ∀ (i : Fin D.R.m) t, (Fin (lDim D A F.P0 F.ψ0 i t) → D.what₂.LL) → (Mt (y.tup t) ((i : ℕ) + 1)).T)
    (l : LfD D.what₂.O (D.what₂.embLL.comp D.what₂.OtoLL) D.what₂.Tup Φ Mt) : Type where
  eW : ∀ i : Fin D.R.m, (l.Mj ((i : ℕ) + 1)).T →ₗ[ℂ] (R.HW i (sg0 D A)).H
  eW_range : ∀ i, LinearMap.range (eW i) = (R.Wat i (sg0 D A) (R.levL F false (sg0 D A))).comap (R.HW i (sg0 D A)).e
  eW_norm : ∀ i x, ‖eW i x‖ ^ 2 = RealDat.nP F false * ‖x‖ ^ 2
  eW_lat : ∀ (i : Fin D.R.m) x, x ∈ (l.lat ((i : ℕ) + 1)).carrier ↔
    ∃ v ∈ (R.FW i).MK, v ∈ (R.FW i).Wgood F.P0 F.ψ0⁻¹ (fun g => (idemOf A.X).coeff g) ∧ eW i x = (R.FW i).j (sg0 D A) v
  jMj : ∀ i : Fin D.R.m, (l.Mj ((i : ℕ) + 1)).T →ₗ[ℂ] (y.L F).AmbW i
  jMj_read : ∀ i v, jMj i v = PiTensorProduct.lift ((R.HW i (sg0 D A)).e (eW i v))
  jMj_inj : ∀ i, Function.Injective (jMj i)
  jMj_range : ∀ i, LinearMap.range (jMj i) = (y.L F).Wc i
  jMj_ip : ∀ i x x', ⟪x, x'⟫_ℂ = (y.L F).ipWc i (jMj i x) (jMj i x')
  jMt : ∀ μ (i : Fin D.R.m), (Mt μ ((i : ℕ) + 1)).T →ₗ[ℂ] (GA D ((y.L F).V i) → (y.L F).TauV i)
  jMt_inj : ∀ μ, y.Us μ → ∀ i, Function.Injective (jMt μ i)
  jMt_range : ∀ μ, y.Us μ → ∀ i, LinearMap.range (jMt μ i) = (y.L F).Amt μ i
  jMt_ip : ∀ μ, y.Us μ → ∀ i x x', ⟪x, x'⟫_ℂ = (y.L F).ipA μ i (jMt μ i x) (jMt μ i x')
  theta : ∀ μ, y.Us μ → ∀ (i : Fin D.R.m) x (h : jMt μ i x ∈ (y.L F).Amt μ i) (w : (y.L F).AmbW i), w ∈ (y.L F).MultW i →
    w ∘ₗ (y.L F).embK i = (y.L F).thC μ i ⟨jMt μ i x, h⟩ → (y.L F).eW i ∘ₗ w ∈ (y.L F).Wc i →
    jMj i (l.th μ ((i : ℕ) + 1) x) = (y.L F).eW i ∘ₗ w
  junk : ∀ μ, ¬ y.Us μ → ∀ j, l.th μ j = 0
  out : ∀ j, j = 0 ∨ D.R.m < j → Subsingleton (l.Mj j).T
  isot : ∀ (i : Fin D.R.m) π v, v ∈ l.isot ((i : ℕ) + 1) π ↔ jMj i v ∈ y.prtW F i (rep π)
  disj : ∀ i π π', π ≠ π' → y.prtW F i (rep π) ⊓ y.prtW F i (rep π') = ⊥
  read : ∀ (i : Fin D.R.m) t, y.Us (y.tup t) → ∀ x,
    jMt (y.tup t) i (jL i t x) = R.extV i t (R.jV i t (liftForm A F.P0 F.ψ0 i t x))

section Pk

structure Pk (K : Type) [Field K] [NumberField K] [StarRing K] (σ : K →+* ℂ) (O : Type) [CommRing O] (φ : O →+* ℂ) (τ G : Type)
    [Group G] (m : ℕ) : Type 1 where
  Φ : Type
  [fin : Fintype Φ]
  [dec : DecidableEq Φ]
  sA : Bool → τ → Sp1 O φ G
  mL : τ → ℕ → Mat1 K G
  sL : τ → ℕ → Sp1 O φ G
  tL : ∀ μ j, Tie1 σ (mL μ j) (sL μ j)
  ch : ∀ b, ChD τ Φ m fun μ => (sA b μ).A
  lf : LfD O φ τ Φ fun μ j => (sL μ j).A
  Dall : ℕ
  delp : ℝ
  delp_le_one : delp ≤ 1
  D_eq : ((ch true).n : ℝ) = (1 - delp) * Dall
  nR : ℕ
  cR : Module.Basis (Fin nR) ℂ (ch true).EE.T
  Xo : InfinitePlace K → Matrix (Fin nR) (Fin nR) ℂ

variable {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m}

def RrT {R : RealDat3 D A3 Ks} (F : Face3 D A3) (y : Hd R.toRealDat) (b : Bool) {E : Hs} (jE : E.T →ₗ[ℂ] (y.C F.lv2).Amb 0) (n : ℕ)
    (c : Module.Basis (Fin n) ℂ E.T) (Xo : InfinitePlace D.what₂.LL → Matrix (Fin n) (Fin n) ℂ) : Prop :=
  ∃ h : n = ((R.toCx3 F).data F.cr b).D,
    (∀ x : Fin n → D.what₂.LL, jE (∑ i, D.what₂.embLL (x i) • c i) =
      PiTensorProduct.lift (R.HE.e (Tw.out (s := twAt D.what₂.embLL A3.A.v0) (E := R.HE.H)
        ((R.toCx3 F).iC F.cr b A3.A.μ0 (cpt A3.A.v0.embedding (x ∘ Fin.cast h.symm)))))) ∧
    ∀ v, Xo v = (((R.toCx3 F).data F.cr b).XE v).submatrix (Fin.cast h) (Fin.cast h) ∧ IsUnit (Xo v).det

abbrev PkD (D : D7) (G : Type) [Group G] : Type 1 :=
  Pk D.what₂.LL D.what₂.embLL D.what₂.O (D.what₂.embLL.comp D.what₂.OtoLL) D.what₂.Tup G D.R.m

set_option genInjectivity false in
set_option genSizeOfSpec false in
set_option maxHeartbeats 2000000 in

structure PkT {R : RealDat3 D A3 Ks} (F : Face3 D A3) (y : Hd R.toRealDat) (mA : Bool → D.what₂.Tup → Mat1 D.what₂.LL G)
    (p : PkD D G) : Type where
  rep : p.Φ → Formalism.L2.NG.FinTyp D.host.E D.R.r
  reps : Reps y F.lv2 rep
  tA : ∀ b μ, Tie1 D.what₂.embLL (mA b μ) (p.sA b μ)
  lawsA : ∀ b μ, (mA b μ).Laws D.what₂.embLL (idemOf A3.A.X)
  lawsL : ∀ μ j, (p.mL μ j).Laws D.what₂.embLL (idemOf A3.A.X)
  hA : ∀ b t, mA b (y.tup t) = rMat A3.A (levP F.lv2 b).1 (levP F.lv2 b).2 t
  hL : ∀ (i : Fin D.R.m) t, p.mL (y.tup t) ((i : ℕ) + 1) = lMat A3.A F.lv2.P0 F.lv2.ψ0 i t
  ch : ∀ b, ChT y F.lv2 b rep (Top := fun μ => (p.sA b μ).A) (fun t x => ((tA b (y.tup t)).cast (hA b t)).j x) (p.ch b)
  lf : LfT y F.lv2 rep (Mt := fun μ j => (p.sL μ j).A) (fun i t x => ((p.tL (y.tup t) ((i : ℕ) + 1)).cast (hL i t)).j x) p.lf
  dall : p.Dall = Module.finrank ℂ (Mult.Mult R.θ (R.MY 0) (levS _ (R.βY 0) (R.dat0 (R.toRealDat.levR F.lv2 true)))
    (levChi _ (R.βY 0) (R.dat0 (R.toRealDat.levR F.lv2 true))))
  rr : RrT F y true (ch true).jE p.nR p.cR p.Xo

def etaOf (R : RealDat3 D A3 Ks) (F : Face3 D A3) (j : ℕ) (w : D.what₂.places.Pl) : ℚ :=
  open Classical in
  if h : 1 ≤ j ∧ j ≤ D.R.m then
    if D.plEq w ∈ R.twPl then
      A3.A.fam.etaJ F.P0 F.ψ0 (A3.fam3.toSub2 (R.toCx3 F).zs) ⟨j - 1, by omega⟩ (R.mu (D.plEq w)) (D.plEq w) else 0
  else 0

set_option genInjectivity false in
set_option genSizeOfSpec false in
set_option maxHeartbeats 4000000 in

structure RationalReadingWithoutCongruence (R : RealDat3 D A3 Ks) (F : Face3 D A3) (X0 : BaseLevelRowSide D) (Y : Read (A3 := A3) R.toRealDat F.lv2 X0) : Type where
  eRR : (Fin ((R.toCx3 F).data F.cr true).D → D.what₂.LL) ≃ₗ[D.what₂.LL] D.div.RR.V
  eRR0 : (Fin ((R.toCx3 F).data F.cr false).D → D.what₂.LL) ≃ₗ[D.what₂.LL] X0.s.RR.V
  jEE : ∀ y, (Y.Ish.jE (D.jEE (eRR y))).1 =
    PiTensorProduct.lift (R.HE.e (Tw.out (s := twAt D.what₂.embLL A3.A.v0) (E := R.HE.H) ((R.toCx3 F).iC F.cr true A3.A.μ0 (cpt A3.A.v0.embedding y))))
  jEE0 : ∀ y, (Y.Iz.jE (X0.s.jEE (eRR0 y))).1 =
    PiTensorProduct.lift (R.HE.e (Tw.out (s := twAt D.what₂.embLL A3.A.v0) (E := R.HE.H) ((R.toCx3 F).iC F.cr false A3.A.μ0 (cpt A3.A.v0.embedding y))))
  met : ∀ v, v ≠ A3.A.v0 → ∀ x y, Formalism.HermitianLatticesTheory.majAt D.div.RR.b D.div.RR.X v (eRR x) (eRR y) =
    Formalism.HermitianLatticesTheory.majAt (Pi.basisFun D.what₂.LL _) ((R.toCx3 F).data F.cr true).XE v x y
  met0 : ∀ v, v ≠ A3.A.v0 → ∀ x y, Formalism.HermitianLatticesTheory.majAt X0.s.RR.b X0.s.RR.X v (eRR0 x) (eRR0 y) =
    Formalism.HermitianLatticesTheory.majAt (Pi.basisFun D.what₂.LL _) ((R.toCx3 F).data F.cr false).XE v x y
  rr : (RowSide.sharp D).RRDef
  rr0 : X0.s.RRDef
  jW : ∀ i : Fin D.R.m, (Fin (((R.toCx3 F).data F.cr false).dW i) → D.what₂.LL) →ₛₗ[D.what₂.embLL] D.what₂.Mj ((i : ℕ) + 1)
  jW_read : ∀ (i : Fin D.R.m) y, Y.mj.eW i (jW i y) =
    (R.FW i).j (sg0 D A3.A) (Fintype.linearCombination D.what₂.LL (R.toRealDat.bL F.lv2 false i) y)

def RationalReadingWithoutCongruence.full {R : RealDat3 D A3 Ks} {F : Face3 D A3} {X0 : BaseLevelRowSide D} {Y : Read (A3 := A3) R.toRealDat F.lv2 X0}
    (Z : RationalReadingWithoutCongruence R F X0 Y) (h : ∀ j w, 1 ≤ j → j ≤ D.R.m → D.what₂.etaJ j w = etaOf R F j w) : ReadL R F X0 Y :=
  ⟨Z.eRR, Z.eRR0, Z.jEE, Z.jEE0, Z.met, Z.met0, Z.rr, Z.rr0, Z.jW, Z.jW_read, fun i w => by
    have hi : 1 ≤ (i : ℕ) + 1 ∧ (i : ℕ) + 1 ≤ D.R.m := ⟨by omega, i.2⟩
    rw [h _ w hi.1 hi.2]
    unfold etaOf
    rw [dif_pos hi]
    congr⟩

def ZeDef (D : D7) : Prop :=
  ∀ (u : D.what₂.Word) (μ : D.what₂.Tup) (c : ℂ),
    (∀ (φ : D.what₂.Mu u) (x : D.what₂.Amb μ), x ∈ D.what₂.V0 μ →
      D.what₂.perCol u μ φ x = c * D.what₂.Bu u φ (D.what₂.iota μ ((D.what₂.Qsp μ).starProjection x))) →
    (∃ (φ : D.what₂.Mu u) (x : D.what₂.Amb μ), x ∈ D.what₂.V0 μ ∧ D.what₂.perCol u μ φ x ≠ 0) → (∃ z : D.what₂.LL, D.what₂.embLL z = c) →
    D.what₂.zeC u μ = c

structure NumOK (D : D7) : Prop where
  lam : DV.LamDef D
  bu : Formalism.BasicNotions.Rows.BuDefQ D.what₂
  ze : ZeDef D
  idx : ∀ Y : DivX D, IdxDefs D Y
  jw : ∀ μ j w, 1 ≤ j → j ≤ D.R.m → D.what₂.jw μ j w = Idx.jwIdx D μ j w

end Pk

section PiLocalization₂

variable {B : Base} {C : Cols B} {G : Type} [Group G]

abbrev PkB (B : Base) (C : Cols B) (G : Type) [Group G] : Type 1 :=
  Pk B.LL B.embLL B.O (B.embLL.comp B.OtoLL) C.Tup G B.R.m

structure PerD (p : PkB B C G) : Type where
  e0 : ∀ u, (C.mem u).P.Mt ≃ₗ[ℂ] (p.sA true C.mu0).A.T
  eT : ∀ u μ, (C.PTw u μ).Mt ≃ₗ[ℂ] (p.sA true μ).A.T

structure Nums (p : PkB B C G) (W₀ : RowsRest B C) : Type where
  Bu : ∀ u, W₀.Mu u → (p.ch true).EE.T → ℂ
  linL : ∀ u F, IsLinearMap ℂ (fun φ : W₀.Mu u => Bu u φ F)
  linR : ∀ u (φ : W₀.Mu u), IsLinearMap ℂ (fun F => Bu u φ F)
  ze : B.Word → C.Tup → B.LLˣ
  rowsRest_wordColumnUnit_baseTuple : ∀ u, ze u C.mu0 = 1
  lamP : C.Tup → ℕ → p.Φ → ℝ
  Ij : C.Tup → ℕ → B.places.Pl → ℤ
  jw : C.Tup → ℕ → B.places.Pl → ℤ

open Classical in

def perOf (p : PkB B C G) (e : PerD p) (W₀ : RowsRest B C) (u : B.Word) (μ : C.Tup) (φ : W₀.Mu u) (F : (p.sA true μ).A.T) : ℂ :=
  if h : μ = C.mu0 then
    (C.mem u).P.PtilCol ((W₀.eMu u φ : (C.mem u).A.Mram) : (C.mem u).C.cls 0 → (C.mem u).C.Y 0 → ℂ)
      ((e.e0 u).symm (cast (congrArg (fun ν => (p.sA true ν).A.T) h) F))
  else (C.PTw u μ).PtilCol (C.e0Tw u μ ((W₀.eMu u φ : (C.mem u).A.Mram) : (C.mem u).C.cls 0 → (C.mem u).C.Y 0 → ℂ))
      ((e.eT u μ).symm F)

@[reducible] def Pk.what₂ (p : PkB B C G) (e : PerD p) (W₀ : RowsRest B C) (n : Nums p W₀) (η : ℕ → B.places.Pl → ℚ)
    (hη : ∀ j w, 0 ≤ η j w) : RowsRest B C where
  muAt := W₀.muAt
  muAt_conj := W₀.muAt_conj
  muTw := W₀.muTw
  muTw_conj := W₀.muTw_conj
  muAt_or := W₀.muAt_or
  EE := (p.ch true).EE.T
  Drows := (p.ch true).n
  onb := (p.ch true).bs
  Dall := p.Dall
  delp := p.delp
  delp_le_one := p.delp_le_one
  D_eq := p.D_eq
  EE0 := (p.ch false).EE.T
  D0 := (p.ch false).n
  onb0 := (p.ch false).bs
  FT := p.Φ
  instFT := p.fin
  instFTd := p.dec
  ft := (p.ch true).ty
  ft0 := (p.ch false).ty
  Amb μ := (p.sA true μ).A.T
  Mult μ j := ((p.ch true).Mult μ j).T
  multZero := (p.ch true).multZero
  multTop := (p.ch true).multTop
  io := (p.ch true).io
  Mtilde μ := (p.sA true μ).lat
  eOp μ := (p.sA true μ).e
  eOp_idem μ := (p.sA true μ).idem
  eOp_sa μ := (p.sA true μ).sa
  Mu := W₀.Mu
  perCol := perOf p e W₀
  Bu := n.Bu
  ze := n.ze
  rowsRest_wordColumnUnit_baseTuple := n.rowsRest_wordColumnUnit_baseTuple
  Mj j := (p.lf.Mj j).T
  MjLat := p.lf.lat
  kaBig := W₀.kaBig
  kaSmall := W₀.kaSmall
  Mt μ j := (p.sL μ j).A.T
  MtLat μ j := (p.sL μ j).lat
  MtL μ j := Fin (p.mL μ j).n → B.LL
  jMt μ j := (p.tL μ j).j
  jMt_basis μ j b := GlobalTheory.semilinear_basis_image_indep_of_basis B.LL B.embLL _ _ (p.tL μ j).j _ _ (Pi.basisFun B.LL _) b
    ⟨by simpa only [Pi.basisFun_apply] using (p.tL μ j).forms.li, by simpa only [Pi.basisFun_apply] using (p.tL μ j).forms.span⟩
  MtLat_sub μ j := (p.tL μ j).latT.1
  eMt μ j := (p.sL μ j).e
  eMt_idem μ j := (p.sL μ j).idem
  eMt_sa μ j := (p.sL μ j).sa
  eMt_LL μ j x := ⟨(p.mL μ j).E.mulVec x, ((p.tL μ j).forms.op_eq x).symm⟩
  thetaP := p.lf.th
  isot := p.lf.isot
  lamP := n.lamP
  Ij := n.Ij
  jw := n.jw
  etaJ := η
  etaJ_nonneg := hη
  shaLen := W₀.shaLen
  shaLen_nonneg := W₀.shaLen_nonneg
  eMu := W₀.eMu
  eMt0 := e.e0
  perCol_base_eq_PtilCol u φ F := by unfold perOf; rw [dif_pos rfl]; rfl
  Bu_linL := n.linL
  Bu_linR := n.linR
  eMtTw := e.eT
  perCol_tie u μ h φ F := by unfold perOf; rw [dif_neg h]
  eMu_isom := W₀.eMu_isom

structure CenIs (p : PkB B C G) {e : PerD p} {W₀ : RowsRest B C} {n : Nums p W₀} {η : ℕ → B.places.Pl → ℚ} {hη : ∀ j w, 0 ≤ η j w}
    (N : NStage B C (p.what₂ e W₀ n η hη)) (eR : G ≃* G0g N.nd) : Prop where
  amb : ∀ μ (z : Subalgebra.center ℂ (MonoidAlgebra ℂ (G0g N.nd))) (z' : Subalgebra.center ℂ (MonoidAlgebra ℂ G)),
    (∀ g, (z' : MonoidAlgebra ℂ G).coeff g = (z : MonoidAlgebra ℂ (G0g N.nd)).coeff (eR g)) →
      ∀ x, N.ntypes.cenAmb μ z x = (p.sA true μ).act z' x
  mt : ∀ μ j (z : Subalgebra.center ℂ (MonoidAlgebra ℂ (G0g N.nd))) (z' : Subalgebra.center ℂ (MonoidAlgebra ℂ G)),
    (∀ g, (z' : MonoidAlgebra ℂ G).coeff g = (z : MonoidAlgebra ℂ (G0g N.nd)).coeff (eR g)) →
      ∀ x, N.ntypes.cenMt μ j z x = (p.sL μ j).act z' x

def DivIs (p : PkB B C G) {e : PerD p} {W₀ : RowsRest B C} {n : Nums p W₀} {η : ℕ → B.places.Pl → ℚ} {hη : ∀ j w, 0 ≤ η j w}
    (V : DivStage B C (p.what₂ e W₀ n η hη)) : Prop :=
  (∃ ε : V.div.RR.V ≃ₗ[B.LL] (Fin p.nR → B.LL), (∀ x, V.jEE x = ∑ i, B.embLL (ε x i) • p.cR i) ∧
    ∀ v, v ≠ InfinitePlace.mk B.embLL → ∀ x y, Formalism.HermitianLatticesTheory.majAt V.div.RR.b V.div.RR.X v x y =
      Formalism.HermitianLatticesTheory.majAt (Pi.basisFun B.LL (Fin p.nR)) p.Xo v (ε x) (ε y)) ∧
  ∀ S N G', (RowSide.sharp (assemble B C (p.what₂ e W₀ n η hη) V S N G')).RRDef

end PiLocalization₂

end GlobalTheory.Mem.R3.Rw

end
