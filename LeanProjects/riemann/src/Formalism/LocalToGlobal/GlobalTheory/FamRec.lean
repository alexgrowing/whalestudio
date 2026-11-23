import Formalism.SharpRestriction.GlobalSchurBounds.QuadraticLogDerivCongr
import Formalism.LocalRingCardinality.Lemmas
import Formalism.SizeWindowBrackets.ChainSlopeWindows.ChainLatticeSizesModelEventually

open Module NumberField IsDedekindDomain Matrix

noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.FamRec

open Formalism Formalism.BasicNotions Formalism.MainNotions Formalism.HN Formalism.LFunctionChainParameters

def plF (D : D7) (w : D.what₂.places.Pl) : slopeLatticeData.FinPl D.what₂.LL := ⟨(D.plEq w).asIdeal, (D.plEq w).isMaximal⟩

def plB (D : D7) (z : slopeLatticeData.FinPl D.what₂.LL) : D.what₂.places.Pl :=
  D.plEq.symm ⟨z.1, z.2.isPrime, Ring.ne_bot_of_isMaximal_of_not_isField z.2 (RingOfIntegers.not_isField D.what₂.LL)⟩

theorem plB_plF (D : D7) (w : D.what₂.places.Pl) : plB D (plF D w) = w := by
  unfold plB plF
  exact D.plEq.symm_apply_apply w

theorem plF_plB (D : D7) (z : slopeLatticeData.FinPl D.what₂.LL) : plF D (plB D z) = z := by
  unfold plB plF
  apply Subtype.ext
  simp

variable {D : D7} (L : SizeData₂ D)

def prOf : Finset ℕ :=
  L.supp.image D.what₂.places.resChar ∪ Finset.univ.image (fun u : D.what₂.Word => (D.mem u).A.T)

def SOf : Finset (slopeLatticeData.FinPl D.what₂.LL) := (prOf L).biUnion (fun p => LChain2.plOver D.what₂.LL p)

def sgZ (u : D.what₂.Word) : slopeLatticeData.FinPl D.what₂.LL →₀ ℤ :=
  Finsupp.onFinset (SOf L) (fun z => if z ∈ SOf L then ⌊DV.ur D (plB D z) (L.sg u (plB D z))⌋ else 0)
    (fun z hz => by by_contra h; exact hz (if_neg h))

def tauZ : slopeLatticeData.FinPl D.what₂.LL →₀ ℤ :=
  Finsupp.onFinset (SOf L) (fun z => if z ∈ SOf L then ⌊DV.ur D (plB D z) (L.tau (plB D z))⌋ else 0)
    (fun z hz => by by_contra h; exact hz (if_neg h))

open Classical in

def ioPr (p : ℕ) : ℝ := if h : ∃ w : D.what₂.places.Pl, D.what₂.places.resChar w = p then L.io h.choose else 0

structure Mx (D : D7) where
  v : InfinitePlace D.what₂.LL
  Y : ∀ u, Matrix (D.div.Nu u).ι (D.div.Nu u).ι ℂ
  Y' : Matrix D.div.RR.ι D.div.RR.ι ℂ
  Ball : ∀ u, Matrix (D.div.RR.ι ⊕ Fin (D.what₂.Dall - D.what₂.Drows)) (D.div.Nu u).ι ℂ
  γ : D.what₂.Word → ℝ
  Bf : ∀ u, Matrix (D.div.RR.ι ⊕ Fin (D.what₂.Dall - D.what₂.Drows)) ((D.fm u).lat 0).ι ℂ
  Vr : ∀ u, Matrix ((D.fm u).lat 0).ι (D.div.Nu u).ι ℂ
  η0 : ℝ
  η1 : ℝ
  e0 : ℝ

def fam0 (m : ℕ) (A : Mx D) : LChain2.Fam D.what₂.Word m where
  K := D.what₂.LL
  Wd := Module.Dual D.what₂.LL D.div.RR.V
  κ := D.div.RR.ι
  κ₁ := Fin (D.what₂.Dall - D.what₂.Drows)
  V := fun u => (D.div.Nu u).V
  ι := fun u => (D.div.Nu u).ι
  Vf := fun u => ((D.fm u).lat 0).V
  ιf := fun u => ((D.fm u).lat 0).ι
  b' := D.div.RR.dualB
  X' := D.div.RR.dualX
  cc := D.div.RR.dualL
  b := fun u => (D.div.Nu u).b
  X := fun u => (D.div.Nu u).X
  M := fun u => DV.MramL D u
  N0 := fun u => L.NuLat u
  bf := fun u => ((D.fm u).lat 0).b
  Xf := fun u => ((D.fm u).lat 0).X
  Mf := fun u => ((D.fm u).lat 0).L
  σ := sgZ L
  τ := tauZ L
  B := D.div.Bk
  v := A.v
  Y := A.Y
  Y' := A.Y'
  Ball := A.Ball
  γ := A.γ
  Bf := A.Bf
  Vr := A.Vr
  S := SOf L
  gain := fun j z => L.gainD (j.val + 1) (plB D z)
  Fj := fun j z => L.F (j.val + 1) (plB D z)
  Ej := fun u j z => L.E u (j.val + 1) (plB D z)
  iop := ioPr L
  T := fun u => (D.mem u).A.T
  h := D.div.h
  lam := fun _ => 0
  Dstar := D.what₂.Dstar
  η0 := A.η0
  η1 := A.η1
  e0 := A.e0

def lamOf (m : ℕ) (A : Mx D) (u : D.what₂.Word) : ℝ :=
  ((fam0 L m A).ST u).fold max 0 (fun z => (fam0 L m A).lenR u z / (fam0 L m A).dM u)

def famOf (m : ℕ) (A : Mx D) : LChain2.Fam D.what₂.Word m := { fam0 L m A with lam := lamOf L m A }

section AtRecord

variable {D : D7} (L : SizeData₂ D)

def NprimeEq : Prop :=
  ∀ (D : D7) (L : SizeData₂ D) (m : ℕ) (A : Mx D), DV.NprimeDef D L → ∀ u, (famOf L m A).N' u = (D.div.Nu u).L

def LocalTie (m : ℕ) (F : LChain2.Fam D.what₂.Word m) : Prop :=
  (∀ u : D.what₂.Word,
    F.du u = ((D.div.Nu u).rank : ℝ) ∧
    (F.T u : ℝ) = ((D.mem u).A.T : ℝ) ∧
    muDef (F.b u) (F.X u) (F.N' u) = (D.div.Nu u).mu ∧
    muMaxDef (F.b u) (F.X u) (F.N' u) = (D.div.Nu u).muMax ∧
    F.h u = D.div.h u ∧
    muDef (F.bf u) (F.Xf u) (F.Mf u) = ((D.fm u).lat 0).mu ∧
    muMaxDef (F.bf u) (F.Xf u) (F.Mf u) = ((D.fm u).lat 0).muMax ∧
    ∀ j : Fin m, F.EeJ u j = ∑ w ∈ L.supp, SizeData₂.sz w (L.E u (j.val + 1) w)) ∧
  muDef F.b' F.X' F.cc = D.div.RR.muDual ∧
  muMinDef F.b' F.X' F.cc = D.div.RR.muMinDual ∧
  F.Fo = L.Fo ∧ F.Ga = L.Ga ∧
  F.Ta = ∑ w ∈ L.supp, SizeData₂.sz w (L.tau w) ∧
  F.IO = ∑ w ∈ L.supp, SizeData₂.lwP w * (D.what₂.places.ramIdx w : ℝ) * L.io w ∧
  F.del = D.what₂.delp

def TauNat : Prop := ∀ w, ∃ n : ℕ, L.tau w = (n : ℝ)

def IoPrime : Prop := ∀ w w', D.what₂.places.resChar w = D.what₂.places.resChar w' → L.io w = L.io w'

def FieldwiseLocalAgreement : Prop :=
  ∀ (D : D7) (L : SizeData₂ D) (m : ℕ) (A : Mx D), D.R.m = m → DV.NprimeDef D L → D.NuFull → TauNat L → IoPrime L →
    0 < D.what₂.Dall → LocalTie L m (famOf L m A)

def GaRounding : Prop :=
  ∀ (D : D7) (L : SizeData₂ D) (m : ℕ) (A : Mx D), D.R.m = m →
    (famOf L m A).Ga = L.Ga + ∑ w ∈ L.supp, 2 * SizeData₂.lwP w *
      (DV.ur D w (L.tau w) - (⌊DV.ur D w (L.tau w)⌋ : ℝ))

def MatRec (A : Mx D) : Prop :=
  (∀ u, IsUnit (A.Y u).det) ∧ IsUnit A.Y'.det ∧
  (∀ u (k : D.div.RR.ι) (j : (D.div.Nu u).ι), A.Ball u (Sum.inl k) j =
    (A.Y'⁻¹ * (LinearMap.toMatrix (D.div.Nu u).b D.div.RR.dualB (D.div.Bk u)).map A.v.embedding * A.Y u) k j) ∧
  (∀ u, 0 < A.γ u) ∧ (∀ u, A.Ball u = A.Bf u * A.Vr u) ∧ (∀ u, (A.Vr u)ᴴ * A.Vr u = 1) ∧
  (∀ u u', u ≠ u' → HilbertSchmidtNormSquare.hsSq (MatrixLatticeEstimates.KpG A.Bf A.γ u u') ≤
    (1 + A.η0) * (D.duS u : ℝ) * (D.duS u' : ℝ) / D.what₂.Dstar) ∧
  (∀ u, HilbertSchmidtNormSquare.hsSq (MatrixLatticeEstimates.KdG A.Bf A.γ u - 1) ≤ A.e0 * (D.duS u : ℝ))

def CardLat0 : Prop := ∀ (D : D7) (u : D.what₂.Word), Fintype.card ((D.fm u).lat 0).ι = D.duS u

def LatticeHypothesisOfColumnFacts : Prop :=
  ∀ (D : D7) (L : SizeData₂ D) (m : ℕ) (A : Mx D) (sg : ℝ), DV.NprimeDef D L → D.RRFull → D.NuFull →
    (∀ u, 0 < (D.div.Nu u).rank) → D.div.OneMapIntoCC →
    (∀ u, D.div.Bk u ≠ 0 →
      htMap (D.div.Nu u).b (D.div.Nu u).X D.div.RR.dualB D.div.RR.dualX (D.div.Bk u) ≤ D.div.h u) →
    0 < D.what₂.Dall → D.what₂.delp < 1 → MatRec A → (D.what₂.Dall : ℝ) ≤ (1 + A.η1) * D.what₂.Dstar →
    0 < sg → sg ≤ 1 / 20 → D.what₂.Dstar / sg ≤ ∑ u, (D.duS u : ℝ) →
    -1 ≤ A.η0 → A.η0 ≤ sg / 2 → A.η1 ≤ sg / 2 → 0 ≤ A.e0 → Real.sqrt A.e0 ≤ sg / 2 →
    (famOf L m A).LatHyp sg

def LenTwist : Prop :=
  ∀ (K V : Type) [Field K] [NumberField K] [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
    [FiniteDimensional K V] (τ : slopeLatticeData.FinPl K →₀ ℤ) (M N : Submodule (𝓞 K) V), (∀ w, 0 ≤ τ w) → M.FG →
    Submodule.span K (M : Set V) = ⊤ →
    N ≤ HermitianLatticesTheory.idealSmul ((slopeLatticeData.idealPow τ : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) : Submodule (𝓞 K) K) M →
    ∀ w : slopeLatticeData.FinPl K, slopeLatticeData.lenAt w M N =
      slopeLatticeData.lenAt w (HermitianLatticesTheory.idealSmul ((slopeLatticeData.idealPow τ : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) :
        Submodule (𝓞 K) K) M) N + ((finrank K V * (τ w).toNat : ℕ) : ℕ∞)

def Commens : Prop :=
  ∀ u, (L.NuLat u).FG ∧ ∃ c : 𝓞 D.what₂.LL, c ≠ 0 ∧ ∀ y ∈ DV.MramL D u, c • y ∈ L.NuLat u

def AtT : Prop :=
  ∀ u w, D.what₂.places.resChar w = (D.mem u).A.T → DV.LocLe (D.plEq w) 0 (L.NuLat u) (DV.MramL D u)

def RamRank (D : D7) : Prop :=
  ∀ u, ((D.mem u).A.du : ℝ) = (D.duS u : ℝ) * (1 - 1 / (((D.mem u).A.T : ℝ) - 1)) ^ D.R.f

def LenEq : Prop :=
  ∀ (D : D7) (L : SizeData₂ D) (m : ℕ) (A : Mx D), DV.NuDef D L → Commens L → TauNat L →
    (∀ u, (famOf L m A).N0 u ≤ (famOf L m A).ItM u) →
    ∀ u w, (famOf L m A).lenR u (plF D w) = (L.lenMN u w : ℝ)

def PlaceHypothesisOfPlaceSizes : Prop :=
  ∀ (D : D7) (L : SizeData₂ D) (m : ℕ) (A : Mx D), D.R.m = m → TauNat L → IoPrime L → (∀ w, 0 ≤ L.io w) →
    DV.NuDef D L → Commens L → AtT L →
    (∀ u w, D.what₂.places.resChar w ≠ (D.mem u).A.T →
      DV.LocLe (D.plEq w) ⌊DV.ur D w (L.tau w)⌋₊ (L.NuLat u) (DV.MramL D u) ∧
      (L.lenMN u w : ℝ) ≤ (D.duS u : ℝ) * (L.tau w + L.io w)) →
    (∀ u w, w ∉ L.supp → (∀ u', D.what₂.places.resChar w ≠ (D.mem u').A.T) →
      DV.LocEq (D.plEq w) (L.NuLat u) (DV.MramL D u)) →
    (∀ u w, D.what₂.places.resChar w = (D.mem u).A.T → L.tau w = 0) →
    RamRank D →
    (∀ u, (D.fm u).ramLat.mu = ((D.fm u).lat 0).mu -
        (D.R.f : ℝ) * Real.log (((D.mem u).A.T : ℝ) - 1) / (((D.mem u).A.T : ℝ) - 2) ∧
      (D.fm u).ramLat.muMax ≤ ((D.fm u).lat 0).muMax) →
    (∀ u, 0 < D.duS u) →
    (∑ w ∈ L.supp, SizeData₂.sz w (L.tau w) ≤ L.sc.b ^ 2) →
    (∀ u, 4 * (D.R.f : ℝ) ≤ ((D.mem u).A.T : ℝ) ∧
      4 * (D.R.f : ℝ) / ((D.mem u).A.T : ℝ) * L.sc.b ^ 2 +
        (D.R.f : ℝ) * Real.log (((D.mem u).A.T : ℝ) - 1) / (((D.mem u).A.T : ℝ) - 2) ≤ 1) →
    (famOf L m A).PlaceHyp D.R.f L.sc.b

end AtRecord

section Family

open Formalism.D5 Formalism.RankGapBounds.WeightedMeanData Formalism.LFunctionChainParameters.WeightedSlopeBounds Formalism.LFunctionChainParameters.characterSumData Formalism.LFunctionChainParameters.ThickSetMeanBounds Formalism.LFunctionChainParameters.LErr Formalism.LFunctionChainParameters.LHost

structure FieldEq {U0 : Type} {W : U0 → Type} {Top Top' : Type} {m f f' : ℕ} (A : Data U0 W Top m f)
    (B : Data U0 W Top' m f') (eT : Top ≃ Top') (eF : Fin f ≃ Fin f') : Prop where
  x : A.x = B.x
  ε : A.ε = B.ε
  a : A.a = B.a
  b : A.b = B.b
  b' : A.b' = B.b'
  k : A.k = B.k
  L : A.L = B.L
  La : A.La = B.La
  B0 : A.B0 = B.B0
  Nc : A.Nc = B.Nc
  gam : A.gam = B.gam
  LpL : A.LpL = B.LpL
  v : A.v = B.v
  lg : A.lg = B.lg
  aT : ∀ t, A.aT t = B.aT (eT t)
  w : ∀ u0 j ρ, A.w u0 j ρ = B.w u0 j (eF ρ)
  d : ∀ u0 u, A.d u0 u = B.d u0 u
  T : ∀ u0 u, A.T u0 u = B.T u0 u
  muN : ∀ u0 u, A.muN u0 u = B.muN u0 u
  muMaxN : ∀ u0 u, A.muMaxN u0 u = B.muMaxN u0 u
  h : ∀ u0 u, A.h u0 u = B.h u0 u
  muM : ∀ u0 u, A.muM u0 u = B.muM u0 u
  muMaxM : ∀ u0 u, A.muMaxM u0 u = B.muMaxM u0 u
  EeJ : ∀ u0 u j, A.EeJ u0 u j = B.EeJ u0 u j
  muCC : ∀ u0, A.muCC u0 = B.muCC u0
  muMinCC : ∀ u0, A.muMinCC u0 = B.muMinCC u0
  Fo : ∀ u0, A.Fo u0 = B.Fo u0
  Ga : ∀ u0, A.Ga u0 = B.Ga u0
  Ta : ∀ u0, A.Ta u0 = B.Ta u0
  ASK : ∀ u0, A.ASK u0 = B.ASK u0
  IO : ∀ u0, A.IO u0 = B.IO u0
  HH : ∀ u0, A.HH u0 = B.HH u0
  del : ∀ u0, A.del u0 = B.del u0
  η : ∀ u0, A.η u0 = B.η u0
  e : ∀ u0, A.e u0 = B.e u0
  delBar : A.delBar = B.delBar
  etaBar : A.etaBar = B.etaBar
  eBar : A.eBar = B.eBar

def Transfer : Prop :=
  ∀ {U0 : Type} [Fintype U0] {W : U0 → Type} [∀ u0, Fintype (W u0)] [∀ u0, Nonempty (W u0)] {Top Top' : Type}
    [Fintype Top] [Fintype Top'] {m f f' : ℕ} (A : Data U0 W Top m f) (B : Data U0 W Top' m f') (eT : Top ≃ Top')
    (eF : Fin f ≃ Fin f'), FieldEq A B eT eF → ∀ (C : Consts) (Xpp eK K : ℝ),
      (LChain.SizeData₂ A C Xpp → LChain.SizeData₂ B C Xpp) ∧ (ErrWindows A C Xpp eK K → ErrWindows B C Xpp eK K)

variable {eps : ℝ} (Fm : FamP eps) (x : ℝ)

def famT {e : Formalism.HC.Frame} (m : ℕ) (pt : e.A → Fm.Ix x) (A : ∀ u0, Mx (Fm.D x (pt u0))) :
    ∀ u0 : e.A, LChain2.Fam ((Fm.D x (pt u0)).what₂.Word) m :=
  fun u0 => famOf (Fm.L x (pt u0)) m (A u0)

def LocalFirstLayerAgreement : Prop :=
  ∀ {eps : ℝ} (Fm : FamP eps) (x : ℝ) (e : Formalism.HC.Frame) (m : ℕ) (pt : e.A → Fm.Ix x) (A : ∀ u0, Mx (Fm.D x (pt u0)))
    (G : LChain2.Glob) (cHH : ℝ) (Dh : ArithData e.A) (ell : AddChar (E0 × e.A) ℂ → ℂ) (N : ℕ)
    (TT T2 : Finset e.A) (a : e.A → ℝ) (w : e.A → Fin m → E0 × e.A → ℝ),
    (∀ u0, LocalTie (Fm.L x (pt u0)) m (famT Fm x m pt A u0)) →
    TieLocal Fm x pt (LChain2.mkData G cHH Dh ell N TT T2 a w (famT Fm x m pt A))

def GlobalFirstLayerFails : Prop :=
  ∀ {eps : ℝ} (Fm : FamP eps) (x : ℝ) (e : Formalism.HC.Frame) (m : ℕ) (pt : e.A → Fm.Ix x) (A : ∀ u0, Mx (Fm.D x (pt u0)))
    (G : LChain2.Glob) (cHH : ℝ) (Dh : ArithData e.A) (ell : AddChar (E0 × e.A) ℂ → ℂ) (N : ℕ)
    (TT T2 : Finset e.A) (a : e.A → ℝ) (w : e.A → Fin m → E0 × e.A → ℝ) (Xpp η X' : ℝ),
    ¬ TieGlobal Fm x pt (LChain2.mkData G cHH Dh ell N TT T2 a w (famT Fm x m pt A)) Xpp η X'

variable {Fm x}

def globM (M : Lnk.Mod Fm x) (etaB eB : ℝ) : LChain2.Glob where
  x := x
  ε := eps
  k := ((Fm.D x M.i0).R.k : ℝ)
  La := (Fm.L x M.i0).La
  v := (Fm.D x M.i0).host.v
  lg := Lnk.lgG (Fm.D x M.i0)
  delBar := Real.exp (-(x ^ (Fm.ez / 7)))
  etaBar := etaB
  eBar := eB

def famM (M : Lnk.Mod Fm x) (A : ∀ u0, Mx (Fm.D x (M.pt u0))) :
    ∀ u0 : M.e.A, LChain2.Fam ((Fm.D x (M.pt u0)).what₂.Word) M.m := famT Fm x M.m M.pt A

def dataK (M : Lnk.Mod Fm x) (A : ∀ u0, Mx (Fm.D x (M.pt u0))) (ell : AddChar (E0 × M.e.A) ℂ → ℂ) (N : ℕ)
    (CH etaB eB : ℝ) : Data M.e.A (fun u0 => (Fm.D x (M.pt u0)).what₂.Word) ↥M.TT M.m (PhiSet (H := M.e.A)).card :=
  LChain2.mkData (globM M etaB eB) CH M.AD ell N M.TT M.T2 M.a M.w (famM M A)

def etaM (M : Lnk.Mod Fm x) (A : ∀ u0, Mx (Fm.D x (M.pt u0))) (CH : ℝ) (u0 : M.e.A) : ℝ :=
  5 * x ^ (-CH) + 3 * Real.sqrt (famM M A u0).deF

def eM (M : Lnk.Mod Fm x) (A : ∀ u0, Mx (Fm.D x (M.pt u0))) (u0 : M.e.A) : ℝ := 2 * (A u0).e0

def ModFieldEq : Prop :=
  ∀ {eps : ℝ} {Fm : FamP eps} {x : ℝ} (M : Lnk.Mod Fm x) (A : ∀ u0, Mx (Fm.D x (M.pt u0)))
    (ell : AddChar (E0 × M.e.A) ℂ → ℂ) (N : ℕ) (CH etaB eB : ℝ), Fm.x1 < x →
    (Fm.L x M.i0).logDerivativeAtOne = (ell chC).re →
    (∀ u0, LocalTie (Fm.L x (M.pt u0)) M.m (famM M A u0)) →
    FieldEq (M.data N CH etaB eB (etaM M A CH) (eM M A)) (dataK M A ell N CH etaB eB) M.eT
      (M.eP.trans LChain2.ePhi.symm)

def Chain2Rec {eps : ℝ} (Fm : FamP eps) (eD eL K cHH eK CL x : ℝ) : Prop :=
  ∃ (M : Lnk.Mod Fm x) (A : ∀ u0, Mx (Fm.D x (M.pt u0))) (ell : AddChar (E0 × M.e.A) ℂ → ℂ) (C : Consts)
    (cT : ℝ) (N : ℕ) (η θ etaB eB : ℝ),
    C.eDiv ≤ eD ∧ C.eLoss ≤ eL ∧ C.cHH ≤ cHH ∧
    TieArith Fm x M.pt M.av M.AD ell M.TT M.T2 M.a M.w ∧
    (Fm.L x M.i0).logDerivativeAtOne = (ell chC).re ∧ η = (Fm.L x M.i0).etaSz ∧
    LChain2.Inputs2 M.AD ell (globM M etaB eB) C cT N M.TT M.T2 M.a M.w (famM M A) η θ eK K CL

def Chain2RecCore : Prop :=
  ∀ {eps : ℝ} (Fm : FamP eps) (eD eL K cHH eK CL x : ℝ),
    (∀ i : Fm.Ix x, HostFacts (arithOf (Fm.D x i).host.toHostRaw)) → Chain2Rec Fm eD eL K cHH eK CL x →
    LChain2.Chain2aCore eD eL K cHH eK CL eps x

def ChainRecordCompatible : Prop :=
  ∀ {eps : ℝ} (Fm : FamP eps) (eD eL K cHH eK CL x : ℝ), Fm.x1 < x →
    (∀ (i : Fm.Ix x) (m : ℕ) (A : Mx (Fm.D x i)), (Fm.D x i).R.m = m → LocalTie (Fm.L x i) m (famOf (Fm.L x i) m A)) →
    Chain2Rec Fm eD eL K cHH eK CL x → ChainTied Fm eD eL K cHH eK CL x

def Chain2OfMod : Prop :=
  ∀ {eps : ℝ} {Fm : FamP eps} {x : ℝ} (M : Lnk.Mod Fm x) (A : ∀ u0, Mx (Fm.D x (M.pt u0)))
    (ell : AddChar (E0 × M.e.A) ℂ → ℂ) (C : Consts) (cT : ℝ) (N : ℕ) (η θ etaB eB eK K CL : ℝ), Fm.x1 < x →
    (Fm.L x M.i0).logDerivativeAtOne = (ell chC).re →
    (∀ u0, LocalTie (Fm.L x (M.pt u0)) M.m (famM M A u0)) →
    (M.data N C.cHH etaB eB (etaM M A C.cHH) (eM M A)).HidaSetting C →
    (M.data N C.cHH etaB eB (etaM M A C.cHH) (eM M A)).DIV C →
    EComp5 (M.data N C.cHH etaB eB (etaM M A C.cHH) (eM M A)) C →
    (M.data N C.cHH etaB eB (etaM M A C.cHH) (eM M A)).HComp C →
    Count5 (M.data N C.cHH etaB eB (etaM M A C.cHH) (eM M A)) C →
    (M.data N C.cHH etaB eB (etaM M A C.cHH) (eM M A)).Slopes C →
    LossBounds (M.data N C.cHH etaB eB (etaM M A C.cHH) (eM M A)) C →
    (M.data N C.cHH etaB eB (etaM M A C.cHH) (eM M A)).HHBound C →
    (∀ u0, (Fm.D x (M.pt u0)).what₂.delp ≤ Real.exp (-(x ^ (Fm.ez / 7))) ∧ etaM M A C.cHH u0 ≤ etaB ∧ eM M A u0 ≤ eB) →
    ErrWindows (M.data N C.cHH etaB eB (etaM M A C.cHH) (eM M A)) C ((Fm.L x M.i0).sc.X'' (Fm.D x M.i0).R.n) eK K →
    LChain.GrowthInequalityRemainingHyps M.AD ell N M.TT M.T2 M.a M.w x eps (Fm.L x M.i0).sc.b (Fm.L x M.i0).sc.b' η
      (Fm.L x M.i0).sc.X' θ CL →
    LChain.CostWindows x (fPl M.e.A) (Fm.L x M.i0).sc.b η θ →
    LChain.RestSize eps x (Fintype.card M.e.A) M.TT.card M.T2.card M.m (Fm.L x M.i0).sc.b
      ((Fm.D x M.i0).R.k : ℝ) (Fm.L x M.i0).sc.a →
    (∀ u0, (famM M A u0).LatHyp (x ^ (-C.cHH))) →
    (∀ u0, (famM M A u0).PlaceHyp (Fm.D x (M.pt u0)).R.f (Fm.L x (M.pt u0)).sc.b) →
    LChain2.SizesPl (globM M etaB eB) C cT M.TT (famM M A) →
    LChain2.Inputs2 M.AD ell (globM M etaB eB) C cT N M.TT M.T2 M.a M.w (famM M A) η θ eK K CL

end Family

end Formalism.L2.GlobalTheoryTheory.FamRec

end
