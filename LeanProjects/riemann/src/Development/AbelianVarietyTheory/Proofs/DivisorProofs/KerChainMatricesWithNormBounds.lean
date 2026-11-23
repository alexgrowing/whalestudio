import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.FactorBounds
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeightedNormSquareRows
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.OrthogonalNormSquareSum
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CosetRefinement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCbData
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OpNormAtPairingSqLeOfValueBoundStatement
open Module NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Col Formalism.L2.Ker GlobalTheory.IndefiniteRowSideFullHecke.PlaceLogThetaBounds GlobalTheory.ColRows

noncomputable section

namespace GlobalTheory.DefRowsChain

variable {K : Type} [Field K] [NumberField K] [StarRing K] {Bs : DefBase K} {Df : DefSide Bs}

def bund (Dc : DefCols Df) (u : Dc.Mem) (Q : KerChain K) (nF : ℕ → ℕ) (XF : ∀ i, InfinitePlace K → Matrix (Fin (nF i)) (Fin (nF i)) ℂ)
    (nS : ℕ) (XS : InfinitePlace K → Matrix (Fin nS) (Fin nS) ℂ) : ℕ → Σ n : ℕ, (InfinitePlace K → Matrix (Fin n) (Fin n) ℂ)
  | 0 => ⟨Dc.a u, Dc.Xc u⟩
  | k + 1 => if k + 1 ≤ Q.n then ⟨nF (k + 1), XF (k + 1)⟩ else ⟨nS, XS⟩

omit [NumberField K] [StarRing K] in

theorem normAt_of_eq (p : Σ n : ℕ, (InfinitePlace K → Matrix (Fin n) (Fin n) ℂ)) (n : ℕ)
    (X : InfinitePlace K → Matrix (Fin n) (Fin n) ℂ) (hp : p = ⟨n, X⟩) (hc : n = p.1) (v : InfinitePlace K) (x : Fin p.1 → K) :
    Formalism.HermitianLatticesTheory.normAt (Pi.basisFun K (Fin p.1)) p.2 v x = Formalism.HermitianLatticesTheory.normAt (Pi.basisFun K (Fin n)) X v (x ∘ Fin.cast hc) := by
  subst hp
  rfl

omit [NumberField K] [StarRing K] in
theorem unit_of_eq (p : Σ n : ℕ, (InfinitePlace K → Matrix (Fin n) (Fin n) ℂ)) (n : ℕ)
    (X : InfinitePlace K → Matrix (Fin n) (Fin n) ℂ) (hp : p = ⟨n, X⟩) (v : InfinitePlace K) (hX : IsUnit (X v).det) :
    IsUnit (p.2 v).det := by
  subst hp
  exact hX

section

variable (Dc : DefCols Df) (u : Dc.Mem) (Q : KerChain K) (f0 : (Fin (Dc.a u) → K) →ₗ[K] (Q.F 0).Forms)
  (nF : ℕ → ℕ) (eF : ∀ i, (Fin (nF i) → K) ≃ₗ[K] (Q.F i).Forms) (XF : ∀ i, InfinitePlace K → Matrix (Fin (nF i)) (Fin (nF i)) ℂ)
  (nS : ℕ) (eS : (Fin nS → K) ≃ₗ[K] Q.S₁.EqFun) (XS : InfinitePlace K → Matrix (Fin nS) (Fin nS) ℂ)

theorem bund_succ_le (k : ℕ) (h : k + 1 ≤ Q.n) : bund Dc u Q nF XF nS XS (k + 1) = ⟨nF (k + 1), XF (k + 1)⟩ := by
  simp [bund, h]

theorem bund_succ_gt (k : ℕ) (h : ¬ k + 1 ≤ Q.n) : bund Dc u Q nF XF nS XS (k + 1) = ⟨nS, XS⟩ := by
  simp [bund, h]

def eN (k : ℕ) (h : k + 1 ≤ Q.n) : (Fin (bund Dc u Q nF XF nS XS (k + 1)).1 → K) ≃ₗ[K] (Q.F (k + 1)).Forms :=
  (LinearEquiv.funCongrLeft K K (finCongr (congrArg Sigma.fst (bund_succ_le Dc u Q nF XF nS XS k h)).symm)).trans (eF (k + 1))

def eL (k : ℕ) (h : ¬ k + 1 ≤ Q.n) : (Fin (bund Dc u Q nF XF nS XS (k + 1)).1 → K) ≃ₗ[K] Q.S₁.EqFun :=
  (LinearEquiv.funCongrLeft K K (finCongr (congrArg Sigma.fst (bund_succ_gt Dc u Q nF XF nS XS k h)).symm)).trans eS

def coFN : ∀ i, i ≤ Q.n → (Fin (bund Dc u Q nF XF nS XS i).1 → K) →ₗ[K] (Q.F i).Forms
  | 0, _ => f0
  | k + 1, h => (eN Dc u Q nF eF XF nS XS k h).toLinearMap

def KjN : ∀ j : Fin (Q.n + 1), Matrix (Fin (bund Dc u Q nF XF nS XS (j.val + 1)).1) (Fin (bund Dc u Q nF XF nS XS j.val).1) K :=
  Fin.lastCases (motive := fun j : Fin (Q.n + 1) =>
      Matrix (Fin (bund Dc u Q nF XF nS XS (j.val + 1)).1) (Fin (bund Dc u Q nF XF nS XS j.val).1) K)
    (LinearMap.toMatrix' ((eL Dc u Q nF XF nS eS XS Q.n (by omega)).symm.toLinearMap ∘ₗ Q.cpl ∘ₗ
      coFN Dc u Q f0 nF eF XF nS XS Q.n le_rfl))
    (fun i => LinearMap.toMatrix' ((eN Dc u Q nF eF XF nS XS i.val i.isLt).symm.toLinearMap ∘ₗ Q.step i.val ∘ₗ
      coFN Dc u Q f0 nF eF XF nS XS i.val i.isLt.le))

end

end GlobalTheory.DefRowsChain

namespace GlobalTheory.DefRowsChain

variable {K : Type} [Field K] [NumberField K] [StarRing K] {Bs : DefBase K} {Df : DefSide Bs}
  (Dc : DefCols Df) (u : Dc.Mem) (Q : KerChain K) (f0 : (Fin (Dc.a u) → K) →ₗ[K] (Q.F 0).Forms)
  (nF : ℕ → ℕ) (eF : ∀ i, (Fin (nF i) → K) ≃ₗ[K] (Q.F i).Forms) (XF : ∀ i, InfinitePlace K → Matrix (Fin (nF i)) (Fin (nF i)) ℂ)
  (nS : ℕ) (eS : (Fin nS → K) ≃ₗ[K] Q.S₁.EqFun) (XS : InfinitePlace K → Matrix (Fin nS) (Fin nS) ℂ)

theorem kerF_N (j : ℕ) (h : j < Q.n) (x : Fin (bund Dc u Q nF XF nS XS j).1 → K) :
    coFN Dc u Q f0 nF eF XF nS XS (j + 1) h ((KjN Dc u Q f0 nF eF XF nS eS XS ⟨j, by omega⟩).mulVec x) =
      Q.step j (coFN Dc u Q f0 nF eF XF nS XS j h.le x) := by
  show coFN Dc u Q f0 nF eF XF nS XS (j + 1) h ((KjN Dc u Q f0 nF eF XF nS eS XS (Fin.castSucc ⟨j, h⟩)).mulVec x) = _
  rw [KjN, Fin.lastCases_castSucc, LinearMap.toMatrix'_mulVec]
  simp [coFN]

theorem kerC_N (x : Fin (bund Dc u Q nF XF nS XS Q.n).1 → K) :
    eL Dc u Q nF XF nS eS XS Q.n (by omega) ((KjN Dc u Q f0 nF eF XF nS eS XS ⟨Q.n, by omega⟩).mulVec x) =
      Q.cpl (coFN Dc u Q f0 nF eF XF nS XS Q.n le_rfl x) := by
  show eL Dc u Q nF XF nS eS XS Q.n (by omega) ((KjN Dc u Q f0 nF eF XF nS eS XS (Fin.last Q.n)).mulVec x) = _
  rw [KjN, Fin.lastCases_last, LinearMap.toMatrix'_mulVec]
  simp

omit [NumberField K] [StarRing K] in
theorem chainMat_zero {m : ℕ} {c : Fin (m + 1) → ℕ} (Kj : ∀ j : Fin m, Matrix (Fin (c j.succ)) (Fin (c j.castSucc)) K) :
    Formalism.DivisionValues.chainMat Kj 0 = 1 := by
  simp [Formalism.DivisionValues.chainMat]

omit [NumberField K] [StarRing K] in
theorem chainMat_succ {m : ℕ} {c : Fin (m + 1) → ℕ} (Kj : ∀ j : Fin m, Matrix (Fin (c j.succ)) (Fin (c j.castSucc)) K)
    (j : Fin m) : Formalism.DivisionValues.chainMat Kj j.succ = Kj j * Formalism.DivisionValues.chainMat Kj j.castSucc := by
  simp [Formalism.DivisionValues.chainMat, Fin.induction_succ]

abbrev cF : Fin (Q.n + 2) → ℕ := fun j => (bund Dc u Q nF XF nS XS j.val).1

theorem chain_le_N : ∀ i (h : i ≤ Q.n) (x : Fin (cF Dc u Q nF XF nS XS 0) → K),
    coFN Dc u Q f0 nF eF XF nS XS i h
      ((Formalism.DivisionValues.chainMat (c := cF Dc u Q nF XF nS XS)
        (KjN Dc u Q f0 nF eF XF nS eS XS) ⟨i, by omega⟩).mulVec x) = Q.kk.colTo Q.hF i (coFN Dc u Q f0 nF eF XF nS XS 0 (Nat.zero_le _) x)
  | 0, h, x => by
    show coFN Dc u Q f0 nF eF XF nS XS 0 h ((Formalism.DivisionValues.chainMat (c := cF Dc u Q nF XF nS XS)
        (KjN Dc u Q f0 nF eF XF nS eS XS) 0).mulVec x) = coFN Dc u Q f0 nF eF XF nS XS 0 (Nat.zero_le _) x
    rw [chainMat_zero, Matrix.one_mulVec]
  | i + 1, h, x => by
    have hi : i < Q.n + 1 := by omega
    have ih := chain_le_N i (by omega) x
    show coFN Dc u Q f0 nF eF XF nS XS (i + 1) h ((Formalism.DivisionValues.chainMat (c := cF Dc u Q nF XF nS XS)
        (KjN Dc u Q f0 nF eF XF nS eS XS) (Fin.succ ⟨i, hi⟩)).mulVec x) = Q.step i (Q.kk.colTo Q.hF i (coFN Dc u Q f0 nF eF XF nS XS 0 (Nat.zero_le _) x))
    rw [chainMat_succ, ← Matrix.mulVec_mulVec, ← ih]
    exact kerF_N Dc u Q f0 nF eF XF nS eS XS i h _

theorem chain_N (x : Fin (cF Dc u Q nF XF nS XS 0) → K) :
    eL Dc u Q nF XF nS eS XS Q.n (by omega)
      ((Formalism.DivisionValues.chainMat (c := cF Dc u Q nF XF nS XS)
        (KjN Dc u Q f0 nF eF XF nS eS XS) (Fin.last (Q.n + 1))).mulVec x) = Q.col (coFN Dc u Q f0 nF eF XF nS XS 0 (Nat.zero_le _) x) := by
  have hi : Q.n < Q.n + 1 := by omega
  show eL Dc u Q nF XF nS eS XS Q.n (by omega)
      ((Formalism.DivisionValues.chainMat (c := cF Dc u Q nF XF nS XS)
        (KjN Dc u Q f0 nF eF XF nS eS XS) (Fin.succ ⟨Q.n, hi⟩)).mulVec x) = Q.cpl (Q.kk.colTo Q.hF Q.n (coFN Dc u Q f0 nF eF XF nS XS 0 (Nat.zero_le _) x))
  rw [chainMat_succ, ← Matrix.mulVec_mulVec, ← chain_le_N Dc u Q f0 nF eF XF nS eS XS Q.n le_rfl x]
  exact kerC_N Dc u Q f0 nF eF XF nS eS XS _

end GlobalTheory.DefRowsChain

namespace GlobalTheory.DefRowsChain

variable {K : Type} [Field K] [NumberField K] [StarRing K] {Bs : DefBase K} {Df : DefSide Bs}
  (Dc : DefCols Df) (u : Dc.Mem) (Q : KerChain K) (f0 : (Fin (Dc.a u) → K) →ₗ[K] (Q.F 0).Forms)
  (nF : ℕ → ℕ) (eF : ∀ i, (Fin (nF i) → K) ≃ₗ[K] (Q.F i).Forms) (XF : ∀ i, InfinitePlace K → Matrix (Fin (nF i)) (Fin (nF i)) ℂ)
  (nS : ℕ) (eS : (Fin nS → K) ≃ₗ[K] Q.S₁.EqFun) (XS : InfinitePlace K → Matrix (Fin nS) (Fin nS) ℂ)

theorem unit_N (h1 : ∀ v, IsUnit (Dc.Xc u v).det) (hXu : ∀ i v, IsUnit (XF i v).det) (hSu : ∀ v, IsUnit (XS v).det) :
    ∀ k v, IsUnit ((bund Dc u Q nF XF nS XS k).2 v).det
  | 0, v => h1 v
  | k + 1, v => by
    by_cases h : k + 1 ≤ Q.n
    · exact unit_of_eq _ _ _ (bund_succ_le Dc u Q nF XF nS XS k h) v (hXu _ v)
    · exact unit_of_eq _ _ _ (bund_succ_gt Dc u Q nF XF nS XS k h) v (hSu v)

theorem metF_N (h2 : ∀ v x, ((Formalism.HermitianLatticesTheory.normAt (Pi.basisFun K (Fin (Dc.a u))) (Dc.Xc u) v x ^ 2 : ℝ) : ℂ) =
      famIpAt (Q.F 0) (Q.hF 0) v (f0 x) (f0 x))
    (hXi : ∀ i v x, ((Formalism.HermitianLatticesTheory.normAt (Pi.basisFun K (Fin (nF i))) (XF i) v x ^ 2 : ℝ) : ℂ) =
      famIpAt (Q.F i) (Q.hF i) v (eF i x) (eF i x)) :
    ∀ i (h : i ≤ Q.n) (v : InfinitePlace K) (x : Fin (bund Dc u Q nF XF nS XS i).1 → K),
      ((Formalism.HermitianLatticesTheory.normAt (Pi.basisFun K (Fin (bund Dc u Q nF XF nS XS i).1)) (bund Dc u Q nF XF nS XS i).2 v x ^ 2 : ℝ) : ℂ) =
        famIpAt (Q.F i) (Q.hF i) v (coFN Dc u Q f0 nF eF XF nS XS i h x) (coFN Dc u Q f0 nF eF XF nS XS i h x)
  | 0, _, v, x => h2 v x
  | k + 1, h, v, x => by
    rw [normAt_of_eq _ _ _ (bund_succ_le Dc u Q nF XF nS XS k h) (congrArg Sigma.fst (bund_succ_le Dc u Q nF XF nS XS k h)).symm]
    exact hXi (k + 1) v _

theorem metL_N (hSi : ∀ v x, ((Formalism.HermitianLatticesTheory.normAt (Pi.basisFun K (Fin nS)) XS v x ^ 2 : ℝ) : ℂ) = Q.S₁.ipAt Q.hS₁ v (eS x) (eS x))
    (k : ℕ) (h : ¬ k + 1 ≤ Q.n) (v : InfinitePlace K) (x : Fin (bund Dc u Q nF XF nS XS (k + 1)).1 → K) :
    ((Formalism.HermitianLatticesTheory.normAt (Pi.basisFun K (Fin (bund Dc u Q nF XF nS XS (k + 1)).1)) (bund Dc u Q nF XF nS XS (k + 1)).2 v x ^ 2 : ℝ) : ℂ) =
      Q.S₁.ipAt Q.hS₁ v (eL Dc u Q nF XF nS eS XS k h x) (eL Dc u Q nF XF nS eS XS k h x) := by
  rw [normAt_of_eq _ _ _ (bund_succ_gt Dc u Q nF XF nS XS k h) (congrArg Sigma.fst (bund_succ_gt Dc u Q nF XF nS XS k h)).symm]
  exact hSi v _

end GlobalTheory.DefRowsChain

namespace GlobalTheory.DefRowsChain

variable {K : Type} [Field K] [NumberField K] [StarRing K] {Bs : DefBase K} {Df : DefSide Bs}

def chainOf (Dc : DefCols Df) (u : Dc.Mem) (Q : KerChain K) (f0 : (Fin (Dc.a u) → K) →ₗ[K] (Q.F 0).Forms)
    (g : Q.S₁.EqFun →ₗ[K] Module.Dual K (Fin (Df.nV Bs.μ0) → K)) (no : Bs.J → ℕ)
    (nF : ℕ → ℕ) (eF : ∀ i, (Fin (nF i) → K) ≃ₗ[K] (Q.F i).Forms) (XF : ∀ i, InfinitePlace K → Matrix (Fin (nF i)) (Fin (nF i)) ℂ)
    (nS : ℕ) (eS : (Fin nS → K) ≃ₗ[K] Q.S₁.EqFun) (XS : InfinitePlace K → Matrix (Fin nS) (Fin nS) ℂ)
    (h1 : ∀ v, IsUnit (Dc.Xc u v).det) (hXu : ∀ i v, IsUnit (XF i v).det) (hSu : ∀ v, IsUnit (XS v).det)
    (h5 : ∀ φ F, Dc.Pt u Bs.μ0 φ F = g (Q.col (f0 φ)) F) : ColChain Dc u where
  mm := Q.n + 1
  lf l := ⟨min (no l) Q.n, by omega⟩
  c := cF Dc u Q nF XF nS XS
  c0 := rfl
  X i := (bund Dc u Q nF XF nS XS i.val).2
  X_unit i v := unit_N Dc u Q nF XF nS XS h1 hXu hSu i.val v
  X_zero _ _ _ := rfl
  Kj := KjN Dc u Q f0 nF eF XF nS eS XS
  PtL := g ∘ₗ (eL Dc u Q nF XF nS eS XS Q.n (by omega)).toLinearMap
  fact φ F := by
    rw [h5]
    show g (Q.col (coFN Dc u Q f0 nF eF XF nS XS 0 (Nat.zero_le _) φ)) F = _
    rw [← chain_N Dc u Q f0 nF eF XF nS eS XS φ]
    rfl

def tieOf (Dc : DefCols Df) (u : Dc.Mem) (Q : KerChain K) (f0 : (Fin (Dc.a u) → K) →ₗ[K] (Q.F 0).Forms)
    (g : Q.S₁.EqFun →ₗ[K] Module.Dual K (Fin (Df.nV Bs.μ0) → K)) (no : Bs.J → ℕ)
    (nF : ℕ → ℕ) (eF : ∀ i, (Fin (nF i) → K) ≃ₗ[K] (Q.F i).Forms) (XF : ∀ i, InfinitePlace K → Matrix (Fin (nF i)) (Fin (nF i)) ℂ)
    (nS : ℕ) (eS : (Fin nS → K) ≃ₗ[K] Q.S₁.EqFun) (XS : InfinitePlace K → Matrix (Fin nS) (Fin nS) ℂ)
    (h1 : ∀ v, IsUnit (Dc.Xc u v).det) (hXu : ∀ i v, IsUnit (XF i v).det) (hSu : ∀ v, IsUnit (XS v).det)
    (h5 : ∀ φ F, Dc.Pt u Bs.μ0 φ F = g (Q.col (f0 φ)) F)
    (h2 : ∀ v x, ((Formalism.HermitianLatticesTheory.normAt (Pi.basisFun K (Fin (Dc.a u))) (Dc.Xc u) v x ^ 2 : ℝ) : ℂ) =
      famIpAt (Q.F 0) (Q.hF 0) v (f0 x) (f0 x))
    (hXi : ∀ i v x, ((Formalism.HermitianLatticesTheory.normAt (Pi.basisFun K (Fin (nF i))) (XF i) v x ^ 2 : ℝ) : ℂ) =
      famIpAt (Q.F i) (Q.hF i) v (eF i x) (eF i x))
    (hSi : ∀ v x, ((Formalism.HermitianLatticesTheory.normAt (Pi.basisFun K (Fin nS)) XS v x ^ 2 : ℝ) : ℂ) = Q.S₁.ipAt Q.hS₁ v (eS x) (eS x)) :
    ChainTie (chainOf Dc u Q f0 g no nF eF XF nS eS XS h1 hXu hSu h5) Q where
  hmm := rfl
  coF := coFN Dc u Q f0 nF eF XF nS XS
  coL := (eL Dc u Q nF XF nS eS XS Q.n (by omega)).toLinearMap
  metF := metF_N Dc u Q f0 nF eF XF nS XS h2 hXi
  metL := metL_N Dc u Q nF XF nS eS XS hSi Q.n (by omega)
  kerF := kerF_N Dc u Q f0 nF eF XF nS eS XS
  kerC := kerC_N Dc u Q f0 nF eF XF nS eS XS

end GlobalTheory.DefRowsChain

namespace GlobalTheory.DefRowsChain

theorem sq_le_of (a b s : ℝ) (za zb : ℂ) (ha : ((a ^ 2 : ℝ) : ℂ) = za) (hb : ((b ^ 2 : ℝ) : ℂ) = zb)
    (hs : za.re ≤ Real.exp s * zb.re) : a ^ 2 ≤ Real.exp s * b ^ 2 := by
  subst ha hb
  rw [Complex.ofReal_re, Complex.ofReal_re] at hs
  exact hs

def tOf {K : Type} [Field K] [NumberField K] [StarRing K] {J Pl : Type} [Fintype J] [Fintype Pl] [DecidableEq Pl] {R : RecNums J Pl}
    (hn : HtNums R (InfinitePlace K)) (n : ℕ) (no : J → ℕ) (j : Fin (n + 1)) (v : InfinitePlace K) : ℝ :=
  ∑ l ∈ Finset.univ.filter (fun l => (⟨min (no l) n, by omega⟩ : Fin (n + 1)) = j), hn.sz l v

theorem rowsBody_of_framed : ∀ (K : Type) [Field K] [NumberField K] [StarRing K] [IsTotallyComplex K] (Bs : DefBase K) (Df : DefSide Bs) (Dc : DefCols Df) (u : Dc.Mem) (Q : KerChain K) (f0 : (Fin (Dc.a u) → K) →ₗ[K] (Q.F 0).Forms) (g : Q.S₁.EqFun →ₗ[K] Module.Dual K (Fin (Df.nV Bs.μ0) → K)) (Pl : Type) [Fintype Pl] [DecidableEq Pl] (R : RecNums Bs.J Pl) (hn : HtNums R (InfinitePlace K)) (no : Bs.J → ℕ) (X0 : InfinitePlace K → Matrix (Fin (Df.nV Bs.μ0)) (Fin (Df.nV Bs.μ0)) ℂ), (∀ v, IsUnit (Dc.Xc u v).det) → (∀ v x, ((Formalism.HermitianLatticesTheory.normAt (Pi.basisFun K (Fin (Dc.a u))) (Dc.Xc u) v x ^ 2 : ℝ) : ℂ) = famIpAt (Q.F 0) (Q.hF 0) v (f0 x) (f0 x)) → (∀ i, FamFramed (Q.F i) (Q.hF i)) → DatFramed Q.S₁ Q.hS₁ → (∀ φ F, Dc.Pt u Bs.μ0 φ F = g (Q.col (f0 φ)) F) → IsFrames Df X0 → FactorBounds Q no hn.sz → (∀ (v : InfinitePlace K) (ψ : Q.S₁.EqFun) F, v (g ψ F) ^ 2 ≤ Real.exp hn.hPn * (Q.S₁.ipAt Q.hS₁ v ψ ψ).re * Formalism.HermitianLatticesTheory.normAt (Pi.basisFun K (Fin (Df.nV Bs.μ0))) X0 v F ^ 2) → RowsBody Dc u Q f0 R := by
  intro K _ _ _ _ Bs Df Dc u Q f0 g Pl _ _ R hn no X0 h1 h2 h3 h4 h5 h6 h7 h8
  choose nF eF XF hXu hXi using h3
  obtain ⟨nS, eS, XS, hSu, hSi⟩ := h4
  let ch := chainOf Dc u Q f0 g no nF eF XF nS eS XS h1 hXu hSu h5
  let T := tieOf Dc u Q f0 g no nF eF XF nS eS XS h1 hXu hSu h5 h2 hXi hSi
  have hb : ∀ (j : Fin (Q.n + 1)) v (x : Fin (ch.c j.castSucc) → K),
      Formalism.HermitianLatticesTheory.normAt (Pi.basisFun K (Fin (ch.c j.succ))) (ch.X j.succ) v ((ch.Kj j).mulVec x) ^ 2 ≤
        Real.exp (tOf hn Q.n no j v) *
          Formalism.HermitianLatticesTheory.normAt (Pi.basisFun K (Fin (ch.c j.castSucc))) (ch.X j.castSucc) v x ^ 2 := by
    intro j
    induction j using Fin.lastCases with
    | last =>
      intro v x
      have hs : tOf hn Q.n no (Fin.last Q.n) v = ∑ l ∈ Finset.univ.filter (fun l => Q.n ≤ no l), hn.sz l v := by
        refine Finset.sum_congr (Finset.filter_congr fun l _ => ?_) fun _ _ => rfl
        simp only [Fin.ext_iff, Fin.val_last]
        omega
      rw [hs]
      refine sq_le_of _ _ _ _ _ (T.cpl_norm v x) (T.metF Q.n le_rfl v x) ?_
      exact h7.2 v _
    | cast i =>
      intro v x
      have hs : tOf hn Q.n no (Fin.castSucc i) v = ∑ l ∈ Finset.univ.filter (fun l => no l = i.val), hn.sz l v := by
        refine Finset.sum_congr (Finset.filter_congr fun l _ => ?_) fun _ _ => rfl
        simp only [Fin.ext_iff, Fin.val_castSucc]
        have := i.isLt
        omega
      rw [hs]
      refine sq_le_of _ _ _ _ _ (T.step_norm i.val i.isLt v x) (T.metF i.val i.isLt.le v x) ?_
      exact h7.1 i.val i.isLt v _
  obtain ⟨cb, hcb⟩ := GlobalTheory.DefRowsCB.exists_cbData K (Q.n + 1) ch.c ch.X ch.Kj
    (tOf hn Q.n no) ch.X_unit hb
  refine ⟨ch, T, fun _ => rfl, X0, h6, hn, fun v => ?_, cb, hcb⟩
  refine GlobalTheory.T.opNormAt_pairing_sq_le_of_value_bound K _ _ (ch.X (Fin.last ch.mm)) X0 ch.PtL v hn.hPn (ch.X_unit _ v) (h6 v).1 fun y F => ?_
  have hm := T.metL v y
  have e : Formalism.HermitianLatticesTheory.normAt (Pi.basisFun K (Fin (ch.c (Fin.last ch.mm)))) (ch.X (Fin.last ch.mm)) v y ^ 2 =
      (Q.S₁.ipAt Q.hS₁ v (T.coL y) (T.coL y)).re := by
    have := congrArg Complex.re hm
    rw [Complex.ofReal_re] at this
    exact this
  rw [e]
  exact h8 v (T.coL y) F

end GlobalTheory.DefRowsChain
