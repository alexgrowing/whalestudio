import Formalism.LocalToGlobal.InertKernelTheory.DefsRep

noncomputable section

namespace Formalism.L2.KerInert.RepFrame

open Formalism.MainNotions.FormalGroupSystem Formalism.L2.Th1.D Formalism.L2.Th1.Top Formalism.L2.KerInert.K1
open Formalism.InvariantFactorPaths.G7 (UnrOK)
open Formalism.L2.Th1.CM (MaximalUnramifiedExtension)
open Formalism.L2.G.Pend (k0ToC wittFractionAlgebraCp OcC Frm thA thFOf invF zOfX tw mAt rank_eq)
open Formalism.MainNotions.FormalGroupSystem (Sys)
open NumberField Formalism.BasicNotions Formalism.MainNotions.TaylorLogMetric Formalism.L2.Ker

variable {p : ℕ} [Fact p.Prime] (X : Sys p) [IsFractionRing X.G.O X.G.Kf] (E : Formalism.L2.G.Pend.CEmbC X.G)
  {T : Type} [Fintype T] (pos : (Σ v : X.Pl, Fin (X.G.P.n' v)) ≃ T)

def kapInv (j : ℕ) (y : T × Fin ((X.Pj (j + 1)).m + 1) × Fin ((X.Pj j).m + 1)) : X.ZA j :=
  ⟨(pos.symm y.1).1, ((pos.symm y.1).2, Fin.cast (rank_eq X j) y.2.2, Fin.cast (rank_eq X (j + 1)) y.2.1)⟩

def linFrame {j : ℕ} {L0 : X.Lt j} {La' : X.Lt (j + 1)} (φ : Frm X j L0 La')
    (S : (T × Fin ((X.Pj (j + 1)).m + 1) × Fin ((X.Pj j).m + 1)) → (T × Fin ((X.Pj (j + 1)).m + 1) × Fin ((X.Pj j).m + 1)) → ℂ_[p])
    (k : T × Fin ((X.Pj (j + 1)).m + 1) × Fin ((X.Pj j).m + 1)) : MvPowerSeries (X.EA j ⊕ X.EA j) ℂ_[p] :=
  letI := wittFractionAlgebraCp p
  letI := Formalism.L2.G.Pend.algKfC E.toCEmb
  ∑ y, MvPowerSeries.C (S k y) * invF ℂ_[p] φ (kapInv X pos j y)

open Classical in

def subGen (M : ∀ j, X.Lt j → ∀ v : X.Pl, Matrix (Fin ((X.Pj j).m + 1)) (Fin ((X.Pj j).m + 1)) (X.G.P.Qq v))
    (j : ℕ) (La : X.Lt j) (La' : X.Lt (j + 1))
    (x y : T × Fin ((X.Pj (j + 1)).m + 1) × Fin ((X.Pj j).m + 1)) : ℂ_[p] :=
  letI := wittFractionAlgebraCp p
  letI := Formalism.L2.G.Pend.algKfC E.toCEmb
  if x.1 = y.1 then
    (if IsOddPos (pos.symm x.1).2 then
      (M j La (pos.symm x.1).1).map (tw X ℂ_[p] (pos.symm x.1).1 (pos.symm x.1).2) x.2.2 y.2.2 *
        ((M (j + 1) La' (pos.symm x.1).1)⁻¹).map (tw X ℂ_[p] (pos.symm x.1).1 (pos.symm x.1).2) y.2.1 x.2.1
    else
      (M (j + 1) La' (pos.symm x.1).1).map (tw X ℂ_[p] (pos.symm x.1).1 (pos.symm x.1).2) x.2.1 y.2.1 *
        ((M j La (pos.symm x.1).1)⁻¹).map (tw X ℂ_[p] (pos.symm x.1).1 (pos.symm x.1).2) y.2.2 x.2.2)
  else 0

def stdLin (M : ∀ j, X.Lt j → ∀ v : X.Pl, Matrix (Fin ((X.Pj j).m + 1)) (Fin ((X.Pj j).m + 1)) (X.G.P.Qq v))
    {j : ℕ} {L0 : X.Lt j} {La' : X.Lt (j + 1)} (φ : Frm X j L0 La')
    (k : T × Fin ((X.Pj (j + 1)).m + 1) × Fin ((X.Pj j).m + 1)) : MvPowerSeries (X.EA j ⊕ X.EA j) ℂ_[p] :=
  letI := wittFractionAlgebraCp p
  letI := Formalism.L2.G.Pend.algKfC E.toCEmb
  if IsOddPos (pos.symm k.1).2 then
    ∑ a' : Fin (Formalism.MainNotions.FormalGroupSystem.NN X.G.P.m X.t j), ∑ b' : Fin (Formalism.MainNotions.FormalGroupSystem.NN X.G.P.m X.t (j + 1)),
      MvPowerSeries.C (mAt X ℂ_[p] j (pos.symm k.1).1 (pos.symm k.1).2 (M j L0 (pos.symm k.1).1 * (φ.g (pos.symm k.1).1 : Matrix _ _ _))
          (Fin.cast (rank_eq X j) k.2.2) a' *
        mAt X ℂ_[p] (j + 1) (pos.symm k.1).1 (pos.symm k.1).2
          ((((φ.g' (pos.symm k.1).1)⁻¹ : GL _ _) : Matrix _ _ _) * (M (j + 1) La' (pos.symm k.1).1)⁻¹)
          b' (Fin.cast (rank_eq X (j + 1)) k.2.1)) *
      zOfX X ℂ_[p] j ⟨(pos.symm k.1).1, ((pos.symm k.1).2, a', b')⟩
  else
    ∑ a' : Fin (Formalism.MainNotions.FormalGroupSystem.NN X.G.P.m X.t j), ∑ b' : Fin (Formalism.MainNotions.FormalGroupSystem.NN X.G.P.m X.t (j + 1)),
      MvPowerSeries.C (mAt X ℂ_[p] (j + 1) (pos.symm k.1).1 (pos.symm k.1).2
          (M (j + 1) La' (pos.symm k.1).1 * (φ.g' (pos.symm k.1).1 : Matrix _ _ _)) (Fin.cast (rank_eq X (j + 1)) k.2.1) b' *
        mAt X ℂ_[p] j (pos.symm k.1).1 (pos.symm k.1).2
          ((((φ.g (pos.symm k.1).1)⁻¹ : GL _ _) : Matrix _ _ _) * (M j L0 (pos.symm k.1).1)⁻¹)
          a' (Fin.cast (rank_eq X j) k.2.2)) *
      zOfX X ℂ_[p] j ⟨(pos.symm k.1).1, ((pos.symm k.1).2, a', b')⟩

variable (hfin : ∀ j c, (X.Lv.lev j c).FinClasses) (D : D7) (pos' : (Σ v : X.Pl, Fin (X.G.P.n' v)) ≃ D.what₂.Tau)
    (large₂ : ∀ j, X.Lt j → X.Lt (j + 1) → Submodule (𝓞 D.host.E) (Fin ((X.Pj j).m + 1) → D.host.E))
    (Lg' : ∀ j, X.Lt j → X.Lt (j + 1) → Submodule (𝓞 D.host.E) (Fin ((X.Pj (j + 1)).m + 1) → D.host.E))

def FrameLin (S : ∀ j, X.Lt j → X.Lt (j + 1) →
      (D.what₂.Tau × Fin ((X.Pj (j + 1)).m + 1) × Fin ((X.Pj j).m + 1)) →
      (D.what₂.Tau × Fin ((X.Pj (j + 1)).m + 1) × Fin ((X.Pj j).m + 1)) → ℂ_[p])
    (lam : Qbar →+* ℂ_[p]) (c : ℂ_[p]) : Prop :=
  ∀ j (L0 : X.Lt j), L0 ∈ Formalism.L2.G.Pend.repOf X.Lv hfin j → ∀ La' : X.Lt (j + 1), (X.Pj (j + 1)).IsLatTup La'.2 →
    ∀ φ : Frm X j L0 La', ∃ (r : ℕ) (b : Fin r → Matrix (Fin ((X.Pj (j + 1)).m + 1)) (Fin ((X.Pj j).m + 1)) D.host.E),
      LocBasis D p (YYl D (large₂ j L0 La') (Lg' j L0 La')) b ∧ Orthonormal D b ∧
      ∃ (σ : MaximalUnramifiedExtension p →+* MaximalUnramifiedExtension p) (f f' : X.EA j → Fin r → MaximalUnramifiedExtension p), UnrOK (MaximalUnramifiedExtension p) p σ ∧ IsHypPair σ f f' ∧
        ∀ k, linFrame X E pos' φ (S j L0 La') k =
          ∑ i, MvPowerSeries.C (c * lamC lam (embT D k.1 (b i k.2.1 k.2.2))) * hypLin p f f' i

def FrameStd (M : ∀ j, X.Lt j → ∀ v : X.Pl, Matrix (Fin ((X.Pj j).m + 1)) (Fin ((X.Pj j).m + 1)) (X.G.P.Qq v))
    (lam : Qbar →+* ℂ_[p]) (c : ℂ_[p]) : Prop :=
  ∀ j (L0 : X.Lt j), L0 ∈ Formalism.L2.G.Pend.repOf X.Lv hfin j → ∀ La' : X.Lt (j + 1), (X.Pj (j + 1)).IsLatTup La'.2 →
    ∀ φ : Frm X j L0 La', ∃ (r : ℕ) (b : Fin r → Matrix (Fin ((X.Pj (j + 1)).m + 1)) (Fin ((X.Pj j).m + 1)) D.host.E),
      LocBasis D p (YYl D (large₂ j L0 La') (Lg' j L0 La')) b ∧ Orthonormal D b ∧
      ∃ (σ : MaximalUnramifiedExtension p →+* MaximalUnramifiedExtension p) (f f' : X.EA j → Fin r → MaximalUnramifiedExtension p), UnrOK (MaximalUnramifiedExtension p) p σ ∧ IsHypPair σ f f' ∧
        ∀ k, stdLin X E pos' M φ k =
          ∑ i, MvPowerSeries.C (c * lamC lam (embT D k.1 (b i k.2.1 k.2.2))) * hypLin p f f' i

end Formalism.L2.KerInert.RepFrame

namespace Formalism.L2.KerInert.RepFrame

open Formalism.MainNotions.FormalGroupSystem Formalism.L2.Th1.D Formalism.L2.Th1.Top Formalism.L2.KerInert.K1
open Formalism.InvariantFactorPaths.G7 (UnrOK)
open Formalism.L2.Th1.CM (MaximalUnramifiedExtension)
open Formalism.L2.G.Pend (Frm)
open NumberField Formalism.BasicNotions Formalism.MainNotions.TaylorLogMetric Formalism.L2.Ker

section Coord

variable (D : D7) {p : ℕ} [Fact p.Prime] (lam : Qbar →+* ℂ_[p]) {N N' r : ℕ} (b : Fin r → Matrix (Fin N') (Fin N) D.host.E)

def lamB (k : D.what₂.Tau × Fin N' × Fin N) (i : Fin r) : ℂ_[p] := lamC lam (embT D k.1 (b i k.2.1 k.2.2))

def lamBc (k : D.what₂.Tau × Fin N' × Fin N) (i : Fin r) : ℂ_[p] :=
  lamC lam (embT D k.1 (D.host.conj (b i k.2.1 k.2.2)))

open Classical in

def LamONB : Prop :=
  ∀ k k' : D.what₂.Tau × Fin N' × Fin N, ∑ i, lamB D lam b k i * lamBc D lam b k' i = if k = k' then 1 else 0

end Coord

variable {p : ℕ} [Fact p.Prime] (X : Sys p) [IsFractionRing X.G.O X.G.Kf] (E : Formalism.L2.G.Pend.CEmbC X.G)
  {T : Type} [Fintype T] (pos : (Σ v : X.Pl, Fin (X.G.P.n' v)) ≃ T)

def frVec (M : ∀ j, X.Lt j → ∀ v : X.Pl, Matrix (Fin ((X.Pj j).m + 1)) (Fin ((X.Pj j).m + 1)) (X.G.P.Qq v))
    {j : ℕ} {L0 : X.Lt j} {La' : X.Lt (j + 1)} (φ : Frm X j L0 La') (y : X.EA j ⊕ X.EA j)
    (k : T × Fin ((X.Pj (j + 1)).m + 1) × Fin ((X.Pj j).m + 1)) : ℂ_[p] :=
  MvPowerSeries.coeff (Finsupp.single y 1) (stdLin X E pos M φ k)

variable (hfin : ∀ j c, (X.Lv.lev j c).FinClasses) (D : D7) (pos' : (Σ v : X.Pl, Fin (X.G.P.n' v)) ≃ D.what₂.Tau)
    (large₂ : ∀ j, X.Lt j → X.Lt (j + 1) → Submodule (𝓞 D.host.E) (Fin ((X.Pj j).m + 1) → D.host.E))
    (Lg' : ∀ j, X.Lt j → X.Lt (j + 1) → Submodule (𝓞 D.host.E) (Fin ((X.Pj (j + 1)).m + 1) → D.host.E))

def OnbEx : Prop :=
  ∀ j (L0 : X.Lt j), L0 ∈ Formalism.L2.G.Pend.repOf X.Lv hfin j → ∀ La' : X.Lt (j + 1), (X.Pj (j + 1)).IsLatTup La'.2 →
    ∃ (r : ℕ) (b : Fin r → Matrix (Fin ((X.Pj (j + 1)).m + 1)) (Fin ((X.Pj j).m + 1)) D.host.E),
      LocBasis D p (YYl D (large₂ j L0 La') (Lg' j L0 La')) b ∧ Orthonormal D b

def LamTrace (lam : Qbar →+* ℂ_[p]) : Prop :=
  ∀ j (L0 : X.Lt j), L0 ∈ Formalism.L2.G.Pend.repOf X.Lv hfin j → ∀ La' : X.Lt (j + 1), (X.Pj (j + 1)).IsLatTup La'.2 →
    ∀ (r : ℕ) (b : Fin r → Matrix (Fin ((X.Pj (j + 1)).m + 1)) (Fin ((X.Pj j).m + 1)) D.host.E),
      LocBasis D p (YYl D (large₂ j L0 La') (Lg' j L0 La')) b → Orthonormal D b → LamONB D lam b

def HypCoord (M : ∀ j, X.Lt j → ∀ v : X.Pl, Matrix (Fin ((X.Pj j).m + 1)) (Fin ((X.Pj j).m + 1)) (X.G.P.Qq v))
    (lam : Qbar →+* ℂ_[p]) (c : ℂ_[p]) : Prop :=
  ∀ j (L0 : X.Lt j), L0 ∈ Formalism.L2.G.Pend.repOf X.Lv hfin j → ∀ La' : X.Lt (j + 1), (X.Pj (j + 1)).IsLatTup La'.2 →
    ∀ (r : ℕ) (b : Fin r → Matrix (Fin ((X.Pj (j + 1)).m + 1)) (Fin ((X.Pj j).m + 1)) D.host.E),
      LocBasis D p (YYl D (large₂ j L0 La') (Lg' j L0 La')) b → Orthonormal D b → ∀ φ : Frm X j L0 La',
      ∃ (σ : MaximalUnramifiedExtension p →+* MaximalUnramifiedExtension p) (f f' : X.EA j → Fin r → MaximalUnramifiedExtension p), UnrOK (MaximalUnramifiedExtension p) p σ ∧ IsHypPair σ f f' ∧
        (∀ e i, (f e i : ℂ_[p]) = c⁻¹ * ∑ k, lamBc D lam b k i * frVec X E pos' M φ (Sum.inl e) k) ∧
        (∀ e i, (f' e i : ℂ_[p]) = c⁻¹ * ∑ k, lamBc D lam b k i * frVec X E pos' M φ (Sum.inr e) k)

end Formalism.L2.KerInert.RepFrame

namespace Formalism.L2.KerInert.RepFrame

open Formalism.MainNotions.FormalGroupSystem
open NumberField Formalism.BasicNotions Formalism.MainNotions.TaylorLogMetric Formalism.L2.Ker

variable {p : ℕ} [Fact p.Prime] (X : Sys p) (hfin : ∀ j c, (X.Lv.lev j c).FinClasses) (D : D7)
    (large₂ : ∀ j, X.Lt j → X.Lt (j + 1) → Submodule (𝓞 D.host.E) (Fin ((X.Pj j).m + 1) → D.host.E))
    (Lg' : ∀ j, X.Lt j → X.Lt (j + 1) → Submodule (𝓞 D.host.E) (Fin ((X.Pj (j + 1)).m + 1) → D.host.E))

def RankTie : Prop :=
  ∀ j (L0 : X.Lt j), L0 ∈ Formalism.L2.G.Pend.repOf X.Lv hfin j → ∀ La' : X.Lt (j + 1), (X.Pj (j + 1)).IsLatTup La'.2 →
    ∀ (r : ℕ) (b : Fin r → Matrix (Fin ((X.Pj (j + 1)).m + 1)) (Fin ((X.Pj j).m + 1)) D.host.E),
      LocBasis D p (YYl D (large₂ j L0 La') (Lg' j L0 La')) b →
        r = Fintype.card (D.what₂.Tau × Fin ((X.Pj (j + 1)).m + 1) × Fin ((X.Pj j).m + 1))

open Classical in

def ColTie (lam : Qbar →+* ℂ_[p]) : Prop :=
  ∀ j (L0 : X.Lt j), L0 ∈ Formalism.L2.G.Pend.repOf X.Lv hfin j → ∀ La' : X.Lt (j + 1), (X.Pj (j + 1)).IsLatTup La'.2 →
    ∀ (r : ℕ) (b : Fin r → Matrix (Fin ((X.Pj (j + 1)).m + 1)) (Fin ((X.Pj j).m + 1)) D.host.E),
      LocBasis D p (YYl D (large₂ j L0 La') (Lg' j L0 La')) b → Orthonormal D b →
        ∀ i i', ∑ k, lamBc D lam b k i * lamB D lam b k i' = if i = i' then 1 else 0

end Formalism.L2.KerInert.RepFrame

namespace Formalism.L2.KerInert.RepFrame

open NumberField Formalism.BasicNotions Formalism.MainNotions.TaylorLogMetric Formalism.L2.Ker

def TraceTau (D : D7) : Prop :=
  ∀ y : D.host.E, ∑ τ : D.what₂.Tau, embT D τ y = D.host.φ₀ ((Algebra.trace D.host.K D.host.E y : D.host.K) : D.host.E)

end Formalism.L2.KerInert.RepFrame
