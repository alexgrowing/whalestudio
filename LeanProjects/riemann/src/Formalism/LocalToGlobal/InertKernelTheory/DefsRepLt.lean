import Formalism.LocalToGlobal.InertKernelTheory.DefsRep
import Formalism.LocalToGlobal.InertKernelTheory.DefsRepFrame
import Formalism.LocalToGlobal.InertKernelTheory.FrameLatMap
import Formalism.LocalToGlobal.InertKernelTheory.InertCoprimeLemmas.RepTwLat
import Formalism.LocalToGlobal.InertKernelTheory.ScalG

noncomputable section

open scoped Matrix

namespace Formalism.L2.KerInert.RepLt

open Formalism.MainNotions.FormalGroupSystem Formalism.L2.Th1.D Formalism.L2.Th1.Top Formalism.L2.KerInert.K1
open Formalism.InvariantFactorPaths.G7 (UnrOK)
open Formalism.L2.Th1.CM (MaximalUnramifiedExtension)
open Formalism.L2.G.Pend (k0ToC wittFractionAlgebraCp OcC Frm thA thFOf)
open NumberField Formalism.BasicNotions Formalism.MainNotions.TaylorLogMetric Formalism.L2.Ker
open Formalism.L2.KerInert.Rep (thOrth)
open Formalism.L2.KerInert.RepFrame (Gm Gp Gmi Gpi twE LamONB frVec lamB lamBc stdLin linFrame)
open Formalism.L2.KerInert.RepTwLat (locSpan SelfDualP)

def FirstKernelLawLocalPowerSeries {p : ℕ} [Fact p.Prime] (X : Sys p) [IsFractionRing X.G.O X.G.Kf] (E : Formalism.L2.G.Pend.CEmbC X.G)
    (hfin : ∀ j c, (X.Lv.lev j c).FinClasses) (be : MvPowerSeries (Fin 2) (K0 p)) {T : Type}
    (pos : (Σ v : X.Pl, Fin (X.G.P.n' v)) ≃ T)
    (F : ∀ j, X.Lt j → X.Lt (j + 1) → MvPowerSeries (T × Fin ((X.Pj (j + 1)).m + 1) × Fin ((X.Pj j).m + 1)) ℂ_[p]) : Prop :=
  letI := wittFractionAlgebraCp p
  letI := Formalism.L2.G.Pend.algKfC E.toCEmb
  ∀ j, j < X.mm → ∀ (L0 : X.Lt j), L0 ∈ Formalism.L2.G.Pend.repOf X.Lv hfin j → ∀ La' : X.Lt (j + 1),
    (X.Pj (j + 1)).IsLatTup La'.2 →
    ∀ φ : Frm X j L0 La', ExtensionGeneratorCondition p ℂ_[p] (OcC p) be (thA ℂ_[p] φ (thFOf X pos F j L0 La'))

def OrthAllLt {p : ℕ} [Fact p.Prime] (X : Sys p) [IsFractionRing X.G.O X.G.Kf] (E : Formalism.L2.G.Pend.CEmbC X.G)
    (hfin : ∀ j c, (X.Lv.lev j c).FinClasses) {T : Type} (pos : (Σ v : X.Pl, Fin (X.G.P.n' v)) ≃ T)
    (F : ∀ j, X.Lt j → X.Lt (j + 1) → MvPowerSeries (T × Fin ((X.Pj (j + 1)).m + 1) × Fin ((X.Pj j).m + 1)) ℂ_[p])
    (g2 g3 s2 ε : MaximalUnramifiedExtension p) : Prop :=
  letI := wittFractionAlgebraCp p
  letI := Formalism.L2.G.Pend.algKfC E.toCEmb
  ∀ j, j < X.mm → ∀ (L0 : X.Lt j), L0 ∈ Formalism.L2.G.Pend.repOf X.Lv hfin j → ∀ La' : X.Lt (j + 1),
    (X.Pj (j + 1)).IsLatTup La'.2 →
    ∀ φ : Frm X j L0 La', Formalism.L2.KerInert.Rep.OrthInt p g2 g3 s2 ε (thA ℂ_[p] φ (thFOf X pos F j L0 La'))

section Glob

variable {p : ℕ} [Fact p.Prime] (X : Sys p) [IsFractionRing X.G.O X.G.Kf] (E : Formalism.L2.G.Pend.CEmbC X.G)
    (hfin : ∀ j c, (X.Lv.lev j c).FinClasses) (D : D7) (pos : (Σ v : X.Pl, Fin (X.G.P.n' v)) ≃ D.what₂.Tau)
    (large₂ : ∀ j, X.Lt j → X.Lt (j + 1) → Submodule (𝓞 D.host.E) (Fin ((X.Pj j).m + 1) → D.host.E))
    (Lg' : ∀ j, X.Lt j → X.Lt (j + 1) → Submodule (𝓞 D.host.E) (Fin ((X.Pj (j + 1)).m + 1) → D.host.E))
    (F : ∀ j, X.Lt j → X.Lt (j + 1) →
      MvPowerSeries (D.what₂.Tau × Fin ((X.Pj (j + 1)).m + 1) × Fin ((X.Pj j).m + 1)) ℂ_[p])

def CombAtLt (T : Tor D) (e : FamE D) (lam : Qbar →+* ℂ_[p]) : Prop :=
  ∀ j, j < X.mm → ∀ (L0 : X.Lt j), L0 ∈ Formalism.L2.G.Pend.repOf X.Lv hfin j → ∀ La' : X.Lt (j + 1),
    (X.Pj (j + 1)).IsLatTup La'.2 →
    admitted D _ _ (large₂ j L0 La') (Lg' j L0 La') ∧ IsComb D T e lam (large₂ j L0 La') (Lg' j L0 La') (F j L0 La')

def FrameHypLt (S : ∀ j, X.Lt j → X.Lt (j + 1) →
      (D.what₂.Tau × Fin ((X.Pj (j + 1)).m + 1) × Fin ((X.Pj j).m + 1)) →
      (D.what₂.Tau × Fin ((X.Pj (j + 1)).m + 1) × Fin ((X.Pj j).m + 1)) → ℂ_[p])
    (lam : Qbar →+* ℂ_[p]) (c : ℂ_[p]) : Prop :=
  letI := wittFractionAlgebraCp p
  letI := Formalism.L2.G.Pend.algKfC E.toCEmb
  ∀ j, j < X.mm → ∀ (L0 : X.Lt j), L0 ∈ Formalism.L2.G.Pend.repOf X.Lv hfin j → ∀ La' : X.Lt (j + 1),
    (X.Pj (j + 1)).IsLatTup La'.2 →
    ∀ φ : Frm X j L0 La', ∃ (r : ℕ) (b : Fin r → Matrix (Fin ((X.Pj (j + 1)).m + 1)) (Fin ((X.Pj j).m + 1)) D.host.E),
      LocBasis D p (YYl D (large₂ j L0 La') (Lg' j L0 La')) b ∧ Orthonormal D b ∧
      ∃ (σ : MaximalUnramifiedExtension p →+* MaximalUnramifiedExtension p) (f f' : X.EA j → Fin r → MaximalUnramifiedExtension p), UnrOK (MaximalUnramifiedExtension p) p σ ∧ IsHypPair σ f f' ∧
        thA ℂ_[p] φ (thFOf X pos (fun j La La' => linSub (S j La La') (F j La La')) j L0 La') =
          MvPowerSeries.subst (hypLin p f f') (thOrth D lam c b (F j L0 La'))

end Glob

section Frame

variable {p : ℕ} [Fact p.Prime] (X : Sys p) [IsFractionRing X.G.O X.G.Kf] (E : Formalism.L2.G.Pend.CEmbC X.G)
    (hfin : ∀ j c, (X.Lv.lev j c).FinClasses) (D : D7) (pos' : (Σ v : X.Pl, Fin (X.G.P.n' v)) ≃ D.what₂.Tau)
    (large₂ : ∀ j, X.Lt j → X.Lt (j + 1) → Submodule (𝓞 D.host.E) (Fin ((X.Pj j).m + 1) → D.host.E))
    (Lg' : ∀ j, X.Lt j → X.Lt (j + 1) → Submodule (𝓞 D.host.E) (Fin ((X.Pj (j + 1)).m + 1) → D.host.E))
    (M : ∀ j, X.Lt j → ∀ v : X.Pl, Matrix (Fin ((X.Pj j).m + 1)) (Fin ((X.Pj j).m + 1)) (X.G.P.Qq v))

def FrameLinLt (S : ∀ j, X.Lt j → X.Lt (j + 1) →
      (D.what₂.Tau × Fin ((X.Pj (j + 1)).m + 1) × Fin ((X.Pj j).m + 1)) →
      (D.what₂.Tau × Fin ((X.Pj (j + 1)).m + 1) × Fin ((X.Pj j).m + 1)) → ℂ_[p])
    (lam : Qbar →+* ℂ_[p]) (c : ℂ_[p]) : Prop :=
  ∀ j, j < X.mm → ∀ (L0 : X.Lt j), L0 ∈ Formalism.L2.G.Pend.repOf X.Lv hfin j → ∀ La' : X.Lt (j + 1),
    (X.Pj (j + 1)).IsLatTup La'.2 →
    ∀ φ : Frm X j L0 La', ∃ (r : ℕ) (b : Fin r → Matrix (Fin ((X.Pj (j + 1)).m + 1)) (Fin ((X.Pj j).m + 1)) D.host.E),
      LocBasis D p (YYl D (large₂ j L0 La') (Lg' j L0 La')) b ∧ Orthonormal D b ∧
      ∃ (σ : MaximalUnramifiedExtension p →+* MaximalUnramifiedExtension p) (f f' : X.EA j → Fin r → MaximalUnramifiedExtension p), UnrOK (MaximalUnramifiedExtension p) p σ ∧ IsHypPair σ f f' ∧
        ∀ k, linFrame X E pos' φ (S j L0 La') k =
          ∑ i, MvPowerSeries.C (c * lamC lam (embT D k.1 (b i k.2.1 k.2.2))) * hypLin p f f' i

def FrameStdLt (lam : Qbar →+* ℂ_[p]) (c : ℂ_[p]) : Prop :=
  ∀ j, j < X.mm → ∀ (L0 : X.Lt j), L0 ∈ Formalism.L2.G.Pend.repOf X.Lv hfin j → ∀ La' : X.Lt (j + 1),
    (X.Pj (j + 1)).IsLatTup La'.2 →
    ∀ φ : Frm X j L0 La', ∃ (r : ℕ) (b : Fin r → Matrix (Fin ((X.Pj (j + 1)).m + 1)) (Fin ((X.Pj j).m + 1)) D.host.E),
      LocBasis D p (YYl D (large₂ j L0 La') (Lg' j L0 La')) b ∧ Orthonormal D b ∧
      ∃ (σ : MaximalUnramifiedExtension p →+* MaximalUnramifiedExtension p) (f f' : X.EA j → Fin r → MaximalUnramifiedExtension p), UnrOK (MaximalUnramifiedExtension p) p σ ∧ IsHypPair σ f f' ∧
        ∀ k, stdLin X E pos' M φ k =
          ∑ i, MvPowerSeries.C (c * lamC lam (embT D k.1 (b i k.2.1 k.2.2))) * hypLin p f f' i

def OnbExLt : Prop :=
  ∀ j, j < X.mm → ∀ (L0 : X.Lt j), L0 ∈ Formalism.L2.G.Pend.repOf X.Lv hfin j → ∀ La' : X.Lt (j + 1),
    (X.Pj (j + 1)).IsLatTup La'.2 →
    ∃ (r : ℕ) (b : Fin r → Matrix (Fin ((X.Pj (j + 1)).m + 1)) (Fin ((X.Pj j).m + 1)) D.host.E),
      LocBasis D p (YYl D (large₂ j L0 La') (Lg' j L0 La')) b ∧ Orthonormal D b

def RankTieLt : Prop :=
  ∀ j, j < X.mm → ∀ (L0 : X.Lt j), L0 ∈ Formalism.L2.G.Pend.repOf X.Lv hfin j → ∀ La' : X.Lt (j + 1),
    (X.Pj (j + 1)).IsLatTup La'.2 →
    ∀ (r : ℕ) (b : Fin r → Matrix (Fin ((X.Pj (j + 1)).m + 1)) (Fin ((X.Pj j).m + 1)) D.host.E),
      LocBasis D p (YYl D (large₂ j L0 La') (Lg' j L0 La')) b →
        r = Fintype.card (D.what₂.Tau × Fin ((X.Pj (j + 1)).m + 1) × Fin ((X.Pj j).m + 1))

def LamTraceLt (lam : Qbar →+* ℂ_[p]) : Prop :=
  ∀ j, j < X.mm → ∀ (L0 : X.Lt j), L0 ∈ Formalism.L2.G.Pend.repOf X.Lv hfin j → ∀ La' : X.Lt (j + 1),
    (X.Pj (j + 1)).IsLatTup La'.2 →
    ∀ (r : ℕ) (b : Fin r → Matrix (Fin ((X.Pj (j + 1)).m + 1)) (Fin ((X.Pj j).m + 1)) D.host.E),
      LocBasis D p (YYl D (large₂ j L0 La') (Lg' j L0 La')) b → Orthonormal D b → LamONB D lam b

def HypCoordLt (lam : Qbar →+* ℂ_[p]) (c : ℂ_[p]) : Prop :=
  ∀ j, j < X.mm → ∀ (L0 : X.Lt j), L0 ∈ Formalism.L2.G.Pend.repOf X.Lv hfin j → ∀ La' : X.Lt (j + 1),
    (X.Pj (j + 1)).IsLatTup La'.2 →
    ∀ (r : ℕ) (b : Fin r → Matrix (Fin ((X.Pj (j + 1)).m + 1)) (Fin ((X.Pj j).m + 1)) D.host.E),
      LocBasis D p (YYl D (large₂ j L0 La') (Lg' j L0 La')) b → Orthonormal D b → ∀ φ : Frm X j L0 La',
      ∃ (σ : MaximalUnramifiedExtension p →+* MaximalUnramifiedExtension p) (f f' : X.EA j → Fin r → MaximalUnramifiedExtension p), UnrOK (MaximalUnramifiedExtension p) p σ ∧ IsHypPair σ f f' ∧
        (∀ e i, (f e i : ℂ_[p]) = c⁻¹ * ∑ k, lamBc D lam b k i * frVec X E pos' M φ (Sum.inl e) k) ∧
        (∀ e i, (f' e i : ℂ_[p]) = c⁻¹ * ∑ k, lamBc D lam b k i * frVec X E pos' M φ (Sum.inr e) k)

def FrameIntLt (ρ : ∀ v : X.Pl, D.host.E →+* X.G.P.Qq v) : Prop :=
  ∀ j, j < X.mm → ∀ (L0 : X.Lt j), L0 ∈ Formalism.L2.G.Pend.repOf X.Lv hfin j → ∀ La' : X.Lt (j + 1),
    (X.Pj (j + 1)).IsLatTup La'.2 →
    ∀ (φ : Frm X j L0 La') (r : ℕ) (b : Fin r → Matrix (Fin ((X.Pj (j + 1)).m + 1)) (Fin ((X.Pj j).m + 1)) D.host.E),
      LocBasis D p (YYl D (large₂ j L0 La') (Lg' j L0 La')) b → Orthonormal D b →
      ∀ (i : Fin r) (v : X.Pl) (s : Fin (X.G.P.n' v)) (b0 : Fin ((X.Pj (j + 1)).m + 1)) (a0 : Fin ((X.Pj j).m + 1)),
        ‖twE X E v s (∑ B, ∑ A, ρ v (D.host.conj (b i B A)) * Gp X M φ v B b0 * Gmi X M φ v a0 A)‖ ≤ 1 ∧
        ‖twE X E v s (∑ B, ∑ A, ρ v (b i B A) * Gm X M φ v A a0 * Gpi X M φ v b0 B)‖ ≤ 1

end Frame

section Lat

variable {p : ℕ} [Fact p.Prime] (X : Sys p) [IsFractionRing X.G.O X.G.Kf]
  (M : ∀ j, X.Lt j → ∀ v : X.Pl, Matrix (Fin ((X.Pj j).m + 1)) (Fin ((X.Pj j).m + 1)) (X.G.P.Qq v))
  (hfin : ∀ j c, (X.Lv.lev j c).FinClasses) (D : D7)
  (large₂ : ∀ j, X.Lt j → X.Lt (j + 1) → Submodule (𝓞 D.host.E) (Fin ((X.Pj j).m + 1) → D.host.E))
  (Lg' : ∀ j, X.Lt j → X.Lt (j + 1) → Submodule (𝓞 D.host.E) (Fin ((X.Pj (j + 1)).m + 1) → D.host.E))

def FrameLatMapLt (ρ : ∀ v : X.Pl, D.host.E →+* X.G.P.Qq v) : Prop :=
  ∀ j, j < X.mm → ∀ (L0 : X.Lt j), L0 ∈ Formalism.L2.G.Pend.repOf X.Lv hfin j → ∀ La' : X.Lt (j + 1),
    (X.Pj (j + 1)).IsLatTup La'.2 →
    ∀ (φ : Frm X j L0 La') (r : ℕ) (b : Fin r → Matrix (Fin ((X.Pj (j + 1)).m + 1)) (Fin ((X.Pj j).m + 1)) D.host.E),
      LocBasis D p (YYl D (large₂ j L0 La') (Lg' j L0 La')) b → Orthonormal D b →
      ∀ (i : Fin r) (v : X.Pl),
        (∀ c, ((b i).map (ρ v)).mulVec (fun x => Gm X M φ v x c) ∈ Formalism.MainNotions.G.colSpan (X.G.P.W v) (Gp X M φ v)) ∧
        (∀ c, ((b i).map (fun y => ρ v (D.host.conj y)))ᵀ.mulVec (fun x => Gp X M φ v x c) ∈
          Formalism.MainNotions.G.colSpan (X.G.P.W v) (Gm X M φ v))

def KerLatWLt (ρ : ∀ v : X.Pl, D.host.E →+* X.G.P.Qq v) : Prop :=
  ∀ j, j < X.mm → ∀ (L0 : X.Lt j), L0 ∈ Formalism.L2.G.Pend.repOf X.Lv hfin j → ∀ La' : X.Lt (j + 1),
    (X.Pj (j + 1)).IsLatTup La'.2 →
    ∀ v : X.Pl,
      locSpan D (X.G.P.W v) (ρ v) (large₂ j L0 La') =
        (X.latAt v j L0.2).map (((M j L0 v).mulVecLin).restrictScalars (X.G.P.W v)) ∧
      locSpan D (X.G.P.W v) (ρ v) (Lg' j L0 La') =
        (X.latAt v (j + 1) La'.2).map (((M (j + 1) La' v).mulVecLin).restrictScalars (X.G.P.W v))

def SelfDualTieLt : Prop :=
  ∀ j, j < X.mm → ∀ (L0 : X.Lt j), L0 ∈ Formalism.L2.G.Pend.repOf X.Lv hfin j → ∀ La' : X.Lt (j + 1),
    (X.Pj (j + 1)).IsLatTup La'.2 →
    SelfDualP D p (large₂ j L0 La') ∧ SelfDualP D p (Lg' j L0 La')

def KerLatWFLt (fd : Formalism.L2.PairingIndexBounds.F.FData X D) (ρ : ∀ v : X.Pl, D.host.E →+* X.G.P.Qq v) : Prop :=
  KerLatWLt X fd.frM hfin D (fun j L0 _ => fd.kerN j L0) (fun j _ La' => fd.kerN (j + 1) La') ρ

def SelfDualFLt (fd : Formalism.L2.PairingIndexBounds.F.FData X D) : Prop :=
  SelfDualTieLt X hfin D (fun j L0 _ => fd.kerN j L0) (fun j _ La' => fd.kerN (j + 1) La')

end Lat

section Data

open Formalism.MainNotions Formalism.MainNotions.G Formalism.L2.G.Pend IsDedekindDomain
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {p : ℕ} [Fact p.Prime] {D : D7}

def AdmGLt (X : Sys p) (hfin : ∀ j c, (X.Lv.lev j c).FinClasses) (D : D7) (fd : Formalism.L2.PairingIndexBounds.F.FData X D) : Prop :=
  ∀ j, j < X.mm → ∀ (L0 : X.Lt j), L0 ∈ repOf X.Lv hfin j → ∀ La' : X.Lt (j + 1), (X.Pj (j + 1)).IsLatTup La'.2 →
    TaylorLogMetric.admitted D _ _ (fd.kerN j L0) (fd.kerN (j + 1) La')

def ScalGLt (X : Sys p) (hfin : ∀ j c, (X.Lv.lev j c).FinClasses) (fd : Formalism.L2.PairingIndexBounds.F.FData X D) (χ : TaylorLogMetric.IdE D → ℂ)
    (muT : ℕ → (D.host.E ⊗[D.host.F] FiniteAdeleRing (𝓞 D.host.F) D.host.F)ˣ → ℂ) (lam : TaylorLogMetric.Qbar →+* ℂ_[p]) : Prop :=
  ∀ j, j < X.mm → ∀ (L0 : X.Lt j), L0 ∈ repOf X.Lv hfin j → ∀ La' : X.Lt (j + 1), (X.Pj (j + 1)).IsLatTup La'.2 →
    Formalism.L2.KerInert.KG.scalG fd χ muT j L0 La' ∈ TaylorLogMetric.Qbar ∧
      ‖(p : ℂ_[p]) ^ Formalism.L2.KerInert.KG.expG X j L0 La' * TaylorLogMetric.lamC lam (Formalism.L2.KerInert.KG.scalG fd χ muT j L0 La')‖ ≤ 1

end Data

end Formalism.L2.KerInert.RepLt

set_option pp.fullNames true
