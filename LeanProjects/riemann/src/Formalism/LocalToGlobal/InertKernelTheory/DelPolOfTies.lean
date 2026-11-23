import Formalism.LocalToGlobal.InertKernelTheory.KernelDifferenceOfFrame
import Formalism.LocalToGlobal.InertKernelTheory.TieSerPin
import Formalism.LocalToGlobal.PairingIndexBounds.OrthogonalChartLevels.FdOfCharts
import Formalism.LocalToGlobal.PairingIndexBounds.OrthogonalChartLevels.LtCNeZero

noncomputable section

open Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Finset

namespace Formalism.L2.KerInert.QuadraticBaseChangeGL3

open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Ker Formalism.L2.KerInert.K2 Formalism.L2.KerInert.SecondKernelInstances Formalism.L2.KerInert.SecondKernelDifference Formalism.L2.KerInert.SecondKernelSeries

section Dict

variable {p : ℕ} [Fact p.Prime] (X : Sys p) (Kc : Type) [Field Kc] [Algebra X.G.Kf Kc] (j : ℕ)

def trDY (D : D7) {N N' : ℕ} {ι : ℂ →+* Kc} (e : GL3Theta.Idx D N N' → X.ZA j)
    (Φ₀ : MvPolynomial (GL3Theta.FrV D N') ℂ →ₛₗ[ι] XspC (X.Pj (j + 1)) Kc)
    (R : MvPolynomial (GL3Theta.Idx D N N') (MvPolynomial (GL3Theta.FrV D N') ℂ)) : Formalism.L2.G.Pend.DA X Kc j :=
  ∑ α ∈ R.support, MvPolynomial.monomial (α.mapDomain e) (Φ₀ (MvPolynomial.coeff α R))

end Dict

def pairR (D : D7) {N N' : ℕ} (R : MvPolynomial (GL3Theta.Idx D N N') (MvPolynomial (GL3Theta.FrV D N') ℂ))
    (Θ : TaylorLogMetric.VC D N N' → ℂ) : MvPolynomial (GL3Theta.FrV D N') ℂ :=
  ∑ α ∈ R.support, MvPolynomial.coeff α R * MvPolynomial.C ((α.prod fun _ n => (n.factorial : ℂ)) * TaylorLogMetric.taylor D Θ α)

def PairDict : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (X : Sys p) (Kc : Type) [Field Kc] [Algebra X.G.Kf Kc] (j : ℕ) (D : D7) (N N' : ℕ)
    (ι : ℂ →+* Kc) (e : GL3Theta.Idx D N N' → X.ZA j), Function.Injective e →
    ∀ (Φ₀ : MvPolynomial (GL3Theta.FrV D N') ℂ →ₛₗ[ι] XspC (X.Pj (j + 1)) Kc)
      (R : MvPolynomial (GL3Theta.Idx D N N') (MvPolynomial (GL3Theta.FrV D N') ℂ)) (Θ : TaylorLogMetric.VC D N N' → ℂ)
      (f : MvPowerSeries (X.ZA j) Kc) (w : Kc),
      (∀ α ∈ R.support, Formalism.L2.G.Pend.GoodDeg X j (α.mapDomain e)) →
      (∀ α ∈ R.support, MvPowerSeries.coeff (α.mapDomain e) f = w * ι (TaylorLogMetric.taylor D Θ α)) →
      Formalism.L2.G.Pend.pairD X Kc j (trDY X Kc j D e Φ₀ R) f = w • Φ₀ (pairR D R Θ)

def phiR {p : ℕ} [Fact p.Prime] {X : Sys p} {Kc : Type} [Field Kc] [Algebra X.G.Kf Kc] (D : D7) {ι : ℂ →+* Kc}
    (Φ₀ : ∀ j, MvPolynomial (GL3Theta.FrV D (D.R.N (j + 1))) ℂ →ₛₗ[ι] XspC (X.Pj (j + 1)) Kc)
    (sc : ∀ j, X.Lv.comp (j + 1) → (X.Pj (j + 1)).Tup → Kc) :
    ∀ j, X.Lv.comp (j + 1) → (X.Pj (j + 1)).Tup → MvPolynomial (GL3Theta.FrV D (D.R.N (j + 1))) ℂ → XspC (X.Pj (j + 1)) Kc :=
  fun j c' L' P => sc j c' L' • Φ₀ j P

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : G.Inst D L} {Gl : G.LatInst D} {Kc0 : G.Consts} {Dx : DivX D}
  {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc0 Dx cX}

def TieOpG {p : ℕ} [Fact p.Prime] {X : Sys p} {Y : Pend X} (t : KerEntTied ex) (u : D.what₂.Word) (μ : D.what₂.Tup)
    {σ : D.what₂.LL →+* X.G.Kf} (cls : ∀ j, X.Lv.comp j → (X.Pj j).Tup → (D.chTw u μ).cls j)
    (cmp : ∀ j, ((ex.tw.fm u μ).lat j).V →ₛₗ[σ] X.Fm j) {ι : ℂ →+* Y.Kc} (j : ℕ)
    (e : GL3Theta.Idx D (D.R.N j) (D.R.N (j + 1)) → X.ZA j)
    (Φ₀ : MvPolynomial (GL3Theta.FrV D (D.R.N (j + 1))) ℂ →ₛₗ[ι] XspC (X.Pj (j + 1)) Y.Kc) : Prop :=
  ∀ La ∈ Y.Rep j, ∀ (x : ((ex.tw.fm u μ).lat j).V) Q, SharpQ t ex.tw u μ j x Q →
    Formalism.L2.G.Pend.polDel X Y.Kc j (cmp j x La.1 La.2) =
      trDY X Y.Kc j D e Φ₀ (polDY D (t.O u μ).dgen (Q (cls j La.1 La.2)) (N' := D.R.N (j + 1)))

def KernelEntryDegreeCondition {p : ℕ} [Fact p.Prime] {X : Sys p} {Y : Pend X} (t : KerEntTied ex) (u : D.what₂.Word) (μ : D.what₂.Tup)
    (cls : ∀ j, X.Lv.comp j → (X.Pj j).Tup → (D.chTw u μ).cls j) (j : ℕ)
    (e : GL3Theta.Idx D (D.R.N j) (D.R.N (j + 1)) → X.ZA j) : Prop :=
  ∀ La ∈ Y.Rep j, ∀ (x : ((ex.tw.fm u μ).lat j).V) Q, SharpQ t ex.tw u μ j x Q →
    ∀ α ∈ (polDY D (t.O u μ).dgen (Q (cls j La.1 La.2)) (N' := D.R.N (j + 1))).support,
      Formalism.L2.G.Pend.GoodDeg X j (α.mapDomain e)

def TieSerG {p : ℕ} [Fact p.Prime] {X : Sys p} (Y : Pend X) (t : KerEntTied ex) (u : D.what₂.Word) (μ : D.what₂.Tup)
    (cls : ∀ j, X.Lv.comp j → (X.Pj j).Tup → (D.chTw u μ).cls j)
    (κ : ∀ j, X.Lv.comp (j + 1) → (X.Pj (j + 1)).Tup → (D.chTw u μ).cls (j + 1)) (ι : ℂ →+* Y.Kc)
    (sc : ∀ j, X.Lv.comp (j + 1) → (X.Pj (j + 1)).Tup → Y.Kc) (j : ℕ)
    (e : GL3Theta.Idx D (D.R.N j) (D.R.N (j + 1)) → X.ZA j) (cK : Y.Kc) : Prop :=
  ∀ La ∈ Y.Rep j, ∀ (c' : X.Lv.comp (j + 1)) (L' : (X.Pj (j + 1)).Tup), (X.Pj (j + 1)).IsLatTup L' →
    ∀ α : GL3Theta.Idx D (D.R.N j) (D.R.N (j + 1)) →₀ ℕ, Formalism.L2.G.Pend.GoodDeg X j (α.mapDomain e) →
      cK * MvPowerSeries.coeff (α.mapDomain e) (srOf Y j La (c', L')) =
        sc j c' L' * ι ((((GL3Theta.rhoOf D (t.O u μ).mt j ((t.O u μ).dt j (cls j La.1 La.2)) : ℂˣ) : ℂ) *
          ((GL3Theta.rhoOf' D (t.O u μ).mt j ((t.O u μ).dt (j + 1) (κ j c' L')) : ℂˣ) : ℂ)) *
          TaylorLogMetric.taylor D ((t.rd u μ).Th t.seam t.amb j (cls j La.1 La.2) (κ j c' L')) α)

def DelPolOfTies : Prop :=
  ∀ (D : D7) (L : SizeData₂ D) (hT : GatTies D) (Gi : G.Inst D L) (Gl : G.LatInst D) (Kc0 : G.Consts) (Dx : DivX D)
    (cX : ExtraC) (ex : Extra D L hT Gi Gl Kc0 Dx cX) (t : KerEntTied ex) (u : D.what₂.Word) (μ : D.what₂.Tup)
    (p : ℕ) [Fact p.Prime] (X : Sys p) (Y : Pend X) (σ : D.what₂.LL →+* X.G.Kf)
    (cls : ∀ j, X.Lv.comp j → (X.Pj j).Tup → (D.chTw u μ).cls j) (cmp : ∀ j, ((ex.tw.fm u μ).lat j).V →ₛₗ[σ] X.Fm j)
    (κ : ∀ j, X.Lv.comp (j + 1) → (X.Pj (j + 1)).Tup → (D.chTw u μ).cls (j + 1)) (ι : ℂ →+* Y.Kc)
    (Φ₀ : ∀ j, MvPolynomial (GL3Theta.FrV D (D.R.N (j + 1))) ℂ →ₛₗ[ι] XspC (X.Pj (j + 1)) Y.Kc)
    (sc : ∀ j, X.Lv.comp (j + 1) → (X.Pj (j + 1)).Tup → Y.Kc) (j : ℕ) (cK : Y.Kc)
    (e : GL3Theta.Idx D (D.R.N j) (D.R.N (j + 1)) → X.ZA j), Function.Injective e →
    (∀ (G : (X.Pj j).Xsp) (f : MvPowerSeries (X.ZA j) Y.Kc),
      Y.DelF j G f = Formalism.L2.G.Pend.pairD X Y.Kc j (Formalism.L2.G.Pend.polDel X Y.Kc j G) f) →
    TieOpG (Y := Y) t u μ cls cmp j e (Φ₀ j) → KernelEntryDegreeCondition (Y := Y) t u μ cls j e → TieSerG Y t u μ cls κ ι sc j e cK →
      DelPolAt (Y := Y) t u μ cls cmp κ (phiR D Φ₀ sc) (srOf Y) j cK

def RankTie {p : ℕ} [Fact p.Prime] (X : Sys p) (D : D7) (j : ℕ) : Prop :=
  D.R.N j = NN X.G.P.m X.t j ∧ D.R.N (j + 1) = NN X.G.P.m X.t (j + 1)

def eIdx {p : ℕ} [Fact p.Prime] (X : Sys p) (D : D7) (pos : (Σ v : X.Pl, Fin (X.G.P.n' v)) ≃ D.what₂.Tau) (j : ℕ)
    (hN : RankTie X D j) : GL3Theta.Idx D (D.R.N j) (D.R.N (j + 1)) → X.ZA j :=
  fun k => ⟨(pos.symm k.1).1, ((pos.symm k.1).2, Fin.cast hN.1 k.2.2, Fin.cast hN.2 k.2.1)⟩

def pendG {p : ℕ} [Fact p.Prime] (X : Sys p) [IsFractionRing X.G.O X.G.Kf] (E : Formalism.L2.G.Pend.CEmbC X.G)
    (hfin : ∀ j c, (X.Lv.lev j c).FinClasses) (hst : Formalism.L2.G.Pend.FinStab X.Lv) {g : GL3Theta.G1 p} (hLT : Formalism.L2.G.Pend.LTIso g)
    (D : D7) (pos : (Σ v : X.Pl, Fin (X.G.P.n' v)) ≃ D.what₂.Tau) (fd : Formalism.L2.PairingIndexBounds.F.FData X D)
    {cc : Ideal (NumberField.RingOfIntegers D.host.K)} {δ : ℂ} (B : Base D cc δ) (χ : TaylorLogMetric.IdE D → ℂ) (lamK : TaylorLogMetric.Qbar →+* ℂ_[p])
    (SS : Finset (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers D.host.E))) (cl : ℕ)
    (Ξ₀ : ∀ j, X.Lt j → X.Lt (j + 1) → Formalism.L2.Col.HomE D.host.E ((X.Pj j).m + 1) ((X.Pj (j + 1)).m + 1) → ℂ)
    (muT : ℕ → (TensorProduct D.host.F D.host.E (IsDedekindDomain.FiniteAdeleRing (NumberField.RingOfIntegers D.host.F) D.host.F))ˣ → ℂ) :
    Pend X :=
  Formalism.L2.G.Pend.pendT X E hfin hst hLT pos
    (Formalism.L2.PairingIndexBounds.F.FrecG E.toCEmb pos fd B χ lamK SS cl Ξ₀ muT (Formalism.L2.PairingIndexBounds.F.ltC g hLT))

def DelPolG : Prop :=
  ∀ (D : D7) (L : SizeData₂ D) (hT : GatTies D) (Gi : G.Inst D L) (Gl : G.LatInst D) (Kc0 : G.Consts) (Dx : DivX D)
    (cX : ExtraC) (ex : Extra D L hT Gi Gl Kc0 Dx cX) (t : KerEntTied ex) (u : D.what₂.Word) (μ : D.what₂.Tup)
    (p : ℕ) [Fact p.Prime] (X : Sys p) [IsFractionRing X.G.O X.G.Kf] (E : Formalism.L2.G.Pend.CEmbC X.G)
    (hfin : ∀ j c, (X.Lv.lev j c).FinClasses) (hst : Formalism.L2.G.Pend.FinStab X.Lv) (g : GL3Theta.G1 p)
    (hLT : Formalism.L2.G.Pend.LTIso g) (pos : (Σ v : X.Pl, Fin (X.G.P.n' v)) ≃ D.what₂.Tau) (fd : Formalism.L2.PairingIndexBounds.F.FData X D)
    (cc : Ideal (NumberField.RingOfIntegers D.host.K)) (δ : ℂ) (B : Base D cc δ) (χ : TaylorLogMetric.IdE D → ℂ)
    (lamK : TaylorLogMetric.Qbar →+* ℂ_[p]) (SS : Finset (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers D.host.E)))
    (cl : ℕ) (Ξ₀ : ∀ j, X.Lt j → X.Lt (j + 1) → Formalism.L2.Col.HomE D.host.E ((X.Pj j).m + 1) ((X.Pj (j + 1)).m + 1) → ℂ)
    (muT : ℕ → (TensorProduct D.host.F D.host.E
      (IsDedekindDomain.FiniteAdeleRing (NumberField.RingOfIntegers D.host.F) D.host.F))ˣ → ℂ),
    let Y := pendG X E hfin hst hLT D pos fd B χ lamK SS cl Ξ₀ muT
    ∀ (σ : D.what₂.LL →+* X.G.Kf) (cls : ∀ j, X.Lv.comp j → (X.Pj j).Tup → (D.chTw u μ).cls j)
      (cmp : ∀ j, ((ex.tw.fm u μ).lat j).V →ₛₗ[σ] X.Fm j)
      (κ : ∀ j, X.Lv.comp (j + 1) → (X.Pj (j + 1)).Tup → (D.chTw u μ).cls (j + 1)) (ι : ℂ →+* Y.Kc)
      (Φ₀ : ∀ j, MvPolynomial (GL3Theta.FrV D (D.R.N (j + 1))) ℂ →ₛₗ[ι] XspC (X.Pj (j + 1)) Y.Kc)
      (sc : ∀ j, X.Lv.comp (j + 1) → (X.Pj (j + 1)).Tup → Y.Kc) (j : ℕ) (cK : Y.Kc) (hN : RankTie X D j),
      TieOpG (Y := Y) t u μ cls cmp j (eIdx X D pos j hN) (Φ₀ j) → KernelEntryDegreeCondition (Y := Y) t u μ cls j (eIdx X D pos j hN) →
        TieSerG Y t u μ cls κ ι sc j (eIdx X D pos j hN) cK →
          DelPolAt (Y := Y) t u μ cls cmp κ (phiR D Φ₀ sc) (srOf Y) j cK

end Formalism.L2.KerInert.QuadraticBaseChangeGL3
