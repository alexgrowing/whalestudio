import Formalism.LocalToGlobal.InertKernelTheory.DelPolOfTies

noncomputable section

open Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Finset

namespace Formalism.L2.KerInert.SecondKernelHermitian

open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Ker Formalism.L2.KerInert.K2 Formalism.L2.KerInert.SecondKernelInstances Formalism.L2.KerInert.SecondKernelDifference Formalism.L2.KerInert.SecondKernelSeries
  Formalism.L2.KerInert.QuadraticBaseChangeGL3

section Chain

variable {p : ℕ} [Fact p.Prime] (X : Sys p) (Kc : Type) [Field Kc] [Algebra X.G.Kf Kc] (j : ℕ)

def trSub (A : X.ZA j → X.ZA j → Kc) : Formalism.L2.G.Pend.DA X Kc j →ₐ[XspC (X.Pj (j + 1)) Kc] Formalism.L2.G.Pend.DA X Kc j :=
  MvPolynomial.aeval (Formalism.L2.G.Pend.linT (fun x y => algebraMap Kc (XspC (X.Pj (j + 1)) Kc) (A x y)))

def BlockDiag (A : X.ZA j → X.ZA j → Kc) : Prop :=
  ∀ x y, A x y ≠ 0 → (⟨y.1, y.2.1⟩ : Σ v : X.Pl, Fin (X.G.P.n' v)) = ⟨x.1, x.2.1⟩

end Chain

def ChainLin : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (X : Sys p) (Kc : Type) [Field Kc] [Algebra X.G.Kf Kc] (j : ℕ) (A : X.ZA j → X.ZA j → Kc),
    BlockDiag X Kc j A → ∀ (P : Formalism.L2.G.Pend.DA X Kc j) (f : MvPowerSeries (X.ZA j) Kc),
      Formalism.L2.G.Pend.pairD X Kc j P (linSub A f) = Formalism.L2.G.Pend.pairD X Kc j (trSub X Kc j A P) f

def RenameLin : Prop :=
  ∀ (κ ι R : Type) [Fintype κ] [Fintype ι] [CommRing R] (e : κ → ι), Function.Bijective e →
    ∀ (B : ι → ι → R) (g : MvPowerSeries ι R), resV e (linSub B g) = linSub (fun x y => B (e x) (e y)) (resV e g)

section Frames

variable {p : ℕ} [Fact p.Prime] {X : Sys p} {D : D7}

def FrInv (fd : Formalism.L2.PairingIndexBounds.F.FData X D) : Prop :=
  ∀ j (La : X.Lt j) (v : X.Pl), IsUnit (fd.frM j La v).det

open Classical in

def frGL (fd : Formalism.L2.PairingIndexBounds.F.FData X D) (j : ℕ) (La : X.Lt j) (v : X.Pl) : GL (Fin ((X.Pj j).m + 1)) (X.G.P.Qq v) :=
  if h : IsUnit (fd.frM j La v).det then Matrix.nonsingInvUnit _ h else 1

def BOf (fd : Formalism.L2.PairingIndexBounds.F.FData X D) (j : ℕ) (La : X.Lt j) : ∀ v : X.Pl, GL (Fin ((X.Pj j).m + 1)) (X.G.P.Qq v) :=
  fun v => (frGL fd j La v)⁻¹

variable (X) in

def glInv : (j : ℕ) → (∀ v : X.Pl, GL (Fin ((X.Fl.Pj j).m + 1)) (X.G.P.Qq v)) →
    ∀ v : Fin (X.Fl.Pj j).nV, GL (Fin ((X.Fl.Pj j).m + 1)) ((X.Fl.Pj j).Qq v)
  | 0, B => B
  | _ + 1, B => B

open Classical in

def VOf (Kc : Type) [Field Kc] [Algebra (K0 p) Kc] [Algebra X.G.Kf Kc] (fd : Formalism.L2.PairingIndexBounds.F.FData X D) (c : Kc) (j : ℕ)
    (La' : X.Lt (j + 1)) (x y : X.ZA j) : Kc :=
  if (⟨y.1, y.2.1⟩ : Σ v : X.Pl, Fin (X.G.P.n' v)) = ⟨x.1, x.2.1⟩ ∧ y.2.2.1 = x.2.2.1 then
    c * (if IsOddPos x.2.1 then
      (((fd.frM (j + 1) La' x.1)⁻¹).map (Formalism.L2.G.Pend.tw X Kc x.1 x.2.1))
        (Fin.cast (Formalism.L2.G.Pend.rank_eq X (j + 1)).symm y.2.2.2) (Fin.cast (Formalism.L2.G.Pend.rank_eq X (j + 1)).symm x.2.2.2)
    else
      ((fd.frM (j + 1) La' x.1).map (Formalism.L2.G.Pend.tw X Kc x.1 x.2.1))
        (Fin.cast (Formalism.L2.G.Pend.rank_eq X (j + 1)).symm x.2.2.2) (Fin.cast (Formalism.L2.G.Pend.rank_eq X (j + 1)).symm y.2.2.2))
  else 0

end Frames

def SubBSplit : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (X : Sys p) (D : D7) (E : Formalism.L2.G.Pend.CEmb X.G)
    (pos : (Σ v : X.Pl, Fin (X.G.P.n' v)) ≃ D.what₂.Tau) (fd : Formalism.L2.PairingIndexBounds.F.FData X D) (c : ℂ_[p]), FrInv fd →
    ∀ (j : ℕ) (La : X.Lt j) (La' : X.Lt (j + 1)) (x y : X.ZA j),
      letI := Formalism.L2.G.Pend.wittFractionAlgebraCp p
      letI := Formalism.L2.G.Pend.algKfC E
      c * Formalism.L2.PairingIndexBounds.F.subBG E pos fd j La La' (Formalism.L2.G.Pend.kapOf X pos j x) (Formalism.L2.G.Pend.kapOf X pos j y) =
        ∑ z, VOf ℂ_[p] fd c j La' x z * Formalism.L2.G.Pend.LkB X ℂ_[p] j (BOf fd j La) z y

section Ties

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : G.Inst D L} {Gl : G.LatInst D} {Kc0 : G.Consts} {Dx : DivX D}
  {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc0 Dx cX}

def MoveH {p : ℕ} [Fact p.Prime] {X : Sys p} (Y : Pend X) (u : D.what₂.Word) (μ : D.what₂.Tup) {σ : D.what₂.LL →+* X.G.Kf}
    (cmp : ∀ j, ((ex.tw.fm u μ).lat j).V →ₛₗ[σ] X.Fm j)
    (A : ∀ j, X.Lt j → ∀ v : Fin (X.Pj j).nV, GL (Fin ((X.Pj j).m + 1)) ((X.Pj j).Qq v))
    (Gm : ∀ j, X.Lt j → ((ex.tw.fm u μ).lat j).V → (X.Pj j).Xsp) (j : ℕ) : Prop :=
  ∀ La ∈ Y.Rep j, ∀ x : ((ex.tw.fm u μ).lat j).V,
    (X.Pj j).natAct (A j La) (Gm j La x) = cmp j x La.1 La.2 ∧ Formalism.L2.G.Pend.GoodG X Y.Kc j (Gm j La x) ∧
      Formalism.L2.G.Pend.OddDeg X j (Gm j La x)

def TieOpH {p : ℕ} [Fact p.Prime] {X : Sys p} {Y : Pend X} (t : KerEntTied ex) (u : D.what₂.Word) (μ : D.what₂.Tup)
    (cls : ∀ j, X.Lv.comp j → (X.Pj j).Tup → (D.chTw u μ).cls j)
    (Gm : ∀ j, X.Lt j → ((ex.tw.fm u μ).lat j).V → (X.Pj j).Xsp) {ι : ℂ →+* Y.Kc} (j : ℕ)
    (e : GL3Theta.Idx D (D.R.N j) (D.R.N (j + 1)) → X.ZA j)
    (Φ₀ : MvPolynomial (GL3Theta.FrV D (D.R.N (j + 1))) ℂ →ₛₗ[ι] XspC (X.Pj (j + 1)) Y.Kc) : Prop :=
  ∀ La ∈ Y.Rep j, ∀ (x : ((ex.tw.fm u μ).lat j).V) Q, SharpQ t ex.tw u μ j x Q →
    Formalism.L2.G.Pend.polDel X Y.Kc j (Gm j La x) =
      trDY X Y.Kc j D e Φ₀ (polDY D (t.O u μ).dgen (Q (cls j La.1 La.2)) (N' := D.R.N (j + 1)))

def TieSerH {p : ℕ} [Fact p.Prime] {X : Sys p} (Y : Pend X) (t : KerEntTied ex) (u : D.what₂.Word) (μ : D.what₂.Tup)
    (cls : ∀ j, X.Lv.comp j → (X.Pj j).Tup → (D.chTw u μ).cls j)
    (κ : ∀ j, X.Lv.comp (j + 1) → (X.Pj (j + 1)).Tup → (D.chTw u μ).cls (j + 1)) (ι : ℂ →+* Y.Kc)
    (gS : ∀ j, X.Lt j → X.Lt (j + 1) → MvPowerSeries (X.ZA j) Y.Kc) (sH : ∀ j, X.Lt j → X.Lt (j + 1) → Y.Kc) (j : ℕ)
    (e : GL3Theta.Idx D (D.R.N j) (D.R.N (j + 1)) → X.ZA j) : Prop :=
  ∀ La ∈ Y.Rep j, ∀ (c' : X.Lv.comp (j + 1)) (L' : (X.Pj (j + 1)).Tup), (X.Pj (j + 1)).IsLatTup L' →
    ∀ α : GL3Theta.Idx D (D.R.N j) (D.R.N (j + 1)) →₀ ℕ, Formalism.L2.G.Pend.GoodDeg X j (α.mapDomain e) →
      MvPowerSeries.coeff (α.mapDomain e) (gS j La (c', L')) =
        sH j La (c', L') * ι (TaylorLogMetric.taylor D ((t.rd u μ).Th t.seam t.amb j (cls j La.1 La.2) (κ j c' L')) α)

def TieChiH {p : ℕ} [Fact p.Prime] {X : Sys p} (Y : Pend X) (t : KerEntTied ex) (u : D.what₂.Word) (μ : D.what₂.Tup)
    (cls : ∀ j, X.Lv.comp j → (X.Pj j).Tup → (D.chTw u μ).cls j)
    (κ : ∀ j, X.Lv.comp (j + 1) → (X.Pj (j + 1)).Tup → (D.chTw u μ).cls (j + 1)) (ι : ℂ →+* Y.Kc)
    (sc : ∀ j, X.Lv.comp (j + 1) → (X.Pj (j + 1)).Tup → Y.Kc) (sH : ∀ j, X.Lt j → X.Lt (j + 1) → Y.Kc)
    (cB : ∀ j, X.Lt j → Y.Kc) (j : ℕ) (cK : Y.Kc) : Prop :=
  ∀ La ∈ Y.Rep j, ∀ (c' : X.Lv.comp (j + 1)) (L' : (X.Pj (j + 1)).Tup), (X.Pj (j + 1)).IsLatTup L' →
    cK * algebraMap X.G.Kf Y.Kc (Y.eS j La * (Y.eT j (c', L'))⁻¹) * cB j La * sH j La (c', L') =
      sc j c' L' * ι (((GL3Theta.rhoOf D (t.O u μ).mt j ((t.O u μ).dt j (cls j La.1 La.2)) : ℂˣ) : ℂ) *
        ((GL3Theta.rhoOf' D (t.O u μ).mt j ((t.O u μ).dt (j + 1) (κ j c' L')) : ℂˣ) : ℂ))

end Ties

def DelYEqH {p : ℕ} [Fact p.Prime] {X : Sys p} (Y : Pend X) (V : ∀ j, X.Lt (j + 1) → X.ZA j → X.ZA j → Y.Kc)
    (τ : ∀ j, X.Lv.comp (j + 1) → (X.Pj (j + 1)).Tup → XspC (X.Pj (j + 1)) Y.Kc →ₗ[Y.Kc] XspC (X.Pj (j + 1)) Y.Kc) (j : ℕ) :
    Prop :=
  ∀ (c' : X.Lv.comp (j + 1)) (L' : (X.Pj (j + 1)).Tup), (X.Pj (j + 1)).IsLatTup L' →
    ∀ G : (X.Pj j).Xsp, Formalism.L2.G.Pend.GoodG X Y.Kc j G → Formalism.L2.G.Pend.OddDeg X j G → ∀ n : X.ZA j →₀ ℕ,
      MvPolynomial.coeff n (trSub X Y.Kc j (V j (c', L')) (Formalism.L2.G.Pend.polDel X Y.Kc j G)) =
        τ j c' L' (MvPolynomial.coeff n (Formalism.L2.G.Pend.polDel X Y.Kc j G))

def phiH {p : ℕ} [Fact p.Prime] {X : Sys p} {Kc : Type} [Field Kc] [Algebra X.G.Kf Kc] (D : D7) {ι : ℂ →+* Kc}
    (Φ₀ : ∀ j, MvPolynomial (GL3Theta.FrV D (D.R.N (j + 1))) ℂ →ₛₗ[ι] XspC (X.Pj (j + 1)) Kc)
    (τ : ∀ j, X.Lv.comp (j + 1) → (X.Pj (j + 1)).Tup → XspC (X.Pj (j + 1)) Kc →ₗ[Kc] XspC (X.Pj (j + 1)) Kc)
    (sc : ∀ j, X.Lv.comp (j + 1) → (X.Pj (j + 1)).Tup → Kc) :
    ∀ j, X.Lv.comp (j + 1) → (X.Pj (j + 1)).Tup → MvPolynomial (GL3Theta.FrV D (D.R.N (j + 1))) ℂ → XspC (X.Pj (j + 1)) Kc :=
  fun j c' L' P => sc j c' L' • τ j c' L' (Φ₀ j P)

def serG {p : ℕ} [Fact p.Prime] {X : Sys p} {D : D7} (fd : Formalism.L2.PairingIndexBounds.F.FData X D)
    {cc : Ideal (NumberField.RingOfIntegers D.host.K)} {δ : ℂ} (B : Base D cc δ) (χ : TaylorLogMetric.IdE D → ℂ) (lam : TaylorLogMetric.Qbar →+* ℂ_[p])
    (SS : Finset (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers D.host.E))) (cl : ℕ)
    (Ξ₀ : ∀ j, X.Lt j → X.Lt (j + 1) → Formalism.L2.Col.HomE D.host.E ((X.Pj j).m + 1) ((X.Pj (j + 1)).m + 1) → ℂ)
    (muT : ℕ → (TensorProduct D.host.F D.host.E
      (IsDedekindDomain.FiniteAdeleRing (NumberField.RingOfIntegers D.host.F) D.host.F))ˣ → ℂ)
    (j : ℕ) (La : X.Lt j) (La' : X.Lt (j + 1)) :
    MvPowerSeries (D.what₂.Tau × Fin ((X.Pj (j + 1)).m + 1) × Fin ((X.Pj j).m + 1)) ℂ_[p] :=
  ((p : ℂ_[p]) ^ (∑ v : X.Pl, X.vm v (j + 1) * (Formalism.L2.G.Pend.len X v (j + 1) La'.2 - Formalism.L2.G.Pend.len X v j La.2))) •
  Formalism.L2.PairingIndexBounds.F.serP lam fun z =>
    (muT (j + 1) (fd.dt (j + 1) La') * (muT (j + 1) (fd.dt j La))⁻¹ *
      (Base.chiFac χ _ _ (fd.kerN j La) (fd.kerN (j + 1) La'))⁻¹ *
      χ (TaylorLogMetric.detId D (StandardLatticesGL3.stdL D _) (fd.kerN j La)) ^ (-(((j * (X.t + 1) / 2 : ℕ) : ℤ))) *
      χ (TaylorLogMetric.detId D (StandardLatticesGL3.stdL D _) (fd.kerN (j + 1) La')) ^ ((((j + 1) * (X.t + 1) / 2 : ℕ) : ℤ))) *
    Formalism.L2.PairingIndexBounds.F.kerTh B χ SS cl (fd.kerN j La) (fd.kerN (j + 1) La')
      (Formalism.L2.PairingIndexBounds.F.movD (Ξ₀ j La La') (fd.trG j La) (fd.trG (j + 1) La')) z

def DelPolH : Prop :=
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
    letI := Formalism.L2.G.Pend.wittFractionAlgebraCp p
    letI := Formalism.L2.G.Pend.algKfC E.toCEmb
    FrInv fd →
    Formalism.L2.G.Pend.StabGeo X ℂ_[p] hfin (Formalism.L2.G.Pend.thFOf X pos
      (Formalism.L2.PairingIndexBounds.F.FrecG E.toCEmb pos fd B χ lamK SS cl Ξ₀ muT (Formalism.L2.PairingIndexBounds.F.ltC g hLT))) →
    Formalism.L2.G.Pend.KapStab X ℂ_[p] →
    let Y := pendG X E hfin hst hLT D pos fd B χ lamK SS cl Ξ₀ muT
    ∀ (σ : D.what₂.LL →+* X.G.Kf) (cls : ∀ j, X.Lv.comp j → (X.Pj j).Tup → (D.chTw u μ).cls j)
      (cmp : ∀ j, ((ex.tw.fm u μ).lat j).V →ₛₗ[σ] X.Fm j)
      (κ : ∀ j, X.Lv.comp (j + 1) → (X.Pj (j + 1)).Tup → (D.chTw u μ).cls (j + 1)) (ι : ℂ →+* Y.Kc)
      (Φ₀ : ∀ j, MvPolynomial (GL3Theta.FrV D (D.R.N (j + 1))) ℂ →ₛₗ[ι] XspC (X.Pj (j + 1)) Y.Kc)
      (τ : ∀ j, X.Lv.comp (j + 1) → (X.Pj (j + 1)).Tup → XspC (X.Pj (j + 1)) Y.Kc →ₗ[Y.Kc] XspC (X.Pj (j + 1)) Y.Kc)
      (sc : ∀ j, X.Lv.comp (j + 1) → (X.Pj (j + 1)).Tup → Y.Kc) (sH : ∀ j, X.Lt j → X.Lt (j + 1) → Y.Kc)
      (Gm : ∀ j, X.Lt j → ((ex.tw.fm u μ).lat j).V → (X.Pj j).Xsp) (j : ℕ) (cK : Y.Kc) (hN : RankTie X D j),
      MoveH Y u μ cmp (fun j La => glInv X j (BOf fd j La)) Gm j →
      TieOpH (Y := Y) t u μ cls Gm j (eIdx X D pos j hN) (Φ₀ j) →
      KernelEntryDegreeCondition (Y := Y) t u μ cls j (eIdx X D pos j hN) →
      TieSerH Y t u μ cls κ ι
        (fun j La La' => resV (Formalism.L2.G.Pend.kapOf X pos j) (serG fd B χ lamK SS cl Ξ₀ muT j La La')) sH j
        (eIdx X D pos j hN) →
      TieChiH Y t u μ cls κ ι sc sH (fun j La => Formalism.L2.G.Pend.cA X Y.Kc j (BOf fd j La)) j cK →
      DelYEqH Y (fun j La' => VOf Y.Kc fd (Formalism.L2.PairingIndexBounds.F.ltC g hLT) j La') τ j →
        DelPolAt (Y := Y) t u μ cls cmp κ (phiH D Φ₀ τ sc) (srOf Y) j cK

end Formalism.L2.KerInert.SecondKernelHermitian
