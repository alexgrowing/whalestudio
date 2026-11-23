import Formalism.HermitianCurvature.HermitianCurvatureProofs.FrameTransport
import Formalism.HermitianCurvature.HermitianCurvatureProofs.ExistsCompactCutoffCoefficient
import Formalism.HermitianCurvature.HermitianCurvatureProofs.AdmissibleOfRange
import Formalism.HermitianCurvature.HermitianCurvatureProofs.ChartCoefficientHasCompactSupport
import Formalism.HermitianCurvature.HermitianCurvatureProofs.IsOpenDomP
import Formalism.DoubleCosetMeasures.Statement

noncomputable section

open Matrix MeasureTheory Filter Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt
open scoped ContDiff

namespace Formalism.FourierDecayAlt.P.CutEX

section defs

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]

def xT (k r : ℕ) (Z : Matrix (Fin r) (Fin r) ℂ) (μ : B.Mat k (r - r)) : B.Mat k r :=
  D.castM (by omega) (U.mMap k r (r - r) Z μ)

def pbTop {P : M.Par} (p : KB.Pl P Wp Wq) (G : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (Z : Matrix (Fin P.r) (Fin P.r) ℂ)
    (μ : B.Mat P.k (P.r - P.r)) : Wq →L[ℂ] Wp :=
  PBQ.pbT p P.r le_rfl G (xT P.k P.r Z μ)

def TopCls {k r : ℕ} (Bs : B.RealPlaceData k r Wp Wq) (G : B.Mat k r → (Wq →L[ℂ] Wp)) : Prop :=
  KB.CptCoef Bs G ∧ ∃ K : Set ℂ, IsCompact K ∧ (0 : ℂ) ∉ K ∧
    ∀ g ∈ B.GV k r, G g ≠ 0 → Dmin k r Bs.z Bs.z' g ⟨r, by omega⟩ ∈ K

def UT (k r : ℕ) (z z' : Fin (2 * (r - r) + k + 1) → ℂ) : Set ((Fin r → Fin r → ℂ) × Mt k (r - r)) :=
  {q | (Matrix.of q.1).det ≠ 0 ∧ 0 < Q.GGl k (r - r) z z' (Matrix.of q.2)}

def psiU {P : M.Par} (p : KB.Pl P Wp Wq) (u : Matrix (Fin P.r) (Fin P.r) ℂ) : ℂ :=
  psi P.k P.r p.T.base.z' cStd (D.castM (by omega) (U.muP P.k P.r (P.r - P.r) u))

def F2 {k r : ℕ} (b b' : U.RC k r (r - r) → ℝ) (Φ : (Fin r → Fin r → ℂ) → Mt k (r - r) → (Wq →L[ℂ] Wp)) :
    B.Mat k r → (Wq →L[ℂ] Wp) :=
  D.castF (by omega : r = r + (r - r)) (PBI.chartCoefficient b b' Φ)

end defs

def UwTop : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq)
    (F : B.Mat P.k P.r → (Wq →L[ℂ] Wp)), TopCls p.T.base F →
    ∀ (w : List C.Letter) (e : Wd.Ix (Fin w.length)),
      TopCls p.T.base (D.uwG P.k P.r p.T.base.z p.T.base.z' F P.r le_rfl w e)

def SliceTop : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq)
    (G : B.Mat P.k P.r → (Wq →L[ℂ] Wp)), TopCls p.T.base G →
    ∀ (h : C.LPt) (hh : D.IsLocPt h P.r) (γ : B.Mat P.k (P.r - P.r)), γ ∈ B.GV P.k (P.r - P.r) →
      0 < Q.GGl P.k (P.r - P.r) (p.T.bs P.r).z (p.T.bs P.r).z' γ →
      Integrable (fun v : PBQ.XH h => PBQ.ellH h v (pbTop p G (PBQ.zxH h P.r hh.2 v) γ)) ∧
      B.JF (p.T.bs P.r) (D.castF (by rw [hh.2]) (D.sliceAt P.k P.r p.T.base.z p.T.base.z' G h)) γ =
        ∫ v, PBQ.ellH h v (pbTop p G (PBQ.zxH h P.r hh.2 v) γ)

def PbSmooth : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq)
    (G : B.Mat P.k P.r → (Wq →L[ℂ] Wp)), TopCls p.T.base G →
    PBI.ParFam P.k (P.r - P.r) (UT P.k P.r (p.T.bs P.r).z (p.T.bs P.r).z')
      (fun q => pbTop p G (Matrix.of q.1) (Matrix.of q.2))

def PbRight : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq)
    (G : B.Mat P.k P.r → (Wq →L[ℂ] Wp)), TopCls p.T.base G →
    ∀ (Z u : Matrix (Fin P.r) (Fin P.r) ℂ) (μ : B.Mat P.k (P.r - P.r)), Formalism.DoubleCosetMeasures.IsUpUni u →
      pbTop p G (Z * u) μ = psiU p u • pbTop p G Z μ

def PbSupp : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq)
    (G : B.Mat P.k P.r → (Wq →L[ℂ] Wp)), TopCls p.T.base G →
    ∃ K : Set ((Fin P.r → Fin P.r → ℂ) × Mt P.k (P.r - P.r)), IsCompact K ∧
      K ⊆ UT P.k P.r (p.T.bs P.r).z (p.T.bs P.r).z' ∧
      ∀ q : (Fin P.r → Fin P.r → ℂ) × Mt P.k (P.r - P.r), (Matrix.of q.1).det ≠ 0 →
        Matrix.of q.2 ∈ Q.Glev P.k (P.r - P.r) (Fin.last _) → pbTop p G (Matrix.of q.1) (Matrix.of q.2) ≠ 0 →
        ∃ u : Matrix (Fin P.r) (Fin P.r) ℂ, Formalism.DoubleCosetMeasures.IsUpUni u ∧ (Matrix.of.symm (Matrix.of q.1 * u), q.2) ∈ K

def PbEquiv : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq)
    (G : B.Mat P.k P.r → (Wq →L[ℂ] Wp)), TopCls p.T.base G →
    ∀ (Z : Matrix (Fin P.r) (Fin P.r) ℂ), Z.det ≠ 0 →
    ∀ μ ∈ Q.Glev P.k (P.r - P.r) (Fin.last _), ∀ h ∈ UWset P.k (P.r - P.r) (p.T.bs P.r).z,
    ∀ h' ∈ UWset P.k (P.r - P.r) (p.T.bs P.r).z',
      pbTop p G Z (h * μ * h') = ((p.T.bs P.r).π h).comp ((pbTop p G Z μ).comp ((p.T.bs P.r).π' h'))

def MkTop : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq),
    ∃ (b b' : U.RC P.k P.r (P.r - P.r) → ℝ) (β : (Fin P.r → Fin P.r → ℂ) → ℝ) (κ : ℂ),
      ContDiff ℝ ∞ b ∧ HasCompactSupport b ∧ ContDiff ℝ ∞ b' ∧ HasCompactSupport b' ∧ κ ≠ 0 ∧
      ContDiffOn ℝ ∞ β {Z | (Matrix.of Z).det ≠ 0} ∧
      (∀ K : Set ((Fin P.r → Fin P.r → ℂ) × Mt P.k (P.r - P.r)), IsCompact K →
        K ⊆ UT P.k P.r (p.T.bs P.r).z (p.T.bs P.r).z' →
        ∃ K' : Set ((Fin P.r → Fin P.r → ℂ) × Mt P.k (P.r - P.r)), IsCompact K' ∧
          K' ⊆ UT P.k P.r (p.T.bs P.r).z (p.T.bs P.r).z' ∧
          ∀ q : (Fin P.r → Fin P.r → ℂ) × Mt P.k (P.r - P.r), (Matrix.of q.1).det ≠ 0 → β q.1 ≠ 0 →
            (∃ u : Matrix (Fin P.r) (Fin P.r) ℂ, Formalism.DoubleCosetMeasures.IsUpUni u ∧ (Matrix.of.symm (Matrix.of q.1 * u), q.2) ∈ K) →
            q ∈ K') ∧
      ∀ Φ : (Fin P.r → Fin P.r → ℂ) → Mt P.k (P.r - P.r) → (Wq →L[ℂ] Wp),
        (∀ Z y, Matrix.of y ∈ Q.Glev P.k (P.r - P.r) (Fin.last _) → ∀ h ∈ UWset P.k (P.r - P.r) (p.T.bs P.r).z,
          ∀ h' ∈ UWset P.k (P.r - P.r) (p.T.bs P.r).z',
            Φ Z (Matrix.of.symm (h * Matrix.of y * h')) = ((p.T.bs P.r).π h).comp ((Φ Z y).comp ((p.T.bs P.r).π' h'))) →
        (∀ Z y (u : Matrix (Fin P.r) (Fin P.r) ℂ), (Matrix.of Z).det ≠ 0 →
          Matrix.of y ∈ Q.Glev P.k (P.r - P.r) (Fin.last _) → Formalism.DoubleCosetMeasures.IsUpUni u →
            Φ (Matrix.of.symm (Matrix.of Z * u)) y = psiU p u • Φ Z y) →
        ∀ Z y, (Matrix.of Z).det ≠ 0 → Matrix.of y ∈ Q.Glev P.k (P.r - P.r) (Fin.last _) →
          pbTop p (F2 b b' (fun Z' y' => ((β Z' : ℝ) : ℂ) • Φ Z' y')) (Matrix.of Z) (Matrix.of y) = κ • Φ Z y

def MkCpt : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq)
    (b b' : U.RC P.k P.r (P.r - P.r) → ℝ), ContDiff ℝ ∞ b → HasCompactSupport b → ContDiff ℝ ∞ b' →
    HasCompactSupport b' → ∀ Φ : (Fin P.r → Fin P.r → ℂ) → Mt P.k (P.r - P.r) → (Wq →L[ℂ] Wp),
    PBI.ParFam P.k (P.r - P.r) (UT P.k P.r (p.T.bs P.r).z (p.T.bs P.r).z') (fun q => Φ q.1 q.2) →
    ∀ K : Set ((Fin P.r → Fin P.r → ℂ) × Mt P.k (P.r - P.r)), IsCompact K →
      K ⊆ UT P.k P.r (p.T.bs P.r).z (p.T.bs P.r).z' →
      (∀ q, Matrix.of q.2 ∈ Q.Glev P.k (P.r - P.r) (Fin.last _) → q ∉ K → Φ q.1 q.2 = 0) →
      TopCls p.T.base (F2 b b' Φ)

def TopPt : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq),
    (∀ x ∈ Q.DomR P.k P.r p.T.base.z p.T.base.z', ∃ g : B.Mat P.k (P.r - P.r),
      g ∈ Q.Glev P.k (P.r - P.r) (Fin.last _) ∧ 0 < Q.GGl P.k (P.r - P.r) (p.T.bs P.r).z (p.T.bs P.r).z' g ∧
      x.2 = D.castM (by omega) (ιLev P.k P.r (P.r - P.r) g)) ∧
    ∀ γ : B.Mat P.k (P.r - P.r), γ ∈ B.GV P.k (P.r - P.r) ↔ γ ∈ Q.Glev P.k (P.r - P.r) (Fin.last _)

def ZxDet : Prop :=
  ∀ (r : ℕ) (h : C.LPt) (hh : D.IsLocPt h r) (v : PBQ.XH h), (PBQ.zxH h r hh.2 v).det ≠ 0

def HeadFam : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq)
    (h : C.LPt) (hh : D.IsLocPt h P.r) (f : (Fin P.r → Fin P.r → ℂ) × Mt P.k (P.r - P.r) → (Wq →L[ℂ] Wp)),
    PBI.ParFam P.k (P.r - P.r) (UT P.k P.r (p.T.bs P.r).z (p.T.bs P.r).z') f →
    ∀ K : Set ((Fin P.r → Fin P.r → ℂ) × Mt P.k (P.r - P.r)), IsCompact K →
      K ⊆ UT P.k P.r (p.T.bs P.r).z (p.T.bs P.r).z' →
      (∀ q, Matrix.of q.2 ∈ Q.Glev P.k (P.r - P.r) (Fin.last _) → f q ≠ 0 →
        ∃ u : Matrix (Fin P.r) (Fin P.r) ℂ, Formalism.DoubleCosetMeasures.IsUpUni u ∧ (Matrix.of.symm (Matrix.of q.1 * u), q.2) ∈ K) →
      PBI.ParFam P.k (P.r - P.r)
        (Set.univ ×ˢ {y | 0 < Q.GGl P.k (P.r - P.r) (p.T.bs P.r).z (p.T.bs P.r).z' (Matrix.of y)})
        (fun q : PBQ.XH h × Mt P.k (P.r - P.r) => PBQ.ellH h q.1 (f (PBQ.zxH h P.r hh.2 q.1, q.2))) ∧
      ∃ Kp : Set (PBQ.XH h), IsCompact Kp ∧ ∀ v ∉ Kp, ∀ y : Mt P.k (P.r - P.r),
        Matrix.of y ∈ Q.Glev P.k (P.r - P.r) (Fin.last _) → f (PBQ.zxH h P.r hh.2 v, y) = 0

def RadSliceTop : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq)
    (G : B.Mat P.k P.r → (Wq →L[ℂ] Wp)), TopCls p.T.base G →
    ∀ (h : C.LPt) (hh : D.IsLocPt h P.r),
      ∃ Ψ : Q.RadSp (JC.parLev P P.r).k (JC.parLev P P.r).r (p.T.bs P.r).z (p.T.bs P.r).z' (p.T.bs P.r).π
          (p.T.bs P.r).π',
        Top.IsRadOf (JC.parLev P P.r) (p.T.bs P.r) Ψ
          (D.castF (by rw [hh.2]; rfl) (D.sliceAt P.k P.r p.T.base.z p.T.base.z' G h))

section mx

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

def RadOfFun : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] (k ρ : ℕ) (z z' : Fin (2 * ρ + k + 1) → ℂ) (π : Q.Mx k ρ → (Wp →L[ℂ] Wp))
    (π' : Q.Mx k ρ → (Wq →L[ℂ] Wq)) (f : Q.Mx k ρ → (Wq →L[ℂ] Wp)),
    (∀ g₀, g₀ ∈ Q.Glev k ρ (Fin.last ρ) → 0 < Q.GGl k ρ z z' g₀ → ∃ (U : Set (Q.Mx k ρ)) (F : Q.Mx k ρ → (Wq →L[ℂ] Wp)),
      IsOpen U ∧ g₀ ∈ U ∧ ContDiffOn ℝ ∞ F U ∧ ∀ g ∈ U, g ∈ Q.Glev k ρ (Fin.last ρ) → f g = F g) →
    (∀ g, g ∈ Q.Glev k ρ (Fin.last ρ) → 0 < Q.GGl k ρ z z' g → ∀ h ∈ UWset k ρ z, ∀ h' ∈ UWset k ρ z',
      f (h * g * h') = (π h).comp ((f g).comp (π' h'))) →
    ∃ Ψ : Q.RadSp k ρ z z' π π', ∀ x ∈ Q.DomR k ρ z z', (Ψ : Q.Fn k ρ (Wq →L[ℂ] Wp)) x.1 x.2 = f x.2

end mx

def RadExt : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] (k ρ : ℕ) (z z' : Fin (2 * ρ + k + 1) → ℂ) (π : Q.Mx k ρ → (Wp →L[ℂ] Wp))
    (π' : Q.Mx k ρ → (Wq →L[ℂ] Wq)) (Ψ Ψ' : Q.RadSp k ρ z z' π π'),
    (∀ x ∈ Q.DomR k ρ z z', (Ψ : Q.Fn k ρ (Wq →L[ℂ] Wp)) x.1 x.2 = (Ψ' : Q.Fn k ρ (Wq →L[ℂ] Wp)) x.1 x.2) → Ψ = Ψ'

def ResTop : Prop :=
  ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] (k ρ : ℕ), ρ = 0 →
    ∀ (J : Q.Mx k ρ → E) (c : Fin ρ → ℂ) (g : Q.Mx k ρ), Q.resG k ρ (Fin.last ρ) J c g = J g

def Asm : Prop :=
  UwTop → SliceTop → PbSmooth → PbRight → PbSupp → PbEquiv → MkTop → MkCpt → TopPt → ZxDet → HeadFam → RadSliceTop →
    RadOfFun → RadExt → ResTop → PBI.FrameParam → PBI.RadWordSlice → PBI.PicSlice → PBI.ExhPic

theorem exhPic_of_leaves (hA : Asm) (h1 : UwTop) (h2 : SliceTop) (h3 : PbSmooth) (h3' : PbRight) (h4 : PbSupp) (h5 : PbEquiv)
    (h6 : MkTop) (h7 : MkCpt) (h8 : TopPt) (h9 : ZxDet) (h10 : HeadFam) (h11 : RadSliceTop) (h12 : RadOfFun)
    (h13 : RadExt) (h14 : ResTop) (hFP : PBI.FrameParam) (hRW : PBI.RadWordSlice) (hPS : PBI.PicSlice) :
    PBI.ExhPic :=
  hA h1 h2 h3 h3' h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 hFP hRW hPS

end Formalism.FourierDecayAlt.P.CutEX
