import Formalism.HermitianCurvature.HermitianCurvatureProofs.TopFirstOfParts

open MeasureTheory Matrix

noncomputable section

namespace Formalism.FourierDecayAlt.P.PBN

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

def JAAop : Prop :=
  ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (Bs : B.RealPlaceData k r Wp Wq)
    (F : B.Mat k r → (Wq →L[ℂ] Wp)) (u : ℂ), KB.CptCoef Bs F → ∀ g ∈ JF.Om k r Bs.z Bs.z',
    B.JF Bs (C3.AAop k r r le_rfl u F) g = C3.AAop k r r le_rfl u (B.JF Bs F) g

def AACell : Prop :=
  ∀ (k r : ℕ) (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] (f : B.Mat k r → E) (u : ℂ) (c : Fin r → ℂ)
    (g : B.Mat k r), g ∈ Q.Glev k r (Fin.last r) →
    C3.AAop k r r le_rfl u f (Q.wCell k r (Fin.last r) c * g) =
      (∏ a, c a) • qminorOp (EabH (Hpk k r)) (C3.xR k r r le_rfl) (C3.xR k r r le_rfl) u f
        (Q.wCell k r (Fin.last r) c * g)

def MinorCell : Prop :=
  ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (Bs : B.RealPlaceData k r Wp Wq)
    (F : B.Mat k r → (Wq →L[ℂ] Wp)) (y : ℂ), KB.CptCoef Bs F → ∀ x ∈ Q.DomR k r Bs.z Bs.z',
    Q.resG k r (Fin.last r) (qminorOp (EabH (Hpk k r)) (C3.xR k r r le_rfl) (C3.xR k r r le_rfl)
        (y + ((2 * r + k : ℕ) : ℂ) / 2) (B.JF Bs F)) x.1 x.2 =
      Q.crd (Q.vAB r y r).1 (Q.resG k r (Fin.last r) (B.JF Bs F)) x.1 x.2

def RadSideA : Prop :=
  ∀ (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]
    (π : Q.Mx k r → (Wp →L[ℂ] Wp)) (π' : Q.Mx k r → (Wq →L[ℂ] Wq)) (X : Q.ActualOps k r z z' π π')
    (L : R.LevelData (Q.Pr (Q.RadSp k r z z' π π')) r) (y : ℂ), Q.IsActualLevel X L →
    ∀ (Ψ : Q.RadSp k r z z' π π'), ∀ x ∈ Q.DomR k r z z',
      (((L.Ar y).1 Ψ : Q.RadSp k r z z' π π') : Q.Fn k r (Wq →L[ℂ] Wp)) x.1 x.2 =
        Q.crd (Q.vAB r y r).1 (Ψ : Q.Fn k r (Wq →L[ℂ] Wp)) x.1 x.2

def AACpt : Prop :=
  ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] (Bs : B.RealPlaceData k r Wp Wq) (F : B.Mat k r → (Wq →L[ℂ] Wp)) (y : ℝ),
    KB.CptCoef Bs F → KB.CptCoef Bs (aaTop Bs y F)

def RadAATopOfParts : Prop := JAAop → AACell → MinorCell → RadSideA → AACpt → RadAATop

end Formalism.FourierDecayAlt.P.PBN
