import Formalism.LocalToGlobal.PairingIndexBounds.RowActionCoefficients.SzTLe

open MvPolynomial

noncomputable section

namespace Formalism.L2.PairingIndexBounds.Ent

open Formalism.GradedWeylDivisibility Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.L2.G.Model.TS

attribute [local instance] Formalism.MainNotions.G.GAtP.ringO Formalism.MainNotions.G.GAtP.domO Formalism.MainNotions.G.GAtP.dvrO Formalism.MainNotions.G.GAtP.fieldK
  Formalism.MainNotions.G.GAtP.algOK

section Defs

variable {p : ℕ} [Fact p.Prime] (X : Sys p)

def srcN (j : ℕ) (b : BX X) (x : Fin (NJ X j) → ℕ → X.G.Kf) : MvPolynomial (Fin (NJ X j) × Fin (NJ X j)) X.G.Kf :=
  if IsOddPos b.2 then hvO (fun a i => C (x a i)) (yV X.G.Kf (NJ X j)) (cX X j b) (fun k => colH (muX X j (NJ X j) b) k.val)
  else C ((Matrix.of fun a i : Fin (NJ X j) => x a i.val).det ^ (eX X j b)) *
    hvE (fun a i => C (x a i)) (yV X.G.Kf (NJ X j)) (cX X j b) (fun k => colH (nuS X j b) k.val) (fun k => colH_le _ k.val)

def tgtN (K' : Type) [CommRing K'] (j : ℕ) (b : BX X) (z : Fin (NJ X (j + 1)) → ℕ → K') :
    MvPolynomial (Fin (NJ X (j + 1)) × Fin (NJ X (j + 1))) K' :=
  if IsOddPos b.2 then
    hvO (fun a i => C (z a i)) (yV K' (NJ X (j + 1))) (cX X j b) (fun k => colH (muX X j (NJ X (j + 1)) b) k.val)
  else hvE (fun a i => C (z a i)) (yV K' (NJ X (j + 1))) (cX X j b) (fun k => colH (muX X j (NJ X (j + 1)) b) k.val)
    (fun k => colH_le _ k.val)

variable (Kc : Type) [Field Kc] [Algebra X.G.Kf Kc]

def tgtD (j : ℕ) (b : BX X) (x : Fin (NJ X j) → ℕ → X.G.Kf) : DA X Kc j :=
  if IsOddPos b.2 then
    hvO (xd X Kc j b.1 b.2 x) (yMat X Kc j b.1 b.2) (cX X j b) (fun k => colH (muX X j (NJ X (j + 1)) b) k.val)
  else hvE (xd X Kc j b.1 b.2 x) (yMat X Kc j b.1 b.2) (cX X j b) (fun k => colH (muX X j (NJ X (j + 1)) b) k.val)
    (fun k => colH_le _ k.val)

def evD (j : ℕ) (d0 : X.ZA j → Kc) : DA X Kc j →+* XspC (X.Pj (j + 1)) Kc :=
  eval₂Hom (RingHom.id _) fun z => C (d0 z)

def dM (j : ℕ) (b : BX X) (d0 : X.ZA j → Kc) : Matrix (Fin (NJ X j)) (Fin (NJ X (j + 1))) Kc :=
  fun a b' => d0 ⟨b.1, (b.2, a, b')⟩

end Defs

def XShape : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (X : Sys p) (j : ℕ) (b : BX X),
    nuM X j b = nuS X j b ∧ nuM X (j + 1) b = nuT X j b ∧
    (∀ n, Antitone (muX X j n b)) ∧ (∀ n t, muX X j n b t ≤ cX X j b) ∧
    (∀ k, colH (muX X j (NJ X j) b) k = X.colHt b.1 (j + 1) b.2 k) ∧
    (∀ k, colH (muX X j (NJ X (j + 1)) b) k = X.colHt b.1 (j + 1) b.2 k) ∧
    (∀ t, eX X j b ≤ muX X j (NJ X j) b t) ∧ (∀ t : Fin (NJ X j), t.val + 1 = NJ X j → muX X j (NJ X j) b t = eX X j b) ∧
    (¬ IsOddPos b.2 → (eX X j b : ℤ) = eJ X j b.1 b.2 + X.w b.1 (j + 1) b.2 ∧ eJ X (j + 1) b.1 b.2 = -X.w b.1 (j + 1) b.2) ∧
    (IsOddPos b.2 → (cX X j b : ℤ) = X.w b.1 (j + 1) b.2 - eJ X j b.1 b.2 ∧ eJ X (j + 1) b.1 b.2 = eJ X j b.1 b.2)

def XBrS : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (X : Sys p), Function.Injective (algebraMap X.G.O X.G.Kf) →
    ∀ (j : ℕ) (L : (X.Pj j).Tup) (g : ∀ v : X.Pl, Matrix (Fin ((X.Pj j).m + 1)) (Fin ((X.Pj j).m + 1)) (X.G.P.Qq v)),
      (∀ v, IsUnit (g v).det) → (∀ v, X.latAt v j L = colSpan (X.G.P.W v) (g v)) →
      ∀ T : Submodule X.G.O (X.Pj j).Xsp,
        (∀ F : BX X → MvPolynomial (Fin (NJ X j) × Fin (NJ X j)) X.G.Kf,
          (∀ b, F b ∈ deltaL X.G.O X.G.Kf (NJ X j) (nuM X j b) (mF X j b (g b.1))) →
            sX X j g • ∏ b, rename (emX X j b) (F b) ∈ T) → (X.Pj j).HtupW L ≤ T

def XBrT : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (X : Sys p), Function.Injective (algebraMap X.G.O X.G.Kf) →
    ∀ (j : ℕ) (L : (X.Pj j).Tup) (g : ∀ v : X.Pl, Matrix (Fin ((X.Pj j).m + 1)) (Fin ((X.Pj j).m + 1)) (X.G.P.Qq v)),
      (∀ v, IsUnit (g v).det) → (∀ v, X.latAt v j L = colSpan (X.G.P.W v) (g v)) →
      ∀ F : BX X → MvPolynomial (Fin (NJ X j) × Fin (NJ X j)) X.G.Kf,
        (∀ b, F b ∈ deltaL X.G.O X.G.Kf (NJ X j) (nuM X j b) (mF X j b (g b.1))) →
          sX X j g • ∏ b, rename (emX X j b) (F b) ∈ (X.Pj j).HtupW L

def XInj : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (X : Sys p) (j : ℕ),
    (Function.Injective fun x : BX X × (Fin (NJ X j) × Fin (NJ X j)) => emX X j x.1 x.2) ∧
    (Function.Injective fun x : BX X × (ℕ × Fin (NJ X j)) => xmX X j x.1 x.2)

def XA : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (X : Sys p) (Kc : Type) [Field Kc] [Algebra X.G.Kf Kc] (j : ℕ)
    (x : ∀ b : BX X, Fin (NJ X j) → ℕ → X.G.Kf),
    polDel X Kc j (∏ b, rename (emX X j b) (srcN X j b (x b))) = ∏ b, tgtD X Kc j b (x b)

def XB : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (X : Sys p) (Kc : Type) [Field Kc] [Algebra (K0 p) Kc] [Algebra X.G.Kf Kc] [Infinite Kc] (j : ℕ)
    (La : X.Lt j) (La' : X.Lt (j + 1)) (φ : Frm X j La La') (P : DA X Kc j) (f : MvPowerSeries (X.ZA j) Kc)
    (l : XspC (X.Pj (j + 1)) Kc →ₗ[Kc] Kc) (R : MvPolynomial (X.ZA j) Kc),
    (∀ d0 : X.ZA j → Kc, eval d0 R = l (evD X Kc j (fun y => ∑ z, bc Kc φ z y * d0 z) P)) →
      l (pairD X Kc j P (linSub (bc Kc φ) f)) = ∑ n ∈ R.support, derAt X Kc j n f * coeff n R

def TransposedFrameImageBlockwise : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (X : Sys p) (Kc : Type) [Field Kc] [Algebra (K0 p) Kc] [Algebra X.G.Kf Kc] (j : ℕ)
    (La : X.Lt j) (La' : X.Lt (j + 1)) (φ : Frm X j La La') (d0 : X.ZA j → Kc) (b : BX X),
    dM X Kc j b (fun y => ∑ z, bc Kc φ z y * d0 z) = (Pf Kc φ b.1 b.2).transpose * dM X Kc j b d0 * Qf Kc φ b.1 b.2

def XC : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (X : Sys p) (Kc : Type) [Field Kc] [Algebra X.G.Kf Kc] (j : ℕ) (b : BX X)
    (x : Fin (NJ X j) → ℕ → X.G.Kf) (d0 : X.ZA j → Kc),
    evD X Kc j d0 (tgtD X Kc j b x) =
      rename (emX X (j + 1) b) (tgtN X Kc j b (mulC (dM X Kc j b d0).transpose fun a i => algebraMap X.G.Kf Kc (x a i)))

def XG : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (X : Sys p) (Kc : Type) [Field Kc] [Algebra X.G.Kf Kc] (j : ℕ) (I : X.ColCh j) (i0 : X.Pl → ℕ)
    (f : MvPowerSeries (X.ZA j) Kc) (x : X.FrI j → Kc),
    ∑ n ∈ (map (eval₂Hom (Int.castRingHom Kc) x) (X.PI j I i0)).support,
        derAt X Kc j n f * coeff n (map (eval₂Hom (Int.castRingHom Kc) x) (X.PI j I i0)) =
      eval x (applyD (X.PI j I i0) f)

end Formalism.L2.PairingIndexBounds.Ent
