import Formalism.LocalToGlobal.PairingIndexBounds.RowActionCoefficients.XFacts

open MvPolynomial

noncomputable section

namespace Formalism.L2.PairingIndexBounds.Ent

open Formalism.GradedWeylDivisibility Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.L2.G.Model.TS

attribute [local instance] Formalism.MainNotions.G.GAtP.ringO Formalism.MainNotions.G.GAtP.domO Formalism.MainNotions.G.GAtP.dvrO Formalism.MainNotions.G.GAtP.fieldK
  Formalism.MainNotions.G.GAtP.algOK

section Defs

variable {p : ℕ} [Fact p.Prime] (X : Sys p)

def DgX (K' : Type) [Field K'] (j : ℕ) (i0 : X.Pl → ℕ) (v : X.Pl) : Matrix (Fin (NJ X (j + 1))) (Fin (NJ X (j + 1))) K' :=
  Matrix.diagonal fun a => if a.val < i0 v then (p : K')⁻¹ else 1

variable (Kc : Type) [Field Kc] [Algebra X.G.Kf Kc]

def numericalIdentityScalar (j : ℕ) (g : ∀ v : X.Pl, Matrix (Fin ((X.Pj j).m + 1)) (Fin ((X.Pj j).m + 1)) (X.G.P.Qq v))
    (g' : ∀ v : X.Pl, Matrix (Fin ((X.Pj (j + 1)).m + 1)) (Fin ((X.Pj (j + 1)).m + 1)) (X.G.P.Qq v)) (i0 : X.Pl → ℕ) : Kc :=
  ∏ b : BX X, if IsOddPos b.2 then
      (algebraMap X.G.Kf Kc (mF X j b (g b.1)).det) ^ (-(cX X j b : ℤ)) *
        (algebraMap X.G.Kf Kc (mF X (j + 1) b (g' b.1) * DgX X X.G.Kf j i0 b.1).det) ^ (cX X j b)
    else (algebraMap X.G.Kf Kc (mF X j b (g b.1)).det) ^ (eX X j b) *
      (p : Kc) ^ (-((∑ k : Fin (cX X j b), min (X.colHt b.1 (j + 1) b.2 k.val) (i0 b.1) : ℕ) : ℤ))

end Defs

def PairingSeriesLinearForm : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (X : Sys p) (Kc : Type) [Field Kc] [Algebra X.G.Kf Kc] [Infinite Kc] (j : ℕ)
    (P : DA X Kc j) (f : MvPowerSeries (X.ZA j) Kc) (l : XspC (X.Pj (j + 1)) Kc →ₗ[Kc] Kc) (R : MvPolynomial (X.ZA j) Kc),
    (∀ d0 : X.ZA j → Kc, eval d0 R = l (evD X Kc j d0 P)) →
      l (pairD X Kc j P f) = ∑ n ∈ R.support, derAt X Kc j n f * coeff n R

def XMid : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (X : Sys p) (Kc : Type) [Field Kc] [Algebra (K0 p) Kc] [Algebra X.G.Kf Kc] [CharZero Kc] (j : ℕ)
    (La : X.Lt j) (La' : X.Lt (j + 1)) (φ : Frm X j La La') (i0 : X.Pl → ℕ)
    (I : ∀ (b : BX X) (k : Fin (cX X j b)), Fin (szT X j b k) → Fin (NJ X (j + 1))), (∀ b k, Function.Injective (I b k)) →
    ∃ (Ist : X.ColCh j) (ε : Kc), (ε = 1 ∨ ε = -1) ∧
      ∀ (f : MvPowerSeries (X.ZA j) Kc) (x : X.FrI j → X.G.Kf),
        fockR (delF X Kc j (∏ b, rename (emX X j b) (rowAct X.G.Kf (mF X j b ((φ.g b.1)⁻¹ : GL _ _))
            (evX (fun s => x (xmX X j b s)) (HgX X X.G.Kf j b)))) (linSub (bc Kc φ) f))
          (map (algebraMap X.G.Kf Kc) (∏ b, rename (emX X (j + 1) b)
            (rowAct X.G.Kf (mF X (j + 1) b (φ.g' b.1) * DgX X X.G.Kf j i0 b.1).transpose
              (bideterminant X.G.Kf (szT X j b) (szT_le X j b) (I b))))) =
        ε * numericalIdentityScalar X Kc j (fun v => φ.g v) (fun v => φ.g' v) i0 * (∏ b, cN Kc (nuT X j b)) *
          eval (fun t => algebraMap X.G.Kf Kc (x t)) (applyD (X.PI j Ist i0) f)

def XSpanN : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (X : Sys p) (Kc : Type) [Field Kc] [Algebra X.G.Kf Kc] [CharZero Kc] (j : ℕ)
    (x : ∀ b : BX X, Fin (NJ X j) → ℕ → X.G.Kf) (f : MvPowerSeries (X.ZA j) Kc),
    delF X Kc j (∏ b, rename (emX X j b) (srcN X j b (x b))) f ∈
      Submodule.span Kc {z | ∃ F : BX X → MvPolynomial (Fin (NJ X (j + 1)) × Fin (NJ X (j + 1))) X.G.Kf,
        (∀ b, F b ∈ dualWeyl X.G.Kf (NJ X (j + 1)) (NJ X (j + 1)) (nuT X j b)) ∧
          z = map (algebraMap X.G.Kf Kc) (∏ b, rename (emX X (j + 1) b) (F b))}

def XUnit : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (X : Sys p) (Kc : Type) [Field Kc] [Algebra X.G.Kf Kc] (Oc : Subring Kc),
    (∀ o : X.G.O, algebraMap X.G.Kf Kc (algebraMap X.G.O X.G.Kf o) ∈ Oc) → (p : Kc) ≠ 0 →
    ∀ (j : ℕ) (L : (X.Pj j).Tup) (L'' : (X.Pj (j + 1)).Tup)
      (g : ∀ v : X.Pl, GL (Fin ((X.Pj j).m + 1)) (X.G.P.Qq v)) (g' : ∀ v : X.Pl, GL (Fin ((X.Pj (j + 1)).m + 1)) (X.G.P.Qq v)),
      (∀ v, X.latAt v j L = colSpan (X.G.P.W v) (g v : Matrix _ _ (X.G.P.Qq v))) →
      (∀ v, X.latAt v (j + 1) L'' = colSpan (X.G.P.W v) (g' v : Matrix _ _ (X.G.P.Qq v))) →
      ∀ i0 : X.Pl → ℕ, (∀ v, i0 v ≤ X.G.P.r) →
        algebraMap X.G.Kf Kc ((∏ v : X.Pl, (p : X.G.Kf) ^ (Nprime (X.G.P.lam0 v) (X.w v) (j + 1) (i0 v))) *
            ((∏ v : X.Pl, (p : X.G.Kf) ^ (X.vm v (j + 1) * len X v j L)) *
              (∏ v : X.Pl, (p : X.G.Kf) ^ (X.vm v (j + 1) * len X v (j + 1) L''))⁻¹) *
            sX X j (fun v => g v) *
            (∏ b : BX X, (mF X (j + 1) b (g' b.1) * DgX X X.G.Kf j i0 b.1).det ^ (-(eJ X (j + 1) b.1 b.2)))⁻¹) *
          numericalIdentityScalar X Kc j (fun v => g v) (fun v => g' v) i0 ∈ Oc

def XEdge : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (X : Sys p) (j : ℕ) (L' L'' : (X.Pj (j + 1)).Tup) (i0 : X.Pl → ℕ),
    (X.Pj (j + 1)).IsLatTup L' →
    (∀ v' : Fin (X.Pj (j + 1)).nV, (i0 (X.vB (j + 1) v') = 0 ∧ L'' v' = L' v') ∨
      (1 ≤ i0 (X.vB (j + 1) v') ∧ IsEdge p ((X.Pj (j + 1)).n' v') (i0 (X.vB (j + 1) v')) ⟨L'' v', L' v'⟩)) →
    ∃ g' h' : ∀ v : X.Pl, GL (Fin ((X.Pj (j + 1)).m + 1)) (X.G.P.Qq v),
      (∀ v, X.latAt v (j + 1) L'' = colSpan (X.G.P.W v) (g' v : Matrix _ _ (X.G.P.Qq v))) ∧
      (∀ v, X.latAt v (j + 1) L' = colSpan (X.G.P.W v) (h' v : Matrix _ _ (X.G.P.Qq v))) ∧
      ∀ b : BX X, mF X (j + 1) b (h' b.1) = mF X (j + 1) b (g' b.1) * DgX X X.G.Kf j i0 b.1

end Formalism.L2.PairingIndexBounds.Ent
