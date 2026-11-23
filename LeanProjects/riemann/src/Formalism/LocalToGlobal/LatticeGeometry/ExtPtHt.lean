import Formalism.LocalToGlobal.LatticeGeometry.CompNe

noncomputable section

open Formalism.BasicNotions

namespace Formalism.L2.Geo

variable {D : D7} {G : DV.Geo D.what₂.LL} {Lev : Type}
  {jC : ∀ (p : ℕ) [Fact p.Prime], PlL D p → (DV.KW p →+* ℂ)} {ng : NgPkg} {w : Dat D Lev}

structure ExtPtHt (U : ShimU D G jC ng w) where

  Pt : U.Comp → Type

  ht : ∀ c, G.Adl (U.alg.Yv c) → Pt c → ℝ

  dense : ∀ c, Set (Pt c) → Prop

  ampleG : ∀ c, G.Adl (U.alg.Yv c) → Prop

def extPtHtJunk (U : ShimU D G jC ng w) : ExtPtHt U where
  Pt := fun _ => Empty
  ht := fun _ _ _ => 0
  dense := fun _ _ => True
  ampleG := fun _ _ => False

def ZhangMinimaProp (U : ShimU D G jC ng w) (E : ExtPtHt U) : Prop :=
  ∀ (Lb : U.alg.ALB) (c : U.Comp), U.alg.semipos Lb → U.alg.nefFib Lb → E.ampleG c (Lb c) →
    (∀ e : ℝ, (∀ y, e ≤ E.ht c (Lb c) y) →
      ((G.dim (U.alg.Yv c) : ℝ) + 1) * e * U.alg.degA c (Lb c) ≤ G.arTop (U.alg.Yv c) (Lb c)) ∧
    (∀ (e' : ℝ) (S : Set (E.Pt c)), E.dense c S → (∀ y ∈ S, E.ht c (Lb c) y ≤ e') →
      G.arTop (U.alg.Yv c) (Lb c) ≤ ((G.dim (U.alg.Yv c) : ℝ) + 1) * e' * U.alg.degA c (Lb c))

end Formalism.L2.Geo
