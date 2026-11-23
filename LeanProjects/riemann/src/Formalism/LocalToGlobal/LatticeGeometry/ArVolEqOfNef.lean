import Formalism.LocalToGlobal.LatticeGeometry.DegFlLApply

noncomputable section

open Formalism.BasicNotions

namespace Formalism.L2.Geo

variable {D : D7}

structure AlgPkg (G : DV.Geo D.what₂.LL) (Tau : Type) [Fintype Tau] (N : ℕ) (Comp : Type) [Fintype Comp] where

  Yv : Comp → G.Var

  Ybd : ∀ c, G.Cl (Yv c)

  bd : ∀ c, G.Dv (Yv c)
  bd_supp : ∀ c, G.supp (Yv c) (bd c) = Ybd c

  Lw : ∀ c, (Tau → Fin N → ℤ) →+ G.Dv (Yv c)

  dim_eq : ∀ c, G.dim (Yv c) = Formalism.DegreeFormula.dimFl Tau N

  degA : ∀ c, G.Adl (Yv c) → ℝ

  degA_ofW : ∀ c (Δ : G.Dv (Yv c)) (W : HLat D.what₂.LL) (ι : W.V →ₗ[D.what₂.LL] G.Fn (Yv c)),
    degA c (G.ofW (Yv c) Δ W ι) = (G.inter (Yv c) (fun _ => Δ) : ℝ)

  degA_twist : ∀ c Lb ci cf, degA c (G.twist (Yv c) Lb ci cf) = degA c Lb

  semipos : (∀ c, G.Adl (Yv c)) → Prop
  nefFib : (∀ c, G.Adl (Yv c)) → Prop

  Mbar : ℝ → (Tau → Fin N → ℝ) → ℚ → ∀ c, G.Adl (Yv c)

namespace AlgPkg

variable {G : DV.Geo D.what₂.LL} {Tau : Type} [Fintype Tau] {N : ℕ} {Comp : Type} [Fintype Comp]
  (A : AlgPkg G Tau N Comp)

def ALB : Type := ∀ c, G.Adl (A.Yv c)

def arSelfC (L : A.ALB) (c : Comp) : ℝ := G.arTop (A.Yv c) (L c)

def geoC (L : A.ALB) (c : Comp) : ℝ := A.degA c (L c)

def arVol (L : A.ALB) : ℝ := ∑ c, G.arVol (A.Yv c) (L c)

def arNef (L : A.ALB) : Prop := ∀ c, G.nefA (A.Yv c) (L c)

theorem arVol_eq_of_nef (h : ∀ (Y : G.Var) (Lb : G.Adl Y), G.nefA Y Lb → G.arVol Y Lb = G.arTop Y Lb)
    (L : A.ALB) (hL : A.arNef L) : A.arVol L = ∑ c, A.arSelfC L c :=
  Finset.sum_congr rfl fun c _ => h _ _ (hL c)

end AlgPkg

end Formalism.L2.Geo
