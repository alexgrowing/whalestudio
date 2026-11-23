import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KappaOK

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.ZarhinFam

section Maps

variable {S : Scheme.{0}} (A B : Over S) [GrpObj A] [GrpObj B] [IsCommMonObj A] [IsCommMonObj B]

def zpr (mu : B ⟶ A) (k : Fin 8) : Zob A B ⟶ A :=
  Sum.elim (pa A B) (fun j => pb A B j ≫ mu) (sig k)

def zphi (mu : B ⟶ A) : Zob A B ⟶ Out.powObj A 8 :=
  (Out.powIsLimit A 8).lift (Fan.mk _ (zpr A B mu))

theorem zphi_powPr (mu : B ⟶ A) (k : Fin 8) : zphi A B mu ≫ Out.powPr A k = zpr A B mu k :=
  (Out.powIsLimit A 8).fac _ ⟨k⟩

end Maps

def zW (d : ℕ) : Matrix (Fin 8) (Fin 8) ℤ := fun k l =>
  Matrix.fromBlocks ((d : ℤ) • (1 : Matrix (Fin 4) (Fin 4) ℤ)) ((2 : ℤ) • (quat d).transpose) 0 1 (sig k) (sig l)

end GlobalTheory.ZarhinFam
