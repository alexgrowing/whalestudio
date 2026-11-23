import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.HzUnit

set_option genSizeOfSpec false
set_option genInjectivity false

noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.SplitWeil GlobalTheory.LocMod ValuativeRel
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SeeSaw

variable {D : D7}

structure LocPl (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (M : GlobalTheory.FinPl.Lat S) (M' : GlobalTheory.FinPl.Lat T) where
  k : Type
  [fld : Field k]
  [val : ValuativeRel k]
  [top : TopologicalSpace k]
  [loc : IsNonarchimedeanLocalField k]
  q : GlobalTheory.FinPl.SplitPt D k
  unit : q.UnitAA
  Y : Type
  Y' : Type
  [fY : Fintype Y]
  [dY : DecidableEq Y]
  [fY' : Fintype Y']
  [dY' : DecidableEq Y']
  FS : Frame k S.rank Y'
  FT : Frame k T.rank Y
  Φ : SB (Matrix Y Y' k)
  e : WO S T →₀ ℂ
  e_is : (ofSplit q).IsCombAt ψ FS FT e Φ.1
  o : WO S T →₀ ℂ
  o_at : ∀ x ∈ o.support, IsHalf (q.e + cA D q.e) x
  o_is : ∀ Tm, (ofSplit q).IsModel ψ FS FT Tm → ∀ Φ₀ Φ₁, IsOne Φ₁ →
    Φ₀.1 = Set.indicator {x | (ofSplit q).up FS FT x ∈ latO S T (M : Set _) (M' : Set _) (· = q.v)} (fun _ => 1) →
    Tm Φ₁ = comb ψ S T o (Tm Φ₀)

attribute [instance] LocPl.fld LocPl.val LocPl.top LocPl.loc LocPl.fY LocPl.dY LocPl.fY' LocPl.dY'

open Classical in

def prodDat {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} {M : GlobalTheory.FinPl.Lat S} {M' : GlobalTheory.FinPl.Lat T} {n : ℕ}
    (L : Fin n → LocPl ψ S T M M') (x : WO S T) : ℂ :=
  if IsHalf (∑ i, (L i).q.e) x then ∏ i, (L i).Φ.1 ((ofSplit (L i).q).down (L i).FS (L i).FT x) else 0

end GlobalTheory.SeeSaw

end
