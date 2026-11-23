import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsChartMember
import ReciprocityTheory.AnalyticForms.RegularLocalRings.FinalTheorems
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsIsSharpAndPrim
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.RelAmpleFormBundlePowerOfPosDef
import Development.AbelianVarietyTheory.Definitions.Divisors.IsNoetherianRingCompletedStalkSiegelFibrePower
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ConnectedSpaceSpecOfIsLocalRing
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianSchemeLawsUnconditional

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.Poinc

theorem exists_sharpOver_field : ∀ (g n : ℕ) (o : Type) [CommRing o] (ζ : o) (F : SFam g n ζ) (W : Matrix (Fin 8) (Fin 8) ℤ), IsE8 W → ∀ (K : Type) [Field K] (u : Sp K ⟶ F.X), ∃ P : PolAV (Sp K), SharpOver F W P u := by
  intro g n o _ ζ F W hW K _ u
  obtain ⟨L₁, -⟩ := abelianSchemeLaws_all
  have hG := L₁.globalFns
  let c := GlobalTheory.LowChart.siegPull F.univ u (u ≫ F.s) rfl
  have hpb : SiegPB c F.univ u := GlobalTheory.LowChart.siegPB_siegPull F.univ u _ rfl
  have hc : c.Principal := GlobalTheory.LowChart.principal_siegPull F.univ u _ rfl F.princ
  obtain ⟨d, hd⟩ := GlobalTheory.AbelianDim.exists_relDim K c.A c.ab
  obtain ⟨G, _, pr, hA, hdim, hpr, hu⟩ := GlobalTheory.EighthPower.exists_power c.A c.ab hd 8
  have hb := GlobalTheory.EighthPower.isSymBilin hG c hc.1
  have hL : (GlobalTheory.MatrixBundle.matLB c.P pr W).IsLB := LB.isLB_linComb c.isLB _ _
  refine ⟨{ A := G, isAb := hA, g := 8 * d, smoothDim := hdim, L := GlobalTheory.MatrixBundle.matLB c.P pr W, isLB := hL
            rigid := GlobalTheory.MatrixBundle.rigidified_matLB c.isLB hb hpr, sym := GlobalTheory.MatrixBundle.sym_matLB c.isLB hb hpr
            ample := _root_.GlobalTheory.PosDefAmple.relAmple_linComb_of_posDef hG _ _ 8 _ _ _ _ c G pr W hpr hu hc.1 hW.1
            ktriv := GlobalTheory.MatrixBundle.kTriv_matLB c.isLB hb hpr hu hW.2 hc.2 }, c, hpb, pr, hpr, hu, ?_⟩
  exact PolBaseChange.lbIso_refl hL

end GlobalTheory.Poinc
