import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FockOfApply
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExistsIsClassSystem
import Development.AutomorphicArithmetic.CyclotomicBounds.DeRhamLattices.LevSIffLevGAndLevChiEq
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.FWT IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.TwInputs GlobalTheory.ConjTwist GlobalTheory.ChoiceRead
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ)
open Formalism.L2.Host (embLL0)
open Formalism.IndefR.RecTie (Used0)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000
open GlobalTheory.PlaceRead
open GlobalTheory.HeightCounting.Up (PrN)

private theorem principal_level_membership {D : D7} {V : HSp D} {β : GL (Fin V.rank) (Lev.EAf D)} {L : LevDat D.host.E ℂ V.rank}
    (P : LevelP L.Pg L.r ℂ) {g : GA D V} (hg : g ∈ GfC V) (h : Lev.finE V g ∈ lev D.sp.cm V.gram β (Lev.flag1L L)) :
    g ∈ Lev.levG V β (Lev.withP L P) ∧ levFn β (Lev.withP L P) (Lev.finE V g) = levFn β (Lev.flag1L L) (Lev.finE V g) := by
  have h1 : rTup β L (Lev.finE V g) = 1 := Subgroup.mem_bot.1 h.2
  have h2 : rTup β L (Lev.finE V g) ∈ P.H := h1 ▸ P.H.one_mem
  refine ⟨⟨hg, h.1, h2⟩, ?_⟩
  rw [Lev.levFn_withP, Lev.levFn_flag1, extendOne_of_mem _ h2]
  have h3 : (⟨_, h2⟩ : P.H) = 1 := Subtype.ext h1
  rw [h3, map_one, one_mul]

theorem _root_.UpperTheory.KN.levEnv_level_subgroup_le_levJ_and_character_eq :
    ∀ (D : D7) (X : RealSide D) (X0 : BaseLevelRowSide D) (Y : GlobalTheory.Mem.R3.Read (A3 := X.A3) X.R.toRealDat X.F.lv2 X0) (S : NX.RatDat D.ntw) (YS : NX.NExpRealS X.R X.cG S) (Z : ExportTie YS X.geo.v₀) (c : NChoice D) (w : D.what₂.places.Pl) (j : Fin D.R.m) (H : AtPlace Y Z c w j),
      ∀ ι : KE c w →+* ℂ, (∀ x, ι (c.embW w x) = D.what₂.embLL x) →
      ∀ k : (levEnv (Vc D j) (X.R.βV j) (X.R.datVt j (Y.tupT (D.what₂.muTw w)))).J, ∃ hk : (k : Bridge.Gf (Vc D j)) ∈ (baseOf Z c w j).levJ (twVia Z.ρ ι),
      (baseOf Z c w j).levLam (twVia Z.ρ ι) ⟨k, hk⟩ = (levEnv (Vc D j) (X.R.βV j) (X.R.datVt j (Y.tupT (D.what₂.muTw w)))).χ k := by
  intro D X X0 Y S YS Z c w j H ι hι k
  obtain ⟨⟨_, g0, rfl⟩, hk⟩ := k
  obtain ⟨g, hg, e⟩ := GlobalTheory.LevelOpen.exists_finPart D (Vc D j) g0
  have e' : (⟨finHom (Vc D j) g0, g0, rfl⟩ : Bridge.Gf (Vc D j)) = finPt (Vc D j) g := Subtype.ext e.symm
  revert hk
  rw [e']
  intro hk
  obtain ⟨a1, a2⟩ := principal_level_membership (L := X.R.datVt j (Y.tupT (D.what₂.muTw w))) (X.R.toRealDat.levR X.F.lv2 false).conj hg hk
  obtain ⟨b1, b2⟩ := UpperTheory.KN.levS_iff_levG_and_levChi_eq D X X0 Y S YS Z c w j H ι hι g
  have hm := b1.1 a1
  refine ⟨((baseOf Z c w j).finPt_mem_levJ _ hg).2 hm, Units.ext ?_⟩
  rw [Base.levLam_finPt, ← b2 hm]
  exact congrArg Units.val a2
