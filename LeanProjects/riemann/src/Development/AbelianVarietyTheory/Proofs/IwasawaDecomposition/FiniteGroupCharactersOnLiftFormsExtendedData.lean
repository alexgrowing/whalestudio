import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsBaseEnlargementFixedCoefFieldOfCoeffEnlargemen
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CoefAEqOfHeq
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Forms
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.GreenCuspidalIff
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsIsBIffCoreB
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DsExistsOfDiscreteSeriesExists
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HarishChandraFinite
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr
open scoped Matrix

noncomputable section

namespace GlobalTheory.Mem.R3.ChiExt

theorem res_unique {E : Type} [Field E] [NumberField E] {χ : Formalism.L2.Host.HChar E} {P : Pl E} {c c' : (kP P)ˣ →* ℂˣ}
    (h : ∀ (a : 𝓞 E) (k : Eˣ) (u : (kP P)ˣ), (k : E) = a → (u : kP P) = Ideal.Quotient.mk _ a → c u = χ.locK P k)
    (h' : ∀ (a : 𝓞 E) (k : Eˣ) (u : (kP P)ˣ), (k : E) = a → (u : kP P) = Ideal.Quotient.mk _ a → c' u = χ.locK P k) : c = c' := by
  ext1 u
  obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (u : kP P)
  have ha0 : (a : E) ≠ 0 := by
    intro h0
    have : a = 0 := by exact_mod_cast h0
    exact u.ne_zero (by rw [← ha, this, map_zero])
  exact (h a (Units.mk0 _ ha0) u rfl ha.symm).trans (h' a (Units.mk0 _ ha0) u rfl ha.symm).symm

theorem prod_eq {B B' : Base} (hB : B'.toPre = B.toPre) {f : Fr B.toPre} {f' : Fr B'.toPre} (hf : HEq f' f)
    {px : PreX B.toPre} {px' : PreX B'.toPre} (hpx : HEq px' px) (j : Fin B.R.m) (j' : Fin B'.R.m) (hj : (j : ℕ) = j')
    {Pg : Finset (Pl B.host.E)} {Pg' : Finset (Pl B'.host.E)} (hPg : HEq Pg' Pg)
    (eG : Gc B px ≃* G0 Pg B.R.r) (eG' : Gc B' px' ≃* G0 Pg' B'.R.r) (heG : HEq eG' eG)
    (c : ∀ PP : Pl B.host.E, (kP PP)ˣ →* ℂˣ) (c' : ∀ PP : Pl B'.host.E, (kP PP)ˣ →* ℂˣ)
    (h : ∀ PP ∈ Pg, ∀ (a : 𝓞 B.host.E) (k : B.host.Eˣ) (u : (kP PP)ˣ), (k : B.host.E) = a → (u : kP PP) = Ideal.Quotient.mk _ a →
      (c PP)⁻¹ u = (f.mu0 j).locK PP k)
    (h' : ∀ PP ∈ Pg', ∀ (a : 𝓞 B'.host.E) (k : B'.host.Eˣ) (u : (kP PP)ˣ), (k : B'.host.E) = a → (u : kP PP) = Ideal.Quotient.mk _ a →
      (c' PP)⁻¹ u = (f'.mu0 j').locK PP k)
    (g : Gc B px) (g' : Gc B' px') (hg : HEq g' g) :
    ∏ PP : Pg', ((c' PP.1 (Matrix.GeneralLinearGroup.det (eG' g' PP)) : ℂˣ) : ℂ) =
      ∏ PP : Pg, ((c PP.1 (Matrix.GeneralLinearGroup.det (eG g PP)) : ℂˣ) : ℂ) := by
  cases B with | mk P => ?_
  cases B' with | mk P' => ?_
  dsimp only at hB
  subst hB
  obtain rfl : px' = px := eq_of_heq hpx
  obtain rfl : f' = f := eq_of_heq hf
  obtain rfl : Pg' = Pg := eq_of_heq hPg
  obtain rfl : eG' = eG := eq_of_heq heG
  obtain rfl : g' = g := eq_of_heq hg
  obtain rfl : j = j' := Fin.ext hj
  refine Finset.prod_congr rfl fun PP _ => ?_
  have e : c' PP.1 = c PP.1 := inv_injective (res_unique (h' PP.1 PP.2) (h PP.1 PP.2))
  rw [e]
  rfl

set_option maxHeartbeats 2000000 in

theorem chi_ext : GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.CasselmanWallach → GlobalTheory.Published.WeilRepresentationUnitaryPair → GlobalTheory.Published.DiscreteSeriesExists → GlobalTheory.Published.HarishChandraFinite → (StepW Pinned fun K B' f' T' w' => ∀ (B : Base) (f : Fr B.toPre) (T : TwDat B) (w : ColW B f T), Enl0 B B' →
  HEq f' f → Pinned K B f T w → HEq w'.px w.px → ∀ (Z : w.Lt) (hX : B.fields.Ok) (Wt : Set B.places.Pl)
    (z : Dat (w.st Z) w.I hX T Wt), GrpTrue Z.N f → GrpAt (w.st Z) w.I → Fine z → HoldsL z.R z.F →
    ∀ (Z' : w'.Lt) (hX' : B'.fields.Ok), GrpTrue Z'.N f' → GrpAt (w'.st Z') w'.I → VolTieG (w'.D Z') →
      ∀ z' : Dat (w'.st Z') w'.I hX' T' {v | B'.places.resChar v ∈ T'.pl}, Fine z' → ExtN z z' →
        ∀ (j : Fin (w.st Z).toD7.R.m) (j' : Fin (w'.st Z').toD7.R.m), (j : ℕ) = j' →
        ∀ φ : (w.st Z).toD7.what₂.LL →+* (w'.st Z').toD7.what₂.LL, (∀ x, (w'.st Z').toD7.what₂.embLL (φ x) = (w.st Z).toD7.what₂.embLL x) →
        ∀ (g : Gc (w.st Z).B w.px) (g' : Gc (w'.st Z').B w'.px), HEq g' g → (((z'.R.toRealDat.FW j').chi g' : (w'.st Z').toD7.what₂.LLˣ) : (w'.st Z').toD7.what₂.LL) = φ (((z.R.toRealDat.FW j).chi g : (w.st Z).toD7.what₂.LLˣ) : (w.st Z).toD7.what₂.LL)) := by
  intro _ _ _ _ _ _ _
  refine StepW.of_all fun K B' f' T' w' _ _ _ B f T w hE hf _ hpx Z hX Wt z _ _ _ _ Z' hX' _ _ _ z' _ hx j j' hj φ hφ g g' hg => ?_
  apply RingHom.injective (w'.st Z').toD7.what₂.embLL
  refine (z'.pins.char.base.grp.chiW j' g').trans (Eq.trans ?_ ((hφ _).trans (z.pins.char.base.grp.chiW j g)).symm)
  have hC : z.R.toLevCh.C.mu0 j = f.mu0 j := by
    rw [z.lev.C, w.C_eq]; rfl
  have hC' : z'.R.toLevCh.C.mu0 j' = f'.mu0 j' := by
    rw [z'.lev.C, w'.C_eq]; rfl
  exact prod_eq hE.1 hf hpx j j' hj hx.Pg z.R.eG z'.R.eG hx.eG (z.R.chi ((j : ℕ) + 1)) (z'.R.chi ((j' : ℕ) + 1))
    (fun PP hP => hC ▸ z.lev.is.chi j PP hP) (fun PP hP => hC' ▸ z'.lev.is.chi j' PP hP) g g' hg

end GlobalTheory.Mem.R3.ChiExt

end
