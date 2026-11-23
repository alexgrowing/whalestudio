import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsEnlargedHeckeSetStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LevelCharacterOfLocalLanglandsStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EigenCompatibleOfBadSet
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AtMemAnd
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CenLocOfCenReal
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.CoreEq
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NoFormsOff
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsRhoPtOfSplitting
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsComp
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.DepthZeroWild
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.DepthZeroSupport
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalGlobalAboveL
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG
namespace GlobalTheory.GalLoc.EigLoc

set_option maxHeartbeats 4000000 in

theorem parIn_loc {hL : GlobalTheory.Published.LocalLanglandsGL} {D' : D7} {cf' : CharFrame D'} {C' : NChoice D'}
    {tp' : TupTied D' cf' C'} (nt : NTrue hL D' cf' C' tp') (rep' : D'.what₂.FT → NG.FinTyp D'.host.E D'.R.r)
    (hrep : HEq nt.rep rep') :
    ∃ Rw : RowSide D', HEq Rw.locR nt.A.row.locR ∧ Nonempty (ParIn hL D' cf' rep' Rw) := by
  obtain ⟨⟨D, cf, jE, A, cg, au, rep, row, low, Pq, S, hk, eig, θ, Bs, M, C, tp, ch, mt, big, L, Sp, Au, ss, eq⟩, pack⟩ := nt
  subst eq
  obtain ⟨-, h2⟩ := Sigma.mk.inj_iff.mp pack
  obtain ⟨hcf, -⟩ := Sigma.mk.inj_iff.mp (eq_of_heq h2)
  subst hcf
  have hr : rep = rep' := eq_of_heq hrep
  subst hr
  let T : GlobalTheory.RowTie.WDTie (withLoc L).nd (withLoc L).naut := { A.wdT with }
  let Rw : RowSide (withLoc L) := { A.row with }
  refine ⟨Rw, HEq.rfl, ⟨{ T := T, lab := A.lab, chr := { A.chr with }, cg := { cg with }, A := { A.au with }, au := au, row := row }⟩⟩

set_option maxHeartbeats 4000000 in

theorem transport {hL : GlobalTheory.Published.LocalLanglandsGL} {D' : D7} {cf' : CharFrame D'} {C' : NChoice D'}
    {tp' : TupTied D' cf' C'} (nt : NTrue hL D' cf' C' tp') (Sb : Finset (PlE D'.host)) (hS0 : ∀ i, Sb ⊆ D'.ntw.S0 i)
    (e : ℕ → D'.what₂.FT → ℕ → PlE D'.host → ↥D'.LL0) (he : HEq nt.eig e)
    (S' : RatDat D'.ntw) (hS : HEq (ratL nt.L nt.S) S')
    (hL' : ∀ j, ℕ → PlE D'.host → Module.End D'.what₂.LL (S'.WL j)) (hh : HEq nt.hL hL')
    (θ' : ∀ kk : Fin 2, Multiplicative (ZMod (D'.host.g kk)) →* (↥D'.LL0)ˣ) (hθ : HEq nt.θ θ')
    (Rw0 : RowSide D') (hR0 : HEq Rw0.locR nt.A.row.locR)
    (hT : GlobalTheory.TwInputs.EigTrue D' cf' Rw0 Sb e) (hO : GlobalTheory.TwInputs.EigOcc D' S' θ' hL' Sb e) :
    ∃ Sb : Finset (PlE nt.D.host), (∀ i, Sb ⊆ (withLoc nt.L).ntw.S0 i) ∧
      (∀ Rw : RowSide (withLoc nt.L), HEq Rw.locR nt.A.row.locR →
        GlobalTheory.TwInputs.EigTrue (withLoc nt.L) (cfL nt.L nt.cf) Rw Sb nt.eig) ∧
      GlobalTheory.TwInputs.EigOcc (withLoc nt.L) ({ nt.S with } : RatDat (withLoc nt.L).ntw) nt.θ nt.hL Sb nt.eig := by
  obtain ⟨⟨D, cf, jE, A, cg, au, rep, row, low, Pq, S, hk, eig, θ, Bs, M, C, tp, ch, mt, big, L, Sp, Au, ss, eq⟩, pack⟩ := nt
  subst eq
  obtain ⟨-, h2⟩ := Sigma.mk.inj_iff.mp pack
  obtain ⟨hcf, -⟩ := Sigma.mk.inj_iff.mp (eq_of_heq h2)
  subst hcf
  have e1 : ratL L S = S' := eq_of_heq hS
  subst e1
  have e2 : hk = hL' := eq_of_heq hh
  subst e2
  have e3 : θ = θ' := eq_of_heq hθ
  subst e3
  have e4 : eig = e := eq_of_heq he
  subst e4
  refine ⟨Sb, hS0, fun Rw hRw => ?_, hO⟩
  have e5 : Rw.locR = Rw0.locR := (eq_of_heq hRw).trans (eq_of_heq hR0).symm
  unfold GlobalTheory.TwInputs.EigTrue at hT ⊢
  rw [e5]
  exact hT

end GlobalTheory.GalLoc.EigLoc

namespace GlobalTheory.GalLoc.EigLoc

set_option maxHeartbeats 4000000 in

theorem eig_at : PrN → SerN → ∀ hL : GlobalTheory.Published.LocalLanglandsGL, AtMem hL fun _ _ _ _ w Z _ _ t nch n c =>
    ∃ Sb : Finset (PlE c.a.nt.D.host), (∀ i, Sb ⊆ (withLoc c.a.nt.L).ntw.S0 i) ∧ (∀ Rw : RowSide (withLoc c.a.nt.L), HEq Rw.locR c.a.nt.A.row.locR → GlobalTheory.TwInputs.EigTrue (withLoc c.a.nt.L) (cfL c.a.nt.L c.a.nt.cf) Rw Sb c.a.nt.eig) ∧ GlobalTheory.TwInputs.EigOcc (withLoc c.a.nt.L) ({ c.a.nt.S with } : RatDat (withLoc c.a.nt.L).ntw) c.a.nt.θ c.a.nt.hL Sb c.a.nt.eig := by
  intro hN hS hL
  have h2 : PrN → SerN → ∀ hL : GlobalTheory.Published.LocalLanglandsGL, AtMem hL fun _ _ _ _ w Z _ _ t _ _ c =>
    ∀ Sb : Finset (PlE (w.D Z).host), (∀ i, Sb ⊆ (w.D Z).ntw.S0 i) → ∃ Sb' : Finset (PlE (w.D Z).host), Sb ⊆ Sb' ∧
      (∀ i, Sb' ⊆ (w.D Z).ntw.S0 i) ∧ GlobalTheory.TwInputs.Eig.Low (w.D Z) Sb' ∧
      GlobalTheory.HeightCounting.RatSide.HeckeRd t.r.z.R t.r.z.cG c.row.kKs c.row.hk Sb' c.row.hecke.hL := GlobalTheory.T.exists_enlarged_hecke_set
  have h3 : PrN → SerN → ∀ hL : GlobalTheory.Published.LocalLanglandsGL, AtMem hL fun _ _ _ _ w Z _ _ t _ _ c =>
    ∃ θ : ∀ kk : Fin 2, Multiplicative (ZMod ((w.D Z).host.g kk)) →* (↥(w.D Z).LL0)ˣ, HEq θ c.a.nt.θ ∧
      GlobalTheory.HeightCounting.RatSide.LvlPsi t.r.z.R t.r.z.F t.r.z.cG θ := GlobalTheory.T.level_character_of_local_langlands
  refine GlobalTheory.GalLoc.atMem_imp (GlobalTheory.GalLoc.atMem_and (h2 hN hS hL) (h3 hN hS hL)) ?_
  intro K B f T w Z Wt p0 t nch n xd c hE H
  obtain ⟨H2, H3⟩ := H
  obtain ⟨e⟩ := hE
  have e' : NMore (D := (w.st Z).toD7) c.row t.r.z.geo xd := e
  obtain ⟨Sb, eg, hSb, heq, hAd⟩ := e'.eig
  obtain ⟨Sb', hsub, hS0, hlow, hrd⟩ := H2 Sb hSb
  obtain ⟨θ, hθ, hψ⟩ := H3
  obtain ⟨Rw0, hRw0, ⟨hpar⟩⟩ := parIn_loc c.a.nt _ c.row.rep_eq
  have hT := GlobalTheory.TwInputs.Eig.eigTrue hL t.r.Y t.r.z.pins.char.base.lev hpar.T Rw0 hpar.row hAd hsub hlow
  have hO := GlobalTheory.TwInputs.Eig.eigOcc t.r.Y t.r.z.pins.char.base.lev t.r.intersectionNumber_baseChange.prim.unif t.r.z.pins.char.base.models.HW
    t.r.z.good.2 hψ hAd hsub hlow hrd
  rw [t.r.z.lev.C] at hT
  exact transport c.a.nt Sb' hS0 eg heq _ c.row.S_eq _ c.row.hL_eq θ hθ.symm Rw0 hRw0 hT hO

end GlobalTheory.GalLoc.EigLoc
