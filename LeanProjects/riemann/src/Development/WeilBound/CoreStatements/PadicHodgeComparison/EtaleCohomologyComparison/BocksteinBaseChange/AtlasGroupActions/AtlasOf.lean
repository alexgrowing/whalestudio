import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.BocksteinBaseChangeP
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.AtlasGroupActions.LimSurjFil
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.AtlasGroupActions.ExistsEpsPeriodTUnit
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.AdicTorsionCup.PrimOfOver
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.ZariskiEtaleLifting.PropsA

set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry
open GroundTheory.PAdicHodge

namespace CrystallineSemistableComparison

namespace GlueB'

variable {l : ℕ} [Fact l.Prime]

def βS (hC : B.Compat l) {O : Type} [CommRing O] (F : B.Fn O) (κ : O →+* OC l) (k : Bool) (j : ℕ) :
    Sys.Hom (B.HcSys F κ k j) (MSys (F.pt κ) j) (RingHom.id _) where
  f n := B.β F κ k n j
  comm n x := (hC.red F κ k n.le_succ j x).symm

variable {K : IntermediateField ℚ_[l] (PadicAlgCl l)}

theorem atlas_of {M : Model l K} (h : M.Sm) : ∃ d, Nonempty ((B.schFn M.p).Atlas d) := by
  obtain ⟨hG, hS⟩ := h
  have hP := AdicGeo.proper_p hG
  exact B.P.atlas M.p

variable (Amp : ∀ M : Model l K, E.LineData M.X → Prop)

def bβ (hC : B.Compat l) {M : Model l K} (a : (dat Amp).Ch M) (j : ℕ) :
    ((dat Amp).H a).N j →ₗ[(per l K).A] ((dat Amp).A a).N j :=
  (βS hC (B.schFn M.p) (okToOC l K) false j).lim

def bβ' (hC : B.Compat l) {M : Model l K} (a : (dat Amp).Ch M) (j : ℕ) :
    ((dat Amp).H' a).N j →ₗ[(per l K).A] ((dat Amp).A a).N j :=
  (βS hC (B.schFn M.p) (okToOC l K) true j).lim

theorem f_inj (hMain : B.Main l) (hC : B.Compat l) {M : Model l K} (a : (dat Amp).Ch M) (hM : M.Sm) (j : ℕ) :
    ∃ n : ℕ, ∀ x, bβ Amp hC a j x = 0 → (per l K).t ^ n • x = 0 := by
  obtain ⟨d, ⟨A⟩⟩ := atlas_of hM
  obtain ⟨ε, u, -, ht⟩ := GlueBE.exists_eps_period_t_unit l K
  obtain ⟨N, hN⟩ := hMain d j
  exact ⟨2 * N, fun x hx => GlueBL.lim_inj (βS hC (B.schFn M.p) (okToOC l K) false j) ε.μ u (per l K).t N ht
    (fun n => (hN (B.schFn M.p) (okToOC l K) ε A n).1 false) x hx⟩

theorem f_inj' (hMain : B.Main l) (hC : B.Compat l) {M : Model l K} (a : (dat Amp).Ch M) (hM : M.Sm) (j : ℕ) :
    ∃ n : ℕ, ∀ x, bβ' Amp hC a j x = 0 → (per l K).t ^ n • x = 0 := by
  obtain ⟨d, ⟨A⟩⟩ := atlas_of hM
  obtain ⟨ε, u, -, ht⟩ := GlueBE.exists_eps_period_t_unit l K
  obtain ⟨N, hN⟩ := hMain d j
  exact ⟨2 * N, fun x hx => GlueBL.lim_inj (βS hC (B.schFn M.p) (okToOC l K) true j) ε.μ u (per l K).t N ht
    (fun n => (hN (B.schFn M.p) (okToOC l K) ε A n).1 true) x hx⟩

theorem f_surj' (hMain : B.Main l) (hC : B.Compat l) {M : Model l K} (a : (dat Amp).Ch M) (hM : M.Sm) (j : ℕ) :
    ∃ n : ℕ, ∀ y, ∃ x, bβ' Amp hC a j x = (per l K).t ^ n • y := by
  obtain ⟨d, ⟨A⟩⟩ := atlas_of hM
  obtain ⟨ε, u, -, ht⟩ := GlueBE.exists_eps_period_t_unit l K
  obtain ⟨N, hN⟩ := hMain d j
  exact ⟨2 * N, fun y => GlueBL.lim_surj (βS hC (B.schFn M.p) (okToOC l K) true j) ε.μ u (per l K).t N ht
    (fun n => (hN (B.schFn M.p) (okToOC l K) ε A n).1 true) y⟩

theorem f_surj (hMain : B.Main l) (hC : B.Compat l) {M : Model l K} (a : (dat Amp).Ch M) (hM : M.Sm) (j : ℕ) :
    ∃ n : ℕ, ∀ y, ∃ x, (dat Amp).fil a j n x ∧ bβ Amp hC a j x = (per l K).t ^ n • y := by
  obtain ⟨d, ⟨A⟩⟩ := atlas_of hM
  obtain ⟨ε, u, -, ht⟩ := GlueBE.exists_eps_period_t_unit l K
  obtain ⟨N, hN⟩ := hMain d j
  refine ⟨2 * N, fun y => ?_⟩
  obtain ⟨x, hx, hxy⟩ := GlueBL.lim_surj_fil (βS hC (B.schFn M.p) (okToOC l K) false j) ε.μ u (per l K).t N ht
    (fun n r => B.HcFil (B.schFn M.p) (okToOC l K) false n r j)
    (fun n r x hx => hC.smul_fil (B.schFn M.p) (okToOC l K) false n r j ε.μ (ε.μ_mem false (PAlg.base l) n) x hx)
    (fun n x hx => ((hN (B.schFn M.p) (okToOC l K) ε A n).1 false).1 x hx)
    (fun n y => (hN (B.schFn M.p) (okToOC l K) ε A n).2 y) y
  exact ⟨x, hx, hxy⟩

end GlueB'

end CrystallineSemistableComparison
