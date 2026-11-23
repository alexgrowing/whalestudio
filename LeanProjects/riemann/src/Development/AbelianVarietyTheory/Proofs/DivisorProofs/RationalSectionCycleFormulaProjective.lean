import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EqOfIsometricTrivShift
import Development.AbelianVarietyTheory.Definitions.Divisors.IsTorsionFreeOfForallExists
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolEqMultiDiff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEffectiveCartierDivisorAddEffectiveStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntersectionNumberGlobalSectionEqSumCycleStatement
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsLinearMapMultilinearMapBaseChange
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsFiniteLengthOfIsArtinianRingAnnihilator
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverIffIsProperAndExistsIsAmpleLB
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsClosedImmersionGenericPoint
import Development.AbelianVarietyTheory.Definitions.Divisors.LineBundleGlobalSectionsDimCongrPicardClass
open CategoryTheory AlgebraicGeometry TopologicalSpace ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.FibreProj

namespace GlobalTheory.RatSecCycle

open GlobalTheory.Cartier.CartierDiv

theorem exists_sec_divOfSec_eq {X : Scheme.{0}} [IsIntegral X] (E : CartierDiv X) (hE : E.Eff) :
    ∃ (s : (toLB E).Sec) (hs : genericPoint X ∈ ReciprocityTheory.ChartRestriction.G.Out.nonzeroLocus s),
      divOfSec (isLB_toLB E) s hs = E := by
  have h := presents_toLB E
  obtain ⟨s, hs1⟩ := h.exists_rat_eq (f := 1) (mem_sections.2 hE)
  have hs : genericPoint X ∈ ReciprocityTheory.ChartRestriction.G.Out.nonzeroLocus s :=
    (h.generatesAt_rat_iff s).1 (hs1 ▸ E.generatesAt_genericPoint one_ne_zero)
  refine ⟨s, hs, Presents.unique (presents_divOfRatSec (isLB_toLB E) _) ⟨isLB_toLB E,
    isRatSec_ratOfSec s hs, fun i x hx => ?_⟩⟩
  have e : ratOfSec s hs i = i.1.2 := Units.ext (by
    rw [val_ratOfSec (gen_mem hx), ← h.rat_mul s i (gen_mem hx), hs1, one_mul])
  rw [e]
  exact h.isEqn i x hx

end GlobalTheory.RatSecCycle

open GlobalTheory.Cartier.CartierDiv in

theorem GlobalTheory.ratSec_cycle_formula : ∀ (κ : Type) [Field κ] (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] [Algebra κ Γ(X, ⊤)], IsProjOver (strHom κ X) → ∀ (n : ℕ), topologicalKrullDim X ≤ (n + 1 : ℕ) → ∀ (M : LB X) (hM : M.IsLB) (P : Fin n → LB X), (∀ i, (P i).IsLB) → ∀ (r : M.ι → X.functionFieldˣ) (hr : IsRatSec M r), interNum κ (structureModule X) (Fin.cons M P : Fin (n + 1) → LB X) = ∑ᶠ w, (divOfRatSec hM hr).mult w * interNumRed κ (⟨closure {w}, isClosed_closure⟩ : Closeds _) P := by
  intro κ _ X _ _ _ hp n hn M hM P hP r hr
  have : AlgebraicGeometry.IsNoetherian X := isNoetherian_of_isProjOver hp
  set D := divOfRatSec hM hr with hD
  obtain ⟨H, hH⟩ := exists_isAmpleLB_of_isProjOver hp
  obtain ⟨E, hE, hDE⟩ := GlobalTheory.T.exists_effective_cartierDivisor_add_effective X H hH D
  have key : ∀ E' : CartierDiv X, E'.Eff →
      interNum κ (structureModule X) (Fin.cons (toLB E') P : Fin (n + 1) → LB X) =
        ∑ᶠ w, E'.mult w * interNumRed κ (⟨closure {w}, isClosed_closure⟩ : Closeds _) P := by
    intro E' hE'
    obtain ⟨s, hs, e⟩ := GlobalTheory.RatSecCycle.exists_sec_divOfSec_eq E' hE'
    have := GlobalTheory.T.intersectionNumber_globalSection_eq_sum_cycle κ X hp n hn (toLB E') (isLB_toLB E') P hP s hs
    rw [e] at this
    exact this
  have hv := diffVanish_chiPic_of_isProjOver (algebraMap_eq_strHom κ X) (structureModule X) hp
    (d := n + 1) (by rw [QCoh.suppDim_structureModule]; exact hn)
  have hc : CechPic.cls (toLB (D + E)) (isLB_toLB (D + E)) =
      CechPic.cls M hM + CechPic.cls (toLB E) (isLB_toLB E) := by
    rw [← toPic_apply, ← toPic_apply, map_add, (presents_divOfRatSec hM hr).toPic_eq]
  have ha := hv.interNum_cons_of_cls_eq_add le_rfl hP (isLB_toLB (D + E)) hM (isLB_toLB E) hc
  rw [key _ hDE, key _ hE] at ha
  have hfin : ∀ F : CartierDiv X, Function.HasFiniteSupport
      (fun w => F.mult w * interNumRed κ (⟨closure {w}, isClosed_closure⟩ : Closeds _) P) :=
    fun F => (F.finite_support_mult).subset (Function.support_mul_subset_left _ _)
  have e2 : (∑ᶠ w, (D + E).mult w * interNumRed κ (⟨closure {w}, isClosed_closure⟩ : Closeds _) P) =
      (∑ᶠ w, D.mult w * interNumRed κ (⟨closure {w}, isClosed_closure⟩ : Closeds _) P) +
        ∑ᶠ w, E.mult w * interNumRed κ (⟨closure {w}, isClosed_closure⟩ : Closeds _) P := by
    simp only [mult_add, add_mul]
    exact finsum_add_distrib (hfin D) (hfin E)
  rw [e2] at ha
  linarith
