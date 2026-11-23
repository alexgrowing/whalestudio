import Mathlib
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.NormSmall
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RatInOfUnit
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NegIdxOfIsStd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BaseFits
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RamificationIdxEqOneOfIsSquare
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LevelCharactersUnramifiedOffLevelPlaces

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset
open Formalism.DivisionValues (vw)
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.CMVal (IsHeckeL)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.SqTop
open GlobalTheory.ConstRatio (NegIdx Factor)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SqStep

variable {D : D7} {T : Type} {L : LevCh D T} {sc : GlobalTheory.ChiGrid.Consts}

theorem nuH_not_unrAt_above {μ₀ : T} (hL : L.Is μ₀) (G : GridData L sc) (t : T) (i j : Fin D.R.m)
    (P : HeightOneSpectrum (𝓞 D.host.E)) (hP : P.under (𝓞 D.host.F) ∈ G.pl.S0) : ¬ (nuH G t i j).UnrAt P := by
  have hm : 1 ≤ D.R.m - (i : ℕ) ∧ D.R.m - (i : ℕ) ≤ D.R.m := ⟨by omega, by omega⟩
  have e : G.ch.chiH (D.R.m - i) = L.C.mu0 j * L.xiH t * (nuH G t i j)⁻¹ := by
    rw [← div_eq_mul_inv, nuH, div_div_cancel]
  intro hn
  rcases G.pl.mem_S0_of_sum_eq.1 hP with hv | hv
  · have hmu : (L.C.mu0 j).UnrAt P := (L.C.isMu0 j).unr _ fun k hk => G.ch.basePlace_not_mem_chiGridBadPlaces (by
      have h : ((D.host.g k : ℕ) : 𝓞 D.host.F) ∈ (P.under (𝓞 D.host.F)).asIdeal := by
        show algebraMap _ (𝓞 D.host.E) _ ∈ P.asIdeal
        rw [map_natCast]; exact hk
      rw [hv] at h
      refine (S1_mem_OmF D).2 ?_
      fin_cases k
      · exact Or.inl h
      · exact Or.inr (Or.inl h))
    have hxi : (L.xiH t).UnrAt P := by
      by_contra hc
      rcases (hL.Q_ram t _).1 hc with h | ⟨PP', h, hc'⟩
      · exact G.pl.levelPlace_ne_basePlace t _ h hv
      · exact G.pl.levelPlace_ne_basePlace t PP' h ((GlobalTheory.LevelPlaces.under_eq_of_isConjPl hc').trans hv)
    apply (G.ch.lev0 _ hm.1 hm.2 _ hv).2
    rw [e]
    exact (hmu.mul hxi).mul hn.inv
  · apply (G.ch.lev1 _ hm.1 hm.2 P hv).2
    rw [e]
    exact (Formalism.L2.Host.HChar.LevelLe.mul ((L.C.isMu0 j).tame P) (hL.xi_tame t P)).mul (hn.levelLe 1).inv

theorem heckeL_eq_of_ram {K : Type} [Field K] [NumberField K] {χ : HChar K} {S : Set (HeightOneSpectrum (𝓞 K))}
    (hr : ∀ w ∈ S, ¬ χ.UnrAt w) {Λ : ℂ → ℂ} (hΛ : IsHeckeL χ Λ) {s : ℂ} (hs : 1 < s.re) :
    GlobalTheory.LFun.heckeL S χ s = Λ s := by
  have e : ({w | w ∉ S} : Set (HeightOneSpectrum (𝓞 K))).mulIndicator (GlobalTheory.CMVal.eulerFactor χ s) =
      GlobalTheory.CMVal.eulerFactor χ s :=
    Set.mulIndicator_eq_self.2 fun w hw => by
      by_contra h
      exact hw (if_neg (hr w (not_not.1 h)))
  have h := (hasProd_subtype_iff_mulIndicator (s := {w | w ∉ S}) (f := GlobalTheory.CMVal.eulerFactor χ s)).2
    (by rw [e]; exact hΛ.2 s hs)
  unfold GlobalTheory.LFun.heckeL GlobalTheory.LFun.eulerProd
  simp only [GlobalTheory.LFun.locL_heckeFam]
  exact h.tprod_eq

theorem chs_nu (G : GridData L sc) (i j : Fin D.R.m) (t : T) : (chs G i j t).ν = G.nu t i (j + 1) :=
  mul_div_mul_right_eq_div _ _ _

theorem charL_chs_eq : GBig fun {D} T _ _ G _ _ _ _ => ∀ (i j : Fin D.R.m) (t : T) (s : ℕ) (Λ : ℂ → ℂ), 2 ≤ s → IsHeckeL (nuH G t i j) Λ →
    GlobalTheory.LFun.charL (GlobalTheory.SqStep.chs G i j t).ν (G.pl.S0 : Set (HeightOneSpectrum (𝓞 D.host.F))) (s : ℂ) = Λ s := by
  refine ⟨0, fun _ _ _ => ⟨0, 0, fun _ _ D _ _ _ _ T Lc μ₀ hL G i j t s Λ hs hΛ => ?_⟩⟩
  rw [chs_nu, GlobalTheory.LFun.charL_eq_of_chrEq (chrEq_nu G t i j hL)]
  refine heckeL_eq_of_ram (fun w hw => nuH_not_unrAt_above hL G t i j w hw) hΛ ?_
  rw [Complex.natCast_re]
  exact_mod_cast (by omega : 1 < s)

end GlobalTheory.SqStep
