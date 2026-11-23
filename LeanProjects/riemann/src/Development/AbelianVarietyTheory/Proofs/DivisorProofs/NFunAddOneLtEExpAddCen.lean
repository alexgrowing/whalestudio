import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.TwistedPlaceChoiceLiesOverPair
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WeightExceedsCenterBound
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsAuxiliaryOfIsAuxiliaryCharacter
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PlacesOkOfModEqOne
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HeckeCharacterIdeleCharacterMatchUnique

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions NumberField IsDedekindDomain Formalism.FrobeniusOrbits
open Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx
open GlobalTheory.ChiGrid Formalism.L2.Host

namespace GlobalTheory.BigTop.Fun

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {T : Type} {Lc : LevCh D T} {sc : Consts}

theorem natCast_mem_of_under {w : HeightOneSpectrum (𝓞 D.host.E)} {p : ℕ}
    (h : ((p : ℕ) : 𝓞 D.host.F) ∈ (w.under (𝓞 D.host.F)).asIdeal) : ((p : ℕ) : 𝓞 D.host.E) ∈ w.asIdeal := by
  have h1 : algebraMap (𝓞 D.host.F) (𝓞 D.host.E) (p : 𝓞 D.host.F) ∈ w.asIdeal := h
  rwa [map_natCast] at h1

theorem natCast_mem_under {w : HeightOneSpectrum (𝓞 D.host.E)} {p : ℕ}
    (h : ((p : ℕ) : 𝓞 D.host.E) ∈ w.asIdeal) : ((p : ℕ) : 𝓞 D.host.F) ∈ (w.under (𝓞 D.host.F)).asIdeal := by
  show algebraMap (𝓞 D.host.F) (𝓞 D.host.E) (p : 𝓞 D.host.F) ∈ w.asIdeal
  rwa [map_natCast]

theorem nFun_add_one_lt_eExp_add_cen (C : ℝ) (j a : Fin D.R.m) (g : D.R.Psi) :
    (BlochKatoReduction.Gen.NFun D.R : ℚ) + 1 < eExp D j g + (cen D C (D.eTau.symm g) (a.1 + 1) : ℚ) := by
  have h1 := GlobalTheory.LamTie.e_add_v_two_pos (D.hc (D.eTau.symm g)) (sLen D) (gap D C) 0 j
  have h2 := Int.lt_floor_add_one
    ((GlobalTheory.SignedHC.GridData.ofHCParam (D.hc (D.eTau.symm g)) (sLen D) (gap D C) 0).mid (a.1 + 1))
  have h3 := (GlobalTheory.SignedHC.GridData.ofHCParam (D.hc (D.eTau.symm g)) (sLen D) (gap D C) 0).mid_eq (i := a.1 + 1) (by omega)
  have h4 : (GlobalTheory.SignedHC.GridData.ofHCParam (D.hc (D.eTau.symm g)) (sLen D) (gap D C) 0).a (a.1 + 1) =
      ((GlobalTheory.SignedHC.GridData.ofHCParam (D.hc (D.eTau.symm g)) (sLen D) (gap D C) 0).v 2 : ℚ) + 1 / 2 +
        ((D.R.m : ℚ) + 1 - ((a.1 + 1 : ℕ) : ℚ)) * (gap D C : ℚ) := rfl
  have h5 : ((GlobalTheory.SignedHC.GridData.ofHCParam (D.hc (D.eTau.symm g)) (sLen D) (gap D C) 0).ga : ℚ) = gap D C := rfl
  have h6 := (isLeast_gap D C).1.2.1
  have h7 : bigN D ≤ bigN D ^ 3 := Nat.le_self_pow (by norm_num) _
  have h8 : ((bigN D + 2 : ℕ) : ℚ) ≤ gap D C := by exact_mod_cast (by omega)
  have h9 : ((a.1 + 1 : ℕ) : ℚ) ≤ D.R.m := by exact_mod_cast a.2
  have h10 : (0 : ℚ) ≤ gap D C := by positivity
  have h11 : (gap D C : ℚ) ≤ ((D.R.m : ℚ) + 1 - ((a.1 + 1 : ℕ) : ℚ)) * (gap D C : ℚ) := by nlinarith
  have h12 : BlochKatoReduction.Gen.NFun D.R = bigN D := GlobalTheory.LamTie.nFun_eq_bigN D
  rw [h12]
  unfold eExp cen
  push_cast at h8
  linarith

theorem lamOf_ok (G : GridData Lc sc) (hP : GlobalTheory.LamTie.PlacesOk D.host (q0 D) (G.pl.w G.pl.v0)) : (lamOf G).Ok := by
  have hw0 : (G.pl.w G.pl.v0).under (𝓞 D.host.F) = G.pl.v0 := G.pl.under_w (G.pl.mem_S0_of_sum_eq.2 (Or.inl rfl))
  have hS1 : ∀ w : HeightOneSpectrum (𝓞 D.host.E), GlobalTheory.LamTie.Over4 D.host w → w.under (𝓞 D.host.F) ∈ S1 D := by
    intro w h
    rw [S1_mem_OmF]
    rcases h with ⟨k, hk⟩ | hk | hk
    · fin_cases k
      · exact Or.inl (natCast_mem_under hk)
      · exact Or.inr (Or.inl (natCast_mem_under hk))
    · exact Or.inr (Or.inr (Or.inl (natCast_mem_under hk)))
    · exact Or.inr (Or.inr (Or.inr (natCast_mem_under hk)))
  have hOv : ∀ w : HeightOneSpectrum (𝓞 D.host.E), w.under (𝓞 D.host.F) ∈ S1 D → GlobalTheory.LamTie.Over4 D.host w := by
    intro w h
    rcases (S1_mem_OmF D).1 h with h | h | h | h
    · exact Or.inl ⟨0, natCast_mem_of_under h⟩
    · exact Or.inl ⟨1, natCast_mem_of_under h⟩
    · exact Or.inr (Or.inl (natCast_mem_of_under h))
    · exact Or.inr (Or.inr (natCast_mem_of_under h))
  refine ⟨hP, fun a => ?_, fun j a g => nFun_add_one_lt_eExp_add_cen sc.cGap j a g⟩
  have a1 : 1 ≤ a.1 + 1 := by omega
  have a2 : a.1 + 1 ≤ D.R.m := a.2
  refine ⟨GlobalTheory.ChrEqUnique.isUnitary_of_chrEq D _ _ (G.ch.chi_eq _ a1 a2), G.ch.triv _ a1 a2, lamOf_hasInfQ G a,
    fun w h4 h0 => ?_, fun w h4 => ?_, fun w he => ?_⟩
  · refine G.ch.unr _ a1 a2 w fun hw => ?_
    rcases G.pl.mem_S0_of_sum_eq.1 hw with h | h
    · exact h0 (h.trans hw0.symm)
    · exact h4 (hOv w h)
  · obtain ⟨l2, l1⟩ := G.ch.lev1 _ a1 a2 w (hS1 w h4)
    exact GlobalTheory.LamTie.GridCharacters.expAt_succ (n := 1) l2 l1
  · have e : w.under (𝓞 D.host.F) = G.pl.v0 := (show w.under (𝓞 D.host.F) = (G.pl.w G.pl.v0).under (𝓞 D.host.F) from he).trans hw0
    obtain ⟨l1, l0⟩ := G.ch.lev0 _ a1 a2 w e
    exact GlobalTheory.LamTie.GridCharacters.expAt_succ (n := 0) l1 fun h => l0 (((G.ch.chiH _).unrAt_iff w).2 h)

end GlobalTheory.BigTop.Fun

end
