import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsRealFam
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsCombAt
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CuspAlongSmoothRows
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PlaceAtIff
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExOneEqSelf
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
open Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

noncomputable section

namespace GlobalTheory.VacComb

variable {D : D7}

theorem eq_zero_of_isHalf_zero {m n : ℕ} {x : Mx D m n} (hx : IsHalf (0 : AE D) x) : x = 0 := by
  ext i j
  have := hx i j
  simp at this
  simpa using this.symm

theorem isHalf_zero_zero {m n : ℕ} (e : AE D) : IsHalf e (0 : Mx D m n) := by
  intro i j
  simp

theorem heisenbergSymplecticForm_zero_right_eq_zero (S T : HSp D) (x : WO S T) : symplO S T x 0 = 0 := by
  simp [symplO, hO]

theorem heisO_zero_eq_self (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (f : WO S T → ℂ) : heisO ψ S T 0 f = f := by
  funext w
  simp [heisO, symplOH, heisenbergSymplecticForm_zero_right_eq_zero]

theorem heisenbergTranslationCombination_single_one_eq_translate (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (w : WO S T) (f : WO S T → ℂ) :
    GlobalTheory.SeeSaw.comb ψ S T (Finsupp.single w 1) f = heisO ψ S T w f := by
  unfold GlobalTheory.SeeSaw.comb
  rw [Finsupp.support_single_ne_zero _ one_ne_zero, Finset.sum_singleton, Finsupp.single_eq_same, one_smul]

theorem isFinComb_single_zero {S T : HSp D} : IsFinComb (Finsupp.single (0 : WO S T) (1 : ℂ)) := by
  intro u hu
  rw [Finsupp.support_single_ne_zero _ one_ne_zero, Finset.mem_singleton] at hu
  subst hu
  ext i j
  simp [Matrix.map]

theorem vacuum_isCombOf {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} (W : G.Weil) (t : T)
    (p : Pair T) : IsCombOf W (FinDatum.vacuum G t p) (Finsupp.single 0 1) := by
  refine ⟨isFinComb_single_zero, ?_, ?_⟩
  · intro u hu
    rw [Finsupp.support_single_ne_zero _ one_ne_zero, Finset.mem_singleton] at hu
    subst hu
    exact isHalf_zero_zero _
  · have he : (FinDatum.vacuum G t p).e = 0 := rfl
    intro f₀ _ _
    show AllSome _ _
    rw [heisenbergTranslationCombination_single_one_eq_translate, heisO_zero_eq_self]
    refine ⟨⟨(LinearMap.proj (R := ℂ) (φ := fun _ : WO (G.pS p) (G.pT p) => ℂ) 0).smulRight f₀, ?_, ?_, ?_⟩, ?_⟩
    · intro Φ _ x hx
      obtain rfl := eq_zero_of_isHalf_zero hx
      simp [heisO_zero_eq_self]
    · intro Φ _ y hy
      have hy0 : IsHalf (0 : AE D) y := by rw [he, map_zero] at hy; exact hy
      obtain rfl := eq_zero_of_isHalf_zero hy0
      simp [heisO_zero_eq_self, heisenbergSymplecticForm_zero_right_eq_zero]
    · have h0 : halfInd (0 : AE D) (latO (G.pS p) (G.pT p) ↑(G.latS p) ↑(G.latT p) fun _ => True) 0 = 1 := by
        rw [halfInd, if_pos ⟨zero_mem _, isHalf_zero_zero _⟩]
      rw [he]
      simp [h0]
    · intro Tm hT
      have := hT.vac
      rw [one_smul] at this
      exact this.symm

end GlobalTheory.VacComb

open GlobalTheory.VacComb in

theorem GlobalTheory.VacComb.main : Big fun {D} _ _ _ _ {T} _ _ _ _ _ _ ch => ∀ (t : T) (j : Fin D.R.m), IsCombOf ch.W (FinDatum.vacuum ch.G t (.top t j)) (Finsupp.single 0 1) := by
  refine ⟨0, fun _ _ _ => ⟨0, ?_⟩⟩
  intros
  exact fun t j => vacuum_isCombOf _ t _
