import Formalism.SharpRestriction.LevelLetterCocycles.DerivativeProdSubEval
import Formalism.SharpRestriction.LevelLetterCocycles.FrobeniusPowUniformizerFactorisation
import Formalism.SharpRestriction.LevelLetterCocycles.CancelUnitMulUniformizerPow

noncomputable section

namespace Formalism.MainNotions.RamifiedCoefficientChains.S9

open Module Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.RamifiedCoefficientChains Polynomial

theorem lemmaGD_cc {l : ℕ} [Fact l.Prime] {P : LocPrime l} (H : LocHW l P) {K LL : FinExt l}
    (hg : Good K 1 LL) :
    ∃ cc : ℤ → ↥(OL LL), ∀ x : ℤ, (-(((P.PD K).p : ℕ) : ↥(OL LL))) * cc x =
      ((((H.W K 1 LL hg).χΓ (H.W K 1 LL hg).gam) ^ (-x) : (↥(OL LL))ˣ) : ↥(OL LL)) - 1 := by
  obtain ⟨z, hz, hv⟩ := Formalism.MainNotions.LiftingTheory.gam_zl (H := H) hg
  have hne : (z : ℤ_[l]) - 1 ≠ 0 := by
    intro h0
    rw [h0] at hv
    simp at hv
  let I : Ideal ℤ_[l] := Ideal.span {((l : ℕ) : ℤ_[l])}
  have hI : (z : ℤ_[l]) - 1 ∈ I := by
    have := (PadicInt.mem_span_pow_iff_le_valuation _ hne 1).2 (by omega)
    simpa using this
  have hz1 : Units.map (Ideal.Quotient.mk I).toMonoidHom z = 1 := by
    refine Units.ext ?_
    rw [Units.coe_map, Units.val_one]
    exact (Ideal.Quotient.eq.2 hI).trans (map_one _)
  have hw : ∀ x : ℤ, ∃ w : ℤ_[l], -((l : ℕ) : ℤ_[l]) * w = ((z ^ (-x) : ℤ_[l]ˣ) : ℤ_[l]) - 1 := by
    intro x
    have h1 : (Ideal.Quotient.mk I) ((z ^ (-x) : ℤ_[l]ˣ) : ℤ_[l]) = (Ideal.Quotient.mk I) 1 := by
      have := congrArg Units.val
        (show Units.map (Ideal.Quotient.mk I).toMonoidHom (z ^ (-x)) = 1 by
          rw [map_zpow, hz1, one_zpow])
      rw [Units.coe_map, Units.val_one] at this
      exact this.trans (map_one _).symm
    obtain ⟨w, hw⟩ := Ideal.mem_span_singleton'.1 (Ideal.Quotient.eq.1 h1)
    exact ⟨-w, by rw [← hw]; ring⟩
  choose w hw using hw
  refine ⟨fun x => algebraMap ℤ_[l] ↥(OL LL) (w x), fun x => ?_⟩
  have e := congrArg (algebraMap ℤ_[l] ↥(OL LL)) (hw x)
  rw [map_mul, map_neg, map_natCast, map_sub, map_one] at e
  rw [P.PD_p K, e]
  congr 1
  have hzu : Units.map (algebraMap ℤ_[l] ↥(OL LL)).toMonoidHom z =
      (H.W K 1 LL hg).χΓ (H.W K 1 LL hg).gam := Units.ext hz
  rw [← hzu, ← map_zpow]
  rfl

theorem lemGB_L (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW)
    (Cm : CmpOf D.loc D.locA HW F) (CR CA CB CK C₀ : ℝ) (hA : Formalism.MainNotions.CrystallineLiftingInputs.admitted D HW F Cm CR CA CB CK C₀)
    (hC4 : Formalism.MainNotions.N.LetterConditionGlobal D HW F)
    (h56 : ∀ (l : ℕ) [Fact l.Prime] (K LL : FinExt l) (hg : Good K 1 LL)
      [NeZero (Module.finrank ℚ_[l] ↥(K0 K))], WachGammaDerivation ((HW l).W K 1 LL hg)) :
    ∀ (l : ℕ) [Fact l.Prime] (K LL : FinExt l) (hg : Good K 1 LL)
      [NeZero (Module.finrank ℚ_[l] ↥(K0 K))], LemGB ((HW l).W K 1 LL hg) := by
  intro l _ K LL hg _
  have hQ := hA.2.2.2.2.2.2.2.2.2.2.2.2.1 l K LL hg
  have h9 := (hA.1 l K 1 LL hg).2.2.2.2.2.2.2.2.1
  refine lemGB_of _ hQ (fun hCA => Formalism.MainNotions.CrystallineLiftingInputs.RToolNum_holds (D.loc l) (HW l) K LL hg hCA)
    (hC4 l K 1 LL hg) h9 (Formalism.MainNotions.LiftingTheory.lattice_clause_every_situation D HW F l K 1 LL hg)
    (fun _ => lemmaGD_cc (HW l) hg) (fun _ => ?_) (h56 l K LL hg)
  rw [(D.loc l).PD_p K]
  exact Formalism.MainNotions.UnusedSlot80.Split2.isUnit_pred l LL

theorem lemmaGs_L (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW)
    (Cm : CmpOf D.loc D.locA HW F) (CR CA CB CK C₀ : ℝ)
    (hA : Formalism.MainNotions.CrystallineLiftingInputs.admitted D HW F Cm CR CA CB CK C₀) (hC4 : Formalism.MainNotions.N.LetterConditionGlobal D HW F)
    (h56 : ∀ (l : ℕ) [Fact l.Prime] (K LL : FinExt l) (hg : Good K 1 LL)
      [NeZero (Module.finrank ℚ_[l] ↥(K0 K))], WachGammaDerivation ((HW l).W K 1 LL hg))
    (hGA : ∀ (l : ℕ) [Fact l.Prime] (K LL : FinExt l) (hg : Good K 1 LL)
      [NeZero (Module.finrank ℚ_[l] ↥(K0 K))], LemGA ((HW l).W K 1 LL hg)) :
    ∀ (l : ℕ) [Fact l.Prime] (K LL : FinExt l) (hg : Good K 1 LL)
      [NeZero (Module.finrank ℚ_[l] ↥(K0 K))], LemmaGs ((HW l).W K 1 LL hg) := by
  intro l _ K LL hg _
  exact lemmaGs_of_lemGAB _ (hGA l K LL hg)
    (lemGB_L D HW F Cm CR CA CB CK C₀ hA hC4 h56 l K LL hg)

theorem local_clause_of_gamma_lemmas (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW)
    (Cm : CmpOf D.loc D.locA HW F) (CR CA CB CK C₀ : ℝ)
    (hA : Formalism.MainNotions.CrystallineLiftingInputs.admitted D HW F Cm CR CA CB CK C₀) (hC4 : Formalism.MainNotions.N.LetterConditionGlobal D HW F)
    (h56 : ∀ (l : ℕ) [Fact l.Prime] (K LL : FinExt l) (hg : Good K 1 LL)
      [NeZero (Module.finrank ℚ_[l] ↥(K0 K))], WachGammaDerivation ((HW l).W K 1 LL hg))
    (hGA : ∀ (l : ℕ) [Fact l.Prime] (K LL : FinExt l) (hg : Good K 1 LL)
      [NeZero (Module.finrank ℚ_[l] ↥(K0 K))], LemGA ((HW l).W K 1 LL hg)) :
    Formalism.MainNotions.CrystallineLiftingInputs.adm18 D HW F Cm := by
  intro l _ K LL hg _
  exact lemmaG_of_sharp _ (lemmaGs_L D HW F Cm CR CA CB CK C₀ hA hC4 h56 hGA l K LL hg)

end Formalism.MainNotions.RamifiedCoefficientChains.S9
