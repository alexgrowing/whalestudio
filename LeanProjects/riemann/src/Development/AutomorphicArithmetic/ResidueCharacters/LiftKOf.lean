import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.LiftingConditionOfCrystallineLift
import Development.AutomorphicArithmetic.ResidueCharacters.LocNum
import Development.AutomorphicArithmetic.ResidueCharacters.LocRes

noncomputable section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations

namespace UpperTheory.N

theorem liftK_of (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (l : ℕ) [Fact l.Prime]
    (h54 : LiftingTheory.LiftTheoremAllCases D HW F 23 32 32) (hres : ElementDenominator.CrystallineRestrictionToExtension D.loc)
    (hF : ∀ K LL : FinExt l, TruncatedSeriesCountingIdentities.FontaineAt ((D.loc l).PD K) ↥LL.1 ↥(OL LL)) : LiftK (D.loc l) := by
  intro N h K LL hC T₁ T₂ f hc1 hc2 hon hj
  obtain ⟨K', hKK, hg, hKs, hnor, hidx⟩ := LocNum.exists_up hC
  have hle : GK K' ≤ GK K := GK_le hKK
  have hrn : (Subgroup.inclusion hle).range.Normal := by
    rw [Subgroup.inclusion_range]; exact hnor.subgroupOf _
  have hB := LocRes.caseB (D.loc l) (HW l) hg hKs
  obtain ⟨r1, j1⟩ := LocRes.res_crys D.loc hres hF hKK hle T₁ hc1
  obtain ⟨r2, -⟩ := LocRes.res_crys D.loc hres hF hKK hle T₂ hc2
  have hJ : LiftingTheory.JumpsLet ((HW l).W K' _ LL hg) (LocRes.res hle T₁) (fun _ => h) (fun _ => h) :=
    fun _ τ _ a ha => hj _ a ((j1 τ a).1 ha)
  have h1 := ((h54.2.2.2.2 l K' K hKK hle (hnor.subgroupOf _) _ LL hg).1 hrn T₁ T₂ f (fun _ => h) (fun _ => h)
    ⟨r1, r2, hon⟩ hJ).2 hB
  have h2 := (h54.2.2.2.1 l K' _ LL hg (LocRes.res hle T₁) (fun _ => h) (fun _ => h) r1 hJ).2.1 hB
  refine LiftF_mono _ f ?_ h1
  have hH := Hmax_const_le (Module.finrank ℚ_[l] ↥(K0 K')) h h
  rw [(HW l).W_s] at h2 ⊢
  rw [(D.loc l).PD_p] at h2 ⊢
  have h3 : LiftingTheory.ePB l (sN l N) (LiftingTheory.Mmax (Module.finrank ℚ_[l] ↥(K0 K')) fun _ => h) (LiftingTheory.Hmax (Module.finrank ℚ_[l] ↥(K0 K')) (fun _ => h) fun _ => h)
      (LiftingTheory.jumpSet ((HW l).W K' (sN l N) LL hg) (LocRes.res hle T₁)
        (LiftingTheory.Mmax (Module.finrank ℚ_[l] ↥(K0 K')) fun _ => h) (LiftingTheory.Mmax (Module.finrank ℚ_[l] ↥(K0 K')) fun _ => h)) ≤
      32 * (LiftingTheory.Hmax (Module.finrank ℚ_[l] ↥(K0 K')) (fun _ => h) (fun _ => h) * sN l N + 1) := by
    exact_mod_cast h2
  have h4 : LiftingTheory.Hmax (Module.finrank ℚ_[l] ↥(K0 K')) (fun _ => h) (fun _ => h) * sN l N ≤
      2 * h * sN l N := Nat.mul_le_mul_right _ (by omega)
  refine (Nat.add_le_add h3 hidx).trans ?_
  unfold eL lamN
  omega

end UpperTheory.N

end
