import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.EmbeddingTypeJumps
import Development.AutomorphicArithmetic.ResidueCharacters.LocNum
import Development.AutomorphicArithmetic.ResidueCharacters.LocRes

noncomputable section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations

namespace UpperTheory.N

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 400000 in
theorem invariants_killed_over_cyclotomic_subfield_of_admissible (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (l : ℕ) [Fact l.Prime]
    (hW : ∀ (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL),
      EmbeddingTypeJumps.WachHypothesisLocal (LocalSituation.sit D.loc HW l (D.locA l) K s LL h) ((F l).E K s LL h).tie)
    (hH0 : ∀ (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL) (M0 h0 : ℕ)
      (T : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL)),
      LocalSituation.HypW (LocalSituation.sit D.loc HW l (D.locA l) K s LL h) ((F l).E K s LL h).tie T M0 h0 →
      (∀ τ, ¬ IsJumpV ((D.loc l).PD K) T.ρ τ 0) → ∀ x : T.V ⧸ T.L.T, (∀ g, actD T.L g x = x) →
      ((((D.loc l).PD K).p : ↥(OL LL)) ^ LocalSituation.cLL l (LocalSituation.mN l s (M0 + h0))
        (padicValNat l (Module.finrank ℚ_[l] ↥(Ks K (LocalSituation.mN l s (M0 + h0)))) - padicValNat l (Module.finrank ℚ_[l] ↥K.1))
        (LocalSituation.Jset (LocalSituation.sit D.loc HW l (D.locA l) K s LL h) T) 0 1) • x = 0)
    (hres : ElementDenominator.CrystallineRestrictionToExtension D.loc)
    (hF : ∀ K LL : FinExt l, TruncatedSeriesCountingIdentities.FontaineAt ((D.loc l).PD K) ↥LL.1 ↥(OL LL)) : InvariantsKilledOverCyclotomic (D.loc l) := by
  intro N h n K LL hC T U hn hb hc hj h0 x hx
  obtain ⟨K', hKK, hg, hKs, hnor, hidx⟩ := LocNum.exists_up hC
  have hle : GK K' ≤ GK K := GK_le hKK
  obtain ⟨r1, j1⟩ := LocRes.res_crys D.loc hres hF hKK hle T hc
  have hsub := LocRes.jset_sub D HW hres hF hKK hle hg T hc U hj
  have hWT := hW K' _ LL hg (LocRes.res hle T) h h r1 fun a ha => hb a (hsub ha)
  have hk := hH0 K' _ LL hg h h (LocRes.res hle T) hWT (fun τ hτ => h0 _ ((j1 τ 0).1 hτ)) x fun g => hx _
  have hvd := LocRes.vdeg_le K' (s := sN l N) (m := LocalSituation.mN l (sN l N) (h + h))
    (le_max_left _ _) (by unfold LocalSituation.mN; omega)
  rw [hKs] at hvd
  obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le (LocNum.latticeExponent_one_le_invariantsKillingExponent l N h n _ Fact.out U _ hsub hn hb hvd)
  rw [(D.loc l).PD_p] at hk
  rw [hd, pow_add, mul_comm, mul_smul]
  erw [hk]
  exact smul_zero _

end UpperTheory.N

end
