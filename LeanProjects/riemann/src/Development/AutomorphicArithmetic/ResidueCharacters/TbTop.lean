import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.EmbeddingTypeJumps
import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.CrysOnCond
import Formalism.LocalRingCardinality.SpanPowerMembership.NDLocE
import Development.AutomorphicArithmetic.ResidueCharacters.LocNum
import Development.AutomorphicArithmetic.ResidueCharacters.LocRes
import Development.AutomorphicArithmetic.ResidueCharacters.LenLeTorsion

noncomputable section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations

namespace UpperTheory.N

set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 800000 in
theorem tb_top (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (l : ℕ) [Fact l.Prime]
    (h4 : LocalSituation.Conclusion4 D HW F) (hCo : CrysOnCond D HW F)
    (hW : ∀ (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL),
      EmbeddingTypeJumps.WachHypothesisLocal (LocalSituation.sit D.loc HW l (D.locA l) K s LL h) ((F l).E K s LL h).tie)
    (hF : ∀ K LL : FinExt l, TruncatedSeriesCountingIdentities.FontaineAt ((D.loc l).PD K) ↥LL.1 ↥(OL LL))
    (N h n t e g : ℕ) (K LL : FinExt l) (hg : Good K (sN l N) LL) (hKs : Ks K (sN l N) = K.1)
    (U : Finset ℤ) (hn : U.card ≤ n) (hb : ∀ u ∈ U, -(h : ℤ) ≤ u ∧ u ≤ h) (he : e < t) (ht : t ≤ h)
    (hgl : g ≤ Nat.log l N + 1)
    (Yt Ve : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL)) (hcrys : IsCrys ((D.loc l).PD K) Yt.ρ)
    (hjmp : ∀ τ, JumpsInV ((D.loc l).PD K) Yt.ρ τ (U : Set ℤ))
    (p : Yt.V →ₗ[↥LL.1] ↥LL.1) (hp : ∀ g v, p (Yt.ρ g v) = p v)
    (hint : ∀ v ∈ Yt.L.T, p v ∈ Set.range (algebraMap ↥(OL LL) ↥LL.1)) (e₀ : Yt.V) (he₀ : e₀ ∈ Yt.L.T) (hpe : p e₀ = 1)
    (h1 : Module.finrank ↥LL.1 Ve.V = 1)
    (hχ : ∀ g x, Ve.ρ g x = ((algebraMap ℚ_[l] ↥LL.1 (((D.loc l).PD K).χ g : ℚ_[l]))⁻¹) ^ e • x)
    (φ : Yt.V →ₗ[↥(OL LL)] (Ve.V ⧸ Ve.L.T))
    (hφ : ∀ g, ∀ y ∈ Yt.L.T, p y = 0 → φ (Yt.ρ g y) = actD Ve.L g (φ y)) :
    ∃ c : ℕ, c + g ≤ cBL l N h n t ∧
      ((l : ↥(OL LL)) ^ c) • (fun g => φ (Yt.ρ g e₀ - e₀)) ∈ HfD ((D.loc l).PD K) Ve.L := by
  haveI : IsDiscreteValuationRing ↥(OL LL) := Formalism.BasicNotions.Examples₂.LB.OL_dvr LL
  let Y := kerY Yt p e₀ hpe hp hint he₀
  have hcjY := cj_sub (hF K LL) (S := fun _ => (U : Set ℤ)) (GRep.ofLat Yt) (LinearMap.ker p)
    (ker_stable Yt p hp) ⟨hcrys, hjmp⟩
  have hsub : LocalSituation.Jset (LocalSituation.sit D.loc HW l (D.locA l) K _ LL hg) Y ⊆ U := fun a ha => by
    obtain ⟨τ, hτ⟩ := JsetEmb.jsetSplit_all D HW l K _ LL hg Y a ha
    exact hcjY.2 τ a hτ
  have hWY := hW K _ LL hg Y h h hcjY.1 fun a ha => hb a (hsub ha)
  have hCt := hCo l K _ LL hg Yt hcrys
  haveI : IsTopologicalRing (LocalSituation.sit D.loc HW l (D.locA l) K _ LL hg).LL := inferInstanceAs (IsTopologicalRing ↥LL.1)
  haveI : IsDomain (LocalSituation.sit D.loc HW l (D.locA l) K _ LL hg).O := inferInstanceAs (IsDomain ↥(OL LL))
  haveI : IsPrincipalIdealRing (LocalSituation.sit D.loc HW l (D.locA l) K _ LL hg).O :=
    inferInstanceAs (IsPrincipalIdealRing ↥(OL LL))
  have key := TBLoc.tb_part1 (LocalSituation.sit D.loc HW l (D.locA l) K _ LL hg) Yt p e₀ hpe hp hint he₀
    Subtype.val_injective _ (h4 l K _ LL hg).1 e h h _ Ve h1 hχ hCt hWY le_rfl φ hφ
  have e1 : LocalSituation.ell (LocalSituation.sit D.loc HW l (D.locA l) K _ LL hg) = l := (D.loc l).PD_p K
  refine ⟨LocalSituation.cTBY (LocalSituation.sit D.loc HW l (D.locA l) K _ LL hg) Y h h e, ?_, ?_⟩
  · have hvd := LocRes.vdeg_le K (s := sN l N) (m := LocalSituation.mN l (sN l N) (h + h))
      (le_max_left _ _) (by unfold LocalSituation.mN; omega)
    have e2 : (LocalSituation.sit D.loc HW l (D.locA l) K _ LL hg).W.s = sN l N := (HW l).W_s _ _ _ _
    have e3 : LocalSituation.gK (LocalSituation.sit D.loc HW l (D.locA l) K _ LL hg) = 0 := by
      unfold LocalSituation.gK
      rw [e2]
      show padicValNat _ (Module.finrank ℚ_[l] ↥(Ks K _)) - padicValNat _ (Module.finrank ℚ_[l] ↥K.1) = 0
      rw [hKs, Nat.sub_self]
    unfold LocalSituation.cTBY LocalSituation.vdegMs
    rw [e3, e1, e2]
    exact LocNum.cTB_le l N h n t e _ _ Fact.out U _ hsub hn hb he ht hvd hgl
  · have e4 : ((((D.loc l).PD K).p : ℕ) : ↥(OL LL)) = (l : ↥(OL LL)) := by rw [(D.loc l).PD_p]
    rw [← e4]
    exact key

end UpperTheory.N

end
