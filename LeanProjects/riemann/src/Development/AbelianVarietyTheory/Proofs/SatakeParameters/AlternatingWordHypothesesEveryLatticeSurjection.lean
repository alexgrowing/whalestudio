import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ThickLetterWordLatticeSurjectionHypotheses
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.HodgeTateJumpsAtModulesForSign
import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
import Formalism.FrobeniusOrbits.HostCorollaries
import Formalism.SharpRestriction.ParConsts
import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.LiftingConditionOfWindows
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.GoodCoefficientRingIntegersPadicFiniteExtension
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsUniqueEmbeddingRestrictsToWachLetterUnrami

open NumberField IsDedekindDomain GlobalTheory.HTW GlobalTheory.HTW.Rec Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.FrobeniusOrbits

namespace GlobalTheory.HTW.RecS

theorem exists_primitiveRoot_of_good {l : ℕ} [Fact l.Prime] {K LL : FinExt l} (hG : Good K 1 LL) :
    ∃ ζ : ↥LL.1, IsPrimitiveRoot ζ l := by
  have hl : l.Prime := Fact.out
  haveI : NeZero (l : Om l) := ⟨Nat.cast_ne_zero.2 hl.ne_zero⟩
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot (Om l) l
  have hmem : ζ ∈ Ks K 1 := by
    refine (le_sup_right : _ ≤ Ks K 1) (IntermediateField.subset_adjoin _ _ ?_)
    simpa using hζ.pow_eq_one
  have hLL : ζ ∈ LL.1 := hG.2.2.2 (Ks K 1).val ⟨ζ, hmem⟩
  refine ⟨⟨ζ, hLL⟩, ?_⟩
  exact IsPrimitiveRoot.of_map_of_injective (f := LL.1.val) hζ LL.1.val.toRingHom.injective

theorem setCS_of_wordsAT {l : ℕ} [Fact l.Prime] {P : LocPrime l} {K LL : FinExt l}
    (hG : Good K 1 LL) (Wc : Wach P K LL) (hs : Wc.s = 1) (hK : K.1 ≤ MaximalUnramifiedExtension l) (h11 : 11 ≤ l)
    [NeZero (Module.finrank ℚ_[l] ↥(K0 K))] (Wd : NWord (Module.finrank ℚ_[l] ↥(K0 K))) (d : ℕ)
    (hA : WordsAT l Wd d) (T₁ T₂ : Lat K LL) (F : LatHom T₁.L T₂.L) (hF : F.Onto)
    (c₁ : IsCrys (P.PD K) T₁.ρ) (c₂ : IsCrys (P.PD K) T₂.ρ)
    (hj : ∀ a, TruncatedSeriesCountingBounds.JumpsAt Wc T₁ a (Wd.win a))
    (hlow : ∀ (_ft : Fintype (↥K.1 →ₐ[ℚ_[l]] ↥LL.1)) (a), TruncatedSeriesCountingBounds.lowCount Wc T₂ a Wd.η ≤ (Wd.m : ℤ)) :
    RamifiedCoefficientChains.SetCS Wc d T₁ T₂ F Wd.sz Wd.S Wd.η Wd.m := by
  classical
  obtain ⟨hev, hup, -, -, hbig⟩ := hA
  have hp : (P.PD K).p = l := P.PD_p K
  have hle : K.1 ≤ K0 K := le_inf le_rfl hK
  obtain ⟨a₀, -, hsup⟩ := Finset.exists_mem_eq_sup (Finset.univ : Finset (ZMod (Module.finrank ℚ_[l] ↥(K0 K))))
    Finset.univ_nonempty Wd.sz
  have hgr : IsGreatest (Set.range Wd.sz) (Finset.univ.sup Wd.sz) := by
    refine ⟨⟨a₀, hsup.symm⟩, ?_⟩
    rintro _ ⟨a, rfl⟩
    exact Finset.le_sup (Finset.mem_univ a)
  have hbig' := hbig _ hgr
  refine ⟨⟨?_, hs, by omega⟩, by omega, hev, ?_, by rw [hp]; exact exists_primitiveRoot_of_good hG, ⟨c₁, c₂, hF⟩, ?_, ?_, ?_, ?_⟩
  · refine ⟨(algebraMap ↥(K0 K) ↥K.1).injective, fun x => ⟨⟨x.1, hle x.2⟩, Subtype.ext rfl⟩⟩
  · exact (goodO_finExt_integers l LL).1
  · intro a τ hτ u hu
    have hw := hj a τ hτ u hu
    have hua := hup a
    unfold NWord.win at hw
    unfold RamifiedCoefficientChains.JumpWinS
    by_cases hpar : (a.val + d) % 2 = 1
    · have h0 : ¬ (a.val + d) % 2 = 0 := by omega
      have hu1 : Wd.up a = true := by simpa [hpar] using hua
      simp only [hu1, if_true, Set.mem_setOf_eq, abs_le] at hw
      simp only [h0, if_false, Set.mem_union, Set.mem_Icc]
      push_cast
      omega
    · have h0 : (a.val + d) % 2 = 0 := by omega
      have hu1 : Wd.up a = false := by simpa [hpar] using hua
      simp only [hu1, Bool.false_eq_true, if_false, Set.mem_setOf_eq, abs_le] at hw
      simp only [h0, if_true, Set.mem_union, Set.mem_Icc]
      push_cast
      omega
  · intro a τ hτ
    haveI : FiniteDimensional ℚ_[l] ↥K.1 := K.2
    letI ft : Fintype (↥K.1 →ₐ[ℚ_[l]] ↥LL.1) := Fintype.ofFinite _
    have h := hlow ft a
    unfold TruncatedSeriesCountingBounds.lowCount at h
    have hfil : (Finset.univ.filter (fun τ' => Formalism.MainNotions.LiftingTheory.Over Wc τ' a)) = {τ} := by
      ext τ'
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
      exact ⟨fun h' => (existsUnique_over P K LL Wc hK a).unique h' hτ, fun h' => h' ▸ hτ⟩
    rw [hfil, Finset.sum_singleton] at h
    exact h
  · intro a
    have h := (hbig' a).2
    rw [hp]
    unfold RamifiedCoefficientChains.aR RamifiedCoefficientChains.lam RamifiedCoefficientChains.hpar
    push_cast
    exact h
  · intro a
    have h := (hbig' a).1
    unfold RamifiedCoefficientChains.hpar
    push_cast
    exact h

theorem settingC_of_wordsAT : ∀ {D : D7} (L : SizeData₂ D) (HW : HWOf D.loc) (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i) (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i)) (Cx : TruncatedSeriesCountingIdentities.CoefExt D i w hw) (hG : Good (D.nbr i w hw).Kw 1 Cx.LL) (Wd : NWord (RecS.nLet i w hw)) (d : ℕ), 11 ≤ D.nd.l i → RecS.WordBase L HW i r ρ π w hw Cx hG Wd → WordsAT (D.nd.l i) Wd d → RecS.AlternatingWordLatticeSurjectionHypotheses HW i r ρ π w hw Cx hG Wd d := by
  intro D L HW i r ρ π w hw Cx hG Wd d h11 hB hA nz T₁ T₂ F h₁ h₂ hF
  have hT1 := hB.t1 T₁ h₁
  have hT2 := hB.t2 T₂ h₂
  exact setCS_of_wordsAT hG (WW HW i w hw Cx hG) ((HW (D.nd.l i)).W_s _ 1 _ hG) hB.unram h11 Wd d hA
    T₁ T₂ F hF hT1.1 hT2.1 hT1.2.1 hT2.2

end GlobalTheory.HTW.RecS
