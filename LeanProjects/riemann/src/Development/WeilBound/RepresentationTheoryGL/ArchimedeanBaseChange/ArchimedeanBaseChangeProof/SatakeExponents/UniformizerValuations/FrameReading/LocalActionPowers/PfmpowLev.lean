import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.FrameReading.FmTools
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousCj
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousInvolutiveLocalTransposeInverse
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBallSubset

noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory Filter
open GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC GlobalTheory.BCT GlobalTheory.LFun PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.SpectralAccumulation PositivityTheory.Rg.BcB.G8 PositivityTheory.Rg.BcB.CG
open PositivityTheory.Rg.BcB.F.RS PositivityTheory.Rg.BcB.F.Tail
open scoped Classical

namespace PositivityTheory.Rg.BcB.F.FA.MatrixConvolutionPowers

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {a b : ℕ}

theorem thL_cont_invol (n : ℕ) (w : Pl E) : Continuous (thL n w) ∧ ∀ g : GLw n w, thL n w (thL n w g) = g := by
  unfold thL
  split_ifs
  · exact ⟨continuous_id, fun g => rfl⟩
  · exact ⟨GlobalTheory.LocTwist.continuous_thetaGL n (cj w) (GlobalTheory.CompanionTheory.IwUFacts.continuous_cj w),
      GlobalTheory.LocTwist.thetaGL_thetaGL n (cj w) (GlobalTheory.PrincCong.cj_cj w)⟩

theorem level_of_comap {G₁ G₂ : Type} [Group G₁] [Group G₂] [TopologicalSpace G₁] [TopologicalSpace G₂]
    [IsTopologicalGroup G₁] [IsTopologicalGroup G₂]
    (θ : G₁ →* G₁) (hθ : Continuous θ) (hθθ : ∀ g, θ (θ g) = g) (ι : G₁ →* G₂) (hι : Continuous ι)
    (U : Subgroup G₂) (hU : IsOpen (U : Set G₂)) (K : Subgroup G₁) (hK : ∀ g, ι g ∈ U → g ∈ K) :
    IsLevel θ K (U.comap ι ⊓ U.comap (ι.comp θ)) ∧ ∀ g ∈ U.comap ι ⊓ U.comap (ι.comp θ), ι g ∈ U := by
  refine ⟨⟨?_, fun g hg => hK g (Subgroup.mem_inf.1 hg).1, fun k hk => ?_⟩, fun g hg => (Subgroup.mem_inf.1 hg).1⟩
  · rw [Subgroup.coe_inf, Subgroup.coe_comap, Subgroup.coe_comap]
    exact (hU.preimage hι).inter (hU.preimage (hι.comp hθ))
  · obtain ⟨h1, h2⟩ := Subgroup.mem_inf.1 hk
    refine Subgroup.mem_inf.2 ⟨h2, ?_⟩
    change ι (θ (θ k)) ∈ U
    rw [hθθ]; exact h1

theorem exists_level_prod (w : Pl E) (U : Subgroup (GLw a w × GLw b w)) (hU : IsOpen (U : Set (GLw a w × GLw b w)))
    (hle : U ≤ K2 a b w) :
    ∃ (V₁ : Subgroup (GLw a w)) (V₂ : Subgroup (GLw b w)), IsLevel (thL a w) (GlobalTheory.LFun.KGL w a) V₁ ∧
      IsLevel (thL b w) (GlobalTheory.LFun.KGL w b) V₂ ∧ V₁.prod V₂ ≤ U := by
  obtain ⟨c₁, i₁⟩ := thL_cont_invol (E := E) a w
  obtain ⟨c₂, i₂⟩ := thL_cont_invol (E := E) b w
  have hl := level_of_comap (thL a w) c₁ i₁ (MonoidHom.inl (GLw a w) (GLw b w))
    (continuous_id.prodMk continuous_const) U hU (GlobalTheory.LFun.KGL w a)
    (fun g hg => (Subgroup.mem_prod.1 (hle hg)).1)
  have hr := level_of_comap (thL b w) c₂ i₂ (MonoidHom.inr (GLw a w) (GLw b w))
    (continuous_const.prodMk continuous_id) U hU (GlobalTheory.LFun.KGL w b)
    (fun g hg => (Subgroup.mem_prod.1 (hle hg)).2)
  refine ⟨_, _, hl.1, hr.1, fun x hx => ?_⟩
  obtain ⟨hx₁, hx₂⟩ := Subgroup.mem_prod.1 hx
  have e : x = MonoidHom.inl (GLw a w) (GLw b w) x.1 * MonoidHom.inr (GLw a w) (GLw b w) x.2 := by
    ext <;> simp
  rw [e]
  exact U.mul_mem (hl.2 _ hx₁) (hr.2 _ hx₂)

theorem isHecke_idem {w : Pl E} (V₁ : Subgroup (GLw a w)) (V₂ : Subgroup (GLw b w))
    (hV₁ : IsLevel (thL a w) (GlobalTheory.LFun.KGL w a) V₁) (hV₂ : IsLevel (thL b w) (GlobalTheory.LFun.KGL w b) V₂) :
    IsHecke (V₁.prod V₂) (idem (V₁.prod V₂)) := by
  have hVo : IsOpen ((V₁.prod V₂ : Subgroup (GLw a w × GLw b w)) : Set (GLw a w × GLw b w)) := by
    rw [Subgroup.coe_prod]; exact hV₁.1.prod hV₂.1
  have hVc : IsClosed ((V₁.prod V₂ : Subgroup (GLw a w × GLw b w)) : Set (GLw a w × GLw b w)) :=
    Subgroup.isClosed_of_isOpen _ hVo
  have hK : IsCompact ((K2 a b w : Subgroup (GLw a w × GLw b w)) : Set (GLw a w × GLw b w)) := by
    rw [K2, Subgroup.coe_prod]
    exact (GlobalTheory.CompanionTheory.IwLevels.isCompact_KGL w a).prod (GlobalTheory.CompanionTheory.IwLevels.isCompact_KGL w b)
  have hsub : ((V₁.prod V₂ : Subgroup (GLw a w × GLw b w)) : Set (GLw a w × GLw b w)) ⊆ (K2 a b w : Set _) := by
    intro x hx
    obtain ⟨h1, h2⟩ := Subgroup.mem_prod.1 hx
    exact Subgroup.mem_prod.2 ⟨hV₁.2.1 h1, hV₂.2.1 h2⟩
  refine ⟨HasCompactSupport.intro' (hK.of_isClosed_subset hVc hsub) hVc fun x hx => ?_, fun k hk x => ⟨?_, ?_⟩⟩
  · unfold idem; exact Set.indicator_of_notMem hx _
  · unfold idem
    by_cases hx : x ∈ V₁.prod V₂
    · rw [Set.indicator_of_mem hx, Set.indicator_of_mem ((V₁.prod V₂).mul_mem hk hx)]
    · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem (fun h => hx (by simpa using (V₁.prod V₂).mul_mem ((V₁.prod V₂).inv_mem hk) h))]
  · unfold idem
    by_cases hx : x ∈ V₁.prod V₂
    · rw [Set.indicator_of_mem hx, Set.indicator_of_mem ((V₁.prod V₂).mul_mem hx hk)]
    · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem (fun h => hx (by simpa using (V₁.prod V₂).mul_mem h ((V₁.prod V₂).inv_mem hk)))]

end PositivityTheory.Rg.BcB.F.FA.MatrixConvolutionPowers

end
