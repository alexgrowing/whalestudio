import Formalism.SharpRestriction.LevelLetterCocycles.SecondLiftAtSituation

noncomputable section

namespace Formalism.MainNotions.RamifiedCoefficientChains.S9.ExtensionLemmaAlt

open Module Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.RamifiedCoefficientChains TensorProduct

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}

theorem second_lift_of_hypotheses [NeZero n] (W : LocWach PD LL O v n) (hZ : TTool2Z W)
    (hF : Formalism.MainNotions.CrystallineLiftingInputs.FTool W) (hB : Sh.BasTool W) (hK : Sh.LemK W) (hD : Sh.FilDim W)
    (hR : Sh.ExpRing W) (hE : Sh.ExpRules W)
    (h2a : ∀ T : LocLat G Qp LL O, IsCrys PD T.ρ → Formalism.MainNotions.DeltaInvariantLattices.p2aK W T)
    (h5 : Formalism.MainNotions.DeltaInvariantLattices.P5W W) (h9 : Formalism.MainNotions.DeltaInvariantLattices.P9W W) (hEx : DcrisExactStrict PD LL)
    (hCs : CrysSubQuot PD LL) (hDq : DdREqDcris PD LL) : Step2 W := by
  intro d T₁ T₂ F b S η m hS
  obtain ⟨hDom, hDVR, hFr⟩ := hS.2.2.2.1
  refine ⟨2 * sigC PD.p (hpar n b S) η, Step2A.sigma_bound_le _ _ _ hS.2.1, ?_⟩
  intro s₁ FF _ _ _ _ g N y z μ ν hX F₁ ms hO
  exact second_lift_at_situation W hZ hF hB hK hD hR hE h2a h5 h9 hEx hCs hDq hS s₁ g N y z μ ν hX F₁ ms hO

end Formalism.MainNotions.RamifiedCoefficientChains.S9.ExtensionLemmaAlt

end
