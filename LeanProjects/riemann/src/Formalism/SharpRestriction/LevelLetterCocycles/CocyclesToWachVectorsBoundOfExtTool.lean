import Formalism.SharpRestriction.LevelLetterCocycles.ExpRules

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

def B1 (l h η S : ℕ) : ℝ :=
  (2 * (aN l (h + η) : ℝ) + 2 * (η : ℝ) + (S : ℝ)) / ((l : ℝ) - 1) + lam l (h + η)

def B2 (l h η : ℕ) : ℝ := 2 * Formalism.TruncatedSeriesCounting.RamifiedCoefficientChains.sig l h η + 2

theorem bound_sum_eq (l h η S : ℕ) : B1 l h η S + B2 l h η = cocyclesToWachVectorsExponent l h η S := by
  unfold B1 B2 cocyclesToWachVectorsExponent; ring

def uOf (W : LocWach PD LL O v n) (T : LocLat G Qp LL O) (N s₁ : ℕ) {FF : Type} [AddCommGroup FF]
    [Module O FF] (μ ms : ZMod n → FF →ₗ[O] W.DD T) (c : ZMod n) (f : FF) : W.DD T :=
  ((PD.p : ℕ) : O) ^ N • ms c f - ((PD.p : ℕ) : O) ^ s₁ • μ c f

def Step1Out [NeZero n] (W : LocWach PD LL O v n) (T : LocLat G Qp LL O) (d a N s₁ : ℕ) {FF : Type}
    [AddCommGroup FF] [Module O FF] (z : FF →ₗ[O] W.DD T) (μ : ZMod n → FF →ₗ[O] W.DD T)
    (F₁ : Submodule O FF) (ms : ZMod n → FF →ₗ[O] W.DD T) : Prop :=
  ∀ c ∈ evens n d, ∀ f : FF,
    Formalism.MainNotions.CrystallineLiftingInputs.DL W T c (ms c f) ∧
    Formalism.MainNotions.CrystallineLiftingInputs.InPN W T 1
      (((PD.p : ℕ) : O) ^ s₁ • ((letE c : LetA O n) • z f) + (W.γ T (ms c f) - ms c f)) ∧
    Formalism.MainNotions.LiftingTheory.qp W ^ a • uOf W T N s₁ μ ms c f ∈ W.N T ∧
    Formalism.MainNotions.CrystallineLiftingInputs.InPN W T 1 (W.γ T (uOf W T N s₁ μ ms c f) - uOf W T N s₁ μ ms c f) ∧
    (f ∈ F₁ → uOf W T N s₁ μ ms c f ∈ W.N T)

def Step1 [NeZero n] (W : LocWach PD LL O v n) : Prop :=
  ∀ (d : ℕ) (T₁ T₂ : LocLat G Qp LL O) (F : LatHom T₁.L T₂.L) (b : ZMod n → ℕ) (S η m : ℕ),
    SetCS W d T₁ T₂ F b S η m →
    ∃ s₁ : ℕ, (s₁ : ℝ) ≤ B1 PD.p (hpar n b S) η S ∧
    ∀ (FF : Type) [AddCommGroup FF] [Module O FF] [Module.Free O FF] [Module.Finite O FF]
      (g : FF →ₗ[O] ↥(latticeFiniteCocycles PD T₂.L)) (N : ℕ) (y z : FF →ₗ[O] W.DD T₂)
      (μ ν : ZMod n → FF →ₗ[O] W.DD T₂),
      Sh.ExtData W T₂ (MiW d b S η) (hiW d b S η) ⌈aR PD.p (hpar n b S + η)⌉₊ N g y z μ ν →
      ∃ (F₁ : Submodule O FF) (ms : ZMod n → FF →ₗ[O] W.DD T₂),
        PChain (lenOl PD (O := O)) m (lenC (finrank LL T₂.V) m PD.p (hpar n b S + η) S) ⊤ F₁
          (evens n d).card 0 ∧
        (m = 0 → F₁ = ⊤) ∧
        Step1Out W T₂ d ⌈aR PD.p (hpar n b S + η)⌉₊ N s₁ z μ F₁ ms

def Step2 [NeZero n] (W : LocWach PD LL O v n) : Prop :=
  ∀ (d : ℕ) (T₁ T₂ : LocLat G Qp LL O) (F : LatHom T₁.L T₂.L) (b : ZMod n → ℕ) (S η m : ℕ),
    SetCS W d T₁ T₂ F b S η m →
    ∃ sg : ℕ, (sg : ℝ) ≤ B2 PD.p (hpar n b S) η ∧
    ∀ (s₁ : ℕ) (FF : Type) [AddCommGroup FF] [Module O FF] [Module.Free O FF] [Module.Finite O FF]
      (g : FF →ₗ[O] ↥(latticeFiniteCocycles PD T₂.L)) (N : ℕ) (y z : FF →ₗ[O] W.DD T₂)
      (μ ν : ZMod n → FF →ₗ[O] W.DD T₂),
      Sh.ExtData W T₂ (MiW d b S η) (hiW d b S η) ⌈aR PD.p (hpar n b S + η)⌉₊ N g y z μ ν →
      ∀ (F₁ : Submodule O FF) (ms : ZMod n → FF →ₗ[O] W.DD T₂),
      Step1Out W T₂ d ⌈aR PD.p (hpar n b S + η)⌉₊ N s₁ z μ F₁ ms →
      ∃ (F₂ : Submodule O FF) (w : ZMod n → ↥F₂ →ₗ[O] W.DD T₂),
        PChain (lenOl PD (O := O)) m (lenC (finrank LL T₂.V) m PD.p (hpar n b S + η) S) F₁ F₂
          (evens n d).card 0 ∧
        (m = 0 → F₂ = F₁) ∧
        (∀ c ∈ evens n d, ∀ f : ↥F₂, QPowSmulMemPullback W T₂ c η (w c f)) ∧
        ∀ f : ↥F₂, ∃ κ : ZMod n → G → T₂.V,
          (∀ c ∈ evens n d, RhoCoc W T₂ c (Formalism.MainNotions.CrystallineLiftingInputs.Mpar PD.p (hpar n b S)) η
            (sigC PD.p (hpar n b S) η) (w c f) (κ c)) ∧
          (((PD.p : O) ^ (s₁ + sg)) • (g (f : FF) : G → T₂.V) - (∑ c ∈ evens n d, κ c) ∈ latticeCoboundaries T₂.L ∨
            ((PD.p : O) ^ (s₁ + sg)) • (g (f : FF) : G → T₂.V) + (∑ c ∈ evens n d, κ c) ∈ latticeCoboundaries T₂.L)

theorem cocyclesToWachVectorsBound_of_extTool [NeZero n] (W : LocWach PD LL O v n) (hE : Sh.ExtTool W) (h1 : Step1 W)
    (h2 : Step2 W) : CocyclesToWachVectorsBound W := by
  intro d T₁ T₂ F b S η m hS
  obtain ⟨s₁, hs₁, H1⟩ := h1 d T₁ T₂ F b S η m hS
  obtain ⟨sg, hsg, H2⟩ := h2 d T₁ T₂ F b S η m hS
  refine ⟨s₁ + sg, ?_, ?_⟩
  · have := bound_sum_eq PD.p (hpar n b S) η S
    push_cast
    linarith
  · intro FF _ _ _ _ g
    obtain ⟨N, y, z, μ, ν, hX⟩ := hE d T₁ T₂ F b S η m hS FF g
    obtain ⟨F₁, ms, hc1, hm1, ho⟩ := H1 FF g N y z μ ν hX
    obtain ⟨F₂, w, hc2, hm2, h36, hid⟩ := H2 s₁ FF g N y z μ ν hX F₁ ms ho
    refine ⟨F₂, w, ?_, ?_, h36, hid⟩
    · have hn : Even n := hS.2.2.1
      have := two_mul_card_evens_le hn d
      exact (hc1.trans hc2).mono (by omega) le_rfl
    · intro h0
      rw [hm2 h0, hm1 h0]

end Formalism.MainNotions.RamifiedCoefficientChains.S9.ExtensionLemmaAlt

end
