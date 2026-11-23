import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied

noncomputable section

namespace GlobalTheory.Published

open Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc Module

namespace BlochKato

variable {l : ℕ} [Fact l.Prime]
    {G : Type} [Group G] [TopologicalSpace G] {K₀ K : Type} [Field K₀] [Field K]
    [Algebra ℚ_[l] K₀] [Algebra ℚ_[l] K] [Algebra K₀ K] [IsScalarTower ℚ_[l] K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra ℚ_[l] B] [Algebra K₀ B] [IsScalarTower ℚ_[l] K₀ B]
    [Algebra ℚ_[l] BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower ℚ_[l] K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower ℚ_[l] K₀ BdR]
    (PD : PeriodData G ℚ_[l] K₀ K B BdR)

def DimFormula : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module ℚ_[l] V] [FiniteDimensional ℚ_[l] V]
    [TopologicalSpace V] [IsModuleTopology ℚ_[l] V] [ContinuousAdd V] [ContinuousConstSMul ℚ_[l] V]
    (ρ : Representation ℚ_[l] G V), (∀ x, Continuous fun g => ρ g x) → IsDR PD ρ →
    FiniteDimensional ℚ_[l] (FiniteCohomology PD ρ) ∧
    (finrank ℚ_[l] (FiniteCohomology PD ρ) : ℤ) = finrank ℚ_[l] ↥(H0V ρ) +
      ((finrank ℚ_[l] ↥(DdR PD ρ) : ℤ) -
        finrank ℚ_[l] ↥(DdR PD ρ ⊓ FilV PD (LL := ℚ_[l]) (V := V) 0))

def RationalDuality : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module ℚ_[l] V] [FiniteDimensional ℚ_[l] V]
    [TopologicalSpace V] [IsModuleTopology ℚ_[l] V] [ContinuousAdd V] [ContinuousConstSMul ℚ_[l] V]
    (V' : Type) [AddCommGroup V'] [Module ℚ_[l] V'] [FiniteDimensional ℚ_[l] V']
    [TopologicalSpace V'] [IsModuleTopology ℚ_[l] V'] [ContinuousAdd V'] [ContinuousConstSMul ℚ_[l] V']
    (ρ : Representation ℚ_[l] G V) (ρ' : Representation ℚ_[l] G V') (P : V →ₗ[ℚ_[l]] V' →ₗ[ℚ_[l]] ℚ_[l]),
    (∀ x, Continuous fun g => ρ g x) → (∀ y, Continuous fun g => ρ' g y) →
    IsDR PD ρ → IsDual1 PD ρ ρ' P →
    (∀ a ∈ continuousCocycles ρ, (a ∈ finiteCocycles PD ρ ↔ ∀ b ∈ finiteCocycles PD ρ', CobL PD (cupL ρ' P a b))) ∧
    (∀ b ∈ continuousCocycles ρ', (b ∈ finiteCocycles PD ρ' ↔ ∀ a ∈ finiteCocycles PD ρ, CobL PD (cupL ρ' P a b)))

def IntegralDuality : Prop :=
  ∀ L1 : Lattice (O := ℤ_[l]) (charRep (cycLL PD ℚ_[l])),
    L1.T = LinearMap.range (Algebra.linearMap ℤ_[l] ℚ_[l]) →
  ∀ (V : Type) [AddCommGroup V] [Module ℚ_[l] V] [Module ℤ_[l] V] [IsScalarTower ℤ_[l] ℚ_[l] V]
    [FiniteDimensional ℚ_[l] V]
    [TopologicalSpace V] [IsModuleTopology ℚ_[l] V] [ContinuousAdd V] [ContinuousConstSMul ℚ_[l] V]
    (V' : Type) [AddCommGroup V'] [Module ℚ_[l] V'] [Module ℤ_[l] V'] [IsScalarTower ℤ_[l] ℚ_[l] V']
    [FiniteDimensional ℚ_[l] V']
    [TopologicalSpace V'] [IsModuleTopology ℚ_[l] V'] [ContinuousAdd V'] [ContinuousConstSMul ℚ_[l] V']
    (ρ : Representation ℚ_[l] G V) (ρ' : Representation ℚ_[l] G V')
    (L : Lattice (O := ℤ_[l]) ρ) (L' : Lattice (O := ℤ_[l]) ρ') (P : V →ₗ[ℚ_[l]] V' →ₗ[ℚ_[l]] ℚ_[l]),
    (∀ x, Continuous fun g => ρ g x) → (∀ y, Continuous fun g => ρ' g y) →
    IsDR PD ρ → IsDualLat1 PD L L' P →
    (∀ c ∈ divisibleCocycles L', (c ∈ HfD PD L' ↔ ∀ d ∈ latticeFiniteCocycles PD L, CobO PD L1 (cupLD L' P d c))) ∧
    (∀ d ∈ latticeCocycles L, (d ∈ latticeFiniteCocycles PD L ↔
      ∀ c ∈ divisibleCocycles L', c ∈ HfD PD L' → CobO PD L1 (cupLD L' P d c)))

end BlochKato

def BlochKatoLocal : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI → ∀ K : FinExt l,
    BlochKato.DimFormula (P.PD K) ∧ BlochKato.RationalDuality (P.PD K) ∧ BlochKato.IntegralDuality (P.PD K)

theorem BlochKato.exists_cyclotomicLattice (l : ℕ) [Fact l.Prime] (P : LocPrime l) (K : FinExt l) :
    ∃ L1 : Lattice (O := ℤ_[l]) (charRep (cycLL (P.PD K) ℚ_[l])),
      L1.T = LinearMap.range (Algebra.linearMap ℤ_[l] ℚ_[l]) := by
  have hχ : ∀ g : ↥(GK K), ‖(((P.PD K).χ g : ℚ_[l]ˣ) : ℚ_[l])‖ ≤ 1 := by
    intro g
    obtain ⟨a, ha, -⟩ := P.χQ_cyc (g : GQ l) 0 1 (by simp)
    rw [P.PD_χ]
    have h1 : ‖(P.χQ (g : GQ l) : ℚ_[l]) - (a : ℚ_[l])‖ ≤ 1 := by simpa using ha
    have h2 : ‖(a : ℚ_[l])‖ ≤ 1 := by
      have := Padic.norm_int_le_one (p := l) (a : ℤ)
      simpa using this
    have := Padic.nonarchimedean ((P.χQ (g : GQ l) : ℚ_[l]) - (a : ℚ_[l])) (a : ℚ_[l])
    rw [sub_add_cancel] at this
    exact this.trans (max_le h1 h2)
  refine ⟨⟨LinearMap.range (Algebra.linearMap ℤ_[l] ℚ_[l]), ?_, ?_, ?_, ?_⟩, rfl⟩
  · rintro g _ ⟨z, rfl⟩
    let u : ℤ_[l] := ⟨_, hχ g⟩
    refine ⟨u * z, ?_⟩
    have hu : (u : ℚ_[l]) = (((P.PD K).χ g : ℚ_[l]ˣ) : ℚ_[l]) := rfl
    simp [charRep, cycLL, hu]
  · rw [LinearMap.range_eq_map]
    exact Submodule.FG.map _ Module.Finite.fg_top
  · exact Module.Free.of_equiv
      (LinearEquiv.ofInjective (Algebra.linearMap ℤ_[l] ℚ_[l]) (IsFractionRing.injective ℤ_[l] ℚ_[l]))
  · rw [eq_top_iff]
    intro x _
    have h1 : (1 : ℚ_[l]) ∈ Submodule.span ℚ_[l]
        ((LinearMap.range (Algebra.linearMap ℤ_[l] ℚ_[l]) : Submodule ℤ_[l] ℚ_[l]) : Set ℚ_[l]) :=
      Submodule.subset_span ⟨1, by simp⟩
    simpa using Submodule.smul_mem _ x h1

namespace BlochKato

variable {l : ℕ} [Fact l.Prime]

theorem goodO_padicInt : GoodO (Qp := ℚ_[l]) ℚ_[l] ℤ_[l] := by
  refine ⟨⟨inferInstance, inferInstance, inferInstance⟩, inferInstance, inferInstance, inferInstance, ?_⟩
  exact (PadicInt.isOpenEmbedding_coe (p := l)).isOpen_range

variable {G : Type} [Group G] [TopologicalSpace G] {K₀ K : Type} [Field K₀] [Field K]
    [Algebra ℚ_[l] K₀] [Algebra ℚ_[l] K] [Algebra K₀ K] [IsScalarTower ℚ_[l] K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra ℚ_[l] B] [Algebra K₀ B] [IsScalarTower ℚ_[l] K₀ B]
    [Algebra ℚ_[l] BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower ℚ_[l] K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower ℚ_[l] K₀ BdR]
    {PD : PeriodData G ℚ_[l] K₀ K B BdR}

theorem rationalDuality_of_allCoefficients (h : bkACore PD) : RationalDuality PD := by
  intro V _ _ _ _ _ _ _ V' _ _ _ _ _ _ _ ρ ρ' P hc hc' hdR hP
  letI : Module ℤ_[l] V := Module.compHom V (algebraMap ℤ_[l] ℚ_[l])
  letI : Module ℤ_[l] V' := Module.compHom V' (algebraMap ℤ_[l] ℚ_[l])
  haveI : IsScalarTower ℤ_[l] ℚ_[l] V := IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  haveI : IsScalarTower ℤ_[l] ℚ_[l] V' := IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  exact h ℚ_[l] ℤ_[l] goodO_padicInt { V := V, ρ := ρ, cont := hc } { V := V', ρ := ρ', cont := hc' } P hdR hP

theorem integralDuality_of_allCoefficients (h : bkBCore PD) : IntegralDuality PD := by
  intro L1 hL1 V _ _ _ _ _ _ _ _ _ V' _ _ _ _ _ _ _ _ _ ρ ρ' L L' P hc hc' hdR hP
  exact h ℚ_[l] ℤ_[l] goodO_padicInt L1 hL1 { V := V, ρ := ρ, cont := hc } { V := V', ρ := ρ', cont := hc' }
    L L' P hdR hP

end BlochKato

end GlobalTheory.Published
