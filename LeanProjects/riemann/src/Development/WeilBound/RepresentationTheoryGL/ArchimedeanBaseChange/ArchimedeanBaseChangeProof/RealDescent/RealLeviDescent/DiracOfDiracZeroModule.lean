import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.RealDescent.RealLeviDescent.ExpansionTerms

noncomputable section

open Matrix Finset

namespace PositivityTheory.RgBcC.RealD

open PositivityTheory.RgBcC.Real

variable {n : ℕ}

structure IsCoreMod0 {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] (χ : Inf n)
    (E1 E2 : Fin n → Fin n → Module.End ℂ V) (σ : Matrix.unitaryGroup (Fin n) ℂ →* (V →ₗ[ℂ] V)) : Prop where
  pair : IsPair E1 E2
  ch1 : ∀ m (x : V), gelA E1 m x = GlobalTheory.Dec.gelfVal (χ true) m • x
  ch2 : ∀ m (x : V), gelA (barF E2) m x = GlobalTheory.Dec.gelfVal (χ false) m • x
  nontriv : Nontrivial V
  irr : ∀ v w : V, v ≠ 0 → ∃ x ∈ alg E1 E2, x v = w
  der : IsDerivK σ (kF E1 E2)

theorem IsCoreMod.toCoreMod0 {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] {χ : Inf n}
    {E1 E2 : Fin n → Fin n → Module.End ℂ V} {σ : Matrix.unitaryGroup (Fin n) ℂ →* (V →ₗ[ℂ] V)} {A : V →ₗ[ℂ] V}
    (h : IsCoreMod χ E1 E2 σ A) : IsCoreMod0 χ E1 E2 σ :=
  ⟨h.pair, h.ch1, h.ch2, h.nontriv, h.irr, h.der⟩

def DiracInequalityWithoutSplitComponent : Prop :=
  ∀ (n : ℕ) (lam : Fin n → ℤ), Antitone lam → ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    (E1 E2 : Fin n → Fin n → Module.End ℂ V) (σ : Matrix.unitaryGroup (Fin n) ℂ →* (V →ₗ[ℂ] V)),
    IsCoreMod0 (infOf lam) E1 E2 σ → ∀ ν : Fin n → ℝ, hwSp E1 E2 ν ≠ ⊥ → LSq lam ≤ spinSq ν

def AdmLeast0 : Prop :=
  ∀ (n : ℕ) (lam : Fin n → ℤ), Antitone lam → ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    (E1 E2 : Fin n → Fin n → Module.End ℂ V) (σ : Matrix.unitaryGroup (Fin n) ℂ →* (V →ₗ[ℂ] V)),
    IsCoreMod0 (infOf lam) E1 E2 σ → ∀ lev : Fin n → ℕ, IsLev lam lev → hwSp E1 E2 (muQ lam lev) ≠ ⊥ →
      (∀ lev' : Fin n → ℕ, IsLev lam lev' → hwSp E1 E2 (muQ lam lev') ≠ ⊥ →
        nsq (muQ lam lev + rhoV n) ≤ nsq (muQ lam lev' + rhoV n)) → AdmFor lam lev E1 E2

theorem adm_least_of_zero_module (h : AdmLeast0) : AdmLeast := fun n lam hlam V _ _ E1 E2 σ _ hc => h n lam hlam V E1 E2 σ hc.toCoreMod0

theorem adm_least_zero_of_dirac (hN : SecondTypeWeightsShorter) (hD : DiracInequalityWithoutSplitComponent) (hH : LemmaHT) : AdmLeast0 := by
  intro n lam hlam V _ _ E1 E2 σ hc lev hlev _ hleast
  refine ⟨hc.pair.gl1, hc.pair.gl2, hc.pair.comm, hc.pair.unitK, fun x => ?_, hc.ch1, hc.ch2, fun ν hν => ?_⟩
  · obtain ⟨S, hS, hxS, -, hK, -⟩ := hc.der.2 x
    exact ⟨S, hS, hxS, hK⟩
  · by_contra hne
    obtain ⟨hνT, hlt⟩ := hN n lam hlam lev hlev ν hν
    have hνh : ν ∈ harmSet lam := ((hH n lam hlam).2 ν hνT).2
      (le_antisymm ((hH n lam hlam).2 ν hνT).1 (hD n lam hlam V E1 E2 σ hc ν hne))
    classical
    simp only [harmSet, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and] at hνh
    obtain ⟨lev', hlev', rfl⟩ := hνh
    exact absurd (hleast _ hlev' hne) (not_le.2 hlt)

end PositivityTheory.RgBcC.RealD
