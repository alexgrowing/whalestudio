import Mathlib
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.EigCoordApply

open scoped NNReal
open NumberField GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Flat.ExG

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Flat.ExG.Red

section Xfer

variable {A B K M : Type} [CommRing A] [CommRing B] [CommRing K] [Algebra A K] [Algebra B K]
  [AddCommGroup M] [Module K M] [Module A M] [Module B M] [IsScalarTower A K M] [IsScalarTower B K M]

def xfer (h : (algebraMap A K).range = (algebraMap B K).range) (X : Submodule A M) : Submodule B M where
  carrier := X
  zero_mem' := X.zero_mem
  add_mem' := fun hx hy => X.add_mem hx hy
  smul_mem' := fun c x hx => by
    obtain ⟨a, ha⟩ : algebraMap B K c ∈ (algebraMap A K).range := h ▸ ⟨c, rfl⟩
    have e : c • x = a • x := by rw [← algebraMap_smul K c x, ← ha, algebraMap_smul]
    rw [e]
    exact X.smul_mem a hx

theorem mem_xfer (h : (algebraMap A K).range = (algebraMap B K).range) {X : Submodule A M} {y : M} :
    y ∈ xfer h X ↔ y ∈ X := Iff.rfl

theorem xfer_span (h : (algebraMap A K).range = (algebraMap B K).range) (s : Set M) :
    xfer h (Submodule.span A s) = Submodule.span B s := by
  apply le_antisymm
  · intro y hy
    exact (Submodule.span_le (p := xfer h.symm (Submodule.span B s))).2
      (fun z hz => Submodule.subset_span hz) hy
  · exact Submodule.span_le.2 fun z hz => Submodule.subset_span hz

end Xfer

section XferEig

variable {A B K M : Type} [CommRing A] [CommRing B] [Field K] [Algebra A K] [Algebra B K]
  [AddCommGroup M] [Module K M] [Module A M] [Module B M] [IsScalarTower A K M] [IsScalarTower B K M]
  {E : Type} [Field E] [NumberField E]

theorem xfer_eigSub (h : (algebraMap A K).range = (algebraMap B K).range) (ρ : 𝓞 E →+* Module.End K M) (σ : E →+* K)
    (X : Submodule A M) : xfer h (HT.eigSub ρ σ X) = HT.eigSub ρ σ (xfer h X) := by
  ext y
  exact Iff.rfl

theorem xfer_eigQuot (h : (algebraMap A K).range = (algebraMap B K).range) (ρ : 𝓞 E →+* Module.End K M) (σ : E →+* K)
    (X : Submodule A M) : xfer h (HT.eigQuot ρ σ X) = HT.eigQuot ρ σ (xfer h X) := by
  ext y
  constructor
  · rintro ⟨z, hz, rfl⟩
    exact ⟨z, hz, rfl⟩
  · rintro ⟨z, hz, rfl⟩
    exact ⟨z, hz, rfl⟩

theorem isFreeOn_xfer (h : (algebraMap A K).range = (algebraMap B K).range) {ρ : 𝓞 E →+* Module.End K M}
    {X : Submodule A M} {N : ℕ} {t : Fin N → M} (hf : HT.IsFreeOn ρ X t) :
    HT.IsFreeOn ρ (xfer h X) t := by
  refine ⟨hf.1, hf.2.1, ?_⟩
  rw [← xfer_span h, ← hf.2.2]

end XferEig

theorem targetV : TargetO → ∀ (E : Type) [Field E] [NumberField E] (V C : Type) [CommRing V] [IsDomain V] [ValuationRing V] [Field C] [CharZero C] [Algebra V C] [IsFractionRing V C] (bar : 𝓞 E ≃+* 𝓞 E) (σ σ' : E →+* C) (rk : (E →+* C) → ℕ) (p q : ℕ) (ν : Valuation C NNReal), ν.Integers V → (∃ ℓ : C, 0 < ν ℓ ∧ ν ℓ < 1) → (∀ (s : E →+* C) (a : 𝓞 E), s (a : E) ∈ (algebraMap V C).range) → Nat.card (E →+* C) = Module.finrank ℚ E → (∀ a : 𝓞 E, σ' (a : E) = σ (bar a : 𝓞 E)) → (∀ a, bar (bar a) = a) → ∃ γ : C, γ ≠ 0 ∧ ∀ (W : Type) [AddCommGroup W] [Module C W] [Module V W] [IsScalarTower V C W] [FiniteDimensional C W] (ρ : 𝓞 E →+* Module.End C W) (ρH : 𝓞 E →+* Module.End C (W × Module.Dual C W)) (HV : Submodule V (W × Module.Dual C W)) (Lie : Submodule V W) (x : Fin (p + q) → W × Module.Dual C W) (v : Fin p → W) (w : Fin q → W) (u : Fin (p + q) → W × Module.Dual C W) (A : Matrix (Fin (p + q)) (Fin (p + q)) C), (∀ a y, (ρH a y).1 = ρ a y.1) → (∀ a φ, ρH a (0, φ) = (0, φ ∘ₗ ρ (bar a))) → HV.map ((LinearMap.fst C W (Module.Dual C W)).restrictScalars V) = Lie → (∀ φ : Module.Dual C W, (0, φ) ∈ HV ↔ ∀ e ∈ Lie, φ e ∈ (algebraMap V C).range) → HT.IsFreeOn ρH HV x → (∀ s, Module.finrank C (HT.eigSp ρ s) = rk s) → LinearIndependent C v → Submodule.span V (Set.range v) = HT.eigSub ρ σ Lie → LinearIndependent C w → Submodule.span V (Set.range w) = HT.eigSub ρ σ' Lie → IsAdapted ρH σ v w u → LinearIndependent C (fun i => ∑ j, A i j • u j) → Submodule.span V (Set.range fun i => ∑ j, A i j • u j) = HT.eigQuot ρH σ HV → ∃ ε : Vˣ, A.det = algebraMap V C ε * γ := by
  intro hO E _ _ V C _ _ _ _ _ _ _ bar σ σ' rk p q ν hν hℓ hs hcard hσ' hbar
  have hr : (algebraMap V C).range = (algebraMap ν.valuationSubring C).range := by
    ext c
    constructor
    · rintro ⟨a, rfl⟩
      exact ⟨⟨_, (Valuation.mem_valuationSubring_iff _ _).2 (hν.map_le_one a)⟩, rfl⟩
    · rintro ⟨o, rfl⟩
      obtain ⟨a, ha⟩ := hν.exists_of_le_one ((Valuation.mem_valuationSubring_iff _ _).1 o.2)
      exact ⟨a, ha⟩
  obtain ⟨γ, hγ, H⟩ := hO E C ν bar σ σ' rk p q hℓ (fun s a => by
    obtain ⟨o, ho⟩ : s (a : E) ∈ (algebraMap ν.valuationSubring C).range := hr ▸ hs s a
    rw [← ho]
    exact o.2) hcard hσ' hbar
  refine ⟨γ, hγ, ?_⟩
  intro W _ _ _ _ _ ρ ρH HV Lie x v w u A h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13
  letI : Module ν.valuationSubring W := Module.compHom W (algebraMap ν.valuationSubring C)
  haveI : IsScalarTower ν.valuationSubring C W := ⟨fun o c y => by
    change ((o : C) * c) • y = (o : C) • (c • y)
    rw [mul_smul]⟩
  obtain ⟨ε, hε⟩ := H W ρ ρH (xfer hr HV) (xfer hr Lie) x v w u A h1 h2
    (by
      ext y
      rw [mem_xfer, ← h3]
      constructor
      · rintro ⟨z, hz, rfl⟩
        exact ⟨z, hz, rfl⟩
      · rintro ⟨z, hz, rfl⟩
        exact ⟨z, hz, rfl⟩)
    (fun φ => by
      rw [mem_xfer, h4, ← hr]
      exact Iff.rfl)
    (isFreeOn_xfer hr h5) h6 h7
    (by rw [← xfer_span hr, h8, xfer_eigSub]) h9
    (by rw [← xfer_span hr, h10, xfer_eigSub]) h11 h12
    (by rw [← xfer_span hr, h13, xfer_eigQuot])
  obtain ⟨a, ha⟩ : algebraMap ν.valuationSubring C (ε : ν.valuationSubring) ∈ (algebraMap V C).range :=
    hr ▸ ⟨_, rfl⟩
  obtain ⟨b, hb⟩ : algebraMap ν.valuationSubring C ((ε⁻¹ : (ν.valuationSubring)ˣ) : ν.valuationSubring) ∈
      (algebraMap V C).range := hr ▸ ⟨_, rfl⟩
  have hab : a * b = 1 := by
    apply hν.hom_inj
    rw [map_mul, ha, hb, ← map_mul, Units.mul_inv, map_one, map_one]
  refine ⟨⟨a, b, hab, by rw [mul_comm]; exact hab⟩, ?_⟩
  rw [hε]
  exact congrArg (· * γ) ha.symm

end GlobalTheory.CompanionTheory.Ar.Flat.ExG.Red
