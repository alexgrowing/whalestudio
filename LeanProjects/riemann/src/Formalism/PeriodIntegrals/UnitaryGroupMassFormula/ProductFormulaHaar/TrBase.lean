import Mathlib

noncomputable section

open IsDedekindDomain NumberField TensorProduct ValuativeRel

namespace PI.ProdFormulaE.Tr

structure LocFam (F : Type) [Field F] [NumberField F] (ℓ : ℕ) [Fact ℓ.Prime] (ι : Type) where
  P : ι → HeightOneSpectrum (𝓞 F)
  K : ι → Type
  [fld : ∀ i, Field (K i)]
  [vr : ∀ i, ValuativeRel (K i)]
  [top : ∀ i, TopologicalSpace (K i)]
  [lf : ∀ i, IsNonarchimedeanLocalField (K i)]
  [cz : ∀ i, CharZero (K i)]
  [alg : ∀ i, Algebra ℚ_[ℓ] (K i)]
  cont : ∀ i, Continuous (algebraMap ℚ_[ℓ] (K i))
  [fin : ∀ i, FiniteDimensional ℚ_[ℓ] (K i)]
  ιF : ∀ i, F →+* K i
  dense : ∀ i, DenseRange (ιF i)
  val : ∀ i (x y : F), (ιF i x ≤ᵥ ιF i y) ↔ (P i).valuation F x ≤ (P i).valuation F y

attribute [instance] LocFam.fld LocFam.vr LocFam.top LocFam.lf LocFam.cz LocFam.alg LocFam.fin

variable {F : Type} [Field F] [NumberField F] {ℓ : ℕ} [Fact ℓ.Prime] {ι : Type}

def LocFam.Over (D : LocFam F ℓ ι) : Prop :=
  Function.Injective D.P ∧ ∀ p, p ∈ Set.range D.P ↔ ((ℓ : 𝓞 F) ∈ p.asIdeal)

def LocFam.Φ (D : LocFam F ℓ ι) : ℚ_[ℓ] ⊗[ℚ] F →ₐ[ℚ_[ℓ]] (∀ i, D.K i) :=
  Algebra.TensorProduct.lift (Algebra.ofId ℚ_[ℓ] _) (AlgHom.pi fun i => (D.ιF i).toRatAlgHom)
    (fun _ _ => Commute.all _ _)

theorem LocFam.Φ_tmul (D : LocFam F ℓ ι) (c : ℚ_[ℓ]) (x : F) (i : ι) :
    D.Φ (c ⊗ₜ x) i = algebraMap ℚ_[ℓ] (D.K i) c * D.ιF i x := by
  simp [LocFam.Φ, Algebra.ofId_apply]

def TrSurj : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (ℓ : ℕ) [Fact ℓ.Prime] (ι : Type) [Fintype ι]
    (D : LocFam F ℓ ι), D.Over → Function.Surjective D.Φ

def TrInj : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (ℓ : ℕ) [Fact ℓ.Prime] (ι : Type) [Fintype ι]
    (D : LocFam F ℓ ι), D.Over → Function.Injective D.Φ

def TrSum : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (ℓ : ℕ) [Fact ℓ.Prime] (ι : Type) [Fintype ι]
    (D : LocFam F ℓ ι), D.Over → ∀ y : F,
      ∑ i, Algebra.trace ℚ_[ℓ] (D.K i) (D.ιF i y) = algebraMap ℚ ℚ_[ℓ] (Algebra.trace ℚ F y)

end PI.ProdFormulaE.Tr
