import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.EigenvalueSeparation.LeftInv
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.InfinitesimalCharacterLimits.AllLeaves

noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL PositivityTheory.Rg.Rs

namespace PositivityTheory.Rg.BcB.E

open PositivityTheory.Rg.BcB

attribute [local instance] borelH

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {a b : ℕ}

def thetaH (x : H E a b) : H E a b := (thetaA E a x.1, thetaA E b x.2)

def chiH (τ : ℝ) (x : H E a b) : ℝ := (cutSet E a τ ×ˢ cutSet E b τ).indicator 1 x

def hs2 (D : Dom E a b) (τ : ℝ) (φ : H E a b → ℂ) : ENNReal :=
  ∫⁻ x, ENNReal.ofReal (chiH τ x) * ∫⁻ y, ‖kerH φ x y‖ₑ ^ 2 ∂D.ν ∂D.ν

def mulS (μ : Measure (H E a b)) (φ₁ φ₂ : H E a b → ℂ) : H E a b → ℂ := fun y => ∫ z, φ₁ z * φ₂ (z⁻¹ * y) ∂μ

abbrev kerTwH (φ : H E a b → ℂ) (x y : H E a b) : ℂ := kerTw2 φ x y

def SmoothSeminormGrowth : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (a b : ℕ) (D : Dom E a b) (ι : Type) [Fintype ι]
  (Φ : Matrix ι ι (H E a b → ℂ)), IsTestM Φ →
    ∃ T : Hs (ι := ι) D →L[ℂ] Hs (ι := ι) D, IsROp D Φ T ∧ IsROp D (adjM Φ) (ContinuousLinearMap.adjoint T) ∧
      ∀ (Φ' : Matrix ι ι (H E a b → ℂ)) (T' : Hs (ι := ι) D →L[ℂ] Hs (ι := ι) D), IsTestM Φ' → IsROp D Φ' T' →
        IsROp D (mulM D.μ Φ Φ') (T.comp T')

def faceMap_comp_succAbove_castSucc : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (a b : ℕ) (D : Dom E a b) (φ : H E a b → ℂ),
  IsTestH φ → ∃ (C : ℝ) (N : ℕ), ∀ τ : ℝ, 0 ≤ τ → hs2 D τ φ ≤ ENNReal.ofReal (C * (1 + τ) ^ N)

def KernelDiagonalIntegrable : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (a b : ℕ) (D : Dom E a b) (ι : Type) [Fintype ι]
  (Φ : Matrix ι ι (H E a b → ℂ)), IsTestM Φ → ∃ M₀ : ℕ, ∀ M : ℕ, M₀ ≤ M →
    ∫⁻ x, ENNReal.ofReal (wt x ^ (-(2 * M : ℤ))) * ‖∑ i, kerH (mulM D.μ Φ (adjM Φ) i i) x x‖ₑ ∂D.ν < ⊤

def E2 : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (a b : ℕ) (D : Dom E a b) (ι : Type) [Fintype ι]
  (K : Type) [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K] (J : K →L[ℂ] Hs (ι := ι) D),
  (∀ v, ‖J v‖ = ‖v‖) →
  ∀ (B : Type) [CommRing B] [StarRing B] [Algebra ℂ B] [StarModule ℂ B] (R : B →⋆ₐ[ℂ] (K →L[ℂ] K))
    (p : B →⋆ₐ[ℂ] ℂ) (a₀ : B) (C : Set B) (Φ : B → Matrix ι ι (H E a b → ℂ)),
    (∀ x, ‖p x‖ ≤ ‖R x‖) → p a₀ ≠ 0 → C.Countable → (1 : B) ∈ C → (∀ x, IsTestM (Φ x)) →
    (∀ x, ∃ T : Hs (ι := ι) D →L[ℂ] Hs (ι := ι) D, IsROp D (Φ x) T ∧
      (∀ v : K, T (J v) = J (R (x * a₀) v)) ∧ ∀ u, (∀ v, inner ℂ (J v) u = 0) → T u = 0) →
    ∃ (M : ℕ) (s : ℕ → (B →⋆ₐ[ℂ] ℂ)) (f : ℕ → ι → H E a b → ℂ),
      (∀ x ∈ C, Tendsto (fun k => s k x) atTop (𝓝 (p x))) ∧
      ∀ k, s k a₀ ≠ 0 ∧ (∀ i, Continuous (f k i)) ∧ f k ≠ 0 ∧ LeftInv (f k) ∧ WL2 D M (f k) ∧
        ∀ x ∈ C, conv D.μ (Φ x) (f k) = s k (x * a₀) • f k

def OrthogonalKeepingOperator : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (a b : ℕ) (D : Dom E a b) (ι : Type) [Fintype ι]
  (K : Type) [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K] (J : K →L[ℂ] Hs (ι := ι) D),
  (∀ v, ‖J v‖ = ‖v‖) →
  ∀ (B : Type) [CommRing B] [StarRing B] [Algebra ℂ B] [StarModule ℂ B] (R : B →⋆ₐ[ℂ] (K →L[ℂ] K))
    (p : B →⋆ₐ[ℂ] ℂ) (a₀ : B) (C : Set B) (Φ : B → Matrix ι ι (H E a b → ℂ)) (g : ℕ → Hs (ι := ι) D),
    (∀ x, ‖p x‖ ≤ ‖R x‖) → p a₀ ≠ 0 → C.Countable → (1 : B) ∈ C → (∀ x, IsTestM (Φ x)) →
    (∀ x, ∃ T : Hs (ι := ι) D →L[ℂ] Hs (ι := ι) D, IsROp D (Φ x) T ∧
      (∀ v : K, T (J v) = J (R (x * a₀) v)) ∧
      ∀ u, (∀ v, inner ℂ (J v) u = 0) → ∀ v, inner ℂ (J v) (T u) = 0) →
    (∀ j v, inner ℂ (J v) (g j) = 0) →
    (∀ j i (M : ℕ), ∫⁻ x, ENNReal.ofReal (wt x ^ (2 * M)) * ‖(g j i : H E a b → ℂ) x‖ₑ ^ 2 ∂D.ν < ⊤) →
    ∃ (M : ℕ) (s : ℕ → (B →⋆ₐ[ℂ] ℂ)) (f : ℕ → ι → H E a b → ℂ),
      (∀ x ∈ C, Tendsto (fun k => s k x) atTop (𝓝 (p x))) ∧
      ∀ k, s k a₀ ≠ 0 ∧ (∀ i, Continuous (f k i)) ∧ f k ≠ 0 ∧ LeftInv (f k) ∧ WL2 D M (f k) ∧
        (∀ x ∈ C, conv D.μ (Φ x) (f k) = s k (x * a₀) • f k) ∧
        ∀ j, ∑ i, ∫ x, starRingEnd ℂ ((g j i : H E a b → ℂ) x) * f k i x ∂D.ν = 0

def hull {N : ℕ} (S : Set (Sm E N)) : Submodule ℂ (Sm E N) := sInf {U | S ⊆ U ∧ IsStable U}

def slices₁ {ι : Type} (f : ι → H E a b → ℂ) : Set (Sm E a) := {φ | ∃ i m₂, φ.1 = fun x => f i (x, m₂)}

def slices₂ {ι : Type} (f : ι → H E a b → ℂ) : Set (Sm E b) := {φ | ∃ i m₁, φ.1 = fun x => f i (m₁, x)}

def E3 : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (a b : ℕ) (D : Dom E a b) (ι : Type) [Fintype ι]
  (M : ℕ) (f : ι → H E a b → ℂ) (K₁ : Subgroup (GL (Fin a) (Af E))) (K₂ : Subgroup (GL (Fin b) (Af E)))
  (W₁ : Submodule ℂ (Kinf E a → ℂ)) (W₂ : Submodule ℂ (Kinf E b → ℂ)) (m₁ m₂ : (E →+* ℂ) → Multiset ℂ),
  IsOpen (K₁ : Set (GL (Fin a) (Af E))) → IsOpen (K₂ : Set (GL (Fin b) (Af E))) →
  FiniteDimensional ℂ W₁ → FiniteDimensional ℂ W₂ →
  (∀ i, Continuous (f i)) → LeftInv f → WL2 D M f → (∀ i, SpectralAccumulation.TypeH K₁ K₂ W₁ W₂ (f i)) →
  (∀ i m₂, ∃ φ : Sm E a, φ.1 = fun x => f i (x, m₂)) → (∀ i m₁, ∃ φ : Sm E b, φ.1 = fun x => f i (m₁, x)) →
  (∀ φ ∈ slices₁ f, IsAutForm φ) → (∀ φ ∈ slices₂ f, IsAutForm φ) →
  (∀ τ, HasInfCharGL (Submodule.span ℂ (slices₁ f)) τ (m₁ τ)) →
  (∀ τ, HasInfCharGL (Submodule.span ℂ (slices₂ f)) τ (m₂ τ)) →
  IsStable (hull (slices₁ f)) ∧ IsStable (hull (slices₂ f)) ∧
  (∀ φ ∈ hull (slices₁ f), IsAutForm φ) ∧ (∀ φ ∈ hull (slices₂ f), IsAutForm φ) ∧
    SpectralAccumulation.NonPos (hull (slices₁ f)) ∧ SpectralAccumulation.NonPos (hull (slices₂ f)) ∧
    SpectralAccumulation.CentIm (hull (slices₁ f)) ∧ SpectralAccumulation.CentIm (hull (slices₂ f)) ∧
    (∀ τ, HasInfCharGL (hull (slices₁ f)) τ (m₁ τ)) ∧ (∀ τ, HasInfCharGL (hull (slices₂ f)) τ (m₂ τ)) ∧
    ∀ i, f i ∈ SpectralAccumulation.pairSpace (hull (slices₁ f)) (hull (slices₂ f))

end PositivityTheory.Rg.BcB.E

end
