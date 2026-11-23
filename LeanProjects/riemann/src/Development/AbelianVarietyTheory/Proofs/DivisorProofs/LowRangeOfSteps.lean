import Mathlib
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.AdelicPeriodicContinuousEqZeroOfFourierCoeff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFundDomainRationalPointsAdeleTupleFinitePo
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilRangeOfSteps
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsNontrivialAdeleCharTrivialOnTotallyReal
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.RationalVectorsSameLengthOneUnitaryOrbit
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.ContFromConst

noncomputable section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.Doubling

namespace GlobalTheory.SWLow

open GlobalTheory.SWLit GlobalTheory.SWWeil GlobalTheory.SWACase

section Defs

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) {n m : ℕ}
variable {JV : Matrix (Fin m) (Fin m) E} {J₂ : Matrix (Fin (n + n)) (Fin (n + n)) E} {κ : Type} [Fintype κ]
variable (om : UA σ JV × UA σ J₂ →* Module.End ℂ ((κ → AF F) → ℂ)) (K : Subgroup (UA σ J₂))

def kfin : Submodule ℂ ((κ → AF F) → ℂ) where
  carrier := {Φ | Φ ∈ schA F κ ∧ FiniteDimensional ℂ (Submodule.span ℂ {Ψ | ∃ k ∈ K, Ψ = om (1, k) Φ})}
  zero_mem' := ⟨zero_mem _, by
    have h : Submodule.span ℂ {Ψ | ∃ k ∈ K, Ψ = om (1, k) 0} ≤ ⊥ :=
      Submodule.span_le.2 (by rintro _ ⟨k, -, rfl⟩; simp)
    exact Submodule.finiteDimensional_of_le h⟩
  add_mem' := by
    rintro Φ Ψ ⟨h1, h2⟩ ⟨h3, h4⟩
    refine ⟨add_mem h1 h3, ?_⟩
    have h : Submodule.span ℂ {X | ∃ k ∈ K, X = om (1, k) (Φ + Ψ)} ≤
        Submodule.span ℂ {X | ∃ k ∈ K, X = om (1, k) Φ} ⊔ Submodule.span ℂ {X | ∃ k ∈ K, X = om (1, k) Ψ} :=
      Submodule.span_le.2 (by
        rintro _ ⟨k, hk, rfl⟩
        rw [map_add]
        exact Submodule.add_mem_sup (Submodule.subset_span ⟨k, hk, rfl⟩) (Submodule.subset_span ⟨k, hk, rfl⟩))
    exact Submodule.finiteDimensional_of_le h
  smul_mem' := by
    rintro c Φ ⟨h1, h2⟩
    refine ⟨Submodule.smul_mem _ c h1, ?_⟩
    have h : Submodule.span ℂ {X | ∃ k ∈ K, X = om (1, k) (c • Φ)} ≤ Submodule.span ℂ {X | ∃ k ∈ K, X = om (1, k) Φ} :=
      Submodule.span_le.2 (by
        rintro _ ⟨k, hk, rfl⟩
        rw [map_smul]
        exact Submodule.smul_mem _ c (Submodule.subset_span ⟨k, hk, rfl⟩))
    exact Submodule.finiteDimensional_of_le h

def sec (Φ : (κ → AF F) → ℂ) (g : UA σ J₂) : ℂ := om (1, g) Φ 0

def eisOf (f : UA σ J₂ → ℂ) (s₁ : ℂ) (s : ℂ) (g : UA σ J₂) : ℂ :=
  Eis.cosetSum (siegelOf finSumFinEquiv (UG (cA σ) (incM F J₂)).subtype) (ratU σ J₂)
    (flatOf finSumFinEquiv (UG (cA σ) (incM F J₂)).subtype (absE F E) K f s₁ s) g

def eis (Φ : (κ → AF F) → ℂ) (g : UA σ J₂) (s : ℂ) : ℂ := eisOf σ K (sec σ om Φ) (((m : ℂ) - (n : ℂ)) / 2) s g

def IsVal (A : ((κ → AF F) → ℂ) → UA σ J₂ → ℂ) : Prop :=
  ∀ Φ ∈ kfin σ om K, ∀ g, Cont.HolValueAt (eis σ om K Φ g) (((m : ℂ) - (n : ℂ)) / 2) (A Φ g)

def IsFinPt {N : ℕ} {Q : Matrix (Fin N) (Fin N) E} (x : UA σ Q) : Prop :=
  ∀ (w : InfinitePlace F) (τ : EmbOver E w), (mat x).map (piInf τ) = 1

def IsAlg (A : ((κ → AF F) → ℂ) → UA σ J₂ → ℂ) : Prop :=
  (∀ Φ ∈ kfin σ om K, ∀ Ψ ∈ kfin σ om K, ∀ g, A (Φ + Ψ) g = A Φ g + A Ψ g) ∧
  (∀ c : ℂ, ∀ Φ ∈ kfin σ om K, ∀ g, A (c • Φ) g = c * A Φ g) ∧
  (∀ Φ ∈ kfin σ om K, ∀ γ ∈ ratU σ J₂, ∀ g, A Φ (γ * g) = A Φ g) ∧
  ∀ Φ ∈ kfin σ om K, ∀ k ∈ K, ∀ g, A (om (1, k) Φ) g = A Φ (g * k)

def KillsKer (A : ((κ → AF F) → ℂ) → UA σ J₂ → ℂ) : Prop :=
  ∀ Φ ∈ kfin σ om K, (∀ g, sec σ om Φ g = 0) → ∀ g, A Φ g = 0

def IsReg (A : ((κ → AF F) → ℂ) → UA σ J₂ → ℂ) : Prop :=
  ∀ Φ ∈ kfin σ om K, Continuous (A Φ) ∧ ∃ (C : ℝ) (N : ℕ), ∀ g, ‖A Φ g‖ ≤ C * (ht g : ℝ) ^ N

def CommFin (A : ((κ → AF F) → ℂ) → UA σ J₂ → ℂ) : Prop :=
  ∀ Φ ∈ kfin σ om K, ∀ x : UA σ J₂, IsFinPt σ x → ∀ g, A (om (1, x) Φ) g = A Φ (g * x)

def CommLie (A : ((κ → AF F) → ℂ) → UA σ J₂ → ℂ) : Prop :=
  ∀ γ : Multiplicative ℝ →* UA σ J₂, Continuous γ → ∀ Φ ∈ kfin σ om K, ∀ Φ' ∈ kfin σ om K,
    (∀ g, HasDerivAt (fun t : ℝ => sec σ om Φ (g * γ (Multiplicative.ofAdd t))) (sec σ om Φ' g) 0) →
    ∀ g, HasDerivAt (fun t : ℝ => A Φ (g * γ (Multiplicative.ofAdd t))) (A Φ' g) 0

def IsEquiv (A : ((κ → AF F) → ℂ) → UA σ J₂ → ℂ) : Prop :=
  IsAlg σ om K A ∧ KillsKer σ om K A ∧ IsReg σ om K A ∧ CommFin σ om K A ∧ CommLie σ om K A

end Defs

def StepCont : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E),
    IsCMExt F E σ → Algebra.Unramified (𝓞 F) (𝓞 E) →
  ∀ ψ : AddChar (AF F) ℂ, IsCharAF F ψ →
  ∀ (n m : ℕ), 1 ≤ n → 1 ≤ m →
  ∀ (l : E) (JV : Matrix (Fin m) (Fin m) E) (J : Matrix (Fin n) (Fin n) E) (J₂ : Matrix (Fin (n + n)) (Fin (n + n)) E),
    l ≠ 0 → IsHermND σ (l • JV) → (∀ x, form σ JV x x = 0 → x = 0) →
    (∀ i j, σ ((l⁻¹ • J) j i) = -(l⁻¹ • J) i j) → J₂ = dblGram finSumFinEquiv J →
  ∀ T : GL (Fin (n + n)) E, IsWittBasis σ J l T →
  ∀ (κ : Type) [Fintype κ] (co : Darboux (symp (R := AF F) (cA σ) (-1) (incM F JV) (incM F J₂)) κ), IsAdapted σ co →
  ∀ [MeasurableSpace (κ → AF F)] [BorelSpace (κ → AF F)] (μ : Measure (κ → AF F)), IsTamagawa F κ μ →
  ∀ χ : Chr F E, IsHecke F E χ → ResEtaPow (Units.map (algebraMap F (AF F)).toMonoidHom).range χ m →
  ∀ om : UA σ JV × UA σ J₂ →* Module.End ℂ ((κ → AF F) → ℂ), IsWeilFormulas σ ψ χ T co μ om →
  ∀ K : Subgroup (UA σ J₂), IsStdK σ T K → IwasawaOf finSumFinEquiv (UG (cA σ) (incM F J₂)).subtype (absE F E) K →
  ∀ (s₁ : ℂ), ∀ f ∈ degPSOf finSumFinEquiv (UG (cA σ) (incM F J₂)).subtype (absE F E) K χ s₁,
  ∃ σ₀ : ℝ, GlobalTheory.EisGen.ContFrom ht σ₀ (eisOf σ K f s₁)

def StepHol : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E),
    IsCMExt F E σ → Algebra.Unramified (𝓞 F) (𝓞 E) →
  ∀ ψ : AddChar (AF F) ℂ, IsCharAF F ψ →
  ∀ (n m : ℕ), 1 ≤ n → 1 ≤ m → m ≤ n →
  ∀ (l : E) (JV : Matrix (Fin m) (Fin m) E) (J : Matrix (Fin n) (Fin n) E) (J₂ : Matrix (Fin (n + n)) (Fin (n + n)) E),
    l ≠ 0 → IsHermND σ (l • JV) → (∀ x, form σ JV x x = 0 → x = 0) →
    (∀ i j, σ ((l⁻¹ • J) j i) = -(l⁻¹ • J) i j) → J₂ = dblGram finSumFinEquiv J →
  ∀ T : GL (Fin (n + n)) E, IsWittBasis σ J l T →
  ∀ (κ : Type) [Fintype κ] (co : Darboux (symp (R := AF F) (cA σ) (-1) (incM F JV) (incM F J₂)) κ), IsAdapted σ co →
  ∀ [MeasurableSpace (κ → AF F)] [BorelSpace (κ → AF F)] (μ : Measure (κ → AF F)), IsTamagawa F κ μ →
  ∀ χ : Chr F E, IsHecke F E χ → ResEtaPow (Units.map (algebraMap F (AF F)).toMonoidHom).range χ m →
  ∀ om : UA σ JV × UA σ J₂ →* Module.End ℂ ((κ → AF F) → ℂ), IsWeilFormulas σ ψ χ T co μ om →
  ∀ K : Subgroup (UA σ J₂), IsStdK σ T K → IwasawaOf finSumFinEquiv (UG (cA σ) (incM F J₂)).subtype (absE F E) K →
  ∀ Φ ∈ kfin σ om K, ∀ g, ∃ v, Cont.HolValueAt (eis σ om K Φ g) (((m : ℂ) - (n : ℂ)) / 2) v

def StepEisAlg : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E),
    IsCMExt F E σ → Algebra.Unramified (𝓞 F) (𝓞 E) →
  ∀ ψ : AddChar (AF F) ℂ, IsCharAF F ψ →
  ∀ (n m : ℕ), 1 ≤ n → 1 ≤ m →
  ∀ (l : E) (JV : Matrix (Fin m) (Fin m) E) (J : Matrix (Fin n) (Fin n) E) (J₂ : Matrix (Fin (n + n)) (Fin (n + n)) E),
    l ≠ 0 → IsHermND σ (l • JV) → (∀ x, form σ JV x x = 0 → x = 0) →
    (∀ i j, σ ((l⁻¹ • J) j i) = -(l⁻¹ • J) i j) → J₂ = dblGram finSumFinEquiv J →
  ∀ T : GL (Fin (n + n)) E, IsWittBasis σ J l T →
  ∀ (κ : Type) [Fintype κ] (co : Darboux (symp (R := AF F) (cA σ) (-1) (incM F JV) (incM F J₂)) κ), IsAdapted σ co →
  ∀ [MeasurableSpace (κ → AF F)] [BorelSpace (κ → AF F)] (μ : Measure (κ → AF F)), IsTamagawa F κ μ →
  ∀ χ : Chr F E, IsHecke F E χ → ResEtaPow (Units.map (algebraMap F (AF F)).toMonoidHom).range χ m →
  ∀ om : UA σ JV × UA σ J₂ →* Module.End ℂ ((κ → AF F) → ℂ), IsWeilFormulas σ ψ χ T co μ om →
  ∀ K : Subgroup (UA σ J₂), IsStdK σ T K → IwasawaOf finSumFinEquiv (UG (cA σ) (incM F J₂)).subtype (absE F E) K →
  ∀ A : ((κ → AF F) → ℂ) → UA σ J₂ → ℂ, IsVal σ om K A →
  IsAlg σ om K A

def StepEisReg : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E),
    IsCMExt F E σ → Algebra.Unramified (𝓞 F) (𝓞 E) →
  ∀ ψ : AddChar (AF F) ℂ, IsCharAF F ψ →
  ∀ (n m : ℕ), 1 ≤ n → 1 ≤ m →
  ∀ (l : E) (JV : Matrix (Fin m) (Fin m) E) (J : Matrix (Fin n) (Fin n) E) (J₂ : Matrix (Fin (n + n)) (Fin (n + n)) E),
    l ≠ 0 → IsHermND σ (l • JV) → (∀ x, form σ JV x x = 0 → x = 0) →
    (∀ i j, σ ((l⁻¹ • J) j i) = -(l⁻¹ • J) i j) → J₂ = dblGram finSumFinEquiv J →
  ∀ T : GL (Fin (n + n)) E, IsWittBasis σ J l T →
  ∀ (κ : Type) [Fintype κ] (co : Darboux (symp (R := AF F) (cA σ) (-1) (incM F JV) (incM F J₂)) κ), IsAdapted σ co →
  ∀ [MeasurableSpace (κ → AF F)] [BorelSpace (κ → AF F)] (μ : Measure (κ → AF F)), IsTamagawa F κ μ →
  ∀ χ : Chr F E, IsHecke F E χ → ResEtaPow (Units.map (algebraMap F (AF F)).toMonoidHom).range χ m →
  ∀ om : UA σ JV × UA σ J₂ →* Module.End ℂ ((κ → AF F) → ℂ), IsWeilFormulas σ ψ χ T co μ om →
  ∀ K : Subgroup (UA σ J₂), IsStdK σ T K → IwasawaOf finSumFinEquiv (UG (cA σ) (incM F J₂)).subtype (absE F E) K →
  ∀ A : ((κ → AF F) → ℂ) → UA σ J₂ → ℂ, IsVal σ om K A →
  IsReg σ om K A

def StepEisFin : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E),
    IsCMExt F E σ → Algebra.Unramified (𝓞 F) (𝓞 E) →
  ∀ ψ : AddChar (AF F) ℂ, IsCharAF F ψ →
  ∀ (n m : ℕ), 1 ≤ n → 1 ≤ m → m ≤ n →
  ∀ (l : E) (JV : Matrix (Fin m) (Fin m) E) (J : Matrix (Fin n) (Fin n) E) (J₂ : Matrix (Fin (n + n)) (Fin (n + n)) E),
    l ≠ 0 → IsHermND σ (l • JV) → (∀ x, form σ JV x x = 0 → x = 0) →
    (∀ i j, σ ((l⁻¹ • J) j i) = -(l⁻¹ • J) i j) → J₂ = dblGram finSumFinEquiv J →
  ∀ T : GL (Fin (n + n)) E, IsWittBasis σ J l T →
  ∀ (κ : Type) [Fintype κ] (co : Darboux (symp (R := AF F) (cA σ) (-1) (incM F JV) (incM F J₂)) κ), IsAdapted σ co →
  ∀ [MeasurableSpace (κ → AF F)] [BorelSpace (κ → AF F)] (μ : Measure (κ → AF F)), IsTamagawa F κ μ →
  ∀ χ : Chr F E, IsHecke F E χ → ResEtaPow (Units.map (algebraMap F (AF F)).toMonoidHom).range χ m →
  ∀ om : UA σ JV × UA σ J₂ →* Module.End ℂ ((κ → AF F) → ℂ), IsWeilFormulas σ ψ χ T co μ om →
  ∀ K : Subgroup (UA σ J₂), IsStdK σ T K → IwasawaOf finSumFinEquiv (UG (cA σ) (incM F J₂)).subtype (absE F E) K →
  ∀ A : ((κ → AF F) → ℂ) → UA σ J₂ → ℂ, IsVal σ om K A →
  CommFin σ om K A

def StepEisLie : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E),
    IsCMExt F E σ → Algebra.Unramified (𝓞 F) (𝓞 E) →
  ∀ ψ : AddChar (AF F) ℂ, IsCharAF F ψ →
  ∀ (n m : ℕ), 1 ≤ n → 1 ≤ m → m ≤ n →
  ∀ (l : E) (JV : Matrix (Fin m) (Fin m) E) (J : Matrix (Fin n) (Fin n) E) (J₂ : Matrix (Fin (n + n)) (Fin (n + n)) E),
    l ≠ 0 → IsHermND σ (l • JV) → (∀ x, form σ JV x x = 0 → x = 0) →
    (∀ i j, σ ((l⁻¹ • J) j i) = -(l⁻¹ • J) i j) → J₂ = dblGram finSumFinEquiv J →
  ∀ T : GL (Fin (n + n)) E, IsWittBasis σ J l T →
  ∀ (κ : Type) [Fintype κ] (co : Darboux (symp (R := AF F) (cA σ) (-1) (incM F JV) (incM F J₂)) κ), IsAdapted σ co →
  ∀ [MeasurableSpace (κ → AF F)] [BorelSpace (κ → AF F)] (μ : Measure (κ → AF F)), IsTamagawa F κ μ →
  ∀ χ : Chr F E, IsHecke F E χ → ResEtaPow (Units.map (algebraMap F (AF F)).toMonoidHom).range χ m →
  ∀ om : UA σ JV × UA σ J₂ →* Module.End ℂ ((κ → AF F) → ℂ), IsWeilFormulas σ ψ χ T co μ om →
  ∀ K : Subgroup (UA σ J₂), IsStdK σ T K → IwasawaOf finSumFinEquiv (UG (cA σ) (incM F J₂)).subtype (absE F E) K →
  ∀ A : ((κ → AF F) → ℂ) → UA σ J₂ → ℂ, IsVal σ om K A →
  CommLie σ om K A

def StepEisConst : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E),
    IsCMExt F E σ → Algebra.Unramified (𝓞 F) (𝓞 E) →
  ∀ ψ : AddChar (AF F) ℂ, IsCharAF F ψ →
  ∀ (n m : ℕ), 1 ≤ n → 1 ≤ m → m ≤ n →
  ∀ (l : E) (JV : Matrix (Fin m) (Fin m) E) (J : Matrix (Fin n) (Fin n) E) (J₂ : Matrix (Fin (n + n)) (Fin (n + n)) E),
    l ≠ 0 → IsHermND σ (l • JV) → (∀ x, form σ JV x x = 0 → x = 0) →
    (∀ i j, σ ((l⁻¹ • J) j i) = -(l⁻¹ • J) i j) → J₂ = dblGram finSumFinEquiv J →
  ∀ T : GL (Fin (n + n)) E, IsWittBasis σ J l T →
  ∀ (κ : Type) [Fintype κ] (co : Darboux (symp (R := AF F) (cA σ) (-1) (incM F JV) (incM F J₂)) κ), IsAdapted σ co →
  ∀ [MeasurableSpace (κ → AF F)] [BorelSpace (κ → AF F)] (μ : Measure (κ → AF F)), IsTamagawa F κ μ →
  ∀ χ : Chr F E, IsHecke F E χ → ResEtaPow (Units.map (algebraMap F (AF F)).toMonoidHom).range χ m →
  ∀ om : UA σ JV × UA σ J₂ →* Module.End ℂ ((κ → AF F) → ℂ), IsWeilFormulas σ ψ χ T co μ om →
  ∀ K : Subgroup (UA σ J₂), IsStdK σ T K → IwasawaOf finSumFinEquiv (UG (cA σ) (incM F J₂)).subtype (absE F E) K →
  ∀ A : ((κ → AF F) → ℂ) → UA σ J₂ → ℂ, IsVal σ om K A →
  ∀ (νN : Measure (unipN σ J₂)) (𝓓 : Set (unipN σ J₂)), νN.IsHaarMeasure → IsFundamentalDomain (ratN σ J₂) 𝓓 νN →
  ∀ Φ ∈ kfin σ om K, ∀ g, coefN σ νN 𝓓 1 (A Φ) g = 2 * sec σ om Φ g

def StepThetaAlg : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E),
    IsCMExt F E σ → Algebra.Unramified (𝓞 F) (𝓞 E) →
  ∀ ψ : AddChar (AF F) ℂ, IsCharAF F ψ →
  ∀ (n m : ℕ), 1 ≤ n → 1 ≤ m →
  ∀ (l : E) (JV : Matrix (Fin m) (Fin m) E) (J : Matrix (Fin n) (Fin n) E) (J₂ : Matrix (Fin (n + n)) (Fin (n + n)) E),
    l ≠ 0 → IsHermND σ (l • JV) → (∀ x, form σ JV x x = 0 → x = 0) →
    (∀ i j, σ ((l⁻¹ • J) j i) = -(l⁻¹ • J) i j) → J₂ = dblGram finSumFinEquiv J →
  ∀ T : GL (Fin (n + n)) E, IsWittBasis σ J l T →
  ∀ (κ : Type) [Fintype κ] (co : Darboux (symp (R := AF F) (cA σ) (-1) (incM F JV) (incM F J₂)) κ), IsAdapted σ co →
  ∀ [MeasurableSpace (κ → AF F)] [BorelSpace (κ → AF F)] (μ : Measure (κ → AF F)), IsTamagawa F κ μ →
  ∀ χ : Chr F E, IsHecke F E χ → ResEtaPow (Units.map (algebraMap F (AF F)).toMonoidHom).range χ m →
  ∀ om : UA σ JV × UA σ J₂ →* Module.End ℂ ((κ → AF F) → ℂ), IsWeilFormulas σ ψ χ T co μ om →
  ∀ K : Subgroup (UA σ J₂), IsStdK σ T K → IwasawaOf finSumFinEquiv (UG (cA σ) (incM F J₂)).subtype (absE F E) K →
  ∀ (ν : Measure (UA σ JV)) (𝓕 : Set (UA σ JV)), ν.IsHaarMeasure → IsFundamentalDomain (ratU σ JV) 𝓕 ν →
  IsAlg σ om K (thetaI σ om ν 𝓕)

def StepThetaReg : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E),
    IsCMExt F E σ → Algebra.Unramified (𝓞 F) (𝓞 E) →
  ∀ ψ : AddChar (AF F) ℂ, IsCharAF F ψ →
  ∀ (n m : ℕ), 1 ≤ n → 1 ≤ m →
  ∀ (l : E) (JV : Matrix (Fin m) (Fin m) E) (J : Matrix (Fin n) (Fin n) E) (J₂ : Matrix (Fin (n + n)) (Fin (n + n)) E),
    l ≠ 0 → IsHermND σ (l • JV) → (∀ x, form σ JV x x = 0 → x = 0) →
    (∀ i j, σ ((l⁻¹ • J) j i) = -(l⁻¹ • J) i j) → J₂ = dblGram finSumFinEquiv J →
  ∀ T : GL (Fin (n + n)) E, IsWittBasis σ J l T →
  ∀ (κ : Type) [Fintype κ] (co : Darboux (symp (R := AF F) (cA σ) (-1) (incM F JV) (incM F J₂)) κ), IsAdapted σ co →
  ∀ [MeasurableSpace (κ → AF F)] [BorelSpace (κ → AF F)] (μ : Measure (κ → AF F)), IsTamagawa F κ μ →
  ∀ χ : Chr F E, IsHecke F E χ → ResEtaPow (Units.map (algebraMap F (AF F)).toMonoidHom).range χ m →
  ∀ om : UA σ JV × UA σ J₂ →* Module.End ℂ ((κ → AF F) → ℂ), IsWeilFormulas σ ψ χ T co μ om →
  ∀ K : Subgroup (UA σ J₂), IsStdK σ T K → IwasawaOf finSumFinEquiv (UG (cA σ) (incM F J₂)).subtype (absE F E) K →
  ∀ (ν : Measure (UA σ JV)) (𝓕 : Set (UA σ JV)), ν.IsHaarMeasure → IsFundamentalDomain (ratU σ JV) 𝓕 ν →
  IsReg σ om K (thetaI σ om ν 𝓕)

def StepThetaKer : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E),
    IsCMExt F E σ → Algebra.Unramified (𝓞 F) (𝓞 E) →
  ∀ ψ : AddChar (AF F) ℂ, IsCharAF F ψ →
  ∀ (n m : ℕ), 1 ≤ n → 1 ≤ m → m ≤ n →
  ∀ (l : E) (JV : Matrix (Fin m) (Fin m) E) (J : Matrix (Fin n) (Fin n) E) (J₂ : Matrix (Fin (n + n)) (Fin (n + n)) E),
    l ≠ 0 → IsHermND σ (l • JV) → (∀ x, form σ JV x x = 0 → x = 0) →
    (∀ i j, σ ((l⁻¹ • J) j i) = -(l⁻¹ • J) i j) → J₂ = dblGram finSumFinEquiv J →
  ∀ T : GL (Fin (n + n)) E, IsWittBasis σ J l T →
  ∀ (κ : Type) [Fintype κ] (co : Darboux (symp (R := AF F) (cA σ) (-1) (incM F JV) (incM F J₂)) κ), IsAdapted σ co →
  ∀ [MeasurableSpace (κ → AF F)] [BorelSpace (κ → AF F)] (μ : Measure (κ → AF F)), IsTamagawa F κ μ →
  ∀ χ : Chr F E, IsHecke F E χ → ResEtaPow (Units.map (algebraMap F (AF F)).toMonoidHom).range χ m →
  ∀ om : UA σ JV × UA σ J₂ →* Module.End ℂ ((κ → AF F) → ℂ), IsWeilFormulas σ ψ χ T co μ om →
  ∀ K : Subgroup (UA σ J₂), IsStdK σ T K → IwasawaOf finSumFinEquiv (UG (cA σ) (incM F J₂)).subtype (absE F E) K →
  ∀ (ν : Measure (UA σ JV)) (𝓕 : Set (UA σ JV)), ν.IsHaarMeasure → IsFundamentalDomain (ratU σ JV) 𝓕 ν →
  KillsKer σ om K (thetaI σ om ν 𝓕)

def StepThetaSmooth : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E),
    IsCMExt F E σ → Algebra.Unramified (𝓞 F) (𝓞 E) →
  ∀ ψ : AddChar (AF F) ℂ, IsCharAF F ψ →
  ∀ (n m : ℕ), 1 ≤ n → 1 ≤ m →
  ∀ (l : E) (JV : Matrix (Fin m) (Fin m) E) (J : Matrix (Fin n) (Fin n) E) (J₂ : Matrix (Fin (n + n)) (Fin (n + n)) E),
    l ≠ 0 → IsHermND σ (l • JV) → (∀ x, form σ JV x x = 0 → x = 0) →
    (∀ i j, σ ((l⁻¹ • J) j i) = -(l⁻¹ • J) i j) → J₂ = dblGram finSumFinEquiv J →
  ∀ T : GL (Fin (n + n)) E, IsWittBasis σ J l T →
  ∀ (κ : Type) [Fintype κ] (co : Darboux (symp (R := AF F) (cA σ) (-1) (incM F JV) (incM F J₂)) κ), IsAdapted σ co →
  ∀ [MeasurableSpace (κ → AF F)] [BorelSpace (κ → AF F)] (μ : Measure (κ → AF F)), IsTamagawa F κ μ →
  ∀ χ : Chr F E, IsHecke F E χ → ResEtaPow (Units.map (algebraMap F (AF F)).toMonoidHom).range χ m →
  ∀ om : UA σ JV × UA σ J₂ →* Module.End ℂ ((κ → AF F) → ℂ), IsWeilFormulas σ ψ χ T co μ om →
  ∀ K : Subgroup (UA σ J₂), IsStdK σ T K → IwasawaOf finSumFinEquiv (UG (cA σ) (incM F J₂)).subtype (absE F E) K →
  ∀ (ν : Measure (UA σ JV)) (𝓕 : Set (UA σ JV)), ν.IsHaarMeasure → IsFundamentalDomain (ratU σ JV) 𝓕 ν →
  ∀ γ : Multiplicative ℝ →* UA σ J₂, Continuous γ → ∀ Φ ∈ kfin σ om K, ∃ Φ' ∈ kfin σ om K,
    (∀ g, HasDerivAt (fun t : ℝ => sec σ om Φ (g * γ (Multiplicative.ofAdd t))) (sec σ om Φ' g) 0) ∧
    ∀ g, HasDerivAt (fun t : ℝ => thetaI σ om ν 𝓕 Φ (g * γ (Multiplicative.ofAdd t))) (thetaI σ om ν 𝓕 Φ' g) 0

def StepStable : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E),
    IsCMExt F E σ → Algebra.Unramified (𝓞 F) (𝓞 E) →
  ∀ ψ : AddChar (AF F) ℂ, IsCharAF F ψ →
  ∀ (n m : ℕ), 1 ≤ n → 1 ≤ m →
  ∀ (l : E) (JV : Matrix (Fin m) (Fin m) E) (J : Matrix (Fin n) (Fin n) E) (J₂ : Matrix (Fin (n + n)) (Fin (n + n)) E),
    l ≠ 0 → IsHermND σ (l • JV) → (∀ x, form σ JV x x = 0 → x = 0) →
    (∀ i j, σ ((l⁻¹ • J) j i) = -(l⁻¹ • J) i j) → J₂ = dblGram finSumFinEquiv J →
  ∀ T : GL (Fin (n + n)) E, IsWittBasis σ J l T →
  ∀ (κ : Type) [Fintype κ] (co : Darboux (symp (R := AF F) (cA σ) (-1) (incM F JV) (incM F J₂)) κ), IsAdapted σ co →
  ∀ [MeasurableSpace (κ → AF F)] [BorelSpace (κ → AF F)] (μ : Measure (κ → AF F)), IsTamagawa F κ μ →
  ∀ χ : Chr F E, IsHecke F E χ → ResEtaPow (Units.map (algebraMap F (AF F)).toMonoidHom).range χ m →
  ∀ om : UA σ JV × UA σ J₂ →* Module.End ℂ ((κ → AF F) → ℂ), IsWeilFormulas σ ψ χ T co μ om →
  ∀ K : Subgroup (UA σ J₂), IsStdK σ T K → IwasawaOf finSumFinEquiv (UG (cA σ) (incM F J₂)).subtype (absE F E) K →
  ∀ Φ ∈ kfin σ om K, ∀ x : UA σ J₂, x ∈ K ∨ IsFinPt σ x → om (1, x) Φ ∈ kfin σ om K

def StepThetaConst : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E),
    IsCMExt F E σ → Algebra.Unramified (𝓞 F) (𝓞 E) →
  ∀ ψ : AddChar (AF F) ℂ, IsCharAF F ψ →
  ∀ (n m : ℕ), 1 ≤ n → 1 ≤ m →
  ∀ (l : E) (JV : Matrix (Fin m) (Fin m) E) (J : Matrix (Fin n) (Fin n) E) (J₂ : Matrix (Fin (n + n)) (Fin (n + n)) E),
    l ≠ 0 → IsHermND σ (l • JV) → (∀ x, form σ JV x x = 0 → x = 0) →
    (∀ i j, σ ((l⁻¹ • J) j i) = -(l⁻¹ • J) i j) → J₂ = dblGram finSumFinEquiv J →
  ∀ T : GL (Fin (n + n)) E, IsWittBasis σ J l T →
  ∀ (κ : Type) [Fintype κ] (co : Darboux (symp (R := AF F) (cA σ) (-1) (incM F JV) (incM F J₂)) κ), IsAdapted σ co →
  ∀ [MeasurableSpace (κ → AF F)] [BorelSpace (κ → AF F)] (μ : Measure (κ → AF F)), IsTamagawa F κ μ →
  ∀ χ : Chr F E, IsHecke F E χ → ResEtaPow (Units.map (algebraMap F (AF F)).toMonoidHom).range χ m →
  ∀ om : UA σ JV × UA σ J₂ →* Module.End ℂ ((κ → AF F) → ℂ), IsWeilFormulas σ ψ χ T co μ om →
  ∀ K : Subgroup (UA σ J₂), IsStdK σ T K → IwasawaOf finSumFinEquiv (UG (cA σ) (incM F J₂)).subtype (absE F E) K →
  ∀ (ν : Measure (UA σ JV)) (𝓕 : Set (UA σ JV)), ν.IsHaarMeasure → IsFundamentalDomain (ratU σ JV) 𝓕 ν →
  ∀ (νN : Measure (unipN σ J₂)) (𝓓 : Set (unipN σ J₂)), νN.IsHaarMeasure → IsFundamentalDomain (ratN σ J₂) 𝓓 νN →
  ∀ Φ ∈ kfin σ om K, ∀ g, coefN σ νN 𝓓 1 (thetaI σ om ν 𝓕 Φ) g = sec σ om Φ g

def StepNonzero : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E),
    IsCMExt F E σ → Algebra.Unramified (𝓞 F) (𝓞 E) →
  ∀ ψ : AddChar (AF F) ℂ, IsCharAF F ψ →
  ∀ (n m : ℕ), 1 ≤ n → 1 ≤ m →
  ∀ (l : E) (JV : Matrix (Fin m) (Fin m) E) (J : Matrix (Fin n) (Fin n) E) (J₂ : Matrix (Fin (n + n)) (Fin (n + n)) E),
    l ≠ 0 → IsHermND σ (l • JV) → (∀ x, form σ JV x x = 0 → x = 0) →
    (∀ i j, σ ((l⁻¹ • J) j i) = -(l⁻¹ • J) i j) → J₂ = dblGram finSumFinEquiv J →
  ∀ T : GL (Fin (n + n)) E, IsWittBasis σ J l T →
  ∀ (κ : Type) [Fintype κ] (co : Darboux (symp (R := AF F) (cA σ) (-1) (incM F JV) (incM F J₂)) κ), IsAdapted σ co →
  ∀ [MeasurableSpace (κ → AF F)] [BorelSpace (κ → AF F)] (μ : Measure (κ → AF F)), IsTamagawa F κ μ →
  ∀ χ : Chr F E, IsHecke F E χ → ResEtaPow (Units.map (algebraMap F (AF F)).toMonoidHom).range χ m →
  ∀ om : UA σ JV × UA σ J₂ →* Module.End ℂ ((κ → AF F) → ℂ), IsWeilFormulas σ ψ χ T co μ om →
  ∀ K : Subgroup (UA σ J₂), IsStdK σ T K → IwasawaOf finSumFinEquiv (UG (cA σ) (incM F J₂)).subtype (absE F E) K →
  ∃ Φ ∈ kfin σ om K, ∃ g, sec σ om Φ g ≠ 0

def StepUniqLow : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E),
    IsCMExt F E σ → Algebra.Unramified (𝓞 F) (𝓞 E) →
  ∀ ψ : AddChar (AF F) ℂ, IsCharAF F ψ →
  ∀ (n m : ℕ), 1 ≤ n → 1 ≤ m → m ≤ n →
  ∀ (l : E) (JV : Matrix (Fin m) (Fin m) E) (J : Matrix (Fin n) (Fin n) E) (J₂ : Matrix (Fin (n + n)) (Fin (n + n)) E),
    l ≠ 0 → IsHermND σ (l • JV) → (∀ x, form σ JV x x = 0 → x = 0) →
    (∀ i j, σ ((l⁻¹ • J) j i) = -(l⁻¹ • J) i j) → J₂ = dblGram finSumFinEquiv J →
  ∀ T : GL (Fin (n + n)) E, IsWittBasis σ J l T →
  ∀ (κ : Type) [Fintype κ] (co : Darboux (symp (R := AF F) (cA σ) (-1) (incM F JV) (incM F J₂)) κ), IsAdapted σ co →
  ∀ [MeasurableSpace (κ → AF F)] [BorelSpace (κ → AF F)] (μ : Measure (κ → AF F)), IsTamagawa F κ μ →
  ∀ χ : Chr F E, IsHecke F E χ → ResEtaPow (Units.map (algebraMap F (AF F)).toMonoidHom).range χ m →
  ∀ om : UA σ JV × UA σ J₂ →* Module.End ℂ ((κ → AF F) → ℂ), IsWeilFormulas σ ψ χ T co μ om →
  ∀ K : Subgroup (UA σ J₂), IsStdK σ T K → IwasawaOf finSumFinEquiv (UG (cA σ) (incM F J₂)).subtype (absE F E) K →
  ∀ A B : ((κ → AF F) → ℂ) → UA σ J₂ → ℂ, IsEquiv σ om K A → IsEquiv σ om K B →
    (∃ Φ ∈ kfin σ om K, ∃ g, B Φ g ≠ 0) →
  ∃ c : ℂ, ∀ Φ ∈ kfin σ om K, ∀ g, A Φ g = c * B Φ g

end GlobalTheory.SWLow

end
