import Mathlib
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory NumberField

noncomputable section

section Forms

variable {R : Type*} [CommSemiring R] {k n : ℕ}

def groupWeight (k n : ℕ) : Fin k × Fin n → (Fin k → ℕ) := fun ij => Pi.single ij.1 1

def IsMultiHomog (δ : ℕ) (f : MvPolynomial (Fin k × Fin n) R) : Prop :=
  IsWeightedHomogeneous (groupWeight k n) f (fun _ => δ)

def linForm (u : Fin n → R) : MvPolynomial (Fin n) R := ∑ j, C (u j) * X j

def specFirstVar (u : Fin n → R) (ij : Fin (k + 1) × Fin n) : MvPolynomial (Fin k × Fin n) R :=
  Fin.cases (motive := fun _ => MvPolynomial (Fin k × Fin n) R) (C (u ij.2))
    (fun i => X (i, ij.2)) ij.1

def specFirst (f : MvPolynomial (Fin (k + 1) × Fin n) R) (u : Fin n → R) :
    MvPolynomial (Fin k × Fin n) R :=
  bind₁ (specFirstVar u) f

end Forms

section Proj

variable {R : Type*} [CommRing R] {n : ℕ}

def IsHomogIdeal (I : Ideal (MvPolynomial (Fin n) R)) : Prop :=
  ∀ f ∈ I, ∀ d, homogeneousComponent d f ∈ I

def IsRelevant (I : Ideal (MvPolynomial (Fin n) R)) : Prop :=
  ∃ j, X j ∉ I

structure IsProjPrime (I : Ideal (MvPolynomial (Fin n) R)) : Prop where
  isPrime : I.IsPrime
  isHomog : IsHomogIdeal I
  isRelevant : IsRelevant I

abbrev ProjCycle (R : Type*) [CommRing R] (n : ℕ) := Ideal (MvPolynomial (Fin n) R) →₀ ℕ

open Classical in

def localMult {A : Type*} [CommRing A] (J W : Ideal A) : ℕ :=
  if h : W.IsPrime then
    haveI := h
    (Module.length (Localization.AtPrime W)
      (Localization.AtPrime W ⧸ J.map (algebraMap A (Localization.AtPrime W)))).toNat
  else 0

def relComps (J : Ideal (MvPolynomial (Fin n) R)) : Set (Ideal (MvPolynomial (Fin n) R)) :=
  {W | W ∈ J.minimalPrimes ∧ IsRelevant W}

open Classical in

def fundCycle [IsNoetherianRing R] (J : Ideal (MvPolynomial (Fin n) R)) : ProjCycle R n :=
  Finsupp.onFinset (J.finite_minimalPrimes_of_isNoetherianRing _).toFinset
    (fun W => if W ∈ relComps J then localMult J W else 0)
    (fun W hW => by
      rw [Set.Finite.mem_toFinset]
      by_contra h
      exact hW (if_neg fun h' => h h'.1))

def divCycle [IsNoetherianRing R] (I : Ideal (MvPolynomial (Fin n) R)) (u : Fin n → R) :
    ProjCycle R n :=
  fundCycle (I ⊔ Ideal.span {linForm u})

end Proj

section ChowForm

variable {F : Type*} [Field F] {n : ℕ}

def incidence (I : Ideal (MvPolynomial (Fin n) F)) (k : ℕ) :
    Set (Fin k × Fin n → AlgebraicClosure F) :=
  {u | ∃ x : Fin n → AlgebraicClosure F, x ≠ 0 ∧ (∀ g ∈ I, aeval x g = 0) ∧
    ∀ i, ∑ j, u (i, j) * x j = 0}

def IsChowForm (I : Ideal (MvPolynomial (Fin n) F)) (k : ℕ)
    (f : MvPolynomial (Fin k × Fin n) F) : Prop :=
  f ≠ 0 ∧ ∀ g : MvPolynomial (Fin k × Fin n) F,
    (∀ u ∈ incidence I k, aeval u g = 0) ↔ f ∣ g

def chowDegree (I : Ideal (MvPolynomial (Fin n) F)) (k : ℕ) : ℕ :=
  sInf {δ | ∃ f, IsChowForm I k f ∧ IsMultiHomog δ f}

def IsChowFormCycle (Z : ProjCycle F n) (k : ℕ) (f : MvPolynomial (Fin k × Fin n) F) : Prop :=
  ∃ c : F, c ≠ 0 ∧ ∃ g : Ideal (MvPolynomial (Fin n) F) → MvPolynomial (Fin k × Fin n) F,
    (∀ W ∈ Z.support, IsChowForm W k (g W)) ∧ f = C c * ∏ W ∈ Z.support, g W ^ Z W

end ChowForm

section Finite

variable {K : Type*} [Field K] [NumberField K] {n : ℕ}

def gaussNorm (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) {ι : Type*}
    (f : MvPolynomial ι K) : ℝ :=
  let s : NNReal := f.support.sup fun m =>
    ⟨NumberField.HeightOneSpectrum.adicAbv K v (f.coeff m), AbsoluteValue.nonneg _ _⟩
  (s : ℝ)

def integralModel (I : Ideal (MvPolynomial (Fin n) K)) : Ideal (MvPolynomial (Fin n) (𝓞 K)) :=
  I.comap (MvPolynomial.map (algebraMap (𝓞 K) K))

def vertComps (I : Ideal (MvPolynomial (Fin n) K)) (u : Fin n → 𝓞 K)
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) : Set (Ideal (MvPolynomial (Fin n) (𝓞 K))) :=
  {W | W ∈ relComps (integralModel I ⊔ Ideal.span {linForm u}) ∧
    W.comap (C : 𝓞 K →+* MvPolynomial (Fin n) (𝓞 K)) = v.asIdeal}

def reduceMod (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) (W : Ideal (MvPolynomial (Fin n) (𝓞 K))) :
    Ideal (MvPolynomial (Fin n) v.asIdeal.ResidueField) :=
  W.map (MvPolynomial.map (algebraMap (𝓞 K) v.asIdeal.ResidueField))

def vertTermAt (I : Ideal (MvPolynomial (Fin n) K)) (k : ℕ) (u : Fin n → 𝓞 K)
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) : ℝ :=
  ∑ᶠ W ∈ vertComps I u v,
    (localMult (integralModel I ⊔ Ideal.span {linForm u}) W : ℝ) *
      chowDegree (reduceMod v W) k * Real.log (Ideal.absNorm v.asIdeal)

def vertTerm (I : Ideal (MvPolynomial (Fin n) K)) (k : ℕ) (u : Fin n → 𝓞 K) : ℝ :=
  ∑ᶠ v : IsDedekindDomain.HeightOneSpectrum (𝓞 K), vertTermAt I k u v

end Finite

section Arch

open Matrix

variable {n : ℕ}

structure HermNorm (n : ℕ) where

  mat : Matrix (Fin n) (Fin n) ℂ

  isUnit_det : IsUnit mat.det

namespace HermNorm

def std (n : ℕ) : HermNorm n := ⟨1, by simp⟩

def norm (h : HermNorm n) (u : Fin n → ℂ) : ℝ :=
  √(∑ i, ‖(h.mat *ᵥ u) i‖ ^ 2)

def dualNorm (h : HermNorm n) (y : Fin n → ℂ) : ℝ :=
  √(∑ i, ‖((h.matᵀ)⁻¹ *ᵥ y) i‖ ^ 2)

def pointOf (h : HermNorm n) (y : EuclideanSpace ℂ (Fin n)) : Fin n → ℂ :=
  h.matᵀ *ᵥ fun i => y i

end HermNorm

def sphereMean (h : HermNorm n) (k : ℕ) (g : (Fin k × Fin n → ℂ) → ℝ) : ℝ :=
  ⨍ u in {u : Fin k × Fin n → ℂ | ∀ i, h.norm (fun j => u (i, j)) < 1},
    g (fun ij => ((h.norm fun j => u (ij.1, j) : ℝ) : ℂ)⁻¹ * u ij)

def mahler (h : HermNorm n) (k : ℕ) (f : MvPolynomial (Fin k × Fin n) ℂ) : ℝ :=
  sphereMean h k fun u => Real.log ‖eval u f‖

def fsLog (h : HermNorm n) (u : Fin n → ℂ) (y : Fin n → ℂ) : ℝ :=
  Real.log (‖∑ j, u j * y j‖ / h.dualNorm y)

def coneIntegral (h : HermNorm n) (J : Ideal (MvPolynomial (Fin n) ℂ)) (e : ℕ)
    (g : (Fin n → ℂ) → ℝ) : ℝ :=
  (∫ y in {y : EuclideanSpace ℂ (Fin n) | ‖y‖ < 1 ∧ ∀ q ∈ J, eval (h.pointOf y) q = 0},
      g (h.pointOf y) ∂(Measure.hausdorffMeasure ((2 * (e + 1) : ℕ) : ℝ))) /
    (Measure.hausdorffMeasure ((2 * (e + 1) : ℕ) : ℝ)
      {y : EuclideanSpace ℂ (Fin n) | ‖y‖ < 1 ∧ ∀ j : Fin n, e + 1 ≤ (j : ℕ) → y j = 0}).toReal

def cycleIntegral (h : HermNorm n) (Z : ProjCycle ℂ n) (e : ℕ) (g : (Fin n → ℂ) → ℝ) : ℝ :=
  ∑ W ∈ Z.support, (Z W : ℝ) * coneIntegral h W e g

end Arch

section Height

structure ArchData (K : Type*) [Field K] [NumberField K] (n : ℕ) where

  normAt : (K →+* ℂ) → HermNorm n

  conj_norm : ∀ σ u, (normAt (ComplexEmbedding.conjugate σ)).norm (star u) = (normAt σ).norm u

def ArchData.std (K : Type*) [Field K] [NumberField K] (n : ℕ) : ArchData K n where
  normAt _ := HermNorm.std n
  conj_norm _ u := by simp [HermNorm.std, HermNorm.norm]

variable {K : Type*} [Field K] [NumberField K] {n : ℕ}

def chowHt (H : ArchData K n) (k δ : ℕ) (f : MvPolynomial (Fin k × Fin n) K) : ℝ :=
  (1 / Module.finrank ℚ K : ℝ) *
    ((∑ᶠ v : IsDedekindDomain.HeightOneSpectrum (𝓞 K), Real.log (gaussNorm v f)) +
      ∑ σ : K →+* ℂ, (mahler (H.normAt σ) k (f.map σ) + k * δ * (harmonic (n - 1) : ℝ) / 2))

end Height

def SphereMeanLinear.Statement : Prop :=
  ∀ (n : ℕ) (p : Fin n → ℂ), ∑ j, ‖p j‖ ^ 2 = 1 →
    sphereMean (HermNorm.std n) 1 (fun z => Real.log ‖∑ j, z (0, j) * star (p j)‖) =
      -(harmonic (n - 1) : ℝ) / 2

def ChowFormSection.Statement : Prop :=
  ∀ (F : Type) [Field F] [CharZero F] (n e : ℕ) (I : Ideal (MvPolynomial (Fin n) F))
    (f : MvPolynomial (Fin (e + 1) × Fin n) F) (u : Fin n → F),
    IsProjPrime I → IsChowForm I (e + 1) f → linForm u ∉ I →
      IsChowFormCycle (divCycle I u) e (specFirst f u)

def ChowFormSectionVertical.Statement : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (n e : ℕ) (I : Ideal (MvPolynomial (Fin n) K))
    (f : MvPolynomial (Fin (e + 1) × Fin n) K) (u : Fin n → 𝓞 K),
    IsProjPrime I → IsChowForm I (e + 1) f → linForm (fun j => (u j : K)) ∉ I →
      ∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 K),
        Real.log (gaussNorm v f) - Real.log (gaussNorm v (specFirst f fun j => (u j : K))) =
          vertTermAt I (e + 1) u v

def ChowFormSwap.Statement : Prop :=
  ∀ (F : Type) [Field F] (n k : ℕ) (I : Ideal (MvPolynomial (Fin n) F))
    (f : MvPolynomial (Fin k × Fin n) F), IsChowForm I k f →
      ∀ τ : Equiv.Perm (Fin k), ∃ c : F, c ^ 2 = 1 ∧ rename (Prod.map τ id) f = C c * f

def MahlerSection.Statement : Prop :=
  ∀ (n e δ : ℕ) (h : HermNorm n) (Z : ProjCycle ℂ n) (f : MvPolynomial (Fin (e + 1) × Fin n) ℂ)
    (u : Fin n → ℂ),
    (∀ W ∈ Z.support, IsProjPrime W) → IsChowFormCycle Z (e + 1) f → IsMultiHomog δ f →
    (∀ W ∈ Z.support, linForm u ∉ W) →
      mahler h e (specFirst f u) =
        mahler h (e + 1) f + δ * (harmonic (n - 1) : ℝ) / 2 + cycleIntegral h Z e (fsLog h u)

def GaussLemma.Statement : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
    (ι : Type) (f g : MvPolynomial ι K), gaussNorm v (f * g) = gaussNorm v f * gaussNorm v g

def MahlerMul.Statement : Prop :=
  ∀ (n k : ℕ) (h : HermNorm n) (f g : MvPolynomial (Fin k × Fin n) ℂ), f ≠ 0 → g ≠ 0 →
    mahler h k (f * g) = mahler h k f + mahler h k g

def ChowHeightMul.Statement : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (n : ℕ) (H : ArchData K n) (k δ₁ δ₂ : ℕ)
    (f₁ f₂ : MvPolynomial (Fin k × Fin n) K), f₁ ≠ 0 → f₂ ≠ 0 →
      chowHt H k (δ₁ + δ₂) (f₁ * f₂) = chowHt H k δ₁ f₁ + chowHt H k δ₂ f₂

def ChowHeightRecursion.Statement : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (n e δ : ℕ) (H : ArchData K n)
    (I : Ideal (MvPolynomial (Fin n) K)) (f : MvPolynomial (Fin (e + 1) × Fin n) K)
    (u : Fin n → 𝓞 K),
    IsProjPrime I → IsChowForm I (e + 1) f → IsMultiHomog δ f →
    linForm (fun j => (u j : K)) ∉ I →
      chowHt H (e + 1) δ f =
        chowHt H e δ (specFirst f fun j => (u j : K)) +
          (1 / Module.finrank ℚ K : ℝ) *
            (vertTerm I (e + 1) u -
              ∑ σ : K →+* ℂ, cycleIntegral (H.normAt σ) (fundCycle (I.map (MvPolynomial.map σ))) e
                (fsLog (H.normAt σ) fun j => σ (u j)))

def ChowHeightLowerBound.Statement : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (n e δ : ℕ) (H : ArchData K n)
    (I : Ideal (MvPolynomial (Fin n) K)) (f : MvPolynomial (Fin (e + 1) × Fin n) K)
    (S : Set (Fin n → 𝓞 K)) (Λ : (K →+* ℂ) → ℝ),
    IsProjPrime I → IsChowForm I (e + 1) f → IsMultiHomog δ f →
    Submodule.span (𝓞 K) S = ⊤ → (∀ s ∈ S, ∀ σ, (H.normAt σ).norm (fun j => σ (s j)) ≤ Λ σ) →
      -(((e + 1) * δ : ℕ) : ℝ) * ((1 / Module.finrank ℚ K : ℝ) * ∑ σ : K →+* ℂ, Real.log (Λ σ)) ≤
        chowHt H (e + 1) δ f

section Inhabitants

theorem X_dvd_iff_constantCoeff_eq_zero {R : Type*} [CommRing R]
    (f : MvPolynomial (Fin 1 × Fin 1) R) : X (0, 0) ∣ f ↔ constantCoeff f = 0 := by
  rw [X_dvd_iff_modMonomial_eq_zero]
  constructor
  · intro h
    have h0 := congrArg (coeff 0) h
    rw [coeff_modMonomial_of_not_le _ (by simp)] at h0
    simpa [constantCoeff_eq] using h0
  · intro h
    ext s
    rw [coeff_zero]
    by_cases hs : Finsupp.single ((0 : Fin 1), (0 : Fin 1)) 1 ≤ s
    · exact coeff_modMonomial_of_le _ hs
    · rw [coeff_modMonomial_of_not_le _ hs]
      have hs0 : s = 0 := by
        ext ij
        obtain rfl : ij = (0, 0) := Subsingleton.elim _ _
        by_contra hne
        exact hs (Finsupp.single_le_iff.mpr (Nat.one_le_iff_ne_zero.mpr hne))
      rw [hs0]
      simpa [constantCoeff_eq] using h

theorem mem_incidence_point {F : Type*} [Field F] (u : Fin 1 × Fin 1 → AlgebraicClosure F) :
    u ∈ incidence (⊥ : Ideal (MvPolynomial (Fin 1) F)) 1 ↔ u = 0 := by
  constructor
  · rintro ⟨x, hx, -, hu⟩
    have hx0 : x 0 ≠ 0 := fun h => hx (funext fun j => by rw [Fin.fin_one_eq_zero j]; exact h)
    have h := hu 0
    simp only [Fin.sum_univ_one] at h
    have hu0 : u (0, 0) = 0 := (mul_eq_zero.mp h).resolve_right hx0
    funext ij
    obtain rfl : ij = (0, 0) := Subsingleton.elim _ _
    exact hu0
  · rintro rfl
    refine ⟨fun _ => 1, fun h => one_ne_zero (congrFun h 0), fun g hg => ?_, fun i => ?_⟩
    · rw [Ideal.mem_bot] at hg
      simp [hg]
    · simp

theorem isProjPrime_point (F : Type*) [Field F] :
    IsProjPrime (⊥ : Ideal (MvPolynomial (Fin 1) F)) where
  isPrime := Ideal.isPrime_bot
  isHomog f hf d := by
    rw [Ideal.mem_bot] at hf ⊢
    simp [hf]
  isRelevant := ⟨0, by rw [Ideal.mem_bot]; exact X_ne_zero 0⟩

theorem isChowForm_point (F : Type*) [Field F] :
    IsChowForm (⊥ : Ideal (MvPolynomial (Fin 1) F)) 1 (X (0, 0)) := by
  refine ⟨X_ne_zero _, fun g => ?_⟩
  rw [X_dvd_iff_constantCoeff_eq_zero]
  simp only [mem_incidence_point, forall_eq, aeval_zero]
  exact map_eq_zero_iff _ (algebraMap F (AlgebraicClosure F)).injective

theorem isMultiHomog_point (R : Type*) [CommSemiring R] :
    IsMultiHomog 1 (X (0, 0) : MvPolynomial (Fin 1 × Fin 1) R) := by
  have h := isWeightedHomogeneous_X (R := R) (groupWeight 1 1) ((0 : Fin 1), (0 : Fin 1))
  have hw : groupWeight 1 1 ((0 : Fin 1), (0 : Fin 1)) = fun _ => 1 := by
    funext i
    rw [Fin.fin_one_eq_zero i]
    simp [groupWeight]
  rw [hw] at h
  exact h

theorem linForm_one_not_mem_point (F : Type*) [Field F] :
    linForm (fun _ => (1 : F)) ∉ (⊥ : Ideal (MvPolynomial (Fin 1) F)) := by
  rw [Ideal.mem_bot]
  simp [linForm, X_ne_zero]

theorem isChowFormCycle_point (F : Type*) [Field F] :
    IsChowFormCycle (Finsupp.single (⊥ : Ideal (MvPolynomial (Fin 1) F)) 1) 1 (X (0, 0)) := by
  refine ⟨1, one_ne_zero, fun _ => X (0, 0), fun W hW => ?_, ?_⟩
  · rw [Finsupp.support_single _ one_ne_zero, Finset.mem_singleton] at hW
    subst hW
    exact isChowForm_point F
  · rw [Finsupp.support_single _ one_ne_zero]
    simp

theorem chowDegree_point (F : Type*) [Field F] :
    chowDegree (⊥ : Ideal (MvPolynomial (Fin 1) F)) 1 = 1 := by
  have hX := isChowForm_point F
  have key : ∀ δ, (∃ f, IsChowForm (⊥ : Ideal (MvPolynomial (Fin 1) F)) 1 f ∧ IsMultiHomog δ f) →
      δ = 1 := by
    rintro δ ⟨f, hf, hδ⟩
    have hXf : X (0, 0) ∣ f := (hX.2 f).mp ((hf.2 f).mpr dvd_rfl)
    have hfX : f ∣ X (0, 0) := (hf.2 _).mp ((hX.2 _).mpr dvd_rfl)
    obtain ⟨q, rfl⟩ := hXf
    obtain ⟨r, hr⟩ := hfX
    have hqr : q * r = 1 := by
      have h' : X (0, 0) * (q * r) = X (0, 0) * 1 := by
        rw [mul_one, ← mul_assoc]
        exact hr.symm
      exact mul_left_cancel₀ (X_ne_zero _) h'
    obtain ⟨c, -, rfl⟩ := (isUnit_iff_eq_C_of_isReduced (P := q)).mp (IsUnit.of_mul_eq_one r hqr)
    have h1 : IsWeightedHomogeneous (groupWeight 1 1) (X (0, 0) * C c : MvPolynomial (Fin 1 × Fin 1) F)
        ((fun _ => 1) + 0) :=
      IsWeightedHomogeneous.mul (isMultiHomog_point F) (isWeightedHomogeneous_C _ c)
    rw [add_zero] at h1
    exact congrFun (IsWeightedHomogeneous.inj_right hf.1 hδ h1) 0
  apply le_antisymm
  · exact Nat.sInf_le ⟨X (0, 0), hX, isMultiHomog_point F⟩
  · exact le_csInf ⟨1, X (0, 0), hX, isMultiHomog_point F⟩ fun δ hδ => (key δ hδ).ge

theorem SphereMeanLinear.hypotheses_inhabited : ∑ j : Fin 1, ‖(fun _ => (1 : ℂ)) j‖ ^ 2 = 1 := by
  simp

theorem ChowFormSection.hypotheses_inhabited :
    IsProjPrime (⊥ : Ideal (MvPolynomial (Fin 1) ℚ)) ∧
      IsChowForm (⊥ : Ideal (MvPolynomial (Fin 1) ℚ)) (0 + 1) (X (0, 0)) ∧
      linForm (fun _ => (1 : ℚ)) ∉ (⊥ : Ideal (MvPolynomial (Fin 1) ℚ)) :=
  ⟨isProjPrime_point ℚ, isChowForm_point ℚ, linForm_one_not_mem_point ℚ⟩

theorem ChowFormSectionVertical.hypotheses_inhabited :
    IsProjPrime (⊥ : Ideal (MvPolynomial (Fin 1) ℚ)) ∧
      IsChowForm (⊥ : Ideal (MvPolynomial (Fin 1) ℚ)) (0 + 1) (X (0, 0)) ∧
      linForm (fun j => (((fun _ => (1 : 𝓞 ℚ)) : Fin 1 → 𝓞 ℚ) j : ℚ)) ∉
        (⊥ : Ideal (MvPolynomial (Fin 1) ℚ)) := by
  refine ⟨isProjPrime_point ℚ, isChowForm_point ℚ, ?_⟩
  simpa using linForm_one_not_mem_point ℚ

theorem ChowFormSwap.hypotheses_inhabited :
    IsChowForm (⊥ : Ideal (MvPolynomial (Fin 1) ℚ)) 1 (X (0, 0)) :=
  isChowForm_point ℚ

theorem MahlerSection.hypotheses_inhabited :
    (∀ W ∈ (Finsupp.single (⊥ : Ideal (MvPolynomial (Fin 1) ℂ)) 1).support, IsProjPrime W) ∧
      IsChowFormCycle (Finsupp.single (⊥ : Ideal (MvPolynomial (Fin 1) ℂ)) 1) (0 + 1) (X (0, 0)) ∧
      IsMultiHomog 1 (X (0, 0) : MvPolynomial (Fin (0 + 1) × Fin 1) ℂ) ∧
      (∀ W ∈ (Finsupp.single (⊥ : Ideal (MvPolynomial (Fin 1) ℂ)) 1).support,
        linForm (fun _ => (1 : ℂ)) ∉ W) := by
  have hs : (Finsupp.single (⊥ : Ideal (MvPolynomial (Fin 1) ℂ)) 1).support = {⊥} :=
    Finsupp.support_single _ one_ne_zero
  refine ⟨?_, isChowFormCycle_point ℂ, isMultiHomog_point ℂ, ?_⟩
  · intro W hW
    rw [hs, Finset.mem_singleton] at hW
    subst hW
    exact isProjPrime_point ℂ
  · intro W hW
    rw [hs, Finset.mem_singleton] at hW
    subst hW
    exact linForm_one_not_mem_point ℂ

theorem MahlerMul.hypotheses_inhabited :
    (X (0, 0) : MvPolynomial (Fin 1 × Fin 1) ℂ) ≠ 0 ∧ (X (0, 0) : MvPolynomial (Fin 1 × Fin 1) ℂ) ≠ 0 :=
  ⟨X_ne_zero _, X_ne_zero _⟩

theorem ChowHeightMul.hypotheses_inhabited :
    (X (0, 0) : MvPolynomial (Fin 1 × Fin 1) ℚ) ≠ 0 ∧ (X (0, 0) : MvPolynomial (Fin 1 × Fin 1) ℚ) ≠ 0 :=
  ⟨X_ne_zero _, X_ne_zero _⟩

theorem ChowHeightRecursion.hypotheses_inhabited :
    IsProjPrime (⊥ : Ideal (MvPolynomial (Fin 1) ℚ)) ∧
      IsChowForm (⊥ : Ideal (MvPolynomial (Fin 1) ℚ)) (0 + 1) (X (0, 0)) ∧
      IsMultiHomog 1 (X (0, 0) : MvPolynomial (Fin (0 + 1) × Fin 1) ℚ) ∧
      linForm (fun j => (((fun _ => (1 : 𝓞 ℚ)) : Fin 1 → 𝓞 ℚ) j : ℚ)) ∉
        (⊥ : Ideal (MvPolynomial (Fin 1) ℚ)) := by
  refine ⟨isProjPrime_point ℚ, isChowForm_point ℚ, isMultiHomog_point ℚ, ?_⟩
  simpa using linForm_one_not_mem_point ℚ

theorem ChowHeightLowerBound.hypotheses_inhabited :
    IsProjPrime (⊥ : Ideal (MvPolynomial (Fin 1) ℚ)) ∧
      IsChowForm (⊥ : Ideal (MvPolynomial (Fin 1) ℚ)) (0 + 1) (X (0, 0)) ∧
      IsMultiHomog 1 (X (0, 0) : MvPolynomial (Fin (0 + 1) × Fin 1) ℚ) ∧
      Submodule.span (𝓞 ℚ) {(fun _ => 1 : Fin 1 → 𝓞 ℚ)} = ⊤ ∧
      (∀ s ∈ ({(fun _ => 1 : Fin 1 → 𝓞 ℚ)} : Set (Fin 1 → 𝓞 ℚ)), ∀ σ : ℚ →+* ℂ,
        ((ArchData.std ℚ 1).normAt σ).norm (fun j => σ (s j)) ≤ 1) := by
  refine ⟨isProjPrime_point ℚ, isChowForm_point ℚ, isMultiHomog_point ℚ, ?_, ?_⟩
  · rw [eq_top_iff]
    intro v _
    rw [Submodule.mem_span_singleton]
    exact ⟨v 0, funext fun j => by rw [Fin.fin_one_eq_zero j]; simp⟩
  · intro s hs σ
    rw [Set.mem_singleton_iff] at hs
    subst hs
    simp [ArchData.std, HermNorm.std, HermNorm.norm]

end Inhabitants

end

end GroundTheory.Heights₂.Heights
