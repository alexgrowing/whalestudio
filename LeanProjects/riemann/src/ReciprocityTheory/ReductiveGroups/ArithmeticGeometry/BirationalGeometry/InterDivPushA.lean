import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterRed
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterDivSupp

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.Geo

open MvPolynomial MeasureTheory ReciprocityTheory.AnForm.M

def DivPushCommonProjStatement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)) (n : ℕ)
    (A : HermLine ι) (s : MRing ι), IsArithVar P (n + 2) → IsSectionOn P A s →
    ∃ Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (n + 1) → ℂ),
      ∀ W ∈ divSupp P s, IsHorizontal W → IsGoodProj W Ψ

def DivPushFibreStatement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P J : Ideal (MRing ι)) (n : ℕ)
    (R : AnLogRes P J (n + 1)) (L : Fin n → HermLine ι) (A B : HermLine ι) (s : MRing ι)
    (r : ℕ) (m : Fin r → ℕ) (W : Fin r → Set R.X) (BW : ∀ k, FinHolAtlas n (W k))
    (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (n + 1) → ℂ)),
    IsArithVar P (n + 2) → (∀ j, IsSmoothHerm (L j)) → IsSmoothHerm A → IsSmoothHerm B →
    B.a = 0 → IsSectionOn P A s →
    IsSNC R.A (potOf R A) (fun x y => eval (R.lift x y) (map (Int.castRingHom ℂ) s)) m W →
    (∀ k, HoloMap (BW k) R.A Subtype.val) →
    (∀ W' ∈ divSupp P s, IsHorizontal W' → IsGoodProj W' Ψ) →
    ∑ k, (m k : ℝ) * mInt (BW k)
        (fun i => (potOf R (L i)).pullback Subtype.val continuous_subtype_val)
        ((fun x => Real.log (B.h (R.lift x x))) ∘ Subtype.val) =
      ∫ y, ∑ᶠ (W') (_ : W' ∈ divSupp P s ∧ IsHorizontal W'),
        (multAt (P ⊔ Ideal.span {s}) W' : ℝ) *
          ∑ᶠ w ∈ fibre W' Ψ y, sheetDensity W' Ψ (pot L) (fun z => Real.log (B.h z)) y w

def projCoord {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {P J : Ideal (MRing ι)}
    {e n : ℕ} (R : AnLogRes P J e) (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (n + 1) → ℂ)) (x : R.X) :
    Fin n → ℂ :=
  fun i => Ψ (segre (R.lift x x)) i.succ / Ψ (segre (R.lift x x)) 0

def divFib {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {P J : Ideal (MRing ι)}
    {n : ℕ} (R : AnLogRes P J (n + 1)) (L : Fin n → HermLine ι) (B : HermLine ι)
    (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (n + 1) → ℂ)) {V : Set R.X} (BV : FinHolAtlas n V)
    (y : Fin n → ℂ) : ℝ :=
  ∑ᶠ x ∈ (projCoord R Ψ ∘ Subtype.val : V → Fin n → ℂ) ⁻¹' {y},
    Real.log (B.h (R.lift x x)) *
      pushDens BV (fun i => (potOf R (L i)).pullback Subtype.val continuous_subtype_val)
        (projCoord R Ψ ∘ Subtype.val) x

def DivPushResSideStatement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P J : Ideal (MRing ι)) (n : ℕ)
    (R : AnLogRes P J (n + 1)) (L : Fin n → HermLine ι) (B : HermLine ι)
    (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (n + 1) → ℂ)) (V : Set R.X) (BV : FinHolAtlas n V),
    IsArithVar P (n + 2) → (∀ j, IsSmoothHerm (L j)) → IsSmoothHerm B → B.a = 0 → IsClosed V →
    HoloMap BV R.A Subtype.val → (∀ x ∈ V, Ψ (segre (R.lift x x)) ≠ 0) →
    Integrable (divFib R L B Ψ BV) ∧
      mInt BV (fun i => (potOf R (L i)).pullback Subtype.val continuous_subtype_val)
        ((fun x => Real.log (B.h (R.lift x x))) ∘ Subtype.val) = ∫ y, divFib R L B Ψ BV y

def DivPushPointStatement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P J : Ideal (MRing ι)) (n : ℕ)
    (R : AnLogRes P J (n + 1)) (L : Fin n → HermLine ι) (A B : HermLine ι) (s : MRing ι)
    (r : ℕ) (m : Fin r → ℕ) (W : Fin r → Set R.X) (BW : ∀ k, FinHolAtlas n (W k))
    (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (n + 1) → ℂ)),
    IsArithVar P (n + 2) → (∀ j, IsSmoothHerm (L j)) → IsSmoothHerm A → IsSmoothHerm B →
    B.a = 0 → IsSectionOn P A s →
    IsSNC R.A (potOf R A) (fun x y => eval (R.lift x y) (map (Int.castRingHom ℂ) s)) m W →
    (∀ k, HoloMap (BW k) R.A Subtype.val) →
    (∀ W' ∈ divSupp P s, IsHorizontal W' → IsGoodProj W' Ψ) →
    ∀ᵐ y, ∑ k, (m k : ℝ) * divFib R L B Ψ (BW k) y =
      ∑ᶠ (W') (_ : W' ∈ divSupp P s ∧ IsHorizontal W'),
        (multAt (P ⊔ Ideal.span {s}) W' : ℝ) *
          ∑ᶠ w ∈ fibre W' Ψ y, sheetDensity W' Ψ (pot L) (fun z => Real.log (B.h z)) y w

theorem finsum_divSupp_eq {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
    (P : Ideal (MRing ι)) (s : MRing ι) (g : Ideal (MRing ι) → ℝ) :
    (∑ᶠ (W') (_ : W' ∈ divSupp P s ∧ IsHorizontal W'), g W') =
      ∑ W' ∈ ((divSupp_finite P s).subset (fun _ h => h.1) :
        {W' | W' ∈ divSupp P s ∧ IsHorizontal W'}.Finite).toFinset, g W' :=
  finsum_mem_eq_finite_toFinset_sum g _

theorem resDivPush_of_fibre (hE : ResExistsStatement) (hB : ResBridgeStatement)
    (hI : PtsIntegrableStatement) (hC : DivPushCommonProjStatement)
    (hF : DivPushFibreStatement) : ResDivPushStatement := by
  intro K _ ι _ P J n R L A B s r m W BW hP hL hA hB1 hB0 hs hsnc hBW
  obtain ⟨Ψ, hΨ⟩ := hC K ι P n A s hP hs
  rw [hF K ι P J n R L A B s r m W BW Ψ hP hL hA hB1 hB0 hs hsnc hBW hΨ]
  have hv : (fun z => Real.log (B.h z)) = logNorm B.inv 1 :=
    funext fun z => (logNorm_inv_one B z).symm
  have hAr : ∀ W' ∈ divSupp P s, IsHorizontal W' → IsArithVar W' (n + 1) :=
    fun W' hW hH => (divSuppArith K ι P (n + 1) A s W' hP hs hW).1 hH
  simp_rw [finsum_divSupp_eq P s]
  rw [integral_finsetSum]
  · refine Finset.sum_congr rfl fun W' hW' => ?_
    rw [Set.Finite.mem_toFinset] at hW'
    have hA' := hAr W' hW'.1 hW'.2
    rw [integral_const_mul, hv, ptsIntegral_eq_at hE hB hA' (hΨ W' hW'.1 hW'.2) hL
      (isSmoothHerm_inv hB1) (isSectionOn_inv_one hA'.2.1.1 hB0)]
    rfl
  · intro W' hW'
    rw [Set.Finite.mem_toFinset] at hW'
    have hA' := hAr W' hW'.1 hW'.2
    rw [hv]
    exact (hI K ι W' n Ψ L B.inv 1 hA' (hΨ W' hW'.1 hW'.2) hL (isSmoothHerm_inv hB1)
      (isSectionOn_inv_one hA'.2.1.1 hB0)).const_mul _

end ReciprocityTheory.ChartRestriction.G.Geo
