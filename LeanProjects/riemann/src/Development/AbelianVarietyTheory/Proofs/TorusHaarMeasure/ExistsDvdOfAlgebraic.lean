import Mathlib
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.PolyImgSuccAbove

noncomputable section

namespace GlobalTheory.SectionBasis

open MvPolynomial ReciprocityTheory.ChartRestriction.G.T0 GlobalTheory.GenericSection
open scoped TensorProduct

section Univ

variable {K Ω Kl K' : Type} [Field K] [Field Ω] [Algebra K Ω] [Field Kl] [Field K'] [Algebra K Kl]
  [Algebra Kl K'] [Algebra K K'] [IsScalarTower K Kl K']

variable (K Kl K') in

def incl : Ω →+* K' ⊗[Kl] (Kl ⊗[K] Ω) :=
  (Algebra.TensorProduct.includeRight : (Kl ⊗[K] Ω) →ₐ[Kl] K' ⊗[Kl] (Kl ⊗[K] Ω)).toRingHom.comp
    (Algebra.TensorProduct.includeRight : Ω →ₐ[K] Kl ⊗[K] Ω).toRingHom

theorem incl_apply (ω : Ω) : incl K Kl K' ω = (1 : K') ⊗ₜ[Kl] ((1 : Kl) ⊗ₜ[K] ω) := rfl

theorem incl_algebraMap (c : K) :
    incl K Kl K' (algebraMap K Ω c) = algebraMap K' (K' ⊗[Kl] (Kl ⊗[K] Ω)) (algebraMap K K' c) := by
  show Algebra.TensorProduct.includeRight (Algebra.TensorProduct.includeRight (algebraMap K Ω c) :
    Kl ⊗[K] Ω) = _
  rw [AlgHom.commutes, IsScalarTower.algebraMap_apply K Kl (Kl ⊗[K] Ω), AlgHom.commutes,
    IsScalarTower.algebraMap_apply Kl K' (K' ⊗[Kl] (Kl ⊗[K] Ω)), ← IsScalarTower.algebraMap_apply K Kl K']

theorem tmul_eq (a : K') (ω : Ω) : a ⊗ₜ[Kl] ((1 : Kl) ⊗ₜ[K] ω) =
    algebraMap K' (K' ⊗[Kl] (Kl ⊗[K] Ω)) a * incl K Kl K' ω := by
  rw [incl_apply, Algebra.TensorProduct.algebraMap_apply, Algebra.TensorProduct.tmul_mul_tmul]
  simp

theorem exists_lift_tensor {R : Type} [CommRing R] (a : K' →+* R) (ψ : Ω →+* R)
    (hc : ∀ c : K, ψ (algebraMap K Ω c) = a (algebraMap K K' c)) :
    ∃ f : K' ⊗[Kl] (Kl ⊗[K] Ω) →+* R, (∀ y, f (algebraMap K' _ y) = a y) ∧ ∀ ω, f (incl K Kl K' ω) = ψ ω := by
  letI : Algebra K' R := a.toAlgebra
  letI : Algebra Kl R := (a.comp (algebraMap Kl K')).toAlgebra
  letI : Algebra K R := (a.comp (algebraMap K K')).toAlgebra
  haveI : IsScalarTower Kl K' R := IsScalarTower.of_algebraMap_eq' rfl
  haveI : IsScalarTower K Kl R := IsScalarTower.of_algebraMap_eq fun c => by
    show a (algebraMap K K' c) = a (algebraMap Kl K' (algebraMap K Kl c))
    rw [← IsScalarTower.algebraMap_apply]
  let ε : Ω →ₐ[K] R := { ψ with commutes' := hc }
  let α₁ : Kl ⊗[K] Ω →ₐ[Kl] R :=
    Algebra.TensorProduct.lift (Algebra.ofId Kl _) ε fun _ _ => Commute.all _ _
  let α₀ : K' ⊗[Kl] (Kl ⊗[K] Ω) →ₐ[K'] R :=
    Algebra.TensorProduct.lift (Algebra.ofId K' _) α₁ fun _ _ => Commute.all _ _
  refine ⟨α₀.toRingHom, fun y => α₀.commutes y, fun ω => ?_⟩
  show α₀ _ = _
  rw [incl_apply, Algebra.TensorProduct.lift_tmul, Algebra.TensorProduct.lift_tmul, map_one, map_one, one_mul,
    one_mul]
  rfl

theorem exists_lift_quot {A R : Type} [CommRing A] [CommRing R] {D : ℕ} (s : Fin (D + 1) → A)
    (I : Ideal (Localization.Away (s 0)))
    (hI : I = Ideal.span (Set.range fun i : Fin D =>
      algebraMap A (Localization.Away (s 0)) (s i.succ) * IsLocalization.Away.invSelf (s 0)))
    (f : A →+* R) (h0 : IsUnit (f (s 0))) (h1 : ∀ i : Fin D, f (s i.succ) = 0) :
    ∃ g : (Localization.Away (s 0) ⧸ I) →+* R,
      ∀ z, g (Ideal.Quotient.mk I (algebraMap A (Localization.Away (s 0)) z)) = f z := by
  let g₀ : Localization.Away (s 0) →+* R := IsLocalization.Away.lift (s 0) h0
  have hg₀ : ∀ z, g₀ (algebraMap A _ z) = f z := fun z => IsLocalization.Away.lift_eq _ _ _
  have hJ : ∀ r ∈ I, g₀ r = 0 := by
    intro r hr
    have hle : I ≤ RingHom.ker g₀ := by
      rw [hI]
      refine Ideal.span_le.mpr ?_
      rintro _ ⟨i, rfl⟩
      rw [SetLike.mem_coe, RingHom.mem_ker, map_mul, hg₀, h1, zero_mul]
    exact hle hr
  exact ⟨Ideal.Quotient.lift I g₀ hJ, fun z => hg₀ z⟩

theorem mk_succ_eq_zero {A : Type} [CommRing A] {D : ℕ} (s : Fin (D + 1) → A)
    (I : Ideal (Localization.Away (s 0)))
    (hI : I = Ideal.span (Set.range fun i : Fin D =>
      algebraMap A (Localization.Away (s 0)) (s i.succ) * IsLocalization.Away.invSelf (s 0))) (i : Fin D) :
    Ideal.Quotient.mk I (algebraMap A (Localization.Away (s 0)) (s i.succ)) = 0 := by
  rw [Ideal.Quotient.eq_zero_iff_mem]
  have e : algebraMap A (Localization.Away (s 0)) (s i.succ) =
      (algebraMap A (Localization.Away (s 0)) (s i.succ) * IsLocalization.Away.invSelf (s 0)) *
        algebraMap A (Localization.Away (s 0)) (s 0) := by
    rw [mul_assoc, mul_comm (IsLocalization.Away.invSelf _), IsLocalization.Away.mul_invSelf, mul_one]
  rw [e, hI]
  exact Ideal.mul_mem_right _ _ (Ideal.subset_span ⟨i, rfl⟩)

end Univ

section Comp

variable {K Ω K' : Type} [Field K] [Field Ω] [Algebra K Ω] [Field K'] [Algebra K K'] {D N : ℕ}

theorem sHom_eq (j0 : Fin (N + 1)) (x : Fin N → Ω) (q : MvPolynomial (TVar D N) K) :
    sHom j0 x q = algebraMap (MvPolynomial (SVar D N) Ω) (OmS Ω D N) (aeval (polyImg j0 x) q) := by
  have : (sHom j0 x : MvPolynomial (TVar D N) K →ₐ[K] OmS Ω D N) =
      (IsScalarTower.toAlgHom K (MvPolynomial (SVar D N) Ω) (OmS Ω D N)).comp
        (aeval (polyImg j0 x)) := by
    refine MvPolynomial.algHom_ext fun p => ?_
    simp only [sHom, aeval_X, AlgHom.comp_apply, IsScalarTower.coe_toAlgHom']
    rfl
  rw [this]
  rfl

theorem polyImg_freeVar (j0 : Fin (N + 1)) (x : Fin N → Ω) (s : SVar D N) :
    polyImg j0 x (freeVar j0 s) = X s := by
  rcases s with ⟨⟨⟩⟩ | ⟨i, k⟩
  · show polyImg j0 x (0, j0) = _
    rw [polyImg_same, if_pos rfl]
  · exact polyImg_succAbove j0 x i k

theorem sum_polyImg (j0 : Fin (N + 1)) (v : Fin (N + 1) → Ω) (x : Fin N → Ω) (hv : v j0 ≠ 0)
    (hx : ∀ k, x k = v (j0.succAbove k) / v j0) (i : Fin (D + 1)) :
    ∑ j, polyImg j0 x (i, j) * C (v j) =
      C (v j0) * (polyImg j0 x (i, j0) + ∑ k, X (Sum.inr (i, k)) * C (x k)) := by
  rw [Fin.sum_univ_succAbove _ j0, mul_add, Finset.mul_sum, mul_comm]
  congr 1
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [polyImg_succAbove, mul_left_comm, ← C_mul, hx, mul_div_cancel₀ _ hv]

theorem sum_polyImg_succ (j0 : Fin (N + 1)) (v : Fin (N + 1) → Ω) (x : Fin N → Ω) (hv : v j0 ≠ 0)
    (hx : ∀ k, x k = v (j0.succAbove k) / v j0) (i : Fin D) :
    ∑ j, polyImg j0 x (i.succ, j) * C (v j) = 0 := by
  rw [sum_polyImg j0 v x hv hx, polyImg_same, if_neg (Fin.succ_ne_zero i), neg_add_cancel, mul_zero]

theorem sum_polyImg_zero (j0 : Fin (N + 1)) (v : Fin (N + 1) → Ω) (x : Fin N → Ω) (hv : v j0 ≠ 0)
    (hx : ∀ k, x k = v (j0.succAbove k) / v j0) :
    ∑ j, polyImg (D := D) j0 x (0, j) * C (v j) ≠ 0 := by
  rw [sum_polyImg j0 v x hv hx, polyImg_same, if_pos rfl]
  intro h
  have := congrArg (eval (Sum.elim (fun _ => (1 : Ω)) (fun _ => 0))) h
  simp [hv] at this

theorem exists_dvd_of_algebraic {P F S L : Type} [CommRing P] [IsDomain P] [Field F] [Algebra P F]
    [IsFractionRing P F] [CommRing S] [IsDomain S] [Field L] [Algebra F L] [FiniteDimensional F L]
    (φ : P →+* S) (i : S →+* L) (hi : Function.Injective i)
    (h : ∀ q, algebraMap F L (algebraMap P F q) = i (φ q)) (f : S) (hf : f ≠ 0) :
    ∃ q : P, q ≠ 0 ∧ f ∣ φ q := by
  letI : Algebra P S := φ.toAlgebra
  letI : Algebra S L := i.toAlgebra
  letI : Algebra P L := (i.comp φ).toAlgebra
  haveI : IsScalarTower P F L := IsScalarTower.of_algebraMap_eq fun q => (h q).symm
  haveI : IsScalarTower P S L := IsScalarTower.of_algebraMap_eq fun q => rfl
  have h1 : IsAlgebraic F (algebraMap S L f) := Algebra.IsAlgebraic.isAlgebraic _
  have h2 := (IsFractionRing.isAlgebraic_iff P F L).2 h1
  have h3 := (isAlgebraic_algebraMap_iff hi).1 h2
  exact h3.exists_nonzero_dvd (mem_nonZeroDivisors_of_ne_zero hf)

theorem exists_dvd (j0 : Fin (N + 1)) (x : Fin N → Ω)
    [Algebra (FractionRing (MvPolynomial (TVar D N) K)) (OmS Ω D N)]
    [FiniteDimensional (FractionRing (MvPolynomial (TVar D N) K)) (OmS Ω D N)]
    (hL : ∀ q : MvPolynomial (TVar D N) K, algebraMap (FractionRing (MvPolynomial (TVar D N) K)) (OmS Ω D N) (algebraMap (MvPolynomial (TVar D N) K) _ q) = sHom j0 x q)
    (f : MvPolynomial (SVar D N) Ω) (hf : f ≠ 0) :
    ∃ q : MvPolynomial (TVar D N) K, q ≠ 0 ∧ f ∣ aeval (polyImg j0 x) q := by
  exact exists_dvd_of_algebraic (F := FractionRing (MvPolynomial (TVar D N) K)) (L := OmS Ω D N)
    (aeval (R := K) (polyImg (D := D) j0 x)).toRingHom (algebraMap _ _) (IsFractionRing.injective _ _)
    (fun q => (hL q).trans (sHom_eq j0 x q)) f hf

theorem exists_maps (j0 : Fin (N + 1)) (v : Fin (N + 1) → Ω) (x : Fin N → Ω) (hv : v j0 ≠ 0)
    (hx : ∀ k, x k = v (j0.succAbove k) / v j0) (t : TVar D N → K') (ht : AlgebraicIndependent K t)
    [Algebra (FractionRing (MvPolynomial (TVar D N) K)) (OmS Ω D N)]
    [FiniteDimensional (FractionRing (MvPolynomial (TVar D N) K)) (OmS Ω D N)]
    (hL : ∀ q : MvPolynomial (TVar D N) K, algebraMap (FractionRing (MvPolynomial (TVar D N) K)) (OmS Ω D N) (algebraMap (MvPolynomial (TVar D N) K) _ q) = sHom j0 x q)
    [Algebra (FractionRing (MvPolynomial (TVar D N) K)) K']
    (hK : ∀ q : MvPolynomial (TVar D N) K, algebraMap (FractionRing (MvPolynomial (TVar D N) K)) K' (algebraMap (MvPolynomial (TVar D N) K) _ q) = aeval t q)
    {Q : Type} [CommRing Q] (a : K' →+* Q) (ψ : Ω →+* Q)
    (hc : ∀ c : K, ψ (algebraMap K Ω c) = a (algebraMap K K' c))
    (hrel : ∀ i : Fin D, ∑ j, a (t (i.succ, j)) * ψ (v j) = 0)
    (huniv : ∀ (R : Type) [CommRing R] (a' : K' →+* R) (ψ' : Ω →+* R),
      (∀ c : K, ψ' (algebraMap K Ω c) = a' (algebraMap K K' c)) → IsUnit (∑ j, a' (t (0, j)) * ψ' (v j)) →
      (∀ i : Fin D, ∑ j, a' (t (i.succ, j)) * ψ' (v j) = 0) →
      ∃ g : Q →+* R, (∀ y, g (a y) = a' y) ∧ ∀ ω, g (ψ ω) = ψ' ω) :
    ∃ β : OmS Ω D N →+* Q, (∀ q : MvPolynomial (TVar D N) K, β (sHom j0 x q) = a (aeval t q)) ∧ (∀ ω, β (algebraMap Ω _ ω) = ψ ω) ∧
      ∃ α : Q →+* K' ⊗[FractionRing (MvPolynomial (TVar D N) K)] OmS Ω D N,
        (∀ y, α (a y) = algebraMap K' _ y) ∧ Function.Surjective α := by
  let β₀ : MvPolynomial (SVar D N) Ω →+* Q := eval₂Hom ψ fun s => a (t (freeVar j0 s))
  have hX : ∀ s, β₀ (X s) = a (t (freeVar j0 s)) := fun s => eval₂Hom_X' _ _ _
  have hC : ∀ ω, β₀ (C ω) = ψ ω := fun ω => eval₂Hom_C _ _ _
  have hp : ∀ p, β₀ (polyImg j0 x p) = a (t p) := by
    rintro ⟨i, j⟩
    rcases Fin.eq_self_or_eq_succAbove j0 j with rfl | ⟨k, rfl⟩
    · refine Fin.cases ?_ (fun i => ?_) i
      · rw [polyImg_same, if_pos rfl, hX]; rfl
      · have h1 := congrArg β₀ (sum_polyImg_succ j v x hv hx i)
        have h2 := hrel i
        rw [map_sum, map_zero, Fin.sum_univ_succAbove _ j] at h1
        rw [Fin.sum_univ_succAbove _ j] at h2
        simp only [map_mul, hC, polyImg_succAbove, hX] at h1
        have h3 : β₀ (polyImg j x (i.succ, j)) * ψ (v j) = a (t (i.succ, j)) * ψ (v j) :=
          add_right_cancel (h1.trans h2.symm)
        exact ((isUnit_iff_ne_zero.2 hv).map ψ).mul_right_cancel h3
    · rw [polyImg_succAbove, hX]; rfl
  have hq : ∀ q : MvPolynomial (TVar D N) K, β₀ (aeval (polyImg j0 x) q) = a (aeval t q) := by
    intro q
    induction q using MvPolynomial.induction_on with
    | C c => rw [aeval_C, aeval_C, MvPolynomial.algebraMap_apply, hC, hc]
    | add p q hp hq => simp only [map_add, hp, hq]
    | mul_X q n hq => simp only [map_mul, aeval_X, hq, hp]
  have hunit : ∀ y : nonZeroDivisors (MvPolynomial (SVar D N) Ω), IsUnit (β₀ y) := by
    intro y
    obtain ⟨q, hq0, hd⟩ := exists_dvd j0 x hL y.1 (nonZeroDivisors.ne_zero y.2)
    have h1 := map_dvd β₀ hd
    rw [hq] at h1
    refine isUnit_of_dvd_unit h1 ((isUnit_iff_ne_zero.2 fun h => hq0 ?_).map a)
    exact algebraicIndependent_iff.mp ht q h
  let β : OmS Ω D N →+* Q := IsLocalization.lift hunit
  have hβ : ∀ f, β (algebraMap (MvPolynomial (SVar D N) Ω) _ f) = β₀ f := fun f => IsLocalization.lift_eq _ _
  have hΩ : ∀ ω : Ω, algebraMap Ω (OmS Ω D N) ω = algebraMap (MvPolynomial (SVar D N) Ω) _ (C ω) := fun ω =>
    IsScalarTower.algebraMap_apply Ω (MvPolynomial (SVar D N) Ω) _ ω
  refine ⟨β, fun q => by rw [sHom_eq, hβ, hq], fun ω => by rw [hΩ, hβ, hC], ?_⟩
  let iR : OmS Ω D N →+* K' ⊗[FractionRing (MvPolynomial (TVar D N) K)] OmS Ω D N :=
    (Algebra.TensorProduct.includeRight :
      OmS Ω D N →ₐ[FractionRing (MvPolynomial (TVar D N) K)] _).toRingHom
  have hT : ∀ q : MvPolynomial (TVar D N) K,
      algebraMap K' (K' ⊗[FractionRing (MvPolynomial (TVar D N) K)] OmS Ω D N) (aeval t q) = iR (sHom j0 x q) := by
    intro q
    rw [← hL, ← hK, ← IsScalarTower.algebraMap_apply]
    exact (AlgHom.commutes _ _).symm
  have hTX : ∀ p, algebraMap K' (K' ⊗[FractionRing (MvPolynomial (TVar D N) K)] OmS Ω D N) (t p) =
      iR (algebraMap (MvPolynomial (SVar D N) Ω) _ (polyImg j0 x p)) := by
    intro p
    have := hT (X p)
    rwa [sHom_eq, aeval_X, aeval_X] at this
  have hsum : ∀ i, ∑ j, algebraMap K' (K' ⊗[FractionRing (MvPolynomial (TVar D N) K)] OmS Ω D N) (t (i, j)) *
      (iR.comp (algebraMap Ω _)) (v j) =
      iR (algebraMap (MvPolynomial (SVar D N) Ω) _ (∑ j, polyImg j0 x (i, j) * C (v j))) := by
    intro i
    rw [map_sum, map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hTX, RingHom.comp_apply, hΩ, map_mul, map_mul]
  obtain ⟨α, hα1, hα2⟩ := huniv _ (algebraMap K' _) (iR.comp (algebraMap Ω _))
    (fun c => by
      have := hT (C c)
      rw [aeval_C, sHom, aeval_C, IsScalarTower.algebraMap_apply K Ω (OmS Ω D N)] at this
      exact this.symm)
    (by
      rw [hsum]
      refine (isUnit_iff_ne_zero.2 ?_).map iR
      rw [Ne, map_eq_zero_iff _ (IsFractionRing.injective _ _)]
      exact sum_polyImg_zero j0 v x hv hx)
    (fun i => by rw [hsum, sum_polyImg_succ j0 v x hv hx, map_zero, map_zero])
  refine ⟨α, hα1, ?_⟩
  have hαβ : α.comp β = iR := by
    refine IsLocalization.ringHom_ext (nonZeroDivisors (MvPolynomial (SVar D N) Ω)) ?_
    refine MvPolynomial.ringHom_ext (fun ω => ?_) (fun s => ?_)
    · simp only [RingHom.comp_apply]
      rw [hβ, hC, hα2, RingHom.comp_apply, hΩ]
    · simp only [RingHom.comp_apply]
      rw [hβ, hX, hα1, hTX, polyImg_freeVar]
  intro z
  induction z using TensorProduct.induction_on with
  | zero => exact ⟨0, map_zero _⟩
  | add y z hy hz =>
    obtain ⟨y, rfl⟩ := hy
    obtain ⟨z, rfl⟩ := hz
    exact ⟨y + z, map_add _ _ _⟩
  | tmul b y =>
    refine ⟨a b * β y, ?_⟩
    rw [map_mul, hα1, ← RingHom.comp_apply α β, hαβ, Algebra.TensorProduct.algebraMap_apply]
    show (_ ⊗ₜ _) * ((1 : K') ⊗ₜ y) = _
    rw [Algebra.TensorProduct.tmul_mul_tmul]
    simp

end Comp

section All

variable {K K' : Type} [Field K] [Field K'] [Algebra K K'] {D N : ℕ} {ι : Type} [Fintype ι]
  {Ω : ι → Type} [∀ Z, Field (Ω Z)] [∀ Z, Algebra K (Ω Z)]

set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 1000000 in

theorem basis_descends (j0 : ι → Fin (N + 1)) (v : ∀ Z, Fin (N + 1) → Ω Z) (x : ∀ Z, Fin N → Ω Z)
    (hv : ∀ Z, v Z (j0 Z) ≠ 0) (hx : ∀ Z k, x Z k = v Z ((j0 Z).succAbove k) / v Z (j0 Z))
    (hind : ∀ Z, AlgebraicIndependent K (sImg (D := D) (j0 Z) (x Z)))
    (hfin : ∀ Z, FiniteDimensional (IntermediateField.adjoin K (Set.range (sImg (D := D) (j0 Z) (x Z))))
      (OmS (Ω Z) D N))
    (t : TVar D N → K') (ht : AlgebraicIndependent K t)
    {Q : ι → Type} [∀ Z, CommRing (Q Z)] (a : ∀ Z, K' →+* Q Z) (ψ : ∀ Z, Ω Z →+* Q Z)
    (hc : ∀ Z (c : K), ψ Z (algebraMap K (Ω Z) c) = a Z (algebraMap K K' c))
    (hrel : ∀ Z (i : Fin D), ∑ j, a Z (t (i.succ, j)) * ψ Z (v Z j) = 0)
    (huniv : ∀ Z (R : Type) [CommRing R] (a' : K' →+* R) (ψ' : Ω Z →+* R),
      (∀ c : K, ψ' (algebraMap K (Ω Z) c) = a' (algebraMap K K' c)) → IsUnit (∑ j, a' (t (0, j)) * ψ' (v Z j)) →
      (∀ i : Fin D, ∑ j, a' (t (i.succ, j)) * ψ' (v Z j) = 0) →
      ∃ g : Q Z →+* R, (∀ y, g (a Z y) = a' y) ∧ ∀ ω, g (ψ Z ω) = ψ' ω)
    {n : ℕ} (θ : Fin n → ∀ Z, Ω Z)
    (hli : ∀ c : Fin n → K', (∀ Z, ∑ k, a Z (c k) * ψ Z (θ k Z) = 0) → ∀ k, c k = 0)
    (hsp : ∀ y : ∀ Z, Q Z, ∃ c : Fin n → K', ∀ Z, y Z = ∑ k, a Z (c k) * ψ Z (θ k Z)) :
    ∑ Z, Module.finrank (IntermediateField.adjoin K (Set.range (sImg (D := D) (j0 Z) (x Z)))) (OmS (Ω Z) D N) = n ∧
    (∀ p : Fin n → MvPolynomial (TVar D N) K,
      (∀ Z, ∑ k, sHom (j0 Z) (x Z) (p k) * algebraMap (Ω Z) (OmS (Ω Z) D N) (θ k Z) = 0) → ∀ k, p k = 0) ∧
    (∀ y : ∀ Z, OmS (Ω Z) D N, ∃ q : MvPolynomial (TVar D N) K, (∀ Z, sHom (j0 Z) (x Z) q ≠ 0) ∧
      ∃ p : Fin n → MvPolynomial (TVar D N) K, ∀ Z, sHom (j0 Z) (x Z) q * y Z =
        ∑ k, sHom (j0 Z) (x Z) (p k) * algebraMap (Ω Z) (OmS (Ω Z) D N) (θ k Z)) := by
  classical
  letI iL : ∀ Z, Algebra (FractionRing (MvPolynomial (TVar D N) K)) (OmS (Ω Z) D N) := fun Z =>
    ((algebraMap (IntermediateField.adjoin K (Set.range (sImg (D := D) (j0 Z) (x Z)))) (OmS (Ω Z) D N)).comp
      (hind Z).aevalEquivField.toRingEquiv.toRingHom).toAlgebra
  have hL : ∀ Z (q : MvPolynomial (TVar D N) K), algebraMap (FractionRing (MvPolynomial (TVar D N) K))
      (OmS (Ω Z) D N) (algebraMap (MvPolynomial (TVar D N) K) _ q) = sHom (j0 Z) (x Z) q := fun Z q =>
    (hind Z).aevalEquivField_algebraMap_apply_coe q
  have hrk : ∀ Z, Module.finrank (FractionRing (MvPolynomial (TVar D N) K)) (OmS (Ω Z) D N) =
      Module.finrank (IntermediateField.adjoin K (Set.range (sImg (D := D) (j0 Z) (x Z)))) (OmS (Ω Z) D N) :=
    fun Z => Algebra.finrank_eq_of_equiv_equiv (hind Z).aevalEquivField.toRingEquiv (RingEquiv.refl _) rfl
  haveI hfd : ∀ Z, FiniteDimensional (FractionRing (MvPolynomial (TVar D N) K)) (OmS (Ω Z) D N) := fun Z => by
    apply Module.finite_of_finrank_pos
    rw [hrk]
    exact Module.finrank_pos
  have hinjt : Function.Injective (aeval t : MvPolynomial (TVar D N) K →ₐ[K] K').toRingHom := ht
  letI iK : Algebra (FractionRing (MvPolynomial (TVar D N) K)) K' :=
    (IsFractionRing.lift (K := FractionRing (MvPolynomial (TVar D N) K)) hinjt).toAlgebra
  have hK : ∀ q : MvPolynomial (TVar D N) K, algebraMap (FractionRing (MvPolynomial (TVar D N) K)) K'
      (algebraMap (MvPolynomial (TVar D N) K) _ q) = aeval t q := fun q => IsFractionRing.lift_algebraMap hinjt q
  choose β hβ1 hβ2 α hα1 hα2 using fun Z => exists_maps (j0 Z) (v Z) (x Z) (hv Z) (hx Z) t ht (hL Z) hK (a Z) (ψ Z)
    (hc Z) (hrel Z) (huniv Z)
  have hβF : ∀ Z (y : FractionRing (MvPolynomial (TVar D N) K)), β Z (algebraMap _ _ y) = a Z (algebraMap _ _ y) := by
    intro Z
    have : (β Z).comp (algebraMap (FractionRing (MvPolynomial (TVar D N) K)) _) = (a Z).comp (algebraMap _ _) := by
      refine IsLocalization.ringHom_ext (nonZeroDivisors (MvPolynomial (TVar D N) K)) (RingHom.ext fun q => ?_)
      simp only [RingHom.comp_apply]
      rw [hL, hK, hβ1]
    exact fun y => RingHom.congr_fun this y
  let u : Fin n → ∀ Z, OmS (Ω Z) D N := fun k Z => algebraMap (Ω Z) _ (θ k Z)
  have hu : LinearIndependent (FractionRing (MvPolynomial (TVar D N) K)) u := by
    rw [Fintype.linearIndependent_iff]
    intro g hg k
    have := hli (fun k => algebraMap _ K' (g k)) (fun Z => by
      have h1 := congrArg (β Z) (congrFun hg Z)
      rw [Finset.sum_apply, map_sum, Pi.zero_apply, map_zero] at h1
      rw [← h1]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [Pi.smul_apply, Algebra.smul_def, map_mul, hβF, hβ2]) k
    exact (map_eq_zero_iff _ (algebraMap _ K').injective).1 this
  have hpi : Module.finrank (FractionRing (MvPolynomial (TVar D N) K)) (∀ Z, OmS (Ω Z) D N) =
      ∑ Z, Module.finrank (FractionRing (MvPolynomial (TVar D N) K)) (OmS (Ω Z) D N) :=
    Module.finrank_pi_fintype _
  have hle : n ≤ Module.finrank (FractionRing (MvPolynomial (TVar D N) K)) (∀ Z, OmS (Ω Z) D N) := by
    simpa using hu.fintype_card_le_finrank
  have hge : Module.finrank (FractionRing (MvPolynomial (TVar D N) K)) (∀ Z, OmS (Ω Z) D N) ≤ n := by
    let u' : Fin n → ∀ Z, K' ⊗[FractionRing (MvPolynomial (TVar D N) K)] OmS (Ω Z) D N :=
      fun k Z => α Z (ψ Z (θ k Z))
    have hs : Submodule.span K' (Set.range u') = ⊤ := by
      rw [eq_top_iff]
      intro z _
      choose y hy using fun Z => hα2 Z (z Z)
      obtain ⟨c, hc⟩ := hsp y
      rw [Submodule.mem_span_range_iff_exists_fun]
      refine ⟨c, funext fun Z => ?_⟩
      rw [← hy, hc, map_sum, Finset.sum_apply]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [Pi.smul_apply, Algebra.smul_def, map_mul, hα1]
    have h1 := finrank_le_of_span_eq_top hs
    rw [Module.finrank_pi_fintype, Fintype.card_fin] at h1
    rw [hpi]
    refine le_trans (le_of_eq (Finset.sum_congr rfl fun Z _ => ?_)) h1
    rw [Module.finrank_baseChange]
  have heq := le_antisymm hge hle
  have hinj : ∀ Z (q : MvPolynomial (TVar D N) K), sHom (j0 Z) (x Z) q = 0 → q = 0 := fun Z q h =>
    algebraicIndependent_iff.mp (hind Z) q h
  refine ⟨?_, fun p hp k => ?_, fun y => ?_⟩
  · rw [← heq, hpi]
    exact Finset.sum_congr rfl fun Z _ => (hrk Z).symm
  · have := Fintype.linearIndependent_iff.1 hu (fun k => algebraMap _ _ (p k)) (funext fun Z => by
      rw [Finset.sum_apply, Pi.zero_apply, ← hp Z]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [Pi.smul_apply, Algebra.smul_def, hL]) k
    exact (map_eq_zero_iff _ (IsFractionRing.injective _ _)).1 this
  · have hs := hu.span_eq_top_of_card_eq_finrank' (by rw [heq, Fintype.card_fin])
    have hy : y ∈ Submodule.span (FractionRing (MvPolynomial (TVar D N) K)) (Set.range u) := hs ▸ Submodule.mem_top
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun _).1 hy
    obtain ⟨q, hq⟩ := IsLocalization.exist_integer_multiples_of_finite
      (nonZeroDivisors (MvPolynomial (TVar D N) K)) c
    choose p hp using hq
    refine ⟨q, fun Z h => nonZeroDivisors.ne_zero q.2 (hinj Z _ h), p, fun Z => ?_⟩
    rw [← hc, Finset.sum_apply, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Pi.smul_apply, Algebra.smul_def, ← hL, ← hL, hp, Algebra.smul_def, map_mul, mul_assoc]

end All

section Loc

theorem coords_of_equiv {K' M ι : Type} [Field K'] [AddCommGroup M] [Module K' M] {Q : ι → Type}
    [∀ Z, CommRing (Q Z)] (a : ∀ Z, K' →+* Q Z) {n : ℕ} (b : Fin n → M) (hli : LinearIndependent K' b)
    (hsp : Submodule.span K' (Set.range b) = ⊤)
    (E : letI : ∀ Z, Module K' (Q Z) := fun Z => (a Z).toModule; M ≃ₗ[K'] ∀ Z, Q Z) :
    (∀ c : Fin n → K', (∀ Z, ∑ k, a Z (c k) * E (b k) Z = 0) → ∀ k, c k = 0) ∧
    ∀ y : ∀ Z, Q Z, ∃ c : Fin n → K', ∀ Z, y Z = ∑ k, a Z (c k) * E (b k) Z := by
  letI : ∀ Z, Module K' (Q Z) := fun Z => (a Z).toModule
  have key : ∀ (c : Fin n → K') Z, E (∑ k, c k • b k) Z = ∑ k, a Z (c k) * E (b k) Z := by
    intro c Z
    rw [map_sum, Finset.sum_apply]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_smul]
    rfl
  refine ⟨fun c hc => Fintype.linearIndependent_iff.1 hli c ?_, fun y => ?_⟩
  · apply E.injective
    rw [map_zero]
    exact funext fun Z => (key c Z).trans (hc Z)
  · have hy : E.symm y ∈ Submodule.span K' (Set.range b) := hsp ▸ Submodule.mem_top
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun _).1 hy
    exact ⟨c, fun Z => by rw [← key, hc, LinearEquiv.apply_symm_apply]⟩

variable {K Kl K' : Type} [Field K] [Field Kl] [Field K'] [Algebra K Kl] [Algebra Kl K'] [Algebra K K']
  [IsScalarTower K Kl K'] {ι : Type} [Fintype ι] {Ω : ι → Type} [∀ Z, Field (Ω Z)] [∀ Z, Algebra K (Ω Z)]

set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 1000000 in

theorem basis_descends_loc {D D' N m n : ℕ} (hD : D = D') (e : Fin m ≃ Fin (N + 1)) (j0 : ι → Fin (N + 1))
    (v : ∀ Z, Fin m → Ω Z) (x : ∀ Z, Fin N → Ω Z)
    (hv : ∀ Z, v Z (e.symm (j0 Z)) ≠ 0)
    (hx : ∀ Z k, x Z k = v Z (e.symm ((j0 Z).succAbove k)) / v Z (e.symm (j0 Z)))
    (hind : ∀ Z, AlgebraicIndependent K (sImg (D := D) (j0 Z) (x Z)))
    (hfin : ∀ Z, FiniteDimensional (IntermediateField.adjoin K (Set.range (sImg (D := D) (j0 Z) (x Z))))
      (OmS (Ω Z) D N))
    (t : Fin (D' + 1) × Fin m → K') (ht : AlgebraicIndependent K t)
    (s : ∀ Z, Fin (D' + 1) → K' ⊗[Kl] (Kl ⊗[K] Ω Z))
    (hs : ∀ Z i, s Z i = ∑ k, t (i, k) ⊗ₜ[Kl] ((1 : Kl) ⊗ₜ[K] v Z k))
    (I : ∀ Z, Ideal (Localization.Away (s Z 0)))
    (hI : ∀ Z, I Z = Ideal.span (Set.range fun i : Fin D' =>
      algebraMap _ (Localization.Away (s Z 0)) (s Z i.succ) * IsLocalization.Away.invSelf (s Z 0)))
    (a : ∀ Z, K' →+* Localization.Away (s Z 0) ⧸ I Z)
    (ha : ∀ Z y, a Z y = Ideal.Quotient.mk (I Z) (algebraMap K' (Localization.Away (s Z 0)) y))
    (θ : Fin n → ∀ Z, Ω Z) (g : ∀ Z, Ω Z) (hg : ∀ Z, g Z ≠ 0)
    (w : Fin n → ∀ Z, Localization.Away (s Z 0) ⧸ I Z)
    (hw : ∀ k Z, w k Z * Ideal.Quotient.mk (I Z) (algebraMap (K' ⊗[Kl] (Kl ⊗[K] Ω Z)) (Localization.Away (s Z 0))
        ((1 : K') ⊗ₜ[Kl] ((1 : Kl) ⊗ₜ[K] g Z))) =
      Ideal.Quotient.mk (I Z) (algebraMap (K' ⊗[Kl] (Kl ⊗[K] Ω Z)) (Localization.Away (s Z 0))
        ((1 : K') ⊗ₜ[Kl] ((1 : Kl) ⊗ₜ[K] θ k Z))))
    (hli : ∀ c : Fin n → K', (∀ Z, ∑ k, a Z (c k) * w k Z = 0) → ∀ k, c k = 0)
    (hsp : ∀ y : ∀ Z, Localization.Away (s Z 0) ⧸ I Z, ∃ c : Fin n → K', ∀ Z, y Z = ∑ k, a Z (c k) * w k Z) :
    ∑ Z, Module.finrank (IntermediateField.adjoin K (Set.range (sImg (D := D) (j0 Z) (x Z)))) (OmS (Ω Z) D N) = n ∧
    (∀ p : Fin n → MvPolynomial (TVar D N) K,
      (∀ Z, ∑ k, sHom (j0 Z) (x Z) (p k) * algebraMap (Ω Z) (OmS (Ω Z) D N) (θ k Z / g Z) = 0) → ∀ k, p k = 0) ∧
    (∀ y : ∀ Z, OmS (Ω Z) D N, ∃ q : MvPolynomial (TVar D N) K, (∀ Z, sHom (j0 Z) (x Z) q ≠ 0) ∧
      ∃ p : Fin n → MvPolynomial (TVar D N) K, ∀ Z, sHom (j0 Z) (x Z) q * y Z =
        ∑ k, sHom (j0 Z) (x Z) (p k) * algebraMap (Ω Z) (OmS (Ω Z) D N) (θ k Z / g Z)) := by
  subst hD
  let π : ∀ Z, K' ⊗[Kl] (Kl ⊗[K] Ω Z) →+* Localization.Away (s Z 0) ⧸ I Z := fun Z =>
    (Ideal.Quotient.mk (I Z)).comp (algebraMap _ _)
  let ψ : ∀ Z, Ω Z →+* Localization.Away (s Z 0) ⧸ I Z := fun Z => (π Z).comp (incl K Kl K')
  have ha' : ∀ Z y, a Z y = π Z (algebraMap K' _ y) := fun Z y => by
    rw [ha, IsScalarTower.algebraMap_apply K' (K' ⊗[Kl] (Kl ⊗[K] Ω Z)) (Localization.Away (s Z 0))]
    rfl
  have hwψ : ∀ k Z, w k Z = ψ Z (θ k Z / g Z) := by
    intro k Z
    have h1 : w k Z * ψ Z (g Z) = ψ Z (θ k Z) := hw k Z
    refine ((isUnit_iff_ne_zero.2 (hg Z)).map (ψ Z)).mul_right_cancel ?_
    rw [h1, ← map_mul, div_mul_cancel₀ _ (hg Z)]
  let ε : TVar D N ≃ Fin (D + 1) × Fin m := (Equiv.refl _).prodCongr e.symm
  have hs' : ∀ Z i, s Z i = ∑ j, algebraMap K' _ ((t ∘ ε) (i, j)) * incl K Kl K' (v Z (e.symm j)) := by
    intro Z i
    rw [hs, ← e.symm.sum_comp]
    exact Finset.sum_congr rfl fun j _ => tmul_eq _ _
  have hf : ∀ Z {R : Type} [CommRing R] (f : K' ⊗[Kl] (Kl ⊗[K] Ω Z) →+* R) (a' : K' →+* R) (ψ' : Ω Z →+* R),
      (∀ y, f (algebraMap K' _ y) = a' y) → (∀ ω, f (incl K Kl K' ω) = ψ' ω) → ∀ i,
      f (s Z i) = ∑ j, a' ((t ∘ ε) (i, j)) * ψ' (v Z (e.symm j)) := by
    intro Z R _ f a' ψ' h1 h2 i
    rw [hs', map_sum]
    exact Finset.sum_congr rfl fun j _ => by rw [map_mul, h1, h2]
  refine basis_descends j0 (fun Z j => v Z (e.symm j)) x hv hx hind hfin (t ∘ ε)
    ((algebraicIndependent_equiv ε).2 ht) a ψ (fun Z c => ?_) (fun Z i => ?_) (fun Z R _ a' ψ' hc h0 h1 => ?_)
    (fun k Z => θ k Z / g Z) (fun c hc => hli c fun Z => ?_) (fun y => ?_)
  · rw [ha', ← incl_algebraMap]; rfl
  · rw [← hf Z (π Z) (a Z) (ψ Z) (fun y => (ha' Z y).symm) (fun _ => rfl)]
    exact mk_succ_eq_zero (s Z) (I Z) (hI Z) i
  · obtain ⟨f, hf1, hf2⟩ := exists_lift_tensor (Kl := Kl) a' ψ' hc
    obtain ⟨G, hG⟩ := exists_lift_quot (s Z) (I Z) (hI Z) f (by rw [hf Z f a' ψ' hf1 hf2]; exact h0)
      (fun i => by rw [hf Z f a' ψ' hf1 hf2]; exact h1 i)
    exact ⟨G, fun y => by rw [ha']; exact (hG _).trans (hf1 y), fun ω => (hG _).trans (hf2 ω)⟩
  · simp only [hwψ]; exact hc Z
  · obtain ⟨c, hc⟩ := hsp y
    exact ⟨c, fun Z => by rw [hc]; simp only [hwψ]⟩

end Loc

end GlobalTheory.SectionBasis
