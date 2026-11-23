import Mathlib
import ReciprocityTheory.CommutativeAlgebra.PolynomialHeights.HeightAddRingKrullDimQuotientMvPolynomialField
import ReciprocityTheory.AnalyticForms.RegularLocalRings.IntToRat
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.TrdegAdjoin

open MvPolynomial Algebra Cardinal

attribute [local instance] MvPolynomial.algebraMvPolynomial

noncomputable section

section Field

variable {R L : Type} [Field R] [CommRing L] [IsDomain L] [Algebra R L]

omit [IsDomain L] in

theorem isAlgebraic_adjoin_range_iff (A : Subalgebra R L) {κ : Type} (x : κ → A) (a : A) :
    IsAlgebraic (adjoin R (Set.range (A.val ∘ x))) (a : L) ↔
      IsAlgebraic (adjoin R (Set.range x)) a := by
  have hmap : (adjoin R (Set.range x)).map A.val = adjoin R (Set.range (A.val ∘ x)) := by
    rw [AlgHom.map_adjoin, Set.range_comp]
  let e : adjoin R (Set.range x) ≃ₐ[R] adjoin R (Set.range (A.val ∘ x)) :=
    (Subalgebra.equivMapOfInjective _ A.val Subtype.val_injective).trans
      (Subalgebra.equivOfEq _ _ hmap)
  exact isAlgebraic_ringHom_iff_of_comp_eq e.toRingEquiv A.val Subtype.val_injective
    (RingHom.ext fun _ ↦ rfl)

theorem trdeg_adjoin_eq {s : Set L} {κ : Type} {b : κ → L} (hb : ∀ i, b i ∈ adjoin R s)
    (hind : AlgebraicIndependent R b)
    (halg : ∀ z ∈ s, IsAlgebraic (adjoin R (Set.range b)) z) :
    Algebra.trdeg R (adjoin R s) = #κ := by
  set A := adjoin R s
  let b' : κ → A := fun i ↦ ⟨b i, hb i⟩
  have hind' : AlgebraicIndependent R b' := AlgebraicIndependent.of_comp A.val hind
  have halg' : Algebra.IsAlgebraic (adjoin R (Set.range b')) A := by
    refine ⟨fun a ↦ ?_⟩
    rw [← isAlgebraic_adjoin_range_iff A b' a]
    have hcomp : A.val ∘ b' = b := rfl
    rw [hcomp]
    exact IsAlgebraic.adjoin_of_forall_isAlgebraic (s := s) (fun z hz ↦ halg z hz.1)
      (isAlgebraic_algebraMap (R := A) a)
  exact ((hind'.isTranscendenceBasis_iff_isAlgebraic).mpr halg').cardinalMk_eq_trdeg.symm

theorem trdeg_adjoin_eq_add_one {Y Z : Set L} {e : L} (hYZ : Y ⊆ Z) (heZ : e ∈ Z)
    (he : Transcendental (adjoin R Y) e)
    (halg : ∀ z ∈ Z, IsAlgebraic (adjoin R (insert e Y)) z)
    {s : ℕ} (hs : Algebra.trdeg R (adjoin R Y) = s) :
    Algebra.trdeg R (adjoin R Z) = s + 1 := by
  set A := adjoin R Y
  have : FaithfulSMul R A :=
    (faithfulSMul_iff_algebraMap_injective R A).mpr (algebraMap R A).injective
  obtain ⟨κ, x, hx⟩ := exists_isTranscendenceBasis' R A
  have hκ : #κ = s := hx.cardinalMk_eq_trdeg.trans hs
  set b₀ : κ → L := A.val ∘ x with hb₀def
  have hb₀ : AlgebraicIndependent R b₀ := hx.1.map' Subtype.val_injective
  have hb₀A : ∀ i, b₀ i ∈ A := fun i ↦ (x i).2
  have hle : adjoin R (Set.range b₀) ≤ A := adjoin_le (Set.range_subset_iff.mpr hb₀A)
  have hY : ∀ y ∈ Y, IsAlgebraic (adjoin R (Set.range b₀)) y := by
    intro y hy
    have h1 := hx.isAlgebraic.isAlgebraic (⟨y, subset_adjoin hy⟩ : A)
    exact (isAlgebraic_adjoin_range_iff A x ⟨y, subset_adjoin hy⟩).mpr h1
  let b : Option κ → L := fun o ↦ o.elim e b₀
  have hind : AlgebraicIndependent R b :=
    AlgebraicIndependent.option_iff.mpr ⟨hb₀, fun h ↦ he (h.tower_top_of_subalgebra_le hle)⟩
  have hrange : Set.range b₀ ⊆ Set.range b := fun _ ⟨i, hi⟩ ↦ ⟨some i, hi⟩
  have heb : e ∈ Set.range b := ⟨none, rfl⟩
  have hleb : adjoin R (Set.range b₀) ≤ adjoin R (Set.range b) := adjoin_mono hrange
  have hmem : ∀ o, b o ∈ adjoin R Z := by
    rintro (_ | i)
    · exact subset_adjoin heZ
    · exact adjoin_mono hYZ (hb₀A i)
  have key := trdeg_adjoin_eq hmem hind fun z hz ↦ by
    refine IsAlgebraic.adjoin_of_forall_isAlgebraic (s := insert e Y) ?_ (halg z hz)
    rintro w ⟨hw, hwb⟩
    rcases hw with rfl | hw
    · exact absurd heb hwb
    · exact (hY w hw).tower_top_of_subalgebra_le hleb
  rw [key, Cardinal.mk_option, hκ]

end Field

section Dimension

variable {σ : Type} [Fintype σ] {L : Type} [CommRing L] [IsDomain L] [Algebra ℚ L]

omit [Fintype σ] [IsDomain L] in

theorem map_C_int (φ : MvPolynomial σ ℤ →+* L) (m : ℤ) : φ (C m) = algebraMap ℚ L m := by
  have h1 : φ (C m) = (m : L) := eq_intCast (φ.comp C) m
  rw [h1, map_intCast]

omit [Fintype σ] [IsDomain L] in

theorem map_mem_adjoin (φ : MvPolynomial σ ℤ →+* L) (g : MvPolynomial σ ℤ) :
    φ g ∈ adjoin ℚ (Set.range fun v ↦ φ (X v)) := by
  induction g using MvPolynomial.induction_on with
  | C a => rw [map_C_int]; exact Subalgebra.algebraMap_mem _ _
  | add p q hp hq => rw [map_add]; exact add_mem hp hq
  | mul_X p v hp => rw [map_mul]; exact mul_mem hp (subset_adjoin ⟨v, rfl⟩)

theorem ringKrullDim_quotient_ker (φ : MvPolynomial σ ℤ →+* L) :
    ∃ s : ℕ, Algebra.trdeg ℚ (adjoin ℚ (Set.range fun v ↦ φ (X v))) = s ∧
      ringKrullDim (MvPolynomial σ ℤ ⧸ RingHom.ker φ) = (s : WithBot ℕ∞) + 1 := by
  set P := RingHom.ker φ
  have hPp : P.IsPrime := RingHom.ker_isPrime φ
  have hP : ∀ m : ℤ, (C m : MvPolynomial σ ℤ) ∈ P → m = 0 := by
    intro m hm
    rw [RingHom.mem_ker, map_C_int] at hm
    exact_mod_cast (algebraMap ℚ L).injective (hm.trans (map_zero _).symm)
  obtain ⟨-, hcomap, hdim⟩ := ReciprocityTheory.AnForm.R.extQ_spec P hP
  set ψ : MvPolynomial σ ℚ →ₐ[ℚ] L := aeval fun v ↦ φ (X v)
  have hψ : (ψ : MvPolynomial σ ℚ →+* L).comp (MvPolynomial.map (Int.castRingHom ℚ)) = φ :=
    MvPolynomial.ringHom_ext (fun m ↦ by simp [ψ]) (fun v ↦ by simp [ψ])
  have hker : RingHom.ker ψ = ReciprocityTheory.AnForm.R.extQ P := by
    apply (IsLocalization.orderEmbedding (ReciprocityTheory.AnForm.R.IntegerToRational.intS σ) (MvPolynomial σ ℚ)).injective
    change (RingHom.ker (ψ : MvPolynomial σ ℚ →+* L)).comap (MvPolynomial.map (Int.castRingHom ℚ)) =
      (ReciprocityTheory.AnForm.R.extQ P).comap (MvPolynomial.map (Int.castRingHom ℚ))
    rw [RingHom.comap_ker, hψ]
    exact hcomap.symm
  have : (RingHom.ker ψ).IsPrime := RingHom.ker_isPrime ψ
  obtain ⟨s, hs1, hs2⟩ :=
    ReciprocityTheory.CA.exists_dim_trdeg_field (K := ℚ) (A := MvPolynomial σ ℚ ⧸ RingHom.ker ψ)
  refine ⟨s, ?_, ?_⟩
  · rw [← hs2]
    exact ((Ideal.quotientKerEquivRange ψ).trans (Subalgebra.equivOfEq _ _ (aeval_range _))).trdeg_eq.symm
  · rw [← hker] at hdim
    rw [← hdim, hs1]

end Dimension

section Constants

variable {M : Type} [CommRing M] [IsDomain M] [Algebra ℚ M]

omit [IsDomain M] in

theorem exists_C_of_mem_adjoin {s : Set (Polynomial M)} (hs : ∀ r ∈ s, ∃ a, r = Polynomial.C a)
    {r : Polynomial M} (hr : r ∈ adjoin ℚ s) : ∃ a, r = Polynomial.C a := by
  induction hr using Algebra.adjoin_induction with
  | mem x hx => exact hs x hx
  | algebraMap q => exact ⟨algebraMap ℚ M q, Polynomial.algebraMap_apply q⟩
  | add x y _ _ hx hy =>
    obtain ⟨a, rfl⟩ := hx
    obtain ⟨b, rfl⟩ := hy
    exact ⟨a + b, (Polynomial.C_add).symm⟩
  | mul x y _ _ hx hy =>
    obtain ⟨a, rfl⟩ := hx
    obtain ⟨b, rfl⟩ := hy
    exact ⟨a * b, (Polynomial.C_mul).symm⟩

theorem transcendental_C_mul_X (S : Subalgebra ℚ (Polynomial M))
    (hS : ∀ r ∈ S, ∃ a, r = Polynomial.C a) {m : M} (hm : m ≠ 0) :
    Transcendental S (Polynomial.C m * Polynomial.X) := by
  rw [transcendental_iff]
  intro p hp
  let κ : S →+* M := Polynomial.constantCoeff.comp (S.val : S →+* Polynomial M)
  have hκ : ∀ r : S, (r : Polynomial M) = Polynomial.C (κ r) := by
    intro r
    obtain ⟨a, ha⟩ := hS r r.2
    simp [κ, ha]
  have hinj : Function.Injective κ := by
    rw [injective_iff_map_eq_zero]
    intro r hr
    apply Subtype.ext
    rw [hκ r, hr, map_zero]
    rfl
  have halg : algebraMap S (Polynomial M) = Polynomial.C.comp κ := RingHom.ext fun r ↦ hκ r
  have h1 : Polynomial.aeval (Polynomial.C m * Polynomial.X) p =
      (p.map κ).comp (Polynomial.C m * Polynomial.X) := by
    rw [Polynomial.aeval_def, halg, ← Polynomial.eval₂_map]
    rfl
  rw [h1] at hp
  rcases Polynomial.comp_eq_zero_iff.mp hp with h | ⟨_, h⟩
  · exact Polynomial.map_injective κ hinj (by rw [h, Polynomial.map_zero])
  · exfalso
    have h2 := congrArg (fun q : Polynomial M ↦ q.coeff 1) h
    simp only [Polynomial.coeff_C_mul_X, Polynomial.coeff_C] at h2
    simp at h2
    exact hm h2

theorem optionEquivLeft_rename_some {K κ : Type} [CommRing K] (a : MvPolynomial κ K) :
    optionEquivLeft K κ (rename some a) = Polynomial.C a := by
  induction a using MvPolynomial.induction_on with
  | C k => rw [rename_C, optionEquivLeft_C]
  | add p q hp hq => rw [map_add, map_add, hp, hq, Polynomial.C_add]
  | mul_X p v hp => rw [map_mul, map_mul, hp, rename_X, optionEquivLeft_X_some, Polynomial.C_mul]

theorem transcendental_C_mul_X_none {K κ : Type} [Field K] [Algebra ℚ K]
    (S : Subalgebra ℚ (MvPolynomial (Option κ) K))
    (hS : ∀ r ∈ S, ∃ a, r = rename some a) {c : K} (hc : c ≠ 0) :
    Transcendental S (C c * X none : MvPolynomial (Option κ) K) := by
  let gℚ : MvPolynomial (Option κ) K →ₐ[ℚ] Polynomial (MvPolynomial κ K) :=
    ((optionEquivLeft K κ : MvPolynomial (Option κ) K →ₐ[K] Polynomial (MvPolynomial κ K))).restrictScalars ℚ
  have hg : Function.Injective gℚ := (optionEquivLeft K κ).injective
  let f : S ≃ₐ[ℚ] S.map gℚ := Subalgebra.equivMapOfInjective S gℚ hg
  refine (transcendental_ringHom_iff_of_comp_eq f.toRingEquiv gℚ hg (RingHom.ext fun _ ↦ rfl)).mp ?_
  have he : gℚ (C c * X none) = Polynomial.C (C c) * Polynomial.X := by
    simp [gℚ, optionEquivLeft_C, optionEquivLeft_X_none]
  rw [he]
  refine transcendental_C_mul_X (S.map gℚ) ?_ (by rwa [Ne, MvPolynomial.C_eq_zero])
  rintro _ ⟨r, hr, rfl⟩
  obtain ⟨a, rfl⟩ := hS r hr
  exact ⟨a, optionEquivLeft_rename_some a⟩

theorem exists_rename_of_mem_adjoin {K κ : Type} [CommRing K] [Algebra ℚ K]
    {s : Set (MvPolynomial (Option κ) K)} (hs : ∀ r ∈ s, ∃ a, r = rename some a)
    {r : MvPolynomial (Option κ) K} (hr : r ∈ adjoin ℚ s) : ∃ a, r = rename some a := by
  induction hr using Algebra.adjoin_induction with
  | mem x hx => exact hs x hx
  | algebraMap q => exact ⟨C (algebraMap ℚ K q), by rw [rename_C]; rfl⟩
  | add x y _ _ hx hy =>
    obtain ⟨a, rfl⟩ := hx
    obtain ⟨b, rfl⟩ := hy
    exact ⟨a + b, (map_add _ _ _).symm⟩
  | mul x y _ _ hx hy =>
    obtain ⟨a, rfl⟩ := hx
    obtain ⟨b, rfl⟩ := hy
    exact ⟨a * b, (map_mul _ _ _).symm⟩

end Constants

end

end GroundTheory.Heights₂.Heights.TrdegAdjoin
