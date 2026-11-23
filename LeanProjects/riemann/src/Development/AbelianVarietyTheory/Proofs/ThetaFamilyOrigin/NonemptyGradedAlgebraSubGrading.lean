import Mathlib
import ReciprocityTheory.CommutativeAlgebra.PolynomialHeights.HeightAddRingKrullDimQuotientMvPolynomialField

namespace GlobalTheory.TorsionZero

open MvPolynomial

section Forms

variable {K σ : Type} [Field K]

theorem aeval_mul_of_isHomogeneous {S : Type} [CommRing S] [Algebra K S] (a : σ → S) (w : S)
    {G : MvPolynomial σ K} {n : ℕ} (hG : G.IsHomogeneous n) :
    aeval (fun j => a j * w) G = aeval a G * w ^ n := by
  conv_lhs => rw [G.as_sum]
  conv_rhs => rw [G.as_sum]
  rw [map_sum, map_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun m hm => ?_
  have hmn : m.degree = n := by
    by_contra hne
    exact (mem_support_iff.mp hm) (hG.coeff_eq_zero hne)
  rw [aeval_monomial, aeval_monomial, ← hmn]
  simp only [Finsupp.prod, mul_pow, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum,
    mul_assoc, Finsupp.degree_apply]

theorem exists_homogenisation (F : MvPolynomial σ K) (i : σ) :
    ∃ (n : ℕ) (G : MvPolynomial σ K), G.IsHomogeneous n ∧
      ∀ (S : Type) [CommRing S] [Algebra K S] (a : σ → S), a i = 1 → aeval a G = aeval a F := by
  refine ⟨F.totalDegree, ∑ n ∈ Finset.range (F.totalDegree + 1),
    homogeneousComponent n F * X i ^ (F.totalDegree - n), ?_, fun S _ _ a ha => ?_⟩
  · refine IsHomogeneous.sum _ _ _ fun n hn => ?_
    have hn' := Finset.mem_range.mp hn
    have h1 := (homogeneousComponent_isHomogeneous n F).mul
      ((isHomogeneous_X K i).pow (F.totalDegree - n))
    have h2 : n + 1 * (F.totalDegree - n) = F.totalDegree := by omega
    rwa [h2] at h1
  · conv_rhs => rw [← sum_homogeneousComponent F]
    simp [map_sum, ha]

theorem aeval_mem_of_isHomogeneous {R : Type} [CommRing R] [Algebra K R] (𝒜 : ℕ → Submodule K R)
    [SetLike.GradedMonoid 𝒜] {N : ℕ} {x : σ → R} (hx : ∀ j, x j ∈ 𝒜 N)
    {G : MvPolynomial σ K} {n : ℕ} (hG : G.IsHomogeneous n) : aeval x G ∈ 𝒜 (N * n) := by
  rw [G.as_sum, map_sum]
  refine Submodule.sum_mem _ fun m hm => ?_
  have hmn : m.degree = n := by
    by_contra hne
    exact (mem_support_iff.mp hm) (hG.coeff_eq_zero hne)
  rw [aeval_monomial, ← Algebra.smul_def]
  refine Submodule.smul_mem _ _ ?_
  have h := SetLike.prod_pow_mem_graded 𝒜 (F := m.support) (fun _ => N) x m (fun j _ => hx j)
  rw [← hmn, Finsupp.degree_apply, Finset.mul_sum]
  simpa [Finsupp.prod, mul_comm] using h

theorem aeval_eq_zero_iff_components {R : Type} [CommRing R] [Algebra K R] (𝒜 : ℕ → Submodule K R)
    [GradedAlgebra 𝒜] {x : σ → R} (hx : ∀ j, x j ∈ 𝒜 1) (G : MvPolynomial σ K) :
    aeval x G = 0 ↔ ∀ n, aeval x (homogeneousComponent n G) = 0 := by
  have hm : ∀ n, aeval x (homogeneousComponent n G) ∈ 𝒜 n := fun n => by
    simpa using aeval_mem_of_isHomogeneous 𝒜 hx (homogeneousComponent_isHomogeneous n G)
  constructor
  · intro h n
    by_cases hn : n ∈ Finset.range (G.totalDegree + 1)
    · rw [← sum_homogeneousComponent G, map_sum] at h
      have h2 := congrArg (GradedRing.proj 𝒜 n) h
      rw [map_sum, map_zero, Finset.sum_eq_single n] at h2
      · rwa [GradedRing.proj_apply, DirectSum.decompose_of_mem_same 𝒜 (hm n)] at h2
      · intro b _ hb
        rw [GradedRing.proj_apply, DirectSum.decompose_of_mem_ne 𝒜 (hm b) hb]
      · exact fun h' => absurd hn h'
    · rw [homogeneousComponent_eq_zero _ _ (by simpa using hn), map_zero]
  · intro h
    rw [← sum_homogeneousComponent G, map_sum]
    exact Finset.sum_eq_zero fun n _ => h n

theorem aeval_cone_eq_zero_iff {C : Type} [CommRing C] [Algebra K C] (r : σ → C)
    (G : MvPolynomial σ K) :
    aeval (fun j => Polynomial.C (r j) * Polynomial.X) G = 0 ↔
      ∀ n, aeval r (homogeneousComponent n G) = 0 := by
  have hm : ∀ n, aeval (fun j => Polynomial.C (r j) * Polynomial.X) (homogeneousComponent n G) =
      Polynomial.C (aeval r (homogeneousComponent n G)) * Polynomial.X ^ n := fun n => by
    rw [aeval_mul_of_isHomogeneous _ _ (homogeneousComponent_isHomogeneous n G)]
    congr 1
    exact (comp_aeval_apply r (Polynomial.CAlgHom (R := K) (A := C)) _).symm
  constructor
  · intro h n
    by_cases hn : n ∈ Finset.range (G.totalDegree + 1)
    · rw [← sum_homogeneousComponent G, map_sum] at h
      have h2 := congrArg (fun p => Polynomial.coeff p n) h
      simp only [Polynomial.finset_sum_coeff, hm, Polynomial.coeff_C_mul_X_pow, Polynomial.coeff_zero] at h2
      rw [Finset.sum_eq_single n] at h2
      · simpa using h2
      · intro b _ hb
        rw [if_neg (Ne.symm hb)]
      · exact fun h' => absurd hn h'
    · rw [homogeneousComponent_eq_zero _ _ (by simpa using hn), map_zero]
  · intro h
    rw [← sum_homogeneousComponent G, map_sum]
    exact Finset.sum_eq_zero fun n _ => by rw [hm, h, map_zero, zero_mul]

theorem trdeg_eq_of_isAlgebraic {A : Type} [CommRing A] [IsDomain A] [Algebra K A]
    (B : Subalgebra K A) [Algebra.IsAlgebraic B A] : Algebra.trdeg K A = Algebra.trdeg K B := by
  haveI : FaithfulSMul K B := (faithfulSMul_iff_algebraMap_injective _ _).2 (algebraMap K B).injective
  rw [← trdeg_add_eq K B (A := A), trdeg_eq_zero (R := B) (A := A), add_zero]

theorem ringKrullDim_cone {T C : Type} [CommRing T] [IsDomain T] [Algebra K T]
    [Algebra.FiniteType K T] (𝒜 : ℕ → Submodule K T) [GradedAlgebra 𝒜] [Finite σ] {x : σ → T}
    (hx : ∀ j, x j ∈ 𝒜 1) [Algebra.IsIntegral (Algebra.adjoin K (Set.range x)) T]
    [CommRing C] [IsDomain C] [Algebra K C] (r : σ → C) (i : σ) (hi : r i = 1)
    (hr : Function.Surjective (aeval r : MvPolynomial σ K →ₐ[K] C))
    (hrel : ∀ n (G : MvPolynomial σ K), G.IsHomogeneous n → (aeval x G = 0 ↔ aeval r G = 0))
    (g : ℕ) (hg : ringKrullDim C = g) : ringKrullDim T = (g + 1 : ℕ) := by
  haveI : Algebra.FiniteType K C := Algebra.FiniteType.of_surjective _ hr
  obtain ⟨s, hs, hs'⟩ := ReciprocityTheory.CA.exists_dim_trdeg_field (K := K) (A := C)
  obtain rfl : s = g := by
    rw [hs] at hg
    exact_mod_cast hg
  refine ReciprocityTheory.CA.ringKrullDim_eq_of_trdeg_eq_field (K := K) _ ?_
  set cone : MvPolynomial σ K →ₐ[K] Polynomial C :=
    aeval (fun j => Polynomial.C (r j) * Polynomial.X) with hcone
  have hker : RingHom.ker (aeval x : MvPolynomial σ K →ₐ[K] T) = RingHom.ker cone := by
    ext G
    rw [RingHom.mem_ker, RingHom.mem_ker, aeval_eq_zero_iff_components 𝒜 hx, hcone,
      aeval_cone_eq_zero_iff]
    exact forall_congr' fun n => hrel n _ (homogeneousComponent_isHomogeneous n G)
  have e : (aeval x : MvPolynomial σ K →ₐ[K] T).range ≃ₐ[K] cone.range :=
    (Ideal.quotientKerEquivRange _).symm.trans
      ((Ideal.quotientEquivAlgOfEq K hker).trans (Ideal.quotientKerEquivRange _))
  have hX : Polynomial.X ∈ cone.range := ⟨X i, by simp [hcone, hi]⟩
  have key : ∀ p : Polynomial C, ∃ n : ℕ, Polynomial.X ^ n * p ∈ cone.range := by
    intro p
    induction p using Polynomial.induction_on' with
    | add p q hp hq =>
      obtain ⟨a, ha⟩ := hp
      obtain ⟨b, hb⟩ := hq
      refine ⟨a + b, ?_⟩
      have : Polynomial.X ^ (a + b) * (p + q) =
          Polynomial.X ^ b * (Polynomial.X ^ a * p) + Polynomial.X ^ a * (Polynomial.X ^ b * q) := by
        ring
      rw [this]
      exact add_mem (mul_mem (pow_mem hX _) ha) (mul_mem (pow_mem hX _) hb)
    | monomial d c =>
      obtain ⟨F, rfl⟩ := hr c
      obtain ⟨n, G, hG, hF⟩ := exists_homogenisation F i
      refine ⟨n, ?_⟩
      have h1 : cone G = Polynomial.C (aeval r F) * Polynomial.X ^ n := by
        rw [hcone, aeval_mul_of_isHomogeneous _ _ hG, ← hF C r hi]
        congr 1
        exact (comp_aeval_apply r (Polynomial.CAlgHom (R := K) (A := C)) _).symm
      have : Polynomial.X ^ n * Polynomial.monomial d (aeval r F) = cone G * Polynomial.X ^ d := by
        rw [h1, ← Polynomial.C_mul_X_pow_eq_monomial]; ring
      rw [this]
      exact mul_mem ⟨G, rfl⟩ (pow_mem hX _)
  haveI : Algebra.IsAlgebraic cone.range (Polynomial C) := ⟨fun p => by
    obtain ⟨n, hn⟩ := key p
    refine IsAlgebraic.of_smul (y := (⟨Polynomial.X ^ n, pow_mem hX n⟩ : cone.range))
      (mem_nonZeroDivisors_of_ne_zero fun h => ?_) ?_
    · exact pow_ne_zero n Polynomial.X_ne_zero (congrArg Subtype.val h)
    · exact isAlgebraic_algebraMap (⟨_, hn⟩ : cone.range)⟩
  rw [trdeg_eq_of_isAlgebraic (Algebra.adjoin K (Set.range x)), Algebra.adjoin_range_eq_range_aeval,
    e.trdeg_eq, ← trdeg_eq_of_isAlgebraic cone.range, ← trdeg_add_eq K C (A := Polynomial C), hs',
    Polynomial.trdeg_of_isDomain]
  simp

end Forms

section Core

variable {K R : Type} [Field K] [CommRing R] [Algebra K R]

def subGrading (𝒜 : ℕ → Submodule K R) (N : ℕ) (T : Subalgebra K R) (e : ℕ) : Submodule K T :=
  (𝒜 (N * e)).comap T.val.toLinearMap

theorem mem_subGrading {𝒜 : ℕ → Submodule K R} {N : ℕ} {T : Subalgebra K R} {e : ℕ} {y : T} :
    y ∈ subGrading 𝒜 N T e ↔ (y : R) ∈ 𝒜 (N * e) := Iff.rfl

theorem nonempty_gradedAlgebra_subGrading (𝒜 : ℕ → Submodule K R) [GradedAlgebra 𝒜] {N : ℕ}
    (hN : 1 ≤ N) (S : Set R) (hS : ∀ y ∈ S, ∃ e, y ∈ 𝒜 (N * e)) :
    Nonempty (GradedAlgebra (subGrading 𝒜 N (Algebra.adjoin K S))) := by
  classical
  set T := Algebra.adjoin K S with hT
  haveI gm : SetLike.GradedMonoid (subGrading 𝒜 N T) :=
    { one_mem := by
        rw [mem_subGrading]
        simpa using SetLike.one_mem_graded 𝒜
      mul_mem := fun i j a b ha hb => by
        rw [mem_subGrading] at ha hb ⊢
        simpa [mul_add] using SetLike.mul_mem_graded ha hb }
  have hind : iSupIndep (subGrading 𝒜 N T) := by
    have h0 : iSupIndep 𝒜 := (DirectSum.Decomposition.isInternal 𝒜).submodule_iSupIndep
    have h1 : iSupIndep (fun e => 𝒜 (N * e)) :=
      h0.comp (f := fun e => N * e) fun a b h => Nat.eq_of_mul_eq_mul_left hN h
    intro e
    rw [Submodule.disjoint_def]
    intro y hy hy'
    refine Subtype.ext ((Submodule.disjoint_def.1 (h1 e)) _ hy ?_)
    have : (⨆ j, ⨆ (_ : j ≠ e), subGrading 𝒜 N T j) ≤
        (⨆ j, ⨆ (_ : j ≠ e), 𝒜 (N * j)).comap T.val.toLinearMap :=
      iSup₂_le fun j hj => Submodule.comap_mono (le_iSup₂ (f := fun j (_ : j ≠ e) => 𝒜 (N * j)) j hj)
    exact this hy'
  have htop : ⨆ e, subGrading 𝒜 N T e = ⊤ := by
    rw [eq_top_iff]
    rintro ⟨y, hy⟩ -
    induction hy using Algebra.adjoin_induction with
    | mem y hy =>
      obtain ⟨e, he⟩ := hS y hy
      exact Submodule.mem_iSup_of_mem e he
    | algebraMap r =>
      refine Submodule.mem_iSup_of_mem 0 ?_
      rw [mem_subGrading]
      simpa using SetLike.algebraMap_mem_graded 𝒜 r
    | add a b ha hb h1 h2 => exact add_mem h1 h2
    | mul a b ha hb h1 h2 =>
      change (⟨a, ha⟩ : T) * ⟨b, hb⟩ ∈ _
      generalize (⟨a, ha⟩ : T) = u at h1
      generalize (⟨b, hb⟩ : T) = v at h2
      induction h1 using Submodule.iSup_induction' with
      | mem i u hu =>
        induction h2 using Submodule.iSup_induction' with
        | mem j v hv => exact Submodule.mem_iSup_of_mem (i + j) (SetLike.mul_mem_graded hu hv)
        | zero => simp
        | add v w _ _ hv hw => rw [mul_add]; exact add_mem hv hw
      | zero => simp
      | add v w _ _ hv hw => rw [add_mul]; exact add_mem hv hw
  exact ⟨{ gm, ((DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top _).2
    ⟨hind, htop⟩).chooseDecomposition with }⟩

theorem map_eq_pow_mul {σ : Type} {x : σ → R} {φ ψ : R →ₐ[K] K} {c : K}
    (h : ∀ j, φ (x j) = ψ (x j) * c) {i : σ} (hi : φ (x i) ≠ 0) {y : R} {e n : ℕ}
    {G : MvPolynomial σ K} (hG : G.IsHomogeneous (n + e)) (hy : y * x i ^ n = aeval x G) :
    φ y = c ^ e * ψ y := by
  have h1 := congrArg φ hy
  have h2 := congrArg ψ hy
  rw [map_mul, map_pow, comp_aeval_apply] at h1 h2
  rw [show (fun j => φ (x j)) = fun j => ψ (x j) * c from funext h,
    aeval_mul_of_isHomogeneous _ _ hG, ← h2] at h1
  refine mul_right_cancel₀ (pow_ne_zero n hi) ?_
  rw [h1, h i]
  ring

theorem card_zeros_le [IsAlgClosed K] [IsDomain R] (𝒜 : ℕ → Submodule K R) [GradedAlgebra 𝒜]
    (hInt : ∀ (T : Type) [CommRing T] [IsDomain T] [Algebra K T] (𝒜 : ℕ → Submodule K T) [GradedAlgebra 𝒜] (m : ℕ) (x : Fin m → T), (∀ i, x i ∈ 𝒜 1) → (∃ i, x i ≠ 0) → ∀ (d : ℕ), ∀ s ∈ 𝒜 d, (∀ i, ∃ n : ℕ, s * x i ^ n ∈ Algebra.adjoin K (Set.range x)) → IsIntegral (Algebra.adjoin K (Set.range x)) s)
    (hBez : ∀ (T : Type) [CommRing T] [IsDomain T] [Algebra K T] (𝒜 : ℕ → Submodule K T) [GradedAlgebra 𝒜] (m g N d a : ℕ) (x : Fin m → T) (s : T) (F : Set T), 1 ≤ g → (∀ i, x i ∈ 𝒜 1) → Module.Finite (Algebra.adjoin K (Set.range x)) T → ringKrullDim T = (g + 1 : ℕ) → (∀ e, 1 ≤ e → Module.finrank K (𝒜 e) ≤ (N * e) ^ g) → s ∈ 𝒜 d → s ≠ 0 → (∀ f ∈ F, f ∈ 𝒜 a) → (∃ Φ : Set (T →ₐ[K] K), Φ.Finite ∧ ∀ φ : T →ₐ[K] K, (∃ i, φ (x i) ≠ 0) → (∀ f ∈ F, φ f = 0) → ∃ ψ ∈ Φ, (∃ c : K, ∀ (e : ℕ), ∀ y ∈ 𝒜 e, φ y = c ^ e * ψ y)) → ∀ (n : ℕ) (φ : Fin n → (T →ₐ[K] K)), (∀ j, ∃ i, φ j (x i) ≠ 0) → (∀ j, φ j s = 0 ∧ ∀ f ∈ F, φ j f = 0) → (∀ j j', (∃ c : K, ∀ (e : ℕ), ∀ y ∈ 𝒜 e, φ j' y = c ^ e * φ j y) → j = j') → n ≤ N ^ g * g.factorial * d * a ^ (g - 1))
    {m g N d a : ℕ} (hg : 1 ≤ g) (hN : 1 ≤ N) (x : Fin m → R) (hx : ∀ j, x j ∈ 𝒜 N)
    (hform : ∀ e, ∀ y ∈ 𝒜 (N * e), ∀ i, ∃ (n : ℕ) (G : MvPolynomial (Fin m) K),
      G.IsHomogeneous (n + e) ∧ y * x i ^ n = aeval x G)
    {C : Type} [CommRing C] [IsDomain C] [Algebra K C] (r : Fin m → C) (i₀ : Fin m) (hi₀ : r i₀ = 1)
    (hx₀ : x i₀ ≠ 0)
    (hr : Function.Surjective (aeval r : MvPolynomial (Fin m) K →ₐ[K] C))
    (hrel : ∀ n (G : MvPolynomial (Fin m) K), G.IsHomogeneous n → (aeval x G = 0 ↔ aeval r G = 0))
    (hC : ringKrullDim C = g)
    (hfin : ∀ e, 1 ≤ e → Module.Finite K (𝒜 (N * e)) ∧ Module.finrank K (𝒜 (N * e)) ≤ (N * e) ^ g)
    (s : R) (hs : s ∈ 𝒜 (N * d)) (hs0 : s ≠ 0) {ι : Type} [Finite ι] (f : ι → R)
    (hf : ∀ j, f j ∈ 𝒜 (N * a)) {Pt : Type} (ev : Pt → (R →ₐ[K] K))
    (hcov : ∀ p, ∃ i, ev p (x i) ≠ 0)
    (hpt : ∀ (v : Fin m → K) (i : Fin m), v i = 1 →
      (∀ n (G : MvPolynomial (Fin m) K), G.IsHomogeneous n → aeval x G = 0 → aeval v G = 0) →
      ∃ p, ev p (x i) ≠ 0 ∧ ∀ j, ev p (x j) = v j * ev p (x i))
    (hsep : ∀ p q (c : K), (∀ j, ev p (x j) = c * ev q (x j)) → p = q)
    (Z : Set Pt) (hZ : Z.Finite) (hZf : ∀ p, p ∈ Z ↔ ∀ j, ev p (f j) = 0) :
    Nat.card {p : Pt // p ∈ Z ∧ ev p s = 0} ≤ N ^ g * g.factorial * d * a ^ (g - 1) := by
  classical
  let S : Set R := Set.range x ∪ ({s} ∪ Set.range f)
  have hS : ∀ y ∈ S, ∃ e, y ∈ 𝒜 (N * e) := by
    rintro y (⟨j, rfl⟩ | rfl | ⟨j, rfl⟩)
    · exact ⟨1, by simpa using hx j⟩
    · exact ⟨d, hs⟩
    · exact ⟨a, hf j⟩
  have hSfin : S.Finite := (Set.finite_range x).union ((Set.finite_singleton s).union (Set.finite_range f))
  obtain ⟨inst⟩ := nonempty_gradedAlgebra_subGrading 𝒜 hN S hS
  set T := Algebra.adjoin K S with hT
  set ℬ := subGrading 𝒜 N T with hℬ
  let x' : Fin m → T := fun j => ⟨x j, Algebra.subset_adjoin (Or.inl ⟨j, rfl⟩)⟩
  let s' : T := ⟨s, Algebra.subset_adjoin (Or.inr (Or.inl rfl))⟩
  let f' : ι → T := fun j => ⟨f j, Algebra.subset_adjoin (Or.inr (Or.inr ⟨j, rfl⟩))⟩
  have hx' : ∀ j, x' j ∈ ℬ 1 := fun j => by
    rw [hℬ, mem_subGrading]
    simpa using hx j
  have hval : ∀ G : MvPolynomial (Fin m) K, ((aeval x' G : T) : R) = aeval x G := fun G =>
    comp_aeval_apply x' T.val G
  have hform' : ∀ e, ∀ y ∈ ℬ e, ∀ i, ∃ (n : ℕ) (G : MvPolynomial (Fin m) K),
      G.IsHomogeneous (n + e) ∧ y * x' i ^ n = aeval x' G := fun e y hy i => by
    obtain ⟨n, G, hG, h⟩ := hform e y hy i
    exact ⟨n, G, hG, Subtype.ext (by rw [hval, ← h]; rfl)⟩
  haveI : Algebra.FiniteType K T := Algebra.FiniteType.adjoin_of_finite hSfin
  haveI : Algebra.IsIntegral (Algebra.adjoin K (Set.range x')) T := ⟨fun y => by
    induction y using DirectSum.Decomposition.inductionOn ℬ with
    | zero => exact isIntegral_zero
    | @homogeneous e y =>
      refine hInt T ℬ m x' hx' ⟨i₀, fun h => hx₀ (congrArg Subtype.val h)⟩ e y y.2 fun i => ?_
      obtain ⟨n, G, -, h⟩ := hform' e y y.2 i
      refine ⟨n, ?_⟩
      rw [h, Algebra.adjoin_range_eq_range_aeval]
      exact ⟨G, rfl⟩
    | add a b ha hb => exact ha.add hb⟩
  haveI : Algebra.FiniteType (Algebra.adjoin K (Set.range x')) T :=
    Algebra.FiniteType.of_restrictScalars_finiteType K _ _
  have hdim : ringKrullDim T = (g + 1 : ℕ) :=
    ringKrullDim_cone ℬ hx' r i₀ hi₀ hr (fun n G hG => by
      rw [← hrel n G hG, ← hval]
      exact ⟨fun h => by rw [h]; rfl, fun h => Subtype.ext h⟩) g hC
  haveI : Finite {p : Pt // p ∈ Z ∧ ev p s = 0} :=
    (hZ.subset (fun p hp => hp.1 : {p | p ∈ Z ∧ ev p s = 0} ⊆ Z)).to_subtype
  let E := (Finite.equivFin {p : Pt // p ∈ Z ∧ ev p s = 0}).symm
  refine hBez T ℬ m g N d a x' s' (Set.range f') hg hx' Algebra.IsIntegral.finite hdim
    (fun e he => ?_) hs (fun h => hs0 (congrArg Subtype.val h)) ?_
    ⟨(fun p => (ev p).comp T.val) '' Z, hZ.image _, fun φ hφ hφf => ?_⟩ _
    (fun j => (ev (E j).1).comp T.val) (fun j => hcov _) (fun j => ⟨(E j).2.2, ?_⟩) ?_
  · obtain ⟨h1, h2⟩ := hfin e he
    refine le_trans ?_ h2
    refine LinearMap.finrank_le_finrank_of_injective
      (f := T.val.toLinearMap.restrict (p := ℬ e) (q := 𝒜 (N * e)) fun y hy => hy) fun y z h => ?_
    have h3 := congrArg Subtype.val h
    exact Subtype.ext (Subtype.ext h3)
  · rintro _ ⟨j, rfl⟩
    exact hf j
  · obtain ⟨i, hi⟩ := hφ
    obtain ⟨p, hp, hp'⟩ := hpt (fun j => φ (x' j) * (φ (x' i))⁻¹) i (mul_inv_cancel₀ hi)
      fun n G hG h => by
        have h0 : aeval x' G = 0 := Subtype.ext (by rw [hval, h]; rfl)
        rw [aeval_mul_of_isHomogeneous _ _ hG, ← comp_aeval_apply, h0, map_zero, zero_mul]
    have hc : ∀ e, ∀ y ∈ ℬ e, φ y = (φ (x' i) * (ev p (x i))⁻¹) ^ e * (ev p).comp T.val y :=
      fun e y hy => by
        obtain ⟨n, G, hG, h⟩ := hform' e y hy i
        refine map_eq_pow_mul (fun j => ?_) hi hG h
        change _ = ev p (x j) * _
        rw [hp' j]
        field_simp
    refine ⟨_, ⟨p, (hZf p).2 fun j => ?_, rfl⟩, _, hc⟩
    have h1 := hc a (f' j) (hf j)
    rw [hφf _ ⟨j, rfl⟩] at h1
    exact (mul_eq_zero.1 h1.symm).resolve_left (pow_ne_zero _ (mul_ne_zero hi (inv_ne_zero hp)))
  · rintro _ ⟨l, rfl⟩
    exact (hZf _).1 (E j).2.1 l
  · rintro j j' ⟨c, hc⟩
    refine E.injective (Subtype.ext (hsep _ _ c fun l => ?_).symm)
    simpa using hc 1 _ (hx' l)

end Core

end GlobalTheory.TorsionZero
