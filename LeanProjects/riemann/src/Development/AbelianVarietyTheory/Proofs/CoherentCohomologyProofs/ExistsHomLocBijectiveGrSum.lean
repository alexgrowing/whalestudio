import Mathlib
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq
import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.ExistsAwayFracOfMemHomLoc
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.CubeTotalComplexAcyclicOfSlicesInductionOnCard

open CategoryTheory DirectSum MvPolynomial

noncomputable section

namespace GlobalTheory

open GradedHilbert

section

variable {ι : Type} {R : Type} [CommRing R]

theorem GrSum.X_smul_bijective {A : ℤ → Type} [∀ n, AddCommGroup (A n)] [∀ n, Module R (A n)]
    {x : ι → ∀ n, A n →ₗ[R] A (n + 1)} (hx : OperatorsCommute x) {i : ι}
    (h : ∀ t, Function.Bijective (x i t)) :
    Function.Bijective fun m : GrSum hx => (X i : MvPolynomial ι R) • m := by
  have hg := isGradedMap_lsmul (GrSum.grading hx) (X_mem_polyGrading (R := R) i)
  refine ⟨hg.injective_iff.2 fun n => ?_, hg.surjective_iff.2 fun n => ?_⟩
  · rintro ⟨_, a, rfl⟩ ⟨_, b, rfl⟩ e
    have e' : (X i : MvPolynomial ι R) • GrSum.of hx n a = (X i : MvPolynomial ι R) • GrSum.of hx n b :=
      congrArg Subtype.val e
    rw [GrSum.X_smul_of, GrSum.X_smul_of] at e'
    obtain rfl := (h n).1 (GrSum.of_injective hx _ e')
    rfl
  · rintro ⟨_, b, rfl⟩
    obtain ⟨a, rfl⟩ := (h n).2 b
    exact ⟨⟨_, a, rfl⟩, Subtype.ext (GrSum.X_smul_of hx i n a)⟩

theorem xProd_smul_bijective_of {N : Type} [AddCommGroup N] [Module (MvPolynomial ι R) N]
    (s : Finset ι) (h : ∀ i ∈ s, Function.Bijective fun m : N => (X i : MvPolynomial ι R) • m) :
    Function.Bijective fun m : N => xProd R s • m := by
  refine Finset.prod_induction _ (fun p : MvPolynomial ι R => Function.Bijective fun m : N => p • m)
    (fun p q hp hq => ?_) ?_ h
  · simp only [mul_smul]
    exact hp.comp hq
  · simp only [one_smul]
    exact Function.bijective_id

theorem exists_homLoc_bijective_of
    {M : Type} [AddCommGroup M] [Module R M] [Module (MvPolynomial ι R) M]
    [IsScalarTower R (MvPolynomial ι R) M]
    {N : Type} [AddCommGroup N] [Module R N] [Module (MvPolynomial ι R) N]
    [IsScalarTower R (MvPolynomial ι R) N]
    {ℳ : ℤ → Submodule R M} [PolyGradedSMul ι ℳ] [Decomposition ℳ]
    {𝒩 : ℤ → Submodule R N} [PolyGradedSMul ι 𝒩] [Decomposition 𝒩]
    {f : M →ₗ[MvPolynomial ι R] N} (hf : IsGradedMap ℳ 𝒩 f) (s : Finset ι)
    (hb : Function.Bijective fun m : N => xProd R s • m)
    (h₁ : ∀ n, ∀ y ∈ ℳ n, f y = 0 → ∃ k : ℕ, xProd R s ^ k • y = 0)
    (h₂ : ∀ n, ∀ a ∈ 𝒩 n, ∃ (k : ℕ) (y : M), f y = xProd R s ^ k • a) (n : ℤ) :
    ∃ φ : homLoc ℳ s n →ₗ[R] 𝒩 n, Function.Bijective φ ∧
      ∀ (z : homLoc ℳ s n) (k : ℕ) (m : M), awayFrac M (xProd R s) k m = z →
        xProd R s ^ k • (φ z : N) = f m := by
  let e := LinearEquiv.ofBijective _ (toHomLoc_bijective 𝒩 hb n)
  refine ⟨e.symm.toLinearMap ∘ₗ homLocMap hf s n, e.symm.bijective.comp ⟨?_, ?_⟩, ?_⟩
  · rw [injective_iff_map_eq_zero]
    rintro ⟨_, k, m, hm, rfl⟩ hz
    have hz' : awayMap _ f (awayFrac M (xProd R s) k m) = 0 := congrArg Subtype.val hz
    rw [awayMap_awayFrac, map_eq_zero_iff _ (awayFrac_injective hb.1 k)] at hz'
    exact Subtype.ext (awayFrac_eq_zero_iff.2 (h₁ _ m hm hz'))
  · refine homLocMap_surjective_of hf (fun y => ?_) n
    induction y using Decomposition.inductionOn 𝒩 with
    | zero => exact ⟨0, by simp⟩
    | @homogeneous d a =>
      obtain ⟨k, y, hy⟩ := h₂ d a a.2
      exact ⟨k, y, hy⟩
    | add a b ha hb =>
      obtain ⟨k, ha⟩ := ha
      obtain ⟨j, hb⟩ := hb
      refine ⟨k + j, ?_⟩
      rw [smul_add]
      refine add_mem ?_ ?_
      · rw [add_comm, pow_add, mul_smul]
        exact Submodule.smul_mem _ _ ha
      · rw [pow_add, mul_smul]
        exact Submodule.smul_mem _ _ hb
  · intro z k m hm
    have h : awayFrac N (xProd R s) 0 (e.symm (homLocMap hf s n z) : N) = awayMap _ f z :=
      congrArg Subtype.val (e.apply_symm_apply (homLocMap hf s n z))
    apply awayFrac_injective hb.1 0
    rw [map_smul]
    erw [h]
    rw [← hm, awayMap_awayFrac, pow_smul_awayFrac]

theorem exists_homLoc_bijective_grSum
    {M : Type} [AddCommGroup M] [Module R M] [Module (MvPolynomial ι R) M]
    [IsScalarTower R (MvPolynomial ι R) M]
    {ℳ : ℤ → Submodule R M} [PolyGradedSMul ι ℳ] [Decomposition ℳ]
    {A : ℤ → Type} [∀ n, AddCommGroup (A n)] [∀ n, Module R (A n)]
    {x : ι → ∀ n, A n →ₗ[R] A (n + 1)} (hx : OperatorsCommute x)
    {f : M →ₗ[MvPolynomial ι R] GrSum hx} (hf : IsGradedMap ℳ (GrSum.grading hx) f) (s : Finset ι)
    (hb : ∀ i ∈ s, ∀ t, Function.Bijective (x i t))
    (h₁ : ∀ n, ∀ y ∈ ℳ n, f y = 0 → ∃ k : ℕ, xProd R s ^ k • y = 0)
    (h₂ : ∀ n (a : A n), ∃ (k : ℕ) (y : M), f y = xProd R s ^ k • GrSum.of hx n a) (n : ℤ) :
    ∃ φ : homLoc ℳ s n →ₗ[R] A n, Function.Bijective φ ∧
      ∀ (z : homLoc ℳ s n) (k : ℕ) (m : M), awayFrac M (xProd R s) k m = z →
        xProd R s ^ k • GrSum.of hx n (φ z) = f m := by
  obtain ⟨ψ, hψ, hψ'⟩ := exists_homLoc_bijective_of hf s
    (xProd_smul_bijective_of s fun i hi => GrSum.X_smul_bijective hx (hb i hi)) h₁
    (by rintro n _ ⟨a, rfl⟩; exact h₂ n a) n
  refine ⟨(GrSum.pieceEquiv hx n).symm.toLinearMap ∘ₗ ψ,
    (GrSum.pieceEquiv hx n).symm.bijective.comp hψ, fun z k m e => ?_⟩
  rw [← hψ' z k m e]
  exact congrArg (fun w : GrSum.grading hx n => xProd R s ^ k • (w : GrSum hx))
    ((GrSum.pieceEquiv hx n).apply_symm_apply (ψ z))

theorem homLoc_grSum_res
    {M : Type} [AddCommGroup M] [Module R M] [Module (MvPolynomial ι R) M]
    [IsScalarTower R (MvPolynomial ι R) M]
    {ℳ : ℤ → Submodule R M} [PolyGradedSMul ι ℳ]
    {A : ℤ → Type} [∀ n, AddCommGroup (A n)] [∀ n, Module R (A n)]
    {x : ι → ∀ n, A n →ₗ[R] A (n + 1)} (hx : OperatorsCommute x)
    {B : ℤ → Type} [∀ n, AddCommGroup (B n)] [∀ n, Module R (B n)]
    {y : ι → ∀ n, B n →ₗ[R] B (n + 1)} (hy : OperatorsCommute y)
    (r : ∀ n, A n →ₗ[R] B n) (hr : ∀ i n a, r (n + 1) (x i n a) = y i n (r n a))
    {f : M →ₗ[MvPolynomial ι R] GrSum hx} (hf : IsGradedMap ℳ (GrSum.grading hx) f)
    {g : M →ₗ[MvPolynomial ι R] GrSum hy}
    (hfg : ∀ n m a, f m = GrSum.of hx n a → g m = GrSum.of hy n (r n a))
    {s t : Finset ι} (h : s ⊆ t) (hb : ∀ i ∈ t, ∀ n, Function.Bijective (y i n)) {n : ℤ}
    (z : homLoc ℳ s n) (a : A n) (b : B n)
    (ha : ∀ (k : ℕ) (m : M), awayFrac M (xProd R s) k m = z →
      xProd R s ^ k • GrSum.of hx n a = f m)
    (hb' : ∀ (k : ℕ) (m : M), awayFrac M (xProd R t) k m = homLocRes ℳ h n z →
      xProd R t ^ k • GrSum.of hy n b = g m) : b = r n a := by
  obtain ⟨k, m, hm, e⟩ := z.2
  obtain ⟨a', ha'⟩ := hf hm
  have h1 : g m = GrSum.map hx hy r hr (f m) := by
    rw [hfg _ m a' ha'.symm, ← ha', GrSum.map_of]
  obtain ⟨c, hc⟩ : ∃ c, xProd R t = c * xProd R s :=
    exists_eq_mul_left_of_dvd (Finset.prod_dvd_prod_of_subset s t X h)
  have h2 := hb' k (c ^ k • m) (by rw [coe_homLocRes, ← e, locRes_awayFrac X h hc])
  rw [map_smul, h1, ← ha k m e, map_smul, GrSum.map_of, ← mul_smul, ← mul_pow, ← hc] at h2
  have h3 := xProd_smul_bijective_of t fun i hi => GrSum.X_smul_bijective hy (hb i hi)
  exact GrSum.of_injective hy n (IsSMulRegular.pow k h3.1 h2)

end

theorem exists_grCube_hom_bijective (ι : Type) [LinearOrder ι] [Fintype ι] (R : Type) [CommRing R]
    (G : Type) [AddCommGroup G] [Module R G] [Module (MvPolynomial ι R) G]
    [IsScalarTower R (MvPolynomial ι R) G] (𝒢 : ℤ → Submodule R G) [PolyGradedSMul ι 𝒢]
    [Decomposition 𝒢] (A : ℤ → Cube.{0} ι R) (x : ι → ∀ t, A t ⟶ A (t + 1))
    (hx : ∀ I : Finset ι,
      OperatorsCommute (A := fun t => (A t).obj I) fun i t => ((x i t).app I).hom)
    (ρ : ∀ I : Finset ι, G →ₗ[MvPolynomial ι R] GrSum (hx I))
    (hρ : ∀ I, IsGradedMap 𝒢 (GrSum.grading (hx I)) (ρ I))
    (hres : ∀ (I J : Finset ι) (h : I ⊆ J) (n : ℤ) (y : G) (a : (A n).obj I),
      ρ I y = GrSum.of (hx I) n a → ρ J y = GrSum.of (hx J) n (Cube.res (A n) h a))
    (hbij : ∀ (I : Finset ι), ∀ i ∈ I, ∀ t, Function.Bijective ((x i t).app I).hom)
    (hker : ∀ (I : Finset ι) (n : ℤ), ∀ y ∈ 𝒢 n, ρ I y = 0 → ∃ k : ℕ, xProd R I ^ k • y = 0)
    (hcoker : ∀ (I : Finset ι) (t : ℤ) (a : (A t).obj I), ∃ (k : ℕ) (y : G),
      ρ I y = xProd R I ^ k • GrSum.of (hx I) t a) (t : ℤ) :
    ∃ φ : grCube ι 𝒢 t ⟶ A t, ∀ I, Function.Bijective (φ.app I).hom := by
  choose φ hφ hφ' using fun I =>
    exists_homLoc_bijective_grSum (hx I) (hρ I) I (hbij I) (hker I) (hcoker I) t
  refine ⟨Cube.homMk (A := grCube ι 𝒢 t) φ fun {I J} h z => ?_, hφ⟩
  exact homLoc_grSum_res (hx I) (hx J) (fun n => Cube.res (A n) h)
    (fun i n a => (Cube.app_res (x i n) h a).symm) (hρ I) (hres I J h) h (hbij J) z _ _
    (hφ' I z) (hφ' J _)

end GlobalTheory
