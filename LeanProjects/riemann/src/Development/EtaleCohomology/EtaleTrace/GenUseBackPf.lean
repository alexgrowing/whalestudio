import Development.EtaleCohomology.EtaleTrace.GenUsePf

noncomputable section
open CategoryTheory Limits AlgebraicGeometry MvPolynomial
attribute [local instance] MvPolynomial.gradedAlgebra

namespace LateralTheory.EtaleTrace.Cov

lemma gub_stalk_inj {X : Scheme.{0}} [IsIntegral X] (x : X) :
    Function.Injective (algebraMap (X.presheaf.stalk x) X.functionField) := by
  rw [injective_iff_map_eq_zero]
  intro a ha
  obtain ⟨U, hxU, s, rfl⟩ := X.presheaf.exists_germ_eq a
  have : Nonempty U := ⟨⟨x, hxU⟩⟩
  rw [Scheme.algebraMap_germ_eq_germToFunctionField] at ha
  have := Scheme.germToFunctionField_injective X U (ha.trans (map_zero _).symm)
  rw [this, map_zero]

lemma gub_notMem {k : Type} [Field k] {N : ℕ} (h : MvPolynomial (Fin (N + 1)) k) {d : ℕ}
    (hh : h ∈ homogeneousSubmodule (Fin (N + 1)) k d) (n : ℕ) (f : MvPolynomial (Fin (N + 1)) k)
    (hf : f ∈ homogeneousSubmodule (Fin (N + 1)) k (n • d)) (y : Proj (homogeneousSubmodule (Fin (N + 1)) k))
    (hy : y ∈ (Proj (homogeneousSubmodule (Fin (N + 1)) k)).basicOpen
      (Proj.awayToSection _ h (HomogeneousLocalization.Away.mk _ hh n f hf))) :
    y ∈ Proj.basicOpen (homogeneousSubmodule (Fin (N + 1)) k) f := by
  obtain ⟨hyU, hu⟩ := (Scheme.mem_basicOpen'' _ _ _).mp hy
  have hu2 := hu.map (Proj.stalkIso' (homogeneousSubmodule (Fin (N + 1)) k) y)
  erw [Proj.stalkIso'_germ] at hu2
  rw [← HomogeneousLocalization.isUnit_iff_isUnit_val] at hu2
  erw [ProjectiveSpectrum.Proj.awayToSection_apply] at hu2
  rw [HomogeneousLocalization.Away.val_mk, Localization.mk_eq_mk', IsLocalization.map_mk'] at hu2
  rw [Proj.mem_basicOpen]
  have hp : y.asHomogeneousIdeal.toIdeal.IsPrime := y.isPrime
  exact (IsLocalization.AtPrime.isUnit_mk'_iff (hI := hp) _ _ _ _).mp hu2

lemma gub_cover {k : Type} [Field k] {N : ℕ} (y : Proj (homogeneousSubmodule (Fin (N + 1)) k)) :
    ∃ i, y ∈ Proj.basicOpen (homogeneousSubmodule (Fin (N + 1)) k) (MvPolynomial.X i) := by
  have hcov : ⨆ i, Proj.basicOpen (homogeneousSubmodule (Fin (N + 1)) k) (MvPolynomial.X i) = ⊤ := by
    apply Proj.iSup_basicOpen_eq_top'
    · exact fun i => ⟨1, (mem_homogeneousSubmodule _ _).mpr (isHomogeneous_X k i)⟩
    · rw [eq_top_iff]
      rintro a -
      induction a using MvPolynomial.induction_on with
      | C c =>
        have : (C c : MvPolynomial (Fin (N + 1)) k) ∈ homogeneousSubmodule (Fin (N + 1)) k 0 :=
          (mem_homogeneousSubmodule _ _).mpr (isHomogeneous_C _ c)
        exact Subalgebra.algebraMap_mem _ (⟨_, this⟩ : homogeneousSubmodule (Fin (N + 1)) k 0)
      | add a b ha hb => exact Subalgebra.add_mem _ ha hb
      | mul_X a i ha => exact Subalgebra.mul_mem _ ha (Algebra.subset_adjoin ⟨i, rfl⟩)
  have hm : y ∈ (⊤ : (Proj (homogeneousSubmodule (Fin (N + 1)) k)).Opens) := trivial
  rw [← hcov, TopologicalSpace.Opens.mem_iSup] at hm
  exact hm

theorem GenUseBack_of : GenUseBack := by
  intro k _ X _ p N ι v hG n hn f hf x hne hloc
  obtain ⟨i, hxi⟩ := gub_cover (ι x)
  have hXi : (MvPolynomial.X i : MvPolynomial (Fin (N + 1)) k) ∈ homogeneousSubmodule (Fin (N + 1)) k 1 :=
    (mem_homogeneousSubmodule _ _).mpr (isHomogeneous_X k i)
  have hxU : x ∈ ι ⁻¹ᵁ Proj.basicOpen (homogeneousSubmodule (Fin (N + 1)) k) (MvPolynomial.X i) := hxi
  have hη := genUse_generic_mem _ x hxU
  have hvi : eval₂ (kHom p) v (MvPolynomial.X i) ≠ 0 := ((hG 1 one_pos _ hXi).1).mp hη
  have hf' : f ∈ homogeneousSubmodule (Fin (N + 1)) k (n • 1) := by
    rw [smul_eq_mul, mul_one]; exact (mem_homogeneousSubmodule _ _).mpr hf
  have key := (hG 1 one_pos _ hXi).2 n f hf' hη
  have : Nonempty (ι ⁻¹ᵁ Proj.basicOpen (homogeneousSubmodule (Fin (N + 1)) k) (MvPolynomial.X i)) := ⟨⟨x, hxU⟩⟩
  have hγ : algebraMap _ X.functionField (X.presheaf.germ _ x hxU (ι.app _ (Proj.awayToSection _ (MvPolynomial.X i)
      (HomogeneousLocalization.Away.mk _ hXi n f hf')))) =
      eval₂ (kHom p) v f / eval₂ (kHom p) v (MvPolynomial.X i) ^ n := by
    rw [Scheme.algebraMap_germ_eq_germToFunctionField, eq_div_iff (pow_ne_zero _ hvi)]
    exact key
  have hg : ((MvPolynomial.X i : MvPolynomial (Fin (N + 1)) k) ^ n).IsHomogeneous n := by
    simpa using (isHomogeneous_X k i).pow n
  obtain ⟨δ, hδ⟩ := hloc _ hg
  have hu : IsUnit (X.presheaf.germ _ x hxU (ι.app _ (Proj.awayToSection _ (MvPolynomial.X i)
      (HomogeneousLocalization.Away.mk _ hXi n f hf')))) := by
    refine isUnit_iff_exists_inv.mpr ⟨δ, gub_stalk_inj x ?_⟩
    rw [map_mul, map_one, hγ, hδ, eval₂_pow]
    have h1 := pow_ne_zero n hvi
    field_simp
  have hmem := (Scheme.mem_basicOpen'' _ _ _).mpr ⟨hxU, hu⟩
  rw [← Scheme.preimage_basicOpen] at hmem
  exact gub_notMem _ hXi n f hf' _ hmem

end LateralTheory.EtaleTrace.Cov
