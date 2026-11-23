import ReciprocityTheory.AnalyticForms.RegularLocalRings.ProjDehom
import ReciprocityTheory.AnalyticForms.RegularLocalRings.LogResStC
import ReciprocityTheory.AnalyticForms.RegularLocalRings.FinTypeQE

namespace ReciprocityTheory.AnForm.R

open MvPolynomial AlgebraicGeometry CategoryTheory

noncomputable section

variable {K : Type} [Fintype K] [Nonempty K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem iSup_chartOpen_eq_top {P : Ideal (MvPolynomial (Σ k, ι k) ℂ)} (hP : IsMultiHomogIdeal P) :
    (⨆ p : (k : K) → ι k, ((chartOpen hP p).1 : (projX P hP).Opens)) = ⊤ := by
  rw [eq_top_iff]
  intro x _
  obtain ⟨p, hp⟩ := chartOpen_cover hP x
  exact TopologicalSpace.Opens.mem_iSup.mpr ⟨p, hp⟩

theorem isNoetherianRing_gammaChart {P : Ideal (MvPolynomial (Σ k, ι k) ℂ)} (hP : IsMultiHomogIdeal P)
    (p : (k : K) → ι k) : IsNoetherianRing Γ(projX P hP, (chartOpen hP p).1) :=
  isNoetherianRing_of_ringEquiv _ (gammaChart hP p).symm

theorem isReduced_away {P : Ideal (MvPolynomial (Σ k, ι k) ℂ)} (hP : IsMultiHomogIdeal P)
    (hrad : P.IsRadical) (p : (k : K) → ι k) :
    letI := segreGraded hP
    _root_.IsReduced (HomogeneousLocalization.Away (segreGrading P) (segreW P p)) := by
  letI := segreGraded hP
  have : _root_.IsReduced (MvPolynomial ((k : K) → ι k) ℂ ⧸ segreIdeal P) :=
    (Ideal.isRadical_iff_quotient_reduced _).mp (hrad.comap _)
  exact isReduced_of_injective (algebraMap _ (Localization.Away (segreW P p)))
    (HomogeneousLocalization.val_injective _)

theorem isReduced_gammaChart {P : Ideal (MvPolynomial (Σ k, ι k) ℂ)} (hP : IsMultiHomogIdeal P)
    (hrad : P.IsRadical) (p : (k : K) → ι k) :
    _root_.IsReduced Γ(projX P hP, (chartOpen hP p).1) := by
  letI := segreGraded hP
  have := isReduced_away hP hrad p
  exact isReduced_of_injective _ ((gammaChart hP p).trans (awayEquiv hP p)).injective

theorem qeRing_gammaChart {P : Ideal (MvPolynomial (Σ k, ι k) ℂ)} (hP : IsMultiHomogIdeal P)
    (hQE : FinalTheorems.FinTypeQE) (p : (k : K) → ι k) : FinalTheorems.QERing Γ(projX P hP, (chartOpen hP p).1) := by
  letI : Algebra ℂ Γ(projX P hP, (chartOpen hP p).1) :=
    ((gammaChart hP p).symm.toRingHom.comp (algebraMap ℂ (chartRing P p))).toAlgebra
  let e : chartRing P p ≃ₐ[ℂ] Γ(projX P hP, (chartOpen hP p).1) :=
    { (gammaChart hP p).symm with commutes' := fun c => rfl }
  haveI : Algebra.FiniteType ℂ Γ(projX P hP, (chartOpen hP p).1) :=
    Algebra.FiniteType.equiv inferInstance e
  exact hQE Γ(projX P hP, (chartOpen hP p).1)

theorem isRegularLocalRing_stalk_fromSpec_iff {X : Scheme.{0}} {U : X.Opens} (hU : IsAffineOpen U)
    (y : PrimeSpectrum Γ(X, U)) (hy : hU.fromSpec y ∈ U) :
    IsRegularLocalRing (X.presheaf.stalk (hU.fromSpec y)) ↔
      IsRegularLocalRing (Localization.AtPrime y.asIdeal) := by
  letI := TopCat.Presheaf.algebra_section_stalk X.presheaf ⟨hU.fromSpec y, hy⟩
  haveI : IsLocalization y.asIdeal.primeCompl (X.presheaf.stalk (hU.fromSpec y)) :=
    hU.isLocalization_stalk' y hy
  let e := IsLocalization.algEquiv y.asIdeal.primeCompl (Localization.AtPrime y.asIdeal)
    (X.presheaf.stalk (hU.fromSpec y))
  exact ⟨fun h => IsRegularLocalRing.of_ringEquiv e.symm.toRingEquiv,
    fun h => IsRegularLocalRing.of_ringEquiv e.toRingEquiv⟩

theorem isOpen_regularLocus_of_cover {X : Scheme.{0}} {J : Type} (U : J → X.affineOpens)
    (hcov : ∀ x, ∃ i, x ∈ (U i).1)
    (h : ∀ i, IsOpen {Q : PrimeSpectrum Γ(X, (U i).1) |
      IsRegularLocalRing (Localization.AtPrime Q.asIdeal)}) :
    IsOpen {x : X | IsRegularLocalRing (X.presheaf.stalk x)} := by
  rw [isOpen_iff_forall_mem_open]
  intro x hx
  obtain ⟨i, hi⟩ := hcov x
  have hU : IsAffineOpen (U i).1 := (U i).2
  refine ⟨(⇑hU.fromSpec) '' {Q : PrimeSpectrum Γ(X, (U i).1) |
    IsRegularLocalRing (Localization.AtPrime Q.asIdeal)}, ?_, ?_, ?_⟩
  · rintro _ ⟨q, hq, rfl⟩
    have hq' : hU.fromSpec q ∈ (U i).1 := hU.range_fromSpec.le ⟨q, rfl⟩
    exact (isRegularLocalRing_stalk_fromSpec_iff hU q hq').mpr hq
  · exact (IsAffineOpen.fromSpec hU).isOpenEmbedding.isOpenMap _ (h i)
  · refine ⟨hU.primeIdealOf ⟨x, hi⟩, ?_, hU.fromSpec_primeIdealOf ⟨x, hi⟩⟩
    have h1 := hU.fromSpec_primeIdealOf ⟨x, hi⟩
    have h2 := isRegularLocalRing_stalk_fromSpec_iff hU (hU.primeIdealOf ⟨x, hi⟩) (by rw [h1]; exact hi)
    rw [h1] at h2
    exact h2.mp hx

theorem eval₂_smul_of_isMultiHomog' {R : Type} [CommRing R] (g : ℂ →+* R)
    {f : MvPolynomial (Σ k, ι k) ℂ} {a : K → ℕ} (hf : IsMultiHomog f a) (c : K → R)
    (y : (Σ k, ι k) → R) :
    eval₂ g (fun q => c q.1 * y q) f = (∏ k, c k ^ a k) * eval₂ g y f := by
  classical
  rw [f.as_sum, MvPolynomial.eval₂_sum, MvPolynomial.eval₂_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun mo hmo => ?_
  rw [MvPolynomial.eval₂_monomial, MvPolynomial.eval₂_monomial,
    Finsupp.prod_fintype _ _ (fun _ => pow_zero _), Finsupp.prod_fintype _ _ (fun _ => pow_zero _)]
  simp_rw [mul_pow, Finset.prod_mul_distrib]
  rw [Fintype.prod_sigma]
  have hk : ∀ k, ∏ i, c k ^ mo ⟨k, i⟩ = c k ^ a k := by
    intro k
    rw [Finset.prod_pow_eq_pow_sum, hf mo hmo k]
  simp only [hk]
  ring

theorem eval₂_smul_of_isHomogeneous' {σ R : Type} [Fintype σ] [CommRing R] (g : ℂ →+* R)
    {f : MvPolynomial σ ℂ} {d : ℕ} (hf : f.IsHomogeneous d) (t : R) (y : σ → R) :
    eval₂ g (fun i => t * y i) f = t ^ d * eval₂ g y f := by
  classical
  rw [f.as_sum, MvPolynomial.eval₂_sum, MvPolynomial.eval₂_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun mo hmo => ?_
  have hd : ∑ i, mo i = d := by
    have := hf (MvPolynomial.mem_support_iff.1 hmo)
    simpa [Finsupp.weight_apply, Finsupp.sum_fintype] using this
  rw [MvPolynomial.eval₂_monomial, MvPolynomial.eval₂_monomial,
    Finsupp.prod_fintype _ _ (fun _ => pow_zero _), Finsupp.prod_fintype _ _ (fun _ => pow_zero _)]
  simp_rw [mul_pow, Finset.prod_mul_distrib]
  rw [Finset.prod_pow_eq_pow_sum, hd]
  ring

theorem isUnit_mapId_mk_iff {A : Type} [CommRing A] [Algebra ℂ A]
    (𝒜 : ℕ → Submodule ℂ A) [GradedAlgebra 𝒜] (f : A) (x : ProjectiveSpectrum 𝒜)
    (H : Submonoid.powers f ≤ x.asHomogeneousIdeal.toIdeal.primeCompl)
    (z : HomogeneousLocalization.NumDenSameDeg 𝒜 (Submonoid.powers f)) :
    IsUnit (HomogeneousLocalization.mapId 𝒜 H (HomogeneousLocalization.mk z)) ↔
      z.num.1 ∉ x.asHomogeneousIdeal := by
  have hv : (HomogeneousLocalization.mapId 𝒜 H (HomogeneousLocalization.mk z)).val =
      IsLocalization.mk' (Localization.AtPrime x.asHomogeneousIdeal.toIdeal) (z.num : A)
        (⟨z.den, H z.den_mem⟩ : x.asHomogeneousIdeal.toIdeal.primeCompl) := by
    rw [← Localization.mk_eq_mk']; rfl
  rw [← HomogeneousLocalization.isUnit_iff_isUnit_val, hv, IsLocalization.AtPrime.isUnit_mk'_iff]
  rfl

theorem evaluation_awayToSection_eq_zero_iff {A : Type} [CommRing A] [Algebra ℂ A]
    (𝒜 : ℕ → Submodule ℂ A) [GradedAlgebra 𝒜] (f : A) (x : Proj 𝒜)
    (hx : x ∈ Proj.basicOpen 𝒜 f)
    (z : HomogeneousLocalization.NumDenSameDeg 𝒜 (Submonoid.powers f)) :
    (Proj 𝒜).evaluation (Proj.basicOpen 𝒜 f) x hx
        (Proj.awayToSection 𝒜 f (HomogeneousLocalization.mk z)) = 0 ↔
      z.num.1 ∈ ProjectiveSpectrum.asHomogeneousIdeal (𝒜 := 𝒜) x := by
  have e1 : (Proj 𝒜).evaluation (Proj.basicOpen 𝒜 f) x hx
        (Proj.awayToSection 𝒜 f (HomogeneousLocalization.mk z)) = 0 ↔
      ¬ IsUnit ((Proj 𝒜).presheaf.germ (Proj.basicOpen 𝒜 f) x hx
        (Proj.awayToSection 𝒜 f (HomogeneousLocalization.mk z))) :=
    (IsLocalRing.residue_eq_zero_iff _).trans (by rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]; exact Iff.rfl)
  refine e1.trans ?_
  have h := congrArg (fun φ => φ.hom (HomogeneousLocalization.mk z))
    (ProjectiveSpectrum.Proj.awayToSection_germ 𝒜 f x hx)
  simp only [CommRingCat.hom_comp, RingHom.comp_apply] at h
  have h2 := (Iff.of_eq (congrArg IsUnit h)).trans
    (isUnit_map_iff (Proj.stalkIso' 𝒜 x).symm _)
  refine (Iff.not h2).trans ?_
  let x' : ProjectiveSpectrum 𝒜 := x
  have H : Submonoid.powers f ≤ x'.asHomogeneousIdeal.toIdeal.primeCompl :=
    Submonoid.powers_le.mpr (by exact hx)
  exact (not_congr (isUnit_mapId_mk_iff 𝒜 f x' H z)).trans not_not

end

end ReciprocityTheory.AnForm.R
