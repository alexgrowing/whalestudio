import Mathlib
import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.BlowupDerivativeIdealBound
import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.DerivativeIdealSheaf
import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.IdealSheafOrder
import Development.ResolutionOfSingularities.EmbeddedResolution.MaximalContactHypersurfaces.MaxContactIdeal
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.DivisorReduction.ControlledTransformBasic
universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace

namespace FunctorialResolution.EmbeddedResolution

private theorem exists_affineOpen_ideal_eq_top_of_not_mem_support {X : Scheme.{u}}
    (I : X.IdealSheafData) (y : ↥X) (hy : y ∉ I.support) :
    ∃ V : X.affineOpens, y ∈ V.1 ∧ I.ideal V = ⊤ := by
  obtain ⟨U, hyU, -⟩ :=
    Scheme.exists_affineOpens_mem_le (X := X) (x := y) (U := ⊤) trivial
  have hny := hy
  rw [AlgebraicGeometry.Scheme.IdealSheafData.mem_support_iff_of_mem (I := I) (U := U) hyU,
    AlgebraicGeometry.Scheme.mem_zeroLocus_iff] at hny
  push Not at hny
  obtain ⟨s, hs, hys⟩ := hny
  refine ⟨X.affineBasicOpen s, hys, ?_⟩
  let _ : Algebra Γ(X, U.1) Γ(X, X.basicOpen s) :=
    (X.presheaf.map (homOfLE (X.basicOpen_le s)).op).hom.toAlgebra
  have hloc : IsLocalization.Away s Γ(X, X.basicOpen s) := U.2.isLocalization_basicOpen s
  have hunit : IsUnit (algebraMap Γ(X, U.1) Γ(X, X.basicOpen s) s) :=
    IsLocalization.map_units (M := Submonoid.powers s) Γ(X, X.basicOpen s)
      ⟨s, Submonoid.mem_powers s⟩
  have hmem : algebraMap Γ(X, U.1) Γ(X, X.basicOpen s) s ∈ I.ideal (X.affineBasicOpen s) := by
    rw [← I.map_ideal_basicOpen U s]
    exact Ideal.mem_map_of_mem _ hs
  exact Ideal.eq_top_of_isUnit_mem _ hmem hunit

theorem not_mem_support_of_mem_support_of_pow_mul {X : Scheme.{u}}
    (Z I I₀ : X.IdealSheafData) (m : ℕ) (hfac : I = Z ^ m * I₀)
    (hord : ∀ x : ↥X, orderAt I x ≤ (m : ℕ∞)) {x : ↥X} (hx : x ∈ Z.support) :
    x ∉ I₀.support := by
  intro hx0
  have hZ : stalkIdeal Z x ≤ IsLocalRing.maximalIdeal (X.presheaf.stalk x) :=
    (mem_support_iff_stalkIdeal_le_maximalIdeal Z x).mp hx
  have hI0 : stalkIdeal I₀ x ≤ IsLocalRing.maximalIdeal (X.presheaf.stalk x) :=
    (mem_support_iff_stalkIdeal_le_maximalIdeal I₀ x).mp hx0
  have hIle : stalkIdeal I x ≤ IsLocalRing.maximalIdeal (X.presheaf.stalk x) ^ (m + 1) := by
    rw [hfac, stalkIdeal_mul, stalkIdeal_pow, pow_succ]
    exact Ideal.mul_mono (Ideal.pow_right_mono hZ m) hI0
  have h1 := (le_orderAt_iff I x (m + 1)).mpr hIle
  have h3 : ((m + 1 : ℕ) : ℕ∞) ≤ (m : ℕ∞) := le_trans h1 (hord x)
  have h4 : m + 1 ≤ m := by exact_mod_cast h3
  omega

theorem isDerivBalanced_of_pow_mul (k : Type u) [Field k] {X : Scheme.{u}}
    (p : X ⟶ Spec (CommRingCat.of k)) [AlgebraicGeometry.Smooth p]
    (Z I I₀ : X.IdealSheafData) (m : ℕ) (hfac : I = Z ^ m * I₀)
    (hord : ∀ x : ↥X, orderAt I x ≤ (m : ℕ∞)) (hbal : IsDerivBalanced k p I m) :
    IsDerivBalanced k p I₀ m := by
  refine (isDerivBalanced_iff k p I₀ m).mpr ?_
  intro i hi
  refine le_of_forall_exists_affineOpen ?_
  intro y
  by_cases hyZ : y ∈ Z.support
  · obtain ⟨V, hyV, hV⟩ := exists_affineOpen_ideal_eq_top_of_not_mem_support I₀ y
      (not_mem_support_of_mem_support_of_pow_mul Z I I₀ m hfac hord hyZ)
    refine ⟨V, hyV, ?_⟩
    have htop : (I₀ ^ (m - i)).ideal V = ⊤ := by
      rw [Scheme.IdealSheafData.ideal_pow]
      show I₀.ideal V ^ (m - i) = ⊤
      rw [hV, ← Ideal.one_eq_top, one_pow]
    rw [htop]
    exact le_top
  · obtain ⟨V, hyV, hV⟩ := exists_affineOpen_ideal_eq_top_of_not_mem_support Z y hyZ
    refine ⟨V, hyV, ?_⟩
    have hIV : I.ideal V = I₀.ideal V := by
      rw [hfac, Scheme.IdealSheafData.ideal_mul, Scheme.IdealSheafData.ideal_pow]
      show Z.ideal V ^ m * I₀.ideal V = I₀.ideal V
      rw [hV, ← Ideal.one_eq_top, one_pow, one_mul]
    have hder : (derivIdealSheafIterate k p i I).ideal V
        = (derivIdealSheafIterate k p i I₀).ideal V := by
      rw [derivIdealSheafIterate_ideal, derivIdealSheafIterate_ideal, hIV]
    have hb : ((derivIdealSheafIterate k p i I).ideal V) ^ m ≤ (I.ideal V) ^ (m - i) := by
      have hb0 := Scheme.IdealSheafData.le_def.mp ((isDerivBalanced_iff k p I m).mp hbal i hi) V
      rwa [Scheme.IdealSheafData.ideal_pow, Scheme.IdealSheafData.ideal_pow] at hb0
    rw [Scheme.IdealSheafData.ideal_pow, Scheme.IdealSheafData.ideal_pow]
    show ((derivIdealSheafIterate k p i I₀).ideal V) ^ m ≤ (I₀.ideal V) ^ (m - i)
    rw [← hIV, ← hder]
    exact hb

end FunctorialResolution.EmbeddedResolution
