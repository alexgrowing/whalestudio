import Mathlib
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.ChartRing
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.EtaleCoordinates
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.EtaleChartExistence
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.FormallyEtaleCoordinates
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.JacobianCriterion
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.LocalParameters
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.StrictNormalCrossings
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.SmoothCenterChart
import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.DerivativeIdealSheaf
import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.IdealSheafOrder
import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.DerivativeIdealSheafOrderDecrease
import Development.ResolutionOfSingularities.Foundations.Schemes.IdealSheafData
import Development.ResolutionOfSingularities.EmbeddedResolution.MaximalContactHypersurfaces.MaxContactIdeal
import Development.ResolutionOfSingularities.Foundations.BlowupUniversalProperty
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionOfSingularities
universe u

open AlgebraicGeometry CategoryTheory TopologicalSpace

open scoped TensorProduct

namespace FunctorialResolution.EmbeddedResolution

private theorem presheaf_map_op_eq_map_op {X : Scheme.{u}} {A B : X.Opens} (f g : B ⟶ A) :
    X.presheaf.map f.op = X.presheaf.map g.op := by
  rw [Subsingleton.elim f g]

private theorem topIso_hom_comp_inv {X : Scheme.{u}} (U : X.Opens) :
    (U.topIso.hom.hom).comp (U.topIso.inv.hom) = RingHom.id _ := by
  rw [← CommRingCat.hom_comp, Iso.inv_hom_id, CommRingCat.hom_id]

private theorem topIso_inv_comp_hom {X : Scheme.{u}} (U : X.Opens) :
    (U.topIso.inv.hom).comp (U.topIso.hom.hom) = RingHom.id _ := by
  rw [← CommRingCat.hom_comp, Iso.hom_inv_id, CommRingCat.hom_id]

private theorem appLE_opensι_top_eq_topIso_inv {X : Scheme.{u}} (U : X.Opens)
    (h : (⊤ : (↑U : Scheme.{u}).Opens) ≤ U.ι ⁻¹ᵁ U) :
    Scheme.Hom.appLE U.ι U ⊤ h = U.topIso.inv := by
  rw [Scheme.Opens.ι_appLE, Scheme.Opens.topIso_inv]
  exact presheaf_map_op_eq_map_op _ _

private theorem topIso_hom_comp_appLE_ι {X : Scheme.{u}} (U : X.Opens)
    (h : (⊤ : (↑U : Scheme.{u}).Opens) ≤ U.ι ⁻¹ᵁ U) :
    (U.topIso.hom.hom).comp ((Scheme.Hom.appLE U.ι U ⊤ h).hom) = RingHom.id _ := by
  rw [appLE_opensι_top_eq_topIso_inv]
  exact topIso_hom_comp_inv U

private theorem basis_det_D_update_eq_coeff {k : Type*} {S : Type*} [CommRing k] [CommRing S] [Algebra k S]
    {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι S (KaehlerDifferential k S))
    (y : ι → S) (hb : ∀ i, b i = KaehlerDifferential.D k S (y i))
    (i0 : ι) (z : S) (a : ι → S)
    (hz : KaehlerDifferential.D k S z = ∑ i, a i • b i) :
    b.det (fun i => KaehlerDifferential.D k S (Function.update y i0 z i)) = a i0 := by
  have hmat : b.toMatrix (fun i => KaehlerDifferential.D k S (Function.update y i0 z i))
      = Matrix.updateCol (1 : Matrix ι ι S) i0 a := by
    ext i j
    rw [Module.Basis.toMatrix_apply, Matrix.updateCol_apply]
    by_cases hj : j = i0
    · subst hj
      rw [if_pos rfl, Function.update_self, hz]
      simp [Finsupp.single_apply]
    · rw [if_neg hj, Function.update_of_ne hj, ← hb, Matrix.one_apply]
      simp [Module.Basis.repr_self, Finsupp.single_apply, eq_comm]
  rw [Module.Basis.det_apply, hmat, ← Matrix.cramer_apply]
  simp [Matrix.cramer_one]

section

private theorem one_tmul_ne_zero_of_notMem_maximalIdeal_sq {A : Type*} [CommRing A] [IsLocalRing A]
    (a : A) (ha : a ∈ IsLocalRing.maximalIdeal A)
    (ha2 : a ∉ IsLocalRing.maximalIdeal A ^ 2) :
    (1 : IsLocalRing.ResidueField A) ⊗ₜ[A]
      (⟨a, ha⟩ : ↥(IsLocalRing.maximalIdeal A)) ≠ 0 := by
  intro h
  apply ha2
  have hker : IsLocalRing.maximalIdeal A ≤ LinearMap.ker
      (LinearMap.toSpanSingleton A
        (↥(IsLocalRing.maximalIdeal A) →ₗ[A] (IsLocalRing.maximalIdeal A).Cotangent)
        (Ideal.toCotangent (IsLocalRing.maximalIdeal A))) := by
    intro b hb
    rw [LinearMap.mem_ker]
    ext y
    have hy : ((b • y : ↥(IsLocalRing.maximalIdeal A)) : A) ∈
        IsLocalRing.maximalIdeal A ^ 2 := by
      rw [pow_two]
      exact Ideal.mul_mem_mul hb y.2
    have h0 : (Ideal.toCotangent (IsLocalRing.maximalIdeal A)) (b • y) = 0 :=
      (Ideal.toCotangent_eq_zero (IsLocalRing.maximalIdeal A) (b • y)).mpr hy
    rw [map_smul] at h0
    show b • (Ideal.toCotangent (IsLocalRing.maximalIdeal A)) y = 0
    exact h0
  have h' : (1 : A ⧸ IsLocalRing.maximalIdeal A) ⊗ₜ[A]
      (⟨a, ha⟩ : ↥(IsLocalRing.maximalIdeal A)) = 0 := h
  have key := congrArg (TensorProduct.lift
      (Submodule.liftQ (IsLocalRing.maximalIdeal A) _ hker)) h'
  rw [TensorProduct.lift.tmul, map_zero] at key
  have h1 : (Submodule.liftQ (IsLocalRing.maximalIdeal A)
      (LinearMap.toSpanSingleton A
        (↥(IsLocalRing.maximalIdeal A) →ₗ[A] (IsLocalRing.maximalIdeal A).Cotangent)
        (Ideal.toCotangent (IsLocalRing.maximalIdeal A))) hker)
      (1 : A ⧸ IsLocalRing.maximalIdeal A)
      = Ideal.toCotangent (IsLocalRing.maximalIdeal A) := by
    have e1 : (1 : A ⧸ IsLocalRing.maximalIdeal A) = Submodule.Quotient.mk (1 : A) := rfl
    rw [e1, Submodule.liftQ_apply, LinearMap.toSpanSingleton_apply, one_smul]
  rw [h1] at key
  exact (Ideal.toCotangent_eq_zero (IsLocalRing.maximalIdeal A) ⟨a, ha⟩).mp key

theorem linearIndependent_one_tmul_D_of_notMem_maximalIdeal_sq
    (k : Type*) (A : Type*) [CommRing k] [CommRing A] [Algebra k A] [IsLocalRing A]
    [IsNoetherianRing A] [Algebra.FormallySmooth k A]
    [Module.Free A (KaehlerDifferential k A)] [Module.Finite A (KaehlerDifferential k A)]
    [Algebra k (IsLocalRing.ResidueField A)] [IsScalarTower k A (IsLocalRing.ResidueField A)]
    [Algebra.FormallySmooth k (IsLocalRing.ResidueField A)]
    (a : A) (ha : a ∈ IsLocalRing.maximalIdeal A)
    (ha2 : a ∉ IsLocalRing.maximalIdeal A ^ 2) :
    LinearIndependent (IsLocalRing.ResidueField A)
      (fun _ : Fin 1 =>
        (1 : IsLocalRing.ResidueField A) ⊗ₜ[A] KaehlerDifferential.D k A a) := by
  have key : LinearIndependent (IsLocalRing.ResidueField A)
      (fun _ : Fin 1 => (1 : IsLocalRing.ResidueField A) ⊗ₜ[A]
        (⟨a, ha⟩ : ↥(IsLocalRing.maximalIdeal A))) := by
    rw [Fintype.linearIndependent_iff]
    intro g hg i
    rw [Fin.sum_univ_one] at hg
    rcases smul_eq_zero.mp hg with hzero | hzero
    · rw [Subsingleton.elim i 0]
      exact hzero
    · exact absurd hzero (one_tmul_ne_zero_of_notMem_maximalIdeal_sq a ha ha2)
  exact linearIndependent_tensor_D_of_maximalIdeal k A
    (fun _ : Fin 1 => (⟨a, ha⟩ : ↥(IsLocalRing.maximalIdeal A))) key

end

section

variable (k : Type u) [Field k] {X : Scheme.{u}} (p : X ⟶ Spec (CommRingCat.of k))

theorem coordIdeal_singleton_le_restrictIdeal_iff {U : X.Opens} (hU : IsAffineOpen U) {n : ℕ}
    (c : EtaleChart p U n) (j : Fin n) (J : X.IdealSheafData) :
    c.coordIdeal {j} ≤ restrictIdeal J U ↔ c.coord j ∈ J.ideal ⟨U, hU⟩ := by
  have : IsAffine (↑U : Scheme.{u}) := hU
  have htop : IsAffineOpen (⊤ : (↑U : Scheme.{u}).Opens) := isAffineOpen_top _
  obtain ⟨t, htdef⟩ : ∃ t : Γ((↑U : Scheme.{u}), ⊤), t = (c.map.appTop).hom
      (AffineSpace.coord (Spec (CommRingCat.of k)) (ULift.up j)) := ⟨_, rfl⟩
  have hcoord : c.coord j = U.topIso.hom.hom t := by rw [htdef]; rfl
  rw [EtaleChart.coordIdeal_eq_comap_coordSubspaceIdeal, coordSubspaceIdeal_eq_ofIdealTop_span_coord, restrictIdeal_eq_comap_ι,
    Scheme.IdealSheafData.comap_ofIdealTop]
  simp only [Ideal.map_span, Set.image_singleton, Finset.coe_singleton]
  rw [← htdef]
  constructor
  · intro h
    have h2 := h ⟨⊤, htop⟩
    rw [Scheme.IdealSheafData.comap_ideal_eq_map_appLE J U.ι ⟨U, hU⟩ ⟨⊤, htop⟩ (by simp),
      Scheme.IdealSheafData.ofIdealTop_ideal_top] at h2
    have ht := h2 (Ideal.mem_span_singleton_self t)
    have hmem2 := Ideal.mem_map_of_mem (U.topIso.hom.hom) ht
    rw [Ideal.map_map, topIso_hom_comp_appLE_ι U (by simp), Ideal.map_id] at hmem2
    rw [hcoord]
    exact hmem2
  · intro h V
    rw [Scheme.IdealSheafData.comap_ideal_eq_map_appLE J U.ι ⟨U, hU⟩ V (by simp),
      Scheme.IdealSheafData.ofIdealTop_ideal, Ideal.map_span, Set.image_singleton,
      Ideal.span_le, Set.singleton_subset_iff]
    have hmorph : Scheme.Hom.appLE U.ι U (V : (↑U : Scheme.{u}).Opens) (by simp)
        = U.topIso.inv ≫ (↑U : Scheme.{u}).presheaf.map
          (homOfLE (le_top : (V : (↑U : Scheme.{u}).Opens) ≤ ⊤)).op := by
      rw [← appLE_opensι_top_eq_topIso_inv U (by simp), Scheme.Hom.appLE_map]
    rw [hmorph, CommRingCat.hom_comp, ← Ideal.map_map]
    refine Ideal.mem_map_of_mem _ ?_
    have e2 : U.topIso.inv.hom (c.coord j) = t := by
      rw [hcoord]
      exact DFunLike.congr_fun (topIso_inv_comp_hom U) t
    rw [← e2]
    exact Ideal.mem_map_of_mem _ h

variable [LocallyOfFiniteType p]

def IsMaxContactCoord (I : X.IdealSheafData) (m : ℕ) {U : X.Opens} {n : ℕ}
    (c : EtaleChart p U n) (j : Fin n) : Prop :=
  c.coordIdeal {j} ≤ restrictIdeal (maxContactIdeal k p I m) U

theorem isMaxContactCoord_iff (I : X.IdealSheafData) (m : ℕ) {U : X.Opens} {n : ℕ}
    (c : EtaleChart p U n) (j : Fin n) :
    IsMaxContactCoord k p I m c j ↔
      c.coordIdeal {j} ≤ restrictIdeal (maxContactIdeal k p I m) U :=
  Iff.rfl

theorem isMaxContactCoord_one_iff (I : X.IdealSheafData) {U : X.Opens} {n : ℕ}
    (c : EtaleChart p U n) (j : Fin n) :
    IsMaxContactCoord k p I 1 c j ↔ c.coordIdeal {j} ≤ restrictIdeal I U := by
  rw [isMaxContactCoord_iff, maxContactIdeal_one k p I]

theorem isMaxContactCoord_iff_coord_mem (I : X.IdealSheafData) (m : ℕ) {U : X.Opens}
    (hU : IsAffineOpen U) {n : ℕ} (c : EtaleChart p U n) (j : Fin n) :
    IsMaxContactCoord k p I m c j ↔ c.coord j ∈ (maxContactIdeal k p I m).ideal ⟨U, hU⟩ :=
  coordIdeal_singleton_le_restrictIdeal_iff k p hU c j (maxContactIdeal k p I m)

variable [CharZero k] [AlgebraicGeometry.Smooth p]

theorem mem_support_maxContactIdeal_of_mem_orderAtLeastLocus (I : X.IdealSheafData) {m : ℕ}
    (hm : 1 ≤ m) {x : X} (hx : x ∈ orderAtLeastLocus I m) :
    x ∈ (maxContactIdeal k p I m).support := by
  have h := support_derivIdealSheafIterate_eq_orderAtLeastLocus k p I hm
  have hx' : x ∈ ((derivIdealSheafIterate k p (m - 1) I).support : Set X) := by
    rw [h]; exact hx
  exact hx'

theorem orderAt_maxContactIdeal_eq_one (I : X.IdealSheafData) {m : ℕ} (hm : 1 ≤ m) {x : X}
    (hx : orderAt I x = (m : ℕ∞)) :
    orderAt (maxContactIdeal k p I m) x = (1 : ℕ∞) := by
  have h := orderAt_derivIdealSheafIterate_eq_sub k p I x hx (Nat.sub_le m 1)
  rw [maxContactIdeal_eq_derivIdealSheafIterate, h, show m - (m - 1) = 1 from by omega, Nat.cast_one]

theorem stalkIdeal_maxContactIdeal_le_maximalIdeal (I : X.IdealSheafData) {m : ℕ}
    (hm : 1 ≤ m) {x : X} (hx : orderAt I x = (m : ℕ∞)) :
    stalkIdeal (maxContactIdeal k p I m) x ≤
      IsLocalRing.maximalIdeal ↑(X.presheaf.stalk x) := by
  have h1 : orderAt (maxContactIdeal k p I m) x = (1 : ℕ∞) :=
    orderAt_maxContactIdeal_eq_one k p I hm hx
  have h2 := (le_orderAt_iff (maxContactIdeal k p I m) x 1).mp (by rw [Nat.cast_one, h1])
  rw [pow_one] at h2
  exact h2

theorem exists_section_maxContactIdeal_notMem_maximalIdeal_sq (I : X.IdealSheafData) {m : ℕ}
    (hm : 1 ≤ m) {x : X} (hx : orderAt I x = (m : ℕ∞)) {U : X.Opens} (hU : IsAffineOpen U)
    (hxU : x ∈ U) :
    ∃ s ∈ (maxContactIdeal k p I m).ideal ⟨U, hU⟩,
      (X.presheaf.germ U x hxU).hom s ∈ IsLocalRing.maximalIdeal ↑(X.presheaf.stalk x) ∧
        (X.presheaf.germ U x hxU).hom s ∉
          IsLocalRing.maximalIdeal ↑(X.presheaf.stalk x) ^ 2 := by
  have h1 : orderAt (maxContactIdeal k p I m) x = (1 : ℕ∞) :=
    orderAt_maxContactIdeal_eq_one k p I hm hx
  have hle : stalkIdeal (maxContactIdeal k p I m) x ≤
      IsLocalRing.maximalIdeal ↑(X.presheaf.stalk x) :=
    stalkIdeal_maxContactIdeal_le_maximalIdeal k p I hm hx
  have hmap : stalkIdeal (maxContactIdeal k p I m) x =
      Ideal.map (X.presheaf.germ U x hxU).hom ((maxContactIdeal k p I m).ideal ⟨U, hU⟩) :=
    stalkIdeal_eq_map_germ _ x ⟨U, hU⟩ hxU
  by_contra hno
  push Not at hno
  have h2 : stalkIdeal (maxContactIdeal k p I m) x ≤
      IsLocalRing.maximalIdeal ↑(X.presheaf.stalk x) ^ 2 := by
    rw [hmap, Ideal.map_le_iff_le_comap]
    intro s hs
    simp only [Ideal.mem_comap]
    exact hno s hs (hle (germ_mem_stalkIdeal _ x ⟨U, hU⟩ hxU hs))
  have h3 := (le_orderAt_iff (maxContactIdeal k p I m) x 2).mpr h2
  rw [h1] at h3
  simp at h3

theorem exists_isMaxContactCoord (I : X.IdealSheafData) {m : ℕ} (hm : 1 ≤ m) (x : X)
    (hx : orderAt I x = (m : ℕ∞)) :
    ∃ (U : X.Opens) (_ : IsAffineOpen U) (hxU : x ∈ U) (n : ℕ) (c : EtaleChart p U n)
      (j : Fin n),
      IsMaxContactCoord k p I m c j ∧
        (X.presheaf.germ U x hxU).hom (c.coord j) ∈
          IsLocalRing.maximalIdeal ↑(X.presheaf.stalk x) := by
  classical
  obtain ⟨U, n, hxU, hU, ⟨c⟩⟩ := exists_etaleChart p x
  obtain ⟨s, hs, hs1, hs2⟩ :=
    exists_section_maxContactIdeal_notMem_maximalIdeal_sq k p I hm hx hU hxU
  let _instSections : Algebra k Γ(X, U) := sectionsAlgebra k p U
  let _instChart : Algebra (MvPolynomial (ULift.{u} (Fin n)) k) Γ(X, U) := c.algebra
  have : IsScalarTower k (MvPolynomial (ULift.{u} (Fin n)) k) Γ(X, U) := c.isScalarTower
  have : Algebra.FormallyEtale (MvPolynomial (ULift.{u} (Fin n)) k) Γ(X, U) :=
    c.algebra_formallyEtale hU
  let _instStalk : Algebra k ↑(X.presheaf.stalk x) := stalkAlgebra k p x
  let _instGerm : Algebra Γ(X, U) ↑(X.presheaf.stalk x) :=
    (X.presheaf.germ U x hxU).hom.toAlgebra
  have : IsScalarTower k Γ(X, U) ↑(X.presheaf.stalk x) :=
    isScalarTower_stalk k p U x hxU (algebraMap_sectionsAlgebra k p U)
      (algebraMap_stalkAlgebra k p x) rfl
  have : IsNoetherianRing ↑(X.presheaf.stalk x) := isNoetherianRing_stalk k p x
  have : Algebra.FormallySmooth k ↑(X.presheaf.stalk x) := formallySmooth_stalk k p x
  have : Module.Finite ↑(X.presheaf.stalk x) (KaehlerDifferential k ↑(X.presheaf.stalk x)) :=
    finite_kaehlerDifferential_stalk k p x
  have : Module.Free ↑(X.presheaf.stalk x) (KaehlerDifferential k ↑(X.presheaf.stalk x)) :=
    free_kaehlerDifferential_stalk k p x
  let _instResidue : Algebra k (IsLocalRing.ResidueField ↑(X.presheaf.stalk x)) :=
    ((IsLocalRing.residue ↑(X.presheaf.stalk x)).comp (stalkAlgebraMap k p x)).toAlgebra
  have : IsScalarTower k ↑(X.presheaf.stalk x)
      (IsLocalRing.ResidueField ↑(X.presheaf.stalk x)) :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  have : Algebra.FormallySmooth k (IsLocalRing.ResidueField ↑(X.presheaf.stalk x)) :=
    formallySmooth_residueField k p x rfl
  have hli := linearIndependent_one_tmul_D_of_notMem_maximalIdeal_sq k ↑(X.presheaf.stalk x)
    ((X.presheaf.germ U x hxU).hom s) hs1 hs2
  have hne : (1 : IsLocalRing.ResidueField ↑(X.presheaf.stalk x)) ⊗ₜ[↑(X.presheaf.stalk x)]
      KaehlerDifferential.D k ↑(X.presheaf.stalk x)
        ((X.presheaf.germ U x hxU).hom s) ≠ 0 := hli.ne_zero 0
  obtain ⟨a, ha⟩ : ∃ a : ULift.{u} (Fin n) → Γ(X, U), ∀ i,
      a i = (EtaleCoordinates.basisKaehler k (ULift.{u} (Fin n)) Γ(X, U)).repr
        (KaehlerDifferential.D k Γ(X, U) s) i := ⟨_, fun i => rfl⟩
  have hrepr : KaehlerDifferential.D k Γ(X, U) s
      = ∑ i, a i • (EtaleCoordinates.basisKaehler k (ULift.{u} (Fin n)) Γ(X, U) i) := by
    have h := (Module.Basis.sum_repr
      (EtaleCoordinates.basisKaehler k (ULift.{u} (Fin n)) Γ(X, U))
      (KaehlerDifferential.D k Γ(X, U) s)).symm
    simpa only [← ha] using h
  have hex : ∃ i : ULift.{u} (Fin n), IsUnit ((X.presheaf.germ U x hxU).hom (a i)) := by
    by_contra hcon
    push Not at hcon
    apply hne
    show (1 : IsLocalRing.ResidueField ↑(X.presheaf.stalk x)) ⊗ₜ[↑(X.presheaf.stalk x)]
      KaehlerDifferential.D k ↑(X.presheaf.stalk x)
        (algebraMap Γ(X, U) ↑(X.presheaf.stalk x) s) = 0
    have h0 : KaehlerDifferential.D k ↑(X.presheaf.stalk x)
        (algebraMap Γ(X, U) ↑(X.presheaf.stalk x) s)
        = ∑ i, (KaehlerDifferential.map k k Γ(X, U) ↑(X.presheaf.stalk x))
            (a i • (EtaleCoordinates.basisKaehler k (ULift.{u} (Fin n)) Γ(X, U) i)) := by
      rw [← KaehlerDifferential.map_D k k Γ(X, U) ↑(X.presheaf.stalk x) s, hrepr, map_sum]
    rw [h0, TensorProduct.tmul_sum]
    refine Finset.sum_eq_zero fun i _ => ?_
    have h1 : (KaehlerDifferential.map k k Γ(X, U) ↑(X.presheaf.stalk x))
        (a i • (EtaleCoordinates.basisKaehler k (ULift.{u} (Fin n)) Γ(X, U) i))
        = ((X.presheaf.germ U x hxU).hom (a i)) •
          (KaehlerDifferential.map k k Γ(X, U) ↑(X.presheaf.stalk x))
            (EtaleCoordinates.basisKaehler k (ULift.{u} (Fin n)) Γ(X, U) i) := by
      rw [map_smul]
      exact (algebraMap_smul (↑(X.presheaf.stalk x)) (a i) _).symm
    rw [h1, ← TensorProduct.smul_tmul]
    have h2 : ((X.presheaf.germ U x hxU).hom (a i)) •
        (1 : IsLocalRing.ResidueField ↑(X.presheaf.stalk x)) = 0 := by
      rw [Algebra.smul_def, mul_one, IsLocalRing.ResidueField.algebraMap_eq,
        IsLocalRing.residue_eq_zero_iff]
      exact (IsLocalRing.mem_maximalIdeal _).mpr (mem_nonunits_iff.mpr (hcon i))
    rw [h2, TensorProduct.zero_tmul]
  obtain ⟨i0, hunit⟩ := hex
  have hV : IsAffineOpen (X.basicOpen (a i0)) := hU.basicOpen (a i0)
  have hxV : x ∈ X.basicOpen (a i0) :=
    (X.toLocallyRingedSpace.toRingedSpace.mem_basicOpen (a i0) x hxU).mpr hunit
  let _instBasicOpen : Algebra k Γ(X, X.basicOpen (a i0)) :=
    sectionsAlgebra k p (X.basicOpen (a i0))
  let _instRestrict : Algebra Γ(X, U) Γ(X, X.basicOpen (a i0)) :=
    (X.presheaf.map (homOfLE (X.basicOpen_le (a i0))).op).hom.toAlgebra
  have : IsScalarTower k Γ(X, U) Γ(X, X.basicOpen (a i0)) :=
    isScalarTower_sections k p U (a i0) (algebraMap_sectionsAlgebra k p U)
      (algebraMap_sectionsAlgebra k p (X.basicOpen (a i0))) rfl
  have : IsLocalization.Away (a i0) Γ(X, X.basicOpen (a i0)) :=
    hU.isLocalization_basicOpen (a i0)
  have : Algebra.FormallyEtale Γ(X, U) Γ(X, X.basicOpen (a i0)) :=
    Algebra.FormallyEtale.of_isLocalization (Submonoid.powers (a i0))
  have : Algebra.FormallySmooth k Γ(X, X.basicOpen (a i0)) :=
    formallySmooth_sections k p (X.basicOpen (a i0)) hV
      (algebraMap_sectionsAlgebra k p (X.basicOpen (a i0)))
  obtain ⟨e, he⟩ : ∃ e : Module.Basis (ULift.{u} (Fin n)) Γ(X, X.basicOpen (a i0))
      (KaehlerDifferential k Γ(X, X.basicOpen (a i0))),
      e = JacobianCriterion.inducedBasis k (ULift.{u} (Fin n)) Γ(X, U)
        Γ(X, X.basicOpen (a i0))
        (EtaleCoordinates.basisKaehler k (ULift.{u} (Fin n)) Γ(X, U)) := ⟨_, rfl⟩
  have he_apply : ∀ i, e i = (KaehlerDifferential.map k k Γ(X, U) Γ(X, X.basicOpen (a i0)))
      (EtaleCoordinates.basisKaehler k (ULift.{u} (Fin n)) Γ(X, U) i) := by
    intro i
    rw [he]
    exact JacobianCriterion.inducedBasis_apply k (ULift.{u} (Fin n)) Γ(X, U)
      Γ(X, X.basicOpen (a i0))
      (EtaleCoordinates.basisKaehler k (ULift.{u} (Fin n)) Γ(X, U)) i
  have hbT : ∀ i, e i = KaehlerDifferential.D k Γ(X, X.basicOpen (a i0))
      (algebraMap Γ(X, U) Γ(X, X.basicOpen (a i0))
        (EtaleCoordinates.coord k (ULift.{u} (Fin n)) Γ(X, U) i)) := by
    intro i
    rw [he]
    exact JacobianCriterion.inducedBasis_apply_D k (ULift.{u} (Fin n)) Γ(X, U)
      Γ(X, X.basicOpen (a i0))
      (EtaleCoordinates.basisKaehler k (ULift.{u} (Fin n)) Γ(X, U))
      (fun i => EtaleCoordinates.coord k (ULift.{u} (Fin n)) Γ(X, U) i)
      (fun i => EtaleCoordinates.basisKaehler_apply k (ULift.{u} (Fin n)) Γ(X, U) i) i
  have hz : KaehlerDifferential.D k Γ(X, X.basicOpen (a i0))
      (algebraMap Γ(X, U) Γ(X, X.basicOpen (a i0)) s)
      = ∑ i, (algebraMap Γ(X, U) Γ(X, X.basicOpen (a i0)) (a i)) • e i := by
    rw [← KaehlerDifferential.map_D k k Γ(X, U) Γ(X, X.basicOpen (a i0)) s, hrepr, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_smul, he_apply i, algebraMap_smul]
  obtain ⟨w, hw⟩ : ∃ w : ULift.{u} (Fin n) → Γ(X, X.basicOpen (a i0)),
      w = Function.update (fun i => algebraMap Γ(X, U) Γ(X, X.basicOpen (a i0))
        (EtaleCoordinates.coord k (ULift.{u} (Fin n)) Γ(X, U) i)) i0
        (algebraMap Γ(X, U) Γ(X, X.basicOpen (a i0)) s) := ⟨_, rfl⟩
  have hdet0 : (e.det fun i => KaehlerDifferential.D k Γ(X, X.basicOpen (a i0)) (w i))
      = algebraMap Γ(X, U) Γ(X, X.basicOpen (a i0)) (a i0) := by
    rw [hw]
    exact basis_det_D_update_eq_coeff e _ hbT i0 _
      (fun i => algebraMap Γ(X, U) Γ(X, X.basicOpen (a i0)) (a i)) hz
  have hdet : IsUnit (e.det fun i => KaehlerDifferential.D k Γ(X, X.basicOpen (a i0)) (w i)) := by
    rw [hdet0]
    exact IsLocalization.map_units Γ(X, X.basicOpen (a i0))
      (⟨a i0, Submonoid.mem_powers _⟩ : Submonoid.powers (a i0))
  obtain ⟨f, hf⟩ : ∃ f : MvPolynomial (ULift.{u} (Fin n)) k →+* Γ(X, X.basicOpen (a i0)),
      f = (MvPolynomial.aeval w :
        MvPolynomial (ULift.{u} (Fin n)) k →ₐ[k] Γ(X, X.basicOpen (a i0))).toRingHom := ⟨_, rfl⟩
  have hC : ∀ b : k, f (MvPolynomial.C b) = sectionsAlgebraMap k p (X.basicOpen (a i0)) b := by
    intro b
    rw [hf]
    show MvPolynomial.aeval w (MvPolynomial.C b) = _
    rw [MvPolynomial.aeval_C, algebraMap_sectionsAlgebra]
  have hXc : ∀ i : ULift.{u} (Fin n), f (MvPolynomial.X i) = w i := by
    intro i
    rw [hf]
    show MvPolynomial.aeval w (MvPolynomial.X i) = _
    rw [MvPolynomial.aeval_X]
  have hfet : f.Etale := by
    subst hf
    let inst : Algebra (MvPolynomial (ULift.{u} (Fin n)) k) Γ(X, X.basicOpen (a i0)) :=
      (MvPolynomial.aeval w :
        MvPolynomial (ULift.{u} (Fin n)) k →ₐ[k] Γ(X, X.basicOpen (a i0))).toRingHom.toAlgebra
    have : @Algebra.FormallyEtale (MvPolynomial (ULift.{u} (Fin n)) k)
        Γ(X, X.basicOpen (a i0)) _ _ inst :=
      EtaleCoordinates.formallyEtale_aeval_of_isUnit_det e w hdet
    have : IsScalarTower k (MvPolynomial (ULift.{u} (Fin n)) k)
        Γ(X, X.basicOpen (a i0)) :=
      IsScalarTower.of_algebraMap_eq fun r => (hC r).symm
    have : Algebra.FiniteType k Γ(X, X.basicOpen (a i0)) :=
      finiteType_sections k p ⟨X.basicOpen (a i0), hV⟩
        (algebraMap_sectionsAlgebra k p (X.basicOpen (a i0)))
    have : Algebra.FiniteType (MvPolynomial (ULift.{u} (Fin n)) k)
        Γ(X, X.basicOpen (a i0)) :=
      Algebra.FiniteType.of_restrictScalars_finiteType k
        (MvPolynomial (ULift.{u} (Fin n)) k) Γ(X, X.basicOpen (a i0))
    have : Algebra.FinitePresentation (MvPolynomial (ULift.{u} (Fin n)) k)
        Γ(X, X.basicOpen (a i0)) := Algebra.FinitePresentation.of_finiteType.mp inferInstance
    exact (⟨inferInstance, inferInstance⟩ :
      Algebra.Etale (MvPolynomial (ULift.{u} (Fin n)) k) Γ(X, X.basicOpen (a i0)))
  obtain ⟨c', hc'⟩ := exists_etaleChart_coord_eq p hV w f hC hXc hfet
  have hwi : w (ULift.up i0.down) = algebraMap Γ(X, U) Γ(X, X.basicOpen (a i0)) s := by
    rw [ULift.up_down, hw, Function.update_self]
  refine ⟨X.basicOpen (a i0), hV, hxV, n, c', i0.down, ?_, ?_⟩
  · rw [isMaxContactCoord_iff_coord_mem k p I m hV c' i0.down, hc' i0.down, hwi]
    have h2 : Ideal.map ((X.presheaf.map (homOfLE (X.basicOpen_le (a i0))).op).hom)
        ((maxContactIdeal k p I m).ideal ⟨U, hU⟩)
        = (maxContactIdeal k p I m).ideal ⟨X.basicOpen (a i0), hV⟩ :=
      Scheme.IdealSheafData.map_ideal_basicOpen _ ⟨U, hU⟩ (a i0)
    rw [← h2]
    exact Ideal.mem_map_of_mem _ hs
  · rw [hc' i0.down, hwi]
    have h3 := DFunLike.congr_fun (congrArg CommRingCat.Hom.hom
      (X.presheaf.germ_res (homOfLE (X.basicOpen_le (a i0))) x hxV)) s
    simp only [CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply] at h3
    have h4 : (X.presheaf.germ (X.basicOpen (a i0)) x hxV).hom
        (algebraMap Γ(X, U) Γ(X, X.basicOpen (a i0)) s)
        = (X.presheaf.germ U x hxU).hom s := h3
    rw [h4]
    exact hs1

end

end FunctorialResolution.EmbeddedResolution
