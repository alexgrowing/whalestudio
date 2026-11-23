import Mathlib
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.AdaptedParameters
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.CoordinateDivisorSmoothness
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.ChartRing
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.EtaleCoordinates
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.EtaleChartExistence
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.FormallyEtaleCoordinates
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.StrictNormalCrossings
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.SmoothCenterChart
import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.DerivativeIdealSheaf
import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.OrderAtGenericPoint
import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.IdealSheafOrder
import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.DerivativeIdealSheafOrderDecrease
import Development.ResolutionOfSingularities.Foundations.Schemes.SchemeMorphismProperties
import Development.ResolutionOfSingularities.Foundations.BlowupUniversalProperty
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionOfSingularities
universe u

open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace

noncomputable section

namespace FunctorialResolution.EmbeddedResolution

theorem det_update_eq_repr {K V : Type*} [CommRing K] [AddCommGroup V] [Module K V]
    {ι : Type*} [Fintype ι] [DecidableEq ι] (e : Module.Basis ι K V) (j : ι) (v : V) :
    e.det (Function.update (⇑e) j v) = e.repr v j := by
  have key : ∀ b : ι → K, (Matrix.updateCol (1 : Matrix ι ι K) j b).det = b j := by
    intro b
    have h : (Matrix.cramer (1 : Matrix ι ι K)) b j
        = (Matrix.updateCol (1 : Matrix ι ι K) j b).det := by
      rw [Matrix.cramer_apply]
    rw [← h]
    simp [Matrix.cramer_one]
  have hm : e.toMatrix (Function.update (⇑e) j v)
      = Matrix.updateCol (1 : Matrix ι ι K) j (fun i => e.repr v i) := by
    ext i l
    rw [Module.Basis.toMatrix_apply, Matrix.updateCol_apply, Function.update_apply]
    by_cases hl : l = j
    · simp [hl]
    · rcases eq_or_ne i l with rfl | hil
      · simp [hl, Module.Basis.repr_self]
      · simp [hl, Module.Basis.repr_self, Matrix.one_apply_ne hil, Ne.symm hil]
  rw [Module.Basis.det_apply, hm]
  exact key _

theorem span_image_update_sum_eq {R : Type*} [CommRing R] {ι : Type*} [DecidableEq ι]
    (y : ι → R) (S : Finset ι) (a : ι → R) (j : ι) (hj : j ∈ S) (ha : IsUnit (a j)) :
    Ideal.span (Function.update y j (∑ i ∈ S, a i * y i) '' (S : Set ι)) =
      Ideal.span (y '' (S : Set ι)) := by
  have hzj : Function.update y j (∑ t ∈ S, a t * y t) j = ∑ t ∈ S, a t * y t := by
    simp
  have hzne : ∀ i : ι, i ≠ j →
      Function.update y j (∑ t ∈ S, a t * y t) i = y i := by
    intro i hi
    rw [Function.update_apply, if_neg hi]
  have hsplit : ∑ t ∈ S, a t * y t = a j * y j + ∑ t ∈ S.erase j, a t * y t :=
    (Finset.add_sum_erase S (fun t => a t * y t) hj).symm
  have key1 : ∀ i ∈ S, Function.update y j (∑ t ∈ S, a t * y t) i
      ∈ Ideal.span (y '' (S : Set ι)) := by
    intro i hi
    by_cases h : i = j
    · rw [h, hzj]
      exact Ideal.sum_mem _ fun t ht =>
        Ideal.mul_mem_left _ _
          (Ideal.subset_span (Set.mem_image_of_mem y (Finset.mem_coe.mpr ht)))
    · rw [hzne i h]
      exact Ideal.subset_span (Set.mem_image_of_mem y (Finset.mem_coe.mpr hi))
  have hmemj : a j * y j ∈
      Ideal.span (Function.update y j (∑ t ∈ S, a t * y t) '' (S : Set ι)) := by
    have h1 : a j * y j
        = Function.update y j (∑ t ∈ S, a t * y t) j - ∑ t ∈ S.erase j, a t * y t := by
      rw [hzj, hsplit]; ring
    rw [h1]
    refine Submodule.sub_mem _
      (Ideal.subset_span (Set.mem_image_of_mem _ (Finset.mem_coe.mpr hj))) ?_
    refine Ideal.sum_mem _ fun t ht => Ideal.mul_mem_left _ _ ?_
    rw [← hzne t (Finset.ne_of_mem_erase ht)]
    exact Ideal.subset_span
      (Set.mem_image_of_mem _ (Finset.mem_coe.mpr (Finset.mem_of_mem_erase ht)))
  have key2 : ∀ i ∈ S, y i ∈
      Ideal.span (Function.update y j (∑ t ∈ S, a t * y t) '' (S : Set ι)) := by
    intro i hi
    by_cases h : i = j
    · obtain ⟨u, hu⟩ := ha
      have hyj : y j = (↑u⁻¹ : R) * (a j * y j) := by
        rw [← mul_assoc, ← hu, Units.inv_mul, one_mul]
      rw [h, hyj]
      exact Ideal.mul_mem_left _ _ hmemj
    · rw [← hzne i h]
      exact Ideal.subset_span (Set.mem_image_of_mem _ (Finset.mem_coe.mpr hi))
  refine le_antisymm (Ideal.span_le.mpr ?_) (Ideal.span_le.mpr ?_)
  · rintro _ ⟨i, hi, rfl⟩
    exact SetLike.mem_coe.mpr (key1 i (Finset.mem_coe.mp hi))
  · rintro _ ⟨i, hi, rfl⟩
    exact SetLike.mem_coe.mpr (key2 i (Finset.mem_coe.mp hi))

theorem exists_basis_isUnit_det_of_isLocalization {k : Type*} [Field k] {ι : Type*} [Fintype ι]
    [DecidableEq ι] {S : Type*} [CommRing S] [Algebra k S] [Algebra (MvPolynomial ι k) S]
    [IsScalarTower k (MvPolynomial ι k) S] [Algebra.FormallyEtale (MvPolynomial ι k) S]
    {S' : Type*} [CommRing S'] [Algebra S S'] [Algebra k S'] [IsScalarTower k S S']
    (M : Submonoid S) [IsLocalization M S'] (v : ι → S)
    (h : IsUnit (algebraMap S S'
      ((EtaleCoordinates.basisKaehler k ι S).det
        fun i : ι => KaehlerDifferential.D k S (v i)))) :
    ∃ e : Module.Basis ι S' (KaehlerDifferential k S'),
      IsUnit (e.det fun i : ι =>
        KaehlerDifferential.D k S' (algebraMap S S' (v i))) := by
  let instPS' : Algebra (MvPolynomial ι k) S' :=
    ((algebraMap S S').comp (algebraMap (MvPolynomial ι k) S)).toAlgebra
  have instT1 : IsScalarTower (MvPolynomial ι k) S S' :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  have t2Space_cuspAdeles : IsScalarTower k (MvPolynomial ι k) S' :=
    IsScalarTower.of_algebraMap_eq fun x => by
      rw [IsScalarTower.algebraMap_apply k S S' x,
        IsScalarTower.algebraMap_apply k (MvPolynomial ι k) S x]
      rfl
  have instFEloc : Algebra.FormallyEtale S S' :=
    Algebra.FormallyEtale.of_isLocalization (M := M)
  have instFormallyEtale : Algebra.FormallyEtale (MvPolynomial ι k) S' :=
    Algebra.FormallyEtale.comp (MvPolynomial ι k) S S'
  refine ⟨EtaleCoordinates.basisKaehler k ι S', ?_⟩
  rw [← EtaleCoordinates.algebraMap_det_basisKaehler k ι S S' v]
  exact h

theorem notMem_basicOpen_of_mem_primeIdealOf {X : Scheme.{u}} {U : X.Opens}
    (hU : IsAffineOpen U) {x : X} (hx : x ∈ U) (f : Γ(X, U))
    (hf : f ∈ (hU.primeIdealOf ⟨x, hx⟩).asIdeal) : x ∉ X.basicOpen f := by
  intro hmem
  have h1 : hU.fromSpec.base (hU.primeIdealOf ⟨x, hx⟩) = x :=
    hU.fromSpec_primeIdealOf ⟨x, hx⟩
  have h2 : hU.primeIdealOf ⟨x, hx⟩ ∈ hU.fromSpec ⁻¹ᵁ X.basicOpen f := by
    show hU.fromSpec.base (hU.primeIdealOf ⟨x, hx⟩) ∈ X.basicOpen f
    rw [h1]
    exact hmem
  rw [hU.fromSpec_preimage_basicOpen] at h2
  exact (PrimeSpectrum.mem_basicOpen f _).mp h2 hf

private theorem map_germ_primeIdealOf_eq_maximalIdeal {X : Scheme.{u}} {U : X.Opens}
    (hU : IsAffineOpen U) {x : X} (hx : x ∈ U) :
    Ideal.map (X.presheaf.germ U x hx).hom (hU.primeIdealOf ⟨x, hx⟩).asIdeal =
      IsLocalRing.maximalIdeal (X.presheaf.stalk x) := by
  let instAlgStalk : Algebra Γ(X, U) (X.presheaf.stalk x) :=
    (X.presheaf.germ U x hx).hom.toAlgebra
  have instLocStalk : IsLocalization.AtPrime (X.presheaf.stalk x)
      (hU.primeIdealOf ⟨x, hx⟩).asIdeal := hU.isLocalization_stalk ⟨x, hx⟩
  have h : Ideal.map (algebraMap Γ(X, U) (X.presheaf.stalk x))
      (hU.primeIdealOf ⟨x, hx⟩).asIdeal = IsLocalRing.maximalIdeal (X.presheaf.stalk x) :=
    IsLocalization.AtPrime.map_eq_maximalIdeal (hU.primeIdealOf ⟨x, hx⟩).asIdeal
      (X.presheaf.stalk x)
  exact h

theorem mem_support_of_ideal_le_primeIdealOf {X : Scheme.{u}} (D : X.IdealSheafData) {U : X.Opens}
    (hU : IsAffineOpen U) {x : X} (hx : x ∈ U)
    (h : D.ideal ⟨U, hU⟩ ≤ (hU.primeIdealOf ⟨x, hx⟩).asIdeal) : x ∈ D.support := by
  rw [mem_support_iff_stalkIdeal_le_maximalIdeal, stalkIdeal_eq_map_germ D x ⟨U, hU⟩ hx]
  refine le_trans (Ideal.map_mono h) ?_
  exact le_of_eq (map_germ_primeIdealOf_eq_maximalIdeal hU hx)

private theorem appLE_top_eq_topIso_inv {X₁ : Scheme.{u}} (V : X₁.Opens)
    (e : (⊤ : (V.toScheme).Opens) ≤ V.ι ⁻¹ᵁ V) :
    V.ι.appLE V ⊤ e = V.topIso.inv := by
  simp
  exact Scheme.presheaf_map_eq_of_parallel ..

private theorem eq_of_ideal_map_topIso_inv_eq {X₁ : Scheme.{u}} (V : X₁.Opens)
    {J₁ J₂ : Ideal Γ(X₁, V)}
    (hJ : Ideal.map V.topIso.inv.hom J₁ = Ideal.map V.topIso.inv.hom J₂) : J₁ = J₂ := by
  have hid : (V.topIso.hom.hom).comp (V.topIso.inv.hom) = RingHom.id _ := by
    ext x
    exact V.topIso.inv_hom_id_apply x
  have key : ∀ J : Ideal Γ(X₁, V),
      Ideal.map V.topIso.hom.hom (Ideal.map V.topIso.inv.hom J) = J := by
    intro J
    rw [Ideal.map_map, hid, Ideal.map_id]
  rw [← key J₁, hJ, key J₂]

theorem ideal_eq_span_image_map_of_le {X : Scheme.{u}} (D : X.IdealSheafData) {U U' : X.Opens}
    (hU : IsAffineOpen U) (hU' : IsAffineOpen U') (h : U' ≤ U) (s : Set Γ(X, U))
    (hs : D.ideal ⟨U, hU⟩ = Ideal.span s) :
    D.ideal ⟨U', hU'⟩ = Ideal.span ((X.presheaf.map (homOfLE h).op).hom '' s) := by
  have hU'aff : IsAffine U'.toScheme := hU'
  have htop : IsAffineOpen (⊤ : (U'.toScheme).Opens) := isAffineOpen_top U'.toScheme
  have e2 : (⊤ : (U'.toScheme).Opens) ≤ U'.ι ⁻¹ᵁ U' := by
    intro x _
    exact x.2
  have e1 : (⊤ : (U'.toScheme).Opens) ≤ U'.ι ⁻¹ᵁ U := by
    intro x _
    exact h x.2
  have key1 : (D.comap U'.ι).ideal ⟨⊤, htop⟩
      = Ideal.map (U'.ι.appLE U ⊤ e1).hom (D.ideal ⟨U, hU⟩) :=
    D.comap_ideal_eq_map_appLE U'.ι ⟨U, hU⟩ ⟨⊤, htop⟩ e1
  have key2 : (D.comap U'.ι).ideal ⟨⊤, htop⟩
      = Ideal.map (U'.ι.appLE U' ⊤ e2).hom (D.ideal ⟨U', hU'⟩) :=
    D.comap_ideal_eq_map_appLE U'.ι ⟨U', hU'⟩ ⟨⊤, htop⟩ e2
  have happ : U'.ι.appLE U ⊤ e1 = X.presheaf.map (homOfLE h).op ≫ U'.ι.appLE U' ⊤ e2 := by
    rw [Scheme.Hom.map_appLE]
  have hmain : D.ideal ⟨U', hU'⟩
      = Ideal.map (X.presheaf.map (homOfLE h).op).hom (D.ideal ⟨U, hU⟩) := by
    refine eq_of_ideal_map_topIso_inv_eq U' ?_
    rw [← appLE_top_eq_topIso_inv U' e2, ← key2, key1, happ, CommRingCat.hom_comp,
      ← Ideal.map_map]
  rw [hmain, hs, Ideal.map_span]

def IsCoordLabeling {X : Scheme.{u}} {k : Type u} [Field k] {p : X ⟶ Spec (CommRingCat.of k)}
    {U : X.Opens} {m : ℕ} (c : EtaleChart p U m) (lab : ℕ → Option (Fin m))
    (N : List X.IdealSheafData) : Prop :=
  ∀ i : ℕ, ∀ hi : i < N.length,
    (lab i = none → restrictIdeal (N[i]'hi) U = ⊤) ∧
    (∀ j : Fin m, lab i = some j → restrictIdeal (N[i]'hi) U = c.coordIdeal {j})

def LabelingInjective {m : ℕ} (lab : ℕ → Option (Fin m)) (n : ℕ) : Prop :=
  ∀ i i' : ℕ, i < n → i' < n → ∀ j : Fin m, lab i = some j → lab i' = some j → i = i'

theorem exists_etaleCharts_of_inStrictNormalCrossingPosition_cons {X : Scheme.{u}} {k : Type u} [Field k]
    (p : X ⟶ Spec (CommRingCat.of k)) (Z H : X.IdealSheafData) (N : List X.IdealSheafData)
    (hN : InStrictNormalCrossingPosition p (H :: N)) (hZ : HasStrictNormalCrossingsWith p Z N) (hHZ : H ≤ Z)
    (x : X) (hx : x ∈ Z.support) :
    ∃ (U : X.Opens) (_ : IsAffineOpen U) (_ : x ∈ U) (m : ℕ) (c : EtaleChart p U m)
      (lab : ℕ → Option (Fin m)) (S : Finset (Fin m)) (m' : ℕ) (c' : EtaleChart p U m')
      (j0 : Fin m') (lab' : ℕ → Option (Fin m')),
      restrictIdeal Z U = c.coordIdeal S ∧
      restrictIdeal H U = c'.coordIdeal {j0} ∧
      IsCoordLabeling c lab N ∧
      LabelingInjective lab N.length ∧
      IsCoordLabeling c' (fun i => lab' (i + 1)) N ∧
      (∀ i : ℕ, i < N.length → lab' (i + 1) ≠ some j0) := by
  obtain ⟨U₁, hxU₁, m₁, c₁, a₁, S₁, hinj₁, hnone₁, hsome₁, hZU₁⟩ := hZ.exists_etaleChart hx
  have hptN := ((inStrictNormalCrossingPosition_iff p (H :: N)).mp hN).2 x
  obtain ⟨U₂, hxU₂, m₂, c₂, a₂, hinj₂, hnone₂, hsome₂⟩ := hptN.exists_etaleChart
  obtain ⟨V, hVaff, hxV, hVW⟩ := exists_isAffineOpen_mem_and_subset (U := U₁ ⊓ U₂) ⟨hxU₁, hxU₂⟩
  have hVU₁ : V ≤ U₁ := le_trans hVW inf_le_left
  have hVU₂ : V ≤ U₂ := le_trans hVW inf_le_right
  have hlen0 : 0 < (H :: N).length := by simp
  have hHsupp : x ∈ H.support := Scheme.IdealSheafData.support_antitone hHZ hx
  obtain ⟨j0, hj0⟩ : ∃ j0 : Fin m₂, a₂ 0 = some j0 := by
    cases hcase : a₂ 0 with
    | none =>
        exfalso
        have h := hnone₂ 0 hlen0 hcase
        simp only [List.getElem_cons_zero] at h
        exact notMem_support_of_mem_opens_of_restrictIdeal_eq_top H U₂ h x hxU₂ hHsupp
    | some j => exact ⟨j, rfl⟩
  refine ⟨V, hVaff, hxV, m₁, c₁.restrict hVU₁, a₁, S₁, m₂, c₂.restrict hVU₂, j0, a₂,
    restrictIdeal_eq_restrict_coordIdeal_of_le hVU₁ c₁ Z S₁ hZU₁, ?_, ?_, ?_, ?_, ?_⟩
  · have h := hsome₂ 0 hlen0 j0 hj0
    simp only [List.getElem_cons_zero] at h
    exact restrictIdeal_eq_restrict_coordIdeal_of_le hVU₂ c₂ H {j0} h
  · intro i hi
    refine ⟨fun hn => ?_, fun j hs => ?_⟩
    · exact restrictIdeal_eq_top_of_le (N[i]'hi) hVU₁ (hnone₁ i hi hn)
    · exact restrictIdeal_eq_restrict_coordIdeal_of_le hVU₁ c₁ (N[i]'hi) {j} (hsome₁ i hi j hs)
  · intro i i' hi hi' j h h'
    exact hinj₁ i hi i' hi' j h h'
  · intro i hi
    have hi' : i + 1 < (H :: N).length := by
      simp only [List.length_cons]
      omega
    refine ⟨fun hn => ?_, fun j hs => ?_⟩
    · have h := hnone₂ (i + 1) hi' hn
      simp only [List.getElem_cons_succ] at h
      exact restrictIdeal_eq_top_of_le (N[i]'hi) hVU₂ h
    · have h := hsome₂ (i + 1) hi' j hs
      simp only [List.getElem_cons_succ] at h
      exact restrictIdeal_eq_restrict_coordIdeal_of_le hVU₂ c₂ (N[i]'hi) {j} h
  · intro i hi hcon
    have hi' : i + 1 < (H :: N).length := by
      simp only [List.length_cons]
      omega
    have hzero := hinj₂ (i + 1) hi' 0 hlen0 j0 hcon hj0
    omega

private theorem exists_coeffs_of_mem_span_image {R : Type*} [CommRing R] {ι : Type*}
    [DecidableEq ι] (y : ι → R) (S : Finset ι) (z : R)
    (hz : z ∈ Ideal.span (y '' (S : Set ι))) :
    ∃ a : ι → R, z = ∑ j ∈ S, a j * y j := by
  classical
  have hle : Ideal.span (y '' (S : Set ι)) ≤
      ({ carrier := {w : R | ∃ a : ι → R, w = ∑ j ∈ S, a j * y j}
         add_mem' := by
           rintro u v ⟨au, rfl⟩ ⟨av, rfl⟩
           refine ⟨fun i => au i + av i, ?_⟩
           rw [← Finset.sum_add_distrib]
           exact Finset.sum_congr rfl fun i _ => by ring
         zero_mem' := ⟨0, by simp⟩
         smul_mem' := by
           rintro r u ⟨au, rfl⟩
           refine ⟨fun i => r * au i, ?_⟩
           rw [smul_eq_mul, Finset.mul_sum]
           exact Finset.sum_congr rfl fun i _ => by ring } : Ideal R) := by
    rw [Ideal.span_le]
    rintro w ⟨j, hj, rfl⟩
    have hjS : j ∈ S := Finset.mem_coe.mp hj
    refine ⟨fun i => if i = j then 1 else 0, ?_⟩
    rw [Finset.sum_eq_single_of_mem j hjS]
    · simp
    · intro i _ hij
      simp [hij]
  exact hle hz

private theorem ideal_eq_span_coord_of_restrictIdeal_eq {X : Scheme.{u}} {k : Type u} [Field k]
    {p : X ⟶ Spec (CommRingCat.of k)} {U : X.Opens} (hU : IsAffineOpen U) {m : ℕ}
    (c : EtaleChart p U m) (I : X.IdealSheafData) (j : Fin m)
    (h : restrictIdeal I U = c.coordIdeal {j}) :
    I.ideal ⟨U, hU⟩ = Ideal.span ({c.coord j} : Set Γ(X, U)) := by
  rw [c.ideal_eq_span_coord hU I {j} h, Finset.coe_singleton, Set.image_singleton]

theorem exists_coord_eq_sum_coeff_not_mem_of_le {X : Scheme.{u}} {k : Type u} [Field k]
    (p : X ⟶ Spec (CommRingCat.of k)) [AlgebraicGeometry.Smooth p] {U : X.Opens}
    (hU : IsAffineOpen U) {x : X} (hx : x ∈ U) {m : ℕ} (c : EtaleChart p U m)
    (lab : ℕ → Option (Fin m)) (S : Finset (Fin m)) {m' : ℕ} (c' : EtaleChart p U m')
    (j0 : Fin m') (lab' : ℕ → Option (Fin m')) (Z H : X.IdealSheafData)
    (N : List X.IdealSheafData)
    (hxZ : x ∈ Z.support)
    (hlab : IsCoordLabeling c lab N)
    (hZU : restrictIdeal Z U = c.coordIdeal S)
    (hHU : restrictIdeal H U = c'.coordIdeal {j0})
    (hlab' : IsCoordLabeling c' (fun i => lab' (i + 1)) N)
    (hj0 : ∀ i : ℕ, i < N.length → lab' (i + 1) ≠ some j0)
    (hHZ : H ≤ Z) :
    ∃ a : Fin m → Γ(X, U),
      c'.coord j0 = ∑ j ∈ S, a j * c.coord j ∧
      ∃ j ∈ S, a j ∉ (hU.primeIdealOf ⟨x, hx⟩).asIdeal ∧
        ∀ i : ℕ, i < N.length → lab i ≠ some j := by
  classical
  let instAlgBase : Algebra k Γ(X, U) := sectionsAlgebra k p U
  let instAlgPoly : Algebra (MvPolynomial (ULift.{u} (Fin m')) k) Γ(X, U) := c'.algebra
  have instTower : IsScalarTower k (MvPolynomial (ULift.{u} (Fin m')) k) Γ(X, U) :=
    c'.isScalarTower
  have instFormallyEtale : Algebra.FormallyEtale (MvPolynomial (ULift.{u} (Fin m')) k) Γ(X, U) :=
    c'.algebra_formallyEtale hU
  obtain ⟨D, hD1, hD0⟩ : ∃ D : Derivation k Γ(X, U) Γ(X, U),
      D (c'.coord j0) = 1 ∧ ∀ t : Fin m', t ≠ j0 → D (c'.coord t) = 0 := by
    refine ⟨EtaleCoordinates.partialDeriv k (ULift.{u} (Fin m')) Γ(X, U) (ULift.up j0), ?_, ?_⟩
    · rw [← c'.etaleCoordinates_coord j0]
      exact EtaleCoordinates.partialDeriv_coord_self k (ULift.{u} (Fin m')) Γ(X, U)
        (ULift.up j0)
    · intro t ht
      rw [← c'.etaleCoordinates_coord t]
      exact EtaleCoordinates.partialDeriv_coord_of_ne k (ULift.{u} (Fin m')) Γ(X, U)
        (ULift.up j0) (ULift.up t) (fun hcon => ht (congrArg ULift.down hcon).symm)
  have hZideal : Z.ideal ⟨U, hU⟩ = Ideal.span (c.coord '' (S : Set (Fin m))) :=
    c.ideal_eq_span_coord hU Z S hZU
  have hZP : Z.ideal ⟨U, hU⟩ ≤ (hU.primeIdealOf ⟨x, hx⟩).asIdeal :=
    ideal_le_primeIdealOf Z hU hx hxZ
  have hcP : ∀ j ∈ S, c.coord j ∈ (hU.primeIdealOf ⟨x, hx⟩).asIdeal := by
    intro j hj
    refine hZP ?_
    rw [hZideal]
    exact Ideal.subset_span ⟨j, Finset.mem_coe.mpr hj, rfl⟩
  have hHideal : H.ideal ⟨U, hU⟩ = Ideal.span ({c'.coord j0} : Set Γ(X, U)) :=
    ideal_eq_span_coord_of_restrictIdeal_eq hU c' H j0 hHU
  obtain ⟨a, ha⟩ : ∃ a : Fin m → Γ(X, U), c'.coord j0 = ∑ j ∈ S, a j * c.coord j := by
    refine exists_coeffs_of_mem_span_image c.coord S (c'.coord j0) ?_
    rw [← hZideal]
    refine hHZ ⟨U, hU⟩ ?_
    rw [hHideal]
    exact Ideal.subset_span rfl
  refine ⟨a, ha, ?_⟩
  by_cases hex : ∃ j ∈ S, a j ∉ (hU.primeIdealOf ⟨x, hx⟩).asIdeal ∧
      ∀ i : ℕ, i < N.length → lab i ≠ some j
  · exact hex
  · exfalso
    have hlabelMem : ∀ j ∈ S, ∀ i : ℕ, i < N.length → lab i = some j →
        D (c.coord j) ∈ (hU.primeIdealOf ⟨x, hx⟩).asIdeal := by
      intro j hjS i hi hli
      obtain ⟨-, hsome⟩ := hlab i hi
      have hNideal : (N[i]'hi).ideal ⟨U, hU⟩ = Ideal.span ({c.coord j} : Set Γ(X, U)) :=
        ideal_eq_span_coord_of_restrictIdeal_eq hU c (N[i]'hi) j (hsome j hli)
      have hNle : (N[i]'hi).ideal ⟨U, hU⟩ ≤ (hU.primeIdealOf ⟨x, hx⟩).asIdeal := by
        rw [hNideal, Ideal.span_le, Set.singleton_subset_iff]
        exact hcP j hjS
      obtain ⟨hnone', hsome'⟩ := hlab' i hi
      cases hlv : lab' (i + 1) with
      | none =>
          exact absurd (mem_support_of_ideal_le_primeIdealOf (N[i]'hi) hU hx hNle)
            (notMem_support_of_mem_opens_of_restrictIdeal_eq_top (N[i]'hi) U (hnone' hlv) x hx)
      | some t =>
          have htj0 : t ≠ j0 := fun hcon =>
            hj0 i hi (hlv.trans (congrArg Option.some hcon))
          have hNideal' : (N[i]'hi).ideal ⟨U, hU⟩ = Ideal.span ({c'.coord t} : Set Γ(X, U)) :=
            ideal_eq_span_coord_of_restrictIdeal_eq hU c' (N[i]'hi) t (hsome' t hlv)
          have hct : c'.coord t ∈ (hU.primeIdealOf ⟨x, hx⟩).asIdeal := by
            refine hNle ?_
            rw [hNideal']
            exact Ideal.subset_span rfl
          have hmem : c.coord j ∈ Ideal.span ({c'.coord t} : Set Γ(X, U)) := by
            rw [← hNideal', hNideal]
            exact Ideal.subset_span rfl
          obtain ⟨v, hv⟩ := Ideal.mem_span_singleton'.mp hmem
          have hDv : D (c.coord j) = c'.coord t * D v := by
            rw [← hv, Derivation.leibniz, hD0 t htj0, smul_zero, zero_add, smul_eq_mul]
          rw [hDv]
          exact Ideal.mul_mem_right _ _ hct
    have hone : (1 : Γ(X, U)) ∈ (hU.primeIdealOf ⟨x, hx⟩).asIdeal := by
      have hsum : (1 : Γ(X, U)) = ∑ j ∈ S, (a j * D (c.coord j) + c.coord j * D (a j)) := by
        calc (1 : Γ(X, U)) = D (c'.coord j0) := hD1.symm
          _ = D (∑ j ∈ S, a j * c.coord j) := by rw [ha]
          _ = ∑ j ∈ S, D (a j * c.coord j) := map_sum D (fun j => a j * c.coord j) S
          _ = ∑ j ∈ S, (a j * D (c.coord j) + c.coord j * D (a j)) := by
              refine Finset.sum_congr rfl fun j _ => ?_
              simp only [Derivation.leibniz, smul_eq_mul]
      rw [hsum]
      refine Ideal.sum_mem _ fun j hj => add_mem ?_ ?_
      · by_cases hlj : ∃ i : ℕ, i < N.length ∧ lab i = some j
        · obtain ⟨i, hi, hli⟩ := hlj
          exact Ideal.mul_mem_left _ _ (hlabelMem j hj i hi hli)
        · have haj : a j ∈ (hU.primeIdealOf ⟨x, hx⟩).asIdeal := by
            by_contra hajP
            exact hex ⟨j, hj, hajP, fun i hi hli => hlj ⟨i, hi, hli⟩⟩
          exact Ideal.mul_mem_right _ _ haj
      · exact Ideal.mul_mem_right _ _ (hcP j hj)
    exact (hU.primeIdealOf ⟨x, hx⟩).isPrime.ne_top ((Ideal.eq_top_iff_one _).mpr hone)

theorem basisKaehler_apply_eq_D_coord {X : Scheme.{u}} {k : Type u} [Field k]
    {p : X ⟶ Spec (CommRingCat.of k)} {U : X.Opens} {m : ℕ} (c : EtaleChart p U m)
    [Algebra k Γ(X, U)] [Algebra (MvPolynomial (ULift.{u} (Fin m)) k) Γ(X, U)]
    [IsScalarTower k (MvPolynomial (ULift.{u} (Fin m)) k) Γ(X, U)]
    [Algebra.FormallyEtale (MvPolynomial (ULift.{u} (Fin m)) k) Γ(X, U)]
    (_hk : algebraMap k Γ(X, U) = sectionsAlgebraMap k p U)
    (hc : algebraMap (MvPolynomial (ULift.{u} (Fin m)) k) Γ(X, U) = c.coordRingHom)
    (j : Fin m) :
    EtaleCoordinates.basisKaehler k (ULift.{u} (Fin m)) Γ(X, U) (ULift.up j) =
      KaehlerDifferential.D k Γ(X, U) (c.coord j) := by
  rw [EtaleCoordinates.basisKaehler_apply, EtaleCoordinates.coord_def, hc,
    EtaleChart.coordRingHom_X]

theorem ringHom_etale_of_formallyEtale {X : Scheme.{u}} {k : Type u} [Field k]
    (p : X ⟶ Spec (CommRingCat.of k)) [AlgebraicGeometry.Smooth p] {V : X.Opens}
    (hV : IsAffineOpen V) {m : ℕ}
    (f : MvPolynomial (ULift.{u} (Fin m)) k →+* Γ(X, V))
    (hC : ∀ a : k, f (MvPolynomial.C a) = sectionsAlgebraMap k p V a)
    (hf : @Algebra.FormallyEtale (MvPolynomial (ULift.{u} (Fin m)) k) Γ(X, V) _ _
      f.toAlgebra) :
    f.Etale := by
  let instP : Algebra (MvPolynomial (ULift.{u} (Fin m)) k) Γ(X, V) := f.toAlgebra
  let instk : Algebra k Γ(X, V) := sectionsAlgebra k p V
  have hk : (algebraMap k Γ(X, V)) = sectionsAlgebraMap k p V :=
    algebraMap_sectionsAlgebra k p V
  have h1 : (algebraMap (MvPolynomial (ULift.{u} (Fin m)) k) Γ(X, V)) = f := rfl
  have instTower : IsScalarTower k (MvPolynomial (ULift.{u} (Fin m)) k) Γ(X, V) := by
    refine IsScalarTower.of_algebraMap_eq fun a => ?_
    rw [hk, h1, MvPolynomial.algebraMap_eq, hC]
  have instFiniteType : Algebra.FiniteType k Γ(X, V) := finiteType_sections k p ⟨V, hV⟩ hk
  have hFTp : Algebra.FiniteType (MvPolynomial (ULift.{u} (Fin m)) k) Γ(X, V) := by
    obtain ⟨t, ht⟩ := instFiniteType.out
    refine ⟨⟨t, ?_⟩⟩
    rw [Algebra.eq_top_iff]
    intro x
    have hx : x ∈ Algebra.adjoin k (↑t : Set Γ(X, V)) := by
      rw [ht]
      exact Algebra.mem_top
    have hle : Algebra.adjoin k (↑t : Set Γ(X, V)) ≤
        Subalgebra.restrictScalars k
          (Algebra.adjoin (MvPolynomial (ULift.{u} (Fin m)) k) (↑t : Set Γ(X, V))) :=
      Algebra.adjoin_le Algebra.subset_adjoin
    exact hle hx
  have hFP : Algebra.FinitePresentation (MvPolynomial (ULift.{u} (Fin m)) k) Γ(X, V) := by
    rw [← Algebra.FinitePresentation.of_finiteType]
    exact hFTp
  have hEt : @Algebra.Etale (MvPolynomial (ULift.{u} (Fin m)) k) Γ(X, V) _ _ instP :=
    ⟨hf, hFP⟩
  exact hEt

theorem exists_etaleChart_update_coord {X : Scheme.{u}} {k : Type u} [Field k]
    (p : X ⟶ Spec (CommRingCat.of k)) [AlgebraicGeometry.Smooth p] {U : X.Opens}
    (hU : IsAffineOpen U) {m : ℕ} (c : EtaleChart p U m) {x : X} (hx : x ∈ U)
    (S : Finset (Fin m)) (a : Fin m → Γ(X, U)) (j : Fin m) (hjS : j ∈ S)
    (hS : ∀ i ∈ S, c.coord i ∈ (hU.primeIdealOf ⟨x, hx⟩).asIdeal)
    (haj : a j ∉ (hU.primeIdealOf ⟨x, hx⟩).asIdeal) :
    ∃ (V : X.Opens) (_ : IsAffineOpen V) (hVU : V ≤ U) (_ : x ∈ V) (c' : EtaleChart p V m),
      (∀ i : Fin m, i ≠ j →
          c'.coord i = (X.presheaf.map (homOfLE hVU).op).hom (c.coord i)) ∧
      c'.coord j = (X.presheaf.map (homOfLE hVU).op).hom (∑ i ∈ S, a i * c.coord i) ∧
      IsUnit ((X.presheaf.map (homOfLE hVU).op).hom (a j)) := by
  classical
  let instAlgU : Algebra k Γ(X, U) := sectionsAlgebra k p U
  let instPolyU : Algebra (MvPolynomial (ULift.{u} (Fin m)) k) Γ(X, U) := c.algebra
  have instTowerU : IsScalarTower k (MvPolynomial (ULift.{u} (Fin m)) k) Γ(X, U) :=
    c.isScalarTower
  have instFEU : Algebra.FormallyEtale (MvPolynomial (ULift.{u} (Fin m)) k) Γ(X, U) :=
    c.algebra_formallyEtale hU
  obtain ⟨v, hvj, hvne⟩ : ∃ v : ULift.{u} (Fin m) → Γ(X, U),
      v (ULift.up j) = ∑ i ∈ S, a i * c.coord i ∧
        ∀ i : ULift.{u} (Fin m), i ≠ ULift.up j → v i = c.coord i.down := by
    refine ⟨Function.update (fun i : ULift.{u} (Fin m) => c.coord i.down) (ULift.up j)
      (∑ i ∈ S, a i * c.coord i), ?_, fun i hi => ?_⟩
    · rw [Function.update_apply, if_pos rfl]
    · rw [Function.update_apply, if_neg hi]
  have hBcoord : ∀ i : ULift.{u} (Fin m),
      EtaleCoordinates.basisKaehler k (ULift.{u} (Fin m)) Γ(X, U) i =
        KaehlerDifferential.D k Γ(X, U) (c.coord i.down) := fun i =>
    basisKaehler_apply_eq_D_coord c (algebraMap_sectionsAlgebra k p U)
      (EtaleChart.algebraMap_eq_coordRingHom c) i.down
  have hfam : (fun i : ULift.{u} (Fin m) => KaehlerDifferential.D k Γ(X, U) (v i)) =
      Function.update (⇑(EtaleCoordinates.basisKaehler k (ULift.{u} (Fin m)) Γ(X, U)))
        (ULift.up j) (KaehlerDifferential.D k Γ(X, U) (∑ i ∈ S, a i * c.coord i)) := by
    funext i
    by_cases hi : i = ULift.up j
    · rw [Function.update_apply, if_pos hi, hi, hvj]
    · rw [Function.update_apply, if_neg hi, hvne i hi, hBcoord i]
  have hdeteq : (EtaleCoordinates.basisKaehler k (ULift.{u} (Fin m)) Γ(X, U)).det
        (fun i : ULift.{u} (Fin m) => KaehlerDifferential.D k Γ(X, U) (v i)) =
      EtaleCoordinates.partialDeriv k (ULift.{u} (Fin m)) Γ(X, U) (ULift.up j)
        (∑ i ∈ S, a i * c.coord i) := by
    rw [hfam, det_update_eq_repr, EtaleCoordinates.partialDeriv_apply]
  have hDself : EtaleCoordinates.partialDeriv k (ULift.{u} (Fin m)) Γ(X, U) (ULift.up j)
      (c.coord j) = 1 := by
    rw [← c.etaleCoordinates_coord j]
    exact EtaleCoordinates.partialDeriv_coord_self k (ULift.{u} (Fin m)) Γ(X, U) (ULift.up j)
  have hDne : ∀ i : Fin m, i ≠ j →
      EtaleCoordinates.partialDeriv k (ULift.{u} (Fin m)) Γ(X, U) (ULift.up j)
        (c.coord i) = 0 := by
    intro i hi
    rw [← c.etaleCoordinates_coord i]
    exact EtaleCoordinates.partialDeriv_coord_of_ne k (ULift.{u} (Fin m)) Γ(X, U)
      (ULift.up j) (ULift.up i) (fun h => hi (congrArg ULift.down h).symm)
  have hsumeq : EtaleCoordinates.partialDeriv k (ULift.{u} (Fin m)) Γ(X, U) (ULift.up j)
        (∑ i ∈ S, a i * c.coord i) =
      a j + ∑ i ∈ S, c.coord i *
        EtaleCoordinates.partialDeriv k (ULift.{u} (Fin m)) Γ(X, U) (ULift.up j) (a i) := by
    have h3 : ∀ i ∈ S, i ≠ j →
        a i * EtaleCoordinates.partialDeriv k (ULift.{u} (Fin m)) Γ(X, U) (ULift.up j)
          (c.coord i) = 0 := by
      intro i _ hij
      rw [hDne i hij, mul_zero]
    have h1 : EtaleCoordinates.partialDeriv k (ULift.{u} (Fin m)) Γ(X, U) (ULift.up j)
          (∑ i ∈ S, a i * c.coord i) =
        (∑ i ∈ S, a i * EtaleCoordinates.partialDeriv k (ULift.{u} (Fin m)) Γ(X, U)
          (ULift.up j) (c.coord i)) +
          ∑ i ∈ S, c.coord i * EtaleCoordinates.partialDeriv k (ULift.{u} (Fin m)) Γ(X, U)
            (ULift.up j) (a i) := by
      rw [map_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      simp only [Derivation.leibniz, smul_eq_mul]
    rw [h1, Finset.sum_eq_single_of_mem j hjS h3, hDself, mul_one]
  have hdetP : (EtaleCoordinates.basisKaehler k (ULift.{u} (Fin m)) Γ(X, U)).det
      (fun i : ULift.{u} (Fin m) => KaehlerDifferential.D k Γ(X, U) (v i)) ∉
      (hU.primeIdealOf ⟨x, hx⟩).asIdeal := by
    rw [hdeteq]
    intro hmem
    refine haj ?_
    have hrw : a j =
        EtaleCoordinates.partialDeriv k (ULift.{u} (Fin m)) Γ(X, U) (ULift.up j)
          (∑ i ∈ S, a i * c.coord i) -
          ∑ i ∈ S, c.coord i * EtaleCoordinates.partialDeriv k (ULift.{u} (Fin m)) Γ(X, U)
            (ULift.up j) (a i) := by
      rw [hsumeq]; ring
    rw [hrw]
    exact Submodule.sub_mem _ hmem
      (Ideal.sum_mem _ fun i hi => Ideal.mul_mem_right _ _ (hS i hi))
  obtain ⟨g, hgdef⟩ : ∃ g : Γ(X, U), g =
      (EtaleCoordinates.basisKaehler k (ULift.{u} (Fin m)) Γ(X, U)).det
        (fun i : ULift.{u} (Fin m) => KaehlerDifferential.D k Γ(X, U) (v i)) * a j := ⟨_, rfl⟩
  have hgP : g ∉ (hU.primeIdealOf ⟨x, hx⟩).asIdeal := by
    rw [hgdef]
    intro hmem
    rcases (hU.primeIdealOf ⟨x, hx⟩).isPrime.mem_or_mem hmem with h | h
    · exact hdetP h
    · exact haj h
  have hVaff : IsAffineOpen (X.basicOpen g) := hU.basicOpen g
  have hVU : X.basicOpen g ≤ U := X.basicOpen_le g
  have hxV : x ∈ X.basicOpen g := mem_basicOpen_of_notMem_primeIdealOf hU hx g hgP
  let instAlgV : Algebra k Γ(X, X.basicOpen g) := sectionsAlgebra k p (X.basicOpen g)
  have instLocV : IsLocalization (Submonoid.powers g) Γ(X, X.basicOpen g) :=
    hU.isLocalization_basicOpen g
  have instTowerV : IsScalarTower k Γ(X, U) Γ(X, X.basicOpen g) :=
    isScalarTower_sections k p U g (algebraMap_sectionsAlgebra k p U)
      (algebraMap_sectionsAlgebra k p (X.basicOpen g)) rfl
  have hgunit : IsUnit (algebraMap Γ(X, U) Γ(X, X.basicOpen g) g) :=
    IsLocalization.map_units (M := Submonoid.powers g) Γ(X, X.basicOpen g)
      ⟨g, Submonoid.mem_powers g⟩
  have hmul : algebraMap Γ(X, U) Γ(X, X.basicOpen g) g =
      algebraMap Γ(X, U) Γ(X, X.basicOpen g)
        ((EtaleCoordinates.basisKaehler k (ULift.{u} (Fin m)) Γ(X, U)).det
          (fun i : ULift.{u} (Fin m) => KaehlerDifferential.D k Γ(X, U) (v i))) *
        algebraMap Γ(X, U) Γ(X, X.basicOpen g) (a j) := by
    rw [← map_mul, ← hgdef]
  rw [hmul] at hgunit
  have hdetunit := isUnit_of_mul_isUnit_left hgunit
  have hajunit := isUnit_of_mul_isUnit_right hgunit
  obtain ⟨e, he⟩ := exists_basis_isUnit_det_of_isLocalization (Submonoid.powers g) v hdetunit
  obtain ⟨w, hw⟩ : ∃ w : ULift.{u} (Fin m) → Γ(X, X.basicOpen g),
      ∀ i : ULift.{u} (Fin m), w i = algebraMap Γ(X, U) Γ(X, X.basicOpen g) (v i) :=
    ⟨_, fun _ => rfl⟩
  have he' : IsUnit (e.det fun i : ULift.{u} (Fin m) =>
      KaehlerDifferential.D k Γ(X, X.basicOpen g) (w i)) := by
    have hfun : (fun i : ULift.{u} (Fin m) =>
        KaehlerDifferential.D k Γ(X, X.basicOpen g) (w i)) =
        fun i : ULift.{u} (Fin m) => KaehlerDifferential.D k Γ(X, X.basicOpen g)
          (algebraMap Γ(X, U) Γ(X, X.basicOpen g) (v i)) := by
      funext i
      rw [hw i]
    rw [hfun]
    exact he
  have instFSV : Algebra.FormallySmooth k Γ(X, X.basicOpen g) :=
    formallySmooth_sections k p (X.basicOpen g) hVaff
      (algebraMap_sectionsAlgebra k p (X.basicOpen g))
  have hformallyEtale := EtaleCoordinates.formallyEtale_aeval_of_isUnit_det e w he'
  have hC : ∀ b : k,
      ((MvPolynomial.aeval w :
          MvPolynomial (ULift.{u} (Fin m)) k →ₐ[k] Γ(X, X.basicOpen g)).toRingHom)
        (MvPolynomial.C b) = sectionsAlgebraMap k p (X.basicOpen g) b := by
    intro b
    have h1 : (MvPolynomial.aeval w :
        MvPolynomial (ULift.{u} (Fin m)) k →ₐ[k] Γ(X, X.basicOpen g)) (MvPolynomial.C b) =
        algebraMap k Γ(X, X.basicOpen g) b := MvPolynomial.aeval_C w b
    exact h1.trans (DFunLike.congr_fun (algebraMap_sectionsAlgebra k p (X.basicOpen g)) b)
  have hXv : ∀ i : ULift.{u} (Fin m),
      ((MvPolynomial.aeval w :
          MvPolynomial (ULift.{u} (Fin m)) k →ₐ[k] Γ(X, X.basicOpen g)).toRingHom)
        (MvPolynomial.X i) = w i := fun i => MvPolynomial.aeval_X w i
  have hetale : ((MvPolynomial.aeval w :
      MvPolynomial (ULift.{u} (Fin m)) k →ₐ[k] Γ(X, X.basicOpen g)).toRingHom).Etale :=
    ringHom_etale_of_formallyEtale p hVaff
      ((MvPolynomial.aeval w :
        MvPolynomial (ULift.{u} (Fin m)) k →ₐ[k] Γ(X, X.basicOpen g)).toRingHom) hC hformallyEtale
  obtain ⟨c', hc'⟩ := exists_etaleChart_coord_eq p hVaff w
    ((MvPolynomial.aeval w :
      MvPolynomial (ULift.{u} (Fin m)) k →ₐ[k] Γ(X, X.basicOpen g)).toRingHom)
    hC hXv hetale
  refine ⟨X.basicOpen g, hVaff, hVU, hxV, c', ?_, ?_, hajunit⟩
  · intro i hi
    exact ((hc' i).trans (hw (ULift.up i))).trans
      (congrArg (algebraMap Γ(X, U) Γ(X, X.basicOpen g))
        (hvne (ULift.up i) (fun h => hi (congrArg ULift.down h))))
  · exact ((hc' j).trans (hw (ULift.up j))).trans
      (congrArg (algebraMap Γ(X, U) Γ(X, X.basicOpen g)) hvj)

theorem hasStrictNormalCrossingsWith_cons_of_le {X : Scheme.{u}} {k : Type u} [Field k]
    (p : X ⟶ Spec (CommRingCat.of k)) [AlgebraicGeometry.Smooth p] (Z H : X.IdealSheafData)
    (N : List X.IdealSheafData) (hN : InStrictNormalCrossingPosition p (H :: N)) (hZ : HasStrictNormalCrossingsWith p Z N)
    (hHZ : H ≤ Z) : HasStrictNormalCrossingsWith p Z (H :: N) := by
  refine hasStrictNormalCrossingsWith_of_forall_exists_etaleChart ?_
  intro x hx
  obtain ⟨U, hU, hxU, m, c, lab, S, m', c', j0, lab', hZU, hHU, hlab, hlabinj, hlab', hj0⟩ :=
    exists_etaleCharts_of_inStrictNormalCrossingPosition_cons p Z H N hN hZ hHZ x hx
  obtain ⟨a, ha, j, hjS, hajP, hjlab⟩ :=
    exists_coord_eq_sum_coeff_not_mem_of_le p hU hxU c lab S c' j0 lab' Z H N hx hlab hZU hHU hlab' hj0 hHZ
  have hZideal : Z.ideal ⟨U, hU⟩ = Ideal.span (c.coord '' (S : Set (Fin m))) :=
    c.ideal_eq_span_coord hU Z S hZU
  have hHideal : H.ideal ⟨U, hU⟩ = Ideal.span ({c'.coord j0} : Set Γ(X, U)) :=
    ideal_eq_span_coord_of_restrictIdeal_eq hU c' H j0 hHU
  have hcP : ∀ i ∈ S, c.coord i ∈ (hU.primeIdealOf ⟨x, hxU⟩).asIdeal := by
    intro i hi
    refine ideal_le_primeIdealOf Z hU hxU hx ?_
    rw [hZideal]
    exact Ideal.subset_span ⟨i, Finset.mem_coe.mpr hi, rfl⟩
  obtain ⟨V, hV, hVU, hxV, c2, hc2ne, hc2j, hc2unit⟩ :=
    exists_etaleChart_update_coord p hU c hxU S a j hjS hcP hajP
  have hcoordfun : c2.coord = Function.update
      (fun i : Fin m => (X.presheaf.map (homOfLE hVU).op).hom (c.coord i)) j
      (∑ i ∈ S, (X.presheaf.map (homOfLE hVU).op).hom (a i) *
        (X.presheaf.map (homOfLE hVU).op).hom (c.coord i)) := by
    funext i
    by_cases hij : i = j
    · rw [Function.update_apply, if_pos hij, hij, hc2j, map_sum]
      exact Finset.sum_congr rfl fun t _ => map_mul _ _ _
    · rw [Function.update_apply, if_neg hij]
      exact hc2ne i hij
  have hupd : Ideal.span (c2.coord '' (S : Set (Fin m)))
      = Ideal.span ((fun i : Fin m => (X.presheaf.map (homOfLE hVU).op).hom (c.coord i)) ''
        (S : Set (Fin m))) := by
    rw [hcoordfun]
    exact span_image_update_sum_eq
      (fun i : Fin m => (X.presheaf.map (homOfLE hVU).op).hom (c.coord i)) S
      (fun i : Fin m => (X.presheaf.map (homOfLE hVU).op).hom (a i)) j hjS hc2unit
  have hZVspan : Z.ideal ⟨V, hV⟩ = Ideal.span (c2.coord '' (S : Set (Fin m))) := by
    rw [hupd, ideal_eq_span_image_map_of_le Z hU hV hVU (c.coord '' (S : Set (Fin m))) hZideal,
      Set.image_image]
  have hZVcoord : restrictIdeal Z V = c2.coordIdeal S :=
    restrictIdeal_eq_coordIdeal_of_ideal_eq_span hV c2 Z S hZVspan
  have hHVspan : H.ideal ⟨V, hV⟩
      = Ideal.span (c2.coord '' ((({j} : Finset (Fin m))) : Set (Fin m))) := by
    rw [Finset.coe_singleton, Set.image_singleton,
      ideal_eq_span_image_map_of_le H hU hV hVU ({c'.coord j0} : Set Γ(X, U)) hHideal,
      Set.image_singleton, ha, ← hc2j]
  have hHVcoord : restrictIdeal H V = c2.coordIdeal {j} :=
    restrictIdeal_eq_coordIdeal_of_ideal_eq_span hV c2 H {j} hHVspan
  have hNVcoord : ∀ (i : ℕ) (hi : i < N.length) (t : Fin m), lab i = some t →
      restrictIdeal (N[i]'hi) V = c2.coordIdeal {t} := by
    intro i hi t hlt
    have htj : t ≠ j := by
      intro hcon
      exact hjlab i hi (by rw [hlt, hcon])
    have hUeq : restrictIdeal (N[i]'hi) U = c.coordIdeal {t} := (hlab i hi).2 t hlt
    have hideal : (N[i]'hi).ideal ⟨U, hU⟩ = Ideal.span ({c.coord t} : Set Γ(X, U)) :=
      ideal_eq_span_coord_of_restrictIdeal_eq hU c (N[i]'hi) t hUeq
    have hspanV : (N[i]'hi).ideal ⟨V, hV⟩
        = Ideal.span (c2.coord '' ((({t} : Finset (Fin m))) : Set (Fin m))) := by
      rw [Finset.coe_singleton, Set.image_singleton, hc2ne t htj,
        ideal_eq_span_image_map_of_le (N[i]'hi) hU hV hVU ({c.coord t} : Set Γ(X, U)) hideal,
        Set.image_singleton]
    exact restrictIdeal_eq_coordIdeal_of_ideal_eq_span hV c2 (N[i]'hi) {t} hspanV
  have hNVtop : ∀ (i : ℕ) (hi : i < N.length), lab i = none →
      restrictIdeal (N[i]'hi) V = ⊤ := by
    intro i hi hn
    exact restrictIdeal_eq_top_of_le (N[i]'hi) hVU ((hlab i hi).1 hn)
  obtain ⟨relab, hnl0, hnls⟩ :
      ∃ nl : ℕ → Option (Fin m), nl 0 = some j ∧ ∀ i : ℕ, nl (i + 1) = lab i :=
    ⟨fun i => if i = 0 then some j else lab (i - 1), by simp, fun i => by simp⟩
  refine ⟨V, hxV, m, c2, relab, S, ?_, ?_, ?_, hZVcoord⟩
  · intro i hi i' hi' t h1 h2
    rcases i with _ | i1
    · rcases i' with _ | i1'
      · rfl
      · exfalso
        rw [hnl0] at h1
        rw [hnls i1'] at h2
        have hb : i1' < N.length := by
          simp only [List.length_cons] at hi'
          omega
        exact hjlab i1' hb (h2.trans h1.symm)
    · rcases i' with _ | i1'
      · exfalso
        rw [hnl0] at h2
        rw [hnls i1] at h1
        have hb : i1 < N.length := by
          simp only [List.length_cons] at hi
          omega
        exact hjlab i1 hb (h1.trans h2.symm)
      · rw [hnls i1] at h1
        rw [hnls i1'] at h2
        have hb1 : i1 < N.length := by
          simp only [List.length_cons] at hi
          omega
        have hb2 : i1' < N.length := by
          simp only [List.length_cons] at hi'
          omega
        have hee := hlabinj i1 i1' hb1 hb2 t h1 h2
        omega
  · intro i hi hn
    rcases i with _ | i1
    · rw [hnl0] at hn
      exact absurd hn (Option.some_ne_none j)
    · rw [hnls i1] at hn
      have hb : i1 < N.length := by
        simp only [List.length_cons] at hi
        omega
      exact hNVtop i1 hb hn
  · intro i hi t hs
    rcases i with _ | i1
    · rw [hnl0] at hs
      have htj : t = j := (Option.some.inj hs).symm
      subst htj
      exact hHVcoord
    · rw [hnls i1] at hs
      have hb : i1 < N.length := by
        simp only [List.length_cons] at hi
        omega
      exact hNVcoord i1 hb t hs

end FunctorialResolution.EmbeddedResolution
