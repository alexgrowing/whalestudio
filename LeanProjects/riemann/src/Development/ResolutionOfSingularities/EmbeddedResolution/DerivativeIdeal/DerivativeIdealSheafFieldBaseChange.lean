import Mathlib
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.ChartRing
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.EtaleCoordinates
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.EtaleChartExistence
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.EtaleChartFieldBaseChange
import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.DerivativeIdealSheaf
import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.DerivativeIdealFieldExtension
import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.IdealSheafOrder
import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.DerivativeIdealSheafOrderDecrease
import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.DerivativeIdealSheafSmoothPullback
import Development.ResolutionOfSingularities.Foundations.Schemes.IdealSheafData
import Development.ResolutionOfSingularities.EmbeddedResolution.MaximalContactHypersurfaces.MaxContactIdeal
universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace

noncomputable section

namespace FunctorialResolution.EmbeddedResolution

private theorem span_eq_top_of_isAffineOpen_of_forall_mem_basicOpen {X : Scheme.{u}} {U : X.Opens}
    (hU : IsAffineOpen U) (s : Set Γ(X, U)) (hcov : ∀ x ∈ U, ∃ g ∈ s, x ∈ X.basicOpen g) :
    Ideal.span s = ⊤ := by
  by_contra hne
  obtain ⟨m, hm, hle⟩ := Ideal.exists_le_maximal _ hne
  have hmp : m.IsPrime := hm.isPrime
  have hx : hU.fromSpec.base (⟨m, hmp⟩ : PrimeSpectrum Γ(X, U)) ∈ U := by
    have hr : hU.fromSpec.base (⟨m, hmp⟩ : PrimeSpectrum Γ(X, U))
        ∈ Set.range hU.fromSpec.base := ⟨_, rfl⟩
    rw [hU.range_fromSpec] at hr
    exact hr
  obtain ⟨g, hgs, hg⟩ := hcov _ hx
  have hmem : (⟨m, hmp⟩ : PrimeSpectrum Γ(X, U)) ∈ hU.fromSpec ⁻¹ᵁ X.basicOpen g := hg
  rw [hU.fromSpec_preimage_basicOpen] at hmem
  have hnot : g ∉ m := hmem
  exact hnot (hle (Ideal.subset_span hgs))

private theorem ideal_eq_of_le {X : Scheme.{u}} (I J : X.IdealSheafData)
    (V W : X.affineOpens) (h : (W : X.Opens) ≤ (V : X.Opens)) (hIJ : I.ideal V = J.ideal V) :
    I.ideal W = J.ideal W := by
  have e : (W : X.Opens) ≤ (𝟙 X) ⁻¹ᵁ (V : X.Opens) := by simpa using h
  have h1 := Scheme.IdealSheafData.comap_ideal_eq_map_appLE I (𝟙 X) V W e
  have h2 := Scheme.IdealSheafData.comap_ideal_eq_map_appLE J (𝟙 X) V W e
  rw [Scheme.IdealSheafData.comap_id] at h1 h2
  rw [h1, h2, hIJ]

private theorem exists_pow_mul_mem_of_map_mem {X : Scheme.{u}} (U : X.affineOpens)
    (g : Γ(X, U.1)) (Jid : Ideal Γ(X, U.1)) (s : Γ(X, U.1))
    (hs : (X.presheaf.map (homOfLE (X.basicOpen_le g)).op).hom s ∈
        Ideal.map (X.presheaf.map (homOfLE (X.basicOpen_le g)).op).hom Jid) :
    ∃ n : ℕ, g ^ n * s ∈ Jid := by
  let algUV : Algebra Γ(X, U.1) Γ(X, X.basicOpen g) :=
    (X.presheaf.map (homOfLE (X.basicOpen_le g)).op).hom.toAlgebra
  have hloc : IsLocalization.Away g Γ(X, X.basicOpen g) := U.2.isLocalization_basicOpen g
  have hmem : algebraMap Γ(X, U.1) Γ(X, X.basicOpen g) s ∈
      Ideal.map (algebraMap Γ(X, U.1) Γ(X, X.basicOpen g)) Jid := hs
  obtain ⟨⟨⟨y, hy⟩, mm⟩, hEq⟩ :=
    (IsLocalization.mem_map_algebraMap_iff (M := Submonoid.powers g)
      (S := Γ(X, X.basicOpen g))).mp hmem
  have hEq' : algebraMap Γ(X, U.1) Γ(X, X.basicOpen g) (s * (mm : Γ(X, U.1)))
      = algebraMap Γ(X, U.1) Γ(X, X.basicOpen g) y := by
    rw [map_mul]
    exact hEq
  obtain ⟨cc, hcc⟩ :=
    (IsLocalization.eq_iff_exists (Submonoid.powers g) Γ(X, X.basicOpen g)).mp hEq'
  obtain ⟨n₁, hn₁⟩ := (Submonoid.mem_powers_iff (cc : Γ(X, U.1)) g).mp cc.2
  obtain ⟨n₂, hn₂⟩ := (Submonoid.mem_powers_iff (mm : Γ(X, U.1)) g).mp mm.2
  refine ⟨n₁ + n₂, ?_⟩
  have hrw : g ^ (n₁ + n₂) * s = (cc : Γ(X, U.1)) * (s * (mm : Γ(X, U.1))) := by
    rw [pow_add, hn₁, hn₂]; ring
  rw [hrw, hcc]
  exact Ideal.mul_mem_left _ _ hy

private theorem ideal_le_of_locally_eq {X : Scheme.{u}} (I J : X.IdealSheafData)
    (h : ∀ x : ↥X, ∃ V : X.affineOpens, x ∈ (V : X.Opens) ∧ I.ideal V = J.ideal V)
    (U : X.affineOpens) : I.ideal U ≤ J.ideal U := by
  intro s hs
  have hspan : Ideal.span {g : Γ(X, U.1) | ∃ n : ℕ, g ^ n * s ∈ J.ideal U} = ⊤ := by
    refine span_eq_top_of_isAffineOpen_of_forall_mem_basicOpen U.2 _ ?_
    intro x hx
    obtain ⟨V, hxV, hIJ⟩ := h x
    obtain ⟨g, hgV, hxg⟩ := U.2.exists_basicOpen_le (⟨x, hxV⟩ : ↥(V : X.Opens)) hx
    have hIJW : I.ideal (X.affineBasicOpen g) = J.ideal (X.affineBasicOpen g) :=
      ideal_eq_of_le I J V (X.affineBasicOpen g) hgV hIJ
    have hres : (X.presheaf.map (homOfLE (X.basicOpen_le g)).op).hom s ∈
        Ideal.map (X.presheaf.map (homOfLE (X.basicOpen_le g)).op).hom (J.ideal U) := by
      rw [J.map_ideal_basicOpen U g, ← hIJW, ← I.map_ideal_basicOpen U g]
      exact Ideal.mem_map_of_mem _ hs
    obtain ⟨n, hn⟩ := exists_pow_mul_mem_of_map_mem U g (J.ideal U) s hres
    exact ⟨g, ⟨n, hn⟩, hxg⟩
  obtain ⟨K, hK⟩ : ∃ K : Ideal Γ(X, U.1), ∀ a : Γ(X, U.1), a ∈ K ↔ a * s ∈ J.ideal U := by
    refine ⟨Submodule.comap (LinearMap.toSpanSingleton Γ(X, U.1) Γ(X, U.1) s) (J.ideal U),
      fun a => ?_⟩
    simp [Submodule.mem_comap, LinearMap.toSpanSingleton_apply, smul_eq_mul]
  have hsub : Ideal.span {g : Γ(X, U.1) | ∃ n : ℕ, g ^ n * s ∈ J.ideal U} ≤ K.radical := by
    refine Ideal.span_le.mpr ?_
    rintro g ⟨n, hn⟩
    exact Ideal.mem_radical_iff.mpr ⟨n, (hK _).mpr hn⟩
  have htop : K.radical = ⊤ := by
    rw [eq_top_iff, ← hspan]
    exact hsub
  have h1 : (1 : Γ(X, U.1)) ∈ K.radical := by
    rw [htop]
    exact Submodule.mem_top
  obtain ⟨n, hn⟩ := Ideal.mem_radical_iff.mp h1
  have hone : (1 : Γ(X, U.1)) ∈ K := by simpa using hn
  simpa using (hK 1).mp hone

private theorem idealSheafData_eq_of_locally_eq {X : Scheme.{u}} (I J : X.IdealSheafData)
    (h : ∀ x : ↥X, ∃ V : X.affineOpens, x ∈ (V : X.Opens) ∧ I.ideal V = J.ideal V) : I = J := by
  have h1 : ∀ U : X.affineOpens, I.ideal U ≤ J.ideal U := fun U =>
    ideal_le_of_locally_eq I J h U
  have h2 : ∀ U : X.affineOpens, J.ideal U ≤ I.ideal U := by
    refine fun U => ideal_le_of_locally_eq J I (fun x => ?_) U
    obtain ⟨V, hV, hIJ⟩ := h x
    exact ⟨V, hV, hIJ.symm⟩
  exact le_antisymm h1 h2

private theorem sectionsAlgebraMap_comp_specMap (k L : Type u) [Field k] [Field L]
    {Y : Scheme.{u}} (q : Y ⟶ Spec (CommRingCat.of L))
    (φ : CommRingCat.of k ⟶ CommRingCat.of L) (W : Y.Opens) :
    sectionsAlgebraMap k (q ≫ Spec.map φ) W = (sectionsAlgebraMap L q W).comp φ.hom := by
  have h1 : (q ≫ Spec.map φ).appLE ⊤ W (le_preimage_top k (q ≫ Spec.map φ) W)
      = ((Spec.map φ).appTop ≫ q.appTop) ≫
          Y.presheaf.map (homOfLE (le_preimage_top L q W)).op := rfl
  have h2 : (Spec.map φ).appTop ≫ q.appLE ⊤ W (le_preimage_top L q W)
      = ((Spec.map φ).appTop ≫ q.appTop) ≫
          Y.presheaf.map (homOfLE (le_preimage_top L q W)).op :=
    (Category.assoc _ _ _).symm
  have happ : (q ≫ Spec.map φ).appLE ⊤ W (le_preimage_top k (q ≫ Spec.map φ) W)
      = (Spec.map φ).appTop ≫ q.appLE ⊤ W (le_preimage_top L q W) := h1.trans h2.symm
  have key : (Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫
        (q ≫ Spec.map φ).appLE ⊤ W (le_preimage_top k (q ≫ Spec.map φ) W)
      = φ ≫ ((Scheme.ΓSpecIso (CommRingCat.of L)).inv ≫
          q.appLE ⊤ W (le_preimage_top L q W)) := by
    rw [happ, ← Category.assoc, ← Scheme.ΓSpecIso_inv_naturality φ, Category.assoc]
  ext a
  exact DFunLike.congr_fun (congrArg CommRingCat.Hom.hom key) a

private theorem exists_affineOpen_derivIdealSheaf_comap_eq {k L : Type u} [Field k] [Field L]
    {X Y : Scheme.{u}} {p : X ⟶ Spec (CommRingCat.of k)} [AlgebraicGeometry.Smooth p]
    {q : Y ⟶ Spec (CommRingCat.of L)} [AlgebraicGeometry.Smooth q] {f : Y ⟶ X}
    {φ : CommRingCat.of k ⟶ CommRingCat.of L} (hsq : IsPullback q f (Spec.map φ) p)
    (I : X.IdealSheafData) (y : ↥Y) :
    ∃ V : Y.affineOpens, y ∈ (V : Y.Opens) ∧
      (derivIdealSheaf L q (I.comap f)).ideal V
        = ((derivIdealSheaf k p I).comap f).ideal V := by
  obtain ⟨U, m, hxU, hU, ⟨c⟩⟩ := exists_etaleChart p (f.base y)
  obtain ⟨V, hVU, c', hVaff, hyV, hcoord⟩ :=
    exists_etaleChart_of_isPullback hsq c y hxU
  refine ⟨⟨V, hVaff⟩, hyV, ?_⟩
  have hdec : DecidableEq (ULift.{u} (Fin m)) := Classical.decEq _
  let instkL : Algebra k L := φ.hom.toAlgebra
  let instA : Algebra k Γ(X, U) := sectionsAlgebra k p U
  let instPA : Algebra (MvPolynomial (ULift.{u} (Fin m)) k) Γ(X, U) := c.algebra
  let instB : Algebra L Γ(Y, V) := sectionsAlgebra L q V
  let instPB : Algebra (MvPolynomial (ULift.{u} (Fin m)) L) Γ(Y, V) := c'.algebra
  let instAlgebra : Algebra k Γ(Y, V) := ((sectionsAlgebraMap L q V).comp φ.hom).toAlgebra
  have tA : IsScalarTower k (MvPolynomial (ULift.{u} (Fin m)) k) Γ(X, U) := c.isScalarTower
  have tB : IsScalarTower L (MvPolynomial (ULift.{u} (Fin m)) L) Γ(Y, V) := c'.isScalarTower
  have feA : Algebra.FormallyEtale (MvPolynomial (ULift.{u} (Fin m)) k) Γ(X, U) :=
    c.algebra_formallyEtale hU
  have feB : Algebra.FormallyEtale (MvPolynomial (ULift.{u} (Fin m)) L) Γ(Y, V) :=
    c'.algebra_formallyEtale hVaff
  have tkL : IsScalarTower k L Γ(Y, V) := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have hcommutes : ∀ a : k, (f.appLE U V hVU).hom (algebraMap k Γ(X, U) a)
      = algebraMap k Γ(Y, V) a := by
    intro a
    show (f.appLE U V hVU).hom (sectionsAlgebraMap k p U a)
      = sectionsAlgebraMap L q V (φ.hom a)
    rw [sectionsAlgebraMap_appLE_apply k p f U V hVU a, ← hsq.w,
      sectionsAlgebraMap_comp_specMap k L q φ V]
    rfl
  let ψ : Γ(X, U) →ₐ[k] Γ(Y, V) := AlgHom.mk (f.appLE U V hVU).hom hcommutes
  have hψ : ∀ i : ULift.{u} (Fin m),
      ψ (EtaleCoordinates.coord k (ULift.{u} (Fin m)) Γ(X, U) i)
        = EtaleCoordinates.coord L (ULift.{u} (Fin m)) Γ(Y, V) i := by
    rintro ⟨j⟩
    have h1 : EtaleCoordinates.coord k (ULift.{u} (Fin m)) Γ(X, U) (ULift.up j) = c.coord j :=
      c.etaleCoordinates_coord j
    have h2 : EtaleCoordinates.coord L (ULift.{u} (Fin m)) Γ(Y, V) (ULift.up j) = c'.coord j :=
      c'.etaleCoordinates_coord j
    rw [h1, h2]
    show (f.appLE U V hVU).hom (c.coord j) = c'.coord j
    exact (hcoord j).symm
  have key := DerivIdealBaseChange.map_derivIdeal k L (ULift.{u} (Fin m)) Γ(X, U) Γ(Y, V) ψ hψ
      (I.ideal ⟨U, hU⟩)
  have hcomapV : (I.comap f).ideal ⟨V, hVaff⟩
      = Ideal.map (f.appLE U V hVU).hom (I.ideal ⟨U, hU⟩) :=
    Scheme.IdealSheafData.comap_ideal_eq_map_appLE I f ⟨U, hU⟩ ⟨V, hVaff⟩ hVU
  have hcomapD : ((derivIdealSheaf k p I).comap f).ideal ⟨V, hVaff⟩
      = Ideal.map (f.appLE U V hVU).hom ((derivIdealSheaf k p I).ideal ⟨U, hU⟩) :=
    Scheme.IdealSheafData.comap_ideal_eq_map_appLE (derivIdealSheaf k p I) f ⟨U, hU⟩
      ⟨V, hVaff⟩ hVU
  rw [derivIdealSheaf_ideal, hcomapV, hcomapD, derivIdealSheaf_ideal]
  exact key.symm

theorem derivIdealSheaf_comap_fieldBaseChange {k L : Type u} [Field k] [Field L]
    {X : Scheme.{u}} (p : X ⟶ Spec (CommRingCat.of k)) [AlgebraicGeometry.Smooth p]
    (φ : CommRingCat.of k ⟶ CommRingCat.of L) (I : X.IdealSheafData) :
    derivIdealSheaf L (pullback.snd p (Spec.map φ))
        (I.comap (pullback.fst p (Spec.map φ))) =
      (derivIdealSheaf k p I).comap (pullback.fst p (Spec.map φ)) :=
  idealSheafData_eq_of_locally_eq _ _ fun y =>
    exists_affineOpen_derivIdealSheaf_comap_eq (isPullback_pullback_specMap p φ) I y

theorem derivIdealSheafIterate_comap_fieldBaseChange {k L : Type u} [Field k] [Field L]
    {X : Scheme.{u}} (p : X ⟶ Spec (CommRingCat.of k)) [AlgebraicGeometry.Smooth p]
    (φ : CommRingCat.of k ⟶ CommRingCat.of L) (r : ℕ) (I : X.IdealSheafData) :
    derivIdealSheafIterate L (pullback.snd p (Spec.map φ)) r
        (I.comap (pullback.fst p (Spec.map φ))) =
      (derivIdealSheafIterate k p r I).comap (pullback.fst p (Spec.map φ)) := by
  induction r with
  | zero => rfl
  | succ n ih =>
      rw [derivIdealSheafIterate_succ, derivIdealSheafIterate_succ, ih,
        derivIdealSheaf_comap_fieldBaseChange p φ (derivIdealSheafIterate k p n I)]

theorem maxContactIdeal_comap_fieldBaseChange {k L : Type u} [Field k] [Field L]
    {X : Scheme.{u}} (p : X ⟶ Spec (CommRingCat.of k)) [AlgebraicGeometry.Smooth p]
    (φ : CommRingCat.of k ⟶ CommRingCat.of L) (m : ℕ) (I : X.IdealSheafData) :
    maxContactIdeal L (pullback.snd p (Spec.map φ))
        (I.comap (pullback.fst p (Spec.map φ))) m =
      (maxContactIdeal k p I m).comap (pullback.fst p (Spec.map φ)) := by
  rw [maxContactIdeal_eq_derivIdealSheafIterate, maxContactIdeal_eq_derivIdealSheafIterate, derivIdealSheafIterate_comap_fieldBaseChange]

theorem orderAtLeastLocus_comap_fieldBaseChange {k L : Type u} [Field k] [Field L] [CharZero k]
    [CharZero L] {X : Scheme.{u}} (p : X ⟶ Spec (CommRingCat.of k))
    [AlgebraicGeometry.Smooth p] (φ : CommRingCat.of k ⟶ CommRingCat.of L)
    (I : X.IdealSheafData) (m : ℕ) :
    orderAtLeastLocus (I.comap (pullback.fst p (Spec.map φ))) m =
      (pullback.fst p (Spec.map φ)).base ⁻¹' orderAtLeastLocus I m := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · rw [orderAtLeastLocus_zero, orderAtLeastLocus_zero, Set.preimage_univ]
  · rw [← support_derivIdealSheafIterate_eq_orderAtLeastLocus L (pullback.snd p (Spec.map φ))
        (I.comap (pullback.fst p (Spec.map φ))) hm,
      ← support_derivIdealSheafIterate_eq_orderAtLeastLocus k p I hm,
      derivIdealSheafIterate_comap_fieldBaseChange p φ (m - 1) I]
    ext y
    simp

theorem orderAt_comap_fieldBaseChange {k L : Type u} [Field k] [Field L] [CharZero k]
    [CharZero L] {X : Scheme.{u}} (p : X ⟶ Spec (CommRingCat.of k))
    [AlgebraicGeometry.Smooth p] (φ : CommRingCat.of k ⟶ CommRingCat.of L)
    (I : X.IdealSheafData) (y : ↥(pullback p (Spec.map φ))) :
    orderAt (I.comap (pullback.fst p (Spec.map φ))) y =
      orderAt I ((pullback.fst p (Spec.map φ)).base y) := by
  refine ENat.eq_of_forall_natCast_le_iff ?_
  intro n
  have h := orderAtLeastLocus_comap_fieldBaseChange p φ I n
  have hy := Set.ext_iff.mp h y
  simpa [mem_orderAtLeastLocus_iff, Set.mem_preimage] using hy

end FunctorialResolution.EmbeddedResolution
