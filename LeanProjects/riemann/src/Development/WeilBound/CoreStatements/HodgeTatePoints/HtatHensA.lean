import Mathlib

namespace PositivityTheory.HtPt.Htat.Hens

open CategoryTheory Limits Polynomial IsLocalRing TensorProduct

universe u v w

section

variable {A : Type u} {B : Type v} {C : Type w} [CommRing A] [CommRing B] [CommRing C]
  [Algebra A B] [Algebra A C] [IsLocalRing C]

theorem algHom_eq_of_residue_eq [Algebra.Etale A B] {σ τ : B →ₐ[A] C}
    (h : ∀ b, residue C (σ b) = residue C (τ b)) : σ = τ := by
  let q := RingHom.ker ((residue C).comp σ.toRingHom)
  have : q.IsPrime := RingHom.ker_isPrime _
  obtain ⟨f, hf, hstd⟩ := Algebra.IsEtaleAt.exists_isStandardEtale (R := A) q
  have hσ : IsUnit (σ f) := (residue_ne_zero_iff_isUnit _).1 (by simpa [q, RingHom.mem_ker] using hf)
  have hτ : IsUnit (τ f) := (residue_ne_zero_iff_isUnit _).1 (by
    rw [← h f]; simpa [q, RingHom.mem_ker] using hf)
  let σ' : Localization.Away f →ₐ[A] C := IsLocalization.Away.liftAlgHom f hσ
  let τ' : Localization.Away f →ₐ[A] C := IsLocalization.Away.liftAlgHom f hτ
  have hσ' : ∀ b, σ' (algebraMap B _ b) = σ b := fun b ↦ IsLocalization.Away.lift_eq f hσ b
  have hτ' : ∀ b, τ' (algebraMap B _ b) = τ b := fun b ↦ IsLocalization.Away.lift_eq f hτ b
  suffices e : σ' = τ' by
    ext b
    rw [← hσ', ← hτ', e]
  let P : StandardEtalePresentation A (Localization.Away f) :=
    hstd.nonempty_standardEtalePresentation.some
  apply P.hom_ext

  have hres : (residue C).comp σ'.toRingHom = (residue C).comp τ'.toRingHom := by
    apply IsLocalization.ringHom_ext (Submonoid.powers f)
    ext b
    simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, hσ', hτ', h]
  have hx := congrArg (fun φ ↦ φ P.x) hres
  simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe] at hx
  have h1 := P.hasMap.map σ'
  have h2 := P.hasMap.map τ'
  refine IsLocalRing.eq_of_eval_eq_zero_of_not_isUnit_sub (f := P.f.map (algebraMap A C))
    (by rw [eval_map_algebraMap]; exact h1.1) (by rw [eval_map_algebraMap]; exact h2.1) ?_ ?_
  · rw [← residue_ne_zero_iff_isUnit, not_not, map_sub, hx, sub_self]
  · rw [derivative_map, eval_map_algebraMap]
    exact StandardEtalePair.HasMap.isUnit_derivative_f _ h1

end

section Pointed

section Algebra

variable {R : Type u} [CommRing R] {K : Type u} [Field K] [Algebra R K]
  {X Y : Type u} [CommRing X] [CommRing Y] [Algebra R X] [Algebra R Y] [Algebra.Etale R X]

theorem exists_away_comp_eq (ψ : Y →ₐ[R] K) (f g : X →ₐ[R] Y) (h : ψ.comp f = ψ.comp g) :
    ∃ t : Y, ψ t ≠ 0 ∧ (IsScalarTower.toAlgHom R Y (Localization.Away t)).comp f =
      (IsScalarTower.toAlgHom R Y (Localization.Away t)).comp g := by
  let q := RingHom.ker ψ
  have : q.IsPrime := RingHom.ker_isPrime _
  let Yq := Localization.AtPrime q
  have e : (IsScalarTower.toAlgHom R Y Yq).comp f = (IsScalarTower.toAlgHom R Y Yq).comp g := by
    refine algHom_eq_of_residue_eq fun x ↦ ?_
    rw [← sub_eq_zero, ← map_sub, residue_eq_zero_iff]
    simp only [AlgHom.comp_apply, IsScalarTower.coe_toAlgHom', ← map_sub]
    rw [IsLocalization.AtPrime.to_map_mem_maximal_iff Yq q, RingHom.mem_ker, map_sub, sub_eq_zero]
    exact congr($h x)
  obtain ⟨s, hs⟩ := Algebra.FiniteType.out (R := R) (A := X)
  have hc : ∀ x : s, ∃ m ∈ q.primeCompl, m * (f x - g x) = 0 := by
    intro x
    have := congr($e x)
    simp only [AlgHom.comp_apply, IsScalarTower.coe_toAlgHom'] at this
    rw [← sub_eq_zero, ← map_sub, IsLocalization.map_eq_zero_iff q.primeCompl] at this
    obtain ⟨⟨m, hm⟩, hm'⟩ := this
    exact ⟨m, hm, hm'⟩
  choose c hc hc' using hc
  refine ⟨∏ x : s, c x, ?_, ?_⟩
  · have : ∏ x : s, c x ∈ q.primeCompl := Submonoid.prod_mem _ fun x _ ↦ hc x
    simpa [q, Ideal.primeCompl, RingHom.mem_ker] using this
  · refine AlgHom.ext_of_adjoin_eq_top hs fun x hx ↦ ?_
    simp only [AlgHom.comp_apply, IsScalarTower.coe_toAlgHom']
    rw [← sub_eq_zero, ← map_sub,
      IsLocalization.map_eq_zero_iff (Submonoid.powers (∏ x : s, c x))]
    obtain ⟨k, hk⟩ := Finset.dvd_prod_of_mem c (Finset.mem_univ (⟨x, hx⟩ : s))
    refine ⟨⟨_, Submonoid.mem_powers _⟩, ?_⟩
    simp only
    rw [hk, mul_right_comm, hc' ⟨x, hx⟩, zero_mul]

end Algebra

variable (R : Type u) [CommRing R] (K : Type u) [CommRing K] [Algebra R K]

structure PointedEtale where

  carrier : Type u
  [commRing : CommRing carrier]
  [algebra : Algebra R carrier]
  [etale : Algebra.Etale R carrier]

  pt : carrier →ₐ[R] K

namespace PointedEtale

attribute [instance] commRing algebra etale

variable {R K}

instance : CoeSort (PointedEtale R K) (Type u) := ⟨carrier⟩

@[ext]
structure Hom (X Y : PointedEtale R K) where

  alg : X →ₐ[R] Y
  comm : Y.pt.comp alg = X.pt

instance : Category (PointedEtale R K) where
  Hom := Hom
  id X := ⟨AlgHom.id R X, by ext; rfl⟩
  comp f g := ⟨g.alg.comp f.alg, by rw [← AlgHom.comp_assoc, g.comm, f.comm]⟩

@[ext]
theorem hom_ext {X Y : PointedEtale R K} {f g : X ⟶ Y} (h : f.alg = g.alg) : f = g :=
  Hom.ext h

@[simp]
theorem id_alg (X : PointedEtale R K) : (𝟙 X : X ⟶ X).alg = AlgHom.id R X := rfl

@[simp]
theorem comp_alg {X Y Z : PointedEtale R K} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (f ≫ g).alg = g.alg.comp f.alg := rfl

theorem pt_alg {X Y : PointedEtale R K} (f : X ⟶ Y) (x : X) : Y.pt (f.alg x) = X.pt x :=
  congr($(f.comm) x)

abbrev base : PointedEtale R K := ⟨R, Algebra.ofId R K⟩

def fromBase (X : PointedEtale R K) : base ⟶ X :=
  ⟨Algebra.ofId R X, by ext⟩

instance (X Y : PointedEtale R K) : Algebra.Etale R (X ⊗[R] Y) :=
  Algebra.Etale.comp R X (X ⊗[R] Y)

noncomputable abbrev tensor (X Y : PointedEtale R K) : PointedEtale R K :=
  ⟨X ⊗[R] Y, Algebra.TensorProduct.lift X.pt Y.pt fun _ _ ↦ Commute.all _ _⟩

noncomputable def inl (X Y : PointedEtale R K) : X ⟶ tensor X Y :=
  ⟨Algebra.TensorProduct.includeLeft, by
    ext x
    change Algebra.TensorProduct.lift X.pt Y.pt (fun _ _ ↦ Commute.all _ _) (x ⊗ₜ 1) = X.pt x
    simp⟩

noncomputable def inr (X Y : PointedEtale R K) : Y ⟶ tensor X Y :=
  ⟨Algebra.TensorProduct.includeRight, by
    ext x
    change Algebra.TensorProduct.lift X.pt Y.pt (fun _ _ ↦ Commute.all _ _) (1 ⊗ₜ x) = Y.pt x
    simp⟩

noncomputable abbrev away (X : PointedEtale R K) (s : X) (hs : IsUnit (X.pt s)) : PointedEtale R K :=
  ⟨Localization.Away s, IsLocalization.Away.liftAlgHom s hs⟩

noncomputable def toAway (X : PointedEtale R K) (s : X) (hs : IsUnit (X.pt s)) :
    X ⟶ X.away s hs :=
  ⟨(IsScalarTower.toAlgHom R X (Localization.Away s) : X →ₐ[R] Localization.Away s), by
    ext x; exact IsLocalization.Away.lift_eq s hs x⟩

theorem toAway_alg_apply (X : PointedEtale R K) (s : X) (hs : IsUnit (X.pt s)) (x : X) :
    (X.toAway s hs).alg x = algebraMap X (Localization.Away s) x := rfl

theorem isUnit_toAway (X : PointedEtale R K) (s : X) (hs : IsUnit (X.pt s)) :
    IsUnit ((X.toAway s hs).alg s) :=
  IsLocalization.Away.algebraMap_isUnit s

end PointedEtale

section Field

variable {R : Type u} [CommRing R] {K : Type u} [Field K] [Algebra R K]

namespace PointedEtale

instance isFiltered : IsFiltered (PointedEtale R K) where
  nonempty := ⟨base⟩
  cocone_objs X Y := ⟨tensor X Y, inl X Y, inr X Y, trivial⟩
  cocone_maps {X Y} f g := by
    obtain ⟨t, ht, e⟩ := exists_away_comp_eq Y.pt f.alg g.alg (by rw [f.comm, g.comm])
    exact ⟨Y.away t (isUnit_iff_ne_zero.2 ht), Y.toAway t _, hom_ext e⟩

abbrev StdIndex (R K : Type u) [CommRing R] [Field K] [Algebra R K] := Σ P : StandardEtalePair R, P.Ring →ₐ[R] K

noncomputable abbrev stdObj (i : StdIndex R K) : PointedEtale R K := ⟨i.1.Ring, i.2⟩

variable (R K) in

abbrev Std := InducedCategory (PointedEtale R K) (stdObj (R := R) (K := K))

variable (R K) in

noncomputable abbrev incl : Std R K ⥤ PointedEtale R K := inducedFunctor _

theorem exists_hom_incl (X : PointedEtale R K) :
    ∃ j : Std R K, Nonempty (X ⟶ (incl R K).obj j) := by
  let q := RingHom.ker X.pt
  have : q.IsPrime := RingHom.ker_isPrime _
  obtain ⟨s, hs, hstd⟩ := Algebra.IsEtaleAt.exists_isStandardEtale (R := R) q
  have hu : IsUnit (X.pt s) := isUnit_iff_ne_zero.2 (by simpa [q, RingHom.mem_ker] using hs)
  let P : StandardEtalePresentation R (Localization.Away s) :=
    hstd.nonempty_standardEtalePresentation.some
  let Y := X.away s hu
  let j : Std R K := ⟨P.P, Y.pt.comp P.equivRing.symm.toAlgHom⟩
  have hc : (Y.pt.comp P.equivRing.symm.toAlgHom).comp P.equivRing.toAlgHom = Y.pt := by
    ext y
    simp
  exact ⟨j, ⟨X.toAway s hu ≫ (⟨P.equivRing.toAlgHom, hc⟩ : Y ⟶ (incl R K).obj j)⟩⟩

theorem exists_hom_root (X : PointedEtale R K) (q : X[X]) (hq : q.Monic) (a₀ : K)
    (h₀ : q.eval₂ X.pt.toRingHom a₀ = 0) (h₁ : (derivative q).eval₂ X.pt.toRingHom a₀ ≠ 0) :
    ∃ (Y : PointedEtale R K) (f : X ⟶ Y) (b : Y), q.eval₂ f.alg.toRingHom b = 0 ∧ Y.pt b = a₀ := by
  let Q : StandardEtalePair X := ⟨q, hq, derivative q, 1, 0, 1, by ring⟩
  let : Algebra X K := X.pt.toRingHom.toAlgebra
  let : Algebra R Q.Ring := ((algebraMap X Q.Ring).comp (algebraMap R X)).toAlgebra
  have : IsScalarTower R X Q.Ring := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  have : IsScalarTower R X K := IsScalarTower.of_algebraMap_eq fun r ↦ (X.pt.commutes r).symm
  have : Algebra.Etale R Q.Ring := Algebra.Etale.comp R X Q.Ring
  have hmap : Q.HasMap a₀ := ⟨h₀, isUnit_iff_ne_zero.2 h₁⟩
  let ψ : Q.Ring →ₐ[X] K := Q.lift a₀ hmap
  let Y : PointedEtale R K := ⟨Q.Ring, ψ.restrictScalars R⟩
  refine ⟨Y, ⟨IsScalarTower.toAlgHom R X Q.Ring, ?_⟩, Q.X, ?_, ?_⟩
  · ext x
    exact ψ.commutes x
  · exact Q.hasMap_X.1
  · exact Q.lift_X a₀ hmap

instance isFiltered_std : IsFiltered (Std R K) :=
  IsFiltered.of_exists_of_isFiltered_of_fullyFaithful (incl R K) exists_hom_incl

instance final_incl : (incl R K).Final :=
  Functor.final_of_exists_of_isFiltered_of_fullyFaithful (incl R K) exists_hom_incl

end PointedEtale

end Field

namespace PointedEtale

variable {R : Type u} [CommRing R] {K : Type u} [CommRing K] [Algebra R K]

variable (R K) in

noncomputable def diagram : PointedEtale R K ⥤ CommRingCat.{u} where
  obj X := CommRingCat.of X
  map f := CommRingCat.ofHom f.alg.toRingHom

@[simp]
theorem diagram_map_apply {X Y : PointedEtale R K} (f : X ⟶ Y) (x : X) :
    (diagram R K).map f x = f.alg x := rfl

end PointedEtale

end Pointed

variable (R : Type u) [CommRing R] (K : Type u) [Field K] [Algebra R K]

open PointedEtale

noncomputable def etaleColimit : CommRingCat.{u} :=
  colimit (incl R K ⋙ diagram R K)

noncomputable def etaleCocone : Cocone (diagram R K) :=
  Functor.Final.extendCocone.obj (colimit.cocone (incl R K ⋙ diagram R K))

noncomputable def etaleCoconeIsColimit : IsColimit (etaleCocone R K) :=
  (Functor.Final.isColimitExtendCoconeEquiv _ _).symm (colimit.isColimit _)

namespace etaleColimit

variable {R K}

noncomputable def of (X : PointedEtale R K) : X →+* etaleColimit R K :=
  ((etaleCocone R K).ι.app X).hom

theorem of_map {X Y : PointedEtale R K} (f : X ⟶ Y) (x : X) : of Y (f.alg x) = of X x :=
  congr($((etaleCocone R K).w f) x)

theorem exists_of (y : etaleColimit R K) : ∃ (X : PointedEtale R K) (x : X), of X x = y := by
  obtain ⟨j, x, hx⟩ := Concrete.colimit_exists_rep (incl R K ⋙ diagram R K) y
  refine ⟨(incl R K).obj j, x, ?_⟩
  have := Functor.Final.extendCocone_obj_ι_app' (G := diagram R K)
    (colimit.cocone (incl R K ⋙ diagram R K)) (𝟙 ((incl R K).obj j))
  rw [← hx]
  change ((etaleCocone R K).ι.app ((incl R K).obj j)).hom x = _
  simp only [etaleCocone, this, CategoryTheory.Functor.map_id, Category.id_comp]
  rfl

theorem exists_of_finset (s : Finset (etaleColimit R K)) :
    ∃ X : PointedEtale R K, ∀ y ∈ s, y ∈ Set.range (of X) := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨base, by simp⟩
  | insert a s _ ih =>
    obtain ⟨X, hX⟩ := ih
    obtain ⟨Y, y, rfl⟩ := exists_of a
    refine ⟨IsFiltered.max X Y, fun z hz ↦ ?_⟩
    rcases Finset.mem_insert.1 hz with rfl | hz
    · exact ⟨(IsFiltered.rightToMax X Y).alg y, of_map _ _⟩
    · obtain ⟨x, rfl⟩ := hX z hz
      exact ⟨(IsFiltered.leftToMax X Y).alg x, of_map _ _⟩

noncomputable def ptCocone : Cocone (diagram R K) where
  pt := CommRingCat.of K
  ι := { app X := CommRingCat.ofHom X.pt.toRingHom
         naturality X Y f := by ext x; exact pt_alg f x }

noncomputable def toK : etaleColimit R K →+* K :=
  ((etaleCoconeIsColimit R K).desc ptCocone).hom

@[simp]
theorem toK_of (X : PointedEtale R K) (x : X) : toK (of X x) = X.pt x :=
  congr($((etaleCoconeIsColimit R K).fac ptCocone X) x)

noncomputable instance : Algebra R (etaleColimit R K) := (of (base : PointedEtale R K)).toAlgebra

theorem algebraMap_eq_of_base : algebraMap R (etaleColimit R K) = of base := rfl

@[simp]
theorem toK_algebraMap (r : R) : toK (algebraMap R (etaleColimit R K) r) = algebraMap R K r :=
  toK_of base r

theorem of_algebraMap (X : PointedEtale R K) (r : R) :
    of X (algebraMap R X r) = algebraMap R (etaleColimit R K) r :=
  of_map (fromBase X) r

noncomputable def ofAlgHom (X : PointedEtale R K) : X →ₐ[R] etaleColimit R K :=
  { of X with commutes' := of_algebraMap X }

@[simp]
theorem ofAlgHom_apply (X : PointedEtale R K) (x : X) : ofAlgHom X x = of X x := rfl

noncomputable def toKAlgHom : etaleColimit R K →ₐ[R] K :=
  { toK with commutes' := fun r ↦ (toK_of base r).trans rfl }

@[simp]
theorem toKAlgHom_apply (y : etaleColimit R K) : toKAlgHom y = toK y := rfl

theorem isUnit_of_toK_ne_zero {y : etaleColimit R K} (hy : toK y ≠ 0) : IsUnit y := by
  obtain ⟨X, x, rfl⟩ := exists_of y
  rw [toK_of] at hy
  have hu : IsUnit (X.pt x) := isUnit_iff_ne_zero.2 hy
  rw [← of_map (X.toAway x hu) x]
  exact (isUnit_toAway X x hu).map _

theorem isUnit_iff_toK_ne_zero (y : etaleColimit R K) : IsUnit y ↔ toK y ≠ 0 :=
  ⟨fun h ↦ (h.map toK).ne_zero, isUnit_of_toK_ne_zero⟩

instance : Nontrivial (etaleColimit R K) :=
  ⟨⟨0, 1, fun h ↦ zero_ne_one (congr_arg toK h |>.trans toK.map_one |>.symm.trans
    (map_zero toK) |>.symm)⟩⟩

instance isLocalRing : IsLocalRing (etaleColimit R K) :=
  .of_nonunits_add fun a b ha hb ↦ by
    simp only [mem_nonunits_iff, isUnit_iff_toK_ne_zero, not_not] at ha hb ⊢
    rw [map_add, ha, hb, add_zero]

theorem maximalIdeal_eq : maximalIdeal (etaleColimit R K) = RingHom.ker toK := by
  ext y
  rw [mem_maximalIdeal, mem_nonunits_iff, isUnit_iff_toK_ne_zero, not_not, RingHom.mem_ker]

theorem residue_eq_zero_iff_toK_eq_zero (y : etaleColimit R K) : residue _ y = 0 ↔ toK y = 0 := by
  rw [IsLocalRing.residue_eq_zero_iff, maximalIdeal_eq, RingHom.mem_ker]

theorem exists_monic_lift (F : (etaleColimit R K)[X]) (hF : F.Monic) :
    ∃ (X : PointedEtale R K) (q : X[X]), q.Monic ∧ q.map (of X) = F := by
  classical
  obtain ⟨X, hX⟩ := exists_of_finset (F.support.image F.coeff)
  have hl : F ∈ lifts (of X) := by
    rw [lifts_iff_coeff_lifts]
    intro n
    by_cases hn : n ∈ F.support
    · exact hX _ (Finset.mem_image_of_mem _ hn)
    · rw [notMem_support_iff.1 hn]
      exact ⟨0, map_zero _⟩
  obtain ⟨q, hq, -, hqm⟩ := lifts_and_degree_eq_and_monic hl hF
  exact ⟨X, q, hqm, hq⟩

theorem henselianLocalRing (hK : Function.Surjective (toK : etaleColimit R K →+* K)) :
    HenselianLocalRing (etaleColimit R K) := by
  refine ((HenselianLocalRing.TFAE (etaleColimit R K)).out 0 2).2 ?_
  intro K' _ φ hφ F hF a₀ h₁ h₂

  have hker : RingHom.ker φ = RingHom.ker toK := by
    rw [← maximalIdeal_eq, ← IsLocalRing.ker_eq_maximalIdeal φ hφ]
  let e : K' ≃+* K := (RingHom.quotientKerEquivOfSurjective hφ).symm.trans
    ((Ideal.quotEquivOfEq hker).trans (RingHom.quotientKerEquivOfSurjective hK))
  have he : ∀ y, e (φ y) = toK y := by
    intro y
    simp [e]
  obtain ⟨X, q, hq, rfl⟩ := exists_monic_lift F hF
  have hc : (toK.comp (of X)) = X.pt.toRingHom := by ext x; simp
  have hφ' : (e : K' →+* K).comp φ = toK := RingHom.ext he
  have key : ∀ p : X[X], p.eval₂ X.pt.toRingHom (e a₀) = e ((p.map (of X)).eval₂ φ a₀) := by
    intro p
    rw [← RingEquiv.coe_toRingHom, hom_eval₂, eval₂_map, hφ', hc]
  obtain ⟨Y, f, b, hb, hbY⟩ := X.exists_hom_root q hq (e a₀)
    (by rw [key, h₁, map_zero])
    (by rw [key, ← derivative_map]; exact (map_ne_zero e).2 h₂)
  have hXY : of X = (of Y).comp f.alg.toRingHom := by
    ext x
    exact (of_map f x).symm
  refine ⟨of Y b, ?_, ?_⟩
  · rw [IsRoot, Polynomial.eval_map, hXY, ← hom_eval₂, hb, map_zero]
  · apply e.injective
    rw [he, toK_of, hbY]

theorem of_incl_eq (j : Std R K) (a : (incl R K).obj j) :
    of ((incl R K).obj j) a = (colimit.ι (incl R K ⋙ diagram R K) j).hom a := by
  have h := Functor.Final.extendCocone_obj_ι_app' (colimit.cocone (incl R K ⋙ diagram R K))
    (𝟙 ((incl R K).obj j))
  change ((Functor.Final.extendCocone.obj (colimit.cocone (incl R K ⋙ diagram R K))).ι.app
    ((incl R K).obj j)).hom a = _
  rw [h]
  rfl

theorem exists_hom_eq_of_of_eq {X : PointedEtale R K} {x y : X} (h : of X x = of X y) :
    ∃ (Y : PointedEtale R K) (f : X ⟶ Y), f.alg x = f.alg y := by
  obtain ⟨j, ⟨e⟩⟩ := exists_hom_incl X
  rw [← of_map e x, ← of_map e y, of_incl_eq, of_incl_eq] at h
  obtain ⟨k, f, g, hfg⟩ :=
    Concrete.colimit_exists_of_rep_eq (incl R K ⋙ diagram R K) (e.alg x) (e.alg y) h
  refine ⟨(incl R K).obj (IsFiltered.coeq f g), e ≫ (incl R K).map (f ≫ IsFiltered.coeqHom f g), ?_⟩
  have h2 : ((incl R K).map (IsFiltered.coeqHom f g)).alg (((incl R K).map f).alg (e.alg x)) =
      ((incl R K).map (IsFiltered.coeqHom f g)).alg (((incl R K).map g).alg (e.alg y)) :=
    congr_arg (fun z ↦ ((incl R K).map (IsFiltered.coeqHom f g)).alg z) hfg
  have h3 : (incl R K).map (f ≫ IsFiltered.coeqHom f g) =
      (incl R K).map (g ≫ IsFiltered.coeqHom f g) := by
    rw [IsFiltered.coeq_condition f g]
  calc (e ≫ (incl R K).map (f ≫ IsFiltered.coeqHom f g)).alg x
      = ((incl R K).map (IsFiltered.coeqHom f g)).alg (((incl R K).map f).alg (e.alg x)) := rfl
    _ = ((incl R K).map (IsFiltered.coeqHom f g)).alg (((incl R K).map g).alg (e.alg y)) := h2
    _ = (e ≫ (incl R K).map (g ≫ IsFiltered.coeqHom f g)).alg y := rfl
    _ = (e ≫ (incl R K).map (f ≫ IsFiltered.coeqHom f g)).alg y := by rw [h3]

end etaleColimit

end PositivityTheory.HtPt.Htat.Hens
