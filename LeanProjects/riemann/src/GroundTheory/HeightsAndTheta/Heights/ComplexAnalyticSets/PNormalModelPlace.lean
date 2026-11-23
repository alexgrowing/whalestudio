import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StNormalModelPlace
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

noncomputable section

namespace NormalModelPlace

theorem ord_eq_of_ringEquiv {A C : Type*} [CommRing A] [CommRing C] (e : A ≃+* C) (x : A) :
    Ring.ord A x = Ring.ord C (e x) := by
  have hJ : Ideal.span {e x} = (Ideal.span {x}).map e := by
    rw [Ideal.map_span, Set.image_singleton]
  let qe := Ideal.quotientEquiv (Ideal.span {x}) (Ideal.span {e x}) e hJ
  have : RingHomSurjective (e : A →+* C) := ⟨e.surjective⟩
  let f : (A ⧸ Ideal.span {x}) →ₛₗ[(e : A →+* C)] (C ⧸ Ideal.span {e x}) :=
    { toFun := qe
      map_add' := qe.map_add
      map_smul' := fun a b => by
        obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective b
        change Ideal.Quotient.mk _ (e (a * b)) = Ideal.Quotient.mk _ (e a * e b)
        rw [map_mul] }
  rw [Ring.ord, Ring.ord, Module.length, Module.length, WithBot.unbot_inj,
    Order.krullDim_eq_of_orderIso (Submodule.orderIsoMapComapOfBijective f qe.bijective)]

theorem not_isUnit_mk_of_mem_maximalIdeal {L : Type*} [CommRing L] [IsLocalRing L] {I : Ideal L} (hI : I ≠ ⊤)
    {z : L} (hz : z ∈ IsLocalRing.maximalIdeal L) : ¬ IsUnit (Ideal.Quotient.mk I z) := by
  intro hu
  obtain ⟨u, hu⟩ := hu.exists_right_inv
  obtain ⟨u, rfl⟩ := Ideal.Quotient.mk_surjective u
  rw [← map_mul, ← map_one (Ideal.Quotient.mk I), Ideal.Quotient.eq] at hu
  have h1 := IsLocalRing.le_maximalIdeal hI hu
  have h2 := (IsLocalRing.maximalIdeal L).mul_mem_right u hz
  exact (IsLocalRing.maximalIdeal.isMaximal L).ne_top
    ((Ideal.eq_top_iff_one _).2 (by simpa using (IsLocalRing.maximalIdeal L).sub_mem h2 h1))

variable {n : ℕ} {J : Ideal (MvPolynomial (Fin n) ℂ)} (M : IndefiniteRowSideFullHecke.ComplexSets.NormalModel J) (w : Fin n ⊕ Fin M.m → ℂ)

theorem eval_rename_inl (f : MvPolynomial (Fin n) ℂ) :
    eval w (rename Sum.inl f) = eval (IndefiniteRowSideFullHecke.ComplexSets.firstCoords w) f := by
  rw [eval_rename]; rfl

theorem rename_mem_normalModel {f : MvPolynomial (Fin n) ℂ} (hf : f ∈ J) : rename Sum.inl f ∈ M.ideal := by
  rw [← M.comap_eq] at hf; exact hf

theorem normalModel_le_ker (hw : w ∈ IndefiniteRowSideFullHecke.ComplexSets.zeroSetIn M.ideal) :
    M.ideal ≤ RingHom.ker (eval w : MvPolynomial (Fin n ⊕ Fin M.m) ℂ →+* ℂ) :=
  fun p hp => RingHom.mem_ker.2 (hw p hp)

theorem le_ker_firstCoords (hw : w ∈ IndefiniteRowSideFullHecke.ComplexSets.zeroSetIn M.ideal) :
    J ≤ RingHom.ker (eval (IndefiniteRowSideFullHecke.ComplexSets.firstCoords w) : MvPolynomial (Fin n) ℂ →+* ℂ) := by
  intro f hf
  rw [RingHom.mem_ker, ← eval_rename_inl]
  exact hw _ (rename_mem_normalModel M hf)

def toPointLocalization :
    Localization.AtPrime (RingHom.ker (eval (IndefiniteRowSideFullHecke.ComplexSets.firstCoords w) : MvPolynomial (Fin n) ℂ →+* ℂ)) →+*
      Localization.AtPrime (RingHom.ker (eval w : MvPolynomial (Fin n ⊕ Fin M.m) ℂ →+* ℂ)) :=
  IsLocalization.map (T := (RingHom.ker (eval w : MvPolynomial (Fin n ⊕ Fin M.m) ℂ →+* ℂ)).primeCompl) _
    (rename Sum.inl : MvPolynomial (Fin n) ℂ →ₐ[ℂ] MvPolynomial (Fin n ⊕ Fin M.m) ℂ).toRingHom
    (fun s hs => by
      show rename Sum.inl s ∈ (RingHom.ker (eval w : MvPolynomial (Fin n ⊕ Fin M.m) ℂ →+* ℂ)).primeCompl
      rw [Ideal.mem_primeCompl_iff, RingHom.mem_ker, eval_rename_inl]
      exact fun h => (Ideal.mem_primeCompl_iff.1 hs) (RingHom.mem_ker.2 h))

def curveToPoint : curveLocalRing J (IndefiniteRowSideFullHecke.ComplexSets.firstCoords w) →+* pointLocalRing M.ideal w :=
  Ideal.quotientMap _ (toPointLocalization M w) (by
    rw [Ideal.map_le_iff_le_comap]
    intro f hf
    rw [Ideal.mem_comap, Ideal.mem_comap, toPointLocalization, IsLocalization.map_eq]
    exact Ideal.mem_map_of_mem _ (rename_mem_normalModel M hf))

theorem curveToPoint_algebraMap (f : MvPolynomial (Fin n) ℂ) :
    curveToPoint M w (algebraMap _ (curveLocalRing J (IndefiniteRowSideFullHecke.ComplexSets.firstCoords w)) f) =
      algebraMap (MvPolynomial (Fin n ⊕ Fin M.m) ℂ) (pointLocalRing M.ideal w) (rename Sum.inl f) := by
  change Ideal.quotientMap _ (toPointLocalization M w) _ (Ideal.Quotient.mk _ (algebraMap _ _ f)) =
    Ideal.Quotient.mk _ (algebraMap _ _ (rename Sum.inl f))
  rw [Ideal.quotientMap_mk, toPointLocalization, IsLocalization.map_eq]
  rfl

theorem isPrime_map_normalModel (hw : w ∈ IndefiniteRowSideFullHecke.ComplexSets.zeroSetIn M.ideal) :
    (M.ideal.map (algebraMap (MvPolynomial (Fin n ⊕ Fin M.m) ℂ)
      (Localization.AtPrime (RingHom.ker (eval w : MvPolynomial (Fin n ⊕ Fin M.m) ℂ →+* ℂ))))).IsPrime :=
  IsLocalization.isPrime_of_isPrime_disjoint
    (RingHom.ker (eval w : MvPolynomial (Fin n ⊕ Fin M.m) ℂ →+* ℂ)).primeCompl _ _ M.isPrime
    (Set.disjoint_left.2 fun _ ha hJ => (Ideal.mem_primeCompl_iff.1 ha) (normalModel_le_ker M w hw hJ))

theorem isPrime_map_curve (hJ : J.IsPrime) (hw : w ∈ IndefiniteRowSideFullHecke.ComplexSets.zeroSetIn M.ideal) :
    (J.map (algebraMap (MvPolynomial (Fin n) ℂ)
      (Localization.AtPrime (RingHom.ker (eval (IndefiniteRowSideFullHecke.ComplexSets.firstCoords w) :
        MvPolynomial (Fin n) ℂ →+* ℂ))))).IsPrime :=
  IsLocalization.isPrime_of_isPrime_disjoint
    (RingHom.ker (eval (IndefiniteRowSideFullHecke.ComplexSets.firstCoords w) : MvPolynomial (Fin n) ℂ →+* ℂ)).primeCompl _ _ hJ
    (Set.disjoint_left.2 fun _ ha hJ => (Ideal.mem_primeCompl_iff.1 ha) (le_ker_firstCoords M w hw hJ))

theorem algebraMap_pointLocalRing_eq_zero_iff (hw : w ∈ IndefiniteRowSideFullHecke.ComplexSets.zeroSetIn M.ideal)
    (b : MvPolynomial (Fin n ⊕ Fin M.m) ℂ) :
    algebraMap (MvPolynomial (Fin n ⊕ Fin M.m) ℂ) (pointLocalRing M.ideal w) b = 0 ↔ b ∈ M.ideal := by
  have h := IsLocalization.under_map_of_isPrime_disjoint
    (RingHom.ker (eval w : MvPolynomial (Fin n ⊕ Fin M.m) ℂ →+* ℂ)).primeCompl
    (Localization.AtPrime (RingHom.ker (eval w : MvPolynomial (Fin n ⊕ Fin M.m) ℂ →+* ℂ))) M.isPrime
    (Set.disjoint_left.2 fun _ ha hJ => (Ideal.mem_primeCompl_iff.1 ha) (normalModel_le_ker M w hw hJ))
  change (Ideal.Quotient.mk (M.ideal.map (algebraMap (MvPolynomial (Fin n ⊕ Fin M.m) ℂ)
      (Localization.AtPrime (RingHom.ker (eval w : MvPolynomial (Fin n ⊕ Fin M.m) ℂ →+* ℂ)))))
      (algebraMap _ _ b) = 0) ↔ _
  rw [Ideal.Quotient.eq_zero_iff_mem]
  conv_rhs => rw [← h]
  rfl

theorem curveToPoint_injective (hw : w ∈ IndefiniteRowSideFullHecke.ComplexSets.zeroSetIn M.ideal) :
    Function.Injective (curveToPoint M w) := by
  rw [injective_iff_map_eq_zero]
  intro x hx
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
  obtain ⟨⟨a, s⟩, rfl⟩ := IsLocalization.mk'_surjective
    (RingHom.ker (eval (IndefiniteRowSideFullHecke.ComplexSets.firstCoords w) : MvPolynomial (Fin n) ℂ →+* ℂ)).primeCompl y
  have hx' : (Ideal.Quotient.mk (M.ideal.map (algebraMap (MvPolynomial (Fin n ⊕ Fin M.m) ℂ)
      (Localization.AtPrime (RingHom.ker (eval w : MvPolynomial (Fin n ⊕ Fin M.m) ℂ →+* ℂ)))))
      (toPointLocalization M w (IsLocalization.mk' _ a s))) = 0 := hx
  rw [toPointLocalization, IsLocalization.map_mk', Ideal.Quotient.eq_zero_iff_mem,
    IsLocalization.mk'_mem_map_algebraMap_iff] at hx'
  obtain ⟨t, ht, hta⟩ := hx'
  have ha : rename Sum.inl a ∈ M.ideal :=
    (M.isPrime.mem_or_mem hta).resolve_left fun h => (Ideal.mem_primeCompl_iff.1 ht) (normalModel_le_ker M w hw h)
  have ha' : a ∈ J := by rw [← M.comap_eq]; exact ha
  change (Ideal.Quotient.mk (J.map (algebraMap (MvPolynomial (Fin n) ℂ)
      (Localization.AtPrime (RingHom.ker (eval (IndefiniteRowSideFullHecke.ComplexSets.firstCoords w) : MvPolynomial (Fin n) ℂ →+* ℂ)))))
      (IsLocalization.mk' _ a s)) = 0
  rw [Ideal.Quotient.eq_zero_iff_mem, IsLocalization.mk'_mem_map_algebraMap_iff]
  exact ⟨1, Submonoid.one_mem _, by rwa [one_mul]⟩

theorem isUnit_of_isUnit_curveToPoint (hw : w ∈ IndefiniteRowSideFullHecke.ComplexSets.zeroSetIn M.ideal)
    (x : curveLocalRing J (IndefiniteRowSideFullHecke.ComplexSets.firstCoords w)) (hx : IsUnit (curveToPoint M w x)) : IsUnit x := by
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
  obtain ⟨⟨a, s⟩, rfl⟩ := IsLocalization.mk'_surjective
    (RingHom.ker (eval (IndefiniteRowSideFullHecke.ComplexSets.firstCoords w) : MvPolynomial (Fin n) ℂ →+* ℂ)).primeCompl y
  by_cases ha : a ∈ RingHom.ker (eval (IndefiniteRowSideFullHecke.ComplexSets.firstCoords w) : MvPolynomial (Fin n) ℂ →+* ℂ)
  · exfalso
    have hx' : IsUnit (Ideal.Quotient.mk (M.ideal.map (algebraMap (MvPolynomial (Fin n ⊕ Fin M.m) ℂ)
        (Localization.AtPrime (RingHom.ker (eval w : MvPolynomial (Fin n ⊕ Fin M.m) ℂ →+* ℂ)))))
        (toPointLocalization M w (IsLocalization.mk' _ a s))) := hx
    rw [toPointLocalization, IsLocalization.map_mk'] at hx'
    refine not_isUnit_mk_of_mem_maximalIdeal (isPrime_map_normalModel M w hw).ne_top ?_ hx'
    refine (IsLocalization.AtPrime.mk'_mem_maximal_iff
      (Localization.AtPrime (RingHom.ker (eval w : MvPolynomial (Fin n ⊕ Fin M.m) ℂ →+* ℂ))) _ _ _).2 ?_
    change rename Sum.inl a ∈ RingHom.ker (eval w : MvPolynomial (Fin n ⊕ Fin M.m) ℂ →+* ℂ)
    rw [RingHom.mem_ker, eval_rename_inl]
    exact RingHom.mem_ker.1 ha
  · exact ((IsLocalization.AtPrime.isUnit_mk'_iff _ _ a s).2 ha).map _

theorem isIntegrallyClosed_pointLocalRing (hw : w ∈ IndefiniteRowSideFullHecke.ComplexSets.zeroSetIn M.ideal) :
    IsIntegrallyClosed (pointLocalRing M.ideal w) := by
  have := M.isPrime
  have : IsIntegrallyClosed (MvPolynomial (Fin n ⊕ Fin M.m) ℂ ⧸ M.ideal) := M.isIntegrallyClosed
  exact isIntegrallyClosed_of_isLocalization
    (Localization.AtPrime (RingHom.ker (eval w : MvPolynomial (Fin n ⊕ Fin M.m) ℂ →+* ℂ)) ⧸
      M.ideal.map (algebraMap (MvPolynomial (Fin n ⊕ Fin M.m) ℂ)
        (Localization.AtPrime (RingHom.ker (eval w : MvPolynomial (Fin n ⊕ Fin M.m) ℂ →+* ℂ)))))
    (Algebra.algebraMapSubmonoid (MvPolynomial (Fin n ⊕ Fin M.m) ℂ ⧸ M.ideal)
      (RingHom.ker (eval w : MvPolynomial (Fin n ⊕ Fin M.m) ℂ →+* ℂ)).primeCompl)
    (by
      rintro _ ⟨s, hs, rfl⟩
      refine mem_nonZeroDivisors_of_ne_zero fun h => (Ideal.mem_primeCompl_iff.1 hs) (normalModel_le_ker M w hw ?_)
      rw [Ideal.Quotient.algebraMap_eq] at h
      exact Ideal.Quotient.eq_zero_iff_mem.1 h)

end NormalModelPlace

end

set_option hygiene false in
local notation "𝒜" => MvPolynomial (Fin n) ℂ
set_option hygiene false in
local notation "ℬ" => MvPolynomial (Fin n ⊕ Fin M.m) ℂ
set_option hygiene false in
local notation "𝒪" => curveLocalRing J (IndefiniteRowSideFullHecke.ComplexSets.firstCoords w)
set_option hygiene false in
local notation "𝒪̄" => curveNormalisation J (IndefiniteRowSideFullHecke.ComplexSets.firstCoords w)
set_option hygiene false in
local notation "𝒯" => pointLocalRing M.ideal w
set_option hygiene false in
local notation "𝒦" => FractionRing (curveLocalRing J (IndefiniteRowSideFullHecke.ComplexSets.firstCoords w))
set_option hygiene false in
local notation "ℱ" => FractionRing (pointLocalRing M.ideal w)
set_option hygiene false in
local notation "𝔏" => Localization.AtPrime (RingHom.ker (eval w : MvPolynomial (Fin n ⊕ Fin M.m) ℂ →+* ℂ))

noncomputable section

theorem NormalModelPlace.proof : NormalModelPlace.Statement := by
  intro n J q M w hJ hw hwq
  subst hwq
  have := isPrime_map_curve M w hJ hw
  have := isPrime_map_normalModel M w hw
  have : IsDomain 𝒪 := Ideal.Quotient.isDomain _
  have : IsDomain 𝒯 := Ideal.Quotient.isDomain _
  have : IsLocalRing 𝒪 := IsLocalRing.of_surjective' (Ideal.Quotient.mk _) Ideal.Quotient.mk_surjective
  have : IsLocalRing 𝒯 := IsLocalRing.of_surjective' (Ideal.Quotient.mk _) Ideal.Quotient.mk_surjective
  have := isIntegrallyClosed_pointLocalRing M w hw
  have hg_alg := curveToPoint_algebraMap M w
  have hg_inj := curveToPoint_injective M w hw

  have hg_loc : (IsLocalRing.maximalIdeal 𝒯).comap (curveToPoint M w) = IsLocalRing.maximalIdeal 𝒪 := by
    refine le_antisymm (IsLocalRing.le_maximalIdeal
      (Ideal.comap_ne_top _ (IsLocalRing.maximalIdeal.isMaximal _).ne_top)) ?_
    intro x hx
    rw [Ideal.mem_comap, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    exact fun h => (IsLocalRing.mem_maximalIdeal _).1 hx (isUnit_of_isUnit_curveToPoint M w hw x h)

  have hι : Function.Injective (algebraMap 𝒯 ℱ) := IsFractionRing.injective _ _
  have hιg : Function.Injective ((algebraMap 𝒯 ℱ).comp (curveToPoint M w)) := hι.comp hg_inj
  obtain ⟨ψ, hψ⟩ : ∃ ψ : 𝒦 →+* ℱ, ∀ x, ψ (algebraMap 𝒪 𝒦 x) = algebraMap 𝒯 ℱ (curveToPoint M w x) :=
    ⟨IsFractionRing.lift hιg, IsFractionRing.lift_algebraMap hιg⟩
  have hψinj : Function.Injective ψ := ψ.injective
  have hcomp : (algebraMap 𝒯 ℱ).comp (curveToPoint M w) = ψ.comp (algebraMap 𝒪 𝒦) :=
    RingHom.ext fun x => (hψ x).symm
  obtain ⟨val, hval_inj, hval_alg, hval_int, hval_surj⟩ : ∃ val : 𝒪̄ →+* 𝒦, Function.Injective val ∧
      (∀ x, val (algebraMap 𝒪 𝒪̄ x) = algebraMap 𝒪 𝒦 x) ∧ (∀ x, IsIntegral 𝒪 (val x)) ∧
      (∀ k, IsIntegral 𝒪 k → ∃ x, val x = k) :=
    ⟨(integralClosure 𝒪 𝒦).val.toRingHom, Subtype.val_injective, fun _ => rfl,
      fun x => (mem_integralClosure_iff _ _).1 (Subtype.prop x),
      fun k hk => ⟨(⟨k, (mem_integralClosure_iff _ _).2 hk⟩ : integralClosure 𝒪 𝒦), rfl⟩⟩

  have hint : ∀ k : 𝒦, IsIntegral 𝒪 k → ∃ t : 𝒯, algebraMap 𝒯 ℱ t = ψ k := by
    rintro k ⟨p, hpm, hp⟩
    refine (IsIntegrallyClosed.isIntegral_iff (R := 𝒯) (K := ℱ)).1 ⟨p.map (curveToPoint M w), hpm.map _, ?_⟩
    rw [Polynomial.eval₂_map, hcomp, ← Polynomial.hom_eval₂, hp, map_zero]
  obtain ⟨φ, hφ⟩ : ∃ φ : 𝒪̄ →+* 𝒯, ∀ x, algebraMap 𝒯 ℱ (φ x) = ψ (val x) := by
    have hr : ∀ x, (ψ.comp val) x ∈ (algebraMap 𝒯 ℱ).range := fun x => hint _ (hval_int x)
    let e := RingEquiv.ofBijective (algebraMap 𝒯 ℱ).rangeRestrict
      ⟨fun a b h => hι (congrArg Subtype.val h), RingHom.rangeRestrict_surjective _⟩
    refine ⟨e.symm.toRingHom.comp ((ψ.comp val).codRestrict _ hr), fun x => ?_⟩
    exact congrArg Subtype.val (e.apply_symm_apply ((ψ.comp val).codRestrict _ hr x))
  have hφinj : Function.Injective φ := fun a b h => hval_inj (hψinj (by rw [← hφ, ← hφ, h]))
  have hφg : ∀ x, φ (algebraMap 𝒪 𝒪̄ x) = curveToPoint M w x := fun x => hι (by rw [hφ, hval_alg, hψ])
  have : IsDomain 𝒪̄ := hφinj.isDomain φ
  have : Algebra.IsIntegral 𝒪 𝒪̄ := inferInstanceAs (Algebra.IsIntegral 𝒪 (integralClosure 𝒪 𝒦))

  obtain ⟨P, hP⟩ : ∃ P : Ideal 𝒪̄, P = (IsLocalRing.maximalIdeal 𝒯).comap φ := ⟨_, rfl⟩
  have : P.IsPrime := by rw [hP]; exact Ideal.comap_isPrime _ _
  have hPmem : ∀ x, x ∈ P ↔ φ x ∈ IsLocalRing.maximalIdeal 𝒯 := fun x => by rw [hP, Ideal.mem_comap]
  have hPmax : P.IsMaximal := by
    refine Ideal.isMaximal_of_isIntegral_of_isMaximal_comap (R := 𝒪) P ?_
    rw [hP, Ideal.comap_comap, show φ.comp (algebraMap 𝒪 𝒪̄) = curveToPoint M w from RingHom.ext hφg, hg_loc]
    exact IsLocalRing.maximalIdeal.isMaximal _
  have hunits : ∀ y : P.primeCompl, IsUnit (φ y) := fun y => by
    by_contra h
    exact y.2 ((hPmem _).2 ((IsLocalRing.mem_maximalIdeal _).2 h))

  have hY : ∀ i, ∃ y : 𝒪̄, φ y = algebraMap ℬ 𝒯 (X (Sum.inr i)) := by
    intro i
    obtain ⟨a, b, hb, hab⟩ := M.birational i
    obtain ⟨p, hpm, hp⟩ := M.integral i
    have hrel : algebraMap ℬ 𝒯 (rename Sum.inl b) * algebraMap ℬ 𝒯 (X (Sum.inr i)) =
        algebraMap ℬ 𝒯 (rename Sum.inl a) := by
      rw [← sub_eq_zero, ← map_mul, ← map_sub]
      exact (algebraMap_pointLocalRing_eq_zero_iff M w hw _).2 hab
    have hb0 : algebraMap 𝒯 ℱ (algebraMap ℬ 𝒯 (rename Sum.inl b)) ≠ 0 := by
      rw [map_ne_zero_iff _ hι]
      intro h
      exact hb (by rw [← M.comap_eq]; exact (algebraMap_pointLocalRing_eq_zero_iff M w hw _).1 h)
    have hk : ψ (algebraMap 𝒪 𝒦 (algebraMap 𝒜 𝒪 a) / algebraMap 𝒪 𝒦 (algebraMap 𝒜 𝒪 b)) =
        algebraMap 𝒯 ℱ (algebraMap ℬ 𝒯 (X (Sum.inr i))) := by
      rw [map_div₀, hψ, hψ, hg_alg, hg_alg]
      refine (eq_div_of_mul_eq hb0 ?_).symm
      rw [← map_mul, mul_comm, hrel]
    have hkint : IsIntegral 𝒪 (algebraMap 𝒪 𝒦 (algebraMap 𝒜 𝒪 a) / algebraMap 𝒪 𝒦 (algebraMap 𝒜 𝒪 b)) := by
      refine ⟨p.map (algebraMap 𝒜 𝒪), hpm.map _, hψinj ?_⟩
      have h1 : (ψ.comp (algebraMap 𝒪 𝒦)).comp (algebraMap 𝒜 𝒪) =
          (algebraMap 𝒯 ℱ).comp ((algebraMap ℬ 𝒯).comp (rename Sum.inl : 𝒜 →ₐ[ℂ] ℬ).toRingHom) :=
        RingHom.ext fun f => by simp [hψ, hg_alg]
      have h2 : algebraMap 𝒯 ℱ (algebraMap ℬ 𝒯 (p.eval₂ (rename Sum.inl : 𝒜 →ₐ[ℂ] ℬ).toRingHom (X (Sum.inr i)))) =
          p.eval₂ ((algebraMap 𝒯 ℱ).comp ((algebraMap ℬ 𝒯).comp (rename Sum.inl : 𝒜 →ₐ[ℂ] ℬ).toRingHom))
            (algebraMap 𝒯 ℱ (algebraMap ℬ 𝒯 (X (Sum.inr i)))) := by
        rw [Polynomial.hom_eval₂, Polynomial.hom_eval₂]
      rw [map_zero, Polynomial.hom_eval₂, Polynomial.eval₂_map, hk, h1, ← h2,
        (algebraMap_pointLocalRing_eq_zero_iff M w hw _).2 hp, map_zero]
    obtain ⟨y, hy⟩ := hval_surj _ hkint
    exact ⟨y, hι (by rw [hφ, hy, hk])⟩

  obtain ⟨χ, hχ⟩ : ∃ χ : ℬ →+* 𝒪̄, ∀ b, φ (χ b) = algebraMap ℬ 𝒯 b := by
    choose y hy using hY
    refine ⟨eval₂Hom ((algebraMap 𝒪 𝒪̄).comp ((algebraMap 𝒜 𝒪).comp C))
      (Sum.elim (fun j => algebraMap 𝒪 𝒪̄ (algebraMap 𝒜 𝒪 (X j))) y), fun b => ?_⟩
    have h : φ.comp (eval₂Hom ((algebraMap 𝒪 𝒪̄).comp ((algebraMap 𝒜 𝒪).comp C))
        (Sum.elim (fun j => algebraMap 𝒪 𝒪̄ (algebraMap 𝒜 𝒪 (X j))) y)) = algebraMap ℬ 𝒯 := by
      refine MvPolynomial.ringHom_ext (fun c => ?_) (fun v => ?_)
      · simp only [RingHom.comp_apply, eval₂Hom_C, hφg, hg_alg, rename_C]
      · rcases v with j | i
        · simp only [RingHom.comp_apply, eval₂Hom_X', Sum.elim_inl, hφg, hg_alg, rename_X]
        · simp only [RingHom.comp_apply, eval₂Hom_X', Sum.elim_inr, hy]
    exact RingHom.congr_fun h b

  have hΦ : ∀ x, IsLocalization.lift hunits (algebraMap 𝒪̄ (Localization.AtPrime P) x) = φ x :=
    IsLocalization.lift_eq hunits
  have hΦinj : Function.Injective (IsLocalization.lift (S := Localization.AtPrime P) hunits) := by
    refine (IsLocalization.lift_injective_iff (M := P.primeCompl) (S := Localization.AtPrime P) (hg := hunits)).2
      fun x y => ⟨fun h => congrArg φ ?_, fun h => congrArg _ (hφinj h)⟩
    exact IsLocalization.injective (Localization.AtPrime P) (Ideal.primeCompl_le_nonZeroDivisors P) h
  have hΦsurj : Function.Surjective (IsLocalization.lift (S := Localization.AtPrime P) hunits) := by
    intro t
    obtain ⟨z, rfl⟩ := Ideal.Quotient.mk_surjective t
    obtain ⟨⟨b, s⟩, rfl⟩ := IsLocalization.mk'_surjective (RingHom.ker (eval w : ℬ →+* ℂ)).primeCompl z
    dsimp only
    have hs : χ s ∈ P.primeCompl := fun h => (IsLocalRing.mem_maximalIdeal _).1 ((hPmem _).1 h) (by
      rw [hχ]
      exact isUnit_algebraMap_pointLocalRing _ _ _ fun h0 => (Ideal.mem_primeCompl_iff.1 s.2) (RingHom.mem_ker.2 h0))
    refine ⟨IsLocalization.mk' (Localization.AtPrime P) (χ b) ⟨χ s, hs⟩, ?_⟩
    refine (IsLocalization.lift_mk'_spec _ _ _ _).2 ?_
    rw [hχ, hχ]
    change Ideal.Quotient.mk (M.ideal.map (algebraMap ℬ 𝔏)) (algebraMap ℬ 𝔏 b) =
      Ideal.Quotient.mk (M.ideal.map (algebraMap ℬ 𝔏)) (algebraMap ℬ 𝔏 (s : ℬ)) *
        Ideal.Quotient.mk (M.ideal.map (algebraMap ℬ 𝔏)) (IsLocalization.mk' 𝔏 b s)
    rw [← map_mul, IsLocalization.mk'_spec']

  refine ⟨⟨P, hPmax⟩, fun f => ?_⟩
  refine (ord_eq_of_ringEquiv (RingEquiv.ofBijective _ ⟨hΦinj, hΦsurj⟩) _).trans ?_
  congr 1
  change IsLocalization.lift hunits (algebraMap 𝒪̄ (Localization.AtPrime P) (algebraMap 𝒪 𝒪̄ (algebraMap 𝒜 𝒪 f))) = _
  rw [hΦ, hφg, hg_alg]

end

end GroundTheory.Heights₂.Heights
