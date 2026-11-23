import Mathlib
import Development.AbelianVarietyTheory.Definitions.KeyFormula.GeomIntSelf
import Development.AbelianVarietyTheory.Statements.FundamentalDomains.AtOfNumberField
import Development.AbelianVarietyTheory.Statements.ThetaLevelCharacters.MemThetaLevelCharDimZero
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.GeometricallyIntegralOfIsIntegralOfIsAlgClosed
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.IsRegularRingOfSmooth
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsRegularOfSupportDimQuotientAddLengthLe
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.KeyPow GlobalTheory.KeyFam GlobalTheory.ZM GlobalTheory.AbLaw

namespace GlobalTheory.GeomComp

theorem exists_idempotent {A : Type} [CommRing A] [IsNoetherianRing A]
    (h : ∀ (q : Ideal A) [q.IsPrime], IsDomain (Localization.AtPrime q)) (P : Ideal A) [P.IsPrime] :
    ∃ e : A, IsIdempotentElem e ∧ e ∉ P ∧ ∀ x y : A, e * (x * y) = 0 → e * x = 0 ∨ e * y = 0 := by
  classical
  let z : ∀ (q : Ideal A) [q.IsPrime], Ideal A := fun q _ =>
    RingHom.ker (algebraMap A (Localization.AtPrime q))
  have zp : ∀ (q : Ideal A) [q.IsPrime], (z q).IsPrime := fun q _ =>
    haveI := h q
    RingHom.ker_isPrime _
  have zm : ∀ (q : Ideal A) [q.IsPrime] (a : A), a ∈ z q ↔ ∃ s ∉ q, s * a = 0 := fun q _ a => by
    rw [RingHom.mem_ker, IsLocalization.map_eq_zero_iff q.primeCompl]
    exact ⟨fun ⟨s, hs⟩ => ⟨s, s.2, hs⟩, fun ⟨s, hs, hs'⟩ => ⟨⟨s, hs⟩, hs'⟩⟩
  have zle : ∀ (q r : Ideal A) [q.IsPrime] [r.IsPrime], r ≤ q → z q ≤ r := fun q r _ hr hrq a ha => by
    obtain ⟨s, hs, hs'⟩ := (zm q a).1 ha
    exact (hr.mem_or_mem (hs' ▸ r.zero_mem)).resolve_left fun h => hs (hrq h)
  have htop : z P ⊔ (z P).annihilator = ⊤ := by
    by_contra hne
    obtain ⟨m, hm, hle⟩ := Ideal.exists_le_maximal _ hne
    haveI := hm.isPrime
    haveI := zp P
    haveI := zp m
    have h1 : z m ≤ z P := zle m (z P) (le_sup_left.trans hle)
    have h2 : z P ≤ z m := zle P (z m) (h1.trans (zle P P le_rfl))
    obtain ⟨s, hs⟩ := IsNoetherian.noetherian (z P)
    have h3 : ∀ a : s, ∃ t ∉ m, t * (a : A) = 0 := fun a =>
      (zm m a).1 (h2 (by rw [← hs]; exact Submodule.subset_span a.2))
    choose t ht ht' using h3
    have h4 : ∏ a, t a ∈ (z P).annihilator := by
      rw [← hs, Submodule.mem_annihilator_span]
      intro a
      obtain ⟨r, hr⟩ : t a ∣ ∏ a, t a := Finset.dvd_prod_of_mem t (Finset.mem_univ _)
      rw [hr, smul_eq_mul, mul_right_comm, ht', zero_mul]
    obtain ⟨a, -, ha⟩ := Ideal.IsPrime.prod_mem_iff.1 (le_sup_right.trans hle h4)
    exact ht a ha
  obtain ⟨f, hf, e, he, hfe⟩ := Submodule.mem_sup.1 (htop ▸ Submodule.mem_top : (1 : A) ∈ _)
  have hk : ∀ a ∈ z P, e * a = 0 := fun a ha => Submodule.mem_annihilator.1 he a ha
  have hfP : f ∈ P := zle P P le_rfl hf
  have heP : e ∉ P := fun h' =>
    Ideal.IsPrime.ne_top ‹_› ((Ideal.eq_top_iff_one _).2 (hfe ▸ P.add_mem hfP h'))
  refine ⟨e, ?_, heP, fun x y hxy => ?_⟩
  · have := hk f hf
    unfold IsIdempotentElem
    linear_combination e * hfe - this
  · exact ((zp P).mem_or_mem ((zm P _).2 ⟨e, heP, hxy⟩)).imp (hk x) (hk y)

theorem isDomain_away {A : Type} [CommRing A] {e : A} (he : IsIdempotentElem e) (h0 : e ≠ 0)
    (h : ∀ x y : A, e * (x * y) = 0 → e * x = 0 ∨ e * y = 0)
    (S : Type) [CommRing S] [Algebra A S] [IsLocalization.Away e S] : IsDomain S := by
  have hz : ∀ a : A, algebraMap A S a = 0 ↔ e * a = 0 := fun a => by
    rw [IsLocalization.map_eq_zero_iff (Submonoid.powers e)]
    refine ⟨fun ⟨⟨_, n, rfl⟩, hn⟩ => ?_, fun h => ⟨⟨e, Submonoid.mem_powers e⟩, h⟩⟩
    have h1 : e ^ (n + 1) * a = 0 := by
      rw [pow_succ', _root_.mul_assoc]
      exact (congrArg (e * ·) hn).trans (mul_zero _)
    rwa [he.pow_succ_eq] at h1
  have hs := IsLocalization.Away.algebraMap_surjective_of_isIdempotentElem e he (S := S)
  haveI : Nontrivial S := ⟨1, 0, fun h1 => h0 (by simpa using (hz 1).1 (by rw [map_one, h1]))⟩
  haveI : NoZeroDivisors S := ⟨fun {a b} hab => by
    obtain ⟨x, rfl⟩ := hs a
    obtain ⟨y, rfl⟩ := hs b
    rw [← map_mul, hz] at hab
    rw [hz, hz]
    exact h x y hab⟩
  exact NoZeroDivisors.to_isDomain S

theorem isDomain_tensor_of_isAlgClosed (K A : Type) [Field K] [IsAlgClosed K] [CommRing A] [IsDomain A]
    [Algebra K A] [Algebra.FiniteType K A] (F : Type) [Field F] [Algebra K F] : IsDomain (F ⊗[K] A) := by
  let f : Spec (.of A) ⟶ Spec (.of K) := Spec.map (CommRingCat.ofHom (algebraMap K A))
  have hf : LocallyOfFiniteType f := by
    rw [HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)]
    exact RingHom.finiteType_algebraMap.2 inferInstance
  have hi : IsIntegral (Over.mk f).left := inferInstanceAs (IsIntegral (Spec (.of A)))
  have hg : GeometricallyIntegral f :=
    GlobalTheory.geometricallyIntegral_of_isIntegral_of_isAlgClosed K (Over.mk f) hf
  let y := Spec.map (CommRingCat.ofHom (algebraMap K F))
  have : IsIntegral (pullback y f) :=
    pullback_of_geometrically' GeometricallyIntegral.geometrically_isIntegral F y
  have : IsIntegral (Spec (.of (F ⊗[K] A))) := IsIntegral.of_isIso (pullbackSpecIso K F A).hom
  exact (affine_isIntegral_iff (.of (F ⊗[K] A))).mp this

theorem isDomain_tensor_of_closure (k Ω S : Type) [Field k] [Field Ω] [IsAlgClosed Ω] [Algebra k Ω]
    [Algebra.IsAlgebraic k Ω] [CommRing S] [Algebra k S] [Algebra.FiniteType k S] [IsDomain (Ω ⊗[k] S)]
    (F : Type) [Field F] [Algebra k F] : IsDomain (F ⊗[k] S) := by
  let L := AlgebraicClosure F
  let j : Ω →ₐ[k] L := IsAlgClosed.lift
  letI : Algebra Ω L := j.toRingHom.toAlgebra
  haveI : IsScalarTower k Ω L := IsScalarTower.of_algebraMap_eq fun x => (j.commutes x).symm
  haveI := isDomain_tensor_of_isAlgClosed Ω (Ω ⊗[k] S) L
  haveI : IsDomain (L ⊗[k] S) :=
    (Algebra.TensorProduct.cancelBaseChange k Ω L L S).symm.toMulEquiv.isDomain _
  let φ := Algebra.TensorProduct.map (IsScalarTower.toAlgHom k F L) (AlgHom.id k S)
  have hφ : Function.Injective φ :=
    Module.Flat.rTensor_preserves_injective_linearMap (M := S)
      (IsScalarTower.toAlgHom k F L).toLinearMap (algebraMap F L).injective
  exact Function.Injective.isDomain φ.toRingHom hφ

theorem geomInt_away (k Ω B : Type) [Field k] [Field Ω] [IsAlgClosed Ω] [Algebra k Ω]
    [Algebra.IsAlgebraic k Ω] [CommRing B] [Algebra k B] [Algebra.Smooth k B] (e : B)
    (he : IsIdempotentElem e) (h0 : ((1 : Ω) ⊗ₜ[k] e) ≠ 0)
    (h : ∀ x y : Ω ⊗[k] B, ((1 : Ω) ⊗ₜ[k] e) * (x * y) = 0 →
      ((1 : Ω) ⊗ₜ[k] e) * x = 0 ∨ ((1 : Ω) ⊗ₜ[k] e) * y = 0) :
    GeomInt k (Localization.Away e) := by
  haveI : Algebra.Smooth B (Localization.Away e) := Algebra.Smooth.of_isLocalization_Away e
  haveI : Algebra.Smooth k (Localization.Away e) := Algebra.Smooth.comp k B _
  refine ⟨this, fun F _ _ => ?_⟩
  letI : Algebra (Ω ⊗[k] B) (Ω ⊗[k] Localization.Away e) :=
    (Algebra.TensorProduct.map (AlgHom.id Ω Ω)
      (IsScalarTower.toAlgHom k B (Localization.Away e))).toAlgebra
  haveI : IsScalarTower Ω (Ω ⊗[k] B) (Ω ⊗[k] Localization.Away e) :=
    IsScalarTower.of_algebraMap_eq fun x => by
      simp [RingHom.algebraMap_toAlgebra]
  have hloc := IsLocalization.tensorProduct_tensorProduct_right k Ω (Submonoid.powers e)
    (Localization.Away e) (by ext; simp [RingHom.algebraMap_toAlgebra])
  rw [Submonoid.map_powers] at hloc
  have he' : IsIdempotentElem ((1 : Ω) ⊗ₜ[k] e) :=
    he.map (Algebra.TensorProduct.includeRight (R := k) (A := Ω) (B := B))
  haveI : IsLocalization.Away ((1 : Ω) ⊗ₜ[k] e) (Ω ⊗[k] Localization.Away e) := hloc
  haveI := isDomain_away he' h0 h (Ω ⊗[k] Localization.Away e)
  exact isDomain_tensor_of_closure k Ω _ F

theorem geomInt_away_baseChange (K k Ω R : Type) [Field K] [Field k] [Field Ω] [IsAlgClosed Ω] [Algebra K k]
    [Algebra k Ω] [Algebra K Ω] [IsScalarTower K k Ω] [Algebra.IsAlgebraic k Ω] [CommRing R] [Algebra K R]
    [Algebra.Smooth K R] (e : k ⊗[K] R) (he : IsIdempotentElem e)
    (h0 : Algebra.TensorProduct.map (IsScalarTower.toAlgHom K k Ω) (AlgHom.id K R) e ≠ 0)
    (h : ∀ x y : Ω ⊗[K] R,
      Algebra.TensorProduct.map (IsScalarTower.toAlgHom K k Ω) (AlgHom.id K R) e * (x * y) = 0 →
      Algebra.TensorProduct.map (IsScalarTower.toAlgHom K k Ω) (AlgHom.id K R) e * x = 0 ∨
      Algebra.TensorProduct.map (IsScalarTower.toAlgHom K k Ω) (AlgHom.id K R) e * y = 0) :
    GeomInt k (Localization.Away e) := by
  let φ := Algebra.TensorProduct.cancelBaseChange K k Ω Ω R
  have hφ : ∀ x : k ⊗[K] R, φ ((1 : Ω) ⊗ₜ[k] x) =
      Algebra.TensorProduct.map (IsScalarTower.toAlgHom K k Ω) (AlgHom.id K R) x := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul a r => simp [φ, Algebra.smul_def]
    | add x y hx hy => simp only [TensorProduct.tmul_add, map_add, hx, hy]
  refine geomInt_away k Ω (k ⊗[K] R) e he (fun h => h0 ?_) (fun x y hxy => ?_)
  · rw [← hφ, h, map_zero]
  · have h1 := congrArg φ hxy
    rw [map_mul, map_mul, map_zero, hφ] at h1
    refine (h _ _ h1).imp (fun h => φ.injective ?_) (fun h => φ.injective ?_) <;>
      rw [map_mul, map_zero, hφ, h]

theorem exists_finite_level (K C R : Type) [Field K] [Field C] [Algebra K C] [CommRing R] [Algebra K R]
    (Ω : IntermediateField K C) [Algebra.IsAlgebraic K Ω] (x : Ω ⊗[K] R) :
    ∃ (k : IntermediateField K C) (hk : k ≤ Ω) (e : k ⊗[K] R), FiniteDimensional K k ∧
      Algebra.TensorProduct.map (IntermediateField.inclusion hk) (AlgHom.id K R) e = x := by
  induction x using TensorProduct.induction_on with
  | zero => exact ⟨⊥, bot_le, 0, inferInstance, map_zero _⟩
  | tmul a r =>
    have ha : _root_.IsIntegral K (a : C) :=
      (Algebra.IsAlgebraic.isAlgebraic a).isIntegral.map Ω.val
    refine ⟨IntermediateField.adjoin K {(a : C)}, by simp,
      ⟨a, IntermediateField.mem_adjoin_simple_self K _⟩ ⊗ₜ r,
      IntermediateField.adjoin.finiteDimensional ha, ?_⟩
    rfl
  | add x y hx hy =>
    obtain ⟨k₁, h₁, e₁, f₁, rfl⟩ := hx
    obtain ⟨k₂, h₂, e₂, f₂, rfl⟩ := hy
    have key : ∀ (a b : IntermediateField K C) (hab : a ≤ b) (hb : b ≤ Ω) (e : a ⊗[K] R),
        Algebra.TensorProduct.map (IntermediateField.inclusion hb) (AlgHom.id K R)
          (Algebra.TensorProduct.map (IntermediateField.inclusion hab) (AlgHom.id K R) e) =
        Algebra.TensorProduct.map (IntermediateField.inclusion (hab.trans hb)) (AlgHom.id K R) e := by
      intro a b hab hb e
      induction e using TensorProduct.induction_on with
      | zero => simp
      | tmul a r => rfl
      | add x y hx hy => simp only [map_add, hx, hy]
    refine ⟨k₁ ⊔ k₂, sup_le h₁ h₂,
      (Algebra.TensorProduct.map (IntermediateField.inclusion (le_sup_left : k₁ ≤ k₁ ⊔ k₂))
        (AlgHom.id K R) : k₁ ⊗[K] R →ₐ[K] _) e₁ +
      (Algebra.TensorProduct.map (IntermediateField.inclusion (le_sup_right : k₂ ≤ k₁ ⊔ k₂))
        (AlgHom.id K R) : k₂ ⊗[K] R →ₐ[K] _) e₂,
      inferInstance, ?_⟩
    rw [map_add, key, key]

theorem exists_geomInt_component : ∀ (K : Type) [Field K] [NumberField K] [Algebra K ℂ] (R : Type) [CommRing R] [Algebra K R] [Algebra.Smooth K R] (p : R →ₐ[K] ℂ), ∃ (k : IntermediateField K ℂ) (e : k ⊗[K] R), FiniteDimensional K k ∧ IsIdempotentElem e ∧ Algebra.TensorProduct.lift k.val p (fun _ _ => Commute.all _ _) e = 1 ∧ GeomInt k (Localization.Away e) := by
  intro K _ _ _ R _ _ _ p
  let Ω : IntermediateField K ℂ := algebraicClosure K ℂ
  haveI : IsAlgClosed Ω := (algebraicClosure.isAlgClosure K ℂ).isAlgClosed
  haveI : Algebra.IsAlgebraic K Ω := algebraicClosure.isAlgebraic K ℂ
  haveI hreg : IsRegularRing (Ω ⊗[K] R) := GlobalTheory.isRegularRing_of_smooth Ω _
  let π : Ω ⊗[K] R →ₐ[K] ℂ := Algebra.TensorProduct.lift Ω.val p (fun _ _ => Commute.all _ _)
  haveI : (RingHom.ker π).IsPrime := RingHom.ker_isPrime _
  obtain ⟨e', he', hP, hpr⟩ := exists_idempotent (A := Ω ⊗[K] R)
    (fun q _ => GlobalTheory.isDomain_of_isRegularLocalRing _) (RingHom.ker π)
  obtain ⟨k, hk, e, hfin, rfl⟩ := exists_finite_level K ℂ R Ω e'
  let inc := Algebra.TensorProduct.map (IntermediateField.inclusion hk) (AlgHom.id K R)
  have hinc : Function.Injective inc :=
    Module.Flat.rTensor_preserves_injective_linearMap (M := R)
      (IntermediateField.inclusion hk).toLinearMap (IntermediateField.inclusion_injective hk)
  have he : IsIdempotentElem e := hinc (by rw [map_mul]; exact he')
  have hπ : ∀ x, π (inc x) = Algebra.TensorProduct.lift k.val p (fun _ _ => Commute.all _ _) x := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul a r => rfl
    | add x y hx hy => simp only [map_add, hx, hy]
  refine ⟨k, e, hfin, he, ?_, ?_⟩
  · rw [← hπ]
    exact (IsIdempotentElem.iff_eq_zero_or_one.1 (he'.map π)).resolve_left hP
  · letI : Algebra k Ω := (IntermediateField.inclusion hk).toRingHom.toAlgebra
    haveI : IsScalarTower K k Ω := IsScalarTower.of_algebraMap_eq fun x => rfl
    haveI : Algebra.IsAlgebraic k Ω := Algebra.IsAlgebraic.tower_top (K := K) k
    exact geomInt_away_baseChange K k Ω R e he (fun h => hP (by
      rw [RingHom.mem_ker]
      exact (congrArg π h).trans (map_zero π))) hpr

end GlobalTheory.GeomComp
