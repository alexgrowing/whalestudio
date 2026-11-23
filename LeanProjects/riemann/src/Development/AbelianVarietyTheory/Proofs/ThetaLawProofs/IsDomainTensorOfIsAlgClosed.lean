import Mathlib
import Development.AbelianVarietyTheory.Definitions.KeyFormula.KaRuleK
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SymplecticGenerators.IsPluriharmonicSiegel
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaUnifAV
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.MapsAtLeA
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SymplecticGenerators.SymplecticCharacters.OneEqSpTranslZero
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ThetaFrameValueIndependentNormalFormStatement
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ThetaFrameValueEqUnitSmoothConnectedBaseStatement
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsUnitThetaKeyRuleSmoothBaseStatement
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.StalkOfAppLEEq
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.DualNumberRingHomExt
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsKeyPBRing
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.MemNonzeroLocusConstMul
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.GeometricallyIntegralOfIsIntegralOfIsAlgClosed
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsDomainAndIsIntegrallyClosedAtPrimeOfSmoothOfCo
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsEquivalenceFiniteEtaleBaseChangeResidueField

namespace GlobalTheory.ThetaEquiv

section Algebra
open Polynomial TensorProduct AlgebraicGeometry CategoryTheory Limits

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

theorem exists_baseChange {K F : Type} [Field K] [Field F] (e : K →+* F) (A : Type) [CommRing A] [Algebra K A]
    [Algebra.Smooth K A] (h : ∀ (L : Type) [Field L] [Algebra K L], IsDomain (L ⊗[K] A)) :
    ∃ (B : Type) (_ : CommRing B) (_ : IsDomain B) (_ : Algebra F B) (_ : Algebra.Smooth F B) (ψ : A →+* B),
      ∀ p : A →+* F, p.comp (algebraMap K A) = e → ∃ q : B →ₐ[F] F, q.toRingHom.comp ψ = p := by
  letI := e.toAlgebra
  refine ⟨F ⊗[K] A, inferInstance, h F, inferInstance, inferInstance,
    (Algebra.TensorProduct.includeRight (R := K) (A := F) (B := A)).toRingHom, fun p hp => ?_⟩
  let p' : A →ₐ[K] F := { p with commutes' := fun a => congr($hp a) }
  refine ⟨Algebra.TensorProduct.lift (AlgHom.id F F) p' fun _ _ => .all _ _, ?_⟩
  ext a
  simp [p']

theorem exists_root_prime (K : Type) [Field K] [IsAlgClosed K] [CharZero K] {n : ℕ} (hn : n.Prime)
    (R : Type) [CommRing R] [IsDomain R] [Algebra K R] [Algebra.Smooth K R] (κ : R) (hκ : IsUnit κ)
    (p₀ p : R →ₐ[K] K) (u₀ : K) (hu : u₀ ^ n = p₀ κ) :
    ∃ (B : Type) (_ : CommRing B) (_ : IsDomain B) (_ : Algebra K B) (_ : Algebra.Smooth K B) (φ : R →ₐ[K] B)
      (r : B) (q₀ q : B →ₐ[K] K), r ^ n = φ κ ∧ q₀.comp φ = p₀ ∧ q.comp φ = p ∧ q₀ r = u₀ := by
  by_cases h : ∃ ρ : R, ρ ^ n = κ
  · obtain ⟨ρ, hρ⟩ := h
    have h₁ : p₀ κ ≠ 0 := (hκ.map p₀).ne_zero
    have h₂ : p₀ ρ ≠ 0 := by
      intro h0
      apply h₁
      rw [← hρ, map_pow, h0, zero_pow hn.ne_zero]
    refine ⟨R, inferInstance, inferInstance, inferInstance, inferInstance, AlgHom.id K R,
      algebraMap K R (u₀ / p₀ ρ) * ρ, p₀, p, ?_, rfl, rfl, ?_⟩
    · rw [mul_pow, ← map_pow, div_pow, hu, ← map_pow, hρ, div_self h₁]
      simp
    · simp [h₂]
  · have hic : IsIntegrallyClosed R := GlobalTheory.isIntegrallyClosed_of_smooth K R
    let L := FractionRing R
    let f : R[X] := X ^ n - C κ
    have hf : f.Monic := monic_X_pow_sub_C κ hn.ne_zero
    have hmap : f.map (algebraMap R L) = X ^ n - C (algebraMap R L κ) := by simp [f]
    have hirr : Irreducible (f.map (algebraMap R L)) := by
      rw [hmap]
      refine X_pow_sub_C_irreducible_of_prime hn fun b hb => h ?_
      have hb' : IsIntegral R b := by
        refine ⟨f, hf, ?_⟩
        simp [f, hb]
      obtain ⟨ρ, rfl⟩ := IsIntegrallyClosed.isIntegral_iff.1 hb'
      exact ⟨ρ, IsFractionRing.injective R L (by rw [map_pow, hb])⟩
    have hpr : Prime f := by
      refine ⟨hf.ne_zero, fun hu => hirr.not_isUnit (hu.map (mapRingHom (algebraMap R L))), fun a b hab => ?_⟩
      rw [← map_dvd_map (algebraMap R L) (IsFractionRing.injective R L) hf, Polynomial.map_mul] at hab
      rw [← map_dvd_map (algebraMap R L) (IsFractionRing.injective R L) hf,
        ← map_dvd_map (algebraMap R L) (IsFractionRing.injective R L) hf]
      exact hirr.prime.dvd_or_dvd hab
    have hdom : IsDomain (AdjoinRoot f) := AdjoinRoot.isDomain_of_prime hpr
    have hroot : AdjoinRoot.root f ^ n = algebraMap R (AdjoinRoot f) κ := by
      have := AdjoinRoot.aeval_eq f (f := f)
      rw [AdjoinRoot.mk_self] at this
      simpa [f, sub_eq_zero] using this
    have hru : IsUnit (AdjoinRoot.root f) := by
      rw [← isUnit_pow_iff hn.ne_zero, hroot]
      exact hκ.map _
    have het : Algebra.Etale R (AdjoinRoot f) := by
      refine GlobalTheory.etale_adjoinRoot_of_isUnit_derivative hf ?_
      have : AdjoinRoot.mk f f.derivative =
          algebraMap K (AdjoinRoot f) (n : K) * AdjoinRoot.root f ^ (n - 1) := by
        simp [f, derivative_X_pow]
      rw [this]
      exact ((Ne.isUnit (Nat.cast_ne_zero.2 hn.ne_zero)).map _).mul (hru.pow _)
    have hsm : Algebra.Smooth K (AdjoinRoot f) := Algebra.Smooth.comp K R (AdjoinRoot f)
    have lift : ∀ (s : R →ₐ[K] K) (u : K), u ^ n = s κ → ∃ q : AdjoinRoot f →ₐ[K] K,
        q.comp (IsScalarTower.toAlgHom K R (AdjoinRoot f)) = s ∧ q (AdjoinRoot.root f) = u := by
      intro s u hs
      refine ⟨AdjoinRoot.liftAlgHom f s u (by simp [f, hs]), ?_, ?_⟩
      · ext a
        simp
      · simp
    obtain ⟨u, hu'⟩ := IsAlgClosed.exists_pow_nat_eq (p κ) hn.pos
    obtain ⟨q₀, h₀, h₀'⟩ := lift p₀ u₀ hu
    obtain ⟨q, h₁, -⟩ := lift p u hu'
    exact ⟨AdjoinRoot f, inferInstance, hdom, inferInstance, hsm, IsScalarTower.toAlgHom K R _,
      AdjoinRoot.root f, q₀, q, hroot, h₀, h₁, h₀'⟩

theorem exists_root (K : Type) [Field K] [IsAlgClosed K] [CharZero K] (n : ℕ) : n ≠ 0 →
    ∀ (R : Type) [CommRing R] [IsDomain R] [Algebra K R] [Algebra.Smooth K R] (κ : R) (_ : IsUnit κ)
    (p₀ p : R →ₐ[K] K) (u₀ : K) (_ : u₀ ^ n = p₀ κ),
    ∃ (B : Type) (_ : CommRing B) (_ : IsDomain B) (_ : Algebra K B) (_ : Algebra.Smooth K B) (φ : R →ₐ[K] B)
      (r : B) (q₀ q : B →ₐ[K] K), r ^ n = φ κ ∧ q₀.comp φ = p₀ ∧ q.comp φ = p ∧ q₀ r = u₀ := by
  induction n using induction_on_primes with
  | zero => exact fun h => (h rfl).elim
  | one =>
    intro _ R _ _ _ _ κ _ p₀ p u₀ hu
    exact ⟨R, inferInstance, inferInstance, inferInstance, inferInstance, AlgHom.id K R, κ, p₀, p,
      by simp, rfl, rfl, by simpa using hu.symm⟩
  | prime_mul l a hl ih =>
    intro hn R _ _ _ _ κ hκ p₀ p u₀ hu
    obtain ⟨B, _, _, _, _, φ, r, q₀, q, h₁, h₂, h₃, h₄⟩ :=
      exists_root_prime K hl R κ hκ p₀ p (u₀ ^ a) (by rw [← pow_mul, mul_comm, hu])
    have hr : IsUnit r := by
      rw [← isUnit_pow_iff hl.ne_zero, h₁]
      exact hκ.map _
    obtain ⟨B', _, _, _, _, φ', r', q₀', q', g₁, g₂, g₃, g₄⟩ :=
      ih (right_ne_zero_of_mul hn) B r hr q₀ q u₀ h₄.symm
    refine ⟨B', inferInstance, inferInstance, inferInstance, inferInstance, φ'.comp φ, r', q₀', q', ?_, ?_, ?_, g₄⟩
    · rw [mul_comm, pow_mul, g₁, ← map_pow, h₁, AlgHom.comp_apply]
    · rw [← AlgHom.comp_assoc, g₂, h₂]
    · rw [← AlgHom.comp_assoc, g₃, h₃]

end Algebra

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw
open GlobalTheory.KeyPow GlobalTheory.KeyKa

def IsVal (x : KeyIn ℂ) (t : ℂ) : Prop :=
  ∃ (τ M : Matrix (Fin x.P.g) (Fin x.P.g) ℂ) (a b : Fin x.P.g → ℂ) (c : ℂ),
    charHalf _ a b ∧ c ≠ 0 ∧ NormalAt x τ M a b c ∧ t = M.det ^ 4 / c ^ 8

theorem exists_isVal (hU : ThetaUnifAV) (x : KeyIn ℂ) : ∃ t, IsVal x t := by
  obtain ⟨τ, M, a, b, c, h₁, h₂, -, h₃⟩ := (GlobalTheory.KeyNormalExists.exists_normalAt hU x).1
  exact ⟨_, τ, M, a, b, c, h₁, h₂, h₃, rfl⟩

theorem val_eq_root (hL : Out.Laws) (hU : ThetaUnifAV) (hI : Key.Chi.InversionStatement) {S : Type} [CommRing S]
    (y : KeyIn S) {n : ℕ} (hn : 1 ≤ n) (κ : Sˣ)
    (hκ : ∀ (s : S →+* ℂ) (x : KeyIn ℂ) (t : ℂ), KeyPB x y s → IsVal x t → t ^ n = s κ)
    (B : Type) [CommRing B] [IsDomain B] [Algebra ℂ B] [Algebra.Smooth ℂ B] (ψ : S →+* B) (r : B)
    (hr : r ^ n = ψ κ) (q₀ q : B →ₐ[ℂ] ℂ)
    (h₀ : ∀ x₀ : KeyIn ℂ, KeyPB x₀ y (q₀.toRingHom.comp ψ) → IsVal x₀ (q₀ r))
    (x : KeyIn ℂ) (t : ℂ) (hx : KeyPB x y (q.toRingHom.comp ψ)) (ht : IsVal x t) : t = q r := by
  obtain ⟨yB, hyB⟩ := GlobalTheory.KeyPow.keyIn_baseChange hL.polBaseChange S B y ψ
  have hex : ∀ p : B →ₐ[ℂ] ℂ, ∃ u : ℂ, (∃ z : KeyIn ℂ, KeyPB z yB p.toRingHom ∧ IsVal z u) ∧ (p = q → u = t) := by
    intro p
    by_cases hp : p = q
    · subst hp
      exact ⟨t, ⟨x, GlobalTheory.KeyCancel.keyPB_cancel _ _ _ y yB x ψ _ hyB hx, ht⟩, fun _ => rfl⟩
    · obtain ⟨z, hz⟩ := GlobalTheory.KeyPow.keyIn_baseChange hL.polBaseChange B ℂ yB p.toRingHom
      obtain ⟨u, hu⟩ := exists_isVal hU z
      exact ⟨u, ⟨z, hz, hu⟩, fun h => (hp h).elim⟩
  choose T hT hTq using hex
  have hru : IsUnit r := by
    rw [← isUnit_pow_iff (Nat.one_le_iff_ne_zero.1 hn), hr]
    exact κ.isUnit.map ψ
  obtain ⟨r, rfl⟩ := hru
  rw [← hTq q rfl]
  refine GlobalTheory.T.thetaFrame_value_eq_unit_smooth_connected_base hL hU hI B yB n r T q₀ hn hT (fun p => ?_) ?_ q
  · obtain ⟨z, hz, hu⟩ := hT p
    rw [hκ _ z _ (GlobalTheory.keyPB_trans _ _ _ y yB z ψ _ hyB hz) hu, ← map_pow, hr]
    rfl
  · obtain ⟨z, hz, hu⟩ := hT q₀
    exact GlobalTheory.T.thetaFrame_value_independent_normalForm hU hI z _ _ hu (h₀ z (GlobalTheory.keyPB_trans _ _ _ y yB z ψ _ hyB hz))

theorem val_equivariant : Out.Laws → ThetaUnifAV → Key.Chi.InversionStatement → (∃ N : ℕ → ℕ, (∀ g, 1 ≤ N g) ∧ KeyRule N 1 charHalf) → (∀ x : KeyIn ℂ, ∃ (k : Type) (_ : Field k) (_ : NumberField k) (S : Type) (_ : CommRing S) (_ : Algebra k S) (y : KeyIn S) (s : S →+* ℂ) (s₀ : S →ₐ[k] k) (t₀ : k), Algebra.Smooth k S ∧ (∀ (K : Type) [Field K] [Algebra k K], IsDomain (TensorProduct k K S)) ∧ KeyPB x y s ∧ ∀ (e : k →+* ℂ) (x₀ : KeyIn ℂ), KeyPB x₀ y (e.comp s₀.toRingHom) → (∃ (τ M : Matrix (Fin x₀.P.g) (Fin x₀.P.g) ℂ) (a b : Fin x₀.P.g → ℂ) (c : ℂ), charHalf _ a b ∧ c ≠ 0 ∧ NormalAt x₀ τ M a b c ∧ e t₀ = M.det ^ 4 / c ^ 8)) → ∀ (f : ℂ →+* ℂ) (x x' : KeyIn ℂ) (t t' : ℂ), KeyPB x' x f → (∃ (τ M : Matrix (Fin x.P.g) (Fin x.P.g) ℂ) (a b : Fin x.P.g → ℂ) (c : ℂ), charHalf _ a b ∧ c ≠ 0 ∧ NormalAt x τ M a b c ∧ t = M.det ^ 4 / c ^ 8) → (∃ (τ M : Matrix (Fin x'.P.g) (Fin x'.P.g) ℂ) (a b : Fin x'.P.g → ℂ) (c : ℂ), charHalf _ a b ∧ c ≠ 0 ∧ NormalAt x' τ M a b c ∧ t' = M.det ^ 4 / c ^ 8) → t' = f t := by
  rintro hL hU hI ⟨N, hN, hR⟩ hfam f x x' t t' hx' ht ht'
  obtain ⟨k, _, _, S, _, _, y, s, s₀, t₀, hsm, hdom, hx, h₀⟩ := hfam x
  have : IsDomain S := by
    have := hdom k
    exact (Algebra.TensorProduct.lid k S).symm.toMulEquiv.isDomain _
  obtain ⟨κ, hκ⟩ := GlobalTheory.T.exists_unit_thetaKeyRule_smooth_base hU hL.polBaseChange N hR k S y
  have hn := hN y.P.g
  let e : k →+* ℂ := s.comp (algebraMap k S)
  obtain ⟨R, _, _, _, _, ψ₁, hψ₁⟩ := exists_baseChange e S hdom
  obtain ⟨p, hp⟩ := hψ₁ s rfl
  obtain ⟨p₀, hp₀⟩ := hψ₁ (e.comp s₀.toRingHom) (by ext a; simp)
  have hu : e t₀ ^ N y.P.g = p₀ (ψ₁ κ) := by
    obtain ⟨x₀, hx₀⟩ := GlobalTheory.KeyPow.keyIn_baseChange hL.polBaseChange S ℂ y (e.comp s₀.toRingHom)
    rw [hκ _ x₀ _ hx₀ (h₀ e x₀ hx₀), ← hp₀]
    rfl
  obtain ⟨B, _, _, _, _, φ, r, q₀, q, hr, hq₀, hq, hq₀r⟩ :=
    exists_root ℂ (N y.P.g) (Nat.one_le_iff_ne_zero.1 hn) R (ψ₁ κ) (κ.isUnit.map ψ₁) p₀ p (e t₀) hu
  have key : ∀ (g : ℂ →+* ℂ) (z : KeyIn ℂ) (u : ℂ), KeyPB z y (g.comp s) → IsVal z u → u = g (q r) := by
    intro g z u hz hu
    obtain ⟨B', _, _, _, _, ψ₂, hψ₂⟩ := exists_baseChange g B fun L _ _ => isDomain_tensor_of_isAlgClosed ℂ B L
    obtain ⟨Q, hQ⟩ := hψ₂ (g.comp q.toRingHom) (by ext a; simp)
    obtain ⟨Q₀, hQ₀⟩ := hψ₂ (g.comp q₀.toRingHom) (by ext a; simp)
    have a₁ : Q.toRingHom.comp (ψ₂.comp (φ.toRingHom.comp ψ₁)) = g.comp s := by
      rw [← RingHom.comp_assoc, hQ, ← hp, ← hq]
      rfl
    have a₀ : Q₀.toRingHom.comp (ψ₂.comp (φ.toRingHom.comp ψ₁)) = (g.comp e).comp s₀.toRingHom := by
      rw [← RingHom.comp_assoc, hQ₀, RingHom.comp_assoc s₀.toRingHom, ← hp₀, ← hq₀]
      rfl
    have b₁ : Q (ψ₂ r) = g (q r) := congr($hQ r)
    have b₀ : Q₀ (ψ₂ r) = (g.comp e) t₀ := by
      rw [RingHom.comp_apply, ← hq₀r]
      exact congr($hQ₀ r)
    rw [← b₁]
    refine val_eq_root hL hU hI y hn κ hκ B' (ψ₂.comp (φ.toRingHom.comp ψ₁)) (ψ₂ r) ?_ Q₀ Q
      (fun x₀ hx₀ => ?_) z u (a₁ ▸ hz) hu
    · rw [← map_pow, hr]
      rfl
    · rw [b₀]
      exact h₀ _ x₀ (a₀ ▸ hx₀)
  have c₁ : t = q r := key (RingHom.id ℂ) x t hx ht
  rw [c₁]
  exact key f x' t' (GlobalTheory.keyPB_trans _ _ _ y x x' s f hx hx') ht'

end GlobalTheory.ThetaEquiv
