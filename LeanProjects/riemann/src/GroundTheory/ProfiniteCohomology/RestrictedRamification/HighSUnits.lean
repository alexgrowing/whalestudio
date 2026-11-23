import Mathlib
import GroundTheory.ProfiniteCohomology.RestrictedRamification.HighInflUnits
set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

open CategoryTheory Limits NumberField IsDedekindDomain GroundTheory.Global

local notation "ℚ̄" => AlgebraicClosure ℚ

noncomputable section

theorem exists_coprime_nsmul_of_primary_eq_zero {M : Type*} [AddCommGroup M] {ℓ : ℕ} (hℓ : ℓ.Prime)
    (hM : ∀ y : M, ∀ k : ℕ, ℓ ^ k • y = 0 → y = 0) {x : M} (hx : IsOfFinAddOrder x) :
    ∃ m : ℕ, m.Coprime ℓ ∧ m • x = 0 := by
  have hn : addOrderOf x ≠ 0 := hx.addOrderOf_pos.ne'
  have hnm : ℓ ^ (addOrderOf x).factorization ℓ * (addOrderOf x / ℓ ^ (addOrderOf x).factorization ℓ) =
      addOrderOf x := Nat.ordProj_mul_ordCompl_eq_self _ ℓ
  refine ⟨addOrderOf x / ℓ ^ (addOrderOf x).factorization ℓ, (Nat.coprime_ordCompl hℓ hn).symm,
    hM _ ((addOrderOf x).factorization ℓ) ?_⟩
  rw [smul_smul, hnm]
  exact addOrderOf_nsmul_eq_zero x

variable (K : FiniteSubfield) (S : Set (HeightOneSpectrum (𝓞 K.1))) (ιs : LocalEmbeddings K) {ℓ : ℕ}
  (hℓ : ℓ.Prime) (hS : ∀ v : HeightOneSpectrum (𝓞 K.1), ((ℓ : ℕ) : 𝓞 K.1) ∈ v.asIdeal → v ∈ S)
  (hD : ∀ p : ℕ, 2 ≤ p → ∀ x : cohomology (gsDiv K S ιs QZ) p, ∀ k : ℕ, ℓ ^ k • x = 0 → x = 0)

include hℓ hD in

theorem eq_zero_of_pow_nsmul_cohomology_gsDiv_int {q : ℕ} (hq : 3 ≤ q) (x : cohomology (gsDiv K S ιs ℤ) q)
    (k : ℕ) (hx : ℓ ^ k • x = 0) : x = 0 := by
  have hX := divFunSequence_shortExact (gsDecomp K S ιs)
  obtain ⟨p, rfl⟩ : ∃ p, q = p + 1 := ⟨q - 1, by omega⟩
  have hzero : IsZero (cohomology (divFunSequence (gsDecomp K S ιs)).X₂ (p + 1)) :=
    isZero_cohomology_of_bijective_nsmul_ulift _ (fun n hn => bijective_nsmul_divFun_rat _ hn) (by omega)
  have hs := ModuleCat.subsingleton_of_isZero hzero
  let x' : cohomology (divFunSequence (gsDecomp K S ιs)).X₁ (p + 1) := x
  obtain ⟨y, hy⟩ := exists_δ_eq_of_cohomologyMap_f_eq_zero hX p (p + 1) rfl x' (Subsingleton.elim _ _)
  have hx' : ℓ ^ k • x' = 0 := hx
  have hk : ℓ ^ k • (δ hX p (p + 1) rfl).hom.toAddMonoidHom y = 0 :=
    (congrArg (fun t => ℓ ^ k • t) hy).trans hx'
  obtain ⟨y', ⟨j, hj⟩, hy'⟩ := exists_primary_map_eq (δ hX p (p + 1) rfl).hom.toAddMonoidHom hℓ
    (isTorsion_cohomology _ (by omega) y) hk
  have h0 : y' = 0 := hD p (by omega) y' j hj
  have e : x' = (δ hX p (p + 1) rfl).hom y' := hy.symm.trans hy'.symm
  rw [h0, map_zero] at e
  exact e

include hℓ hS hD in

theorem eq_zero_of_pow_nsmul_cohomology_galUnitsModSUnits {q : ℕ} (hq : 3 ≤ q)
    (x : cohomology (galUnitsModSUnits K.1 ℚ̄ S) q) (k : ℕ) (hx : ℓ ^ k • x = 0) : x = 0 := by
  have hP := picSequence_shortExact K S ιs
  obtain ⟨p, rfl⟩ : ∃ p, q = p + 1 := ⟨q - 1, by omega⟩
  let x' : cohomology (picSequence K S ιs).X₁ (p + 1) := x
  have hx' : ℓ ^ k • x' = 0 := hx
  have hxD : (cohomologyMap (picSequence K S ιs).f (p + 1)).hom x' = 0 :=
    eq_zero_of_pow_nsmul_cohomology_gsDiv_int K S ιs hℓ hD hq _ k
      ((map_nsmul (cohomologyMap (picSequence K S ιs).f (p + 1)).hom (ℓ ^ k) x').symm.trans
        ((congrArg _ hx').trans (map_zero _)))
  exact eq_zero_of_mem_range_δ_of_coprime hP p (p + 1) rfl
    (exists_δ_eq_of_cohomologyMap_f_eq_zero hP p (p + 1) rfl x' hxD) ℓ
    (fun r => exists_coprime_smul_cohomology_eq_zero (picInfRep K S ιs) ℓ
      (exists_coprime_smul_picInfRep K S ιs ℓ hℓ hS) p r) k hx

include hℓ hS hD in

theorem isIsoModCoprime_sUnitsToUnits {r : ℕ} (hr : 4 ≤ r) :
    IsIsoModCoprime ℓ (cohomologyMap (sUnitsToUnits S (maxUnramifiedOutside K.1 ℚ̄ S)) r).hom.toAddMonoidHom := by
  have hQ := sUnitsQuotSequence_shortExact K.1 ℚ̄ S
  have hP : ∀ q, 3 ≤ q → ∀ w : cohomology (galUnitsModSUnits K.1 ℚ̄ S) q,
      ∃ m : ℕ, m.Coprime ℓ ∧ m • w = 0 := fun q hq w =>
    exists_coprime_nsmul_of_primary_eq_zero hℓ
      (fun w' k hk => eq_zero_of_pow_nsmul_cohomology_galUnitsModSUnits K S ιs hℓ hS hD hq w' k hk)
      (isTorsion_cohomology _ (by omega) w)
  obtain ⟨p, rfl⟩ : ∃ p, r = p + 1 := ⟨r - 1, by omega⟩
  refine ⟨fun z hz => ?_, fun y => ?_⟩
  · let z' : cohomology (sUnitsQuotSequence K.1 ℚ̄ S).X₁ (p + 1) := z
    obtain ⟨w, hw⟩ := exists_δ_eq_of_cohomologyMap_f_eq_zero hQ p (p + 1) rfl z' hz
    obtain ⟨m, hm, hmw⟩ := hP p (by omega) w
    refine ⟨m, hm, ?_⟩
    have e : m • z' = 0 := by
      rw [← hw, ← map_nsmul]
      exact (congrArg _ hmw).trans (map_zero _)
    exact e
  · let y' : cohomology (sUnitsQuotSequence K.1 ℚ̄ S).X₂ (p + 1) := y
    obtain ⟨m, hm, hmy⟩ := hP (p + 1) (by omega) ((cohomologyMap (sUnitsQuotSequence K.1 ℚ̄ S).g (p + 1)).hom y')
    have hg : (cohomologyMap (sUnitsQuotSequence K.1 ℚ̄ S).g (p + 1)).hom (m • y') = 0 :=
      (map_nsmul _ m y').trans hmy
    obtain ⟨z, hz⟩ := exists_cohomologyMap_f_eq_of_cohomologyMap_g_eq_zero hQ (p + 1) (m • y') hg
    exact ⟨m, hm, z, hz⟩

def sUnitsInfl (r : ℕ) : cohomology (galSUnitsMax K.1 ℚ̄ S) r →+ cohomology (unitsLimitRep K) r :=
  (gsUnitsInfl K S r).comp (cohomologyMap (sUnitsToUnits S (maxUnramifiedOutside K.1 ℚ̄ S)) r).hom.toAddMonoidHom

theorem sUnitsInfl_apply (r : ℕ) (y : cohomology (galSUnitsMax K.1 ℚ̄ S) r) :
    sUnitsInfl K S r y = gsUnitsInfl K S r ((cohomologyMap (sUnitsToUnits S (maxUnramifiedOutside K.1 ℚ̄ S)) r).hom y) :=
  rfl

include hℓ hS hD in

theorem isIsoModCoprime_sUnitsInfl_of_divisor {r : ℕ} (hr : 4 ≤ r) : IsIsoModCoprime ℓ (sUnitsInfl K S r) :=
  (isIsoModCoprime_gsUnitsInfl K S hℓ hS (by omega)).comp (isIsoModCoprime_sUnitsToUnits K S ιs hℓ hS hD hr)

end

end GroundTheory.ProfCoh
