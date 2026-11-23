import Mathlib
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.StConeRingLaurent
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Targets

open MvPolynomial

namespace ConeRingLaurent

theorem map_C_isPrime {D σ : Type*} [CommRing D] (𝔮 : Ideal D) [𝔮.IsPrime] :
    (𝔮.map (C : D →+* MvPolynomial σ D)).IsPrime := by
  rw [← Ideal.mk_ker (I := 𝔮), ← MvPolynomial.ker_map]
  exact RingHom.ker_isPrime _

variable {K : Type} [Fintype K] {ι : K → Type} (i : (k : K) → ι k)

def tProd : MvPolynomial K (DehomRing i) := ∏ k, X k

abbrev Laurent := Localization.Away (tProd i)

def laurentToConeRing : MvPolynomial K (DehomRing i) →+* ConeRing i :=
  eval₂Hom (ratioMap i) fun k => algebraMap (MvPolynomial (Σ k, ι k) ℂ) (ConeRing i) (X ⟨k, i k⟩)

theorem laurentToConeRing_tProd : laurentToConeRing i (tProd i) = algebraMap _ (ConeRing i) (coneUnit i) := by
  simp [laurentToConeRing, tProd, coneUnit, map_prod]

def toCone : Laurent i →+* ConeRing i :=
  IsLocalization.Away.lift (tProd i) (g := laurentToConeRing i) (by
    rw [laurentToConeRing_tProd]; exact IsLocalization.Away.algebraMap_isUnit (coneUnit i))

def coneToLaurentPolynomial : MvPolynomial (Σ k, ι k) ℂ →+* Laurent i :=
  eval₂Hom ((algebraMap (MvPolynomial K (DehomRing i)) (Laurent i)).comp (C.comp (algebraMap ℂ (DehomRing i))))
    fun p => algebraMap (MvPolynomial K (DehomRing i)) (Laurent i) (C (dehom i (X p)) * X p.1)

theorem coneToLaurent_X_self (k : K) :
    coneToLaurentPolynomial i (X ⟨k, i k⟩) = algebraMap (MvPolynomial K (DehomRing i)) (Laurent i) (X k) := by
  simp [coneToLaurentPolynomial, dehom_X_self]

theorem coneToLaurent_coneUnit :
    coneToLaurentPolynomial i (coneUnit i) = algebraMap (MvPolynomial K (DehomRing i)) (Laurent i) (tProd i) := by
  rw [coneUnit, map_prod]
  exact (Finset.prod_congr rfl fun k _ => coneToLaurent_X_self i k).trans (map_prod _ _ _).symm

def fromCone : ConeRing i →+* Laurent i :=
  IsLocalization.Away.lift (coneUnit i) (g := coneToLaurentPolynomial i) (by
    rw [coneToLaurent_coneUnit]; exact IsLocalization.Away.algebraMap_isUnit (tProd i))

theorem ratioMap_algebraMap (c : ℂ) :
    ratioMap i (algebraMap ℂ (DehomRing i) c) = algebraMap (MvPolynomial (Σ k, ι k) ℂ) (ConeRing i) (C c) := by
  rw [← AlgHom.commutes (dehom i) c, ratioMap_dehom, AlgHom.commutes,
    IsScalarTower.algebraMap_apply ℂ (MvPolynomial (Σ k, ι k) ℂ) (ConeRing i), MvPolynomial.algebraMap_eq]

theorem toCone_comp_fromCone : (toCone i).comp (fromCone i) = RingHom.id _ := by
  apply IsLocalization.ringHom_ext (Submonoid.powers (coneUnit i))
  apply MvPolynomial.ringHom_ext
  · intro c
    simp only [RingHom.comp_apply, RingHom.id_apply, fromCone, IsLocalization.Away.lift_eq, coneToLaurentPolynomial,
      eval₂Hom_C, toCone, laurentToConeRing]
    exact ratioMap_algebraMap i c
  · intro p
    simp only [RingHom.comp_apply, RingHom.id_apply, fromCone, IsLocalization.Away.lift_eq, coneToLaurentPolynomial,
      eval₂Hom_X', toCone, map_mul, laurentToConeRing, eval₂Hom_C]
    rw [ratioMap_dehom, coneRatio, aeval_X, mul_right_comm, (isUnit_coneX i p.1).val_inv_mul, one_mul]

theorem fromCone_algebraMap (f : MvPolynomial (Σ k, ι k) ℂ) :
    fromCone i (algebraMap _ (ConeRing i) f) = coneToLaurentPolynomial i f :=
  IsLocalization.Away.lift_eq _ _ _

theorem fromCone_comp_ratioMap :
    (fromCone i).comp (ratioMap i) =
      (algebraMap (MvPolynomial K (DehomRing i)) (Laurent i)).comp (C : DehomRing i →+* MvPolynomial K (DehomRing i)) := by
  apply Ideal.Quotient.ringHom_ext
  apply MvPolynomial.ringHom_ext
  · intro c
    simp only [RingHom.comp_apply]
    rw [show Ideal.Quotient.mk (dehomIdeal i) (C c) = dehom i (C c) from rfl, ratioMap_dehom, coneRatio, aeval_C,
      IsScalarTower.algebraMap_apply ℂ (MvPolynomial (Σ k, ι k) ℂ) (ConeRing i), MvPolynomial.algebraMap_eq,
      fromCone_algebraMap, coneToLaurentPolynomial, eval₂Hom_C]
    rfl
  · intro p
    simp only [RingHom.comp_apply]
    rw [show Ideal.Quotient.mk (dehomIdeal i) (X p) = dehom i (X p) from rfl, ratioMap_dehom, coneRatio, aeval_X,
      map_mul, fromCone_algebraMap, coneToLaurentPolynomial, eval₂Hom_X', map_mul, ← mul_assoc]
    have hu : fromCone i (((isUnit_coneX i p.1).unit : (ConeRing i)ˣ) : ConeRing i) =
        algebraMap (MvPolynomial K (DehomRing i)) (Laurent i) (X p.1) := by
      rw [IsUnit.unit_spec, fromCone_algebraMap, coneToLaurent_X_self]
    have hinv : fromCone i (((isUnit_coneX i p.1).unit⁻¹ : (ConeRing i)ˣ) : ConeRing i) *
        algebraMap (MvPolynomial K (DehomRing i)) (Laurent i) (X p.1) = 1 := by
      rw [← hu, ← map_mul, Units.inv_mul, map_one]
    rw [mul_comm _ (algebraMap _ _ (C _)), mul_assoc, hinv, mul_one]

theorem fromCone_comp_toCone : (fromCone i).comp (toCone i) = RingHom.id _ := by
  apply IsLocalization.ringHom_ext (Submonoid.powers (tProd i))
  apply MvPolynomial.ringHom_ext
  · intro y
    have h := RingHom.congr_fun (fromCone_comp_ratioMap i) y
    simp only [RingHom.comp_apply, RingHom.id_apply, toCone, IsLocalization.Away.lift_eq, laurentToConeRing,
      eval₂Hom_C] at h ⊢
    exact h
  · intro k
    simp only [RingHom.comp_apply, RingHom.id_apply, toCone, IsLocalization.Away.lift_eq, laurentToConeRing, eval₂Hom_X']
    rw [fromCone_algebraMap, coneToLaurent_X_self]

def laurentEquiv : Laurent i ≃+* ConeRing i :=
  RingEquiv.ofRingHom (toCone i) (fromCone i) (toCone_comp_fromCone i) (fromCone_comp_toCone i)

theorem toCone_comp_algebraMap : (toCone i).comp (algebraMap (DehomRing i) (Laurent i)) = ratioMap i := by
  refine RingHom.ext fun y => ?_
  rw [RingHom.comp_apply, IsScalarTower.algebraMap_apply (DehomRing i) (MvPolynomial K (DehomRing i)) (Laurent i),
    toCone, IsLocalization.Away.lift_eq, MvPolynomial.algebraMap_eq, laurentToConeRing, eval₂Hom_C]

theorem map_laurent_isPrime (𝔮 : Ideal (DehomRing i)) [𝔮.IsPrime] :
    (𝔮.map (algebraMap (DehomRing i) (Laurent i))).IsPrime := by
  rw [IsScalarTower.algebraMap_eq (DehomRing i) (MvPolynomial K (DehomRing i)) (Laurent i), ← Ideal.map_map,
    MvPolynomial.algebraMap_eq]
  apply IsLocalization.isPrime_of_isPrime_disjoint (Submonoid.powers (tProd i)) (Laurent i) _ (map_C_isPrime 𝔮)
  rw [Set.disjoint_left]
  intro x hx hmem
  obtain ⟨n, rfl⟩ := (Submonoid.mem_powers_iff _ _).1 hx
  have hle : 𝔮.map (C : DehomRing i →+* MvPolynomial K (DehomRing i)) ≤
      RingHom.ker (eval₂Hom (Ideal.Quotient.mk 𝔮) fun _ : K => (1 : DehomRing i ⧸ 𝔮)) := by
    rw [Ideal.map_le_iff_le_comap]
    intro y hy
    simp [Ideal.Quotient.eq_zero_iff_mem.2 hy]
  have h0 := hle hmem
  rw [RingHom.mem_ker] at h0
  simp [tProd] at h0
  rw [← map_one (Ideal.Quotient.mk 𝔮), Ideal.Quotient.eq_zero_iff_mem] at h0
  exact Ideal.IsPrime.ne_top ‹_› ((Ideal.eq_top_iff_one _).2 h0)

end ConeRingLaurent

theorem ConeRingLaurent.proof : ConeRingLaurent.Statement := by
  intro K _ ι i
  have hcomp : ratioMap i = (ConeRingLaurent.laurentEquiv i : ConeRingLaurent.Laurent i →+* ConeRing i).comp
      (algebraMap (DehomRing i) (ConeRingLaurent.Laurent i)) :=
    (ConeRingLaurent.toCone_comp_algebraMap i).symm
  constructor
  · rw [hcomp]
    refine RingHom.Flat.comp ?_ (RingHom.Flat.of_bijective (ConeRingLaurent.laurentEquiv i).bijective)
    rw [RingHom.flat_algebraMap_iff]
    infer_instance
  · intro 𝔮 h𝔮
    rw [hcomp, ← Ideal.map_map]
    have := ConeRingLaurent.map_laurent_isPrime i 𝔮
    exact Ideal.map_isPrime_of_equiv (ConeRingLaurent.laurentEquiv i)

end GroundTheory.Heights₂.Heights.Targets
