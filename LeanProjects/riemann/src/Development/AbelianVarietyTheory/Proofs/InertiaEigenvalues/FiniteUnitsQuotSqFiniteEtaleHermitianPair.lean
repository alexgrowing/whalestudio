import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsTestRep
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FiniteNormedAlgebraEqModuleTopology
open GlobalTheory.JR Matrix MeasureTheory Filter Topology

namespace GlobalTheory

theorem finite_units_quot_sq_normed (F : Type) [NontriviallyNormedField F] [CompleteSpace F]
    [ProperSpace F] [CharZero F] (R : Type) [NormedCommRing R] [Nontrivial R] [NormedAlgebra F R]
    [Module.Finite F R] (hR : ∀ x : R, x ≠ 0 → IsUnit x) :
    Finite (Rˣ ⧸ (powMonoidHom 2 : Rˣ →* Rˣ).range) := by
  classical
  obtain ⟨-, hsq⟩ := isOpenUnits_and_eventually_sq_normed F R
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.mp hsq
  obtain ⟨b, hb0, hb1⟩ := NormedField.exists_norm_lt_one F
  have hρ2 : 0 < ‖b‖ ^ 2 := by positivity
  have : ProperSpace R := FiniteDimensional.proper F R
  let C : Set R := {x | ‖b‖ ^ 2 ≤ ‖x‖ ∧ ‖x‖ ≤ 1}
  have hCc : IsCompact C := by
    apply Metric.isCompact_of_isClosed_isBounded
    · exact (isClosed_le continuous_const continuous_norm).inter
        (isClosed_le continuous_norm continuous_const)
    · exact (Metric.isBounded_closedBall (x := (0 : R)) (r := 1)).subset
        (fun x hx => by simpa using hx.2)
  have hCu : ∀ c ∈ C, IsUnit c := fun c hc => hR c (by
    intro h
    have h1 := hc.1
    rw [h, norm_zero] at h1
    linarith)
  obtain ⟨t, htC, hcov⟩ := hCc.elim_nhds_subcover
    (fun c => {x : R | dist (x * Ring.inverse c) 1 < ε}) (by
      intro c hc
      apply IsOpen.mem_nhds
      · exact isOpen_lt (by fun_prop) continuous_const
      · simp [Ring.mul_inverse_cancel _ (hCu c hc), hε])
  let f : R → Rˣ ⧸ (powMonoidHom 2 : Rˣ →* Rˣ).range := fun x =>
    if h : IsUnit x then QuotientGroup.mk h.unit else 1
  have hsurj : (Set.univ : Set (Rˣ ⧸ (powMonoidHom 2 : Rˣ →* Rˣ).range)) ⊆ f '' (t : Set R) := by
    rintro q -
    induction q using QuotientGroup.induction_on with | H u => ?_
    have hu0 : 0 < ‖(u : R)‖ := norm_pos_iff.mpr u.ne_zero
    have hy : 1 < (‖b‖ ^ 2)⁻¹ := (one_lt_inv₀ hρ2).mpr (by nlinarith [norm_nonneg b])
    obtain ⟨n, hn1, hn2⟩ := exists_mem_Ioc_zpow hu0 hy
    have hb0' : b ≠ 0 := norm_pos_iff.mp hb0
    have hβ0 : b ^ (n + 1) ≠ 0 := zpow_ne_zero _ hb0'
    have hnv : ‖(b ^ (n + 1)) ^ 2 • (u : R)‖ = ‖(u : R)‖ / ((‖b‖ ^ 2)⁻¹) ^ (n + 1) := by
      rw [norm_smul, norm_pow, norm_zpow, _root_.inv_zpow, div_inv_eq_mul, mul_comm, ← zpow_natCast, ← zpow_natCast,
        ← _root_.zpow_mul, ← _root_.zpow_mul]
      rw [mul_comm (n + 1)]
    have hv : (b ^ (n + 1)) ^ 2 • (u : R) ∈ C := by
      have hpos : 0 < ((‖b‖ ^ 2)⁻¹) ^ n := zpow_pos (by positivity) n
      refine ⟨?_, ?_⟩
      · rw [hnv, zpow_add₀ (by positivity), zpow_one, le_div_iff₀ (by positivity)]
        calc ‖b‖ ^ 2 * (((‖b‖ ^ 2)⁻¹) ^ n * (‖b‖ ^ 2)⁻¹) = ((‖b‖ ^ 2)⁻¹) ^ n := by field_simp
          _ ≤ ‖(u : R)‖ := hn1.le
      · rw [hnv, div_le_one (by positivity)]
        exact hn2
    obtain ⟨c, hct, hcv⟩ := Set.mem_iUnion₂.mp (hcov hv)
    have hcu := hCu c (htC c hct)
    obtain ⟨s, hs⟩ := hball hcv
    have hsU : IsUnit s := by
      have : IsUnit (s ^ 2) := by
        have hic : Ring.inverse c = ↑(hcu.unit⁻¹) := by rw [← Ring.inverse_unit, IsUnit.unit_spec]
        rw [hs, Algebra.smul_def, hic]
        exact ((isUnit_iff_ne_zero.mpr (pow_ne_zero 2 hβ0)).map (algebraMap F R) |>.mul u.isUnit).mul
          (hcu.unit⁻¹).isUnit
      exact (isUnit_pow_iff two_ne_zero).mp this
    refine ⟨c, hct, ?_⟩
    simp only [f, dif_pos hcu]
    rw [QuotientGroup.eq, MonoidHom.mem_range]
    let bu : Rˣ := Units.map (algebraMap F R).toMonoidHom (Units.mk0 _ hβ0)
    have hs' : hsU.unit ^ 2 = bu ^ 2 * u * hcu.unit⁻¹ := by
      ext
      simp only [Units.val_pow_eq_pow_val, Units.val_mul, IsUnit.unit_spec, bu, Units.coe_map,
        Units.val_mk0]
      rw [hs, ← Ring.inverse_unit, IsUnit.unit_spec, Algebra.smul_def, map_pow]
      rfl
    refine ⟨hsU.unit * bu⁻¹, ?_⟩
    rw [powMonoidHom_apply, mul_pow, inv_pow, hs']
    simp only [mul_comm, mul_left_comm, mul_assoc, mul_inv_cancel_left, inv_mul_cancel_left, mul_inv_cancel, mul_one]
  have hfin : (Set.univ : Set (Rˣ ⧸ (powMonoidHom 2 : Rˣ →* Rˣ).range)).Finite :=
    (t.finite_toSet.image f).subset hsurj
  exact Set.finite_univ_iff.mp hfin

end GlobalTheory

namespace GlobalTheory

theorem finite_units_quot_sq_field (F : Type) [NontriviallyNormedField F] [CompleteSpace F]
    [ProperSpace F] [CharZero F] (L : Type) [Field L] [Algebra F L] [Module.Finite F L] :
    Finite (Lˣ ⧸ (powMonoidHom 2 : Lˣ →* Lˣ).range) := by
  classical
  let b := Module.finBasis F L
  let : NormedRing (Matrix (Fin (Module.finrank F L)) (Fin (Module.finrank F L)) F) :=
    Matrix.linftyOpNormedRing
  let : NormedAlgebra F (Matrix (Fin (Module.finrank F L)) (Fin (Module.finrank F L)) F) :=
    Matrix.linftyOpNormedAlgebra
  let N : NormedCommRing L := NormedCommRing.induced L _ (Algebra.leftMulMatrix b)
    (Algebra.leftMulMatrix_injective b)
  let A : @NormedAlgebra F L _ N.toNormedRing.toSeminormedRing :=
    NormedAlgebra.induced F L _ (Algebra.leftMulMatrix b)
  exact @finite_units_quot_sq_normed F _ _ _ _ L N inferInstance A ‹_› (fun x hx => hx.isUnit)

theorem finite_units_quot_sq_reduced (F : Type) [NontriviallyNormedField F] [CompleteSpace F]
    [ProperSpace F] [CharZero F] (K : Type) [CommRing K] [Algebra F K] [Module.Finite F K]
    [IsReduced K] : Finite (Kˣ ⧸ (powMonoidHom 2 : Kˣ →* Kˣ).range) := by
  classical
  have : IsArtinianRing K := IsArtinianRing.of_finite F K
  letI (I : MaximalSpectrum K) : Field (K ⧸ I.asIdeal) :=
    @Ideal.Quotient.field _ _ I.asIdeal I.isMaximal
  have hfin (I : MaximalSpectrum K) :
      Finite ((K ⧸ I.asIdeal)ˣ ⧸ (powMonoidHom 2 : (K ⧸ I.asIdeal)ˣ →* (K ⧸ I.asIdeal)ˣ).range) :=
    finite_units_quot_sq_field F (K ⧸ I.asIdeal)
  let φ : Kˣ →* ∀ I : MaximalSpectrum K,
      (K ⧸ I.asIdeal)ˣ ⧸ (powMonoidHom 2 : (K ⧸ I.asIdeal)ˣ →* (K ⧸ I.asIdeal)ˣ).range :=
    Pi.monoidHom fun I => (QuotientGroup.mk' _).comp
      (Units.map (Ideal.Quotient.mk I.asIdeal).toMonoidHom)
  have hker : φ.ker = (powMonoidHom 2 : Kˣ →* Kˣ).range := by
    ext u
    simp only [MonoidHom.mem_ker, MonoidHom.mem_range, powMonoidHom_apply]
    constructor
    · intro hu
      have hI (I : MaximalSpectrum K) : ∃ s : (K ⧸ I.asIdeal)ˣ,
          s ^ 2 = Units.map (Ideal.Quotient.mk I.asIdeal).toMonoidHom u := by
        have := congrFun hu I
        change ((Units.map (Ideal.Quotient.mk I.asIdeal).toMonoidHom u : (K ⧸ I.asIdeal)ˣ) :
          (K ⧸ I.asIdeal)ˣ ⧸ (powMonoidHom 2 : (K ⧸ I.asIdeal)ˣ →* (K ⧸ I.asIdeal)ˣ).range) = 1 at this
        rw [QuotientGroup.eq_one_iff] at this
        obtain ⟨s, hs⟩ := this
        exact ⟨s, hs⟩
      choose s hs using hI
      let e := IsArtinianRing.equivPi K
      let x : K := e.symm fun I => (s I : K ⧸ I.asIdeal)
      let y : K := e.symm fun I => ((s I)⁻¹ : (K ⧸ I.asIdeal)ˣ)
      have hxy : x * y = 1 := e.injective (by
        rw [map_mul, map_one]
        funext I
        simp [x, y])
      refine ⟨⟨x, y, hxy, by rw [mul_comm]; exact hxy⟩, ?_⟩
      ext
      apply e.injective
      funext I
      have := congrArg Units.val (hs I)
      simp only [Units.val_pow_eq_pow_val, Units.coe_map, MonoidHom.coe_coe] at this
      simp [x, this] <;> rfl
    · rintro ⟨w, rfl⟩
      funext I
      change ((Units.map (Ideal.Quotient.mk I.asIdeal).toMonoidHom (w ^ 2) : (K ⧸ I.asIdeal)ˣ) :
        (K ⧸ I.asIdeal)ˣ ⧸ (powMonoidHom 2 : (K ⧸ I.asIdeal)ˣ →* (K ⧸ I.asIdeal)ˣ).range) = 1
      rw [QuotientGroup.eq_one_iff, map_pow]
      exact ⟨_, rfl⟩
  have := Finite.of_injective _ (QuotientGroup.kerLift_injective φ)
  rw [hker] at this
  exact this

theorem Et.finite_units_quot_sq : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E]
    [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E),
    Finite (A.Kˣ ⧸ (powMonoidHom 2 : A.Kˣ →* A.Kˣ).range) := by
  intro F E _ _ _ _ hU A
  have : CharZero F := hU.charZero
  have : LocallyCompactSpace F := hU.lcF
  have : ProperSpace F := ProperSpace.of_locallyCompactSpace F
  exact finite_units_quot_sq_reduced F A.K

end GlobalTheory
