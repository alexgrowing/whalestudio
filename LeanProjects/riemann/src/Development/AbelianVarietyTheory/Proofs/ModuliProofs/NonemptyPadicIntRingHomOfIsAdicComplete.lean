import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaUnifAV
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsDiscreteValuationRingIntegralClosurePadicInt
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.BoundedOnFramesIffIntegralOnFrames

open IsLocalRing

namespace GlobalTheory

open IsLocalRing in

theorem _root_.GlobalTheory.nonempty_padicInt_ringHom_of_isAdicComplete {V : Type*} [CommRing V] (I : Ideal V)
    [IsAdicComplete I V] (p : ℕ) [Fact p.Prime] (hp : (p : V) ∈ I) : Nonempty (ℤ_[p] →+* V) := by
  have hzero : ∀ n : ℕ, ∀ a ∈ Ideal.span {((p ^ n : ℕ) : ℤ)}, (Int.castRingHom (V ⧸ I ^ n)) a = 0 := by
    intro n a ha
    obtain ⟨k, rfl⟩ := Ideal.mem_span_singleton'.mp ha
    have h : ((p ^ n : ℕ) : V ⧸ I ^ n) = 0 := by
      rw [show ((p ^ n : ℕ) : V ⧸ I ^ n) = Ideal.Quotient.mk _ ((p : V) ^ n) by simp,
        Ideal.Quotient.eq_zero_iff_mem]
      exact Ideal.pow_mem_pow hp n
    rw [map_mul, map_natCast, h, mul_zero]
  let g : (n : ℕ) → ZMod (p ^ n) →+* V ⧸ I ^ n := fun n =>
    (Ideal.Quotient.lift _ (Int.castRingHom _) (hzero n)).comp
      (Int.quotientSpanNatEquivZMod (p ^ n)).symm.toRingHom
  refine ⟨IsAdicComplete.liftRingHom I (fun n => (g n).comp (PadicInt.toZModPow n)) ?_⟩
  intro m n hle
  have hg : (Ideal.Quotient.factorPow I hle).comp (g n) =
      (g m).comp (ZMod.castHom (pow_dvd_pow p hle) _) := Subsingleton.elim _ _
  ext x
  have hx := RingHom.congr_fun hg (PadicInt.toZModPow n x)
  rw [← PadicInt.zmod_cast_comp_toZModPow m n hle]
  exact hx

open IsLocalRing in

theorem _root_.GlobalTheory.exists_padicInt_algebra_finite (V : Type*) [CommRing V] [IsDomain V]
    [IsDiscreteValuationRing V] [IsAdicComplete (maximalIdeal V) V] [CharZero V]
    [Finite (ResidueField V)] :
    ∃ (p : ℕ) (_ : Fact p.Prime) (_ : Algebra ℤ_[p] V), Module.Finite ℤ_[p] V := by
  obtain ⟨q, hq⟩ := CharP.exists (ResidueField V)
  have hprime : q.Prime := CharP.char_is_prime (ResidueField V) q
  haveI hfact : Fact q.Prime := ⟨hprime⟩
  have hmem : (q : V) ∈ maximalIdeal V := by
    rw [← residue_eq_zero_iff, map_natCast]
    exact CharP.cast_eq_zero _ q
  obtain ⟨φ⟩ := _root_.GlobalTheory.nonempty_padicInt_ringHom_of_isAdicComplete (maximalIdeal V) q hmem
  letI : Algebra ℤ_[q] V := φ.toAlgebra
  refine ⟨q, hfact, this, ?_⟩
  haveI : Finite (V ⧸ maximalIdeal V) := ‹Finite (ResidueField V)›
  have hne : (q : V) ≠ 0 := Nat.cast_ne_zero.mpr hprime.ne_zero
  have himage : algebraMap ℤ_[q] V (q : ℤ_[q]) = (q : V) := map_natCast _ q
  refine _root_.GlobalTheory.finite_of_forall_prime_mem hne ?_ ?_ ?_
  · intro P hP hPne
    have hmax : P.IsMaximal := hP.isMaximal hPne
    rw [IsLocalRing.eq_maximalIdeal hmax]
    exact hmem
  · intro hbot
    apply hne
    rw [← himage, ← Ideal.mem_bot, ← hbot]
    apply Ideal.mem_map_of_mem
    rw [PadicInt.maximalIdeal_eq_span_p]
    exact Ideal.mem_span_singleton_self _
  · apply ne_top_of_le_ne_top (IsLocalRing.maximalIdeal.isMaximal V).ne_top
    rw [Ideal.map_le_iff_le_comap, PadicInt.maximalIdeal_eq_span_p, Ideal.span_le,
      Set.singleton_subset_iff]
    change algebraMap ℤ_[q] V (q : ℤ_[q]) ∈ maximalIdeal V
    rw [himage]
    exact hmem

open IsLocalRing in

theorem _root_.GlobalTheory.exists_ringEquiv_integralClosure_padicInt (V K : Type*) [CommRing V] [IsDomain V]
    [IsDiscreteValuationRing V] [IsAdicComplete (maximalIdeal V) V] [Field K] [CharZero K]
    [Algebra V K] [IsFractionRing V K] [Finite (ResidueField V)] :
    ∃ (p : ℕ) (_ : Fact p.Prime) (K₀ : IntermediateField ℚ_[p] (PadicAlgCl p)) (e : K ≃+* K₀)
      (e₀ : V ≃+* integralClosure ℤ_[p] K₀), FiniteDimensional ℚ_[p] K₀ ∧
      ∀ x, e (algebraMap V K x) = ((e₀ x : integralClosure ℤ_[p] K₀) : K₀) := by
  haveI : CharZero V := (algebraMap V K).charZero
  obtain ⟨p, hfact, _, hfin⟩ := _root_.GlobalTheory.exists_padicInt_algebra_finite V
  have hp : (p : V) ≠ 0 := Nat.cast_ne_zero.mpr hfact.out.ne_zero
  obtain ⟨L, hL, g, hg⟩ := _root_.GlobalTheory.exists_injective_algHom_integralClosure V hp
  let ψ : V →+* PadicAlgCl p :=
    L.val.toRingHom.comp ((integralClosure ℤ_[p] L).val.toRingHom.comp g.toRingHom)
  have hψ : ∀ v, ψ v = ((g v : L) : PadicAlgCl p) := fun v => rfl
  have hψinj : Function.Injective ψ := fun a b h => hg (Subtype.ext (Subtype.ext h))
  let f : K →+* PadicAlgCl p := IsFractionRing.lift hψinj
  have hf : ∀ v, f (algebraMap V K v) = ψ v := IsFractionRing.lift_algebraMap hψinj
  have hψZ : ∀ x : ℤ_[p], ψ (algebraMap ℤ_[p] V x) = algebraMap ℤ_[p] (PadicAlgCl p) x := by
    intro x
    rw [hψ, g.commutes]
    rfl
  let K₀ : IntermediateField ℚ_[p] (PadicAlgCl p) :=
    { f.fieldRange with
      algebraMap_mem' := by
        intro r
        obtain ⟨a, b, -, rfl⟩ := IsFractionRing.div_surjective (A := ℤ_[p]) r
        rw [map_div₀, ← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply,
          ← hψZ, ← hψZ, ← hf, ← hf, ← map_div₀]
        exact ⟨_, rfl⟩ }
  have hK₀ : ∀ y, y ∈ K₀ ↔ ∃ x, f x = y := fun y => Iff.rfl
  have hle : K₀ ≤ L := by
    intro y hy
    obtain ⟨x, rfl⟩ := (hK₀ y).mp hy
    obtain ⟨a, b, -, rfl⟩ := IsFractionRing.div_surjective (A := V) x
    rw [map_div₀, hf, hf, hψ, hψ]
    exact div_mem (g a : L).2 (g b : L).2
  haveI : FiniteDimensional ℚ_[p] K₀ := FiniteDimensional.of_injective
    (IntermediateField.inclusion hle).toLinearMap (IntermediateField.inclusion_injective hle)
  let e : K ≃+* K₀ := RingEquiv.ofBijective (f.codRestrict K₀ fun x => (hK₀ _).mpr ⟨x, rfl⟩)
    ⟨fun a b h => f.injective (congrArg Subtype.val h), fun y => by
      obtain ⟨x, hx⟩ := (hK₀ y).mp y.2
      exact ⟨x, Subtype.ext hx⟩⟩
  have he : ∀ x, ((e x : K₀) : PadicAlgCl p) = f x := fun x => rfl
  have hint : ∀ v, e (algebraMap V K v) ∈ integralClosure ℤ_[p] K₀ := by
    intro v
    rw [_root_.GlobalTheory.mem_integralClosure_padicInt_iff, he, hf, hψ]
    exact (_root_.GlobalTheory.mem_integralClosure_padicInt_iff L _).mp (g v).2
  let φ : V →+* integralClosure ℤ_[p] K₀ :=
    (e.toRingHom.comp (algebraMap V K)).codRestrict (integralClosure ℤ_[p] K₀) hint
  have hφ : ∀ v, ((φ v : integralClosure ℤ_[p] K₀) : K₀) = e (algebraMap V K v) := fun v => rfl
  haveI : IsLocalHom (g : V →+* integralClosure ℤ_[p] L) :=
    _root_.GlobalTheory.isLocalHom_of_injective_integralClosure g hg
  have hbij : Function.Bijective φ := by
    refine ⟨fun a b h => IsFractionRing.injective V K (e.injective ?_), fun y => ?_⟩
    · rw [← hφ, ← hφ, h]
    obtain ⟨x, hx⟩ := e.surjective (y : K₀)
    have hy : ‖f x‖ ≤ 1 := by
      rw [← he, hx]
      exact (_root_.GlobalTheory.mem_integralClosure_padicInt_iff K₀ _).mp y.2
    have hpre : ∀ v, algebraMap V K v = x → ∃ w, φ w = y := fun v hv =>
      ⟨v, Subtype.ext (by rw [hφ, hv, hx])⟩
    by_cases hx0 : x = 0
    · exact hpre 0 (by rw [map_zero, hx0])
    rcases ValuationRing.isInteger_or_isInteger V x with ⟨v, hv⟩ | ⟨v, hv⟩
    · exact hpre v hv
    by_cases hu : IsUnit v
    · refine hpre (↑hu.unit⁻¹) ?_
      rw [map_units_inv, IsUnit.unit_spec, hv, inv_inv]
    · exfalso
      have hgv : g v ∈ maximalIdeal (integralClosure ℤ_[p] L) := by
        rw [mem_maximalIdeal, mem_nonunits_iff]
        exact fun h => hu (isUnit_of_map_unit (g : V →+* integralClosure ℤ_[p] L) v h)
      have hlt : ‖ψ v‖ < 1 := by
        rw [hψ]
        exact (_root_.GlobalTheory.mem_maximalIdeal_integralClosure_iff L _).mp hgv
      have hone : f x * ψ v = 1 := by
        rw [← hf, hv, ← map_mul, mul_inv_cancel₀ hx0, map_one]
      have h1 : ‖f x * ψ v‖ < 1 := by
        rw [norm_mul]
        calc ‖f x‖ * ‖ψ v‖ ≤ 1 * ‖ψ v‖ := mul_le_mul_of_nonneg_right hy (norm_nonneg _)
          _ < 1 := by rw [one_mul]; exact hlt
      rw [hone, norm_one] at h1
      exact lt_irrefl _ h1
  exact ⟨p, hfact, K₀, e, RingEquiv.ofBijective φ hbij, inferInstance, fun x => rfl⟩

open IsLocalRing in
private theorem isAdicComplete_integralClosure_padicInt (p : ℕ) [Fact p.Prime]
    (K : IntermediateField ℚ_[p] (PadicAlgCl p)) [FiniteDimensional ℚ_[p] K]
    [IsLocalRing (integralClosure ℤ_[p] K)] :
    IsAdicComplete (maximalIdeal (integralClosure ℤ_[p] K)) (integralClosure ℤ_[p] K) := by
  haveI := _root_.GlobalTheory.isDiscreteValuationRing_integralClosure_padicInt p K
  set O := integralClosure ℤ_[p] K
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible O
  let nm : O → ℝ := fun x => ‖((x : K) : PadicAlgCl p)‖
  have hnm_mul : ∀ x y : O, nm (x * y) = nm x * nm y := fun x y => by simp [nm]
  have hnm_pow : ∀ (x : O) (n : ℕ), nm (x ^ n) = nm x ^ n := fun x n => by simp [nm]
  have hnm_le : ∀ x : O, nm x ≤ 1 := fun x => (_root_.GlobalTheory.mem_integralClosure_padicInt_iff K _).mp x.2
  have hunit : ∀ u : Oˣ, nm u = 1 := by
    intro u
    have h1 := hnm_mul u ↑u⁻¹
    rw [Units.mul_inv] at h1
    have h2 : nm 1 = 1 := by simp [nm]
    have hu := hnm_le u
    have hv := hnm_le ↑u⁻¹
    nlinarith [norm_nonneg ((((u : O) : K)) : PadicAlgCl p),
      norm_nonneg (((((u⁻¹ : Oˣ) : O) : K)) : PadicAlgCl p)]
  have hπ0 : π ≠ 0 := hπ.ne_zero
  have hpos : 0 < nm π := by
    simp only [nm, norm_pos_iff, ne_eq, ZeroMemClass.coe_eq_zero]
    exact hπ0
  have hr : nm π < 1 := (_root_.GlobalTheory.mem_maximalIdeal_integralClosure_iff K π).mp
    ((mem_maximalIdeal _).mpr hπ.not_isUnit)
  have hmax : maximalIdeal O = Ideal.span {π} := hπ.maximalIdeal_eq
  have hmem : ∀ (n : ℕ) (x : O), x ∈ maximalIdeal O ^ n ↔ nm x ≤ nm π ^ n := by
    intro n x
    rw [hmax, Ideal.span_singleton_pow, Ideal.mem_span_singleton]
    constructor
    · rintro ⟨c, rfl⟩
      rw [hnm_mul, hnm_pow]
      exact mul_le_of_le_one_right (pow_nonneg hpos.le n) (hnm_le c)
    · intro hx
      by_cases hx0 : x = 0
      · rw [hx0]
        exact dvd_zero _
      obtain ⟨k, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hx0 hπ
      rw [hnm_mul, hunit, one_mul, hnm_pow] at hx
      have hk : n ≤ k := (pow_le_pow_iff_right_of_lt_one₀ hpos hr).mp hx
      exact Dvd.dvd.mul_left (pow_dvd_pow π hk) _
  have hsmod : ∀ (n : ℕ) (x y : O),
      x ≡ y [SMOD (maximalIdeal O ^ n • ⊤ : Submodule O O)] ↔ nm (x - y) ≤ nm π ^ n := by
    intro n x y
    rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top, hmem]
  have hdist : ∀ x y : O, dist ((x : K) : PadicAlgCl p) ((y : K) : PadicAlgCl p) = nm (x - y) := by
    intro x y
    simp [nm, dist_eq_norm]
  refine { haus' := ?_, prec' := ?_ }
  · intro x hx
    have hle : ∀ n : ℕ, nm x ≤ nm π ^ n := fun n => by simpa using (hsmod n x 0).mp (hx n)
    have hlim : Filter.Tendsto (fun n : ℕ => nm π ^ n) Filter.atTop (nhds 0) :=
      tendsto_pow_atTop_nhds_zero_of_lt_one hpos.le hr
    have h0 : nm x ≤ 0 := ge_of_tendsto' hlim hle
    have hx0 : ((x : K) : PadicAlgCl p) = 0 := norm_le_zero_iff.mp h0
    exact Subtype.ext (Subtype.ext hx0)
  · intro f hf
    let g : ℕ → PadicAlgCl p := fun n => ((f n : K) : PadicAlgCl p)
    have hcauchy : CauchySeq g := by
      refine cauchySeq_of_le_tendsto_0 (fun N => nm π ^ N) (fun n m N hn hm => ?_)
        (tendsto_pow_atTop_nhds_zero_of_lt_one hpos.le hr)
      rw [hdist, ← hmem]
      have h1 := (hmem N _).mpr ((hsmod N _ _).mp (hf hn))
      have h2 := (hmem N _).mpr ((hsmod N _ _).mp (hf hm))
      have h3 := sub_mem h2 h1
      rwa [sub_sub_sub_cancel_left] at h3
    haveI : FiniteDimensional ℚ_[p] (Subalgebra.toSubmodule K.toSubalgebra) :=
      ‹FiniteDimensional ℚ_[p] K›
    have hKc : IsComplete (K : Set (PadicAlgCl p)) :=
      Submodule.complete_of_finiteDimensional (Subalgebra.toSubmodule K.toSubalgebra)
    obtain ⟨a, haK, hlim⟩ := cauchySeq_tendsto_of_isComplete hKc (fun n => (f n : K).2) hcauchy
    have ha1 : ‖a‖ ≤ 1 := le_of_tendsto' hlim.norm fun n => hnm_le (f n)
    let L : O := ⟨⟨a, haK⟩, (_root_.GlobalTheory.mem_integralClosure_padicInt_iff K _).mpr ha1⟩
    refine ⟨L, fun n => (hsmod n _ _).mpr ?_⟩
    have hlim' : Filter.Tendsto (fun k => ‖g n - g k‖) Filter.atTop (nhds ‖g n - a‖) :=
      (tendsto_const_nhds.sub hlim).norm
    have hbound : ∀ᶠ k in Filter.atTop, ‖g n - g k‖ ≤ nm π ^ n := by
      refine Filter.eventually_atTop.mpr ⟨n, fun k hk => ?_⟩
      rw [← dist_eq_norm, hdist]
      exact (hsmod n _ _).mp (hf hk)
    have hfin := le_of_tendsto hlim' hbound
    simpa [nm, g, L] using hfin

open IsLocalRing in

theorem _root_.GlobalTheory.completeDVR_eq_integralClosure_padicInt :
    (∀ (V K : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [IsAdicComplete (maximalIdeal V) V] [Field K] [CharZero K] [Algebra V K] [IsFractionRing V K], Finite (ResidueField V) → ∃ (p : ℕ) (_ : Fact p.Prime) (K₀ : IntermediateField ℚ_[p] (PadicAlgCl p)) (e : K ≃+* K₀) (e₀ : V ≃+* integralClosure ℤ_[p] K₀), FiniteDimensional ℚ_[p] K₀ ∧ ∀ x, e (algebraMap V K x) = ((e₀ x : integralClosure ℤ_[p] K₀) : K₀)) ∧ ∀ (p : ℕ) [Fact p.Prime] (K₀ K' : IntermediateField ℚ_[p] (PadicAlgCl p)) (h : K₀ ≤ K'), FiniteDimensional ℚ_[p] K' → IsDiscreteValuationRing (integralClosure ℤ_[p] K') ∧ IsFractionRing (integralClosure ℤ_[p] K') K' ∧ (∀ [IsLocalRing (integralClosure ℤ_[p] K')], IsAdicComplete (maximalIdeal (integralClosure ℤ_[p] K')) (integralClosure ℤ_[p] K')) ∧ ∃ f : integralClosure ℤ_[p] K₀ →+* integralClosure ℤ_[p] K', f.Finite ∧ IsLocalHom f ∧ ∀ x, ((f x : integralClosure ℤ_[p] K') : K') = IntermediateField.inclusion h x := by
  refine ⟨fun V K _ _ _ _ _ _ _ _ hres => ?_, fun p _ K₀ K' h hK' => ?_⟩
  · haveI := hres
    exact _root_.GlobalTheory.exists_ringEquiv_integralClosure_padicInt V K
  · haveI := hK'
    refine ⟨_root_.GlobalTheory.isDiscreteValuationRing_integralClosure_padicInt p K',
      _root_.GlobalTheory.isFractionRing_integralClosure_padicInt p K',
      isAdicComplete_integralClosure_padicInt p K', ?_⟩
    let F := ((IntermediateField.inclusion h).restrictScalars ℤ_[p]).mapIntegralClosure
    have hF : Function.Injective F := _root_.GlobalTheory.mapIntegralClosure_padicInt_injective _
    refine ⟨(F : integralClosure ℤ_[p] K₀ →+* integralClosure ℤ_[p] K'), ?_,
      _root_.GlobalTheory.isLocalHom_of_injective_integralClosure F hF, fun x => rfl⟩
    haveI := _root_.GlobalTheory.finite_integralClosure_padicInt p K'
    refine RingHom.Finite.of_comp_finite (f := algebraMap ℤ_[p] (integralClosure ℤ_[p] K₀)) ?_
    rw [AlgHom.comp_algebraMap]
    exact RingHom.finite_algebraMap.mpr inferInstance

end GlobalTheory
