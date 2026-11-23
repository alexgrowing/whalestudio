import Mathlib
import GroundTheory.PAdicHodge.BdRGalois
set_option maxSynthPendingDepth 1

open Ideal WittVector IsLocalRing

noncomputable section

namespace GroundTheory.PAdicHodge

section General

variable (R : Type*) [CommRing R] (p : ℕ) [Fact p.Prime] [Fact ¬IsUnit (p : R)]
  [IsAdicComplete (span {(p : R)}) R]

def bDeRhamSubmonoid : Submonoid (BDeRhamPlus R p) :=
  Submonoid.closure <| AdicCompletion.of (RingHom.ker (fontaineThetaInvertP R p)) _ ''
    {a | RingHom.ker (fontaineThetaInvertP R p) = span {a}}

instance instCommRingBDeRham : CommRing (BDeRham R p) :=
  inferInstanceAs (CommRing (Localization (bDeRhamSubmonoid R p)))

instance instAlgebraBDeRham : Algebra (BDeRhamPlus R p) (BDeRham R p) :=
  inferInstanceAs (Algebra (BDeRhamPlus R p) (Localization (bDeRhamSubmonoid R p)))

instance isLocalization_bDeRham : IsLocalization (bDeRhamSubmonoid R p) (BDeRham R p) :=
  inferInstanceAs (IsLocalization (bDeRhamSubmonoid R p) (Localization (bDeRhamSubmonoid R p)))

end General

namespace IsPerfectoidField

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K]
variable {p : ℕ} [Fact p.Prime] [IsPerfectoidField K p] [CharZero K]

local notation "𝒪" => normInteger K
local notation "𝔸" => Localization.Away (p : WittVector p (PreTilt (normInteger K) p))
local notation "𝔹" => BDeRhamPlus (normInteger K) p
local notation "𝔹dR" => BDeRham (normInteger K) p
local notation "J" => RingHom.ker (fontaineThetaInvertP (normInteger K) p)

theorem maximalIdeal_eq_span_of_ker_eq_span {a : 𝔸} (ha : J = span {a}) :
    maximalIdeal 𝔹 = span {toBDeRhamPlus 𝒪 p a} := by
  rw [← map_ker_fontaineThetaInvertP K p, ha, Ideal.map_span, Set.image_singleton]

variable (K p) in

def varpi : 𝔹 := wittToBDeRhamPlus 𝒪 p (kerThetaGenerator K p)

variable (K p) in
theorem maximalIdeal_eq_span_varpi : maximalIdeal 𝔹 = span {varpi K p} :=
  maximalIdeal_bDeRhamPlus_eq_span (ker_fontaineTheta_eq_span_kerThetaGenerator K p)

theorem ne_zero_of_maximalIdeal_eq_span {π : 𝔹} (hπ : maximalIdeal 𝔹 = span {π}) : π ≠ 0 := by
  rintro rfl
  rw [span_singleton_eq_bot.2 rfl] at hπ
  exact IsDiscreteValuationRing.not_a_field 𝔹 hπ

variable (K p) in
theorem varpi_mem_bDeRhamSubmonoid : varpi K p ∈ bDeRhamSubmonoid 𝒪 p := by
  refine Submonoid.subset_closure ⟨algebraMap _ 𝔸 (kerThetaGenerator K p), ?_, rfl⟩
  exact ker_fontaineThetaInvertP (ker_fontaineTheta_eq_span_kerThetaGenerator K p)

variable (K p) in
theorem bDeRhamSubmonoid_le_nonZeroDivisors : bDeRhamSubmonoid 𝒪 p ≤ nonZeroDivisors 𝔹 := by
  refine Submonoid.closure_le.2 ?_
  rintro _ ⟨a, ha, rfl⟩
  exact mem_nonZeroDivisors_of_ne_zero (ne_zero_of_maximalIdeal_eq_span
    (maximalIdeal_eq_span_of_ker_eq_span ha))

theorem isUnit_algebraMap_bDeRham {x : 𝔹} (hx : x ≠ 0) : IsUnit (algebraMap 𝔹 𝔹dR x) := by
  obtain ⟨n, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hx
    (irreducible_wittToBDeRhamPlus (ker_fontaineTheta_eq_span_kerThetaGenerator K p))
  rw [map_mul, map_pow]
  exact (u.isUnit.map _).mul ((IsLocalization.map_units (M := bDeRhamSubmonoid 𝒪 p) 𝔹dR
    ⟨varpi K p, varpi_mem_bDeRhamSubmonoid K p⟩).pow n)

instance isFractionRing_bDeRham : IsFractionRing 𝔹 𝔹dR := by
  have hS := bDeRhamSubmonoid_le_nonZeroDivisors K p
  have hL : IsLocalization (bDeRhamSubmonoid 𝒪 p) 𝔹dR := inferInstance
  rw [IsFractionRing, isLocalization_iff] at *
  refine ⟨fun y => isUnit_algebraMap_bDeRham (nonZeroDivisors.coe_ne_zero y), fun z => ?_,
    fun {x y} h => ?_⟩
  · obtain ⟨⟨x, s⟩, hs⟩ := hL.2.1 z
    exact ⟨⟨x, ⟨s, hS s.2⟩⟩, hs⟩
  · obtain ⟨c, hc⟩ := hL.2.2 h
    exact ⟨⟨c, hS c.2⟩, hc⟩

instance instFieldBDeRham : Field 𝔹dR := IsFractionRing.toField 𝔹

theorem algebraMap_bDeRham_injective : Function.Injective (algebraMap 𝔹 𝔹dR) :=
  IsFractionRing.injective 𝔹 𝔹dR

theorem algebraMap_ne_zero_of_maximalIdeal_eq_span {π : 𝔹} (hπ : maximalIdeal 𝔹 = span {π}) :
    algebraMap 𝔹 𝔹dR π ≠ 0 :=
  (map_ne_zero_iff _ algebraMap_bDeRham_injective).2 (ne_zero_of_maximalIdeal_eq_span hπ)

theorem isLocalization_away_bDeRham {π : 𝔹} (hπ : maximalIdeal 𝔹 = span {π}) :
    IsLocalization.Away π 𝔹dR := by
  have hirr : Irreducible π := IsDiscreteValuationRing.irreducible_iff_uniformizer π |>.2 hπ
  rw [IsLocalization.Away, isLocalization_iff]
  refine ⟨?_, fun z => ?_, fun {x y} h => ⟨1, by rw [algebraMap_bDeRham_injective h]⟩⟩
  · rintro ⟨_, n, rfl⟩
    have h := (isUnit_algebraMap_bDeRham (K := K) (ne_zero_of_maximalIdeal_eq_span hπ)).pow n
    rw [← map_pow] at h
    exact h
  · obtain ⟨⟨x, y⟩, hxy⟩ := IsLocalization.surj (nonZeroDivisors 𝔹) z
    obtain ⟨n, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible
      (nonZeroDivisors.coe_ne_zero y) hirr
    refine ⟨⟨x * ↑u⁻¹, ⟨π ^ n, n, rfl⟩⟩, ?_⟩
    simp only at hxy ⊢
    have hu' : (y : 𝔹) * ↑u⁻¹ = π ^ n := by rw [hu, mul_comm (↑u : 𝔹), mul_assoc, Units.mul_inv, mul_one]
    rw [← hu', map_mul, ← mul_assoc, hxy, map_mul]

variable (K p) in

def fil (i : ℤ) : Submodule 𝔹 𝔹dR := Submodule.span 𝔹 {algebraMap 𝔹 𝔹dR (varpi K p) ^ i}

theorem algebraMap_units_zpow (u : 𝔹ˣ) (i : ℤ) :
    algebraMap 𝔹 𝔹dR (↑u) ^ i = algebraMap 𝔹 𝔹dR ↑(u ^ i) := by
  rcases i with n | n
  · simp only [Int.ofNat_eq_coe, zpow_natCast, Units.val_pow_eq_pow_val, map_pow]
  · rw [zpow_negSucc, zpow_negSucc, ← map_pow, ← Units.val_pow_eq_pow_val]
    exact (map_units_inv (algebraMap 𝔹 𝔹dR) _).symm

theorem fil_eq_span {π : 𝔹} (hπ : maximalIdeal 𝔹 = span {π}) (i : ℤ) :
    fil K p i = Submodule.span 𝔹 {algebraMap 𝔹 𝔹dR π ^ i} := by
  obtain ⟨u, hu⟩ := Ideal.span_singleton_eq_span_singleton.1
    (hπ.symm.trans (maximalIdeal_eq_span_varpi K p))
  rw [fil, ← hu, map_mul, mul_zpow, algebraMap_units_zpow, mul_comm (algebraMap 𝔹 𝔹dR π ^ i),
    ← Algebra.smul_def, Submodule.span_singleton_smul_eq (Units.isUnit _)]

theorem mem_fil_iff {π : 𝔹} (hπ : maximalIdeal 𝔹 = span {π}) {i : ℤ} {x : 𝔹dR} :
    x ∈ fil K p i ↔ ∃ b : 𝔹, x = algebraMap 𝔹 𝔹dR π ^ i * algebraMap 𝔹 𝔹dR b := by
  rw [fil_eq_span hπ, Submodule.mem_span_singleton]
  constructor
  · rintro ⟨b, rfl⟩
    exact ⟨b, by rw [Algebra.smul_def, mul_comm]⟩
  · rintro ⟨b, rfl⟩
    exact ⟨b, by rw [Algebra.smul_def, mul_comm]⟩

variable (K p) in

theorem fil_antitone : Antitone (fil K p) := by
  intro i j hij
  have hϖ := maximalIdeal_eq_span_varpi K p
  change Submodule.span 𝔹 {algebraMap 𝔹 𝔹dR (varpi K p) ^ j} ≤ fil K p i
  rw [Submodule.span_singleton_le_iff_mem, mem_fil_iff hϖ]
  refine ⟨varpi K p ^ (j - i).toNat, ?_⟩
  rw [map_pow, ← zpow_natCast, Int.toNat_of_nonneg (by omega),
    ← zpow_add₀ (algebraMap_ne_zero_of_maximalIdeal_eq_span hϖ), add_sub_cancel]

variable (K p) in

theorem fil_zero : fil K p 0 = 1 := by
  rw [fil, zpow_zero, Submodule.one_eq_span]

variable (K p) in

theorem mem_fil_zero_iff {x : 𝔹dR} : x ∈ fil K p 0 ↔ ∃ b : 𝔹, x = algebraMap 𝔹 𝔹dR b := by
  rw [mem_fil_iff (maximalIdeal_eq_span_varpi K p), zpow_zero]
  simp only [one_mul]

theorem algebraMap_mem_fil_iff (b : 𝔹) (n : ℕ) :
    algebraMap 𝔹 𝔹dR b ∈ fil K p n ↔ b ∈ maximalIdeal 𝔹 ^ n := by
  rw [mem_fil_iff (maximalIdeal_eq_span_varpi K p), maximalIdeal_eq_span_varpi K p,
    span_singleton_pow, mem_span_singleton]
  simp only [zpow_natCast, ← map_pow, ← map_mul]
  constructor
  · rintro ⟨c, hc⟩
    exact ⟨c, algebraMap_bDeRham_injective hc⟩
  · rintro ⟨c, hc⟩
    exact ⟨c, by rw [hc]⟩

variable (K p) in

theorem iInf_fil : ⨅ i, fil K p i = ⊥ := by
  have hϖ := maximalIdeal_eq_span_varpi K p
  have hne := algebraMap_ne_zero_of_maximalIdeal_eq_span (K := K) hϖ
  haveI := isLocalization_away_bDeRham hϖ
  refine eq_bot_iff.2 fun x hx => ?_
  rw [Submodule.mem_iInf] at hx
  obtain ⟨⟨a, ⟨_, m, rfl⟩⟩, ha⟩ := IsLocalization.surj (Submonoid.powers (varpi K p)) x
  simp only [map_pow] at ha
  have ha0 : a = 0 := by
    refine eq_zero_of_forall_mem_maximalIdeal_pow fun n => ?_
    obtain ⟨b, hb⟩ := (mem_fil_iff hϖ).1 (hx ((n : ℤ) - m))
    have h2 : algebraMap 𝔹 𝔹dR a = algebraMap 𝔹 𝔹dR (varpi K p ^ n * b) := by
      rw [← ha, hb, map_mul, map_pow, mul_right_comm,
        ← zpow_natCast (algebraMap 𝔹 𝔹dR (varpi K p)) m, ← zpow_add₀ hne, sub_add_cancel,
        zpow_natCast]
    rw [algebraMap_bDeRham_injective h2, hϖ, span_singleton_pow]
    exact mul_mem_right _ _ (mem_span_singleton_self _)
  rw [ha0, map_zero] at ha
  rw [Submodule.mem_bot]
  exact (mul_eq_zero.1 ha).resolve_right (pow_ne_zero _ hne)

variable (K p) in

theorem iSup_fil : ⨆ i, fil K p i = ⊤ := by
  have hϖ := maximalIdeal_eq_span_varpi K p
  have hne := algebraMap_ne_zero_of_maximalIdeal_eq_span (K := K) hϖ
  haveI := isLocalization_away_bDeRham hϖ
  refine eq_top_iff.2 fun x _ => ?_
  obtain ⟨⟨a, ⟨_, m, rfl⟩⟩, ha⟩ := IsLocalization.surj (Submonoid.powers (varpi K p)) x
  simp only [map_pow] at ha
  refine Submodule.mem_iSup_of_mem (-(m : ℤ)) ((mem_fil_iff hϖ).2 ⟨a, ?_⟩)
  rw [← ha, zpow_neg, zpow_natCast, mul_comm x, ← mul_assoc, inv_mul_cancel₀ (pow_ne_zero _ hne),
    one_mul]

variable (K p) in

theorem fil_mul_fil (i j : ℤ) : fil K p i * fil K p j = fil K p (i + j) := by
  rw [fil, fil, fil, Submodule.span_mul_span, Set.singleton_mul_singleton,
    ← zpow_add₀ (algebraMap_ne_zero_of_maximalIdeal_eq_span (maximalIdeal_eq_span_varpi K p))]

theorem mul_mem_fil {i j : ℤ} {x y : 𝔹dR} (hx : x ∈ fil K p i) (hy : y ∈ fil K p j) :
    x * y ∈ fil K p (i + j) :=
  fil_mul_fil K p i j ▸ Submodule.mul_mem_mul hx hy

def filMk {π : 𝔹} (hπ : maximalIdeal 𝔹 = span {π}) (i : ℤ) : 𝔹 →ₗ[𝔹] fil K p i where
  toFun b := ⟨algebraMap 𝔹 𝔹dR π ^ i * algebraMap 𝔹 𝔹dR b, (mem_fil_iff hπ).2 ⟨b, rfl⟩⟩
  map_add' a b := Subtype.ext (by simp only [map_add, mul_add, Submodule.coe_add])
  map_smul' c b := Subtype.ext (by
    simp only [smul_eq_mul, map_mul, Submodule.coe_smul, RingHom.id_apply, Algebra.smul_def]
    ring)

theorem filMk_bijective {π : 𝔹} (hπ : maximalIdeal 𝔹 = span {π}) (i : ℤ) :
    Function.Bijective (filMk (K := K) hπ i) := by
  have hne := zpow_ne_zero i (algebraMap_ne_zero_of_maximalIdeal_eq_span (K := K) hπ)
  refine ⟨fun a b h => algebraMap_bDeRham_injective (mul_left_cancel₀ hne
    (congrArg Subtype.val h)), fun x => ?_⟩
  obtain ⟨b, hb⟩ := (mem_fil_iff hπ).1 x.2
  exact ⟨b, Subtype.ext hb.symm⟩

def filEquiv {π : 𝔹} (hπ : maximalIdeal 𝔹 = span {π}) (i : ℤ) : fil K p i ≃ₗ[𝔹] 𝔹 :=
  (LinearEquiv.ofBijective (filMk hπ i) (filMk_bijective hπ i)).symm

theorem coe_eq_filEquiv {π : 𝔹} (hπ : maximalIdeal 𝔹 = span {π}) {i : ℤ} (x : fil K p i) :
    (x : 𝔹dR) = algebraMap 𝔹 𝔹dR π ^ i * algebraMap 𝔹 𝔹dR (filEquiv hπ i x) :=
  (congrArg Subtype.val
    ((LinearEquiv.ofBijective (filMk hπ i) (filMk_bijective hπ i)).apply_symm_apply x)).symm

theorem filEquiv_mk {π : 𝔹} (hπ : maximalIdeal 𝔹 = span {π}) {i : ℤ} (b : 𝔹)
    (h : algebraMap 𝔹 𝔹dR π ^ i * algebraMap 𝔹 𝔹dR b ∈ fil K p i) :
    filEquiv hπ i ⟨algebraMap 𝔹 𝔹dR π ^ i * algebraMap 𝔹 𝔹dR b, h⟩ = b :=
  (LinearEquiv.ofBijective (filMk hπ i) (filMk_bijective hπ i)).symm_apply_apply b

def grMap {π : 𝔹} (hπ : maximalIdeal 𝔹 = span {π}) (i : ℤ) : fil K p i →+ K :=
  (thetaBDeRhamPlusField p).toAddMonoidHom.comp (filEquiv hπ i).toLinearMap.toAddMonoidHom

theorem grMap_apply {π : 𝔹} (hπ : maximalIdeal 𝔹 = span {π}) {i : ℤ} (x : fil K p i) :
    grMap hπ i x = thetaBDeRhamPlusField p (filEquiv hπ i x) := rfl

theorem grMap_mk {π : 𝔹} (hπ : maximalIdeal 𝔹 = span {π}) {i : ℤ} (b : 𝔹)
    (h : algebraMap 𝔹 𝔹dR π ^ i * algebraMap 𝔹 𝔹dR b ∈ fil K p i) :
    grMap hπ i ⟨algebraMap 𝔹 𝔹dR π ^ i * algebraMap 𝔹 𝔹dR b, h⟩ = thetaBDeRhamPlusField p b := by
  rw [grMap_apply, filEquiv_mk]

theorem grMap_smul {π : 𝔹} (hπ : maximalIdeal 𝔹 = span {π}) {i : ℤ} (c : 𝔹) (x : fil K p i) :
    grMap hπ i (c • x) = thetaBDeRhamPlusField p c * grMap hπ i x := by
  rw [grMap_apply, grMap_apply, map_smul, smul_eq_mul, map_mul]

theorem grMap_surjective {π : 𝔹} (hπ : maximalIdeal 𝔹 = span {π}) (i : ℤ) :
    Function.Surjective (grMap (K := K) hπ i) :=
  (surjective_thetaBDeRhamPlusField p).comp (filEquiv hπ i).surjective

theorem grMap_eq_zero_iff {π : 𝔹} (hπ : maximalIdeal 𝔹 = span {π}) {i : ℤ} (x : fil K p i) :
    grMap hπ i x = 0 ↔ (x : 𝔹dR) ∈ fil K p (i + 1) := by
  have hne := algebraMap_ne_zero_of_maximalIdeal_eq_span (K := K) hπ
  rw [grMap_apply, ← RingHom.mem_ker, ← maximalIdeal_bDeRhamPlus (K := K) (p := p), hπ,
    mem_span_singleton, mem_fil_iff hπ, coe_eq_filEquiv hπ x]
  constructor
  · rintro ⟨c, hc⟩
    exact ⟨c, by rw [hc, map_mul, zpow_add_one₀ hne]; ring⟩
  · rintro ⟨c, hc⟩
    refine ⟨c, algebraMap_bDeRham_injective ?_⟩
    rw [zpow_add_one₀ hne, mul_assoc] at hc
    rw [map_mul]
    exact mul_left_cancel₀ (zpow_ne_zero i hne) hc

theorem ker_grMap {π : 𝔹} (hπ : maximalIdeal 𝔹 = span {π}) (i : ℤ) :
    (grMap hπ i).ker = ((fil K p (i + 1)).comap (fil K p i).subtype).toAddSubgroup := by
  ext x
  rw [AddMonoidHom.mem_ker, grMap_eq_zero_iff]
  rfl

def grEquiv {π : 𝔹} (hπ : maximalIdeal 𝔹 = span {π}) (i : ℤ) :
    (fil K p i) ⧸ ((fil K p (i + 1)).comap (fil K p i).subtype) ≃+ K :=
  (QuotientAddGroup.quotientAddEquivOfEq (ker_grMap hπ i).symm).trans
    (QuotientAddGroup.quotientKerEquivOfSurjective _ (grMap_surjective hπ i))

theorem grEquiv_mk {π : 𝔹} (hπ : maximalIdeal 𝔹 = span {π}) {i : ℤ} (x : fil K p i) :
    grEquiv hπ i (Submodule.Quotient.mk x) = grMap hπ i x := rfl

end IsPerfectoidField

section Galois

variable {p : ℕ} [Fact p.Prime] {L : IntermediateField ℚ_[p] (PadicAlgCl p)}

local notation "𝔹" => BDeRhamPlus (normInteger ℂ_[p]) p
local notation "𝔹dR" => BDeRham (normInteger ℂ_[p]) p

def galBdRField (σ : Gal(PadicAlgCl p/L)) : 𝔹dR ≃+* 𝔹dR :=
  IsFractionRing.ringEquivOfRingEquiv (galBdR σ)

theorem galBdRField_algebraMap (σ : Gal(PadicAlgCl p/L)) (b : 𝔹) :
    galBdRField σ (algebraMap 𝔹 𝔹dR b) = algebraMap 𝔹 𝔹dR (σ • b) :=
  IsFractionRing.ringEquivOfRingEquiv_algebraMap _ b

theorem galBdRField_one : galBdRField (1 : Gal(PadicAlgCl p/L)) = RingEquiv.refl 𝔹dR := by
  refine RingEquiv.toRingHom_injective (IsLocalization.ringHom_ext (nonZeroDivisors 𝔹)
    (RingHom.ext fun b => ?_))
  simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingHom.coe_coe,
    galBdRField_algebraMap, one_smul, RingEquiv.coe_ringHom_refl, RingHom.id_apply]

theorem galBdRField_mul (σ τ : Gal(PadicAlgCl p/L)) :
    galBdRField (σ * τ) = (galBdRField τ).trans (galBdRField σ) := by
  refine RingEquiv.toRingHom_injective (IsLocalization.ringHom_ext (nonZeroDivisors 𝔹)
    (RingHom.ext fun b => ?_))
  simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingHom.coe_coe,
    galBdRField_algebraMap, mul_smul, RingEquiv.coe_trans, Function.comp_apply]

instance instMulSemiringActionBdRField : MulSemiringAction Gal(PadicAlgCl p/L) 𝔹dR where
  smul σ x := galBdRField σ x
  one_smul x := by
    change galBdRField 1 x = x
    rw [galBdRField_one]
    rfl
  mul_smul σ τ x := by
    change galBdRField (σ * τ) x = galBdRField σ (galBdRField τ x)
    rw [galBdRField_mul]
    rfl
  smul_zero σ := map_zero (galBdRField σ)
  smul_add σ := map_add (galBdRField σ)
  smul_one σ := map_one (galBdRField σ)
  smul_mul σ := map_mul (galBdRField σ)

theorem gal_smul_bDeRham_def (σ : Gal(PadicAlgCl p/L)) (x : 𝔹dR) : σ • x = galBdRField σ x :=
  rfl

theorem gal_smul_algebraMap_bDeRham (σ : Gal(PadicAlgCl p/L)) (b : 𝔹) :
    σ • algebraMap 𝔹 𝔹dR b = algebraMap 𝔹 𝔹dR (σ • b) :=
  galBdRField_algebraMap σ b

theorem maximalIdeal_eq_span_gal_smul (σ : Gal(PadicAlgCl p/L)) {π : 𝔹}
    (hπ : maximalIdeal 𝔹 = span {π}) : maximalIdeal 𝔹 = span {σ • π} := by
  calc maximalIdeal 𝔹 = (maximalIdeal 𝔹).map (galBdR σ) := by
        simpa using (map_galBdR_maximalIdeal_pow σ 1).symm
    _ = span {σ • π} := by
        rw [hπ, Ideal.map_span, Set.image_singleton]
        rfl

theorem gal_smul_mem_fil (σ : Gal(PadicAlgCl p/L)) {i : ℤ} {x : 𝔹dR}
    (hx : x ∈ IsPerfectoidField.fil ℂ_[p] p i) : σ • x ∈ IsPerfectoidField.fil ℂ_[p] p i := by
  have hϖ := IsPerfectoidField.maximalIdeal_eq_span_varpi ℂ_[p] p
  obtain ⟨b, rfl⟩ := (IsPerfectoidField.mem_fil_iff hϖ).1 hx
  refine (IsPerfectoidField.mem_fil_iff (maximalIdeal_eq_span_gal_smul σ hϖ)).2 ⟨σ • b, ?_⟩
  rw [gal_smul_bDeRham_def, map_mul, map_zpow₀, galBdRField_algebraMap, galBdRField_algebraMap]

theorem gal_smul_mem_fil_iff (σ : Gal(PadicAlgCl p/L)) (i : ℤ) (x : 𝔹dR) :
    σ • x ∈ IsPerfectoidField.fil ℂ_[p] p i ↔ x ∈ IsPerfectoidField.fil ℂ_[p] p i := by
  refine ⟨fun h => ?_, gal_smul_mem_fil σ⟩
  have := gal_smul_mem_fil σ⁻¹ h
  rwa [inv_smul_smul] at this

end Galois

end GroundTheory.PAdicHodge
