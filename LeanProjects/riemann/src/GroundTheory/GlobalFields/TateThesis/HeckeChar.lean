import Mathlib
import GroundTheory.GlobalFields.IdeleGroups.ClassGroup
import GroundTheory.GlobalFields.TateThesis.ConductorIdeal

open Topology Filter NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum WithZero
  FractionalIdeal Function
open scoped NumberField.AdeleRing nonZeroDivisors

namespace GroundTheory.Global

noncomputable section

variable (K : Type*) [Field K] [NumberField K]

abbrev HeckeCharacter : Type _ := IdeleClassGroup K →ₜ* Circle

variable {K}

def idealsPrimeTo (𝔪 : Ideal (𝓞 K)) : Subgroup (FractionalIdeal (𝓞 K)⁰ K)ˣ where
  carrier := {I | ∀ v : HeightOneSpectrum (𝓞 K), v.asIdeal ∣ 𝔪 →
    count K v (I : FractionalIdeal (𝓞 K)⁰ K) = 0}
  one_mem' := fun v _ ↦ by rw [Units.val_one, count_one]
  mul_mem' {I J} hI hJ v hv := by
    rw [Units.val_mul, count_mul K v I.ne_zero J.ne_zero, hI v hv, hJ v hv, add_zero]
  inv_mem' {I} hI v hv := by
    rw [Units.val_inv_eq_inv_val, count_inv, hI v hv, neg_zero]

theorem primeIdealUnit_mem_idealsPrimeTo {𝔪 : Ideal (𝓞 K)} {v : HeightOneSpectrum (𝓞 K)}
    (hv : ¬ v.asIdeal ∣ 𝔪) : primeIdealUnit v ∈ idealsPrimeTo 𝔪 := by
  classical
  intro w hw
  rw [count_primeIdealUnit, if_neg]
  rintro rfl
  exact hv hw

theorem idealsPrimeTo_top : idealsPrimeTo (⊤ : Ideal (𝓞 K)) = ⊤ := by
  exact eq_top_iff.2 fun I _ v hv ↦
    absurd (top_le_iff.1 (Ideal.le_of_dvd hv)) v.isPrime.ne_top

namespace IdeleGroup

theorem exists_uniformizer (v : HeightOneSpectrum (𝓞 K)) :
    ∃ π : (v.adicCompletion K)ˣ, Valued.v (π : v.adicCompletion K) = exp (-1 : ℤ) := by
  obtain ⟨π, hπ⟩ := v.valuation_exists_uniformizer K
  have hne : ((π : K) : v.adicCompletion K) ≠ 0 := by
    intro h
    have h' := congrArg Valued.v h
    rw [valuedAdicCompletion_eq_valuation', hπ, map_zero] at h'
    exact exp_ne_zero h'
  exact ⟨Units.mk0 _ hne, by rw [Units.val_mk0, valuedAdicCompletion_eq_valuation', hπ]⟩

@[simp]
theorem toInfinite_finiteEmbedding (v : HeightOneSpectrum (𝓞 K)) (a : (v.adicCompletion K)ˣ) :
    toInfinite K (finiteEmbedding v a) = 1 :=
  Units.ext rfl

theorem finiteComponent_toFinite (v : HeightOneSpectrum (𝓞 K)) (x : IdeleGroup K) :
    finiteComponent v (toFinite K x) = finiteProj v x :=
  Units.ext rfl

@[simp]
theorem ofFinite_finiteUnitsSingle (v : HeightOneSpectrum (𝓞 K)) (a : (v.adicCompletion K)ˣ) :
    ofFinite (finiteUnitsSingle v a) = finiteEmbedding v a :=
  Units.ext rfl

theorem ofFinite_toFinite_of_toInfinite_eq_one {x : IdeleGroup K} (hx : toInfinite K x = 1) :
    ofFinite (toFinite K x) = x := by
  apply (prodEquiv K).injective
  refine Prod.ext ?_ ?_
  · change toInfinite K (ofFinite (toFinite K x)) = toInfinite K x
    rw [toInfinite_ofFinite, hx]
  · change toFinite K (ofFinite (toFinite K x)) = toFinite K x
    rw [toFinite_ofFinite]

theorem ord_eq_zero_of_mem_unitsLevel {v : HeightOneSpectrum (𝓞 K)} {x : IdeleGroup K} {n : ℕ}
    (h : finiteProj v x ∈ unitsLevel v n) : ord v x = 0 := by
  rw [ord, ← coe_finiteProj, (mem_unitsLevel.1 h).1, log_one, neg_zero]

theorem toFractionalIdeal_finiteEmbedding_of_uniformizer {v : HeightOneSpectrum (𝓞 K)}
    {π : (v.adicCompletion K)ˣ} (hπ : Valued.v (π : v.adicCompletion K) = exp (-1 : ℤ)) :
    toFractionalIdeal (finiteEmbedding v π) = primeIdealUnit v := by
  classical
  refine toFractionalIdeal_eq_iff.2 fun w ↦ ?_
  rw [count_primeIdealUnit]
  split_ifs with h
  · subst h
    rw [ord_finiteEmbedding_self, hπ, log_exp, neg_neg]
  · exact ord_finiteEmbedding_of_ne h _

def primeToLevel (𝔪 : Ideal (𝓞 K)) : Subgroup (IdeleGroup K) :=
  (toInfinite K).ker ⊓ ⨅ v : HeightOneSpectrum (𝓞 K), ⨅ (_ : v.asIdeal ∣ 𝔪),
    (unitsLevel v (multiplicity v.asIdeal 𝔪)).comap (finiteProj v)

theorem mem_primeToLevel {𝔪 : Ideal (𝓞 K)} {x : IdeleGroup K} :
    x ∈ primeToLevel 𝔪 ↔ toInfinite K x = 1 ∧ ∀ v : HeightOneSpectrum (𝓞 K), v.asIdeal ∣ 𝔪 →
      finiteProj v x ∈ unitsLevel v (multiplicity v.asIdeal 𝔪) := by
  simp only [primeToLevel, Subgroup.mem_inf, MonoidHom.mem_ker, Subgroup.mem_iInf,
    Subgroup.mem_comap]

theorem finiteEmbedding_mem_primeToLevel {𝔪 : Ideal (𝓞 K)} {v : HeightOneSpectrum (𝓞 K)}
    (hv : ¬ v.asIdeal ∣ 𝔪) (a : (v.adicCompletion K)ˣ) : finiteEmbedding v a ∈ primeToLevel 𝔪 := by
  refine mem_primeToLevel.2 ⟨toInfinite_finiteEmbedding v a, fun w hw ↦ ?_⟩
  have hwv : w ≠ v := by
    rintro rfl
    exact hv hw
  rw [finiteProj_finiteEmbedding_of_ne hwv]
  exact one_mem _

theorem toFractionalIdeal_mem_idealsPrimeTo {𝔪 : Ideal (𝓞 K)} {x : IdeleGroup K}
    (hx : x ∈ primeToLevel 𝔪) : toFractionalIdeal x ∈ idealsPrimeTo 𝔪 := by
  intro v hv
  rw [count_toFractionalIdeal]
  exact ord_eq_zero_of_mem_unitsLevel ((mem_primeToLevel.1 hx).2 v hv)

theorem exists_mem_primeToLevel {𝔪 : Ideal (𝓞 K)} {I : (FractionalIdeal (𝓞 K)⁰ K)ˣ}
    (hI : I ∈ idealsPrimeTo 𝔪) : ∃ x ∈ primeToLevel 𝔪, toFractionalIdeal x = I := by
  have key : ∀ v : HeightOneSpectrum (𝓞 K), primeIdealUnit v ^ count K v
      (I : FractionalIdeal (𝓞 K)⁰ K) ∈ (primeToLevel 𝔪).map toFractionalIdeal := by
    intro v
    by_cases hv : v.asIdeal ∣ 𝔪
    · rw [hI v hv, zpow_zero]
      exact one_mem _
    · obtain ⟨π, hπ⟩ := exists_uniformizer v
      exact zpow_mem (Subgroup.mem_map.2 ⟨finiteEmbedding v π, finiteEmbedding_mem_primeToLevel hv π,
        toFractionalIdeal_finiteEmbedding_of_uniformizer hπ⟩) _
  have h : I ∈ (primeToLevel 𝔪).map toFractionalIdeal := by
    rw [← finprod_primeIdealUnit_zpow_count I]
    exact finprod_induction (· ∈ (primeToLevel 𝔪).map toFractionalIdeal) (one_mem _)
      (fun _ _ ↦ mul_mem) key
  obtain ⟨x, hx, hxI⟩ := h
  exact ⟨x, hx, hxI⟩

theorem mem_map_idealLevel_of_mem_primeToLevel {𝔪 : Ideal (𝓞 K)} {x : IdeleGroup K}
    (hx : x ∈ primeToLevel 𝔪) (h1 : toFractionalIdeal x = 1) :
    x ∈ (idealLevel 𝔪).map ofFinite := by
  obtain ⟨hinf, hfin⟩ := mem_primeToLevel.1 hx
  refine ⟨toFinite K x, mem_finiteLevel.2 fun v ↦ ?_, ofFinite_toFinite_of_toInfinite_eq_one hinf⟩
  rw [finiteComponent_toFinite]
  by_cases hv : v.asIdeal ∣ 𝔪
  · exact hfin v hv
  · have hord : ord v x = 0 := by
      rw [← count_toFractionalIdeal, h1, Units.val_one, count_one]
    change finiteProj v x ∈ unitsLevel v (multiplicity v.asIdeal 𝔪)
    rw [multiplicity_eq_zero.2 hv, unitsLevel_zero, Submonoid.mem_units_iff]
    exact (ord_eq_zero_iff v x).1 hord

end IdeleGroup

namespace HeckeCharacter

open IdeleGroup

variable (χ : HeckeCharacter K)

def toIdele : IdeleGroup K →* Circle :=
  (χ : IdeleClassGroup K →* Circle).comp (IdeleClassGroup.mk K)

theorem toIdele_apply (x : IdeleGroup K) : χ.toIdele x = χ (IdeleClassGroup.mk K x) :=
  rfl

theorem continuous_toIdele : Continuous χ.toIdele :=
  χ.continuous.comp (IdeleClassGroup.continuous_mk K)

@[simp]
theorem toIdele_diagonal (a : Kˣ) : χ.toIdele (diagonal K a) = 1 := by
  rw [toIdele_apply, IdeleClassGroup.mk_diagonal, map_one]

def localComponent (v : HeightOneSpectrum (𝓞 K)) : (v.adicCompletion K)ˣ →ₜ* Circle where
  toMonoidHom := χ.toIdele.comp (finiteEmbedding v)
  continuous_toFun := χ.continuous_toIdele.comp (continuous_finiteEmbedding v)

theorem localComponent_apply (v : HeightOneSpectrum (𝓞 K)) (a : (v.adicCompletion K)ˣ) :
    χ.localComponent v a = χ.toIdele (finiteEmbedding v a) :=
  rfl

def infiniteComponent (w : InfinitePlace K) : (w.Completion)ˣ →ₜ* Circle where
  toMonoidHom := χ.toIdele.comp (infiniteEmbedding w)
  continuous_toFun := χ.continuous_toIdele.comp (continuous_infiniteEmbedding w)

theorem infiniteComponent_apply (w : InfinitePlace K) (a : (w.Completion)ˣ) :
    χ.infiniteComponent w a = χ.toIdele (infiniteEmbedding w a) :=
  rfl

def conductor : Ideal (𝓞 K) :=
  IdeleGroup.conductor (χ.toIdele.comp ofFinite)

theorem conductor_ne_bot : χ.conductor ≠ ⊥ :=
  IdeleGroup.conductor_ne_bot _

theorem map_idealLevel_le_ker_iff {𝔪 : Ideal (𝓞 K)} (h𝔪 : 𝔪 ≠ ⊥) :
    (idealLevel 𝔪).map ofFinite ≤ χ.toIdele.ker ↔ χ.conductor ∣ 𝔪 :=
  IdeleGroup.map_idealLevel_le_ker_iff Circle.noSmallSubgroups χ.toIdele χ.continuous_toIdele h𝔪

theorem map_idealLevel_conductor_le_ker : (idealLevel χ.conductor).map ofFinite ≤ χ.toIdele.ker :=
  (χ.map_idealLevel_le_ker_iff χ.conductor_ne_bot).2 dvd_rfl

theorem not_dvd_conductor_iff (v : HeightOneSpectrum (𝓞 K)) :
    ¬ v.asIdeal ∣ χ.conductor ↔
      (Submonoid.ofClass (v.adicCompletionIntegers K)).units ≤
        (χ.localComponent v : (v.adicCompletion K)ˣ →* Circle).ker := by
  have h : (χ.toIdele.comp ofFinite).comp (finiteUnitsSingle v) =
      (χ.localComponent v : (v.adicCompletion K)ˣ →* Circle) := by
    ext a
    simp only [MonoidHom.comp_apply, ofFinite_finiteUnitsSingle]
    rfl
  rw [conductor, IdeleGroup.not_dvd_conductor_iff Circle.noSmallSubgroups _
    (χ.continuous_toIdele.comp continuous_ofFinite), h]

theorem localComponent_eq_one_of_not_dvd {v : HeightOneSpectrum (𝓞 K)}
    (hv : ¬ v.asIdeal ∣ χ.conductor) {a : (v.adicCompletion K)ˣ}
    (ha : a ∈ (Submonoid.ofClass (v.adicCompletionIntegers K)).units) :
    χ.localComponent v a = 1 :=
  (χ.not_dvd_conductor_iff v).1 hv ha

theorem localComponent_uniformizer_eq {v : HeightOneSpectrum (𝓞 K)}
    (hv : ¬ v.asIdeal ∣ χ.conductor) {π π' : (v.adicCompletion K)ˣ}
    (hπ : Valued.v (π : v.adicCompletion K) = exp (-1 : ℤ))
    (hπ' : Valued.v (π' : v.adicCompletion K) = exp (-1 : ℤ)) :
    χ.localComponent v π = χ.localComponent v π' := by
  have hu : π * π'⁻¹ ∈ (Submonoid.ofClass (v.adicCompletionIntegers K)).units := by
    rw [← unitsLevel_zero, mem_unitsLevel]
    have hπ0 : Valued.v (π' : v.adicCompletion K) ≠ 0 := by rw [hπ']; exact exp_ne_zero
    have h1 : Valued.v ((π * π'⁻¹ : (v.adicCompletion K)ˣ) : v.adicCompletion K) = 1 := by
      rw [Units.val_mul, Units.val_inv_eq_inv_val, map_mul, map_inv₀, hπ, ← hπ',
        mul_inv_cancel₀ hπ0]
    refine ⟨h1, ?_⟩
    rw [Nat.cast_zero, neg_zero, exp_zero]
    exact Valuation.map_sub_le _ h1.le (by simp)
  have h := χ.localComponent_eq_one_of_not_dvd hv hu
  rwa [map_mul, map_inv, mul_inv_eq_one] at h

theorem toIdele_eq_of_toFractionalIdeal_eq {x y : IdeleGroup K}
    (hx : x ∈ primeToLevel χ.conductor) (hy : y ∈ primeToLevel χ.conductor)
    (h : toFractionalIdeal x = toFractionalIdeal y) : χ.toIdele x = χ.toIdele y := by
  have hmem : x * y⁻¹ ∈ (idealLevel χ.conductor).map ofFinite :=
    mem_map_idealLevel_of_mem_primeToLevel (mul_mem hx (inv_mem hy))
      (by rw [map_mul, map_inv, h, mul_inv_cancel])
  have h' := χ.map_idealLevel_conductor_le_ker hmem
  rwa [MonoidHom.mem_ker, map_mul, map_inv, mul_inv_eq_one] at h'

def idealCharacter : idealsPrimeTo χ.conductor →* Circle where
  toFun I := χ.toIdele (exists_mem_primeToLevel I.2).choose
  map_one' := by
    obtain ⟨hx, hx1⟩ := (exists_mem_primeToLevel (1 : idealsPrimeTo χ.conductor).2).choose_spec
    rw [← map_one χ.toIdele]
    exact χ.toIdele_eq_of_toFractionalIdeal_eq hx (one_mem _) (by rw [hx1, map_one]; rfl)
  map_mul' I J := by
    obtain ⟨hx, hxI⟩ := (exists_mem_primeToLevel I.2).choose_spec
    obtain ⟨hy, hyJ⟩ := (exists_mem_primeToLevel J.2).choose_spec
    obtain ⟨hz, hzIJ⟩ := (exists_mem_primeToLevel (I * J).2).choose_spec
    rw [← map_mul]
    exact χ.toIdele_eq_of_toFractionalIdeal_eq hz (mul_mem hx hy)
      (by rw [hzIJ, map_mul, hxI, hyJ]; rfl)

theorem idealCharacter_apply {x : IdeleGroup K} (hx : x ∈ primeToLevel χ.conductor)
    (I : idealsPrimeTo χ.conductor) (h : toFractionalIdeal x = I) :
    χ.idealCharacter I = χ.toIdele x := by
  obtain ⟨hy, hyI⟩ := (exists_mem_primeToLevel I.2).choose_spec
  exact χ.toIdele_eq_of_toFractionalIdeal_eq hy hx (hyI.trans h.symm)

theorem idealCharacter_primeIdealUnit {v : HeightOneSpectrum (𝓞 K)}
    (hv : ¬ v.asIdeal ∣ χ.conductor) {π : (v.adicCompletion K)ˣ}
    (hπ : Valued.v (π : v.adicCompletion K) = exp (-1 : ℤ)) :
    χ.idealCharacter ⟨primeIdealUnit v, primeIdealUnit_mem_idealsPrimeTo hv⟩ =
      χ.localComponent v π :=
  χ.idealCharacter_apply (finiteEmbedding_mem_primeToLevel hv π) _
    (toFractionalIdeal_finiteEmbedding_of_uniformizer hπ)

end HeckeCharacter

end

end GroundTheory.Global
