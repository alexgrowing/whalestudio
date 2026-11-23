import Mathlib
import GroundTheory.GlobalFields.SplittingFromInequality
import GroundTheory.GlobalFields.IdeleGroups.SIdeleGroups
import GroundTheory.GlobalFields.KummerTheory.SplittingKummer
import GroundTheory.GlobalFields.KummerTheory.Unramified

namespace GroundTheory.Global

open NumberField IsDedekindDomain IntermediateField GroundTheory.ProfCoh
open IdeleNorm SemiLocal
open scoped NumberField.LiesOver

noncomputable section

section InfiniteSplit

variable {K : Type*} [Field K] [NumberField K] {L : Type*} [Field L] [NumberField L] [Algebra K L]

theorem range_infiniteLocalNorm_eq_top_of_splitsCompletely (v : InfinitePlace K)
    (h : InfinitePlace.SplitsCompletely L v) : (infiniteLocalNorm L v).range = ⊤ := by
  classical
  obtain ⟨w⟩ := nonempty_infinitePlacesOver L v
  have hw := (InfinitePlace.splitsCompletely_iff_forall_finrank v).1 h w
  refine eq_top_iff.2 fun a _ ↦ ⟨Pi.mulSingle w (Units.map (algebraMap v.Completion
    (w : InfinitePlace L).Completion : v.Completion →* (w : InfinitePlace L).Completion) a), ?_⟩
  rw [infiniteLocalNorm_mulSingle]
  apply Units.ext
  rw [LocalField.coe_normUnits, Units.coe_map]
  exact (Algebra.norm_algebraMap (a : v.Completion)).trans (by rw [hw, pow_one])

end InfiniteSplit

section Kummer

variable {K : Type*} [Field K] {n : ℕ} [NeZero n]

omit [NeZero n] in

theorem forall_mem_zpowers_exists_pow_eq {F : Type*} [Field F] [Algebra K F] {y : Kˣ}
    (h : ∃ x : F, x ^ n = algebraMap K F (y : K)) :
    ∀ a ∈ Subgroup.zpowers y, ∃ x : F, x ^ n = algebraMap K F (a : K) := by
  obtain ⟨x, hx⟩ := h
  rintro _ ⟨k, rfl⟩
  refine ⟨x ^ k, ?_⟩
  rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hx, Units.val_zpow_eq_zpow_val,
    map_zpow₀]

instance finite_zpowers_quotient_unitsPow (y : Kˣ) :
    Finite (Subgroup.zpowers y ⧸ (unitsPow K n).subgroupOf (Subgroup.zpowers y)) := by
  have hle : (powMonoidHom n : Subgroup.zpowers y →* Subgroup.zpowers y).range ≤
      (unitsPow K n).subgroupOf (Subgroup.zpowers y) := by
    rintro _ ⟨x, rfl⟩
    rw [Subgroup.mem_subgroupOf]
    exact ⟨(x : Kˣ), rfl⟩
  have : Group.FG (Subgroup.zpowers y) := (Group.fg_iff_subgroup_fg _).2
    ⟨{y}, by rw [Finset.coe_singleton, ← Subgroup.zpowers_eq_closure]⟩
  have := Subgroup.finiteIndex_range_powMonoidHom_of_fg (Subgroup.zpowers y) (NeZero.ne n)
  have := Subgroup.finiteIndex_of_le hle
  exact Subgroup.finite_quotient_of_finiteIndex

variable [HasEnoughRootsOfUnity K n] {Ω : Type*} [Field Ω] [Algebra K Ω] [IsSepClosed Ω]

omit [IsSepClosed Ω] in

theorem adjoin_eq_top_of_pow_eq {y : Kˣ} (α : kummerExtension K n Ω (Subgroup.zpowers y))
    (hα : α ^ n = algebraMap K _ (y : K)) : adjoin K {α} = ⊤ := by
  refine eq_top_iff.2 fun m _ ↦ ?_
  have hg : AdjoinSimple.gen K α ^ n = algebraMap K (adjoin K {α}) (y : K) := by
    apply Subtype.ext
    rw [IntermediateField.coe_pow, AdjoinSimple.coe_gen, hα]
    rfl
  obtain ⟨f, hf⟩ := algHom_kummerExtension_mem_fieldRange (F := adjoin K {α})
    (AlgHom.id K (kummerExtension K n Ω (Subgroup.zpowers y)))
    (forall_mem_zpowers_exists_pow_eq ⟨_, hg⟩) m
  have hfm : (f : kummerExtension K n Ω (Subgroup.zpowers y)) = m := hf
  rw [← hfm]
  exact f.2

theorem isCyclic_gal_kummerExtension_zpowers (y : Kˣ) :
    IsCyclic Gal(kummerExtension K n Ω (Subgroup.zpowers y)/K) := by
  set Δ := Subgroup.zpowers y
  let q : Δ ⧸ (unitsPow K n).subgroupOf Δ := ((⟨y, Subgroup.mem_zpowers y⟩ : Δ) : _)
  let ev : ((Δ ⧸ (unitsPow K n).subgroupOf Δ) →* rootsOfUnity n K) →* rootsOfUnity n K :=
    { toFun := fun φ ↦ φ q
      map_one' := rfl
      map_mul' := fun _ _ ↦ rfl }
  have hev : Function.Injective ev := by
    intro φ ψ h
    refine MonoidHom.ext fun c ↦ ?_
    induction c using QuotientGroup.induction_on with
    | H a =>
      obtain ⟨_, k, rfl⟩ := a
      have ha : ((⟨y ^ k, k, rfl⟩ : Δ) : Δ ⧸ (unitsPow K n).subgroupOf Δ) = q ^ k := by
        rw [← QuotientGroup.mk_zpow]
        rfl
      rw [ha, map_zpow, map_zpow]
      exact congrArg (· ^ k) h
  exact isCyclic_of_injective (ev.comp (kummerExtensionGalEquiv K n Ω Δ).toMonoidHom)
    (hev.comp (kummerExtensionGalEquiv K n Ω Δ).injective)

end Kummer

universe u

variable {K : Type u} [Field K] [NumberField K]

theorem FirstInequality.exists_pow_eq_of_forall_pow_eq (hFI : FirstInequality.{u}) {n : ℕ}
    [NeZero n] [HasEnoughRootsOfUnity K n] (S : Set (HeightOneSpectrum (𝓞 K)))
    (hS : ∀ v : HeightOneSpectrum (𝓞 K), (n : 𝓞 K) ∈ v.asIdeal → v ∈ S)
    (hJ : (IdeleGroup.diagonal K).range ⊔ IdeleGroup.sIdeles S = ⊤) {y : Kˣ} (hy : y ∈ S.unit K)
    (hfin : ∀ v ∈ S, ∃ x : v.adicCompletion K, x ^ n = algebraMap K _ (y : K))
    (hinf : ∀ w : InfinitePlace K, ∃ x : w.Completion, x ^ n = algebraMap K _ (y : K)) :
    ∃ z : K, z ^ n = y := by
  set Δ := Subgroup.zpowers y
  set M := kummerExtension K n (AlgebraicClosure K) Δ
  obtain ⟨α, hα⟩ := IsAlgClosed.exists_pow_nat_eq (algebraMap K (AlgebraicClosure K) (y : K))
    (NeZero.pos n)
  let α' : M := ⟨α, subset_adjoin _ _ ⟨y, Subgroup.mem_zpowers y, hα⟩⟩
  have hα' : α' ^ n = algebraMap K M (y : K) := kummerExtension_pow_eq hα
  have hgen : adjoin K {α'} = ⊤ := adjoin_eq_top_of_pow_eq α' hα'

  have hnorm : IdeleGroup.sIdeles S ≤ (ideleNorm K M).range := by
    intro x hx
    refine mem_range_ideleNorm_of_forall x (fun v ↦ ?_) (fun w ↦ ?_)
    · by_cases hv : v ∈ S
      · rw [range_finiteLocalNorm_eq_top_of_isFiniteSplit v ((splitsCompletely_iff_isFiniteSplit v).1
          ((splitsCompletely_kummerExtension_iff v).2
            (forall_mem_zpowers_exists_pow_eq (hfin v hv))))]
        exact Subgroup.mem_top _
      · obtain ⟨w⟩ := nonempty_placesOver M v
        have he : w.1.asIdeal.ramificationIdx (𝓞 K) = 1 :=
          Kummer.ramificationIdx_eq_one_of_pow_eq y hα' hgen v (fun h ↦ hv (hS v h))
            (by rw [hy v hv, WithZero.log_one]; exact dvd_zero _) w.1.asIdeal
        have hu : IdeleGroup.finiteProj v x ∈
            (Submonoid.ofClass (v.adicCompletionIntegers K)).units := by
          have h := (IdeleGroup.mem_sIdeles_iff S).1 hx v hv
          rw [Submonoid.mem_units_iff, ← map_inv, IdeleGroup.coe_finiteProj,
            IdeleGroup.coe_finiteProj]
          exact ⟨h.1, h.2⟩
        rw [← map_integerUnitsOver_eq_of_ramificationIdx_eq_one v w he] at hu
        obtain ⟨z, -, hz⟩ := hu
        exact ⟨z, hz⟩
    · rw [range_infiniteLocalNorm_eq_top_of_splitsCompletely w
        ((InfinitePlace.splitsCompletely_kummerExtension_iff w).2
          (forall_mem_zpowers_exists_pow_eq (hinf w)))]
      exact Subgroup.mem_top _
  have htop : (ideleNorm K M).range ⊔ (IdeleGroup.diagonal K).range = ⊤ := by
    rw [eq_top_iff, ← hJ]
    exact sup_le le_sup_right (hnorm.trans le_sup_left)
  have := isCyclic_gal_kummerExtension_zpowers (n := n) (Ω := AlgebraicClosure K) y
  have h1 := hFI.finrank_eq_one_of_sup_eq_top htop
  rw [finrank_kummerExtension] at h1
  have hsub : Subsingleton (Δ ⧸ (unitsPow K n).subgroupOf Δ) :=
    (Nat.card_eq_one_iff_unique.1 h1).1
  have hyΔ : (⟨y, Subgroup.mem_zpowers y⟩ : Δ) ∈ (unitsPow K n).subgroupOf Δ := by
    rw [← QuotientGroup.eq_one_iff]
    exact Subsingleton.elim _ _
  obtain ⟨z, hz⟩ := mem_unitsPow.1 (Subgroup.mem_subgroupOf.1 hyΔ)
  exact ⟨z, by rw [← Units.val_pow_eq_pow_val, hz]⟩

end

end GroundTheory.Global
