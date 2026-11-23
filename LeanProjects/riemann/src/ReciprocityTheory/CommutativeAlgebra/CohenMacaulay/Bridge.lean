import ReciprocityTheory.CommutativeAlgebra.CohenMacaulay.ModDepthGE

namespace ReciprocityTheory.CA

open IsLocalRing RingTheory.Sequence

variable {R : Type*} [CommRing R] [IsLocalRing R]

theorem isCM_iff_isCMMod : IsCM R ↔ IsCMMod R R := by
  have hd : Module.supportDim R R = ringKrullDim R := Module.supportDim_self_eq_ringKrullDim R
  constructor
  · rintro ⟨h1, n, hn, h2⟩
    exact ⟨h1, Module.Finite.self R, n, hd.trans hn, h2⟩
  · rintro ⟨h1, -, n, hn, h2⟩
    exact ⟨h1, n, hd.symm.trans hn, h2⟩

theorem modDepthGE_congr {M N : Type*} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (e : M ≃ₗ[R] N) (n : ℕ) : ModDepthGE R M n ↔ ModDepthGE R N n := by
  constructor
  · rintro ⟨rs, h1, h2, h3⟩
    exact ⟨rs, h1, h2, (e.isRegular_congr rs).mp h3⟩
  · rintro ⟨rs, h1, h2, h3⟩
    exact ⟨rs, h1, h2, (e.isRegular_congr rs).mpr h3⟩

theorem isCMMod_congr {M N : Type*} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (e : M ≃ₗ[R] N) : IsCMMod R M ↔ IsCMMod R N := by
  have hs : Module.support R M = Module.support R N :=
    (Module.support_subset_of_injective e.toLinearMap e.injective).antisymm
      (Module.support_subset_of_surjective e.toLinearMap e.surjective)
  have hd : Module.supportDim R M = Module.supportDim R N := by
    unfold Module.supportDim
    rw [hs]
  constructor
  · rintro ⟨h1, h2, n, hn, h3⟩
    exact ⟨h1, Module.Finite.equiv e, n, hd.symm.trans hn, (modDepthGE_congr e n).mp h3⟩
  · rintro ⟨h1, h2, n, hn, h3⟩
    exact ⟨h1, Module.Finite.equiv e.symm, n, hd.trans hn, (modDepthGE_congr e n).mpr h3⟩

lemma isRegular_map_algebraMap_iff' {S M : Type*} [CommRing S] [Algebra R S] [AddCommGroup M]
    [Module R M] [Module S M] [IsScalarTower R S M] (rs : List R) :
    IsRegular M (rs.map (algebraMap R S)) ↔ IsRegular M rs := by
  open Pointwise in
  have key : ∀ l : List R,
      ((Ideal.ofList (l.map (algebraMap R S))) • (⊤ : Submodule S M)).restrictScalars R
        = Ideal.ofList l • (⊤ : Submodule R M) := by
    intro l
    induction l with
    | nil => simp
    | cons r l ih =>
      have ih' : ∀ y : M, y ∈ (Ideal.ofList (l.map (algebraMap R S))) • (⊤ : Submodule S M) ↔
          y ∈ Ideal.ofList l • (⊤ : Submodule R M) :=
        fun y => by rw [← ih, Submodule.restrictScalars_mem]
      have hr : ∀ y : M, y ∈ (algebraMap R S r) • (⊤ : Submodule S M) ↔
          y ∈ r • (⊤ : Submodule R M) := fun y => by
        simp [Submodule.mem_smul_pointwise_iff_exists, algebraMap_smul]
      ext m
      simp only [List.map_cons, Ideal.ofList_cons, Submodule.sup_smul,
        Submodule.ideal_span_singleton_smul, Submodule.restrictScalars_mem, Submodule.mem_sup, ih', hr]
  rw [RingTheory.Sequence.isRegular_iff, RingTheory.Sequence.isRegular_iff,
    RingTheory.Sequence.isWeaklyRegular_map_algebraMap_iff]
  refine and_congr_right fun _ => ?_
  constructor
  · intro h h'
    apply h
    apply Submodule.restrictScalars_injective R S M
    rw [key, Submodule.restrictScalars_top]
    exact h'
  · intro h h'
    apply h
    rw [← key, ← h', Submodule.restrictScalars_top]

lemma mk_mem_maximalIdeal_quot (I : Ideal R) [IsLocalRing (R ⧸ I)] {r : R}
    (hr : r ∈ maximalIdeal R) : Ideal.Quotient.mk I r ∈ maximalIdeal (R ⧸ I) := by
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
  intro hu
  obtain ⟨v, hv⟩ := hu.exists_right_inv
  obtain ⟨s, rfl⟩ := Ideal.Quotient.mk_surjective v
  have h1 : r * s - 1 ∈ I := by
    rw [← Ideal.Quotient.eq, map_mul, hv, map_one]
  have h2 : r * s - 1 ∉ maximalIdeal R := by
    intro h
    have h' : r * s - (r * s - 1) ∈ maximalIdeal R :=
      (maximalIdeal R).sub_mem ((maximalIdeal R).mul_mem_right s hr) h
    rw [sub_sub_cancel] at h'
    exact (Ideal.ne_top_iff_one _).mp (Ideal.IsMaximal.ne_top inferInstance) h'
  have h3 : IsUnit (r * s - 1) := by
    by_contra h
    exact h2 ((IsLocalRing.mem_maximalIdeal _).mpr h)
  have h4 : IsUnit (Ideal.Quotient.mk I (r * s - 1)) := h3.map _
  rw [Ideal.Quotient.eq_zero_iff_mem.mpr h1] at h4
  exact not_isUnit_zero h4

theorem depthGE_quotient_iff (I : Ideal R) [IsLocalRing (R ⧸ I)] (n : ℕ) :
    DepthGE (R ⧸ I) n ↔ ModDepthGE R (R ⧸ I) n := by
  have key : ∀ rs : List R, RingTheory.Sequence.IsRegular (R ⧸ I) (rs.map (Ideal.Quotient.mk I)) ↔
      RingTheory.Sequence.IsRegular (R ⧸ I) rs := fun rs => by
    have := isRegular_map_algebraMap_iff' (S := R ⧸ I) (M := R ⧸ I) rs
    rwa [Ideal.Quotient.algebraMap_eq] at this
  have hs : Function.Surjective (Ideal.Quotient.mk I) := Ideal.Quotient.mk_surjective
  constructor
  · rintro ⟨rs, hlen, hmem, hreg⟩
    refine ⟨rs.map (Function.surjInv hs), by simp [hlen], ?_, ?_⟩
    · intro x hx
      obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx
      have hy' := hmem y hy
      rw [← Function.surjInv_eq hs y] at hy'
      rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] at hy' ⊢
      exact fun hu => hy' (hu.map _)
    · have hl : (rs.map (Function.surjInv hs)).map (Ideal.Quotient.mk I) = rs := by
        simp [Function.comp_def, Function.surjInv_eq hs]
      rw [← key, hl]
      exact hreg
  · rintro ⟨rs, hlen, hmem, hreg⟩
    refine ⟨rs.map (Ideal.Quotient.mk I), by simp [hlen], ?_, (key rs).mpr hreg⟩
    intro x hx
    obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx
    exact mk_mem_maximalIdeal_quot I (hmem y hy)

theorem isCM_quotient_iff [IsNoetherianRing R] (I : Ideal R) [IsLocalRing (R ⧸ I)] :
    IsCM (R ⧸ I) ↔ IsCMMod R (R ⧸ I) := by
  have hfin : Module.Finite R (R ⧸ I) :=
    Module.Finite.of_surjective (Submodule.mkQ I) (Submodule.mkQ_surjective I)
  have hd : Module.supportDim R (R ⧸ I) = ringKrullDim (R ⧸ I) := by
    rw [Module.supportDim_eq_ringKrullDim_quotient_annihilator, Ideal.annihilator_quotient]
  constructor
  · rintro ⟨-, n, hn, h⟩
    exact ⟨inferInstance, hfin, n, hd.trans hn, (depthGE_quotient_iff I n).mp h⟩
  · rintro ⟨-, -, n, hn, h⟩
    exact ⟨inferInstance, n, hd.symm.trans hn, (depthGE_quotient_iff I n).mpr h⟩

theorem DepthGE.of_ringEquiv {S : Type*} [CommRing S] [IsLocalRing S] (e : R ≃+* S) {n : ℕ}
    (h : DepthGE R n) : DepthGE S n := by
  obtain ⟨rs, hlen, hmem, hreg⟩ := h
  refine ⟨rs.map (e : R →+* S), by simp [hlen], ?_, ?_⟩
  · intro x hx
    obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx
    have hy' := hmem y hy
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] at hy' ⊢
    intro hu
    apply hy'
    simpa using hu.map (e.symm : S →+* R)
  · haveI h1 : RingHomInvPair (e : R →+* S) (e.symm : S →+* R) := ⟨by ext; simp, by ext; simp⟩
    have h2 : RingHomInvPair (e.symm : S →+* R) (e : R →+* S) := ⟨by ext; simp, by ext; simp⟩
    exact (LinearEquiv.isRegular_congr' (σ' := (e.symm : S →+* R)) e.toSemilinearEquiv rs).mp hreg

theorem IsCM.of_ringEquiv {S : Type*} [CommRing S] [IsLocalRing S] (e : R ≃+* S)
    (h : IsCM R) : IsCM S := by
  obtain ⟨hN, n, hn, hd⟩ := h
  exact ⟨isNoetherianRing_of_ringEquiv R e, n, (ringKrullDim_eq_of_ringEquiv e).symm.trans hn,
    hd.of_ringEquiv e⟩

end ReciprocityTheory.CA
