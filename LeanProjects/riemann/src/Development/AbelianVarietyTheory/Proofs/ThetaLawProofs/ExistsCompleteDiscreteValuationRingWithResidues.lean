import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RangeAlgebraMapEqIInfDiscreteValuationSubring

open IsLocalRing Polynomial

namespace GlobalTheory

namespace ResidueExtension

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {Ω : Type} [Field Ω]

theorem injective_of_map_ne_zero {B : Type} [CommRing B] [IsDomain B] (j : O →+* B) {π : O}
    (hπ : Irreducible π) (h : j π ≠ 0) : Function.Injective j := by
  rw [injective_iff_map_eq_zero]
  intro x hx
  by_contra h0
  obtain ⟨n, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible h0 hπ
  rw [map_mul, map_pow] at hx
  exact mul_ne_zero (u.isUnit.map j).ne_zero (pow_ne_zero n h) hx

theorem exists_localization {A : Type} [CommRing A] [IsNoetherianRing A] (i : O →+* A)
    (ψ : A →+* Ω) {π : O} (hπ : Irreducible π) (hker : RingHom.ker ψ = Ideal.span {i π})
    (hreg : ∀ x, i π * x = 0 → x = 0) :
    ∃ (B : Type) (_ : CommRing B) (_ : IsDomain B) (_ : IsDiscreteValuationRing B)
      (j : O →+* B) (r' : B →+* Ω), Function.Injective j ∧ r'.comp j = ψ.comp i ∧
      RingHom.ker r' = maximalIdeal B ∧ Set.range ψ ⊆ Set.range r' := by
  have hp : (RingHom.ker ψ).IsPrime := RingHom.ker_isPrime ψ
  let B := Localization.AtPrime (RingHom.ker ψ)
  have hu : ∀ y : (RingHom.ker ψ).primeCompl, IsUnit (ψ y) := fun y =>
    isUnit_iff_ne_zero.mpr y.2
  let r' : B →+* Ω := IsLocalization.lift hu
  have hr' : ∀ x, r' (algebraMap A B x) = ψ x := fun x => IsLocalization.lift_eq hu x
  have hmax : maximalIdeal B = Ideal.span {algebraMap A B (i π)} := by
    rw [← Localization.AtPrime.map_eq_maximalIdeal]
    conv_lhs => enter [2]; rw [hker]
    rw [Ideal.map_span, Set.image_singleton]
  have hpow : ∀ (n : ℕ) x, i π ^ n * x = 0 → x = 0 := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      intro x hx
      rw [pow_succ, mul_assoc] at hx
      exact hreg x (ih _ hx)
  have hn : ¬ IsNilpotent (algebraMap A B (i π)) := by
    rintro ⟨n, hn⟩
    rw [← map_pow, IsLocalization.map_eq_zero_iff (RingHom.ker ψ).primeCompl] at hn
    obtain ⟨m, hm⟩ := hn
    have := hpow n m (by rw [mul_comm]; exact hm)
    exact m.2 (this ▸ zero_mem _)
  obtain ⟨hd, hdvr, hirr⟩ := isDiscreteValuationRing_of_maximalIdeal_eq_span hmax hn
  refine ⟨B, inferInstance, hd, hdvr, (algebraMap A B).comp i, r',
    injective_of_map_ne_zero _ hπ hirr.ne_zero, RingHom.ext fun x => hr' _, ?_, ?_⟩
  · refine ((maximalIdeal.isMaximal B).eq_of_le (RingHom.ker_ne_top r') ?_).symm
    rw [hmax, Ideal.span_singleton_le_iff_mem, RingHom.mem_ker, hr', ← RingHom.mem_ker, hker]
    exact Ideal.mem_span_singleton_self _
  · rintro _ ⟨x, rfl⟩
    exact ⟨_, hr' x⟩

theorem exists_generator (r : O →+* Ω) (hr : RingHom.ker r = maximalIdeal O) (a : Ω) {π : O}
    (hπ : Irreducible π) :
    ∃ G : O[X], (G.Monic ∨ G = 0) ∧ G.eval₂ r a = 0 ∧
      ∀ f : O[X], f.eval₂ r a = 0 → ∃ g h, f = G * g + C π * h := by
  let rb : ResidueField O →+* Ω :=
    Ideal.Quotient.lift (maximalIdeal O) r fun x hx => by rwa [← hr] at hx
  let _ : Algebra (ResidueField O) Ω := rb.toAlgebra
  have hev : ∀ f : O[X], aeval a (f.map (residue O)) = f.eval₂ r a := by
    intro f
    rw [aeval_def, eval₂_map]
    rfl
  obtain ⟨G, hG, hG'⟩ : ∃ G : O[X], (G.Monic ∨ G = 0) ∧
      G.map (residue O) = minpoly (ResidueField O) a := by
    by_cases h : IsIntegral (ResidueField O) a
    · obtain ⟨G, h1, -, h2⟩ := lifts_and_degree_eq_and_monic
        ((mem_lifts _).mpr (map_surjective (residue O) residue_surjective _)) (minpoly.monic h)
      exact ⟨G, Or.inl h2, h1⟩
    · exact ⟨0, Or.inr rfl, by rw [minpoly.eq_zero h, Polynomial.map_zero]⟩
  refine ⟨G, hG, by rw [← hev, hG', minpoly.aeval], fun f hf => ?_⟩
  rw [← hev] at hf
  obtain ⟨g', hg'⟩ := minpoly.dvd _ _ hf
  obtain ⟨g, rfl⟩ := map_surjective (residue O) residue_surjective g'
  have h1 : f - G * g ∈ RingHom.ker (mapRingHom (residue O)) := by
    rw [RingHom.mem_ker, coe_mapRingHom, Polynomial.map_sub, Polynomial.map_mul, hG', hg', sub_self]
  rw [ker_mapRingHom, ker_residue, hπ.maximalIdeal_eq, Ideal.map_span, Set.image_singleton,
    Ideal.mem_span_singleton] at h1
  obtain ⟨h, hh⟩ := h1
  exact ⟨g, h, by rw [← hh]; ring⟩

theorem exists_step (r : O →+* Ω) (hr : RingHom.ker r = maximalIdeal O) (a : Ω) :
    ∃ (B : Type) (_ : CommRing B) (_ : IsDomain B) (_ : IsDiscreteValuationRing B)
      (j : O →+* B) (r' : B →+* Ω), Function.Injective j ∧ r'.comp j = r ∧
      RingHom.ker r' = maximalIdeal B ∧ a ∈ Set.range r' := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible O
  obtain ⟨G, hG, h0, hgen⟩ := exists_generator r hr a hπ
  have hrπ : r π = 0 := by
    rw [← RingHom.mem_ker, hr, hπ.maximalIdeal_eq]
    exact Ideal.mem_span_singleton_self _
  have hk : RingHom.ker (AdjoinRoot.lift r a h0) = Ideal.span {AdjoinRoot.of G π} := by
    apply le_antisymm
    · intro x hx
      obtain ⟨f, rfl⟩ := AdjoinRoot.mk_surjective x
      rw [RingHom.mem_ker, AdjoinRoot.lift_mk] at hx
      obtain ⟨g, h, rfl⟩ := hgen f hx
      rw [map_add, map_mul, AdjoinRoot.mk_self, zero_mul, zero_add, map_mul, AdjoinRoot.mk_C]
      exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)
    · rw [Ideal.span_singleton_le_iff_mem, RingHom.mem_ker, AdjoinRoot.lift_of, hrπ]
  have hreg : ∀ x, AdjoinRoot.of G π * x = 0 → x = 0 := by
    intro x hx
    obtain ⟨f, rfl⟩ := AdjoinRoot.mk_surjective x
    rw [← AdjoinRoot.mk_C, ← map_mul, AdjoinRoot.mk_eq_zero] at hx
    rw [AdjoinRoot.mk_eq_zero]
    rcases hG with hG | rfl
    · rw [← modByMonic_eq_zero_iff_dvd hG] at hx ⊢
      rw [← smul_eq_C_mul, smul_modByMonic] at hx
      exact (smul_eq_zero.mp hx).resolve_left hπ.ne_zero
    · rw [zero_dvd_iff] at hx ⊢
      exact (mul_eq_zero.mp hx).resolve_left (C_ne_zero.mpr hπ.ne_zero)
  obtain ⟨B, _, _, _, j, r', h1, h2, h3, h4⟩ := exists_localization (AdjoinRoot.of G)
    (AdjoinRoot.lift r a h0) hπ hk hreg
  exact ⟨B, _, ‹_›, ‹_›, j, r', h1, h2.trans (AdjoinRoot.lift_comp_of h0), h3,
    h4 ⟨_, AdjoinRoot.lift_root h0⟩⟩

theorem exists_finset (r : O →+* Ω) (hr : RingHom.ker r = maximalIdeal O) (S : Finset Ω) :
    ∃ (B : Type) (_ : CommRing B) (_ : IsDomain B) (_ : IsDiscreteValuationRing B)
      (j : O →+* B) (r' : B →+* Ω), Function.Injective j ∧ r'.comp j = r ∧
      RingHom.ker r' = maximalIdeal B ∧ ∀ a ∈ S, a ∈ Set.range r' := by
  classical
  induction S using Finset.induction_on with
  | empty => exact ⟨O, _, ‹_›, ‹_›, RingHom.id O, r, Function.injective_id, rfl, hr, by simp⟩
  | insert a S _ ih =>
    obtain ⟨B, _, _, _, j, r', h1, h2, h3, h4⟩ := ih
    obtain ⟨B', _, _, _, j', r'', h1', h2', h3', h4'⟩ := exists_step r' h3 a
    refine ⟨B', _, ‹_›, ‹_›, j'.comp j, r'', h1'.comp h1,
      by rw [← RingHom.comp_assoc, h2', h2], h3', fun b hb => ?_⟩
    rcases Finset.mem_insert.mp hb with rfl | hb
    · exact h4'
    · obtain ⟨y, rfl⟩ := h4 b hb
      exact ⟨j' y, RingHom.congr_fun h2' y⟩

theorem exists_completion (r : O →+* Ω) (hr : RingHom.ker r = maximalIdeal O) :
    ∃ r' : AdicCompletion (maximalIdeal O) O →+* Ω,
      r'.comp (algebraMap O _) = r ∧ RingHom.ker r' = maximalIdeal _ := by
  let rb : ResidueField O →+* Ω :=
    Ideal.Quotient.lift (maximalIdeal O) r fun x hx => by rwa [← hr] at hx
  let e := RingEquiv.ofBijective _ (AdicCompletion.residueField_map_bijective O)
  refine ⟨(rb.comp e.symm.toRingHom).comp (residue _), RingHom.ext fun x => ?_, ?_⟩
  · have : e.symm (residue _ (algebraMap O _ x)) = residue O x := by
      rw [RingEquiv.symm_apply_eq]
      rfl
    change rb (e.symm (residue _ (algebraMap O _ x))) = r x
    rw [this]
    rfl
  · rw [RingHom.ker_comp_of_injective _ (RingHom.injective _), ker_residue]

end ResidueExtension

theorem exists_complete_discreteValuationRing_with_residues :
    ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (Ω : Type) [Field Ω]
      (r : O →+* Ω) (S : Finset Ω), RingHom.ker r = IsLocalRing.maximalIdeal O →
      ∃ (O' : Type) (_ : CommRing O') (_ : IsDomain O') (_ : IsDiscreteValuationRing O')
        (j : O →+* O') (r' : O' →+* Ω), IsAdicComplete (IsLocalRing.maximalIdeal O') O' ∧
        Function.Injective j ∧ IsLocalHom j ∧ r'.comp j = r ∧
        RingHom.ker r' = IsLocalRing.maximalIdeal O' ∧ ∀ a ∈ S, a ∈ Set.range r' := by
  intro O _ _ _ Ω _ r S hr
  obtain ⟨B, _, _, _, j, r', h1, h2, h3, h4⟩ := ResidueExtension.exists_finset r hr S
  obtain ⟨r'', h5, h6⟩ := ResidueExtension.exists_completion r' h3
  have h7 : r''.comp ((algebraMap B (AdicCompletion (maximalIdeal B) B)).comp j) = r := by
    rw [← RingHom.comp_assoc, h5, h2]
  refine ⟨AdicCompletion (maximalIdeal B) B, inferInstance, inferInstance, inferInstance,
    (algebraMap B _).comp j, r'', inferInstance,
    (algebraMap_adicCompletion_injective_of_dvr B).comp h1, ⟨fun x hx => ?_⟩, h7, h6,
    fun a ha => ?_⟩
  · rw [← notMem_maximalIdeal, ← hr, RingHom.mem_ker, ← h7]
    exact (hx.map r'').ne_zero
  · obtain ⟨y, rfl⟩ := h4 a ha
    exact ⟨_, RingHom.congr_fun h5 y⟩

end GlobalTheory
