import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.PoitouTateNineTermTransgressionZeroApply
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.ContinuousCycMod
import Formalism.GaloisCohomology.Statement

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.Published GlobalTheory.Published.PoitouTate

namespace GlobalTheory

theorem exists_addHom_zmod_pow_extend (O : Type) [CommRing O] (l n : ℕ) [Fact l.Prime]
    (hinj : Function.Injective (fun o : O => (l : O) ^ n * o)) (β : O →+ ZMod (l ^ 1)) :
    ∃ A : O →+ ZMod (l ^ (n + 1)), ∀ o : O,
      A ((l : O) ^ n * o) = ((l ^ n * (β o).val : ℕ) : ZMod (l ^ (n + 1))) := by
  classical
  have hl0 : l ≠ 0 := (Fact.out : l.Prime).ne_zero
  have : NeZero (l ^ (n + 1)) := ⟨pow_ne_zero _ hl0⟩
  have : NeZero (l ^ 1) := ⟨pow_ne_zero _ hl0⟩

  have hcong : ∀ x : ℕ, ((l ^ n * (x % l ^ 1) : ℕ) : ZMod (l ^ (n + 1)))
      = ((l ^ n * x : ℕ) : ZMod (l ^ (n + 1))) := by
    intro x
    rw [ZMod.natCast_eq_natCast_iff, pow_one, pow_succ]
    exact Nat.ModEq.mul_left' _ (Nat.mod_modEq x l)
  let g : O →+ ZMod (l ^ (n + 1)) :=
    { toFun := fun o => ((l ^ n * (β o).val : ℕ) : ZMod (l ^ (n + 1)))
      map_zero' := by simp
      map_add' := by
        intro a b
        rw [map_add, ZMod.val_add, hcong, mul_add, Nat.cast_add] }

  obtain ⟨h, hh⟩ := (Module.Baer.of_divisible UnitAddCircle).extension_property_addMonoidHom
    (AddMonoidHom.mulLeft ((l : O) ^ n)) hinj ((ZMod.toAddCircle).comp g)
  have hh' : ∀ o, h ((l : O) ^ n * o) = ZMod.toAddCircle (g o) := fun o =>
    DFunLike.congr_fun hh o

  have htors : ∀ o, (l ^ (n + 1)) • h o = 0 := by
    intro o
    have hlo : β ((l : O) * o) = 0 := by
      have hz : ((l : ℕ) : ZMod (l ^ 1)) = 0 := (ZMod.natCast_eq_zero_iff _ _).mpr (by rw [pow_one])
      rw [← nsmul_eq_mul, map_nsmul, nsmul_eq_mul, hz, zero_mul]
    rw [← map_nsmul, nsmul_eq_mul, Nat.cast_pow, pow_succ, mul_assoc, hh']
    simp [g, hlo]

  have hdesc : ∀ o, ∃ k : ZMod (l ^ (n + 1)), ZMod.toAddCircle k = h o := by
    intro o
    have ht := htors o
    obtain ⟨x, hx⟩ := QuotientAddGroup.mk_surjective (h o)
    rw [← hx] at ht ⊢
    rw [← QuotientAddGroup.mk_nsmul, AddCircle.coe_eq_zero_iff] at ht
    obtain ⟨m, hm⟩ := ht
    refine ⟨(m : ZMod (l ^ (n + 1))), ?_⟩
    rw [ZMod.toAddCircle_intCast]
    congr 1
    have hN : ((l ^ (n + 1) : ℕ) : ℝ) ≠ 0 := by exact_mod_cast pow_ne_zero _ hl0
    rw [zsmul_eq_mul, mul_one, nsmul_eq_mul] at hm
    rw [hm, mul_div_cancel_left₀ _ hN]
  choose A hA using hdesc
  have hAadd : ∀ a b, A (a + b) = A a + A b := by
    intro a b
    apply ZMod.toAddCircle_injective (l ^ (n + 1))
    rw [map_add, hA, hA, hA, map_add]
  refine ⟨⟨⟨A, ?_⟩, hAadd⟩, ?_⟩
  · apply ZMod.toAddCircle_injective (l ^ (n + 1))
    rw [hA, map_zero, map_zero]
  · intro o
    apply ZMod.toAddCircle_injective (l ^ (n + 1))
    show ZMod.toAddCircle (A _) = _
    rw [hA, hh']
    rfl

theorem addHom_zmod_pow_algebraMap_mul (O : Type) [CommRing O] (l m : ℕ) [Fact l.Prime]
    [Algebra ℤ_[l] O] (A : O →+ ZMod (l ^ m)) (u : ℤ_[l]) (o : O) :
    A (algebraMap ℤ_[l] O u * o) = PadicInt.toZModPow m u * A o := by
  set v : ℕ := (PadicInt.toZModPow m u).val with hv

  have hk : u - (v : ℤ_[l]) ∈ RingHom.ker (PadicInt.toZModPow m : ℤ_[l] →+* ZMod (l ^ m)) := by
    rw [RingHom.mem_ker, map_sub, map_natCast, hv, ZMod.natCast_zmod_val, sub_self]
  rw [PadicInt.ker_toZModPow, Ideal.mem_span_singleton'] at hk
  obtain ⟨w, hw⟩ := hk
  have hu : u = (v : ℤ_[l]) + w * (l : ℤ_[l]) ^ m := by rw [hw]; ring
  have hkill : ∀ x : O, A ((l : O) ^ m * x) = 0 := by
    intro x
    rw [← Nat.cast_pow, ← nsmul_eq_mul, map_nsmul, nsmul_eq_mul, ZMod.natCast_self, zero_mul]
  have hsplit : algebraMap ℤ_[l] O u * o
      = v • o + (l : O) ^ m * (algebraMap ℤ_[l] O w * o) := by
    rw [hu, map_add, map_mul, map_pow, map_natCast, map_natCast, nsmul_eq_mul]
    ring
  rw [hsplit, map_add, hkill, add_zero, map_nsmul, nsmul_eq_mul, hv, ZMod.natCast_zmod_val]

theorem exists_zmod_pow_coboundary_of_rational_coboundary :
    ∀ (Γ : Type) [Group Γ] [TopologicalSpace Γ] [CompactSpace Γ] (l : ℕ) [Fact l.Prime] (ε : Γ → ℤ_[l]) (O L : Type) [CommRing O] [Algebra ℤ_[l] O] [Field L] [TopologicalSpace L] [IsTopologicalRing L] (ι : O →+* L), Function.Injective ι → IsOpen (Set.range ι) → (l : L) ≠ 0 → (∀ x : L, ∃ n : ℕ, (l : L) ^ n * x ∈ Set.range ι) → ∀ (β : O →+ ZMod (l ^ 1)) (z : Γ → Γ → O) (f : Γ → L), Continuous f → (∀ g h, ι (z g h) = ι (algebraMap ℤ_[l] O (ε g)) * f h - f (g * h) + f g) → ∃ (n : ℕ) (a : Γ → ZMod (l ^ (n + 1))), Continuous a ∧ ∀ g h, PadicInt.toZModPow (n + 1) (ε g) * a h - a (g * h) + a g = ((l ^ n * (β (z g h)).val : ℕ) : ZMod (l ^ (n + 1))) := by
  intro Γ _ _ _ l _ ε O L _ _ _ _ _ ι hι hopen hl hcov β z f hf hz

  have hstep : ∀ k x, (l : L) ^ k * x ∈ Set.range ι → (l : L) ^ (k + 1) * x ∈ Set.range ι := by
    rintro k x ⟨o, ho⟩
    exact ⟨(l : O) * o, by rw [map_mul, map_natCast, ho, pow_succ]; ring⟩
  have hmono : Monotone (fun k : ℕ => {x : L | (l : L) ^ k * x ∈ Set.range ι}) :=
    monotone_nat_of_le_succ (fun k x hx => hstep k x hx)
  obtain ⟨N, hN⟩ := (isCompact_range hf).elim_directed_cover
    (fun k : ℕ => {x : L | (l : L) ^ k * x ∈ Set.range ι})
    (fun k => hopen.preimage (continuous_const.mul continuous_id))
    (fun x _ => Set.mem_iUnion.mpr (hcov x)) hmono.directed_le
  have hN' : ∀ g, ∃ o : O, ι o = (l : L) ^ N * f g := fun g => hN ⟨g, rfl⟩
  choose F hF using hN'
  have hlN : ∀ k, (l : L) ^ k ≠ 0 := fun k => pow_ne_zero _ hl
  have hinjO : Function.Injective (fun o : O => (l : O) ^ N * o) := by
    intro a b hab
    apply hι
    have := congrArg ι hab
    simp only [map_mul, map_pow, map_natCast] at this
    exact mul_left_cancel₀ (hlN N) this
  obtain ⟨A, hA⟩ := exists_addHom_zmod_pow_extend O l N hinjO β

  have hrel : ∀ g h, (l : O) ^ N * z g h
      = algebraMap ℤ_[l] O (ε g) * F h - F (g * h) + F g := by
    intro g h
    apply hι
    rw [map_mul, map_pow, map_natCast, hz, map_add, map_sub, map_mul, hF, hF, hF]
    ring
  have hkill : ∀ x : O, A ((l : O) ^ (N + 1) * x) = 0 := by
    intro x
    rw [← Nat.cast_pow, ← nsmul_eq_mul, map_nsmul, nsmul_eq_mul, ZMod.natCast_self, zero_mul]
  refine ⟨N, fun g => A (F g), ?_, ?_⟩
  ·
    refine ((IsLocallyConstant.iff_eventually_eq _).mpr fun g₁ => ?_).continuous
    have hPo : IsOpen {g : Γ | ((l : L) ^ (N + 1))⁻¹ * ((l : L) ^ N * f g - (l : L) ^ N * f g₁)
        ∈ Set.range ι} :=
      hopen.preimage (continuous_const.mul ((continuous_const.mul hf).sub continuous_const))
    have hmem : g₁ ∈ {g : Γ | ((l : L) ^ (N + 1))⁻¹ * ((l : L) ^ N * f g - (l : L) ^ N * f g₁)
        ∈ Set.range ι} := ⟨0, by simp⟩
    filter_upwards [hPo.mem_nhds hmem] with g hg
    obtain ⟨o, ho⟩ := hg
    have hFg : F g = F g₁ + (l : O) ^ (N + 1) * o := by
      apply hι
      rw [map_add, map_mul, map_pow, map_natCast, ho, mul_inv_cancel_left₀ (hlN _), hF, hF]
      ring
    show A (F g) = A (F g₁)
    rw [hFg, map_add, hkill, add_zero]
  · intro g h
    rw [← addHom_zmod_pow_algebraMap_mul O l (N + 1) A (ε g) (F h), ← map_sub, ← map_add,
      ← hrel, hA]

end GlobalTheory
