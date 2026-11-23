import Development.EtaleCohomology.EtaleSheaves.LeafTensQIsoPf

open TensorProduct

namespace LateralTheory.E.LeafZModInjFlatPf

universe v

theorem flat_of_injective_of_ann {R : Type v} [CommRing R] [IsPrincipalIdealRing R]
    (hP : ∀ a : R, ∃ b : R, b * a = 0 ∧ ∀ r : R, r * b = 0 → ∃ s : R, r = s * a)
    (M : Type v) [AddCommGroup M] [Module R M] (hM : Module.Injective R M) :
    Module.Flat R M := by
  rw [Module.Flat.iff_lift_lsmul_comp_subtype_injective]
  intro I _
  obtain ⟨a, rfl⟩ : ∃ a : R, I = Ideal.span {a} :=
    ⟨_, (Ideal.span_singleton_generator I).symm⟩
  have ha : a ∈ Ideal.span ({a} : Set R) := Ideal.mem_span_singleton_self a
  have key : ∀ x : Ideal.span ({a} : Set R) ⊗[R] M, ∃ m : M, x = (⟨a, ha⟩ : Ideal.span ({a} : Set R)) ⊗ₜ m := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => exact ⟨0, by simp⟩
    | tmul i n =>
      obtain ⟨s, hs⟩ := Ideal.mem_span_singleton'.1 i.2
      refine ⟨s • n, ?_⟩
      rw [← smul_tmul]
      congr 1
      ext
      simp [smul_eq_mul, hs]
    | add x y hx hy =>
      obtain ⟨m1, rfl⟩ := hx
      obtain ⟨m2, rfl⟩ := hy
      exact ⟨m1 + m2, (tmul_add _ _ _).symm⟩
  rw [injective_iff_map_eq_zero]
  intro x hx
  obtain ⟨m, rfl⟩ := key x
  simp at hx
  obtain ⟨b, hba, hb⟩ := hP a
  have well : ∀ r r' : R, r * b = r' * b → r • m = r' • m := by
    intro r r' h
    obtain ⟨s, hs⟩ := hb (r - r') (by rw [sub_mul, h, sub_self])
    rw [← sub_eq_zero, ← sub_smul, hs, mul_smul, hx, smul_zero]
  let f : Ideal.span ({b} : Set R) → R := fun x => Classical.choose (Ideal.mem_span_singleton'.1 x.2)
  have hf : ∀ x, f x * b = x := fun x => Classical.choose_spec (Ideal.mem_span_singleton'.1 x.2)
  let g : Ideal.span ({b} : Set R) →ₗ[R] M :=
    { toFun := fun x => f x • m
      map_add' := fun x y => by
        rw [← add_smul]; apply well; rw [hf, add_mul, hf, hf]; rfl
      map_smul' := fun c x => by
        rw [RingHom.id_apply, smul_smul]; apply well; rw [hf, mul_assoc, hf]; rfl }
  obtain ⟨g', hg'⟩ := Module.Baer.of_injective hM _ g
  have hm : m = b • g' 1 := by
    rw [← map_smul, smul_eq_mul, mul_one, hg' b (Ideal.mem_span_singleton_self b)]
    show m = f _ • m
    conv_lhs => rw [← one_smul R m]
    apply well; rw [hf, one_mul]
  rw [hm, ← smul_tmul]
  have : b • (⟨a, ha⟩ : Ideal.span ({a} : Set R)) = 0 := by ext; simp [smul_eq_mul, hba]
  rw [this, zero_tmul]

theorem zmod_ann (q : ℕ) [NeZero q] :
    ∀ a : ZMod q, ∃ b : ZMod q, b * a = 0 ∧ ∀ r : ZMod q, r * b = 0 → ∃ s, r = s * a := by
  intro a
  set d := Nat.gcd a.val q with hd
  have hdq : d ∣ q := Nat.gcd_dvd_right _ _
  have hda : d ∣ a.val := Nat.gcd_dvd_left _ _
  have hq0 : q ≠ 0 := NeZero.ne q
  have hd0 : 0 < d := Nat.gcd_pos_of_pos_right _ (Nat.pos_of_ne_zero hq0)
  refine ⟨((q / d : ℕ) : ZMod q), ?_, ?_⟩
  · conv_lhs => rw [← ZMod.natCast_zmod_val a]
    rw [← Nat.cast_mul]
    obtain ⟨t, ht⟩ := hda
    have : q / d * a.val = q * t := by
      rw [ht, ← mul_assoc, Nat.div_mul_cancel hdq]
    rw [this, Nat.cast_mul, ZMod.natCast_self, zero_mul]
  · intro r hr
    rw [← ZMod.natCast_zmod_val r, ← Nat.cast_mul, ZMod.natCast_eq_zero_iff] at hr
    have hqd : 0 < q / d := Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero hq0) hdq) hd0
    have h2 : d * (q / d) ∣ r.val * (q / d) := by rwa [Nat.mul_div_cancel' hdq]
    obtain ⟨t, ht⟩ := Nat.dvd_of_mul_dvd_mul_right hqd h2
    refine ⟨a⁻¹ * t, ?_⟩
    rw [← ZMod.natCast_zmod_val r, ht, Nat.cast_mul, hd, ← ZMod.mul_inv_eq_gcd]
    ring

instance pir_zmod (q : ℕ) : IsPrincipalIdealRing (ZMod q) :=
  IsPrincipalIdealRing.of_surjective (Int.castRingHom (ZMod q)) ZMod.intCast_surjective

instance pir_ulift (q : ℕ) : IsPrincipalIdealRing (ULift.{1} (ZMod q)) :=
  IsPrincipalIdealRing.of_surjective (ULift.ringEquiv.{0, 1} (R := ZMod q)).symm
    (ULift.ringEquiv.{0, 1} (R := ZMod q)).symm.surjective

theorem ulift_ann (q : ℕ) [NeZero q] :
    ∀ a : ULift.{1} (ZMod q), ∃ b, b * a = 0 ∧ ∀ r, r * b = 0 → ∃ s, r = s * a := by
  intro a
  obtain ⟨b, hba, hb⟩ := zmod_ann q a.down
  refine ⟨ULift.up b, ULift.ext _ _ hba, fun r hr => ?_⟩
  obtain ⟨s, hs⟩ := hb r.down (congrArg ULift.down hr)
  exact ⟨ULift.up s, ULift.ext _ _ hs⟩

theorem LeafZModInjFlat_of : LateralTheory.E.LeafTensQIsoPf.LeafZModInjFlat := by
  intro q _ M _ _ hM
  exact flat_of_injective_of_ann (ulift_ann q) M hM

end LateralTheory.E.LeafZModInjFlatPf
