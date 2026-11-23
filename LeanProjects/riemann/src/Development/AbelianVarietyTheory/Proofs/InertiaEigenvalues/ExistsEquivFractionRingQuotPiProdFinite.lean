import Mathlib
import Formalism.CharacterColumnKernels.StatementRho
import Formalism.GaloisCohomology.LocalTateDualityK
import ReciprocityTheory.Hypotheses.GalCohDefs
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LevRepZApply
open ReciprocityTheory.Gal

namespace GlobalTheory.CofinGen

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {ϖ : O}

omit [IsDomain O] [IsDiscreteValuationRing O] in
theorem exists_pow_smul_eq {M : Type} [AddCommGroup M] [Module O M]
    (hd : ∀ m : M, ∃ m', ϖ • m' = m) (n : ℕ) (m : M) : ∃ m', ϖ ^ n • m' = m := by
  induction n generalizing m with
  | zero => exact ⟨m, by simp⟩
  | succ n ih =>
    obtain ⟨m1, h1⟩ := ih m
    obtain ⟨m2, h2⟩ := hd m1
    exact ⟨m2, by rw [pow_succ, mul_smul, h2, h1]⟩

theorem baer_of_div (hϖ : Irreducible ϖ) {M : Type} [AddCommGroup M] [Module O M]
    (hd : ∀ m : M, ∃ m', ϖ • m' = m) : Module.Baer O M := by
  intro I g
  by_cases hI : I = ⊥
  · subst hI
    refine ⟨0, fun x hx => ?_⟩
    have : (⟨x, hx⟩ : (⊥ : Ideal O)) = 0 := Subtype.ext (by simpa using hx)
    rw [this]; simp
  · obtain ⟨n, hn⟩ := IsDiscreteValuationRing.ideal_eq_span_pow_irreducible hI hϖ
    subst hn
    obtain ⟨m, hm⟩ := exists_pow_smul_eq hd n (g ⟨ϖ ^ n, Ideal.mem_span_singleton_self _⟩)
    refine ⟨LinearMap.toSpanSingleton O M m, fun x hx => ?_⟩
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.1 hx
    have : (⟨c * ϖ ^ n, hx⟩ : Ideal.span {ϖ ^ n}) =
        c • ⟨ϖ ^ n, Ideal.mem_span_singleton_self _⟩ := Subtype.ext rfl
    rw [this, map_smul, ← hm, LinearMap.toSpanSingleton_apply, mul_smul]

theorem KO_div (hϖ : Irreducible ϖ) (m : Formalism.NG.KO O) : ∃ m', ϖ • m' = m := by
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ m
  have h0 : algebraMap O (FractionRing O) ϖ ≠ 0 := by
    simpa using hϖ.ne_zero
  refine ⟨Submodule.Quotient.mk ((algebraMap O (FractionRing O) ϖ)⁻¹ * x), ?_⟩
  rw [← Submodule.Quotient.mk_smul, Algebra.smul_def, ← mul_assoc, mul_inv_cancel₀ h0, one_mul]

theorem exists_inj (hϖ : Irreducible ϖ) {M : Type} [AddCommGroup M] [Module O M]
    (hd : ∀ m : M, ∃ m', ϖ • m' = m) (y : M) (hy : y ≠ 0) (hy' : ϖ • y = 0) :
    ∃ i : Formalism.NG.KO O →ₗ[O] M, Function.Injective i ∧ y ∈ LinearMap.range i := by
  have h0 : algebraMap O (FractionRing O) ϖ ≠ 0 := by
    simpa using hϖ.ne_zero
  set w : FractionRing O := (algebraMap O (FractionRing O) ϖ)⁻¹ with hw
  have hinj : Function.Injective (LinearMap.toSpanSingleton O (FractionRing O) w) := by
    rw [injective_iff_map_eq_zero]
    intro c hc
    rw [LinearMap.toSpanSingleton_apply, Algebra.smul_def, mul_eq_zero] at hc
    rcases hc with hc | hc
    · simpa using hc
    · exact absurd hc (inv_ne_zero h0)
  obtain ⟨h, hh⟩ := (baer_of_div hϖ hd).extension_property _ hinj
    (LinearMap.toSpanSingleton O M y)
  have hw1 : h w = y := by simpa using LinearMap.congr_fun hh 1
  have h1 : h 1 = 0 := by
    have : (1 : FractionRing O) = ϖ • w := by rw [Algebra.smul_def, hw, mul_inv_cancel₀ h0]
    rw [this, map_smul, hw1, hy']
  have hle : (1 : Submodule O (FractionRing O)) ≤ LinearMap.ker h := by
    intro x hx
    obtain ⟨c, rfl⟩ := Submodule.mem_one.1 hx
    rw [LinearMap.mem_ker, Algebra.algebraMap_eq_smul_one, map_smul, h1, smul_zero]
  refine ⟨Submodule.liftQ _ h hle, ?_, ⟨Submodule.Quotient.mk w, by simpa using hw1⟩⟩
  rw [← LinearMap.ker_eq_bot]
  refine Submodule.ker_liftQ_eq_bot _ _ _ fun x hx => ?_
  rw [LinearMap.mem_ker] at hx
  by_cases hx0 : x = 0
  · subst hx0; exact Submodule.zero_mem _
  rcases ValuationRing.isInteger_or_isInteger O x with ⟨c, hc⟩ | ⟨c, hc⟩
  · exact Submodule.mem_one.2 ⟨c, hc⟩
  · by_cases hu : IsUnit c
    · obtain ⟨d, hd'⟩ := hu.exists_right_inv
      refine Submodule.mem_one.2 ⟨d, ?_⟩
      have := congrArg (algebraMap O (FractionRing O)) hd'
      rw [map_mul, hc, map_one] at this
      field_simp at this
      exact this
    · exfalso
      have hm : c ∈ IsLocalRing.maximalIdeal O := hu
      rw [hϖ.maximalIdeal_eq] at hm
      obtain ⟨d, rfl⟩ := Ideal.mem_span_singleton'.1 hm
      have : w = d • x := by
        rw [map_mul] at hc
        rw [Algebra.smul_def, hw]
        field_simp at hc ⊢
        rw [← hc]
      apply hy
      rw [← hw1, this, map_smul, hx, smul_zero]

omit [IsDomain O] [IsDiscreteValuationRing O] in

theorem exists_socle {Y : Type} [AddCommGroup Y] [Module O Y]
    (hp : ∀ y : Y, ∃ n : ℕ, ϖ ^ n • y = 0) (T : Submodule O Y) (y : Y) (hy : y ∈ T) (h0 : y ≠ 0) :
    ∃ z ∈ T, z ≠ 0 ∧ ϖ • z = 0 := by
  obtain ⟨n, hn⟩ := hp y
  induction n generalizing y with
  | zero => exact absurd (by simpa using hn) h0
  | succ n ih =>
    by_cases h : ϖ • y = 0
    · exact ⟨y, hy, h0, h⟩
    · exact ih (ϖ • y) (T.smul_mem _ hy) h (by rw [← mul_smul, ← pow_succ, hn])

omit [IsDomain O] [IsDiscreteValuationRing O] in
theorem finite_fiber {Y : Type} [AddCommGroup Y] [Module O Y]
    (hf : {y : Y | ϖ • y = 0}.Finite) (y : Y) : {z : Y | ϖ • z = y}.Finite := by
  rcases Set.eq_empty_or_nonempty {z : Y | ϖ • z = y} with h | ⟨z, hz⟩
  · rw [h]; exact Set.finite_empty
  · refine (hf.image (fun t => z + t)).subset fun x hx => ⟨x - z, ?_, by simp⟩
    simp only [Set.mem_setOf_eq] at hz hx ⊢
    rw [smul_sub, hz, hx, sub_self]

omit [IsDomain O] [IsDiscreteValuationRing O] in
theorem finite_pow {Y : Type} [AddCommGroup Y] [Module O Y]
    (hf : {y : Y | ϖ • y = 0}.Finite) (n : ℕ) : {z : Y | ϖ ^ n • z = 0}.Finite := by
  induction n with
  | zero => exact (Set.finite_singleton 0).subset fun x hx => by simpa using hx
  | succ n ih =>
    refine (ih.biUnion fun y _ => finite_fiber hf y).subset fun x hx => ?_
    simp only [Set.mem_iUnion, Set.mem_setOf_eq] at hx ⊢
    exact ⟨ϖ • x, by rw [← mul_smul, ← pow_succ, hx], rfl⟩

def pw (ϖ : O) (Y : Type) [AddCommGroup Y] [Module O Y] (n : ℕ) : Submodule O Y :=
  LinearMap.range (ϖ ^ n • LinearMap.id : Y →ₗ[O] Y)

omit [IsDomain O] [IsDiscreteValuationRing O] in
theorem mem_pw {Y : Type} [AddCommGroup Y] [Module O Y] {n : ℕ} {y : Y} :
    y ∈ pw ϖ Y n ↔ ∃ z, ϖ ^ n • z = y := Iff.rfl

omit [IsDomain O] [IsDiscreteValuationRing O] in
theorem pw_anti {Y : Type} [AddCommGroup Y] [Module O Y] {n m : ℕ} (h : n ≤ m) :
    pw ϖ Y m ≤ pw ϖ Y n := by
  intro y hy
  obtain ⟨z, rfl⟩ := mem_pw.1 hy
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h
  exact mem_pw.2 ⟨ϖ ^ k • z, by rw [pow_add, mul_smul]⟩

omit [IsDomain O] [IsDiscreteValuationRing O] in

theorem exists_uniform {Y : Type} [AddCommGroup Y] [Module O Y] {S : Set Y} (hS : S.Finite) :
    ∃ N, ∀ y ∈ S, y ∈ pw ϖ Y N → y ∈ ⨅ n, pw ϖ Y n := by
  have h1 : ∀ y : Y, ∃ N, y ∈ pw ϖ Y N → y ∈ ⨅ n, pw ϖ Y n := by
    intro y
    by_cases h : y ∈ ⨅ n, pw ϖ Y n
    · exact ⟨0, fun _ => h⟩
    · rw [Submodule.mem_iInf, not_forall] at h
      obtain ⟨n, hn⟩ := h
      exact ⟨n, fun h => absurd h hn⟩
  choose f hf using h1
  obtain ⟨N, hN⟩ := (hS.image f).bddAbove
  exact ⟨N, fun y hy h => hf y (pw_anti (hN ⟨y, hy, rfl⟩) h)⟩

omit [IsDomain O] [IsDiscreteValuationRing O] in
theorem iInf_div {Y : Type} [AddCommGroup Y] [Module O Y]
    (hf : {y : Y | ϖ • y = 0}.Finite) (m : (⨅ n, pw ϖ Y n : Submodule O Y)) :
    ∃ m', ϖ • m' = m := by
  obtain ⟨N, hN⟩ := exists_uniform (ϖ := ϖ) (finite_fiber hf m.1)
  obtain ⟨z, hz⟩ := mem_pw.1 ((Submodule.mem_iInf _).1 m.2 (N + 1))
  have h1 : ϖ • ϖ ^ N • z = m.1 := by rw [← mul_smul, ← pow_succ', hz]
  exact ⟨⟨ϖ ^ N • z, hN _ h1 (mem_pw.2 ⟨z, rfl⟩)⟩, Subtype.ext h1⟩

omit [IsDomain O] [IsDiscreteValuationRing O] in
theorem finite_of_iInf_bot {Y : Type} [AddCommGroup Y] [Module O Y]
    (hp : ∀ y : Y, ∃ n : ℕ, ϖ ^ n • y = 0) (hf : {y : Y | ϖ • y = 0}.Finite)
    (hb : (⨅ n, pw ϖ Y n : Submodule O Y) = ⊥) : Finite Y := by
  obtain ⟨N, hN⟩ := exists_uniform (ϖ := ϖ) hf
  have : ∀ y : Y, ϖ ^ N • y = 0 := by
    intro y
    by_contra h
    obtain ⟨z, hz, hz0, hz1⟩ := exists_socle hp (pw ϖ Y N) _ (mem_pw.2 ⟨y, rfl⟩) h
    have := hN z hz1 hz
    rw [hb] at this
    exact hz0 (by simpa using this)
  exact Set.finite_univ_iff.1 ((finite_pow hf N).subset fun y _ => this y)

theorem aux (hϖ : Irreducible ϖ) (k : ℕ) : ∀ {Y : Type} [AddCommGroup Y] [Module O Y],
    (∀ y : Y, ∃ n : ℕ, ϖ ^ n • y = 0) → {y : Y | ϖ • y = 0}.Finite →
    {y : Y | ϖ • y = 0}.ncard = k →
    ∃ (a : ℕ) (F : Type) (_ : AddCommGroup F) (_ : Module O F), Finite F ∧
      Nonempty (Y ≃ₗ[O] (Fin a → Formalism.NG.KO O) × F) := by
  induction k using Nat.strong_induction_on with
  | _ k ih =>
  intro Y _ _ hp hf hk
  by_cases hb : (⨅ n, pw ϖ Y n : Submodule O Y) = ⊥
  · exact ⟨0, Y, inferInstance, inferInstance, finite_of_iInf_bot hp hf hb,
      ⟨(LinearEquiv.uniqueProd).symm⟩⟩
  · obtain ⟨y, hy, hy0⟩ := (Submodule.ne_bot_iff _).1 hb
    obtain ⟨z, hz, hz0, hz1⟩ := exists_socle hp _ y hy hy0
    obtain ⟨i0, hi0, x, hx⟩ := exists_inj hϖ (iInf_div hf) ⟨z, hz⟩
      (fun h => hz0 (congrArg Subtype.val h)) (Subtype.ext hz1)
    set i : Formalism.NG.KO O →ₗ[O] Y := (Submodule.subtype _).comp i0 with hi
    have hinj : Function.Injective i := Subtype.val_injective.comp hi0
    have hxz : i x = z := congrArg Subtype.val hx
    obtain ⟨r, hr⟩ := (baer_of_div hϖ (KO_div hϖ)).extension_property i hinj LinearMap.id
    have hri : ∀ t, r (i t) = t := fun t => LinearMap.congr_fun hr t
    have hsub : Subtype.val '' {y : LinearMap.ker r | ϖ • y = 0} ⊂ {y : Y | ϖ • y = 0} := by
      refine ⟨?_, fun h => ?_⟩
      · rintro _ ⟨t, ht, rfl⟩
        exact congrArg Subtype.val ht
      · obtain ⟨t, -, ht⟩ := h hz1
        have h2 : r z = 0 := ht ▸ t.2
        rw [← hxz, hri] at h2
        exact hz0 (by rw [← hxz, h2, map_zero])
    have hf' : {y : LinearMap.ker r | ϖ • y = 0}.Finite :=
      (hf.subset hsub.1).of_finite_image Subtype.val_injective.injOn
    have hlt := Set.ncard_lt_ncard hsub hf
    rw [Set.ncard_image_of_injective _ Subtype.val_injective, hk] at hlt
    obtain ⟨a, F, _, _, hF, ⟨e⟩⟩ := ih _ hlt (Y := LinearMap.ker r)
      (fun t => (hp t.1).imp fun n hn => Subtype.ext hn) hf' rfl
    have hbij : Function.Bijective (i.coprod (LinearMap.ker r).subtype) := by
      constructor
      · rw [injective_iff_map_eq_zero]
        rintro ⟨s, t⟩ h
        have h1 : i s + t.1 = 0 := h
        have h2 := congrArg r h1
        rw [map_add, hri, t.2, add_zero, map_zero] at h2
        subst h2
        rw [map_zero, zero_add] at h1
        exact Prod.ext rfl (Subtype.ext h1)
      · intro y
        exact ⟨(r y, ⟨y - i (r y), by simp [hri]⟩), by simp⟩
    refine ⟨a + 1, F, inferInstance, inferInstance, hF, ⟨?_⟩⟩
    exact (LinearEquiv.ofBijective _ hbij).symm ≪≫ₗ (LinearEquiv.refl O _).prodCongr e ≪≫ₗ
      (LinearEquiv.prodAssoc O _ _ _).symm ≪≫ₗ
      (Fin.consLinearEquiv O fun _ : Fin (a + 1) => Formalism.NG.KO O).prodCongr (LinearEquiv.refl O F)

theorem exists_equiv_pi_prod_finite :
    ∀ {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {ϖ : O}, Irreducible ϖ →
    ∀ {Y : Type} [AddCommGroup Y] [Module O Y], (∀ y : Y, ∃ n : ℕ, ϖ ^ n • y = 0) →
    Finite (LinearMap.ker (ϖ • LinearMap.id : Y →ₗ[O] Y)) →
    ∃ (a : ℕ) (F : Type) (_ : AddCommGroup F) (_ : Module O F), Finite F ∧
      Nonempty (Y ≃ₗ[O] (Fin a → Formalism.NG.KO O) × F) := by
  intro O _ _ _ ϖ hϖ Y _ _ hp hf
  exact aux hϖ _ hp hf rfl

end GlobalTheory.CofinGen
