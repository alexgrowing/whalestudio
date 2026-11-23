import Formalism.HermitianCurvature.PrimeToDifferent

namespace Formalism.FourierDecayAlt.P.S6x3

open Formalism.FourierDecayAlt.S6
open NumberField NumberField.IsCMField Module
open scoped nonZeroDivisors

theorem trace_eq (E : Type) [Field E] [NumberField E] [IsCMField E] (x : E) :
    algebraMap (maximalRealSubfield E) E (Algebra.trace (maximalRealSubfield E) E x)
      = x + complexConj E x := by
  classical
  rw [trace_eq_sum_automorphisms]
  have hu : (Finset.univ : Finset (E ≃ₐ[maximalRealSubfield E] E)) = {1, complexConj E} := by
    symm
    apply Finset.eq_univ_of_card
    rw [Finset.card_pair (complexConj_ne_one E).symm, ← Nat.card_eq_fintype_card,
      IsGalois.card_aut_eq_finrank, Algebra.IsQuadraticExtension.finrank_eq_two]
  rw [hu, Finset.sum_pair (complexConj_ne_one E).symm]
  rfl

theorem exists_theta (E : Type) [Field E] [NumberField E] [IsCMField E] (g : ℕ) (hg : 0 < g)
    (hU : UnramAbove E g) :
    ∃ θ w : 𝓞 E, (θ : E) + complexConj E θ = 1 + (g : E) * w := by
  set F := maximalRealSubfield E with hF
  let I : Ideal (𝓞 F) := LinearMap.range (Algebra.intTrace (𝓞 F) (𝓞 E))
  have key : I ⊔ Ideal.span {(g : 𝓞 F)} = ⊤ := by
    by_contra hne
    obtain ⟨P, hP, hle⟩ := Ideal.exists_le_maximal _ hne
    have hgP : (g : 𝓞 F) ∈ P := hle (Ideal.mem_sup_right (Ideal.mem_span_singleton_self _))
    have hP0 : P ≠ ⊥ := by
      intro h
      rw [h, Ideal.mem_bot] at hgP
      exact hg.ne' (by exact_mod_cast hgP)
    obtain ⟨x, hx, hx1⟩ := FractionalIdeal.exists_notMem_one_of_ne_bot (K := F) hP0 hP.ne_top
    have hPF : ((P : Ideal (𝓞 F)) : FractionalIdeal (𝓞 F)⁰ F) ≠ 0 := by
      simpa using hP0
    rw [FractionalIdeal.mem_inv_iff hPF] at hx
    have hxP : ∀ p ∈ P, ∃ z : 𝓞 F, x * (p : F) = z := by
      intro p hp
      have := hx (algebraMap (𝓞 F) F p) ((FractionalIdeal.mem_coeIdeal _).mpr ⟨p, hp, rfl⟩)
      obtain ⟨z, hz⟩ := (FractionalIdeal.mem_one_iff _).mp this
      exact ⟨z, hz.symm⟩

    have h10 : (1 : FractionalIdeal (𝓞 E)⁰ E) ≠ 0 := one_ne_zero
    have hdual : algebraMap F E x ∈ FractionalIdeal.dual (𝓞 F) F (1 : FractionalIdeal (𝓞 E)⁰ E) := by
      rw [FractionalIdeal.mem_dual h10]
      intro a ha
      obtain ⟨a0, rfl⟩ := (FractionalIdeal.mem_one_iff _).mp ha
      have h1 : Algebra.traceForm F E (algebraMap F E x) (algebraMap (𝓞 E) E a0)
          = x * algebraMap (𝓞 F) F (Algebra.intTrace (𝓞 F) (𝓞 E) a0) := by
        rw [Algebra.traceForm_apply, ← Algebra.smul_def, map_smul, smul_eq_mul,
          Algebra.algebraMap_intTrace (L := E)]
      rw [h1]
      obtain ⟨z, hz⟩ := hxP (Algebra.intTrace (𝓞 F) (𝓞 E) a0)
        (hle (Ideal.mem_sup_left ⟨a0, rfl⟩))
      exact ⟨z, hz.symm⟩
    obtain ⟨d, hd, j, hj, hdj⟩ := Ideal.isCoprime_iff_exists.mp hU
    obtain ⟨y, rfl⟩ := Ideal.mem_span_singleton'.mp hj
    have hd' : algebraMap (𝓞 E) E d ∈
        (FractionalIdeal.dual (𝓞 F) F (1 : FractionalIdeal (𝓞 E)⁰ E))⁻¹ := by
      rw [← coeIdeal_differentIdeal (𝓞 F) F E (𝓞 E)]
      exact (FractionalIdeal.mem_coeIdeal _).mpr ⟨d, hd, rfl⟩
    rw [FractionalIdeal.mem_inv_iff (FractionalIdeal.dual_ne_zero _ _ h10)] at hd'
    obtain ⟨z1, hz1⟩ := (FractionalIdeal.mem_one_iff _).mp (hd' _ hdual)
    obtain ⟨z2, hz2⟩ := hxP _ hgP
    have hxE : algebraMap F E x = algebraMap (𝓞 E) E (z1 + y * algebraMap (𝓞 F) (𝓞 E) z2) := by
      have e1 : algebraMap (𝓞 E) E d + algebraMap (𝓞 E) E y * (g : E) = 1 := by
        have := congrArg (algebraMap (𝓞 E) E) hdj
        simpa using this
      have e2 : algebraMap F E x * (g : E) = algebraMap (𝓞 E) E (algebraMap (𝓞 F) (𝓞 E) z2) := by
        have := congrArg (algebraMap F E) hz2
        rw [map_mul] at this
        have e4 : algebraMap F E (((g : 𝓞 F) : 𝓞 F) : F) = (g : E) := by simp
        rw [e4] at this
        exact this
      rw [map_add, map_mul, hz1, ← e2]
      linear_combination (-(algebraMap F E x)) * e1
    have hint : IsIntegral ℤ x := by
      have : IsIntegral ℤ (algebraMap F E x) := by
        rw [hxE]; exact RingOfIntegers.isIntegral_coe _
      exact (isIntegral_algebraMap_iff (algebraMap F E).injective).mp this
    exact hx1 ((FractionalIdeal.mem_one_iff _).mpr ⟨⟨x, hint⟩, rfl⟩)
  have h1 : (1 : 𝓞 F) ∈ I ⊔ Ideal.span {(g : 𝓞 F)} := by rw [key]; trivial
  obtain ⟨i, ⟨θ, rfl⟩, j, hj, hij⟩ := Submodule.mem_sup.mp h1
  obtain ⟨w, rfl⟩ := Ideal.mem_span_singleton'.mp hj
  refine ⟨θ, -algebraMap (𝓞 F) (𝓞 E) w, ?_⟩
  rw [← trace_eq, ← Algebra.algebraMap_intTrace (A := 𝓞 F) (B := 𝓞 E)]
  have := congrArg (fun t : 𝓞 F => algebraMap F E (algebraMap (𝓞 F) F t)) hij
  simp only [map_add, map_mul, map_one, map_natCast] at this
  have e3 : algebraMap (𝓞 E) E (algebraMap (𝓞 F) (𝓞 E) w) = algebraMap F E (algebraMap (𝓞 F) F w) := rfl
  have e5 : ((-algebraMap (𝓞 F) (𝓞 E) w : 𝓞 E) : E)
      = -algebraMap F E (algebraMap (𝓞 F) F w) := by
    rw [← e3]; exact map_neg (algebraMap (𝓞 E) E) _
  rw [e5]
  linear_combination this

section Lattices

variable (E : Type) [Field E] [NumberField E] [IsCMField E]

theorem mem_twLat (A B : FI E) (s : ℕ) (t : E) :
    t ∈ twLat E A B s ↔ t ∈ A ∧ t - (-1) ^ s * complexConj E t ∈ B := by
  unfold twLat
  rw [Submodule.mem_inf, Submodule.mem_comap]
  have : ((LinearMap.id : E →ₗ[ℤ] E) - ((-1 : ℤ) ^ s) • conjZ E) t
      = t - (-1) ^ s * complexConj E t := by
    rw [LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply, zsmul_eq_mul]
    push_cast
    rfl
  rw [this]; rfl

noncomputable def eig (A : FI E) (s : ℕ) : Submodule ℤ E :=
  zsub E A ⊓ LinearMap.ker (LinearMap.id - ((-1 : ℤ) ^ s) • conjZ E)

theorem mem_eig (A : FI E) (s : ℕ) (t : E) :
    t ∈ eig E A s ↔ t ∈ A ∧ t - (-1) ^ s * complexConj E t = 0 := by
  unfold eig
  rw [Submodule.mem_inf, LinearMap.mem_ker]
  have : ((LinearMap.id : E →ₗ[ℤ] E) - ((-1 : ℤ) ^ s) • conjZ E) t
      = t - (-1) ^ s * complexConj E t := by
    rw [LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply, zsmul_eq_mul]
    push_cast
    rfl
  rw [this]; rfl

theorem mul_mem_FI (A : FI E) (z : 𝓞 E) (t : E) (ht : t ∈ A) : (z : E) * t ∈ A := by
  have := (A : Submodule (𝓞 E) E).smul_mem z ht
  rw [Algebra.smul_def] at this
  exact this

theorem sign_mem (A : FI E) (s : ℕ) (t : E) (ht : t ∈ A) : (-1) ^ s * t ∈ A := by
  have := mul_mem_FI E A ((-1) ^ s) t ht
  simpa using this

theorem sign_sq (s : ℕ) : ((-1 : E) ^ s) * (-1) ^ s = 1 := by
  rw [← mul_pow]; simp

theorem mem_gA (A : FI E) (g : ℕ) (x : E) :
    x ∈ A * FractionalIdeal.spanSingleton (𝓞 E)⁰ (g : E) ↔ ∃ a ∈ A, x = (g : E) * a := by
  rw [mul_comm, FractionalIdeal.mem_singleton_mul]

theorem gA_le (A : FI E) (g : ℕ) (x : E)
    (hx : x ∈ A * FractionalIdeal.spanSingleton (𝓞 E)⁰ (g : E)) : x ∈ A := by
  obtain ⟨a, ha, rfl⟩ := (mem_gA E A g x).mp hx
  have := mul_mem_FI E A (g : 𝓞 E) a ha
  simpa using this

theorem tw_eq (A : FI E) (g s : ℕ) (hA : ConjStable E A) (hg : 0 < g) (hU : UnramAbove E g) :
    twLat E A (A * FractionalIdeal.spanSingleton _ (g : E)) s
      = eig E A s ⊔ zsub E (A * FractionalIdeal.spanSingleton _ (g : E)) := by
  apply le_antisymm
  · intro t ht
    obtain ⟨ht1, ht2⟩ := (mem_twLat E _ _ s t).mp ht
    obtain ⟨θ, w, hθ⟩ := exists_theta E g hg hU
    have h1 : (θ : E) * t ∈ A := mul_mem_FI E A θ t ht1
    have h2 : (θ : E) * t + (-1) ^ s * complexConj E ((θ : E) * t) ∈ eig E A s := by
      rw [mem_eig]
      refine ⟨A.val.add_mem h1 (sign_mem E A s _ (hA _ h1)), ?_⟩
      simp only [map_add, map_mul, map_pow, map_neg, map_one, complexConj_apply_apply]
      linear_combination (-(θ : E) * t) * sign_sq E s
    have h3 : complexConj E θ * (t - (-1) ^ s * complexConj E t) - (g : E) * ((w : E) * t)
        ∈ zsub E (A * FractionalIdeal.spanSingleton _ (g : E)) := by
      refine Submodule.sub_mem _ ?_ ?_
      · exact mul_mem_FI E _ (ringOfIntegersComplexConj E θ) _ ht2
      · exact (mem_gA E A g _).mpr ⟨_, mul_mem_FI E A w t ht1, rfl⟩
    have h4 : t = ((θ : E) * t + (-1) ^ s * complexConj E ((θ : E) * t)) +
        (complexConj E θ * (t - (-1) ^ s * complexConj E t) - (g : E) * ((w : E) * t)) := by
      rw [map_mul]
      linear_combination (-t) * hθ
    rw [h4]
    exact Submodule.add_mem_sup h2 h3
  · refine sup_le ?_ ?_
    · intro t ht
      obtain ⟨ht1, ht2⟩ := (mem_eig E A s t).mp ht
      rw [mem_twLat, ht2]
      exact ⟨ht1, Submodule.zero_mem _⟩
    · intro t ht
      rw [mem_twLat]
      refine ⟨gA_le E A g t ht, ?_⟩
      obtain ⟨a, ha, rfl⟩ := (mem_gA E A g t).mp ht
      refine (mem_gA E A g _).mpr ⟨a - (-1) ^ s * complexConj E a,
        A.val.sub_mem ha (sign_mem E A s _ (hA _ ha)), ?_⟩
      rw [map_mul, map_natCast]
      ring

end Lattices

section Ranks

variable (E : Type) [Field E] [NumberField E] [IsCMField E]

instance finite_zsub (A : FI E) : Module.Finite ℤ (zsub E A) :=
  inferInstanceAs (Module.Finite ℤ A)

theorem finrank_zsub (A : FI E) (hA : A ≠ 0) : finrank ℤ (zsub E A) = finrank ℚ E := by
  have := fractionalIdeal_rank E (Units.mk0 A hA)
  rw [RingOfIntegers.rank] at this
  exact this

theorem finite_of_le (N : Submodule ℤ E) (A : FI E) (h : N ≤ zsub E A) : Module.Finite ℤ N := by
  have : IsNoetherian ℤ (zsub E A) := inferInstance
  have := isNoetherian_of_le h
  infer_instance

theorem finrank_le_of_map_le (f : E →ₗ[ℤ] E) (hf : Function.Injective f) (N N' : Submodule ℤ E)
    [Module.Finite ℤ N'] (h : N.map f ≤ N') : finrank ℤ N ≤ finrank ℤ N' := by
  rw [(Submodule.equivMapOfInjective f hf N).finrank_eq]
  exact Submodule.finrank_mono h

theorem relIndex_nsmul (N : Submodule ℤ E) [Module.Finite ℤ N] (g : ℕ) :
    (N.toAddSubgroup.map (nsmulAddMonoidHom (α := E) g)).relIndex N.toAddSubgroup
      = g ^ finrank ℤ N := by
  have h1 : Module.Finite ℤ ↥(AddSubgroup.toIntSubmodule N.toAddSubgroup) :=
    inferInstanceAs (Module.Finite ℤ N)
  have h2 : Module.Free ℤ ↥(AddSubgroup.toIntSubmodule N.toAddSubgroup) := inferInstance
  exact AddSubgroup.relIndex_map_nsmul g N.toAddSubgroup

theorem finrank_sup (N₁ N₂ : Submodule ℤ E) [Module.Finite ℤ N₁] [Module.Finite ℤ N₂]
    (h : Disjoint N₁ N₂) : finrank ℤ ↥(N₁ ⊔ N₂) = finrank ℤ N₁ + finrank ℤ N₂ := by
  have hinj : Function.Injective (N₁.subtype.coprod N₂.subtype) := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_coprod_of_disjoint_range]
    · simp
    · simpa using h
  have := LinearMap.finrank_range_of_inj hinj
  rw [LinearMap.range_coprod, Submodule.range_subtype, Submodule.range_subtype,
    Module.finrank_prod] at this
  exact this

theorem exists_delta : ∃ δ : 𝓞 E, (δ : E) ≠ 0 ∧ complexConj E δ = -(δ : E) := by
  by_contra h
  push Not at h
  have hfix : ∀ a : 𝓞 E, complexConj E a = a := by
    intro a
    by_contra hne
    refine h (a - ringOfIntegersComplexConj E a) ?_ ?_
    · intro h0
      apply hne
      have : (a : E) - complexConj E a = 0 := h0
      linear_combination -this
    · have : ((a - ringOfIntegersComplexConj E a : 𝓞 E) : E) = (a : E) - complexConj E a := rfl
      rw [this, map_sub, complexConj_apply_apply]
      ring
  apply complexConj_ne_one E
  ext x
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := 𝓞 E) x
  rw [map_div₀, hfix, hfix]
  rfl

instance finite_eig (A : FI E) (s : ℕ) : Module.Finite ℤ (eig E A s) :=
  finite_of_le E _ A inf_le_left

theorem rk_le (A : FI E) (s : ℕ) : finrank ℤ (eig E A s) ≤ finrank ℤ (eig E A (s + 1)) := by
  obtain ⟨δ, h0, hδ⟩ := exists_delta E
  refine finrank_le_of_map_le E (LinearMap.mulLeft ℤ (δ : E)) (mul_right_injective₀ h0) _ _ ?_
  rintro _ ⟨t, ht, rfl⟩
  obtain ⟨ht1, ht2⟩ := (mem_eig E A s t).mp ht
  rw [mem_eig, LinearMap.mulLeft_apply]
  refine ⟨mul_mem_FI E A δ t ht1, ?_⟩
  rw [map_mul, hδ, pow_succ]
  linear_combination (δ : E) * ht2

theorem eig_add_two (A : FI E) (s : ℕ) : eig E A (s + 2) = eig E A s := by
  ext t
  rw [mem_eig, mem_eig, pow_add]
  simp

theorem rk_succ (A : FI E) (s : ℕ) : finrank ℤ (eig E A (s + 1)) = finrank ℤ (eig E A s) := by
  apply le_antisymm _ (rk_le E A s)
  have := rk_le E A (s + 1)
  rwa [eig_add_two] at this

theorem rk_add (A : FI E) (s : ℕ) (hA : ConjStable E A) :
    finrank ℤ (eig E A s) + finrank ℤ (eig E A (s + 1)) = finrank ℤ (zsub E A) := by
  have hd : Disjoint (eig E A s) (eig E A (s + 1)) := by
    rw [Submodule.disjoint_def]
    intro t h1 h2
    have e1 := ((mem_eig E A s t).mp h1).2
    have e2 := ((mem_eig E A (s + 1) t).mp h2).2
    rw [pow_succ] at e2
    have : (2 : E) * t = 0 := by linear_combination e1 + e2
    simpa using this
  rw [← finrank_sup E _ _ hd]
  apply le_antisymm
  · exact Submodule.finrank_mono (sup_le inf_le_left inf_le_left)
  · have : Module.Finite ℤ ↥(eig E A s ⊔ eig E A (s + 1)) :=
      finite_of_le E _ A (sup_le inf_le_left inf_le_left)
    refine finrank_le_of_map_le E (LinearMap.mulLeft ℤ (2 : E))
      (mul_right_injective₀ two_ne_zero) _ _ ?_
    rintro _ ⟨a, ha, rfl⟩
    have ha' : a ∈ A := ha
    have hc := sign_mem E A s _ (hA _ ha')
    have h1 : a + (-1) ^ s * complexConj E a ∈ eig E A s := by
      rw [mem_eig]
      refine ⟨A.val.add_mem ha' hc, ?_⟩
      simp only [map_add, map_mul, map_pow, map_neg, map_one, complexConj_apply_apply]
      linear_combination (-a) * sign_sq E s
    have h2 : a - (-1) ^ s * complexConj E a ∈ eig E A (s + 1) := by
      rw [mem_eig]
      refine ⟨A.val.sub_mem ha' hc, ?_⟩
      simp only [map_sub, map_mul, map_pow, map_neg, map_one, complexConj_apply_apply, pow_succ]
      linear_combination (-a) * sign_sq E s
    have h3 : LinearMap.mulLeft ℤ (2 : E) a
        = (a + (-1) ^ s * complexConj E a) + (a - (-1) ^ s * complexConj E a) := by
      rw [LinearMap.mulLeft_apply]; ring
    rw [h3]
    exact Submodule.add_mem_sup h1 h2

theorem rk_eq (A : FI E) (s : ℕ) (hA0 : A ≠ 0) (hA : ConjStable E A) :
    finrank ℤ (eig E A s) = deg E := by
  have h1 := rk_add E A s hA
  rw [rk_succ, finrank_zsub E A hA0] at h1
  have h2 : finrank (maximalRealSubfield E) E = 2 :=
    Algebra.IsQuadraticExtension.finrank_eq_two _ _
  have h3 := finrank_mul_finrank ℚ (maximalRealSubfield E) E
  rw [h2] at h3
  unfold deg
  omega

end Ranks

section Index

variable (E : Type) [Field E] [NumberField E] [IsCMField E]

theorem gA_eq_map (A : FI E) (g : ℕ) :
    (zsub E (A * FractionalIdeal.spanSingleton _ (g : E))).toAddSubgroup
      = (zsub E A).toAddSubgroup.map (nsmulAddMonoidHom (α := E) g) := by
  ext x
  rw [AddSubgroup.mem_map]
  constructor
  · intro hx
    obtain ⟨a, ha, rfl⟩ := (mem_gA E A g x).mp hx
    exact ⟨a, ha, by simp⟩
  · rintro ⟨a, ha, rfl⟩
    exact (mem_gA E A g _).mpr ⟨a, ha, by simp⟩

theorem inf_eq_map (A : FI E) (g s : ℕ) (hg : 0 < g) :
    (zsub E (A * FractionalIdeal.spanSingleton _ (g : E))).toAddSubgroup ⊓
        (eig E A s).toAddSubgroup
      = (eig E A s).toAddSubgroup.map (nsmulAddMonoidHom (α := E) g) := by
  have hg' : (g : E) ≠ 0 := by exact_mod_cast hg.ne'
  ext x
  rw [AddSubgroup.mem_map, AddSubgroup.mem_inf]
  constructor
  · rintro ⟨hx1, hx2⟩
    obtain ⟨a, ha, rfl⟩ := (mem_gA E A g x).mp hx1
    obtain ⟨-, h2⟩ := (mem_eig E A s _).mp hx2
    refine ⟨a, (mem_eig E A s a).mpr ⟨ha, ?_⟩, by simp⟩
    rw [map_mul, map_natCast] at h2
    apply mul_left_cancel₀ hg'
    linear_combination h2
  · rintro ⟨a, ha, rfl⟩
    obtain ⟨h1, h2⟩ := (mem_eig E A s a).mp ha
    have e : nsmulAddMonoidHom (α := E) g a = (g : E) * a := by simp
    rw [e]
    refine ⟨(mem_gA E A g _).mpr ⟨a, h1, rfl⟩, (mem_eig E A s _).mpr ⟨?_, ?_⟩⟩
    · exact gA_le E A g _ ((mem_gA E A g _).mpr ⟨a, h1, rfl⟩)
    · rw [map_mul, map_natCast]
      linear_combination (g : E) * h2

end Index

end Formalism.FourierDecayAlt.P.S6x3

namespace Formalism.FourierDecayAlt.P

open Formalism.FourierDecayAlt.S6 Formalism.FourierDecayAlt.P.S6x3
open NumberField NumberField.IsCMField Module
open scoped nonZeroDivisors

theorem twistedLatticeIndex : Formalism.FourierDecayAlt.S6.IndexCore := by
  intro E _ _ _ A g s hA0 hA hg hU
  have h2 : idx E (zsub E (A * FractionalIdeal.spanSingleton _ (g : E)))
      (twLat E A (A * FractionalIdeal.spanSingleton _ (g : E)) s) = g ^ deg E := by
    unfold idx
    rw [tw_eq E A g s hA hg hU, Submodule.sup_toAddSubgroup, AddSubgroup.relIndex_sup_right,
      ← AddSubgroup.inf_relIndex_right, inf_eq_map E A g s hg, relIndex_nsmul, rk_eq E A s hA0 hA]
  refine ⟨?_, h2⟩
  have h3 : idx E (zsub E (A * FractionalIdeal.spanSingleton _ (g : E))) (zsub E A)
      = g ^ deg E * g ^ deg E := by
    unfold idx
    rw [gA_eq_map, relIndex_nsmul, ← rk_add E A s hA, rk_succ, rk_eq E A s hA0 hA, pow_add]
  have hle1 : (zsub E (A * FractionalIdeal.spanSingleton _ (g : E))).toAddSubgroup ≤
      (twLat E A (A * FractionalIdeal.spanSingleton _ (g : E)) s).toAddSubgroup := by
    rw [tw_eq E A g s hA hg hU]
    exact Submodule.toAddSubgroup_mono le_sup_right
  have hle2 : (twLat E A (A * FractionalIdeal.spanSingleton _ (g : E)) s).toAddSubgroup ≤
      (zsub E A).toAddSubgroup := Submodule.toAddSubgroup_mono inf_le_left
  have h4 := AddSubgroup.relIndex_mul_relIndex _ _ _ hle1 hle2
  unfold idx at h2 h3 ⊢
  rw [h2, h3] at h4
  exact Nat.eq_of_mul_eq_mul_left (pow_pos hg _) h4

end Formalism.FourierDecayAlt.P
