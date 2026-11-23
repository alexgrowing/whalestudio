import Mathlib
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.LeadMinor

noncomputable section

namespace PositivityTheory.HtPt.Famproj

open NumberField GlobalTheory.CompanionTheory.Ar.HT

theorem projective_of_factor {A M : Type} [CommRing A] [AddCommGroup M] [Module A M]
    (h : ∀ m : Ideal A, m.IsMaximal → ∃ (N : Type) (_ : AddCommGroup N) (_ : Module A N) (_ : Module.Projective A N)
      (f : M →ₗ[A] N) (g : N →ₗ[A] M) (t : A), t ∉ m ∧ ∀ x, g (f x) = t • x) : Module.Projective A M := by
  classical
  choose N inst1 inst2 proj f g t ht hfg using fun m : {m : Ideal A // m.IsMaximal} => h m.1 m.2
  have hspan : (1 : A) ∈ Submodule.span A (Set.range t) := by
    by_contra h1
    have hne : Ideal.span (Set.range t) ≠ ⊤ := fun h2 => h1 (by
      change (1 : A) ∈ Ideal.span (Set.range t)
      rw [h2]
      trivial)
    obtain ⟨m, hm, hle⟩ := Ideal.exists_le_maximal _ hne
    exact ht ⟨m, hm⟩ (hle (Ideal.subset_span ⟨⟨m, hm⟩, rfl⟩))
  obtain ⟨c, hc⟩ := Finsupp.mem_span_range_iff_exists_finsupp.mp hspan
  refine Module.Projective.of_split (M := DirectSum _ N)
    (∑ i ∈ c.support, (DirectSum.lof A _ N i).comp (f i))
    (DirectSum.toModule A _ M (fun i => c i • g i)) ?_
  apply LinearMap.ext
  intro x
  simp only [LinearMap.comp_apply, LinearMap.sum_apply, map_sum,
    DirectSum.toModule_lof, LinearMap.smul_apply, hfg, LinearMap.id_apply, smul_smul]
  rw [← Finset.sum_smul]
  rw [Finsupp.sum] at hc
  simp only [smul_eq_mul] at hc
  rw [hc, one_smul]

section Sub

variable {A Ω V : Type} [CommRing A] [Field Ω] [Algebra A Ω] [AddCommGroup V] [Module Ω V] [Module A V]
  [IsScalarTower A Ω V]

theorem exists_smul_mem (m : Ideal A) [hm : m.IsPrime] (R : Subring Ω)
    (hR : ∀ r ∈ R, ∃ t ∉ m, ∃ a : A, algebraMap A Ω t * r = algebraMap A Ω a) (M : Submodule A V) {x : V}
    (hx : x ∈ Submodule.span R (M : Set V)) : ∃ t ∉ m, t • x ∈ M := by
  have h1 : (1 : A) ∉ m := fun h => hm.ne_top ((Ideal.eq_top_iff_one _).2 h)
  induction hx using Submodule.span_induction with
  | mem y hy => exact ⟨1, h1, by simpa using hy⟩
  | zero => exact ⟨1, h1, by simp⟩
  | add y z _ _ hy hz =>
    obtain ⟨t1, ht1, hy1⟩ := hy
    obtain ⟨t2, ht2, hz2⟩ := hz
    refine ⟨t1 * t2, fun h => (hm.mem_or_mem h).elim ht1 ht2, ?_⟩
    rw [smul_add]
    apply M.add_mem
    · rw [mul_comm, mul_smul]
      exact M.smul_mem _ hy1
    · rw [mul_smul]
      exact M.smul_mem _ hz2
  | smul r y _ hy =>
    obtain ⟨t', ht', hy'⟩ := hy
    obtain ⟨t, ht, a, hta⟩ := hR r r.2
    have key : t • (r • y) = a • y := by
      rw [← algebraMap_smul Ω t, Subring.smul_def, smul_smul, hta, algebraMap_smul]
    refine ⟨t' * t, fun h => (hm.mem_or_mem h).elim ht' ht, ?_⟩
    rw [mul_smul, key, smul_comm]
    exact M.smul_mem _ hy'

omit [Algebra A Ω] [Module Ω V] [IsScalarTower A Ω V] in

theorem exists_smul_le (m : Ideal A) [hm : m.IsPrime] {M N : Submodule A V} (hM : M.FG)
    (h : ∀ x ∈ M, ∃ t ∉ m, t • x ∈ N) : ∃ t ∉ m, ∀ x ∈ M, t • x ∈ N := by
  classical
  obtain ⟨S, hS⟩ := hM
  have hSM : ∀ s ∈ S, s ∈ M := fun s hs => hS ▸ Submodule.subset_span hs
  choose! t ht hts using fun s (hs : s ∈ S) => h s (hSM s hs)
  refine ⟨∏ s ∈ S, t s, fun hp => ?_, ?_⟩
  · obtain ⟨s, hs, hsm⟩ := Ideal.IsPrime.prod_mem_iff.1 hp
    exact ht s hs hsm
  · intro x hx
    rw [← hS] at hx
    induction hx using Submodule.span_induction with
    | mem y hy =>
      rw [← Finset.mul_prod_erase S t hy, mul_comm, mul_smul]
      exact N.smul_mem _ (hts y hy)
    | zero => simp
    | add y z _ _ hy hz =>
      rw [smul_add]
      exact N.add_mem hy hz
    | smul a y _ hy =>
      rw [smul_comm]
      exact N.smul_mem _ hy

theorem factor_of_frame (hA : Function.Injective (algebraMap A Ω)) (m : Ideal A) [hm : m.IsPrime] (R : Subring Ω)
    (hR : ∀ r ∈ R, ∃ t ∉ m, ∃ a : A, algebraMap A Ω t * r = algebraMap A Ω a) (M : Submodule A V) (hM : M.FG)
    {r : ℕ} (b : Fin r → V) (hb : LinearIndependent Ω b)
    (he : Submodule.span R (M : Set V) = Submodule.span R (Set.range b)) :
    ∃ (N : Type) (_ : AddCommGroup N) (_ : Module A N) (_ : Module.Projective A N)
      (f : M →ₗ[A] N) (g : N →ₗ[A] M) (t : A), t ∉ m ∧ ∀ x, g (f x) = t • x := by
  have h1 : (1 : A) ∉ m := fun h => hm.ne_top ((Ideal.eq_top_iff_one _).2 h)
  have hbA : LinearIndependent A b := by
    refine hb.restrict_scalars ?_
    intro x y hxy
    apply hA
    simpa [Algebra.smul_def] using hxy
  set M' := Submodule.span A (Set.range b) with hM'
  haveI : Module.Free A M' := Module.Free.of_basis (Module.Basis.span hbA)
  have hM'fg : M'.FG := Submodule.fg_span (Set.finite_range b)
  obtain ⟨t, ht, hto⟩ := exists_smul_le m hM (N := M') (fun x hx => exists_smul_mem m R hR M' (by
    have hx' : x ∈ Submodule.span R (Set.range b) := he ▸ Submodule.subset_span hx
    exact Submodule.span_mono (Submodule.subset_span (R := A)) hx'))
  have hback : ∀ y ∈ M', ∃ s ∉ m, s • y ∈ M := by
    intro y hy
    induction hy using Submodule.span_induction with
    | mem z hz =>
      refine exists_smul_mem m R hR M ?_
      rw [he]
      exact Submodule.subset_span hz
    | zero => exact ⟨1, h1, by simp⟩
    | add y z _ _ hy hz =>
      obtain ⟨t1, ht1, hy1⟩ := hy
      obtain ⟨t2, ht2, hz2⟩ := hz
      refine ⟨t1 * t2, fun h => (hm.mem_or_mem h).elim ht1 ht2, ?_⟩
      rw [smul_add]
      apply M.add_mem
      · rw [mul_comm, mul_smul]
        exact M.smul_mem _ hy1
      · rw [mul_smul]
        exact M.smul_mem _ hz2
    | smul a y _ hy =>
      obtain ⟨s, hs, hsy⟩ := hy
      exact ⟨s, hs, by rw [smul_comm]; exact M.smul_mem _ hsy⟩
  obtain ⟨t', ht', hto'⟩ := exists_smul_le m hM'fg (N := M) hback
  let f : M →ₗ[A] M' := LinearMap.codRestrict M' (t • M.subtype) (fun x => by simpa using hto x x.2)
  let g : M' →ₗ[A] M := LinearMap.codRestrict M (t' • M'.subtype) (fun y => by simpa using hto' y y.2)
  refine ⟨M', inferInstance, inferInstance, Module.Projective.of_free, f, g, t' * t,
    fun h => (hm.mem_or_mem h).elim ht' ht, fun x => ?_⟩
  apply Subtype.ext
  simp [f, g, smul_smul]

end Sub

theorem exists_diff_gen (E : Type) [Field E] [NumberField E] (p : ℕ) [hp : Fact p.Prime] :
    ∃ δ ∈ differentIdeal ℤ (𝓞 E), ∃ r : ℤ, ¬ (p : ℤ) ∣ r ∧ ∀ x ∈ differentIdeal ℤ (𝓞 E), ∃ z, (r : 𝓞 E) * x = z * δ := by
  classical
  set D := differentIdeal ℤ (𝓞 E) with hD
  have hD0 : D ≠ ⊥ := differentIdeal_ne_bot
  have hp0 : (p : 𝓞 E) ≠ 0 := by exact_mod_cast hp.out.ne_zero
  obtain ⟨a, ha⟩ := IsDedekindDomain.exists_sup_span_eq (I := D * Ideal.span {(p : 𝓞 E)}) (J := D)
    Ideal.mul_le_left (by
      rw [Ne, Ideal.zero_eq_bot, Ideal.mul_eq_bot, not_or]
      exact ⟨hD0, by rwa [Ideal.span_singleton_eq_bot]⟩)
  obtain ⟨δ, hδD, hδ0, hsup⟩ : ∃ δ ∈ D, δ ≠ 0 ∧ D * Ideal.span {(p : 𝓞 E)} ⊔ Ideal.span {δ} = D := by
    by_cases ha0 : a = 0
    · obtain ⟨d, hdD, hd0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hD0
      refine ⟨d, hdD, hd0, ?_⟩
      rw [ha0, Ideal.span_singleton_eq_bot.mpr rfl, sup_bot_eq] at ha
      rw [ha]
      exact sup_eq_left.mpr ((Ideal.span_singleton_le_iff_mem _).mpr hdD)
    · refine ⟨a, ?_, ha0, ha⟩
      rw [← ha]
      exact Ideal.mem_sup_right (Ideal.mem_span_singleton_self a)
  have hdec : ∀ x ∈ D, ∃ y ∈ D, ∃ z, x = (p : 𝓞 E) * y + z * δ := by
    intro x hx
    rw [← hsup, Submodule.mem_sup] at hx
    obtain ⟨u, hu, v, hv, rfl⟩ := hx
    obtain ⟨y, hy, rfl⟩ := (Submodule.mem_mul_span_singleton).mp hu
    obtain ⟨z, rfl⟩ := Ideal.mem_span_singleton'.mp hv
    exact ⟨y, hy, z, by ring⟩
  have hfin : Finite (𝓞 E ⧸ Ideal.span {δ}) :=
    Ring.HasFiniteQuotients.finiteQuotient (by rwa [Ne, Ideal.span_singleton_eq_bot])
  set H := D.map (Ideal.Quotient.mk (Ideal.span {δ})) with hH
  have hsurj : Function.Surjective (fun h : H => (p : ℕ) • h) := by
    rintro ⟨h, hh⟩
    obtain ⟨x, hx, rfl⟩ := (Ideal.mem_map_iff_of_surjective _ Ideal.Quotient.mk_surjective).mp hh
    obtain ⟨y, hy, z, rfl⟩ := hdec x hx
    refine ⟨⟨Ideal.Quotient.mk _ y, Ideal.mem_map_of_mem _ hy⟩, ?_⟩
    apply Subtype.ext
    simp [Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton'.mpr ⟨z, rfl⟩), nsmul_eq_mul]
  have hinj : Function.Injective (fun h : H => (p : ℕ) • h) := Finite.injective_iff_surjective.mpr hsurj
  refine ⟨δ, hδD, (Nat.card H : ℤ), ?_, ?_⟩
  · intro hdvd
    have hdvd' : p ∣ Nat.card H := by exact_mod_cast hdvd
    obtain ⟨g, hg⟩ := exists_prime_addOrderOf_dvd_card' (G := H) p hdvd'
    have h1 : (p : ℕ) • g = (p : ℕ) • (0 : H) := by rw [smul_zero, ← hg, addOrderOf_nsmul_eq_zero]
    have h2 := hinj h1
    rw [h2, addOrderOf_zero] at hg
    exact hp.out.ne_one hg.symm
  · intro x hx
    have hm : Ideal.Quotient.mk (Ideal.span {δ}) x ∈ H := Ideal.mem_map_of_mem _ hx
    have h0 : Nat.card H • (⟨_, hm⟩ : H) = 0 := card_nsmul_eq_zero'
    have h0' : Ideal.Quotient.mk (Ideal.span {δ}) ((Nat.card H : ℤ) * x) = 0 := by
      have := congrArg Subtype.val h0
      simpa [nsmul_eq_mul] using this
    obtain ⟨z, hz⟩ := Ideal.mem_span_singleton'.mp (Ideal.Quotient.eq_zero_iff_mem.mp h0')
    exact ⟨z, hz.symm⟩

theorem exists_den (E : Type) [Field E] [NumberField E] :
    ∃ n : ℤ, n ≠ 0 ∧ ∀ k, ∃ z : 𝓞 E, (n : E) * dualInt E k = z := by
  classical
  obtain ⟨y, hy, hint⟩ := exists_integral_multiples ℤ ℚ (Finset.univ.image (dualInt E))
  refine ⟨y, hy, fun k => ?_⟩
  have hk := hint (dualInt E k) (Finset.mem_image_of_mem _ (Finset.mem_univ k))
  refine ⟨⟨y • dualInt E k, hk⟩, ?_⟩
  show (y : E) * dualInt E k = y • dualInt E k
  rw [zsmul_eq_mul]

theorem exists_emb (E : Type) [Field E] [NumberField E] (F : IntermediateField ℚ ℂ)
    (hF : ∀ (τ : E →+* ℂ) (a : E), τ a ∈ F) {Ω : Type} [Field Ω] (j : F →+* Ω) (σ : E →+* Ω) :
    ∃ τ : E →+* ℂ, σ = j.comp (τ.codRestrict F (hF τ)) := by
  classical
  haveI : CharZero Ω := (RingHom.charZero_iff σ.injective).mp inferInstance
  let Φ : (E →+* ℂ) → (E →+* Ω) := fun τ => j.comp (τ.codRestrict F (hF τ))
  have hinj : Function.Injective Φ := by
    intro τ₁ τ₂ h
    ext a
    have h1 := RingHom.congr_fun h a
    have h2 := j.injective h1
    simpa using congrArg Subtype.val h2
  have hle : Fintype.card (E →+* Ω) ≤ Module.finrank ℚ E := by
    rw [← Nat.card_eq_fintype_card, Nat.card_congr (RingHom.equivRatAlgHom E Ω)]
    exact card_algHom_le_finrank ℚ E Ω
  have hcard : Fintype.card (E →+* ℂ) = Fintype.card (E →+* Ω) := by
    apply le_antisymm (Fintype.card_le_of_injective Φ hinj)
    rw [NumberField.Embeddings.card E ℂ]
    exact hle
  obtain ⟨τ, hτ⟩ := ((Fintype.bijective_iff_injective_and_card Φ).mpr ⟨hinj, hcard⟩).2 σ
  exact ⟨τ, hτ.symm⟩

section Chart

variable {A Ω : Type} [CommRing A] [Field Ω] [Algebra A Ω] {E : Type} [Field E] [NumberField E]
  {c : E ≃+* E} {p R N : ℕ} {V : Type} [AddCommGroup V] [Module Ω V] [Module A V] [IsScalarTower A Ω V]
  (D : HTChart A Ω c p R N V)

theorem om'_le : D.om' ≤ D.om := by
  refine sup_le (Submodule.span_le.2 ?_) ?_
  · rintro _ ⟨x, rfl⟩; exact D.h_mem x
  · rintro _ ⟨x, hx, rfl⟩; exact D.om.smul_mem _ hx

theorem smul_mem_om' {x : V} (hx : x ∈ D.om) : ((p : A) ^ R) • x ∈ D.om' :=
  Submodule.mem_sup_right ⟨x, hx, rfl⟩

theorem om'_fg [IsNoetherianRing A] : D.om'.FG := by
  exact Submodule.FG.of_le D.om_lat.fg (om'_le D)

theorem factor_om' (m : Ideal A) [hm : m.IsPrime] (hp : (p : A) ∉ m) :
    ∃ (N : Type) (_ : AddCommGroup N) (_ : Module A N) (_ : Module.Projective A N)
      (f : D.om' →ₗ[A] N) (g : N →ₗ[A] D.om') (t : A), t ∉ m ∧ ∀ x, g (f x) = t • x :=
  ⟨D.om, inferInstance, inferInstance, D.om_proj, Submodule.inclusion (om'_le D),
    (((p : A) ^ R) • LinearMap.id : V →ₗ[A] V).restrict fun _ hx => smul_mem_om' D hx, (p : A) ^ R,
    fun h => hp (hm.mem_of_pow_mem _ h), fun _ => rfl⟩

private theorem integralBasis_repr_eq_trace_mul_dualInt (z : E) (k : Module.Free.ChooseBasisIndex ℤ (𝓞 E)) :
    (integralBasis E).repr z k = Algebra.trace ℚ E (z * dualInt E k) := by
  classical
  have hd : ∀ i, Algebra.trace ℚ E (integralBasis E i * dualInt E k) = if i = k then 1 else 0 := by
    intro i
    have := (Algebra.traceForm ℚ E).apply_dualBasis_right (traceForm_nondegenerate ℚ E)
      (Algebra.traceForm_isSymm ℚ) (integralBasis E) i k
    simpa [dualInt, Algebra.traceForm_apply] using this
  conv_rhs => rw [← (integralBasis E).sum_repr z]
  rw [Finset.sum_mul, map_sum]
  simp only [smul_mul_assoc, map_smul, hd, smul_eq_mul, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq', Finset.mem_univ, if_true]

private theorem sum_dualInt_mul_integralBasis_eq_one : ∑ k, dualInt E k * integralBasis E k = 1 := by
  classical
  have key : ∀ y : E, Algebra.traceForm ℚ E (∑ k, dualInt E k * integralBasis E k - 1) y = 0 := by
    intro y
    rw [Algebra.traceForm_apply, sub_mul, one_mul, map_sub, Finset.sum_mul, map_sum,
      Algebra.trace_eq_matrix_trace (integralBasis E) y, Matrix.trace, sub_eq_zero]
    apply Finset.sum_congr rfl
    intro k _
    rw [Matrix.diag_apply, Algebra.leftMulMatrix_eq_repr_mul, integralBasis_repr_eq_trace_mul_dualInt]
    congr 1
    ring
  exact sub_eq_zero.mp ((traceForm_nondegenerate ℚ E).1 _ key)

private theorem coe_mul_dualInt_eq_sum (a : 𝓞 E) (j : Module.Free.ChooseBasisIndex ℤ (𝓞 E)) :
    (a : E) * dualInt E j = ∑ l, ((RingOfIntegers.basis E).repr (a * RingOfIntegers.basis E l) j : E) *
      dualInt E l := by
  classical
  set db := (Algebra.traceForm ℚ E).dualBasis (traceForm_nondegenerate ℚ E) (integralBasis E)
  have hdb : ∀ l, dualInt E l = db l := fun l => rfl
  conv_lhs => rw [← db.sum_repr ((a : E) * dualInt E j)]
  apply Finset.sum_congr rfl
  intro l _
  rw [LinearMap.BilinForm.dualBasis_repr_apply, Algebra.traceForm_apply, ← hdb]
  have ht : Algebra.trace ℚ E ((a : E) * dualInt E j * integralBasis E l) =
      ((RingOfIntegers.basis E).repr (a * RingOfIntegers.basis E l) j : ℚ) := by
    rw [show (a : E) * dualInt E j * integralBasis E l = ((a : E) * integralBasis E l) * dualInt E j by ring,
      ← integralBasis_repr_eq_trace_mul_dualInt, integralBasis_apply, show (a : E) = algebraMap (𝓞 E) E a from rfl, ← map_mul,
      integralBasis_repr_apply]
    simp
  rw [ht, Algebra.smul_def]
  simp

private theorem rho_mul_eigProj' {K L : Type} [Field K] [AddCommGroup L] [Module K L]
    (ρ : 𝓞 E →+* Module.End K L) (σ : E →+* K) (a : 𝓞 E) :
    ρ a * eigProj ρ σ = σ (a : E) • eigProj ρ σ := by
  classical
  calc ρ a * eigProj ρ σ = ∑ l, σ (dualInt E l) • ρ (a * RingOfIntegers.basis E l) := by
        unfold eigProj
        rw [Finset.mul_sum]
        simp only [mul_smul_comm, map_mul]
    _ = ∑ l, σ (dualInt E l) • ∑ j, ((RingOfIntegers.basis E).repr (a * RingOfIntegers.basis E l) j : K) •
          ρ (RingOfIntegers.basis E j) := by
        apply Finset.sum_congr rfl
        intro l _
        conv_lhs => rw [← (RingOfIntegers.basis E).sum_repr (a * RingOfIntegers.basis E l)]
        simp only [map_sum, map_zsmul, Int.cast_smul_eq_zsmul]
    _ = ∑ j, (∑ l, ((RingOfIntegers.basis E).repr (a * RingOfIntegers.basis E l) j : K) * σ (dualInt E l)) •
          ρ (RingOfIntegers.basis E j) := by
        simp only [Finset.smul_sum, smul_smul, Finset.sum_smul]
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro j _
        apply Finset.sum_congr rfl
        intro l _
        rw [mul_comm]
    _ = ∑ j, (σ (a : E) * σ (dualInt E j)) • ρ (RingOfIntegers.basis E j) := by
        apply Finset.sum_congr rfl
        intro j _
        rw [← map_mul, coe_mul_dualInt_eq_sum, map_sum]
        simp only [map_mul, map_intCast]
    _ = σ (a : E) • eigProj ρ σ := by
        unfold eigProj
        rw [Finset.smul_sum]
        simp only [smul_smul]

private theorem eigProj_eq_self_of_eigenvector {K L : Type} [Field K] [AddCommGroup L] [Module K L]
    (ρ : 𝓞 E →+* Module.End K L) (σ : E →+* K) (x : L) (hx : ∀ a : 𝓞 E, ρ a x = σ (a : E) • x) :
    eigProj ρ σ x = x := by
  classical
  unfold eigProj
  simp only [LinearMap.sum_apply, LinearMap.smul_apply, hx, smul_smul]
  rw [← Finset.sum_smul]
  have h1 : ∑ k, σ (dualInt E k) * σ ((RingOfIntegers.basis E k : 𝓞 E) : E) = 1 := by
    rw [← map_one σ, ← sum_dualInt_mul_integralBasis_eq_one, map_sum]
    apply Finset.sum_congr rfl
    intro k _
    rw [integralBasis_apply, map_mul]
  rw [h1, one_smul]

private theorem eigProj_idem {K L : Type} [Field K] [AddCommGroup L] [Module K L]
    (ρ : 𝓞 E →+* Module.End K L) (σ : E →+* K) (x : L) :
    eigProj ρ σ (eigProj ρ σ x) = eigProj ρ σ x := by
  apply eigProj_eq_self_of_eigenvector
  intro a
  rw [← Module.End.mul_apply, rho_mul_eigProj']
  rfl

theorem factor_omHT (m : Ideal A) [hm : m.IsPrime] (hp : (p : A) ∉ m) (σ : E →+* Ω) (t : A) (ht : t ∉ m)
    (hσ : ∀ k, algebraMap A Ω t * σ (dualInt E k) ∈ (algebraMap A Ω).range) :
    ∃ (N : Type) (_ : AddCommGroup N) (_ : Module A N) (_ : Module.Projective A N)
      (f : D.omHT σ →ₗ[A] N) (g : N →ₗ[A] D.omHT σ) (t : A), t ∉ m ∧ ∀ x, g (f x) = t • x := by
  classical
  obtain ⟨N', _, _, _, f', g', t', ht', hfg'⟩ := factor_om' D m hp
  have hst : ∀ (a : 𝓞 E), ∀ x ∈ D.om', D.ρΩ a x ∈ D.om' := by
    intro a x hx
    unfold HTChart.om' at hx ⊢
    obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.mp hx
    clear hx
    rw [map_add]
    apply Submodule.add_mem
    · induction hy using Submodule.span_induction with
      | mem w hw =>
        obtain ⟨x', rfl⟩ := hw
        obtain ⟨y', hy', he⟩ := D.h_lin a x'
        have hrw : D.ρΩ a (D.h x') = D.h (a • x') - p ^ R • y' := by
          rw [he]
          abel
        rw [hrw]
        apply Submodule.sub_mem
        · exact Submodule.mem_sup_left (Submodule.subset_span ⟨_, rfl⟩)
        · apply Submodule.mem_sup_right
          refine ⟨y', hy', ?_⟩
          simp only [LinearMap.smul_apply, LinearMap.id_apply, ← Nat.cast_pow, Nat.cast_smul_eq_nsmul]
      | zero => simp
      | add u v _ _ hu hv =>
        rw [map_add]
        exact Submodule.add_mem _ hu hv
      | smul c u _ hu =>
        rw [LinearMap.map_smul_of_tower]
        exact Submodule.smul_mem _ c hu
    · obtain ⟨z', hz', rfl⟩ := hz
      apply Submodule.mem_sup_right
      refine ⟨D.ρΩ a z', D.om_stable a z' hz', ?_⟩
      simp only [LinearMap.smul_apply, LinearMap.id_apply, LinearMap.map_smul_of_tower]
  have hP : ∀ x ∈ D.om', t • eigProj D.ρΩ σ x ∈ D.om' := by
    intro x hx
    unfold eigProj
    rw [LinearMap.sum_apply, Finset.smul_sum]
    apply Submodule.sum_mem
    intro k _
    obtain ⟨a, ha⟩ := hσ k
    rw [LinearMap.smul_apply, ← algebraMap_smul Ω t, smul_smul, ← ha, algebraMap_smul]
    exact Submodule.smul_mem _ a (hst _ x hx)
  have hmem : ∀ x : D.omHT σ, ∃ y ∈ D.om', eigProj D.ρΩ σ y = (x : V) := by
    rintro ⟨x, hx⟩
    simp only [HTChart.omHT, eigQuot, Submodule.mem_map] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    exact ⟨y, hy, rfl⟩
  have hf1 : ∀ x : D.omHT σ, (t • (D.omHT σ).subtype) x ∈ D.om' := by
    intro x
    obtain ⟨y, hy, hyx⟩ := hmem x
    rw [LinearMap.smul_apply, Submodule.subtype_apply, ← hyx]
    exact hP y hy
  have hg1 : ∀ y : D.om', (((eigProj D.ρΩ σ).restrictScalars A).comp D.om'.subtype) y ∈ D.omHT σ :=
    fun y => Submodule.mem_map_of_mem y.2
  refine ⟨N', inferInstance, inferInstance, inferInstance,
    f'.comp (LinearMap.codRestrict D.om' (t • (D.omHT σ).subtype) hf1),
    (LinearMap.codRestrict (D.omHT σ) (((eigProj D.ρΩ σ).restrictScalars A).comp D.om'.subtype) hg1).comp g',
    t' * t, fun h => ?_, fun x => ?_⟩
  · rcases hm.mem_or_mem h with h | h
    exacts [ht' h, ht h]
  · apply Subtype.ext
    obtain ⟨y, hy, hyx⟩ := hmem x
    have hx : eigProj D.ρΩ σ (x : V) = x := by
      rw [← hyx, eigProj_idem]
    simp only [LinearMap.comp_apply, hfg', map_smul, LinearMap.codRestrict_apply, Submodule.coe_smul,
      LinearMap.smul_apply, Submodule.subtype_apply, LinearMap.restrictScalars_apply,
      LinearMap.map_smul_of_tower, hx, mul_smul]

end Chart

theorem eigProj_dual {Ω L : Type} [Field Ω] [AddCommGroup L] [Module Ω L] {E : Type} [Field E] [NumberField E]
    (ρ : 𝓞 E →+* Module.End Ω L) (ρ' : 𝓞 E →+* Module.End Ω (Module.Dual Ω L))
    (h : ∀ a w, ρ' a w = w ∘ₗ ρ a) (σ : E →+* Ω) (w : Module.Dual Ω L) (e : L) :
    eigProj ρ' σ w e = w (eigProj ρ σ e) := by
  simp [eigProj, h]

theorem nonempty_equiv_dual {A Ω L : Type} [CommRing A] [Field Ω] [Algebra A Ω] [AddCommGroup L] [Module Ω L]
    {E : Type} [Field E] [NumberField E] (ρ : 𝓞 E →+* Module.End Ω L) (ρ' : 𝓞 E →+* Module.End Ω (Module.Dual Ω L))
    (h : ∀ a w, ρ' a w = w ∘ₗ ρ a) (σ : E →+* Ω) (X : Submodule A (Module.Dual Ω L)) (W : Submodule Ω L)
    (hW : W = eigSp ρ σ) :
    Nonempty (eigQuot ρ' σ X ≃ₗ[A] X.map (W.dualRestrict.restrictScalars A)) := by
  classical
  unfold eigQuot
  set F := (eigProj ρ' σ).restrictScalars A with hF
  set G := W.dualRestrict.restrictScalars A with hG
  have hker : ∀ w : Module.Dual Ω L, F w = 0 ↔ G w = 0 := by
    intro w
    constructor
    · intro hw
      ext ⟨x, hx⟩
      have hxW : ∀ a : 𝓞 E, ρ a x = σ (a : E) • x := by
        intro a
        rw [hW] at hx
        have := (Submodule.mem_iInf _).mp hx a
        rw [LinearMap.mem_ker, LinearMap.sub_apply, sub_eq_zero] at this
        simpa using this
      have h1 := congrArg (fun f : Module.Dual Ω L => f x) hw
      simp only [hF, LinearMap.restrictScalars_apply, eigProj_dual ρ ρ' h σ w x, eigProj_eq_self_of_eigenvector ρ σ x hxW,
        LinearMap.zero_apply] at h1
      simpa [hG, Submodule.dualRestrict_apply] using h1
    · intro hw
      ext e
      simp only [hF, LinearMap.restrictScalars_apply, eigProj_dual ρ ρ' h σ w e, LinearMap.zero_apply]
      have hPe : eigProj ρ σ e ∈ W := by
        rw [hW]
        apply (Submodule.mem_iInf _).mpr
        intro a
        rw [LinearMap.mem_ker, LinearMap.sub_apply, ← Module.End.mul_apply, rho_mul_eigProj']
        simp
      have := congrArg (fun f : Module.Dual Ω W => f ⟨_, hPe⟩) hw
      simpa [hG, Submodule.dualRestrict_apply] using this
  have hk : LinearMap.ker (F.comp X.subtype) = LinearMap.ker (G.comp X.subtype) := by
    ext x
    simp only [LinearMap.mem_ker, LinearMap.comp_apply, Submodule.subtype_apply]
    exact hker x
  have h1 : LinearMap.range (F.comp X.subtype) = X.map F := by
    rw [LinearMap.range_comp, Submodule.range_subtype]
  have h2 : LinearMap.range (G.comp X.subtype) = X.map G := by
    rw [LinearMap.range_comp, Submodule.range_subtype]
  exact ⟨(LinearEquiv.ofEq _ _ h1.symm).trans ((F.comp X.subtype).quotKerEquivRange.symm.trans
    ((Submodule.quotEquivOfEq _ _ hk).trans ((G.comp X.subtype).quotKerEquivRange.trans
      (LinearEquiv.ofEq _ _ h2))))⟩

end PositivityTheory.HtPt.Famproj
