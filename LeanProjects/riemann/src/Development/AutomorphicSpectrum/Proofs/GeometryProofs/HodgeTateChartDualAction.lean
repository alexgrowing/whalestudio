import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsExtendLin

namespace GlobalTheory.CompanionTheory.Ar.Flat.HTL

open Module NumberField GlobalTheory.CompanionTheory.Ar.HT GlobalTheory.CompanionTheory.Ar.Flat

theorem eq_zero_of_forall_om' {A K : Type} [CommRing A] [Field K] [Algebra A K] [CharZero K] {E : Type} [Field E]
    [NumberField E] {c : E ≃+* E} {p R N : ℕ} [Fact p.Prime] {Li : Type} [AddCommGroup Li] [Module K Li]
    (D : HTChart A K c p R N (Module.Dual K Li)) {e : Li} (he : ∀ w ∈ D.om', w e = 0) : e = 0 := by
  have hp : (p : K) ≠ 0 := Nat.cast_ne_zero.2 (Fact.out : p.Prime).ne_zero
  have h1 : ∀ w ∈ D.om, w e = 0 := by
    intro w hw
    have hm : ((p : A) ^ R) • w ∈ D.om' := Submodule.mem_sup_right ⟨w, hw, rfl⟩
    have h := he _ hm
    rw [LinearMap.smul_apply, Algebra.smul_def, map_pow, map_natCast] at h
    exact (mul_eq_zero.1 h).resolve_left (pow_ne_zero _ hp)
  have h2 : Submodule.span K (D.om : Set (Module.Dual K Li)) ≤ LinearMap.ker (Module.Dual.eval K Li e) :=
    Submodule.span_le.2 fun w hw => h1 w hw
  rw [D.om_lat.span_eq_top] at h2
  exact (Module.forall_dual_apply_eq_zero_iff K e).1 fun w => h2 (Submodule.mem_top (x := w))

theorem exists_lift_retract : ∀ (A K : Type) [CommRing A] [IsDomain A] [IsNoetherianRing A] [Field K] [Algebra A K] [IsFractionRing A K] [CharZero K] (E : Type) [Field E] [NumberField E] (c : E ≃+* E) (hc : ∀ x, c (c x) = x) (p R N : ℕ) [Fact p.Prime] (Li : Type) [AddCommGroup Li] [Module K Li] (D : HTChart A K c p R N (Module.Dual K Li)) (ρ : 𝓞 E →+* Module.End K Li), (∀ (a : 𝓞 E) (w : Module.Dual K Li), D.ρΩ a w = w ∘ₗ ρ (RingOfIntegers.mapRingEquiv c a)) → ∀ (σ : E →+* K) (d : A) (m : ℕ) (i : Module.Dual A (D.omHT (σ.comp c.toRingHom)) →ₗ[A] (Fin N → A)), algebraMap A K d ≠ 0 → D.ExactMod σ m i → ∃ (J : Li →ₗ[K] (Fin N → K)) (Rr : (Fin N → K) →ₗ[K] Li), (∀ e ∈ HTL.latOn D (GlobalTheory.CompanionTheory.Ar.HT.eigSp ρ σ) (algebraMap A K d) (algebraMap A K).range, ∃ f : Module.Dual A (D.omHT (σ.comp c.toRingHom)), (∀ z : D.omHT (σ.comp c.toRingHom), algebraMap A K (f z) = algebraMap A K d * (z : Module.Dual K Li) e) ∧ ∀ l, J e l = algebraMap A K (i f l)) ∧ (∀ k, Rr (Pi.single k 1) ∈ HTL.latOn D (GlobalTheory.CompanionTheory.Ar.HT.eigSp ρ σ) (algebraMap A K d) (algebraMap A K).range) ∧ ∀ e ∈ HTL.latOn D (GlobalTheory.CompanionTheory.Ar.HT.eigSp ρ σ) (algebraMap A K d) (algebraMap A K).range, ∃ e' ∈ HTL.latOn D (GlobalTheory.CompanionTheory.Ar.HT.eigSp ρ σ) (algebraMap A K d) (algebraMap A K).range, Rr (J e) = e + ((p : K) ^ m) • e' := by
  intro A K _ _ _ _ _ _ _ E _ _ c hc p R N _ Li _ _ D ρ hact σ d m i hd hex
  classical
  have hττ : (σ.comp c.toRingHom).comp c.toRingHom = σ := by
    ext x
    simp [hc]
  have hinj := IsFractionRing.injective A K
  have hE : ∀ e ∈ eigSp ρ σ, ∀ w : Module.Dual K Li, eigProj D.ρΩ (σ.comp c.toRingHom) w e = w e :=
    fun e he w => eigProj_apply D ρ hc hact (σ.comp c.toRingHom) (by rw [hττ]; exact he) w
  have hvec0 : ∀ g : Module.Dual A (D.omHT (σ.comp c.toRingHom)), ∃ e ∈ eigSp ρ σ,
      ∀ z : D.omHT (σ.comp c.toRingHom),
        algebraMap A K d * (z : Module.Dual K Li) e = algebraMap A K (g z) := by
    intro g
    obtain ⟨e, he, hz⟩ := exists_vec D ρ hc hact (σ.comp c.toRingHom) g
    rw [hττ] at he
    refine ⟨(algebraMap A K d)⁻¹ • e, Submodule.smul_mem _ _ he, fun z => ?_⟩
    rw [map_smul, hz, smul_eq_mul, mul_inv_cancel_left₀ hd]
  choose vec hvecS hvec using hvec0
  have hmem : ∀ w ∈ D.om', ∃ z : D.omHT (σ.comp c.toRingHom),
      (z : Module.Dual K Li) = eigProj D.ρΩ (σ.comp c.toRingHom) w :=
    fun w hw => ⟨⟨_, w, hw, rfl⟩, rfl⟩
  have hsep : ∀ e ∈ eigSp ρ σ, (∀ z : D.omHT (σ.comp c.toRingHom), (z : Module.Dual K Li) e = 0) → e = 0 := by
    intro e he h
    refine eq_zero_of_forall_om' D fun w hw => ?_
    obtain ⟨z, hz⟩ := hmem w hw
    rw [← hE e he w, ← hz]
    exact h z
  have hun : ∀ e ∈ eigSp ρ σ, ∀ e' ∈ eigSp ρ σ, (∀ z : D.omHT (σ.comp c.toRingHom),
      algebraMap A K d * (z : Module.Dual K Li) e = algebraMap A K d * (z : Module.Dual K Li) e') → e = e' := by
    intro e he e' he' h
    refine sub_eq_zero.1 (hsep _ (Submodule.sub_mem _ he he') fun z => ?_)
    rw [map_sub, sub_eq_zero]
    exact mul_left_cancel₀ hd (h z)
  letI : Module A Li := Module.compHom Li (algebraMap A K)
  haveI : IsScalarTower A K Li := ⟨fun a k v => by
    change (a • k) • v = algebraMap A K a • (k • v)
    rw [Algebra.smul_def, mul_smul]⟩
  have hsmul : ∀ (a : A) (v : Li), a • v = algebraMap A K a • v := fun _ _ => rfl
  let vecL : Module.Dual A (D.omHT (σ.comp c.toRingHom)) →ₗ[A] Li :=
    { toFun := vec
      map_add' := fun g g' => hun _ (hvecS _) _ (Submodule.add_mem _ (hvecS g) (hvecS g')) fun z => by
        rw [hvec, map_add, mul_add, hvec, hvec, LinearMap.add_apply, map_add]
      map_smul' := fun a g => hun _ (hvecS _) _ (by
          rw [RingHom.id_apply, hsmul]
          exact Submodule.smul_mem _ _ (hvecS g)) fun z => by
        rw [hvec, RingHom.id_apply, hsmul, map_smul, smul_eq_mul, mul_left_comm, hvec, LinearMap.smul_apply,
          smul_eq_mul, map_mul] }
  have hvW : ∀ g, vec g ∈ latOn D (eigSp ρ σ) (algebraMap A K d) (algebraMap A K).range := fun g =>
    ⟨hvecS g, fun w hw => by
      obtain ⟨z, hz⟩ := hmem w hw
      rw [← hE _ (hvecS g) w, ← hz, hvec]
      exact ⟨_, rfl⟩⟩
  let Wsub : Submodule A Li :=
    { carrier := latOn D (eigSp ρ σ) (algebraMap A K d) (algebraMap A K).range
      add_mem' := fun {a b} ha hb => ⟨Submodule.add_mem _ ha.1 hb.1, fun w hw => by
        rw [map_add, mul_add]
        exact add_mem (ha.2 w hw) (hb.2 w hw)⟩
      zero_mem' := ⟨Submodule.zero_mem _, fun w _ => by
        rw [map_zero, mul_zero]
        exact zero_mem _⟩
      smul_mem' := fun a x hx => ⟨by
          rw [hsmul]
          exact Submodule.smul_mem _ _ hx.1, fun w hw => by
        rw [hsmul, map_smul, smul_eq_mul, mul_left_comm]
        exact mul_mem ⟨a, rfl⟩ (hx.2 w hw)⟩ }
  have hfe : ∀ e ∈ latOn D (eigSp ρ σ) (algebraMap A K d) (algebraMap A K).range,
      ∃ f : Module.Dual A (D.omHT (σ.comp c.toRingHom)),
        ∀ z : D.omHT (σ.comp c.toRingHom),
          algebraMap A K (f z) = algebraMap A K d * (z : Module.Dual K Li) e := by
    intro e he
    have h0 : ∀ z : D.omHT (σ.comp c.toRingHom), ∃ a : A,
        algebraMap A K a = algebraMap A K d * (z : Module.Dual K Li) e := by
      intro z
      obtain ⟨w, hw, hz⟩ := z.2
      have hz' : eigProj D.ρΩ (σ.comp c.toRingHom) w = (z : Module.Dual K Li) := hz
      rw [← hz', hE e he.1 w]
      exact he.2 w hw
    choose F hF using h0
    refine ⟨{ toFun := F, map_add' := fun x y => hinj ?_, map_smul' := fun a x => hinj ?_ }, hF⟩
    · rw [map_add, hF, hF, hF, Submodule.coe_add, LinearMap.add_apply, mul_add]
    · rw [RingHom.id_apply, smul_eq_mul, map_mul, hF, hF, Submodule.coe_smul, LinearMap.smul_apply,
        Algebra.smul_def, mul_left_comm]
  let Lv : Module.Dual A (D.omHT (σ.comp c.toRingHom)) →ₗ[A] Wsub := vecL.codRestrict Wsub hvW
  have hLv : Function.Bijective Lv := by
    constructor
    · intro g g' h
      have h' : vec g = vec g' := congrArg Subtype.val h
      ext z
      apply hinj
      rw [← hvec, ← hvec, h']
    · rintro ⟨e, he⟩
      obtain ⟨f, hf⟩ := hfe e he
      refine ⟨f, Subtype.ext ?_⟩
      change vec f = e
      exact hun _ (hvecS f) _ he.1 fun z => by rw [hvec, hf]
  let Leq := LinearEquiv.ofBijective Lv hLv
  have hLeq : ∀ (e : Li) (he : e ∈ Wsub), vec (Leq.symm ⟨e, he⟩) = e := fun e he =>
    congrArg Subtype.val (Leq.apply_symm_apply ⟨e, he⟩)
  obtain ⟨G, hG⟩ := exists_extend_lin (K := K) Wsub
    (((Algebra.linearMap A K).compLeft (Fin N)) ∘ₗ i ∘ₗ Leq.symm.toLinearMap)
  obtain ⟨⟨r, hr⟩, -⟩ := hex
  let Rr : (Fin N → K) →ₗ[K] Li := Fintype.linearCombination K fun k => vec (r (Pi.single k 1))
  have hRr : ∀ y : Fin N → A, Rr (fun l => algebraMap A K (y l)) = vec (r y) := by
    intro y
    have hy : y = ∑ k, y k • Pi.single k (1 : A) := by
      ext l
      simp [Finset.sum_apply, Pi.single_apply]
    have h1 : vec (r y) = vecL (r y) := rfl
    rw [h1]
    conv_rhs => rw [hy]
    rw [map_sum, map_sum]
    simp only [Rr, Fintype.linearCombination_apply, map_smul, hsmul]
    rfl
  refine ⟨G, Rr, fun e he => ?_, fun k => ?_, fun e he => ?_⟩
  · refine ⟨Leq.symm ⟨e, he⟩, fun z => ?_, fun l => ?_⟩
    · rw [← hvec, hLeq e he]
    · have := hG ⟨e, he⟩
      exact congrFun this l
  · have h1 : Rr (Pi.single k 1) = vec (r (Pi.single k 1)) := by
      simp [Rr, Fintype.linearCombination_apply_single]
    rw [h1]
    exact hvW _
  · obtain ⟨w', hw'⟩ := hr (Leq.symm ⟨e, he⟩)
    refine ⟨vec w', hvW w', ?_⟩
    have h1 : G e = fun l => algebraMap A K (i (Leq.symm ⟨e, he⟩) l) := hG ⟨e, he⟩
    have h2 : vec (r (i (Leq.symm ⟨e, he⟩))) = vecL (Leq.symm ⟨e, he⟩) + (((p : A) ^ m) • vecL w') := by
      change vecL _ = _
      rw [hw', map_add, map_smul]
    rw [h1, hRr, h2]
    change vec (Leq.symm ⟨e, he⟩) + _ = _
    rw [hLeq e he, hsmul, map_pow, map_natCast]
    rfl

end GlobalTheory.CompanionTheory.Ar.Flat.HTL
