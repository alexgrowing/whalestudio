import Mathlib
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

namespace GenericFreeness

open Module

universe u

variable {A : Type u} [CommRing A]

def IsGenericallyFree (A : Type u) [CommRing A] (M : Type*) [AddCommGroup M] [Module A M] : Prop :=
  ∃ f : A, f ≠ 0 ∧ Module.Free (Localization.Away f) (LocalizedModule (Submonoid.powers f) M)

theorem free_iff_of_isLocalizedModule (f : A) {M N : Type*} [AddCommGroup M] [Module A M]
    [AddCommGroup N] [Module A N] (g : M →ₗ[A] N) [IsLocalizedModule (Submonoid.powers f) g]
    (Rf : Type*) [CommRing Rf] [Algebra A Rf] [IsLocalization.Away f Rf] [Module Rf N]
    [IsScalarTower A Rf N] :
    Module.Free Rf N ↔ Module.Free (Localization.Away f) (LocalizedModule (Submonoid.powers f) M) := by
  let e₁ : Localization.Away f ≃+* Rf :=
    (IsLocalization.algEquiv (Submonoid.powers f) (Localization.Away f) Rf).toRingEquiv
  let e₂ : LocalizedModule (Submonoid.powers f) M ≃ₗ[A] N := IsLocalizedModule.iso _ g
  have key : ∀ (r : Localization.Away f) (x : LocalizedModule (Submonoid.powers f) M),
      e₂ (r • x) = e₁ r • e₂ x := by
    intro r x
    obtain ⟨⟨a, s⟩, rfl⟩ := IsLocalization.mk'_surjective (Submonoid.powers f) r
    have hs := IsLocalizedModule.map_units g s
    rw [Module.End.isUnit_iff] at hs
    apply hs.1
    simp only [Module.algebraMap_end_apply]
    have h1 : (s : A) • IsLocalization.mk' (Localization.Away f) a s = algebraMap A _ a := by
      rw [Algebra.smul_def, IsLocalization.mk'_spec']
    have h2 : (s : A) • e₁ (IsLocalization.mk' (Localization.Away f) a s) = algebraMap A Rf a := by
      have : e₁ (IsLocalization.mk' (Localization.Away f) a s) = IsLocalization.mk' Rf a s :=
        IsLocalization.algEquiv_mk' _ _
      rw [this, Algebra.smul_def, IsLocalization.mk'_spec']
    rw [← map_smul, ← smul_assoc, h1, algebraMap_smul, ← smul_assoc, h2, algebraMap_smul, map_smul]
  haveI := RingHomInvPair.of_ringEquiv e₁
  haveI := RingHomInvPair.of_ringEquiv_symm e₁
  let e : LinearEquiv (e₁ : Localization.Away f →+* Rf) (LocalizedModule (Submonoid.powers f) M) N :=
    { e₂.toAddEquiv with map_smul' := fun r x ↦ key r x }
  exact (Module.Free.iff_of_equiv e).symm

theorem isLocalizedModule_powers_mul (a c : A) {M N P : Type*} [AddCommGroup M] [Module A M]
    {Ra : Type*} [CommRing Ra] [Algebra A Ra] [IsLocalization.Away a Ra]
    [AddCommGroup N] [Module A N] [Module Ra N] [IsScalarTower A Ra N]
    [AddCommGroup P] [Module A P] [Module Ra P] [IsScalarTower A Ra P]
    (g : M →ₗ[A] N) [IsLocalizedModule (Submonoid.powers a) g]
    (h : N →ₗ[Ra] P) [IsLocalizedModule (Submonoid.powers (algebraMap A Ra c)) h] :
    IsLocalizedModule (Submonoid.powers (a * c)) (h.restrictScalars A ∘ₗ g) := by
  have hh : IsLocalizedModule (Submonoid.powers c) (h.restrictScalars A) :=
    IsLocalizedModule.restrictScalars_powers c h
  have ha : IsUnit (algebraMap A (Module.End A P) a) := by
    obtain ⟨u, hu⟩ := IsLocalization.Away.algebraMap_isUnit (S := Ra) a
    rw [Module.End.isUnit_iff]
    have hb : Function.Bijective (fun p : P ↦ (u : Ra) • p) := by
      refine ⟨fun p q hpq ↦ ?_, fun p ↦ ⟨(↑u⁻¹ : Ra) • p, ?_⟩⟩
      · have := congr_arg (fun x : P ↦ (↑u⁻¹ : Ra) • x) hpq
        simpa only [smul_smul, Units.inv_mul, one_smul] using this
      · show (u : Ra) • ((↑u⁻¹ : Ra) • p) = p
        rw [smul_smul, Units.mul_inv, one_smul]
    convert hb using 1
    funext p
    simp [hu]
  have hc : IsUnit (algebraMap A (Module.End A P) c) :=
    hh.map_units ⟨c, Submonoid.mem_powers c⟩
  constructor
  · rintro ⟨_, k, rfl⟩
    show IsUnit (algebraMap A (Module.End A P) ((a * c) ^ k))
    rw [map_pow, map_mul]
    exact (ha.mul hc).pow k
  · intro y
    obtain ⟨⟨n, ⟨_, j, rfl⟩⟩, hn⟩ := hh.surj y
    obtain ⟨⟨m, ⟨_, i, rfl⟩⟩, hm⟩ := IsLocalizedModule.surj (Submonoid.powers a) g n
    refine ⟨⟨(a ^ j * c ^ i) • m, ⟨(a * c) ^ (i + j), i + j, rfl⟩⟩, ?_⟩
    simp only [Submonoid.smul_def] at hn hm ⊢
    have e1 : (h.restrictScalars A ∘ₗ g) ((a ^ j * c ^ i) • m) =
        (a ^ j * c ^ i * a ^ i) • (h.restrictScalars A) n := by
      rw [LinearMap.comp_apply, map_smul, ← hm, map_smul, map_smul, smul_smul]
    rw [e1, ← hn, smul_smul]
    congr 1
    ring
  · intro m₁ m₂ e
    obtain ⟨⟨_, j, rfl⟩, hj⟩ := hh.exists_of_eq e
    simp only [Submonoid.smul_def] at hj
    rw [← map_smul, ← map_smul] at hj
    obtain ⟨⟨_, i, rfl⟩, hi⟩ := IsLocalizedModule.exists_of_eq (S := Submonoid.powers a) (f := g) hj
    refine ⟨⟨(a * c) ^ (i + j), i + j, rfl⟩, ?_⟩
    simp only [Submonoid.smul_def] at hi ⊢
    have : (a * c) ^ (i + j) = a ^ j * c ^ i * (a ^ i * c ^ j) := by ring
    rw [this]
    simp only [mul_smul (a ^ j * c ^ i), mul_smul (a ^ i) (c ^ j), hi]

theorem free_away_mul {f : A} (g : A) {M : Type*} [AddCommGroup M] [Module A M]
    (hf : Module.Free (Localization.Away f) (LocalizedModule (Submonoid.powers f) M)) :
    Module.Free (Localization.Away (f * g)) (LocalizedModule (Submonoid.powers (f * g)) M) := by
  let Ra := Localization.Away f
  let N := LocalizedModule (Submonoid.powers f) M
  let T := Localization.Away (algebraMap A Ra g)
  let P := LocalizedModule (Submonoid.powers (algebraMap A Ra g)) N
  have hP : Module.Free T P :=
    Module.free_of_isLocalizedModule (Submonoid.powers (algebraMap A Ra g))
      (LocalizedModule.mkLinearMap (Submonoid.powers (algebraMap A Ra g)) N)
  haveI := isLocalizedModule_powers_mul f g (LocalizedModule.mkLinearMap (Submonoid.powers f) M)
    (LocalizedModule.mkLinearMap (Submonoid.powers (algebraMap A Ra g)) N)
  exact (free_iff_of_isLocalizedModule (f * g)
    ((LocalizedModule.mkLinearMap (Submonoid.powers (algebraMap A Ra g)) N).restrictScalars A ∘ₗ
      LocalizedModule.mkLinearMap (Submonoid.powers f) M) T).1 hP

theorem IsGenericallyFree.of_linearEquiv {M M' : Type*} [AddCommGroup M] [Module A M] [AddCommGroup M']
    [Module A M'] (e : M ≃ₗ[A] M') (hM : IsGenericallyFree A M) : IsGenericallyFree A M' := by
  obtain ⟨f, hf, hfree⟩ := hM
  refine ⟨f, hf, ?_⟩
  exact (free_iff_of_isLocalizedModule f
    (LocalizedModule.mkLinearMap (Submonoid.powers f) M ∘ₗ e.symm.toLinearMap) (Localization.Away f)).1 hfree

theorem isGenericallyFree_of_smul_eq_zero {M : Type*} [AddCommGroup M] [Module A M] (a : A) (ha : a ≠ 0)
    (h : ∀ m : M, a • m = 0) : IsGenericallyFree A M := by
  refine ⟨a, ha, ?_⟩
  have h0 : ∀ x : LocalizedModule (Submonoid.powers a) M, x = 0 := fun x ↦ by
    induction x using LocalizedModule.induction_on with
    | h m s =>
      exact LocalizedModule.eq_zero_of_smul_eq_zero a (Submonoid.mem_powers a) _
        (by rw [LocalizedModule.smul'_mk, h, LocalizedModule.zero_mk])
  haveI : Subsingleton (LocalizedModule (Submonoid.powers a) M) := ⟨fun x y ↦ by rw [h0 x, h0 y]⟩
  infer_instance

theorem isGenericallyFree_of_free [Nontrivial A] {M : Type*} [AddCommGroup M] [Module A M] [Module.Free A M] :
    IsGenericallyFree A M :=
  ⟨1, one_ne_zero, Module.free_of_isLocalizedModule (Submonoid.powers (1 : A))
    (LocalizedModule.mkLinearMap (Submonoid.powers (1 : A)) M)⟩

theorem IsGenericallyFree.of_injective [IsDomain A] {N M : Type*} [AddCommGroup N] [Module A N] [AddCommGroup M]
    [Module A M] (i : N →ₗ[A] M) (hi : Function.Injective i) (a : A) (ha : a ≠ 0)
    (hsat : ∀ m : M, ∃ k : ℕ, a ^ k • m ∈ LinearMap.range i) (hN : IsGenericallyFree A N) :
    IsGenericallyFree A M := by
  obtain ⟨f, hf, hfree⟩ := hN
  have hfree' := free_away_mul a hfree
  set F := f * a with hF
  refine ⟨F, mul_ne_zero hf ha, ?_⟩
  haveI : IsLocalizedModule (Submonoid.powers F) (LocalizedModule.mkLinearMap (Submonoid.powers F) M ∘ₗ i) := by
    constructor
    · exact IsLocalizedModule.map_units (LocalizedModule.mkLinearMap (Submonoid.powers F) M)
    · intro y
      obtain ⟨⟨m, s⟩, hms⟩ := IsLocalizedModule.surj (Submonoid.powers F)
        (LocalizedModule.mkLinearMap (Submonoid.powers F) M) y
      obtain ⟨k, n, hn⟩ := hsat m
      refine ⟨⟨f ^ k • n, ⟨F ^ k, k, rfl⟩ * s⟩, ?_⟩
      simp only [Submonoid.smul_def, Submonoid.coe_mul, LinearMap.coe_comp, Function.comp_apply,
        map_smul, hn] at hms ⊢
      rw [mul_smul, hms, ← map_smul, smul_smul, hF, mul_pow]
      exact map_smul _ _ _
    · intro n₁ n₂ e
      obtain ⟨c, hc⟩ := IsLocalizedModule.exists_of_eq (S := Submonoid.powers F)
        (f := LocalizedModule.mkLinearMap (Submonoid.powers F) M) e
      refine ⟨c, hi ?_⟩
      simpa only [Submonoid.smul_def, map_smul] using hc
  exact (free_iff_of_isLocalizedModule F
    (LocalizedModule.mkLinearMap (Submonoid.powers F) M ∘ₗ i) (Localization.Away F)).2 hfree'

theorem IsGenericallyFree.of_exact [IsDomain A] {N₁ N₂ N₃ : Type*} [AddCommGroup N₁] [Module A N₁]
    [AddCommGroup N₂] [Module A N₂] [AddCommGroup N₃] [Module A N₃] (i : N₁ →ₗ[A] N₂) (p : N₂ →ₗ[A] N₃)
    (hi : Function.Injective i) (hp : Function.Surjective p) (hex : Function.Exact i p)
    (h₁ : IsGenericallyFree A N₁) (h₃ : IsGenericallyFree A N₃) : IsGenericallyFree A N₂ := by
  obtain ⟨f₁, hf₁, hfree₁⟩ := h₁
  obtain ⟨f₃, hf₃, hfree₃⟩ := h₃
  have free₁ := free_away_mul f₃ hfree₁
  have free₃ := free_away_mul f₁ hfree₃
  rw [mul_comm f₃ f₁] at free₃
  set f := f₁ * f₃
  refine ⟨f, mul_ne_zero hf₁ hf₃, ?_⟩
  let S := Submonoid.powers f
  let iL : LocalizedModule S N₁ →ₗ[Localization.Away f] LocalizedModule S N₂ :=
    (IsLocalizedModule.map S (LocalizedModule.mkLinearMap S N₁) (LocalizedModule.mkLinearMap S N₂) i).extendScalarsOfIsLocalization S (Localization.Away f)
  let pL : LocalizedModule S N₂ →ₗ[Localization.Away f] LocalizedModule S N₃ :=
    (IsLocalizedModule.map S (LocalizedModule.mkLinearMap S N₂) (LocalizedModule.mkLinearMap S N₃) p).extendScalarsOfIsLocalization S (Localization.Away f)
  have ex : Function.Exact iL pL := LocalizedModule.map_exact S i p hex
  have hiL : Function.Injective iL := IsLocalizedModule.map_injective S _ _ i hi
  have hpL : Function.Surjective pL := IsLocalizedModule.map_surjective S _ _ p hp
  obtain ⟨s, hs⟩ := Module.projective_lifting_property pL LinearMap.id hpL
  exact Module.Free.of_equiv (ex.splitSurjectiveEquiv hiL ⟨s, hs⟩).1.symm

end GenericFreeness

end GroundTheory.Heights₂.Heights
