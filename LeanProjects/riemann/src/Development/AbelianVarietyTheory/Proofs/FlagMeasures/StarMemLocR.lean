import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ChartGen
import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.MaxMass
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsLocalizedModuleSubtype
open NumberField Matrix GlobalTheory.Mass Formalism.HermitianLatticesTheory
open scoped ENNReal Classical

namespace GlobalTheory.Mass.Hyperplane

section Refl
variable {K V : Type} [Field K] [StarRing K] [AddCommGroup V] [Module K V]

theorem exists_refl (h : V →ₗ⋆[K] V →ₗ[K] K) (hs : ∀ x y, star (h x y) = h y x) (v : V) (a : K)
    (ha : a + star a = a * star a * h v v) :
    ∃ g ∈ isom h, (∀ x, g x = x - (a * h v x) • v) ∧ ∀ x, g.symm x = x - (star a * h v x) • v := by
  let f : K → V →ₗ[K] V := fun c => LinearMap.id - (c • h v).smulRight v
  have hf : ∀ c x, f c x = x - (c * h v x) • v := fun c x => by simp [f]
  have key : ∀ c d : K, c + d = c * d * h v v → f c ∘ₗ f d = LinearMap.id := by
    intro c d hcd
    ext x
    rw [LinearMap.comp_apply, hf, hf, map_sub, map_smul, smul_eq_mul, sub_sub, ← add_smul]
    have : d * h v x + c * (h v x - d * h v x * h v v) = 0 := by linear_combination (h v x) * hcd
    rw [this, zero_smul, sub_zero, LinearMap.id_apply]
  refine ⟨LinearEquiv.ofLinear (f a) (f (star a)) (key _ _ ha) (key _ _ (by linear_combination ha)), ?_,
    fun x => hf _ x, fun x => hf _ x⟩
  intro x y
  change h (f a x) (f a y) = h x y
  rw [hf, hf]
  simp only [map_sub, map_smul, LinearMap.map_smulₛₗ, LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul,
    starRingEnd_apply, star_mul', hs]
  linear_combination (-(h x v * h v y)) * ha

theorem exists_move (h : V →ₗ⋆[K] V →ₗ[K] K) (hs : ∀ x y, star (h x y) = h y x) (A : Subring K)
    (I : AddSubgroup K) (Λ : AddSubgroup V) (hA : ∀ a ∈ A, star a ∈ A) (hI : ∀ a ∈ A, ∀ x ∈ I, a * x ∈ I)
    (hU : ∀ a ∈ A, a ∉ I → star a ∉ I → a⁻¹ ∈ A) (e : K) (heA : e ∈ A) (he : e ∈ I) (he' : 1 - star e ∈ I)
    (hΛ : ∀ a ∈ A, ∀ x ∈ Λ, a • x ∈ Λ) (hh : ∀ x ∈ Λ, ∀ y ∈ Λ, h x y ∈ A) (u u' w : V) (hu : u ∈ Λ)
    (hu' : u' ∈ Λ) (hw : w ∈ Λ) (h1 : h u w ∉ I) (h2 : h u' w ∉ I) :
    ∃ g ∈ isom h, (∀ x ∈ Λ, g x ∈ Λ) ∧ (∀ x ∈ Λ, g.symm x ∈ Λ) ∧ ∀ x ∈ Λ, h u' (g x) - h u x ∈ I := by
  have hI' : ∀ a ∈ A, ∀ x ∈ I, x * a ∈ I := fun a ha x hx => mul_comm a x ▸ hI a ha x hx
  have one : (1 : K) ∉ I := fun H => h1 (by simpa using hI _ (hh u hu w hw) 1 H)
  have hd : e + star e ∉ I := fun H => one (by
    have := I.add_mem (I.sub_mem H he) he'
    simpa using this)
  have hd0 : e + star e ≠ 0 := fun H => hd (H ▸ I.zero_mem)
  have hds : star (e + star e) = e + star e := by rw [star_add, star_star, add_comm]
  have hdi : (e + star e)⁻¹ ∈ A := hU _ (A.add_mem heA (hA e heA)) hd (by rw [hds]; exact hd)
  obtain ⟨θ, hθA, hθI, hθ⟩ : ∃ θ ∈ A, θ ∈ I ∧ star θ = 1 - θ := by
    refine ⟨e * (e + star e)⁻¹, A.mul_mem heA hdi, hI' _ hdi _ he, ?_⟩
    rw [star_mul', star_inv₀, hds]
    field_simp
    ring
  have hθ' : 1 - θ ∈ A := A.sub_mem A.one_mem hθA
  set v : V := θ • (u - u') + (1 - θ) • w with hv
  have hvΛ : v ∈ Λ := Λ.add_mem (hΛ _ hθA _ (Λ.sub_mem hu hu')) (hΛ _ hθ' _ hw)
  have l1 : ∀ x ∈ Λ, h v x - (h u x - h u' x) ∈ I := by
    intro x hx
    have : h v x - (h u x - h u' x) = θ * (h w x - (h u x - h u' x)) := by
      simp only [hv, map_add, map_sub, LinearMap.map_smulₛₗ, LinearMap.sub_apply, LinearMap.add_apply,
        LinearMap.smul_apply, smul_eq_mul, starRingEnd_apply, hθ, map_one]
      ring
    rw [this]
    exact hI' _ (A.sub_mem (hh _ hw _ hx) (A.sub_mem (hh _ hu _ hx) (hh _ hu' _ hx))) _ hθI
  have l2 : ∀ x ∈ Λ, h x v - h x w ∈ I := by
    intro x hx
    have : h x v - h x w = θ * (h x (u - u') - h x w) := by
      simp only [hv, map_add, map_smul, smul_eq_mul]
      ring
    rw [this]
    exact hI' _ (A.sub_mem (hh _ hx _ (Λ.sub_mem hu hu')) (hh _ hx _ hw)) _ hθI
  set n := h v v with hn
  set γ := h u' v with hγ
  have hnA : n ∈ A := hh _ hvΛ _ hvΛ
  have hγA : γ ∈ A := hh _ hu' _ hvΛ
  have hns : star n = n := hs v v
  set b := (1 - θ) * (-γ) + θ * (n + star γ) with hb
  have hbs : star b = θ * (-star γ) + (1 - θ) * (n + γ) := by
    simp only [hb, star_add, star_mul', star_sub, star_neg, star_one, star_star, hθ, hns]
    ring
  have hbA : b ∈ A := A.add_mem (A.mul_mem hθ' (A.neg_mem hγA)) (A.mul_mem hθA (A.add_mem hnA (hA _ hγA)))
  have hbγ : b + γ ∈ I := by
    have : b + γ = θ * (γ + n + star γ) := by rw [hb]; ring
    rw [this]
    exact hI' _ (A.add_mem (A.add_mem hγA hnA) (hA _ hγA)) _ hθI
  have hbI : b ∉ I := fun H => h2 (by
    have := I.sub_mem (I.sub_mem hbγ H) (l2 _ hu')
    simpa [hγ] using this)
  have hbI' : star b ∉ I := fun H => h1 (by
    have h3 : θ * (γ + n + star γ) ∈ I := hI' _ (A.add_mem (A.add_mem hγA hnA) (hA _ hγA)) _ hθI
    have := I.sub_mem (I.sub_mem (I.add_mem H h3) (l1 _ hvΛ)) (l2 _ hu)
    convert this using 1
    rw [hbs]
    ring)
  have hb0 : b ≠ 0 := fun H => hbI (H ▸ I.zero_mem)
  have hb0' : star b ≠ 0 := fun H => hbI' (H ▸ I.zero_mem)
  have haA : b⁻¹ ∈ A := hU b hbA hbI hbI'
  obtain ⟨g, hg, g1, g2⟩ := exists_refl h hs v b⁻¹ (by
    have : h v v = b + star b := by rw [hbs, hb, ← hn]; ring
    rw [this, star_inv₀]
    field_simp
    ring)
  refine ⟨g, hg, fun x hx => ?_, fun x hx => ?_, fun x hx => ?_⟩
  · rw [g1]
    exact Λ.sub_mem hx (hΛ _ (A.mul_mem haA (hh _ hvΛ _ hx)) _ hvΛ)
  · rw [g2]
    exact Λ.sub_mem hx (hΛ _ (A.mul_mem (hA _ haA) (hh _ hvΛ _ hx)) _ hvΛ)
  · have : h u' (g x) - h u x = (h v x - (h u x - h u' x)) - (b⁻¹ * h v x) * (b + γ) := by
      rw [g1, map_sub, map_smul, smul_eq_mul, ← hγ]
      field_simp
      ring
    rw [this]
    exact I.sub_mem (l1 x hx) (hI _ (A.mul_mem haA (hh _ hvΛ _ hx)) _ hbγ)

end Refl

section Local
variable {K : Type} [Field K] [StarRing K]

noncomputable def cj (K : Type) [Field K] [StarRing K] : 𝓞 K →+* 𝓞 K := RingOfIntegers.mapRingHom (starRingEnd K)

theorem cj_coe (s : 𝓞 K) : algebraMap (𝓞 K) K (cj K s) = star (algebraMap (𝓞 K) K s) := rfl

theorem cj_cj (s : 𝓞 K) : cj K (cj K s) = s := by
  apply RingOfIntegers.coe_injective
  rw [cj_coe, cj_coe, star_star]

theorem mem_hcompl {P : Ideal (𝓞 K)} (hP : P.IsPrime) (s : 𝓞 K) :
    s ∈ hcompl (K := K) P ↔ s ∉ P ∧ cj K s ∉ P := by
  constructor
  · intro hs
    induction hs using Submonoid.closure_induction with
    | mem x hx => exact ⟨hx.1, hx.2 _ (cj_coe x)⟩
    | one => rw [map_one]; exact ⟨hP.one_notMem, hP.one_notMem⟩
    | mul x y _ _ hx hy =>
      rw [map_mul]
      exact ⟨fun H => (hP.mem_or_mem H).elim hx.1 hy.1, fun H => (hP.mem_or_mem H).elim hx.2 hy.2⟩
  · rintro ⟨h1, h2⟩
    refine Submonoid.subset_closure ⟨h1, fun t ht => ?_⟩
    rw [← cj_coe] at ht
    rw [RingOfIntegers.coe_injective ht]
    exact h2

theorem conjIdeal_eq (P : Ideal (𝓞 K)) : conjIdeal (K := K) P = P.comap (cj K) := by
  apply le_antisymm
  · rw [conjIdeal, Ideal.span_le]
    rintro r ⟨s, hs, hr⟩
    rw [← cj_coe] at hr
    rw [RingOfIntegers.coe_injective hr]
    change cj K (cj K s) ∈ P
    rwa [cj_cj]
  · intro r hr
    refine Ideal.subset_span ⟨cj K r, hr, ?_⟩
    rw [cj_coe, star_star]

theorem exists_idem {P : Ideal (𝓞 K)} (hP : P.IsMaximal) (hc : conjIdeal (K := K) P ≠ P) :
    ∃ e ∈ P, 1 - cj K e ∈ P := by
  rw [conjIdeal_eq] at hc
  have hm : (P.comap (cj K)).IsMaximal :=
    Ideal.comap_isMaximal_of_surjective _ fun s => ⟨cj K s, cj_cj s⟩
  have := hP.coprime_of_ne hm hc.symm
  obtain ⟨e, he, f, hf, hef⟩ := Submodule.mem_sup.1 (this ▸ Submodule.mem_top : (1 : 𝓞 K) ∈ P ⊔ P.comap (cj K))
  refine ⟨e, he, ?_⟩
  have : 1 - cj K e = cj K f := by rw [← map_one (cj K), ← hef, map_add]; ring
  rw [this]
  exact hf

theorem mem_locR {P : Ideal (𝓞 K)} {x : K} :
    x ∈ locR (K := K) P ↔ ∃ s ∈ hcompl (K := K) P, ∃ r : 𝓞 K, algebraMap _ K r = algebraMap _ K s * x := by
  change (∃ s ∈ hcompl (K := K) P, s • x ∈ (1 : Submodule (𝓞 K) K)) ↔ _
  simp only [Submodule.mem_one, Algebra.smul_def]

def locRing (P : Ideal (𝓞 K)) : Subring K where
  carrier := locR (K := K) P
  zero_mem' := Submodule.zero_mem _
  add_mem' := Submodule.add_mem _
  neg_mem' := Submodule.neg_mem _
  one_mem' := mem_locR.2 ⟨1, Submonoid.one_mem _, 1, by simp⟩
  mul_mem' := by
    intro a b ha hb
    obtain ⟨s, hs, r, hr⟩ := mem_locR.1 ha
    obtain ⟨t, ht, q, hq⟩ := mem_locR.1 hb
    refine mem_locR.2 ⟨s * t, Submonoid.mul_mem _ hs ht, r * q, ?_⟩
    rw [map_mul, map_mul, hr, hq]
    ring

def locId (P : Ideal (𝓞 K)) : Submodule (𝓞 K) K := loc (K := K) P (Submodule.map (Algebra.linearMap (𝓞 K) K) P)

theorem mem_locId {P : Ideal (𝓞 K)} {x : K} :
    x ∈ locId P ↔ ∃ s ∈ hcompl (K := K) P, ∃ r ∈ P, algebraMap _ K r = algebraMap _ K s * x := by
  change (∃ s ∈ hcompl (K := K) P, s • x ∈ Submodule.map (Algebra.linearMap (𝓞 K) K) P) ↔ _
  simp only [Submodule.mem_map, Algebra.smul_def, Algebra.linearMap_apply]

theorem cj_mem_hcompl {P : Ideal (𝓞 K)} (hP : P.IsPrime) {s : 𝓞 K} (hs : s ∈ hcompl (K := K) P) :
    cj K s ∈ hcompl (K := K) P := by
  rw [mem_hcompl hP] at hs ⊢
  rw [cj_cj]
  exact hs.symm

theorem star_mem_locR {P : Ideal (𝓞 K)} (hP : P.IsPrime) {x : K} (hx : x ∈ locR (K := K) P) :
    star x ∈ locR (K := K) P := by
  obtain ⟨s, hs, r, hr⟩ := mem_locR.1 hx
  exact mem_locR.2 ⟨cj K s, cj_mem_hcompl hP hs, cj K r, by rw [cj_coe, cj_coe, hr, star_mul']⟩

theorem mul_mem_locId {P : Ideal (𝓞 K)} {a x : K} (ha : a ∈ locR (K := K) P) (hx : x ∈ locId P) :
    a * x ∈ locId P := by
  obtain ⟨s, hs, r, hr⟩ := mem_locR.1 ha
  obtain ⟨t, ht, q, hqP, hq⟩ := mem_locId.1 hx
  refine mem_locId.2 ⟨s * t, Submonoid.mul_mem _ hs ht, r * q, P.mul_mem_left _ hqP, ?_⟩
  rw [map_mul, map_mul, hr, hq]
  ring

theorem inv_mem_locR {P : Ideal (𝓞 K)} (hP : P.IsPrime) {a : K} (ha : a ∈ locR (K := K) P) (h1 : a ∉ locId P)
    (h2 : star a ∉ locId P) : a⁻¹ ∈ locR (K := K) P := by
  obtain ⟨s, hs, r, hr⟩ := mem_locR.1 ha
  have ha0 : a ≠ 0 := fun H => h1 (H ▸ Submodule.zero_mem _)
  refine mem_locR.2 ⟨r, (mem_hcompl hP r).2 ⟨fun H => h1 (mem_locId.2 ⟨s, hs, r, H, hr⟩), fun H =>
    h2 (mem_locId.2 ⟨cj K s, cj_mem_hcompl hP hs, cj K r, H, by rw [cj_coe, cj_coe, hr, star_mul']⟩)⟩, s, ?_⟩
  rw [hr]
  field_simp

theorem coe_mem_locId {P : Ideal (𝓞 K)} (hP : P.IsPrime) {r : 𝓞 K} : algebraMap _ K r ∈ locId P ↔ r ∈ P := by
  rw [mem_locId]
  constructor
  · rintro ⟨s, hs, q, hq, e⟩
    rw [← map_mul] at e
    rw [RingOfIntegers.coe_injective e] at hq
    exact (hP.mem_or_mem hq).resolve_left ((mem_hcompl hP s).1 hs).1
  · exact fun hr => ⟨1, Submonoid.one_mem _, r, hr, by simp⟩

variable {V : Type} [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]

theorem smul_mem_loc {P : Ideal (𝓞 K)} {M : Submodule (𝓞 K) V} {a : K} {x : V} (ha : a ∈ locR (K := K) P)
    (hx : x ∈ loc (K := K) P M) : a • x ∈ loc (K := K) P M := by
  obtain ⟨s, hs, r, hr⟩ := mem_locR.1 ha
  obtain ⟨t, ht, hq⟩ := hx
  refine ⟨t * s, Submonoid.mul_mem _ ht hs, ?_⟩
  have : (t * s) • a • x = r • t • x := by
    rw [smul_comm r t x, mul_smul, ← algebraMap_smul K r, hr, mul_smul, algebraMap_smul]
  rw [this]
  exact M.smul_mem _ hq

theorem mem_dualAt (h : V →ₗ⋆[K] V →ₗ[K] K) {P : Ideal (𝓞 K)} {M : Submodule (𝓞 K) V} {x : V} :
    x ∈ dualAt h P M ↔ ∀ y ∈ M, h y x ∈ locR (K := K) P := by
  simp [dualAt, Submodule.mem_iInf]

theorem exists_rep [FiniteDimensional K V] (h : V →ₗ⋆[K] V →ₗ[K] K) (hn : h.Nondegenerate) (f : V →ₗ[K] K) :
    ∃ y, h y = f := by
  have h1 : (LinearMap.range h).dualCoannihilator = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    rw [Submodule.mem_dualCoannihilator] at hx
    exact hn.2 x fun y => hx _ ⟨y, rfl⟩
  have h2 := Subspace.dualCoannihilator_dualAnnihilator_eq (W := LinearMap.range h)
  rw [h1, Submodule.dualAnnihilator_bot] at h2
  have h3 : f ∈ LinearMap.range h := h2 ▸ Submodule.mem_top
  exact h3

variable [NumberField K]

omit [StarRing K] in

theorem exists_form {M L : Submodule (𝓞 K) V} (hM : Submodule.IsLattice K M) {P : Ideal (𝓞 K)}
    (φ : (↥M ⧸ L.comap M.subtype) ≃ₗ[𝓞 K] (𝓞 K ⧸ P)) :
    ∃ (f : V →ₗ[K] K) (ψ : M →ₗ[𝓞 K] 𝓞 K), (∀ y : M, f y = algebraMap (𝓞 K) K (ψ y)) ∧
      ∀ y : M, ψ y ∈ P ↔ (y : V) ∈ L := by
  have hflat : Module.Flat (𝓞 K) M := by
    rw [IsDedekindDomain.flat_iff_torsion_eq_bot, eq_bot_iff]
    rintro x ⟨a, ha⟩
    have h2 : (algebraMap (𝓞 K) K a) • (x : V) = 0 := by
      rw [algebraMap_smul]; exact congrArg Subtype.val ha
    have h3 : algebraMap (𝓞 K) K a ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors a.2
    exact Subtype.ext ((smul_eq_zero.1 h2).resolve_left h3)
  have : Module.FinitePresentation (𝓞 K) M := Module.finitePresentation_of_finite _ _
  have : Module.Projective (𝓞 K) M := Module.Flat.projective_of_finitePresentation
  obtain ⟨ψ, hψ⟩ := Module.projective_lifting_property (Submodule.mkQ P)
    (φ.toLinearMap ∘ₗ (L.comap M.subtype).mkQ) (Submodule.mkQ_surjective P)
  have := GlobalTheory.UnimodQuot.isLocalizedModule_subtype hM
  have hu : ∀ x : nonZeroDivisors (𝓞 K), IsUnit (algebraMap (𝓞 K) (Module.End (𝓞 K) K) x) :=
    fun x => IsLocalizedModule.map_units (S := nonZeroDivisors (𝓞 K)) (Algebra.linearMap (𝓞 K) K) x
  refine ⟨LinearMap.extendScalarsOfIsLocalization (nonZeroDivisors (𝓞 K)) K
      (IsLocalizedModule.lift (nonZeroDivisors (𝓞 K)) M.subtype (Algebra.linearMap (𝓞 K) K ∘ₗ ψ) hu), ψ,
    fun y => IsLocalizedModule.lift_apply (nonZeroDivisors (𝓞 K)) M.subtype _ hu y, fun y => ?_⟩
  have e : Submodule.mkQ P (ψ y) = φ ((L.comap M.subtype).mkQ y) := LinearMap.congr_fun hψ y
  rw [← Submodule.Quotient.mk_eq_zero, ← Submodule.mkQ_apply, e, LinearEquiv.map_eq_zero_iff, Submodule.mkQ_apply,
    Submodule.Quotient.mk_eq_zero]
  rfl

theorem exists_vec [FiniteDimensional K V] (h : V →ₗ⋆[K] V →ₗ[K] K) (hs : ∀ x y, star (h x y) = h y x)
    (hn : h.Nondegenerate) {M L : Submodule (𝓞 K) V} (hM : Submodule.IsLattice K M) {P : Ideal (𝓞 K)}
    (hP : P.IsPrime) (hU : IsUnimodularAt h P M) (hL : L ≤ M)
    (φ : (↥M ⧸ L.comap M.subtype) ≃ₗ[𝓞 K] (𝓞 K ⧸ P)) :
    ∃ u ∈ loc (K := K) P M, (∃ w ∈ loc (K := K) P M, h u w ∉ locId P) ∧
      ∀ x, x ∈ loc (K := K) P L ↔ x ∈ loc (K := K) P M ∧ h u x ∈ locId P := by
  obtain ⟨f, ψ, hf, hψ⟩ := exists_form hM φ
  obtain ⟨u, rfl⟩ := exists_rep h hn f
  have e : ∀ (s : 𝓞 K) (x : V) (hx : s • x ∈ M), algebraMap _ K (ψ ⟨_, hx⟩) = algebraMap _ K s * h u x := by
    intro s x hx
    rw [← hf]
    change h u (s • x) = _
    rw [← algebraMap_smul K s, map_smul, smul_eq_mul]
  refine ⟨u, ?_, ?_, fun x => ⟨?_, ?_⟩⟩
  · rw [← hU, mem_dualAt]
    rintro y ⟨s, hs', hy⟩
    rw [← hs]
    exact star_mem_locR hP (mem_locR.2 ⟨s, hs', _, e s y hy⟩)
  · obtain ⟨y, hy⟩ := (L.comap M.subtype).mkQ_surjective (φ.symm 1)
    refine ⟨y, ⟨1, Submonoid.one_mem _, by simp⟩, fun H => ?_⟩
    rw [hf, coe_mem_locId hP, hψ] at H
    have : (L.comap M.subtype).mkQ y = 0 := (Submodule.Quotient.mk_eq_zero _).2 H
    rw [hy, LinearEquiv.map_eq_zero_iff] at this
    exact hP.one_notMem (Ideal.Quotient.eq_zero_iff_mem.1 this)
  · rintro ⟨s, hs', hx⟩
    exact ⟨⟨s, hs', hL hx⟩, mem_locId.2 ⟨s, hs', _, (hψ ⟨_, hL hx⟩).2 hx, e s x (hL hx)⟩⟩
  · rintro ⟨⟨s, hs', hx⟩, H⟩
    refine ⟨s, hs', (hψ ⟨_, hx⟩).1 ?_⟩
    rw [← coe_mem_locId hP, e]
    exact mul_mem_locId (mem_locR.2 ⟨1, Submonoid.one_mem _, s, by simp⟩) H

end Local

theorem main : ∀ (K V : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (h : V →ₗ⋆[K] V →ₗ[K] K), IsCMUnram K → h.IsSymm → h.Nondegenerate → ∀ (M : Submodule (𝓞 K) V), Submodule.IsLattice K M → ∀ P : Ideal (𝓞 K), P.IsMaximal → conjIdeal (K := K) P ≠ P → IsUnimodularAt h P M → ∀ L L' : Submodule (𝓞 K) V, L ≤ M → L' ≤ M → Nonempty ((↥M ⧸ L.comap M.subtype) ≃ₗ[𝓞 K] (𝓞 K ⧸ P)) → Nonempty ((↥M ⧸ L'.comap M.subtype) ≃ₗ[𝓞 K] (𝓞 K ⧸ P)) → ∃ g ∈ isom h, gmap g (loc (K := K) P M) = loc (K := K) P M ∧ gmap g (loc (K := K) P L) = loc (K := K) P L' := by
  intro K V _ _ _ _ _ _ _ _ h _ hsy hn M hM P hP hc hU L L' hL hL' ⟨φ⟩ ⟨φ'⟩
  have hs : ∀ x y, star (h x y) = h y x := fun x y => hsy.eq x y
  have hp := hP.isPrime
  obtain ⟨u, hu, ⟨w₁, hw₁, k₁⟩, hLu⟩ := exists_vec h hs hn hM hp hU hL φ
  obtain ⟨u', hu', ⟨w₂, hw₂, k₂⟩, hLu'⟩ := exists_vec h hs hn hM hp hU hL' φ'
  obtain ⟨w, hw, h1, h2⟩ : ∃ w ∈ loc (K := K) P M, h u w ∉ locId P ∧ h u' w ∉ locId P := by
    by_cases a : h u' w₁ ∈ locId P
    · by_cases b : h u w₂ ∈ locId P
      · refine ⟨w₁ + w₂, Submodule.add_mem _ hw₁ hw₂, fun H => k₁ ?_, fun H => k₂ ?_⟩
        · rw [map_add] at H
          simpa using Submodule.sub_mem _ H b
        · rw [map_add] at H
          simpa using Submodule.sub_mem _ H a
      · exact ⟨w₂, hw₂, b, k₂⟩
    · exact ⟨w₁, hw₁, k₁, a⟩
  obtain ⟨e, he, he'⟩ := exists_idem hP hc
  obtain ⟨g, hg, g1, g2, g3⟩ := exists_move h hs (locRing P) (locId P).toAddSubgroup
    (loc (K := K) P M).toAddSubgroup (fun a ha => star_mem_locR hp ha) (fun a ha x hx => mul_mem_locId ha hx)
    (fun a ha => inv_mem_locR hp ha) (algebraMap _ K e) (mem_locR.2 ⟨1, Submonoid.one_mem _, e, by simp⟩)
    ((coe_mem_locId hp).2 he) (by
      have := (coe_mem_locId hp).2 he'
      rwa [map_sub, map_one, cj_coe] at this)
    (fun a ha x hx => smul_mem_loc ha hx) (fun x hx y hy => by
      have : y ∈ dualAt h P (loc (K := K) P M) := by rw [hU]; exact hy
      exact (mem_dualAt h).1 this x hx) u u' w hu hu' hw h1 h2
  refine ⟨g, hg, ?_, ?_⟩
  · ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact g1 y hy
    · exact fun hx => ⟨g.symm x, g2 x hx, g.apply_symm_apply x⟩
  · ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      obtain ⟨a, b⟩ := (hLu y).1 hy
      refine (hLu' _).2 ⟨g1 y a, ?_⟩
      have := Submodule.add_mem (locId P) (g3 y a) b
      simpa using this
    · intro hx
      obtain ⟨a, b⟩ := (hLu' x).1 hx
      refine ⟨g.symm x, (hLu _).2 ⟨g2 x a, ?_⟩, g.apply_symm_apply x⟩
      have := Submodule.sub_mem (locId P) b (g3 _ (g2 x a))
      simpa using this

end GlobalTheory.Mass.Hyperplane
