import Mathlib
import GroundTheory.GlobalFields.Artin.LogCharpoly

noncomputable section

open IsDedekindDomain NumberField Polynomial

open scoped Pointwise

namespace GroundTheory.Global

section Average

variable {G : Type*} [Group G]

def cosetAverage (I : Subgroup G) (f : G → ℂ) (g : G) : ℂ :=
  (Nat.card I : ℂ)⁻¹ * ∑ᶠ i : I, f (g * i)

theorem cosetAverage_mul_of_mem (I : Subgroup G) (f : G → ℂ) (g : G) {j : G} (hj : j ∈ I) :
    cosetAverage I f (g * j) = cosetAverage I f g := by
  unfold cosetAverage
  congr 1
  have := finsum_comp_equiv (Equiv.mulLeft (⟨j, hj⟩ : I)) (f := fun i : I => f (g * (i : G)))
  simpa [mul_assoc] using this

theorem cosetAverage_conj (I J : Subgroup G) (f : G → ℂ) (hf : ∀ g h : G, f (h * g * h⁻¹) = f g)
    (h : G) (hIJ : ∀ σ, σ ∈ J ↔ h⁻¹ * σ * h ∈ I) (g : G) :
    cosetAverage J f (h * g * h⁻¹) = cosetAverage I f g := by
  let e : I ≃ J :=
    { toFun := fun i => ⟨h * i * h⁻¹, (hIJ _).2 (by
        rw [show h⁻¹ * (h * (i : G) * h⁻¹) * h = i by group]; exact i.2)⟩
      invFun := fun j => ⟨h⁻¹ * j * h, (hIJ _).1 j.2⟩
      left_inv := fun i => by ext; simp [mul_assoc]
      right_inv := fun j => by ext; simp [mul_assoc] }
  unfold cosetAverage
  rw [Nat.card_congr e, ← finsum_comp_equiv e]
  congr 1
  refine finsum_congr fun i => ?_
  simp only [e, Equiv.coe_fn_mk]
  rw [show h * g * h⁻¹ * (h * (i : G) * h⁻¹) = h * (g * i) * h⁻¹ by group, hf]

end Average

section Inertia

variable {G S : Type*} [Group G] [CommRing S] [MulSemiringAction G S]

theorem mem_inertia_smul_iff (P : Ideal S) (h σ : G) :
    σ ∈ (h • P).inertia G ↔ h⁻¹ * σ * h ∈ P.inertia G := by
  constructor
  · intro hσ x
    have := hσ (h • x)
    rw [Submodule.mem_toAddSubgroup, Ideal.mem_pointwise_smul_iff_inv_smul_mem] at this
    simpa [mul_smul, smul_sub] using this
  · intro hσ x
    rw [Submodule.mem_toAddSubgroup, Ideal.mem_pointwise_smul_iff_inv_smul_mem]
    simpa [mul_smul, smul_sub] using hσ (h⁻¹ • x)

theorem mul_mul_inv_mem_inertia {P : Ideal S} {s i : G} (hs : s ∈ MulAction.stabilizer G P)
    (hi : i ∈ P.inertia G) : s * i * s⁻¹ ∈ P.inertia G := by
  have hsP : s • P = P := hs
  rw [← hsP, mem_inertia_smul_iff, show s⁻¹ * (s * i * s⁻¹) * s = i by group]
  exact hi

theorem inv_pow_mul_pow_mem_inertia {P : Ideal S} {a b : G} (ha : a ∈ MulAction.stabilizer G P)
    (hab : b * a⁻¹ ∈ P.inertia G) (m : ℕ) : (a ^ m)⁻¹ * b ^ m ∈ P.inertia G := by
  induction m with
  | zero => simp [one_mem]
  | succ m ih =>
    have h1 := mul_mul_inv_mem_inertia (inv_mem ha) (mul_mem ih hab)
    rw [inv_inv] at h1
    convert h1 using 1
    rw [pow_succ, pow_succ]
    group

end Inertia

section Place

variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  [IsGalois K L] (v : HeightOneSpectrum (𝓞 K))

theorem cosetAverage_inertia_eq (f : Gal(L/K) → ℂ) (hf : ∀ g h, f (h * g * h⁻¹) = f g)
    (w w' : HeightOneSpectrum (𝓞 L)) [w.asIdeal.LiesOver v.asIdeal]
    [w'.asIdeal.LiesOver v.asIdeal] {φ φ' : Gal(L/K)} (hφ : IsArithFrobAt (𝓞 K) φ w.asIdeal)
    (hφ' : IsArithFrobAt (𝓞 K) φ' w'.asIdeal) (m : ℕ) :
    cosetAverage (w'.asIdeal.inertia Gal(L/K)) f (φ' ^ m) =
      cosetAverage (w.asIdeal.inertia Gal(L/K)) f (φ ^ m) := by
  obtain ⟨h, hh⟩ := Ideal.exists_smul_eq_of_isGaloisGroup v.asIdeal w.asIdeal w'.asIdeal Gal(L/K)
  have hψ : IsArithFrobAt (𝓞 K) (h * φ * h⁻¹) w'.asIdeal := hh ▸ hφ.conj h
  have hI := inv_pow_mul_pow_mem_inertia hψ.mem_stabilizer (hφ'.mul_inv_mem_inertia hψ) m
  rw [← mul_inv_cancel_left ((h * φ * h⁻¹) ^ m) (φ' ^ m), cosetAverage_mul_of_mem _ _ _ hI,
    conj_pow]
  refine cosetAverage_conj _ _ f hf h (fun σ => ?_) _
  rw [← hh, mem_inertia_smul_iff]

omit [NumberField L] [IsGalois K L] in
theorem exists_liesOver : ∃ w : HeightOneSpectrum (𝓞 L), w.asIdeal.LiesOver v.asIdeal := by
  obtain ⟨Q, hQmax, hQ⟩ := Ideal.exists_maximal_ideal_liesOver_of_isIntegral (S := 𝓞 L) v.asIdeal
  refine ⟨⟨Q, hQmax.isPrime, fun h => v.ne_bot ?_⟩, hQ⟩
  rw [hQ.over, h]
  exact Ideal.comap_bot_of_injective _ (FaithfulSMul.algebraMap_injective _ _)

def placeAbove : HeightOneSpectrum (𝓞 L) :=
  (exists_liesOver (L := L) v).choose

instance liesOver_placeAbove : (placeAbove (L := L) v).asIdeal.LiesOver v.asIdeal :=
  (exists_liesOver (L := L) v).choose_spec

variable (L) in

def localAverage (f : Gal(L/K) → ℂ) (m : ℕ) : ℂ :=
  cosetAverage ((placeAbove (L := L) v).asIdeal.inertia Gal(L/K)) f
    (arithFrobAt (𝓞 K) Gal(L/K) (placeAbove (L := L) v).asIdeal ^ m)

theorem localAverage_eq (f : Gal(L/K) → ℂ) (hf : ∀ g h, f (h * g * h⁻¹) = f g)
    (w : HeightOneSpectrum (𝓞 L)) [w.asIdeal.LiesOver v.asIdeal] {φ : Gal(L/K)}
    (hφ : IsArithFrobAt (𝓞 K) φ w.asIdeal) (m : ℕ) :
    localAverage L v f m = cosetAverage (w.asIdeal.inertia Gal(L/K)) f (φ ^ m) :=
  cosetAverage_inertia_eq v f hf w (placeAbove v) hφ (IsArithFrobAt.arithFrobAt _ _ _) m

end Place

section Representation

variable {G V : Type*} [Group G] [Finite G] [AddCommGroup V] [Module ℂ V]
  [FiniteDimensional ℂ V] (ρ : Representation ℂ G V)

abbrev subgroupInvariants (I : Subgroup G) : Submodule ℂ V :=
  Representation.invariants (ρ.comp I.subtype)

omit [Finite G] [FiniteDimensional ℂ V] in
theorem mem_invariants_comp_subtype_iff (I : Subgroup G) (x : V) :
    x ∈ subgroupInvariants ρ I ↔ ∀ i ∈ I, ρ i x = x :=
  ⟨fun h i hi => h ⟨i, hi⟩, fun h i => h i i.2⟩

omit [Finite G] [FiniteDimensional ℂ V] in

theorem mapsTo_invariants (I : Subgroup G) {g : G} (hg : ∀ i ∈ I, g⁻¹ * i * g ∈ I) (x : V)
    (hx : x ∈ subgroupInvariants ρ I) : ρ g x ∈ subgroupInvariants ρ I := by
  rw [mem_invariants_comp_subtype_iff] at hx ⊢
  intro i hi
  rw [← Module.End.mul_apply, ← map_mul, show i * g = g * (g⁻¹ * i * g) by group, map_mul,
    Module.End.mul_apply, hx _ (hg i hi)]

theorem trace_restrict_invariants (I : Subgroup G) (B : Module.End ℂ V)
    (hB : ∀ x ∈ subgroupInvariants ρ I, B x ∈ subgroupInvariants ρ I) :
    LinearMap.trace ℂ _ (B.restrict hB) =
      (Nat.card I : ℂ)⁻¹ * ∑ᶠ i : I, LinearMap.trace ℂ V (B * ρ i) := by
  classical
  have := Fintype.ofFinite I
  set W := subgroupInvariants ρ I
  have hI : (Nat.card I : ℂ) ≠ 0 := Nat.cast_ne_zero.2 Nat.card_pos.ne'
  set e : Module.End ℂ V := (Nat.card I : ℂ)⁻¹ • ∑ i : I, ρ i with he
  have he_apply : ∀ x, e x = (Nat.card I : ℂ)⁻¹ • ∑ i : I, ρ i x := fun x => by
    rw [he, LinearMap.smul_apply, LinearMap.sum_apply]
  have he_mem : ∀ x, e x ∈ W := by
    intro x
    rw [mem_invariants_comp_subtype_iff]
    intro j hj
    rw [he_apply, map_smul, map_sum]
    congr 1
    exact Fintype.sum_equiv (Equiv.mulLeft (⟨j, hj⟩ : I)) _ _ (fun i => by
      simp only [Equiv.coe_mulLeft, Subgroup.coe_mul, map_mul, Module.End.mul_apply])
  have he_id : ∀ x ∈ W, e x = x := by
    intro x hx
    rw [mem_invariants_comp_subtype_iff] at hx
    rw [he_apply, Finset.sum_congr rfl fun i _ => hx i.1 i.2, Finset.sum_const, Finset.card_univ,
      ← Nat.card_eq_fintype_card, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul, inv_mul_cancel₀ hI,
      one_smul]
  let e' : V →ₗ[ℂ] W := e.codRestrict W he_mem
  have h1 : B.restrict hB = (e' ∘ₗ B) ∘ₗ W.subtype := by
    ext x
    simp [e', he_id _ (hB x x.2)]
  have h2 : W.subtype ∘ₗ (e' ∘ₗ B) = e ∘ₗ B := by
    ext x
    rfl
  rw [h1, LinearMap.trace_comp_comm', h2, finsum_eq_sum_of_fintype, he, LinearMap.smul_comp,
    map_smul, smul_eq_mul, ← Module.End.mul_eq_comp, Finset.sum_mul, map_sum]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  exact LinearMap.trace_mul_comm ℂ (ρ i) B

def invariantsEnd (I : Subgroup G) (g : G) (hg : ∀ i ∈ I, g⁻¹ * i * g ∈ I) :
    Module.End ℂ (subgroupInvariants ρ I) :=
  (ρ g).restrict (mapsTo_invariants ρ I hg)

theorem trace_invariantsEnd_pow (I : Subgroup G) (g : G) (hg : ∀ i ∈ I, g⁻¹ * i * g ∈ I)
    (m : ℕ) :
    LinearMap.trace ℂ _ (invariantsEnd ρ I g hg ^ m) = cosetAverage I ρ.character (g ^ m) := by
  rw [invariantsEnd, Module.End.pow_restrict, trace_restrict_invariants, cosetAverage]
  congr 1
  refine finsum_congr fun i => ?_
  rw [Representation.character, map_mul ρ, map_pow ρ]

end Representation

section GaloisRepresentation

variable {K L V : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  [IsGalois K L] (v : HeightOneSpectrum (𝓞 K)) [AddCommGroup V] [Module ℂ V]
  [FiniteDimensional ℂ V] (ρ : Representation ℂ Gal(L/K) V)

omit [NumberField K] [NumberField L] [IsGalois K L] in

theorem inv_mul_mul_mem_inertia (w : HeightOneSpectrum (𝓞 L)) {φ : Gal(L/K)}
    (hφ : φ ∈ MulAction.stabilizer Gal(L/K) w.asIdeal) :
    ∀ i ∈ w.asIdeal.inertia Gal(L/K), φ⁻¹ * i * φ ∈ w.asIdeal.inertia Gal(L/K) :=
  fun _ hi => by simpa using mul_mul_inv_mem_inertia (inv_mem hφ) hi

def inertiaFactor (w : HeightOneSpectrum (𝓞 L)) (φ : Gal(L/K))
    (hφ : φ ∈ MulAction.stabilizer Gal(L/K) w.asIdeal) : ℂ[X] :=
  (invariantsEnd ρ (w.asIdeal.inertia Gal(L/K)) φ (inv_mul_mul_mem_inertia w hφ)).charpoly.reverse

theorem inertiaFactor_eq (w w' : HeightOneSpectrum (𝓞 L)) [w.asIdeal.LiesOver v.asIdeal]
    [w'.asIdeal.LiesOver v.asIdeal] {φ φ' : Gal(L/K)} (hφ : IsArithFrobAt (𝓞 K) φ w.asIdeal)
    (hφ' : IsArithFrobAt (𝓞 K) φ' w'.asIdeal) :
    inertiaFactor ρ w φ hφ.mem_stabilizer = inertiaFactor ρ w' φ' hφ'.mem_stabilizer :=
  reverse_charpoly_eq_of_trace_pow_eq _ _ fun m _ => by
    rw [trace_invariantsEnd_pow, trace_invariantsEnd_pow,
      cosetAverage_inertia_eq v ρ.character (fun g h => ρ.char_conj g h) w w' hφ hφ' m]

omit [IsGalois K L] in

theorem logOf_inv_inertiaFactor (w : HeightOneSpectrum (𝓞 L)) {φ : Gal(L/K)}
    (hφ : φ ∈ MulAction.stabilizer Gal(L/K) w.asIdeal) :
    PowerSeries.logOf ((inertiaFactor ρ w φ hφ : PowerSeries ℂ)⁻¹) =
      PowerSeries.mk fun m => if m = 0 then 0 else
        cosetAverage (w.asIdeal.inertia Gal(L/K)) ρ.character (φ ^ m) / m := by
  rw [inertiaFactor, logOf_inv_reverse_charpoly]
  congr 1
  funext m
  rw [trace_invariantsEnd_pow]

def localFactor : ℂ[X] :=
  inertiaFactor ρ (placeAbove v) (arithFrobAt (𝓞 K) Gal(L/K) (placeAbove (L := L) v).asIdeal)
    (IsArithFrobAt.arithFrobAt_mem_stabilizer _ _ _)

theorem localFactor_eq (w : HeightOneSpectrum (𝓞 L)) [w.asIdeal.LiesOver v.asIdeal]
    {φ : Gal(L/K)} (hφ : IsArithFrobAt (𝓞 K) φ w.asIdeal) :
    localFactor v ρ = inertiaFactor ρ w φ hφ.mem_stabilizer :=
  inertiaFactor_eq v ρ _ _ (IsArithFrobAt.arithFrobAt _ _ _) hφ

theorem logOf_inv_localFactor :
    PowerSeries.logOf ((localFactor v ρ : PowerSeries ℂ)⁻¹) =
      PowerSeries.mk fun m => if m = 0 then 0 else localAverage L v ρ.character m / m :=
  logOf_inv_inertiaFactor ρ _ _

end GaloisRepresentation

end GroundTheory.Global
