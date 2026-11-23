import Mathlib
import GroundTheory.AutomorphicForms.SmoothRep

noncomputable section

namespace GroundTheory.Automorphic

open Set Filter Topology

section Exactness

variable {N : Type*} [Group N] [TopologicalSpace N] [IsTopologicalGroup N]
  [LocallyCompactSpace N] [T2Space N] [TotallyDisconnectedSpace N]
  {V : Type*} [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ N V)

omit [TopologicalSpace N] [IsTopologicalGroup N] [LocallyCompactSpace N] [T2Space N]
  [TotallyDisconnectedSpace N] in

theorem coinvariantsKer_le_ker (K : Subgroup N) :
    coinvariantsKer ρ K ≤ Representation.Coinvariants.ker ρ := by
  refine Submodule.span_le.2 ?_
  rintro _ ⟨⟨k, v⟩, rfl⟩
  exact Representation.Coinvariants.sub_mem_ker (k : N) v

omit [IsTopologicalGroup N] [LocallyCompactSpace N] [T2Space N] [TotallyDisconnectedSpace N] in

theorem exists_mem_coinvariantsKer
    (hN : ∀ s : Finset N, ∃ K : Subgroup N, IsCompact (K : Set N) ∧ IsOpen (K : Set N) ∧
      ∀ x ∈ s, x ∈ K)
    {v : V} (hv : v ∈ Representation.Coinvariants.ker ρ) :
    ∃ K : Subgroup N, IsCompact (K : Set N) ∧ IsOpen (K : Set N) ∧ v ∈ coinvariantsKer ρ K := by
  classical
  obtain ⟨T, hT, hvT⟩ := Submodule.mem_span_finite_of_mem_span hv
  have : ∀ t ∈ T, ∃ g : N, ∃ w : V, ρ g w - w = t := fun t ht => by
    obtain ⟨⟨g, w⟩, h⟩ := hT ht
    exact ⟨g, w, h⟩
  choose! gf wf hgf using this
  obtain ⟨K, hKc, hKo, hK⟩ := hN (T.image gf)
  refine ⟨K, hKc, hKo, Submodule.span_le.2 (fun t ht => ?_) hvT⟩
  rw [← hgf t ht]
  exact sub_mem_coinvariantsKer (hK _ (Finset.mem_image_of_mem gf ht)) (wf t)

variable {W X : Type*} [AddCommGroup W] [Module ℂ W] [AddCommGroup X] [Module ℂ X]
  {ρ} {σ : Representation ℂ N W} {τ : Representation ℂ N X}

theorem exact_coinvariantsMap
    (hN : ∀ s : Finset N, ∃ K : Subgroup N, IsCompact (K : Set N) ∧ IsOpen (K : Set N) ∧
      ∀ x ∈ s, x ∈ K)
    (hσ : IsSmooth σ) (hτ : IsSmooth τ)
    (f : Representation.IntertwiningMap ρ σ) (g : Representation.IntertwiningMap σ τ)
    (hfg : Function.Exact f g) :
    Function.Exact (Representation.Coinvariants.map ρ σ f)
      (Representation.Coinvariants.map σ τ g) := by
  intro y
  obtain ⟨w, rfl⟩ := Representation.Coinvariants.mk_surjective _ y
  rw [Representation.Coinvariants.map_mk]
  constructor
  · intro h0
    rw [Representation.Coinvariants.mk_eq_zero] at h0
    obtain ⟨K, hKc, hKo, hK⟩ := exists_mem_coinvariantsKer τ hN h0
    have h1 : g (fixedProj σ hσ hKc hKo w : W) = 0 := by
      have := congrArg Subtype.val (fixedProj_map hKc hKo hσ hτ g w)
      rw [fixedProj_apply_of_mem_coinvariantsKer hτ hKc hKo hK, coe_fixedMap_apply] at this
      exact this.symm
    obtain ⟨u, hu⟩ := (hfg _).1 h1
    refine ⟨Representation.Coinvariants.mk ρ u, ?_⟩
    rw [Representation.Coinvariants.map_mk, hu, Representation.Coinvariants.mk_eq_iff, ← neg_sub]
    exact Submodule.neg_mem _ (coinvariantsKer_le_ker σ K (sub_fixedProj_mem hσ hKc hKo w))
  · rintro ⟨u, hu⟩
    obtain ⟨u, rfl⟩ := Representation.Coinvariants.mk_surjective _ u
    rw [Representation.Coinvariants.map_mk] at hu
    rw [← Representation.Coinvariants.map_mk g w, ← hu, Representation.Coinvariants.map_mk,
      (hfg _).2 ⟨u, rfl⟩, map_zero]

end Exactness

section Translate

variable {G : Type*} [Group G] {V : Type*} [AddCommGroup V] [Module ℂ V]
  (ρ : Representation ℂ G V) (N : Subgroup G)

theorem mk_apply_of_mem {n : G} (hn : n ∈ N) (u : V) :
    Representation.Coinvariants.mk (ρ.comp N.subtype) (ρ n u) =
      Representation.Coinvariants.mk (ρ.comp N.subtype) u :=
  Representation.Coinvariants.mk_self_apply (ρ := ρ.comp N.subtype) ⟨n, hn⟩ u

def coinvariantsTranslate (a : G) (ha : ∀ n ∈ N, a * n * a⁻¹ ∈ N) :
    Representation.Coinvariants (ρ.comp N.subtype) →ₗ[ℂ]
      Representation.Coinvariants (ρ.comp N.subtype) :=
  Representation.Coinvariants.lift _ (Representation.Coinvariants.mk _ ∘ₗ ρ a) fun n =>
    LinearMap.ext fun u => by
      simp only [LinearMap.coe_comp, Function.comp_apply, MonoidHom.coe_comp,
        Subgroup.coe_subtype]
      have : ρ a (ρ n u) = ρ (a * n * a⁻¹) (ρ a u) := by
        simp only [← Module.End.mul_apply, ← map_mul, inv_mul_cancel_right]
      rw [this]
      exact mk_apply_of_mem ρ N (ha n n.2) (ρ a u)

variable {ρ N}

@[simp]
theorem coinvariantsTranslate_mk {a : G} (ha : ∀ n ∈ N, a * n * a⁻¹ ∈ N) (u : V) :
    coinvariantsTranslate ρ N a ha (Representation.Coinvariants.mk _ u) =
      Representation.Coinvariants.mk _ (ρ a u) := rfl

theorem iterate_coinvariantsTranslate_mk {a : G} (ha : ∀ n ∈ N, a * n * a⁻¹ ∈ N) (m : ℕ)
    (u : V) :
    (coinvariantsTranslate ρ N a ha)^[m] (Representation.Coinvariants.mk _ u) =
      Representation.Coinvariants.mk _ (ρ (a ^ m) u) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Function.iterate_succ_apply', ih, coinvariantsTranslate_mk, pow_succ', map_mul,
      Module.End.mul_apply]

theorem coinvariantsTranslate_injective {a : G} (ha : ∀ n ∈ N, a * n * a⁻¹ ∈ N)
    (ha' : ∀ n ∈ N, a⁻¹ * n * a ∈ N) :
    Function.Injective (coinvariantsTranslate ρ N a ha) := by
  have ha'' : ∀ n ∈ N, a⁻¹ * n * a⁻¹⁻¹ ∈ N := fun n hn => by simpa using ha' n hn
  refine Function.LeftInverse.injective (g := coinvariantsTranslate ρ N a⁻¹ ha'') fun u => ?_
  obtain ⟨u, rfl⟩ := Representation.Coinvariants.mk_surjective _ u
  rw [coinvariantsTranslate_mk, coinvariantsTranslate_mk, ← Module.End.mul_apply, ← map_mul,
    inv_mul_cancel, map_one, Module.End.one_apply]

end Translate

section JacquetLemma

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [LocallyCompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
  {V : Type*} [AddCommGroup V] [Module ℂ V] {ρ : Representation ℂ G V} {N M Nbar K : Subgroup G}

omit [LocallyCompactSpace G] [T2Space G] [TotallyDisconnectedSpace G] in

theorem exists_fixedVectors_mk_eq_of_fixed (hρ : IsSmooth ρ) (hKc : IsCompact (K : Set G))
    (hKo : IsOpen (K : Set G))
    (hfact : ∀ k ∈ K, ∃ x ∈ K ⊓ N, ∃ y ∈ K ⊓ M, ∃ z ∈ K ⊓ Nbar, k = x * y * z)
    {w : V} (hwNbar : ∀ z ∈ K ⊓ Nbar, ρ z w = w)
    (hwM : ∀ y ∈ K ⊓ M, Representation.Coinvariants.mk (ρ.comp N.subtype) (ρ y w) =
      Representation.Coinvariants.mk (ρ.comp N.subtype) w) :
    ∃ x ∈ fixedVectors ρ K, Representation.Coinvariants.mk (ρ.comp N.subtype) x =
      Representation.Coinvariants.mk (ρ.comp N.subtype) w := by
  classical
  set S : Subgroup G := stabilizerOf ρ w ⊓ K with hS
  have hSo : IsOpen (S : Set G) := by
    rw [hS, Subgroup.coe_inf]
    exact (hρ w).inter hKo
  have : CompactSpace K := isCompact_iff_compactSpace.1 hKc
  have hfin : Finite (K ⧸ S.subgroupOf K) := by
    refine Subgroup.quotient_finite_of_isOpen _ ?_
    rw [Subgroup.coe_subgroupOf]
    exact hSo.preimage continuous_subtype_val
  have := Fintype.ofFinite (K ⧸ S.subgroupOf K)
  set n : ℂ := (Fintype.card (K ⧸ S.subgroupOf K) : ℂ)
  have hn : n ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero

  have hterm : ∀ k ∈ K, Representation.Coinvariants.mk (ρ.comp N.subtype) (ρ k w) =
      Representation.Coinvariants.mk (ρ.comp N.subtype) w := by
    intro k hk
    obtain ⟨x, hx, y, hy, z, hz, rfl⟩ := hfact k hk
    rw [map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply, hwNbar z hz,
      mk_apply_of_mem ρ N (Subgroup.mem_inf.1 hx).2, hwM y hy]

  have hrep : ∀ (k : K) (c : K ⧸ S.subgroupOf K),
      ρ ((k : G) * ((Quotient.out c : K) : G)) w = ρ ((Quotient.out (k • c) : K) : G) w := by
    intro k c
    have h1 : (QuotientGroup.mk (Quotient.out (k • c)) : K ⧸ S.subgroupOf K) =
        QuotientGroup.mk (k * Quotient.out c) := by
      rw [QuotientGroup.out_eq', ← smul_eq_mul, ← MulAction.Quotient.smul_mk,
        QuotientGroup.out_eq']
    rw [QuotientGroup.eq] at h1
    have h2 : ((Quotient.out (k • c) : K) : G)⁻¹ * ((k : G) * ((Quotient.out c : K) : G)) ∈
        stabilizerOf ρ w := by
      have := (Subgroup.mem_subgroupOf.1 h1)
      simp only [Subgroup.coe_mul, Subgroup.coe_inv] at this
      exact (Subgroup.mem_inf.1 this).1
    rw [← mul_inv_cancel_left ((Quotient.out (k • c) : K) : G)
      ((k : G) * ((Quotient.out c : K) : G)), map_mul, Module.End.mul_apply,
      mem_stabilizerOf.1 h2]
  set y : V := ∑ c : K ⧸ S.subgroupOf K, ρ ((Quotient.out c : K) : G) w with hy
  have hyK : y ∈ fixedVectors ρ K := by
    intro k hk
    rw [hy, map_sum]
    simp only [← Module.End.mul_apply, ← map_mul]
    calc ∑ c : K ⧸ S.subgroupOf K, ρ (k * ((Quotient.out c : K) : G)) w
        = ∑ c : K ⧸ S.subgroupOf K,
            ρ ((Quotient.out ((⟨k, hk⟩ : K) • c) : K) : G) w :=
          Finset.sum_congr rfl fun c _ => hrep ⟨k, hk⟩ c
      _ = ∑ c : K ⧸ S.subgroupOf K, ρ ((Quotient.out c : K) : G) w :=
          Fintype.sum_equiv (MulAction.toPerm (⟨k, hk⟩ : K)) _ _
            (fun c => by rw [MulAction.toPerm_apply])
  have hyq : Representation.Coinvariants.mk (ρ.comp N.subtype) y =
      n • Representation.Coinvariants.mk (ρ.comp N.subtype) w := by
    rw [hy, map_sum, Finset.sum_congr rfl fun c _ => hterm _ (Quotient.out c).2,
      Finset.sum_const, Finset.card_univ, ← Nat.cast_smul_eq_nsmul ℂ]
  refine ⟨n⁻¹ • y, Submodule.smul_mem _ _ hyK, ?_⟩
  rw [map_smul, hyq, smul_smul, inv_mul_cancel₀ hn, one_smul]

omit [LocallyCompactSpace G] [T2Space G] [TotallyDisconnectedSpace G] in

theorem exists_fixedVectors_mk_eq (hρ : IsAdmissible ρ) (hKc : IsCompact (K : Set G))
    (hKo : IsOpen (K : Set G))
    (hfact : ∀ k ∈ K, ∃ z ∈ K ⊓ Nbar, ∃ y ∈ K ⊓ M, ∃ x ∈ K ⊓ N, k = z * y * x)
    (a : G) (haN : ∀ n ∈ N, a * n * a⁻¹ ∈ N) (haN' : ∀ n ∈ N, a⁻¹ * n * a ∈ N)
    (haM : ∀ y ∈ K ⊓ M, a * y = y * a)
    (haK : ∀ z ∈ K ⊓ Nbar, a⁻¹ * z * a ∈ K)
    (hlim : ∀ U ∈ 𝓝 (1 : G), ∃ m : ℕ, ∀ z ∈ K ⊓ Nbar, (a ^ m)⁻¹ * z * a ^ m ∈ U)
    {v : V} (hv : ∀ y ∈ K ⊓ M, Representation.Coinvariants.mk (ρ.comp N.subtype) (ρ y v) =
      Representation.Coinvariants.mk (ρ.comp N.subtype) v) :
    ∃ x ∈ fixedVectors ρ K, Representation.Coinvariants.mk (ρ.comp N.subtype) x =
      Representation.Coinvariants.mk (ρ.comp N.subtype) v := by
  classical
  obtain ⟨hsm, hadm⟩ := hρ

  have hfact' : ∀ k ∈ K, ∃ x ∈ K ⊓ N, ∃ y ∈ K ⊓ M, ∃ z ∈ K ⊓ Nbar, k = x * y * z := by
    intro k hk
    obtain ⟨z, hz, y, hy, x, hx, h⟩ := hfact k⁻¹ (K.inv_mem hk)
    refine ⟨x⁻¹, Subgroup.inv_mem _ hx, y⁻¹, Subgroup.inv_mem _ hy, z⁻¹, Subgroup.inv_mem _ hz, ?_⟩
    rw [← inv_inv k, h]
    group
  set q := Representation.Coinvariants.mk (ρ.comp N.subtype) with hq
  set A := coinvariantsTranslate ρ N a haN with hA
  have hAinj : Function.Injective A := coinvariantsTranslate_injective haN haN'
  set I : Submodule ℂ (Representation.Coinvariants (ρ.comp N.subtype)) :=
    Submodule.map q (fixedVectors ρ K) with hI
  have : FiniteDimensional ℂ (fixedVectors ρ K) := hadm K hKc hKo
  have hIfin : FiniteDimensional ℂ I := by
    rw [hI]
    infer_instance

  have hAI : ∀ u ∈ I, A u ∈ I := by
    rintro _ ⟨x, hx, rfl⟩
    have hNbar : ∀ z ∈ K ⊓ Nbar, ρ z (ρ a x) = ρ a x := by
      intro z hz
      have : z = a * (a⁻¹ * z * a) * a⁻¹ := by group
      rw [this, map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply,
        ← Module.End.mul_apply (ρ a⁻¹), ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply,
        hx _ (haK z hz)]
    have hM0 : ∀ y ∈ K ⊓ M, q (ρ y (ρ a x)) = q (ρ a x) := by
      intro y hy
      rw [← Module.End.mul_apply, ← map_mul, ← haM y hy, map_mul, Module.End.mul_apply,
        hx y (Subgroup.mem_inf.1 hy).1]
    obtain ⟨x', hx', hx'q⟩ := exists_fixedVectors_mk_eq_of_fixed hsm hKc hKo hfact' hNbar hM0
    refine ⟨x', hx', ?_⟩
    rw [hx'q, hA, coinvariantsTranslate_mk]

  set Ai : I →ₗ[ℂ] I := A.restrict hAI with hAi
  have hAiinj : Function.Injective Ai := by
    intro u u' h
    exact Subtype.ext (hAinj (congrArg Subtype.val h))
  have hAisurj : Function.Surjective Ai := LinearMap.injective_iff_surjective.1 hAiinj
  have hback : ∀ u, A u ∈ I → u ∈ I := by
    intro u hu
    obtain ⟨i, hi⟩ := hAisurj ⟨A u, hu⟩
    have : A i = A u := congrArg Subtype.val hi
    rw [← hAinj this]
    exact i.2
  have hiter : ∀ m : ℕ, ∀ u, A^[m] u ∈ I → u ∈ I := by
    intro m
    induction m with
    | zero => exact fun u hu => hu
    | succ m ih =>
      intro u hu
      rw [Function.iterate_succ_apply] at hu
      exact hback u (ih _ hu)

  obtain ⟨m, hm⟩ := hlim _ ((hsm v).mem_nhds (one_mem (stabilizerOf ρ v)))
  have hNbar : ∀ z ∈ K ⊓ Nbar, ρ z (ρ (a ^ m) v) = ρ (a ^ m) v := by
    intro z hz
    have : z = a ^ m * ((a ^ m)⁻¹ * z * a ^ m) * (a ^ m)⁻¹ := by group
    rw [this, map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply,
      ← Module.End.mul_apply (ρ (a ^ m)⁻¹), ← map_mul, inv_mul_cancel, map_one,
      Module.End.one_apply, mem_stabilizerOf.1 (hm z hz)]
  have hM0 : ∀ y ∈ K ⊓ M, q (ρ y (ρ (a ^ m) v)) = q (ρ (a ^ m) v) := by
    intro y hy
    have hc : a ^ m * y = y * a ^ m := ((Commute.pow_left (haM y hy) m))
    rw [← Module.End.mul_apply, ← map_mul, ← hc, map_mul, Module.End.mul_apply,
      ← iterate_coinvariantsTranslate_mk haN, hv y hy, iterate_coinvariantsTranslate_mk haN]
  obtain ⟨x, hx, hxq⟩ := exists_fixedVectors_mk_eq_of_fixed hsm hKc hKo hfact' hNbar hM0
  have hmem : A^[m] (q v) ∈ I := by
    rw [hA, iterate_coinvariantsTranslate_mk haN, ← hxq]
    exact ⟨x, hx, rfl⟩
  obtain ⟨x', hx', hx'q⟩ := hiter m _ hmem
  exact ⟨x', hx', hx'q⟩

end JacquetLemma

end GroundTheory.Automorphic
