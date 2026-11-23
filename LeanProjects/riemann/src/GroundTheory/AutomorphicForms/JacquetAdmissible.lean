import Mathlib
import GroundTheory.AutomorphicForms.CuspidalAdmissible
import GroundTheory.AutomorphicForms.AdmissibleInduction

noncomputable section

namespace GroundTheory.Automorphic

namespace Parabolic

open Matrix Iwasawa GLnLocal ValuativeRel Topology Filter Set MeasureTheory Measure

section Quotient

variable {G : Type*} [Group G] {U : Type*} [AddCommGroup U] [Module ℂ U]
  {τ : Representation ℂ G U}

def quotientMk (Y : Submodule ℂ U) (hY : ∀ g, Y ≤ Y.comap (τ g)) :
    Representation.IntertwiningMap τ (Representation.quotient τ Y hY) :=
  ⟨Y.mkQ, fun _ => LinearMap.ext fun _ => rfl⟩

theorem quotientMk_apply (Y : Submodule ℂ U) (hY : ∀ g, Y ≤ Y.comap (τ g)) (x : U) :
    quotientMk Y hY x = Submodule.Quotient.mk x := rfl

theorem quotientMk_surjective (Y : Submodule ℂ U) (hY : ∀ g, Y ≤ Y.comap (τ g)) :
    Function.Surjective (quotientMk Y hY) :=
  Submodule.mkQ_surjective Y

theorem isSmooth_quotient [TopologicalSpace G] [IsTopologicalGroup G] (hτ : IsSmooth τ) (Y : Submodule ℂ U)
    (hY : ∀ g, Y ≤ Y.comap (τ g)) : IsSmooth (Representation.quotient τ Y hY) := by
  intro x
  obtain ⟨u, rfl⟩ := Submodule.mkQ_surjective Y x
  refine Subgroup.isOpen_mono (fun g hg => ?_) (hτ u)
  show Representation.quotient τ Y hY g (Submodule.Quotient.mk u) = Submodule.Quotient.mk u
  rw [Representation.quotient_apply, Submodule.mapQ_apply, mem_stabilizerOf.1 hg]

theorem exists_mem_subset_of_chain {c : Set (Submodule ℂ U)} (hc : IsChain (· ≤ ·) c)
    {y : Submodule ℂ U} (hy : y ∈ c) (S : Finset U) (hS : ∀ s ∈ S, ∃ Z ∈ c, s ∈ Z) :
    ∃ Z ∈ c, ∀ s ∈ S, s ∈ Z := by
  classical
  induction S using Finset.induction_on with
  | empty => exact ⟨y, hy, by simp⟩
  | insert a S ha ih =>
    obtain ⟨Z₁, hZ₁, haZ₁⟩ := hS a (Finset.mem_insert_self a S)
    obtain ⟨Z₂, hZ₂, hSZ₂⟩ := ih fun s hs => hS s (Finset.mem_insert_of_mem hs)
    rcases hc.total hZ₁ hZ₂ with h | h
    · exact ⟨Z₂, hZ₂, fun s hs => by
        rcases Finset.mem_insert.1 hs with rfl | hs
        · exact h haZ₁
        · exact hSZ₂ s hs⟩
    · exact ⟨Z₁, hZ₁, fun s hs => by
        rcases Finset.mem_insert.1 hs with rfl | hs
        · exact haZ₁
        · exact h (hSZ₂ s hs)⟩

theorem exists_irreducible_quotient [Nontrivial U] (S : Finset U)
    (hS : Submodule.span ℂ {x | ∃ g, ∃ s ∈ S, x = τ g s} = ⊤) :
    ∃ (Y : Submodule ℂ U) (hY : ∀ g, Y ≤ Y.comap (τ g)),
      (Representation.quotient τ Y hY).IsIrreducible := by
  classical
  let P : Set (Submodule ℂ U) := {Y | (∀ g, Y ≤ Y.comap (τ g)) ∧ ¬ ((S : Set U) ⊆ Y)}

  have htop : ∀ Z : Submodule ℂ U, (∀ g, Z ≤ Z.comap (τ g)) → (S : Set U) ⊆ Z → Z = ⊤ := by
    intro Z hZ hSZ
    rw [eq_top_iff, ← hS]
    refine Submodule.span_le.2 ?_
    rintro _ ⟨g, s, hs, rfl⟩
    exact hZ g (hSZ hs)
  have hbot : (⊥ : Submodule ℂ U) ∈ P := by
    refine ⟨fun g => bot_le, fun h => ?_⟩
    have := htop ⊥ (fun g => bot_le) h
    exact bot_ne_top this
  obtain ⟨Y, -, hYmax⟩ := zorn_le_nonempty₀ P (fun c hcP hc y hy => by
    refine ⟨sSup c, ⟨fun g x hx => ?_, fun hsub => ?_⟩, fun z hz => le_sSup hz⟩
    · obtain ⟨Z, hZ, hxZ⟩ := (Submodule.mem_sSup_of_directed ⟨y, hy⟩ hc.directedOn).1 hx
      exact (Submodule.mem_sSup_of_directed ⟨y, hy⟩ hc.directedOn).2 ⟨Z, hZ, (hcP hZ).1 g hxZ⟩
    · obtain ⟨Z, hZ, hSZ⟩ := exists_mem_subset_of_chain hc hy S fun s hs =>
        (Submodule.mem_sSup_of_directed ⟨y, hy⟩ hc.directedOn).1 (hsub hs)
      exact (hcP hZ).2 fun s hs => hSZ s hs) ⊥ hbot
  obtain ⟨⟨hYs, hYS⟩, hYm⟩ := hYmax
  refine ⟨Y, hYs, ?_⟩
  have hYtop : Y ≠ ⊤ := fun h => hYS (by rw [h]; exact fun _ _ => Submodule.mem_top)
  refine { exists_pair_ne := ⟨⊥, ⊤, fun h => hYtop ?_⟩, eq_bot_or_eq_top := fun X => ?_ }
  · have h' := congrArg Subrepresentation.toSubmodule h
    rw [eq_top_iff]
    intro x _
    have hx : (Submodule.Quotient.mk x : U ⧸ Y) ∈ (⊤ : Subrepresentation (Representation.quotient τ Y hYs)).toSubmodule :=
      Submodule.mem_top
    rw [← h'] at hx
    exact (Submodule.Quotient.mk_eq_zero Y).1 hx
  · let Z : Submodule ℂ U := X.toSubmodule.comap Y.mkQ
    have hZs : ∀ g, Z ≤ Z.comap (τ g) := by
      intro g x hx
      show Submodule.Quotient.mk (τ g x) ∈ X.toSubmodule
      have := X.apply_mem_toSubmodule g hx
      exact this
    have hYZ : Y ≤ Z := by
      intro x hx
      show Submodule.Quotient.mk x ∈ X.toSubmodule
      rw [(Submodule.Quotient.mk_eq_zero Y).2 hx]
      exact X.toSubmodule.zero_mem
    by_cases hSZ : (S : Set U) ⊆ Z
    · right
      have hZt := htop Z hZs hSZ
      apply Subrepresentation.ext
      show X.toSubmodule = ⊤
      rw [eq_top_iff]
      intro x _
      obtain ⟨u, rfl⟩ := Submodule.mkQ_surjective Y x
      have hu : u ∈ Z := by rw [hZt]; exact Submodule.mem_top
      exact hu
    · left
      have hZY : Z ≤ Y := hYm ⟨hZs, hSZ⟩ hYZ
      apply Subrepresentation.ext
      show X.toSubmodule = ⊥
      rw [eq_bot_iff]
      intro x hx
      obtain ⟨u, rfl⟩ := Submodule.mkQ_surjective Y x
      rw [Submodule.mem_bot]
      exact (Submodule.Quotient.mk_eq_zero Y).2 (hZY hx)

end Quotient

variable {F : Type*} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {n : ℕ} {α : Type*} [LinearOrder α] {β : Fin n → α}

theorem sqrtModular_leviIncl_of_mem {γ : Fin n → ℕ} (m : levi F n β)
    (hm : (m : GL (Fin n) F) ∈ unipotentRadical F n γ) :
    sqrtModular F n β (leviIncl m) = 1 := by
  have key : modularCharacter (leviIncl m) = 1 := by
    obtain ⟨e, he⟩ := exists_pow_mul_mem_of_isCompact F n
      (Set.toFinite ({(m : GL (Fin n) F), (m : GL (Fin n) F)⁻¹} : Set _)).isCompact
    let t : blockUpper F n β :=
      ⟨rankTorus F n γ e, levi_le_blockUpper (diagGL_mem_levi _)⟩
    have hint : ((t * leviIncl m * t⁻¹ : blockUpper F n β) : GL (Fin n) F) ∈ integralGL F n := by
      show rankTorus F n γ e * (m : GL (Fin n) F) * (rankTorus F n γ e)⁻¹ ∈ integralGL F n
      rw [mem_integralGL_iff]
      refine ⟨rankTorus_conj_apply_mem hm (fun i j => he _ (by simp) i j), fun i j => ?_⟩
      have : (rankTorus F n γ e * (m : GL (Fin n) F) * (rankTorus F n γ e)⁻¹)⁻¹ =
          rankTorus F n γ e * (m : GL (Fin n) F)⁻¹ * (rankTorus F n γ e)⁻¹ := by group
      rw [this]
      exact rankTorus_conj_apply_mem ((unipotentRadical F n γ).inv_mem hm)
        (fun i j => he _ (by simp) i j) i j
    have h1 := Measures.modularCharacter_eq_one_of_mem_integralGL (t * leviIncl m * t⁻¹) hint
    rw [map_mul, map_mul, mul_comm (modularCharacter t), mul_assoc, ← map_mul, mul_inv_cancel,
      map_one, mul_one] at h1
    exact h1
  show ((NNReal.sqrt (modularCharacter (leviIncl m)) : ℝ) : ℂ) = 1
  rw [key]
  simp

section Transitivity

variable {V : Type*} [AddCommGroup V] [Module ℂ V] {π : Representation ℂ (GL (Fin n) F) V}

theorem subsingleton_coinvariants_jacquetRep {β γ : Fin n → ℕ}
    (hβγ : ∀ i j, β j < β i → γ j < γ i) (h : Subsingleton (JacquetModule F n γ π)) :
    Subsingleton (Representation.Coinvariants
      ((jacquetRep F n β π).comp (leviUnipotent F n β γ).subtype)) := by
  set q' := Representation.Coinvariants.mk
    ((jacquetRep F n β π).comp (leviUnipotent F n β γ).subtype)
  set qβ := Representation.Coinvariants.mk (π.comp (unipotentRadical F n β).subtype)
  have hβeq : ∀ i j, γ i = γ j → β i = β j := by
    intro i j hij
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hlt
    · have := hβγ j i hlt
      omega
    · have := hβγ i j hlt
      omega
  have hker : Representation.Coinvariants.ker (π.comp (unipotentRadical F n γ).subtype) ≤
      LinearMap.ker (q' ∘ₗ qβ) := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨⟨u, w⟩, rfl⟩
    obtain ⟨huP, hu1⟩ := mem_unipotentRadical.1 u.2
    have huβ : (u : GL (Fin n) F) ∈ blockUpper F n β := fun i j hij => huP (hβγ i j hij)
    set p : blockUpper F n β := ⟨u, huβ⟩
    set m := leviProj F n β p
    have hmN : ((m : levi F n β) : GL (Fin n) F) ∈ unipotentRadical F n γ := by
      refine mem_unipotentRadical.2 ⟨fun i j hij => ?_, fun i j hij => ?_⟩
      · show ((m : levi F n β) : GL (Fin n) F) i j = 0
        rw [leviProj_apply]
        split_ifs
        · exact huP hij
        · rfl
      · rw [leviProj_apply, if_pos (hβeq i j hij)]
        exact hu1 i j hij
    have hn' := leviProj_inv_mul_mem p
    have hu : (u : GL (Fin n) F) = ((m : levi F n β) : GL (Fin n) F) *
        (((leviIncl m)⁻¹ * p : blockUpper F n β) : GL (Fin n) F) := by
      rw [Subgroup.coe_mul, Subgroup.coe_inv, leviIncl_coe, mul_inv_cancel_left]
    simp only [SetLike.mem_coe, LinearMap.mem_ker, LinearMap.coe_comp, Function.comp_apply,
      MonoidHom.coe_comp, Subgroup.coe_subtype, map_sub]
    rw [hu, map_mul, Module.End.mul_apply, mk_apply_levi, mk_apply_of_mem π _ hn',
      sqrtModular_leviIncl_of_mem m hmN, one_smul, sub_eq_zero]
    exact Representation.Coinvariants.mk_self_apply
      (ρ := (jacquetRep F n β π).comp (leviUnipotent F n β γ).subtype)
      ⟨m, Subgroup.mem_subgroupOf.2 hmN⟩ (qβ w)
  have hzero : ∀ x : V, q' (qβ x) = 0 := by
    intro x
    have hx : x ∈ Representation.Coinvariants.ker (π.comp (unipotentRadical F n γ).subtype) :=
      (Representation.Coinvariants.mk_eq_zero _).1 (Subsingleton.elim _ _)
    exact hker hx
  refine ⟨fun a b => ?_⟩
  obtain ⟨a, rfl⟩ := Representation.Coinvariants.mk_surjective _ a
  obtain ⟨a, rfl⟩ := Representation.Coinvariants.mk_surjective _ a
  obtain ⟨b, rfl⟩ := Representation.Coinvariants.mk_surjective _ b
  obtain ⟨b, rfl⟩ := Representation.Coinvariants.mk_surjective _ b
  exact (hzero a).trans (hzero b).symm

end Transitivity

section Generators

variable {G : Type*} [Group G] {V : Type*} [AddCommGroup V] [Module ℂ V]

theorem span_range_eq_top_of_isIrreducible {ρ : Representation ℂ G V} [ρ.IsIrreducible] {v : V}
    (hv : v ≠ 0) : Submodule.span ℂ (Set.range fun g : G => ρ g v) = ⊤ := by
  have hstable : ∀ g : G, Submodule.span ℂ (Set.range fun h : G => ρ h v) ≤
      (Submodule.span ℂ (Set.range fun h : G => ρ h v)).comap (ρ g) := by
    intro g
    refine Submodule.span_le.2 ?_
    rintro _ ⟨h, rfl⟩
    exact Submodule.subset_span ⟨g * h, by simp [map_mul, Module.End.mul_apply]⟩
  let Wsub : Subrepresentation ρ :=
    ⟨Submodule.span ℂ (Set.range fun h : G => ρ h v), fun g _ hx => hstable g hx⟩
  have hW : Wsub = ⊤ := (eq_bot_or_eq_top Wsub).resolve_left fun h => hv (by
    have hvW : v ∈ Wsub.toSubmodule := Submodule.subset_span ⟨1, by simp⟩
    rw [h] at hvW
    exact (Submodule.mem_bot ℂ).1 hvW)
  exact congrArg Subrepresentation.toSubmodule hW

theorem subsingleton_coinvariants_of_surjective {W : Type*} [AddCommGroup W] [Module ℂ W]
    {ρ : Representation ℂ G V} {σ : Representation ℂ G W} {H : Subgroup G}
    (f : Representation.IntertwiningMap ρ σ) (hf : Function.Surjective f)
    (h : Subsingleton (Representation.Coinvariants (ρ.comp H.subtype))) :
    Subsingleton (Representation.Coinvariants (σ.comp H.subtype)) := by
  have hker : Representation.Coinvariants.ker (ρ.comp H.subtype) ≤
      (Representation.Coinvariants.ker (σ.comp H.subtype)).comap f.toLinearMap := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨⟨u, x⟩, rfl⟩
    simp only [MonoidHom.coe_comp, Function.comp_apply, Subgroup.coe_subtype, SetLike.mem_coe,
      Submodule.mem_comap, map_sub, Representation.IntertwiningMap.toLinearMap_apply]
    rw [Representation.IntertwiningMap.isIntertwining]
    exact Representation.Coinvariants.sub_mem_ker (ρ := σ.comp H.subtype) u (f x)
  have hzero : ∀ y : W, Representation.Coinvariants.mk (σ.comp H.subtype) y = 0 := by
    intro y
    obtain ⟨x, rfl⟩ := hf y
    exact (Representation.Coinvariants.mk_eq_zero _).2 (hker
      ((Representation.Coinvariants.mk_eq_zero _).1 (Subsingleton.elim _ _)))
  refine ⟨fun a b => ?_⟩
  obtain ⟨a, rfl⟩ := Representation.Coinvariants.mk_surjective _ a
  obtain ⟨b, rfl⟩ := Representation.Coinvariants.mk_surjective _ b
  rw [hzero a, hzero b]

end Generators

section Jacquet

universe u

variable {V : Type u} [AddCommGroup V] [Module ℂ V] {π : Representation ℂ (GL (Fin n) F) V}

theorem exists_finset_span_jacquetRep (hπ : IsSmooth π) {v : V}
    (hv : Submodule.span ℂ (Set.range fun g : GL (Fin n) F => π g v) = ⊤) :
    ∃ S : Finset (JacquetModule F n β π),
      Submodule.span ℂ {x | ∃ m, ∃ s ∈ S, x = jacquetRep F n β π m s} = ⊤ := by
  classical
  obtain ⟨m₀, -, hm₀⟩ := (hasBasis_nhds_one F n).mem_iff.1 ((hπ v).mem_nhds (one_mem _))
  set K₀ := integralGL F n
  set Km := congruenceSubgroup F n m₀
  have hvK : v ∈ fixedVectors π Km := fun k hk => hm₀ hk
  have : CompactSpace K₀ := isCompact_iff_compactSpace.1 (isCompact_integralGL F n)
  have hQ : Finite (K₀ ⧸ Km.subgroupOf K₀) := by
    refine Subgroup.quotient_finite_of_isOpen _ ?_
    rw [Subgroup.coe_subgroupOf]
    exact (isOpen_congruenceSubgroup F n m₀).preimage continuous_subtype_val
  have := Fintype.ofFinite (K₀ ⧸ Km.subgroupOf K₀)
  let R : Finset (GL (Fin n) F) :=
    Finset.univ.image fun q : K₀ ⧸ Km.subgroupOf K₀ => ((Quotient.out q : K₀) : GL (Fin n) F)
  have hR : ∀ k ∈ K₀, ∃ r ∈ R, π k v = π r v := by
    intro k hk
    refine ⟨_, Finset.mem_image_of_mem _ (Finset.mem_univ (QuotientGroup.mk (⟨k, hk⟩ : K₀))), ?_⟩
    exact act_eq_of_mk_eq π hvK (a := ⟨k, hk⟩)
      (b := Quotient.out (QuotientGroup.mk (⟨k, hk⟩ : K₀) : K₀ ⧸ Km.subgroupOf K₀))
      (QuotientGroup.out_eq' _).symm
  set q := Representation.Coinvariants.mk (π.comp (unipotentRadical F n β).subtype)
  refine ⟨R.image fun r => q (π r v), ?_⟩
  set T := Submodule.span ℂ {x | ∃ m, ∃ s ∈ R.image fun r => q (π r v), x = jacquetRep F n β π m s}
  have hclaim : ∀ g : GL (Fin n) F, q (π g v) ∈ T := by
    intro g
    obtain ⟨p, hp, k, hk, rfl⟩ := exists_blockUpper_mul_integralGL' (β := β) g
    obtain ⟨r, hr, hrv⟩ := hR k hk
    set p' : blockUpper F n β := ⟨p, hp⟩
    set m := leviProj F n β p'
    have hn' := leviProj_inv_mul_mem p'
    have hpeq : p = ((m : levi F n β) : GL (Fin n) F) *
        (((leviIncl m)⁻¹ * p' : blockUpper F n β) : GL (Fin n) F) := by
      rw [Subgroup.coe_mul, Subgroup.coe_inv, leviIncl_coe, mul_inv_cancel_left]
    rw [map_mul, Module.End.mul_apply, hrv, hpeq, map_mul, Module.End.mul_apply, mk_apply_levi,
      mk_apply_of_mem π _ hn']
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨m, q (π r v),
      Finset.mem_image_of_mem _ hr, rfl⟩)
  rw [eq_top_iff]
  intro x _
  obtain ⟨y, rfl⟩ := Representation.Coinvariants.mk_surjective _ x
  have hy : y ∈ Submodule.span ℂ (Set.range fun g : GL (Fin n) F => π g v) := by
    rw [hv]
    exact Submodule.mem_top
  have hmap : Submodule.map q (Submodule.span ℂ (Set.range fun g : GL (Fin n) F => π g v)) ≤ T := by
    rw [Submodule.map_span]
    refine Submodule.span_le.2 ?_
    rintro _ ⟨_, ⟨g, rfl⟩, rfl⟩
    exact hclaim g
  exact hmap ⟨y, hy, rfl⟩

theorem nontrivial_jacquetModule_const [Nontrivial V] :
    Nontrivial (JacquetModule F n (fun _ : Fin n => (0 : ℕ)) π) := by
  obtain ⟨v, hv⟩ := exists_ne (0 : V)
  refine ⟨⟨Representation.Coinvariants.mk _ v, 0, fun h => hv ?_⟩⟩
  have hmem := (Representation.Coinvariants.mk_eq_zero _).1 h
  have hle : Representation.Coinvariants.ker
      (π.comp (unipotentRadical F n (fun _ : Fin n => (0 : ℕ))).subtype) ≤ ⊥ := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨⟨u, x⟩, rfl⟩
    have hu : (u : GL (Fin n) F) = 1 := by
      apply Units.ext
      ext i j
      exact (mem_unipotentRadical.1 u.2).2 i j rfl
    simp [hu]
  exact (Submodule.mem_bot ℂ).1 (hle hmem)

def refineFun (β γ : Fin n → ℕ) : Fin n → ℕ :=
  fun i => (Finset.univ.sup γ + 1) * β i + γ i

theorem lt_refineFun_bound (γ : Fin n → ℕ) (i : Fin n) : γ i < Finset.univ.sup γ + 1 :=
  Nat.lt_succ_of_le (Finset.le_sup (Finset.mem_univ i))

theorem refineFun_lt {β γ : Fin n → ℕ} {i j : Fin n} (h : β j < β i) :
    refineFun β γ j < refineFun β γ i := by
  have h1 := lt_refineFun_bound γ j
  simp only [refineFun]
  set B := Finset.univ.sup γ + 1
  have : B * β j + B ≤ B * β i := by nlinarith
  omega

theorem refineFun_eq_iff {β γ : Fin n → ℕ} {i j : Fin n} :
    refineFun β γ i = refineFun β γ j ↔ β i = β j ∧ γ i = γ j := by
  constructor
  · intro h
    have hβ : β i = β j := by
      by_contra hne
      rcases lt_or_gt_of_ne hne with hlt | hlt
      · exact (refineFun_lt (γ := γ) hlt).ne h
      · exact (refineFun_lt (γ := γ) hlt).ne' h
    refine ⟨hβ, ?_⟩
    simp only [refineFun, hβ] at h
    omega
  · rintro ⟨h1, h2⟩
    simp [refineFun, h1, h2]

theorem refineFun_lt_of_eq {β γ : Fin n → ℕ} {i j : Fin n} (hβ : β i = β j) :
    refineFun β γ j < refineFun β γ i ↔ γ j < γ i := by
  simp only [refineFun, hβ]
  omega

variable (F) in

theorem leviUnipotent_refineFun (β γ : Fin n → ℕ) :
    leviUnipotent F n β γ = leviUnipotent F n β (refineFun β γ) := by
  ext u
  simp only [leviUnipotent, Subgroup.mem_subgroupOf]
  have hu := mem_levi.1 u.2
  constructor
  · intro h
    obtain ⟨hP, h1⟩ := mem_unipotentRadical.1 h
    refine mem_unipotentRadical.2 ⟨fun i j hij => ?_, fun i j hij => ?_⟩
    · by_cases hb : β i = β j
      · exact hP ((refineFun_lt_of_eq hb).1 hij)
      · exact hu i j hb
    · exact h1 i j (refineFun_eq_iff.1 hij).2
  · intro h
    obtain ⟨hP, h1⟩ := mem_unipotentRadical.1 h
    refine mem_unipotentRadical.2 ⟨fun i j hij => ?_, fun i j hij => ?_⟩
    · by_cases hb : β i = β j
      · exact hP ((refineFun_lt_of_eq hb).2 hij)
      · exact hu i j hb
    · by_cases hb : β i = β j
      · exact h1 i j (refineFun_eq_iff.2 ⟨hb, hij⟩)
      · rw [hu i j hb, one_apply_ne (fun e => hb (by rw [e]))]

theorem card_image_lt_refineFun {β γ : Fin n → ℕ} (h : ∃ i j, β i = β j ∧ γ i ≠ γ j) :
    (Finset.univ.image β).card < (Finset.univ.image (refineFun β γ)).card := by
  classical
  obtain ⟨i, j, hij, hγ⟩ := h
  set B := Finset.univ.sup γ + 1
  have hdiv : ∀ k, refineFun β γ k / B = β k := by
    intro k
    simp only [refineFun]
    rw [Nat.mul_add_div (Nat.succ_pos _), Nat.div_eq_of_lt (lt_refineFun_bound γ k), add_zero]
  have himg : Finset.univ.image β = (Finset.univ.image (refineFun β γ)).image (· / B) := by
    rw [Finset.image_image]
    congr 1
    funext k
    exact (hdiv k).symm
  rw [himg]
  refine lt_of_le_of_ne Finset.card_image_le fun hc => ?_
  have hinj := Finset.card_image_iff.1 hc
  have : refineFun β γ i = refineFun β γ j :=
    hinj (by simp) (by simp) (by simp only [hdiv, hij])
  exact hγ (refineFun_eq_iff.1 this).2

theorem exists_embedding_parabolicInd [π.IsIrreducible] (hπ : IsSmooth π) :
    ∃ (β : Fin n → ℕ) (W : Type u) (_ : AddCommGroup W) (_ : Module ℂ W)
      (σ : Representation ℂ (levi F n β) W), σ.IsIrreducible ∧ IsSmooth σ ∧ IsCuspidal σ ∧
        IsAdmissible σ ∧ ∃ Φ : Representation.IntertwiningMap π (parabolicInd F n β σ),
          Function.Injective Φ := by
  classical
  obtain ⟨v, hv0⟩ := exists_ne_zero_of_isIrreducible (ρ := π)
  have : Nontrivial V := ⟨⟨v, 0, hv0⟩⟩
  have hspan := span_range_eq_top_of_isIrreducible (ρ := π) hv0

  let P : ℕ → Prop := fun k => ∃ β : Fin n → ℕ, (Finset.univ.image β).card = k ∧
    Nontrivial (JacquetModule F n β π)
  have hbound : ∀ β : Fin n → ℕ, (Finset.univ.image β).card ≤ n := fun β =>
    (Finset.card_image_le).trans (by simp)
  have hP0 : P (Finset.univ.image fun _ : Fin n => (0 : ℕ)).card :=
    ⟨_, rfl, nontrivial_jacquetModule_const⟩
  obtain ⟨β, hβcard, hβnt⟩ := Nat.findGreatest_spec (hbound _) hP0
  have hfinest : ∀ γ : Fin n → ℕ, (∃ i j, β i = β j ∧ γ i ≠ γ j) →
      Subsingleton (JacquetModule F n (refineFun β γ) π) := by
    intro γ hγ
    have hlt := card_image_lt_refineFun hγ
    rw [hβcard] at hlt
    have := Nat.findGreatest_is_greatest hlt (hbound _)
    rw [← not_nontrivial_iff_subsingleton]
    exact fun hnt => this ⟨_, rfl, hnt⟩

  obtain ⟨S, hS⟩ := exists_finset_span_jacquetRep (β := β) hπ hspan
  obtain ⟨Y, hY, hirr⟩ := exists_irreducible_quotient (τ := jacquetRep F n β π) S hS
  let σ := Representation.quotient (jacquetRep F n β π) Y hY
  have hσs : IsSmooth σ := isSmooth_quotient (isSmooth_jacquetRep π hπ) Y hY
  have hσc : IsCuspidal σ := by
    intro γ hγ
    have h1 := subsingleton_coinvariants_jacquetRep (π := π) (β := β) (γ := refineFun β γ)
      (fun i j h => refineFun_lt h) (hfinest γ hγ)
    rw [← leviUnipotent_refineFun] at h1
    exact subsingleton_coinvariants_of_surjective (quotientMk Y hY) (quotientMk_surjective Y hY) h1
  have hσa : IsAdmissible σ := isAdmissible_of_isCuspidal hσs hσc
  refine ⟨β, _, inferInstance, inferInstance, σ, hirr, hσs, hσc, hσa, ?_⟩

  set Φ := (frobeniusParabolic F n β σ hπ).symm (quotientMk Y hY)
  refine ⟨Φ, ?_⟩
  rcases Representation.IsIrreducible.injective_or_eq_zero Φ with h | h
  · exact h
  · exfalso
    have h0 : quotientMk Y hY = 0 := by
      rw [← (frobeniusParabolic F n β σ hπ).apply_symm_apply (quotientMk Y hY)]
      show frobeniusParabolic F n β σ hπ Φ = 0
      rw [h, map_zero]
    obtain ⟨w, hw⟩ := exists_ne_zero_of_isIrreducible (ρ := σ)
    obtain ⟨x, rfl⟩ := quotientMk_surjective Y hY w
    exact hw (by rw [h0]; rfl)

theorem isAdmissible_of_isIrreducible [π.IsIrreducible] (hπ : IsSmooth π) : IsAdmissible π := by
  obtain ⟨β, W, _, _, σ, -, -, -, hσa, Φ, hΦ⟩ := exists_embedding_parabolicInd hπ
  exact isAdmissible_of_injective hπ (isAdmissible_parabolicInd hσa) Φ hΦ

end Jacquet

end Parabolic

end GroundTheory.Automorphic
