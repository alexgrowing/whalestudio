import Mathlib
import GroundTheory.AutomorphicForms.LeviCartan
import GroundTheory.AutomorphicForms.SmoothRepSchur
import GroundTheory.AutomorphicForms.MeasuresModulus

noncomputable section

namespace GroundTheory.Automorphic

namespace Parabolic

open Matrix Iwasawa GLnLocal ValuativeRel Topology Filter Set

section Normalize

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [LocallyCompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
  {V : Type*} [AddCommGroup V] [Module ℂ V] {ρ : Representation ℂ G V} {K : Subgroup G}

theorem fixedProj_act_of_normalizes (hρ : IsSmooth ρ) (hKc : IsCompact (K : Set G))
    (hKo : IsOpen (K : Set G)) {g : G} (hg : ∀ k ∈ K, g * k * g⁻¹ ∈ K)
    (hg' : ∀ k ∈ K, g⁻¹ * k * g ∈ K) (v : V) :
    (fixedProj ρ hρ hKc hKo (ρ g v) : V) = ρ g (fixedProj ρ hρ hKc hKo v) := by
  have hmem : ρ g (fixedProj ρ hρ hKc hKo v : V) ∈ fixedVectors ρ K := by
    intro k hk
    have hk' : k = g * (g⁻¹ * k * g) * g⁻¹ := by group
    rw [hk', map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply,
      ← Module.End.mul_apply (ρ g⁻¹), ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply,
      (fixedProj ρ hρ hKc hKo v).2 _ (hg' k hk)]
  have hmap : coinvariantsKer ρ K ≤ (coinvariantsKer ρ K).comap (ρ g) := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨⟨k, x⟩, rfl⟩
    simp only [MonoidHom.coe_comp, Function.comp_apply, Subgroup.coe_subtype, SetLike.mem_coe,
      Submodule.mem_comap, map_sub]
    have hk : ρ g (ρ (k : G) x) = ρ (g * (k : G) * g⁻¹) (ρ g x) := by
      rw [← Module.End.mul_apply, ← map_mul, ← Module.End.mul_apply, ← map_mul, inv_mul_cancel_right]
    rw [hk]
    exact sub_mem_coinvariantsKer (hg k k.2) (ρ g x)
  have h := (fixedProj_eq_iff hρ hKc hKo (v := ρ g v) (w := ⟨_, hmem⟩)).2 (by
    show ρ g v - ρ g _ ∈ coinvariantsKer ρ K
    rw [← map_sub]
    exact hmap (sub_fixedProj_mem hρ hKc hKo v))
  exact congrArg Subtype.val h

end Normalize

variable {F : Type*} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {n : ℕ} {α : Type*} [LinearOrder α] {β : Fin n → α}

section DiagPow

open Cartan

theorem diagPow_add (μ ν : Fin n → ℤ) : diagPow F n (μ + ν) = diagPow F n μ * diagPow F n ν := by
  apply Units.ext
  rw [Units.val_mul, coe_diagPow, coe_diagPow, coe_diagPow, diagonal_mul_diagonal]
  congr 1
  funext i
  rw [Pi.add_apply, zpow_add₀ (Cartan.uniformizer_ne_zero F)]

theorem diagPow_zero : diagPow F n 0 = 1 := by
  apply Units.ext
  rw [coe_diagPow, Units.val_one]
  simp

theorem diagPow_neg (μ : Fin n → ℤ) : diagPow F n (-μ) = (diagPow F n μ)⁻¹ := by
  refine eq_inv_of_mul_eq_one_left ?_
  rw [← diagPow_add, neg_add_cancel, diagPow_zero]

theorem diagPow_conj_apply (μ : Fin n → ℤ) (g : GL (Fin n) F) (i j : Fin n) :
    (diagPow F n μ * g * (diagPow F n μ)⁻¹ : GL (Fin n) F) i j =
      (uniformizer F : F) ^ (μ i - μ j) * g i j := by
  rw [← diagPow_neg]
  rw [Units.val_mul, Units.val_mul, coe_diagPow, coe_diagPow, mul_diagonal, diagonal_mul,
    Pi.neg_apply,
    zpow_sub₀ (Cartan.uniformizer_ne_zero F), _root_.zpow_neg, div_eq_mul_inv]
  ring

theorem diagPow_mem_levi (μ : Fin n → ℤ) : diagPow F n μ ∈ levi F n β := by
  rw [mem_levi]
  intro i j hij
  have : i ≠ j := fun h => hij (h ▸ rfl)
  show (diagPow F n μ : Matrix (Fin n) (Fin n) F) i j = 0
  rw [coe_diagPow, diagonal_apply_ne _ this]

theorem diagPow_mem_center {c : Fin n → ℤ} (hc : ∀ i j, β i = β j → c i = c j) :
    (⟨diagPow F n c, diagPow_mem_levi c⟩ : levi F n β) ∈ Submonoid.center (levi F n β) := by
  rw [Submonoid.mem_center_iff]
  intro g
  apply Subtype.ext
  apply Units.ext
  ext i j
  show (((g : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) * (diagPow F n c : Matrix (Fin n) (Fin n) F)) i j
    = ((diagPow F n c : Matrix (Fin n) (Fin n) F) * ((g : GL (Fin n) F) : Matrix (Fin n) (Fin n) F)) i j
  rw [coe_diagPow, mul_diagonal, diagonal_mul]
  by_cases h : β i = β j
  · rw [hc i j h, mul_comm]
  · have : ((g : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) i j = 0 := mem_levi.1 g.2 i j h
    rw [this, zero_mul, mul_zero]

theorem diagPow_conj_mem_congruenceSubgroup {μ : Fin n → ℤ} {u : GL (Fin n) F} {t m : ℕ}
    {C : ℤ} (hC : ((t + m : ℕ) : ℤ) < C)
    (hu : ∀ i j, u i j = (1 : Matrix (Fin n) (Fin n) F) i j ∨ μ j + C ≤ μ i)
    (hu' : ∀ i j, (u⁻¹ : GL (Fin n) F) i j = (1 : Matrix (Fin n) (Fin n) F) i j ∨ μ j + C ≤ μ i)
    (hb : ∀ i j, (uniformizer F : F) ^ t * u i j ∈ 𝒪[F])
    (hb' : ∀ i j, (uniformizer F : F) ^ t * (u⁻¹ : GL (Fin n) F) i j ∈ 𝒪[F]) :
    diagPow F n μ * u * (diagPow F n μ)⁻¹ ∈ congruenceSubgroup F n m := by
  have key : ∀ x : F, ∀ i j, (x = (1 : Matrix (Fin n) (Fin n) F) i j ∨ μ j + C ≤ μ i) →
      (uniformizer F : F) ^ t * x ∈ 𝒪[F] →
      (uniformizer F : F) ^ (μ i - μ j) * x ∈ 𝒪[F] ∧
        valuation F ((uniformizer F : F) ^ (μ i - μ j) * x - (1 : Matrix (Fin n) (Fin n) F) i j) ≤
          valuation F (uniformizer F : F) ^ m := by
    intro x i j hx hxb
    rcases hx with hx | hx
    · by_cases hij : i = j
      · subst hij
        rw [hx, sub_self, zpow_zero, one_mul, one_apply_eq, sub_self, map_zero]
        exact ⟨one_mem _, zero_le'⟩
      · rw [hx, one_apply_ne hij, mul_zero, sub_zero, map_zero]
        exact ⟨zero_mem _, zero_le'⟩
    · have hij : i ≠ j := by
        rintro rfl
        omega
      rw [one_apply_ne hij, sub_zero]
      exact ⟨zpow_mul_mem hxb (by omega), valuation_zpow_mul_le hxb (by push_cast at hC ⊢; omega)⟩
  rw [mem_congruenceSubgroup_iff, mem_integralGL_iff]
  refine ⟨⟨fun i j => ?_, fun i j => ?_⟩, fun i j => ?_⟩
  · rw [diagPow_conj_apply]
    exact (key _ i j (hu i j) (hb i j)).1
  · have : (diagPow F n μ * u * (diagPow F n μ)⁻¹)⁻¹ = diagPow F n μ * u⁻¹ * (diagPow F n μ)⁻¹ := by
      group
    rw [this, diagPow_conj_apply]
    exact (key _ i j (hu' i j) (hb' i j)).1
  · rw [diagPow_conj_apply]
    exact (key _ i j (hu i j) (hb i j)).2

end DiagPow

theorem gap_or_bounded (μ : Fin n → ℤ) {C : ℤ} (hC : 0 < C) :
    (∃ θ : ℤ, ∃ b : α, (∃ j, β j = b ∧ θ ≤ μ j) ∧ (∃ k, β k = b ∧ μ k < θ) ∧
      ∀ k, β k = b → μ k < θ → μ k + C ≤ θ) ∨
    (∀ i j, β i = β j → μ i < μ j + n * C) := by
  classical
  by_contra hcon
  rw [not_or] at hcon
  obtain ⟨hA, hB⟩ := hcon
  push_neg at hB
  obtain ⟨i, j, hij, hbig⟩ := hB
  obtain ⟨j₀, hj₀, hmin⟩ := Finset.exists_min_image (Finset.univ.filter fun k => β k = β j) μ
    ⟨j, by simp⟩
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj₀ hmin
  have hj₀j : μ j₀ ≤ μ j := hmin j rfl
  have hk : ∀ t : Fin n, ∃ k, β k = β j ∧ μ k < μ j₀ + ((t : ℕ) + 1 : ℤ) * C ∧
      μ j₀ + ((t : ℕ) + 1 : ℤ) * C < μ k + C := by
    intro t
    by_contra hne
    push_neg at hne
    apply hA
    refine ⟨μ j₀ + ((t : ℕ) + 1 : ℤ) * C, β j, ⟨i, hij, ?_⟩, ⟨j₀, hj₀, ?_⟩, fun k hk hlt => hne k hk hlt⟩
    · have ht : ((t : ℕ) + 1 : ℤ) ≤ n := by have := t.2; omega
      nlinarith
    · nlinarith
  choose k hkb hk1 hk2 using hk
  have hinj : Function.Injective k := by
    intro s t hst
    have h1 := hk1 s
    have h2 := hk2 s
    have h3 := hk1 t
    have h4 := hk2 t
    rw [hst] at h1 h2
    have hs : ((s : ℕ) : ℤ) < (t : ℕ) + 1 := by
      by_contra h
      push_neg at h
      nlinarith
    have ht : ((t : ℕ) : ℤ) < (s : ℕ) + 1 := by
      by_contra h
      push_neg at h
      nlinarith
    exact Fin.ext (by omega)
  obtain ⟨t, ht⟩ := (Finite.injective_iff_surjective.1 hinj) j₀
  have h1 := hk2 t
  rw [ht] at h1
  have : (0 : ℤ) ≤ ((t : ℕ) : ℤ) * C := by positivity
  nlinarith

section Cuspidal

variable (F n β) in

def leviUnipotent (γ : Fin n → ℕ) : Subgroup (levi F n β) :=
  (unipotentRadical F n γ).subgroupOf (levi F n β)

variable {W : Type*} [AddCommGroup W] [Module ℂ W]

def IsCuspidal (σ : Representation ℂ (levi F n β) W) : Prop :=
  ∀ γ : Fin n → ℕ, (∃ i j, β i = β j ∧ γ i ≠ γ j) →
    Subsingleton (Representation.Coinvariants (σ.comp (leviUnipotent F n β γ).subtype))

def splitFun (S : Finset (Fin n)) : Fin n → ℕ := fun j => if j ∈ S then 0 else 1

theorem exists_finset_of_isCuspidal {σ : Representation ℂ (levi F n β) W} (hc : IsCuspidal σ)
    {S : Finset (Fin n)} (hS : ∃ i j, β i = β j ∧ i ∈ S ∧ j ∉ S) (w : W) :
    ∃ U : Finset (levi F n β), (∀ u ∈ U, (u : GL (Fin n) F) ∈ unipotentRadical F n (splitFun S)) ∧
      w ∈ Submodule.span ℂ {y | ∃ u ∈ U, ∃ x, y = σ u x - x} := by
  classical
  obtain ⟨i, j, hij, hi, hj⟩ := hS
  have hsub := hc (splitFun S) ⟨i, j, hij, by simp [splitFun, hi, hj]⟩
  have hw : w ∈ Representation.Coinvariants.ker
      (σ.comp (leviUnipotent F n β (splitFun S)).subtype) :=
    (Representation.Coinvariants.mk_eq_zero _).1 (Subsingleton.elim _ _)
  obtain ⟨T, hT, hwT⟩ := Submodule.mem_span_finite_of_mem_span hw
  have hpre : ∀ y ∈ T, ∃ gv : leviUnipotent F n β (splitFun S) × W,
      σ (gv.1 : levi F n β) gv.2 - gv.2 = y := by
    intro y hy
    obtain ⟨gv, h⟩ := hT hy
    exact ⟨gv, h⟩
  choose! pre hpre using hpre
  refine ⟨T.image fun y => ((pre y).1 : levi F n β), ?_, ?_⟩
  · intro u hu
    obtain ⟨y, -, rfl⟩ := Finset.mem_image.1 hu
    exact Subgroup.mem_subgroupOf.1 (pre y).1.2
  · refine Submodule.span_mono ?_ hwT
    intro y hy
    exact ⟨((pre y).1 : levi F n β), Finset.mem_image_of_mem _ hy, (pre y).2, (hpre y hy).symm⟩

theorem apply_eq_or_gap {θ C : ℤ} {b : α} {μ : Fin n → ℤ}
    (hgap : ∀ k, β k = b → μ k < θ → μ k + C ≤ θ) {u : GL (Fin n) F} (hu : u ∈ levi F n β)
    (hN : u ∈ unipotentRadical F n (splitFun (Finset.univ.filter fun j => β j = b ∧ θ ≤ μ j)))
    (i j : Fin n) : u i j = (1 : Matrix (Fin n) (Fin n) F) i j ∨ μ j + C ≤ μ i := by
  classical
  obtain ⟨hP, h1⟩ := mem_unipotentRadical.1 hN
  by_cases hb : β i = β j
  swap
  · left
    rw [mem_levi.1 hu i j hb, one_apply_ne (fun e => hb (by rw [e]))]
  rcases lt_trichotomy (splitFun (Finset.univ.filter fun j => β j = b ∧ θ ≤ μ j) i)
    (splitFun (Finset.univ.filter fun j => β j = b ∧ θ ≤ μ j) j) with h | h | h
  · right
    simp only [splitFun, Finset.mem_filter, Finset.mem_univ, true_and] at h
    split_ifs at h with hi hj
    · omega
    · have hjb : β j = b := hb.symm.trans hi.1
      have hjθ : μ j < θ := by
        by_contra h'
        exact hj ⟨hjb, not_lt.1 h'⟩
      have := hgap j hjb hjθ
      linarith [hi.2]
    · omega
    · omega
  · left
    exact h1 i j h
  · left
    have hij : i ≠ j := fun e => by rw [e] at h; exact lt_irrefl _ h
    rw [one_apply_ne hij]
    exact hP h

theorem exists_subgroupOf_congruenceSubgroup_subset {U : Set (levi F n β)}
    (hU : U ∈ 𝓝 (1 : levi F n β)) :
    ∃ m, (((congruenceSubgroup F n m).subgroupOf (levi F n β) : Subgroup (levi F n β)) :
      Set (levi F n β)) ⊆ U := by
  have hU' : U ∈ comap (Subtype.val : levi F n β → GL (Fin n) F) (𝓝 (1 : GL (Fin n) F)) := by
    rw [nhds_subtype] at hU
    exact hU
  obtain ⟨m, -, hm⟩ :=
    ((hasBasis_nhds_one F n).comap (Subtype.val : levi F n β → GL (Fin n) F)).mem_iff.1 hU'
  exact ⟨m, by rw [Subgroup.coe_subgroupOf]; exact hm⟩

instance secondCountableTopology_levi : SecondCountableTopology (levi F n β) :=
  inferInstanceAs (SecondCountableTopology (levi F n β : Set (GL (Fin n) F)))

theorem isAdmissible_of_isCuspidal {σ : Representation ℂ (levi F n β) W} [σ.IsIrreducible]
    (hσ : IsSmooth σ) (hc : IsCuspidal σ) : IsAdmissible σ := by
  classical
  haveI : LocallyCompactSpace (levi F n β) :=
    isClosed_levi.isClosedEmbedding_subtypeVal.locallyCompactSpace
  let KM : ℕ → Subgroup (levi F n β) := fun m => (congruenceSubgroup F n m).subgroupOf (levi F n β)
  have hKMc : ∀ m, IsCompact (KM m : Set (levi F n β)) := fun m =>
    isCompact_subgroupOf_levi (isCompact_congruenceSubgroup F n m)
  have hKMo : ∀ m, IsOpen (KM m : Set (levi F n β)) := fun m =>
    isOpen_subgroupOf_levi (isOpen_congruenceSubgroup F n m)
  have hKManti : ∀ {m m' : ℕ}, m ≤ m' → KM m' ≤ KM m := fun h x hx =>
    Subgroup.mem_subgroupOf.2 (congruenceSubgroup_antitone F n h (Subgroup.mem_subgroupOf.1 hx))
  obtain ⟨v, hv0⟩ := exists_ne_zero_of_isIrreducible (ρ := σ)

  have hspan : Submodule.span ℂ (Set.range fun g : levi F n β => σ g v) = ⊤ := by
    have hstable : ∀ g : levi F n β, Submodule.span ℂ (Set.range fun h : levi F n β => σ h v) ≤
        (Submodule.span ℂ (Set.range fun h : levi F n β => σ h v)).comap (σ g) := by
      intro g
      refine Submodule.span_le.2 ?_
      rintro _ ⟨h, rfl⟩
      exact Submodule.subset_span ⟨g * h, by simp [map_mul, Module.End.mul_apply]⟩
    let Wsub : Subrepresentation σ :=
      ⟨Submodule.span ℂ (Set.range fun h : levi F n β => σ h v), fun g _ hx => hstable g hx⟩
    have hW : Wsub = ⊤ := (eq_bot_or_eq_top Wsub).resolve_left fun h => hv0 (by
      have hvW : v ∈ Wsub.toSubmodule := Submodule.subset_span ⟨1, by simp⟩
      rw [h] at hvW
      exact (Submodule.mem_bot ℂ).1 hvW)
    exact congrArg Subrepresentation.toSubmodule hW
  obtain ⟨m₀, hm₀⟩ := exists_subgroupOf_congruenceSubgroup_subset
    ((hσ v).mem_nhds (one_mem (stabilizerOf σ v)))
  have hvm₀ : v ∈ fixedVectors σ (KM m₀) := fun k hk => hm₀ hk
  suffices hmain : ∀ m, m₀ ≤ m → FiniteDimensional ℂ (fixedVectors σ (KM m)) by
    refine ⟨hσ, fun K hKc hKo => ?_⟩
    obtain ⟨m₁, hm₁⟩ := exists_subgroupOf_congruenceSubgroup_subset (hKo.mem_nhds K.one_mem)
    have hle : KM (max m₀ m₁) ≤ K := fun x hx => hm₁ (hKManti (le_max_right _ _) hx)
    have := hmain (max m₀ m₁) (le_max_left _ _)
    exact Submodule.finiteDimensional_of_le (fixedVectors_antitone _ hle)
  intro m hm
  set K := KM m with hKdef
  set e := fixedProj σ hσ (hKMc m) (hKMo m) with hedef
  have hvK : v ∈ fixedVectors σ K := fixedVectors_antitone _ (hKManti hm) hvm₀

  let K₀ : Subgroup (levi F n β) := (integralGL F n).subgroupOf (levi F n β)
  have hK₀c : IsCompact (K₀ : Set (levi F n β)) := isCompact_subgroupOf_levi (isCompact_integralGL F n)
  have : CompactSpace K₀ := isCompact_iff_compactSpace.1 hK₀c
  have hQ : Finite (K₀ ⧸ K.subgroupOf K₀) := by
    refine Subgroup.quotient_finite_of_isOpen _ ?_
    rw [Subgroup.coe_subgroupOf]
    exact (hKMo m).preimage continuous_subtype_val
  have := Fintype.ofFinite (K₀ ⧸ K.subgroupOf K₀)
  let R : Finset (levi F n β) :=
    Finset.univ.image fun q : K₀ ⧸ K.subgroupOf K₀ => ((Quotient.out q : K₀) : levi F n β)
  have hR : ∀ k ∈ K₀, ∃ r ∈ R, ∀ w ∈ fixedVectors σ K, σ k w = σ r w := by
    intro k hk
    refine ⟨_, Finset.mem_image_of_mem _ (Finset.mem_univ (QuotientGroup.mk (⟨k, hk⟩ : K₀))),
      fun w hw => ?_⟩
    exact act_eq_of_mk_eq σ hw (a := ⟨k, hk⟩)
      (b := Quotient.out (QuotientGroup.mk (⟨k, hk⟩ : K₀) : K₀ ⧸ K.subgroupOf K₀))
      (QuotientGroup.out_eq' _).symm
  have hnorm : ∀ k ∈ K₀, ∀ x ∈ K, k * x * k⁻¹ ∈ K := fun k hk x hx =>
    Subgroup.mem_subgroupOf.2 (by
      simpa using conj_mem_congruenceSubgroup F n (Subgroup.mem_subgroupOf.1 hk)
        (Subgroup.mem_subgroupOf.1 hx))
  have hnorm' : ∀ k ∈ K₀, ∀ x ∈ K, k⁻¹ * x * k ∈ K := fun k hk x hx => by
    simpa using hnorm k⁻¹ (K₀.inv_mem hk) x hx
  have hecomm : ∀ k ∈ K₀, ∀ y : W, ((e (σ k y) : fixedVectors σ K) : W) =
      σ k (e y : fixedVectors σ K) := fun k hk y =>
    fixedProj_act_of_normalizes hσ (hKMc m) (hKMo m) (hnorm k hk) (hnorm' k hk) y

  let V₂ : Finset W := R.image fun r => σ r v

  have hU : ∀ S : Finset (Fin n), (∃ i j, β i = β j ∧ i ∈ S ∧ j ∉ S) → ∀ w : W,
      ∃ U : Finset (levi F n β), (∀ u ∈ U, (u : GL (Fin n) F) ∈ unipotentRadical F n (splitFun S)) ∧
        w ∈ Submodule.span ℂ {y | ∃ u ∈ U, ∃ x, y = σ u x - x} :=
    fun S hS w => exists_finset_of_isCuspidal hc hS w
  choose! Uf hUf1 hUf2 using hU
  let Uall : Finset (levi F n β) := Finset.univ.biUnion fun S : Finset (Fin n) => V₂.biUnion (Uf S)
  obtain ⟨t, ht⟩ := exists_pow_mul_mem_of_isCompact F n
    (((Uall.image fun u : levi F n β => u.1) ∪ (Uall.image fun u : levi F n β => u.1⁻¹) :
      Finset (GL (Fin n) F)) : Set (GL (Fin n) F)).toFinite.isCompact
  have hbu : ∀ u ∈ Uall, ∀ i j, (uniformizer F : F) ^ t * (u : GL (Fin n) F) i j ∈ 𝒪[F] :=
    fun u hu => ht _ (by simp only [Finset.coe_union, Finset.coe_image, Set.mem_union,
      Set.mem_image, Finset.mem_coe]; exact Or.inl ⟨u, hu, rfl⟩)
  have hbu' : ∀ u ∈ Uall, ∀ i j,
      (uniformizer F : F) ^ t * ((u : GL (Fin n) F)⁻¹ : GL (Fin n) F) i j ∈ 𝒪[F] :=
    fun u hu => ht _ (by simp only [Finset.coe_union, Finset.coe_image, Set.mem_union,
      Set.mem_image, Finset.mem_coe]; exact Or.inr ⟨u, hu, rfl⟩)
  set C : ℤ := ((t + m : ℕ) : ℤ) + 1 with hCdef
  have hC : ((t + m : ℕ) : ℤ) < C := lt_add_one _
  have hC0 : 0 < C := by positivity

  let Nset : Finset (Fin n → ℤ) := Fintype.piFinset fun _ => Finset.Icc 0 (n * C)
  let T₀ : Finset W := (Nset ×ˢ V₂).image fun p =>
    ((e (σ ⟨Cartan.diagPow F n p.1, diagPow_mem_levi p.1⟩ p.2) : fixedVectors σ K) : W)
  let T : Finset W := (R ×ˢ T₀).image fun p => σ p.1 p.2
  have hT₀K : ∀ x ∈ T₀, x ∈ fixedVectors σ K := by
    intro x hx
    obtain ⟨p, -, rfl⟩ := Finset.mem_image.1 hx
    exact (e _).2
  have hclaim : ∀ g : levi F n β,
      ((e (σ g v) : fixedVectors σ K) : W) ∈ Submodule.span ℂ (T : Set W) := by
    intro g
    obtain ⟨μ, k₁, hk₁, k₂, hk₂, hg⟩ := exists_eq_mul_diagPow_mul_levi g.2
    set a : levi F n β := ⟨Cartan.diagPow F n μ, diagPow_mem_levi μ⟩ with hadef
    have hk₁K : (⟨k₁, hk₁.1⟩ : levi F n β) ∈ K₀ := Subgroup.mem_subgroupOf.2 hk₁.2
    have hk₂K : (⟨k₂, hk₂.1⟩ : levi F n β) ∈ K₀ := Subgroup.mem_subgroupOf.2 hk₂.2
    have hgeq : g = ⟨k₁, hk₁.1⟩ * a * ⟨k₂, hk₂.1⟩ := Subtype.ext hg
    obtain ⟨r₂, hr₂, hr₂v⟩ := hR _ hk₂K
    obtain ⟨r₁, hr₁, hr₁v⟩ := hR _ hk₁K
    have hwV : σ r₂ v ∈ V₂ := Finset.mem_image_of_mem _ hr₂
    have he : ((e (σ g v) : fixedVectors σ K) : W) =
        σ ⟨k₁, hk₁.1⟩ ((e (σ a (σ r₂ v)) : fixedVectors σ K) : W) := by
      rw [hgeq, map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply, hr₂v v hvK,
        hecomm _ hk₁K]
    rw [he]
    rcases gap_or_bounded (β := β) μ hC0 with
      ⟨θ, b, ⟨i, hib, hiθ⟩, ⟨j, hjb, hjθ⟩, hgap⟩ | hbd
    ·
      set S : Finset (Fin n) := Finset.univ.filter fun j => β j = b ∧ θ ≤ μ j with hSdef
      have hS : ∃ i j, β i = β j ∧ i ∈ S ∧ j ∉ S :=
        ⟨i, j, hib.trans hjb.symm, by simp [S, hib, hiθ], by simp [S, hjb, not_le.2 hjθ]⟩
      have hzero : ((e (σ a (σ r₂ v)) : fixedVectors σ K) : W) = 0 := by
        have hsp := hUf2 S hS (σ r₂ v)
        have hker : Submodule.span ℂ {y | ∃ u ∈ Uf S (σ r₂ v), ∃ x, y = σ u x - x} ≤
            LinearMap.ker ((fixedVectors σ K).subtype ∘ₗ e ∘ₗ σ a) := by
          refine Submodule.span_le.2 ?_
          rintro _ ⟨u, hu, x, rfl⟩
          have huA : u ∈ Uall := Finset.mem_biUnion.2 ⟨S, Finset.mem_univ _,
            Finset.mem_biUnion.2 ⟨σ r₂ v, hwV, hu⟩⟩
          have huN := hUf1 S hS (σ r₂ v) u hu
          have hconj : a * u * a⁻¹ ∈ K := by
            refine Subgroup.mem_subgroupOf.2 ?_
            have hco : ((a * u * a⁻¹ : levi F n β) : GL (Fin n) F) =
                Cartan.diagPow F n μ * (u : GL (Fin n) F) * (Cartan.diagPow F n μ)⁻¹ := rfl
            rw [hco]
            exact diagPow_conj_mem_congruenceSubgroup hC (apply_eq_or_gap hgap u.2 huN)
              (apply_eq_or_gap hgap ((levi F n β).inv_mem u.2)
                ((unipotentRadical F n _).inv_mem huN)) (hbu u huA) (hbu' u huA)
          simp only [SetLike.mem_coe, LinearMap.mem_ker, LinearMap.coe_comp, Function.comp_apply,
            Submodule.coe_subtype, map_sub]
          have h1 : σ a (σ u x) = σ (a * u * a⁻¹) (σ a x) := by
            rw [← Module.End.mul_apply, ← map_mul, ← Module.End.mul_apply, ← map_mul,
              inv_mul_cancel_right]
          rw [h1, fixedProj_apply_act hσ (hKMc m) (hKMo m) hconj, sub_self]
        have := hker hsp
        simpa using this
      rw [hzero, map_zero]
      exact Submodule.zero_mem _
    ·
      let cb : α → ℤ := fun b => if h : ∃ k, β k = b then
        ((Finset.univ.filter fun k => β k = b).image μ).min' (by
          obtain ⟨k, hk⟩ := h
          exact ⟨μ k, Finset.mem_image_of_mem _ (by simp [hk])⟩) else 0
      have hcb_le : ∀ k, cb (β k) ≤ μ k := by
        intro k
        simp only [cb, dif_pos (⟨k, rfl⟩ : ∃ j, β j = β k)]
        exact Finset.min'_le _ _ (Finset.mem_image_of_mem _ (by simp))
      have hcb_mem : ∀ j, ∃ k, β k = β j ∧ cb (β j) = μ k := by
        intro j
        simp only [cb, dif_pos (⟨j, rfl⟩ : ∃ k, β k = β j)]
        obtain ⟨k, hk, hkeq⟩ := Finset.mem_image.1
          (Finset.min'_mem ((Finset.univ.filter fun k => β k = β j).image μ) _)
        exact ⟨k, (Finset.mem_filter.1 hk).2, hkeq.symm⟩
      let c : Fin n → ℤ := fun j => cb (β j)
      let ν : Fin n → ℤ := μ - c
      have hν : ν ∈ Nset := by
        rw [Fintype.mem_piFinset]
        intro j
        rw [Finset.mem_Icc]
        obtain ⟨k, hk, hkeq⟩ := hcb_mem j
        have h1 := hcb_le j
        have h2 := hbd j k hk.symm
        constructor
        · show 0 ≤ μ j - cb (β j)
          linarith
        · show μ j - cb (β j) ≤ n * C
          linarith
      have hμ : μ = c + ν := by
        funext j
        simp [ν]
      have hz := diagPow_mem_center (F := F) (β := β) (c := c) (fun i j h => by simp [c, h])
      obtain ⟨lam, hlam⟩ := exists_central_character hσ hz
      have ha : a = ⟨Cartan.diagPow F n c, diagPow_mem_levi c⟩ *
          ⟨Cartan.diagPow F n ν, diagPow_mem_levi ν⟩ := by
        apply Subtype.ext
        show Cartan.diagPow F n μ = Cartan.diagPow F n c * Cartan.diagPow F n ν
        rw [← diagPow_add, ← hμ]
      have hmemT₀ : ((e (σ ⟨Cartan.diagPow F n ν, diagPow_mem_levi ν⟩ (σ r₂ v)) :
          fixedVectors σ K) : W) ∈ T₀ :=
        Finset.mem_image.2 ⟨(ν, σ r₂ v), Finset.mem_product.2 ⟨hν, hwV⟩, rfl⟩
      rw [ha, map_mul, Module.End.mul_apply, hlam, map_smul, Submodule.coe_smul, map_smul,
        hr₁v _ (hT₀K _ hmemT₀)]
      exact Submodule.smul_mem _ _ (Submodule.subset_span
        (Finset.mem_coe.2 (Finset.mem_image.2 ⟨(r₁, _), Finset.mem_product.2 ⟨hr₁, hmemT₀⟩, rfl⟩)))
  have hle : fixedVectors σ K ≤ Submodule.span ℂ (T : Set W) := by
    intro x hx
    have hx' : x = ((e x : fixedVectors σ K) : W) :=
      (fixedProj_apply_of_mem hσ (hKMc m) (hKMo m) hx).symm
    rw [hx']
    have hxtop : x ∈ Submodule.span ℂ (Set.range fun g : levi F n β => σ g v) := by
      rw [hspan]
      exact Submodule.mem_top
    have hmap : Submodule.map ((fixedVectors σ K).subtype ∘ₗ e)
        (Submodule.span ℂ (Set.range fun g : levi F n β => σ g v)) ≤
          Submodule.span ℂ (T : Set W) := by
      rw [Submodule.map_span]
      refine Submodule.span_le.2 ?_
      rintro _ ⟨_, ⟨g, rfl⟩, rfl⟩
      exact hclaim g
    exact hmap ⟨x, hxtop, rfl⟩
  exact Submodule.finiteDimensional_of_le hle

end Cuspidal

end Parabolic

end GroundTheory.Automorphic
