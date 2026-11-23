import Mathlib

open Module

namespace GlobalTheory.CommDet

variable {V : Type} [AddCommGroup V] [Module ℂ V] {ι : Type}

def Stab (C : ι → Subalgebra ℂ (Module.End ℂ V)) (U : Submodule ℂ V) : Prop :=
  ∀ v, ∀ c ∈ C v, ∀ x ∈ U, c x ∈ U

def Comm (C : ι → Subalgebra ℂ (Module.End ℂ V)) (U : Submodule ℂ V) : Prop :=
  ∀ v w, v ≠ w → ∀ c ∈ C v, ∀ d ∈ C w, ∀ x ∈ U, c (d x) = d (c x)

def Irr (C : ι → Subalgebra ℂ (Module.End ℂ V)) (U : Submodule ℂ V) : Prop :=
  ∀ Y ≤ U, Stab C Y → Y = ⊥ ∨ Y = U

def Kills (c : Module.End ℂ V) (U : Submodule ℂ V) : Prop := ∀ x ∈ U, c x = 0

def Graph (C : ι → Subalgebra ℂ (Module.End ℂ V)) (U₁ U₂ : Submodule ℂ V)
    (X : Submodule ℂ (V × V)) : Prop :=
  X ≠ ⊥ ∧ (∀ z ∈ X, z.1 ∈ U₁ ∧ z.2 ∈ U₂) ∧ (∀ v, ∀ c ∈ C v, ∀ z ∈ X, (c z.1, c z.2) ∈ X) ∧
    (∀ u, ((0 : V), u) ∈ X → u = 0) ∧ (∀ u, (u, (0 : V)) ∈ X → u = 0)

theorem kills_iff_map (c : Module.End ℂ V) (U : Submodule ℂ V) :
    Kills c U ↔ U.map c = ⊥ := by
  constructor
  · intro h
    rw [eq_bot_iff]
    rintro _ ⟨x, hx, rfl⟩
    simp [h x hx]
  · intro h x hx
    have : c x ∈ U.map c := Submodule.mem_map_of_mem hx
    rw [h] at this
    simpa using this

theorem kills_scalar {U : Submodule ℂ V} (hU : U ≠ ⊥) (r : ℂ) :
    Kills (algebraMap ℂ (Module.End ℂ V) r) U ↔ r = 0 := by
  constructor
  · intro h
    obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hU
    have := h x hx
    rw [Module.algebraMap_end_apply] at this
    exact (smul_eq_zero.mp this).resolve_right hx0
  · rintro rfl x _
    simp

theorem eig_drop (U : Submodule ℂ V) [FiniteDimensional ℂ U] (hU : U ≠ ⊥)
    (g : Module.End ℂ V) (hg : ∀ x ∈ U, g x ∈ U) :
    ∃ μ : ℂ, finrank ℂ (U.map (g - algebraMap ℂ (Module.End ℂ V) μ)) < finrank ℂ U := by
  haveI : Nontrivial U := Submodule.nontrivial_iff_ne_bot.mpr hU
  obtain ⟨μ, hμ⟩ := Module.End.exists_eigenvalue (g.restrict hg)
  obtain ⟨z, hz⟩ := hμ.exists_hasEigenvector
  refine ⟨μ, ?_⟩
  set f := (g - algebraMap ℂ (Module.End ℂ V) μ).comp U.subtype with hf
  have hr : LinearMap.range f = U.map (g - algebraMap ℂ (Module.End ℂ V) μ) := by
    rw [hf, LinearMap.range_comp, Submodule.range_subtype]
  have hz1 : g (z : V) = μ • (z : V) := by
    have h1 := congrArg Subtype.val hz.apply_eq_smul
    simpa [LinearMap.restrict_apply] using h1
  have hk : z ∈ LinearMap.ker f := by
    simp [hf, hz1]
  have hsum := LinearMap.finrank_range_add_finrank_ker f
  rw [hr] at hsum
  have hpos : 0 < finrank ℂ (LinearMap.ker f) := by
    rw [Nat.pos_iff_ne_zero, Ne, Submodule.finrank_eq_zero]
    intro h
    rw [h] at hk
    exact hz.2 ((Submodule.mem_bot ℂ).mp hk)
  omega

theorem graph_of_scalars (C : ι → Subalgebra ℂ (Module.End ℂ V)) (U₁ U₂ : Submodule ℂ V)
    (h₁ : U₁ ≠ ⊥) (h₂ : U₂ ≠ ⊥)
    (hs : ∀ v, ∀ a ∈ C v, ∃ μ : ℂ, (∀ x ∈ U₁, a x = μ • x) ∧ (∀ x ∈ U₂, a x = μ • x)) :
    ∃ X, Graph C U₁ U₂ X := by
  obtain ⟨x₁, hx₁, hx₁0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot h₁
  obtain ⟨x₂, hx₂, hx₂0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot h₂
  refine ⟨ℂ ∙ (x₁, x₂), ?_, ?_, ?_, ?_, ?_⟩
  · rw [Ne, Submodule.span_singleton_eq_bot]
    intro h
    exact hx₁0 (congrArg Prod.fst h)
  · intro z hz
    obtain ⟨t, rfl⟩ := Submodule.mem_span_singleton.mp hz
    exact ⟨U₁.smul_mem t hx₁, U₂.smul_mem t hx₂⟩
  · intro v c hc z hz
    obtain ⟨t, rfl⟩ := Submodule.mem_span_singleton.mp hz
    obtain ⟨μ, hμ₁, hμ₂⟩ := hs v c hc
    rw [Submodule.mem_span_singleton]
    refine ⟨t * μ, ?_⟩
    ext
    · simp [hμ₁ x₁ hx₁, smul_smul]
    · simp [hμ₂ x₂ hx₂, smul_smul]
  · intro u hu
    obtain ⟨t, ht⟩ := Submodule.mem_span_singleton.mp hu
    have e1 : t • x₁ = 0 := congrArg Prod.fst ht
    have e2 : t • x₂ = u := congrArg Prod.snd ht
    have : t = 0 := (smul_eq_zero.mp e1).resolve_right hx₁0
    rw [← e2, this, zero_smul]
  · intro u hu
    obtain ⟨t, ht⟩ := Submodule.mem_span_singleton.mp hu
    have e1 : t • x₁ = u := congrArg Prod.fst ht
    have e2 : t • x₂ = 0 := congrArg Prod.snd ht
    have : t = 0 := (smul_eq_zero.mp e2).resolve_right hx₂0
    rw [← e1, this, zero_smul]

open Classical in

noncomputable def drop (C : ι → Subalgebra ℂ (Module.End ℂ V)) (v : ι) :
    ι → Subalgebra ℂ (Module.End ℂ V) :=
  fun w => if w = v then ⊥ else C w

theorem drop_le (C : ι → Subalgebra ℂ (Module.End ℂ V)) (v w : ι) : drop C v w ≤ C w := by
  unfold drop
  split_ifs
  · exact bot_le
  · exact le_rfl

theorem drop_ne (C : ι → Subalgebra ℂ (Module.End ℂ V)) (v : ι) {w : ι} (h : w ≠ v) :
    drop C v w = C w := by
  simp [drop, h]

theorem drop_self (C : ι → Subalgebra ℂ (Module.End ℂ V)) (v : ι) {d : Module.End ℂ V}
    (hd : d ∈ drop C v v) : ∃ r : ℂ, algebraMap ℂ (Module.End ℂ V) r = d := by
  have h : drop C v v = ⊥ := by simp [drop]
  rw [h] at hd
  exact Algebra.mem_bot.mp hd

theorem comm_drop (C : ι → Subalgebra ℂ (Module.End ℂ V)) (v : ι) {U U' : Submodule ℂ V}
    (hc : Comm C U) (hle : U' ≤ U) : Comm (drop C v) U' := by
  intro w₁ w₂ hw c hc' d hd x hx
  by_cases h1 : w₁ = v
  · rw [h1] at hc'
    obtain ⟨r, rfl⟩ := drop_self C v hc'
    simp [Module.algebraMap_end_apply]
  · by_cases h2 : w₂ = v
    · rw [h2] at hd
      obtain ⟨r, rfl⟩ := drop_self C v hd
      simp [Module.algebraMap_end_apply]
    · rw [drop_ne C v h1] at hc'
      rw [drop_ne C v h2] at hd
      exact hc w₁ w₂ hw c hc' d hd x (hle hx)

theorem map_le_self {C : ι → Subalgebra ℂ (Module.End ℂ V)} {v : ι} {U : Submodule ℂ V}
    {c₀ : Module.End ℂ V} (hS : Stab C U) (hc₀ : c₀ ∈ C v) : U.map c₀ ≤ U := by
  rintro _ ⟨x, hx, rfl⟩
  exact hS v c₀ hc₀ x hx

theorem stab_drop {C : ι → Subalgebra ℂ (Module.End ℂ V)} {v : ι} {U : Submodule ℂ V}
    {c₀ : Module.End ℂ V} (hS : Stab C U) (hC : Comm C U) (hc₀ : c₀ ∈ C v) :
    Stab (drop C v) (U.map c₀) := by
  rintro w d hd _ ⟨x, hx, rfl⟩
  by_cases h : w = v
  · rw [h] at hd
    obtain ⟨r, rfl⟩ := drop_self C v hd
    rw [Module.algebraMap_end_apply]
    exact Submodule.smul_mem _ r (Submodule.mem_map_of_mem hx)
  · rw [drop_ne C v h] at hd
    have e : d (c₀ x) = c₀ (d x) := (hC v w (Ne.symm h) c₀ hc₀ d hd x hx).symm
    rw [e]
    exact Submodule.mem_map_of_mem (hS w d hd x hx)

def orbSpan (C : ι → Subalgebra ℂ (Module.End ℂ V)) (v : ι) (Y : Submodule ℂ V) :
    Submodule ℂ V :=
  Submodule.span ℂ {x | ∃ a ∈ C v, ∃ y ∈ Y, a y = x}

theorem orbSpan_eq {C : ι → Subalgebra ℂ (Module.End ℂ V)} {v : ι} {U : Submodule ℂ V}
    (hS : Stab C U) (hC : Comm C U) (hI : Irr C U) {Y : Submodule ℂ V}
    (hYU : Y ≤ U) (hYS : Stab (drop C v) Y) (hY : Y ≠ ⊥) : orbSpan C v Y = U := by
  have hle : orbSpan C v Y ≤ U := by
    rw [orbSpan, Submodule.span_le]
    rintro _ ⟨a, ha, y, hy, rfl⟩
    exact hS v a ha y (hYU hy)
  have hst : Stab C (orbSpan C v Y) := by
    intro w c hc x hx
    have key : orbSpan C v Y ≤ (orbSpan C v Y).comap c := by
      unfold orbSpan
      rw [Submodule.span_le]
      rintro _ ⟨a, ha, y, hy, rfl⟩
      rw [SetLike.mem_coe, Submodule.mem_comap]
      by_cases h : w = v
      · rw [h] at hc
        exact Submodule.subset_span ⟨c * a, mul_mem hc ha, y, hy, rfl⟩
      · have hc' : c ∈ drop C v w := by rw [drop_ne C v h]; exact hc
        rw [hC w v h c hc a ha y (hYU hy)]
        exact Submodule.subset_span ⟨a, ha, c y, hYS w c hc' y hy, rfl⟩
    exact key hx
  have hYle : Y ≤ orbSpan C v Y := fun y hy =>
    Submodule.subset_span ⟨1, one_mem _, y, hy, by simp⟩
  rcases hI _ hle hst with h | h
  · exact absurd (eq_bot_iff.mpr (h ▸ hYle)) hY
  · exact h

theorem irr_drop {C : ι → Subalgebra ℂ (Module.End ℂ V)} {v : ι} {U : Submodule ℂ V}
    {c₀ : Module.End ℂ V} (hS : Stab C U) (hC : Comm C U) (hI : Irr C U) (hc₀ : c₀ ∈ C v)
    (hsc : ∀ a ∈ C v, ∃ μ : ℂ, ∀ x ∈ U, c₀ (a (c₀ x)) = μ • c₀ x) :
    Irr (drop C v) (U.map c₀) := by
  intro Y hY hYS
  by_cases hb : Y = ⊥
  · exact Or.inl hb
  right
  apply le_antisymm hY
  have hsp := orbSpan_eq hS hC hI (hY.trans (map_le_self hS hc₀)) hYS hb
  rw [Submodule.map_le_iff_le_comap, ← hsp, orbSpan, Submodule.span_le]
  rintro _ ⟨a, ha, y, hy, rfl⟩
  obtain ⟨x, hx, rfl⟩ := Submodule.mem_map.mp (hY hy)
  obtain ⟨μ, hμ⟩ := hsc a ha
  show c₀ (a (c₀ x)) ∈ Y
  rw [hμ x hx]
  exact Y.smul_mem μ hy

theorem kills_drop {C : ι → Subalgebra ℂ (Module.End ℂ V)} {v : ι} {U : Submodule ℂ V}
    {c₀ : Module.End ℂ V} (hS : Stab C U) (hC : Comm C U) (hI : Irr C U) (hc₀ : c₀ ∈ C v)
    (hne : U.map c₀ ≠ ⊥) (w : ι) (d : Module.End ℂ V) (hd : d ∈ drop C v w) :
    Kills d (U.map c₀) ↔ Kills d U := by
  have hU : U ≠ ⊥ := by
    rintro rfl
    exact hne (Submodule.map_bot _)
  by_cases h : w = v
  · rw [h] at hd
    obtain ⟨r, rfl⟩ := drop_self C v hd
    rw [kills_scalar hne, kills_scalar hU]
  · rw [drop_ne C v h] at hd
    constructor
    · intro hk
      have hsp := orbSpan_eq hS hC hI (map_le_self hS hc₀) (stab_drop hS hC hc₀) hne
      have key : orbSpan C v (U.map c₀) ≤ LinearMap.ker d := by
        rw [orbSpan, Submodule.span_le]
        rintro _ ⟨a, ha, y, hy, rfl⟩
        rw [SetLike.mem_coe, LinearMap.mem_ker]
        rw [hC w v h d hd a ha y (map_le_self hS hc₀ hy), hk y hy, map_zero]
      intro x hx
      rw [← hsp] at hx
      exact key hx
    · intro hk x hx
      exact hk x (map_le_self hS hc₀ hx)

theorem glue (C : ι → Subalgebra ℂ (Module.End ℂ V)) (v : ι) {U₁ U₂ : Submodule ℂ V}
    {c₀ : Module.End ℂ V} (hc₀ : c₀ ∈ C v)
    (hS₁ : Stab C U₁) (hS₂ : Stab C U₂) (hC₁ : Comm C U₁) (hC₂ : Comm C U₂)
    (hI₁ : Irr C U₁) (hI₂ : Irr C U₂) (hk₁ : ¬ Kills c₀ U₁) (hk₂ : ¬ Kills c₀ U₂)
    (hsc : ∀ a ∈ C v, ∃ μ : ℂ, (∀ x ∈ U₁, c₀ (a (c₀ x)) = μ • c₀ x) ∧
      (∀ x ∈ U₂, c₀ (a (c₀ x)) = μ • c₀ x))
    {X' : Submodule ℂ (V × V)} (hX' : Graph (drop C v) (U₁.map c₀) (U₂.map c₀) X') :
    ∃ X, Graph C U₁ U₂ X := by
  obtain ⟨hX'0, hX'U, hX'S, hX'l, hX'r⟩ := hX'
  set S : Set (V × V) := {z | ∃ a ∈ C v, ∃ z' ∈ X', (a z'.1, a z'.2) = z} with hSdef
  have hsub : X' ≤ Submodule.span ℂ S := fun z hz =>
    Submodule.subset_span ⟨1, one_mem _, z, hz, by simp⟩
  have hU : Submodule.span ℂ S ≤ U₁.prod U₂ := by
    rw [Submodule.span_le]
    rintro _ ⟨a, ha, z', hz', rfl⟩
    obtain ⟨h1, h2⟩ := hX'U z' hz'
    exact ⟨hS₁ v a ha _ (map_le_self hS₁ hc₀ h1), hS₂ v a ha _ (map_le_self hS₂ hc₀ h2)⟩
  have hst : ∀ w, ∀ c ∈ C w, ∀ z ∈ Submodule.span ℂ S, (c z.1, c z.2) ∈ Submodule.span ℂ S := by
    intro w c hc z hz
    have key : Submodule.span ℂ S ≤ (Submodule.span ℂ S).comap (c.prodMap c) := by
      rw [Submodule.span_le]
      rintro _ ⟨a, ha, z', hz', rfl⟩
      rw [SetLike.mem_coe, Submodule.mem_comap, LinearMap.prodMap_apply]
      by_cases h : w = v
      · rw [h] at hc
        exact Submodule.subset_span ⟨c * a, mul_mem hc ha, z', hz', rfl⟩
      · obtain ⟨h1, h2⟩ := hX'U z' hz'
        have hc' : c ∈ drop C v w := by rw [drop_ne C v h]; exact hc
        rw [hC₁ w v h c hc a ha _ (map_le_self hS₁ hc₀ h1),
          hC₂ w v h c hc a ha _ (map_le_self hS₂ hc₀ h2)]
        exact Submodule.subset_span ⟨a, ha, (c z'.1, c z'.2), hX'S w c hc' z' hz', rfl⟩
    have := key hz
    rwa [Submodule.mem_comap, LinearMap.prodMap_apply] at this
  have hc₀X : ∀ z ∈ Submodule.span ℂ S, (c₀ z.1, c₀ z.2) ∈ X' := by
    intro z hz
    have key : Submodule.span ℂ S ≤ X'.comap (c₀.prodMap c₀) := by
      rw [Submodule.span_le]
      rintro _ ⟨a, ha, z', hz', rfl⟩
      rw [SetLike.mem_coe, Submodule.mem_comap, LinearMap.prodMap_apply]
      obtain ⟨h1, h2⟩ := hX'U z' hz'
      obtain ⟨x₁, hx₁, e₁⟩ := Submodule.mem_map.mp h1
      obtain ⟨x₂, hx₂, e₂⟩ := Submodule.mem_map.mp h2
      obtain ⟨μ, hμ₁, hμ₂⟩ := hsc a ha
      have e : (c₀ (a z'.1), c₀ (a z'.2)) = μ • z' := by
        ext
        · simp only [Prod.smul_fst]
          rw [← e₁, hμ₁ x₁ hx₁]
        · simp only [Prod.smul_snd]
          rw [← e₂, hμ₂ x₂ hx₂]
      rw [e]
      exact X'.smul_mem μ hz'
    have := key hz
    rwa [Submodule.mem_comap, LinearMap.prodMap_apply] at this
  refine ⟨Submodule.span ℂ S, ?_, fun z hz => Submodule.mem_prod.mp (hU hz), hst, ?_, ?_⟩
  · intro h
    apply hX'0
    rw [eq_bot_iff, ← h]
    exact hsub
  · set K := (Submodule.span ℂ S).comap (LinearMap.inr ℂ V V) with hK
    have hKU : K ≤ U₂ := fun u hu => (Submodule.mem_prod.mp (hU hu)).2
    have hKS : Stab C K := by
      intro w c hc u hu
      have h0 := hst w c hc _ hu
      simp only [LinearMap.inr_apply, map_zero] at h0
      simpa [hK] using h0
    rcases hI₂ K hKU hKS with h | h
    · intro u hu
      have hu' : u ∈ K := by simpa [hK] using hu
      rw [h] at hu'
      exact (Submodule.mem_bot ℂ).mp hu'
    · exfalso
      apply hk₂
      intro u hu
      rw [← h] at hu
      have h0 := hc₀X _ hu
      simp only [LinearMap.inr_apply, map_zero] at h0
      exact hX'l _ h0
  · set K := (Submodule.span ℂ S).comap (LinearMap.inl ℂ V V) with hK
    have hKU : K ≤ U₁ := fun u hu => (Submodule.mem_prod.mp (hU hu)).1
    have hKS : Stab C K := by
      intro w c hc u hu
      have h0 := hst w c hc _ hu
      simp only [LinearMap.inl_apply, map_zero] at h0
      simpa [hK] using h0
    rcases hI₁ K hKU hKS with h | h
    · intro u hu
      have hu' : u ∈ K := by simpa [hK] using hu
      rw [h] at hu'
      exact (Submodule.mem_bot ℂ).mp hu'
    · exfalso
      apply hk₁
      intro u hu
      rw [← h] at hu
      have h0 := hc₀X _ hu
      simp only [LinearMap.inl_apply, map_zero] at h0
      exact hX'r _ h0

theorem main_ind (n : ℕ) : ∀ (C : ι → Subalgebra ℂ (Module.End ℂ V)) (U₁ U₂ : Submodule ℂ V),
    FiniteDimensional ℂ U₁ → finrank ℂ U₁ = n → U₁ ≠ ⊥ → U₂ ≠ ⊥ →
    Stab C U₁ → Stab C U₂ → Comm C U₁ → Comm C U₂ →
    (∀ v, ∀ c ∈ C v, Kills c U₁ ↔ Kills c U₂) → Irr C U₁ → Irr C U₂ →
    ∃ X, Graph C U₁ U₂ X := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro C U₁ U₂ hfd hn h₁ h₂ hS₁ hS₂ hC₁ hC₂ hK hI₁ hI₂
  classical
  haveI := hfd
  by_cases hB : ∀ v, ∀ a ∈ C v, ∃ μ : ℂ, ∀ x ∈ U₁, a x = μ • x
  · apply graph_of_scalars C U₁ U₂ h₁ h₂
    intro v a ha
    obtain ⟨μ, hμ⟩ := hB v a ha
    refine ⟨μ, hμ, ?_⟩
    have hm : a - algebraMap ℂ (Module.End ℂ V) μ ∈ C v :=
      sub_mem ha (Subalgebra.algebraMap_mem _ μ)
    have hk : Kills (a - algebraMap ℂ (Module.End ℂ V) μ) U₁ := by
      intro x hx
      simp [hμ x hx]
    intro x hx
    have := (hK v _ hm).mp hk x hx
    simpa [sub_eq_zero] using this
  push_neg at hB
  obtain ⟨v₁, a₁, ha₁, hna⟩ := hB
  obtain ⟨μ₁, hμ₁⟩ := eig_drop U₁ h₁ a₁ (fun x hx => hS₁ v₁ a₁ ha₁ x hx)
  have he₁m : a₁ - algebraMap ℂ (Module.End ℂ V) μ₁ ∈ C v₁ :=
    sub_mem ha₁ (Subalgebra.algebraMap_mem _ μ₁)
  have he₁ne : U₁.map (a₁ - algebraMap ℂ (Module.End ℂ V) μ₁) ≠ ⊥ := by
    intro h
    obtain ⟨x, hx, hne⟩ := hna μ₁
    apply hne
    have := (kills_iff_map _ U₁).mpr h x hx
    simpa [sub_eq_zero] using this
  have hex : ∃ m, ∃ v, ∃ c ∈ C v, U₁.map c ≠ ⊥ ∧ finrank ℂ (U₁.map c) = m :=
    ⟨_, v₁, _, he₁m, he₁ne, rfl⟩
  obtain ⟨v, c₀, hc₀, hc₀ne, hc₀fr⟩ := Nat.find_spec hex
  have hmin : ∀ w, ∀ c ∈ C w, U₁.map c ≠ ⊥ → Nat.find hex ≤ finrank ℂ (U₁.map c) :=
    fun w c hc hne => Nat.find_min' hex ⟨w, c, hc, hne, rfl⟩
  have hlt : finrank ℂ (U₁.map c₀) < n := by
    have := hmin v₁ _ he₁m he₁ne
    omega
  have hsc : ∀ a ∈ C v, ∃ μ : ℂ, (∀ x ∈ U₁, c₀ (a (c₀ x)) = μ • c₀ x) ∧
      (∀ x ∈ U₂, c₀ (a (c₀ x)) = μ • c₀ x) := by
    intro a ha
    have hg : ∀ x ∈ U₁.map c₀, (c₀ * a) x ∈ U₁.map c₀ := by
      rintro _ ⟨y, hy, rfl⟩
      exact Submodule.mem_map_of_mem (hS₁ v a ha _ (hS₁ v c₀ hc₀ y hy))
    obtain ⟨μ, hμ⟩ := eig_drop (U₁.map c₀) hc₀ne (c₀ * a) hg
    have hem : (c₀ * a - algebraMap ℂ (Module.End ℂ V) μ) * c₀ ∈ C v :=
      mul_mem (sub_mem (mul_mem hc₀ ha) (Subalgebra.algebraMap_mem _ μ)) hc₀
    have hmap : U₁.map ((c₀ * a - algebraMap ℂ (Module.End ℂ V) μ) * c₀) =
        (U₁.map c₀).map (c₀ * a - algebraMap ℂ (Module.End ℂ V) μ) := by
      rw [Module.End.mul_eq_comp, Submodule.map_comp]
    have hk : Kills ((c₀ * a - algebraMap ℂ (Module.End ℂ V) μ) * c₀) U₁ := by
      rw [kills_iff_map]
      by_contra hne
      have := hmin v _ hem hne
      rw [hmap] at this
      omega
    refine ⟨μ, fun x hx => ?_, fun x hx => ?_⟩
    · have := hk x hx
      simpa [sub_eq_zero] using this
    · have := (hK v _ hem).mp hk x hx
      simpa [sub_eq_zero] using this
  have hk₁ : ¬ Kills c₀ U₁ := fun h => hc₀ne ((kills_iff_map c₀ U₁).mp h)
  have hk₂ : ¬ Kills c₀ U₂ := fun h => hk₁ ((hK v c₀ hc₀).mpr h)
  have h₂' : U₂.map c₀ ≠ ⊥ := fun h => hk₂ ((kills_iff_map c₀ U₂).mpr h)
  have hsc₁ : ∀ a ∈ C v, ∃ μ : ℂ, ∀ x ∈ U₁, c₀ (a (c₀ x)) = μ • c₀ x :=
    fun a ha => (hsc a ha).imp fun _ h => h.1
  have hsc₂ : ∀ a ∈ C v, ∃ μ : ℂ, ∀ x ∈ U₂, c₀ (a (c₀ x)) = μ • c₀ x :=
    fun a ha => (hsc a ha).imp fun _ h => h.2
  obtain ⟨X', hX'⟩ := ih _ hlt (drop C v) (U₁.map c₀) (U₂.map c₀) inferInstance rfl hc₀ne h₂'
    (stab_drop hS₁ hC₁ hc₀) (stab_drop hS₂ hC₂ hc₀)
    (comm_drop C v hC₁ (map_le_self hS₁ hc₀)) (comm_drop C v hC₂ (map_le_self hS₂ hc₀))
    (fun w d hd => by
      rw [kills_drop hS₁ hC₁ hI₁ hc₀ hc₀ne w d hd, kills_drop hS₂ hC₂ hI₂ hc₀ h₂' w d hd]
      exact hK w d (drop_le C v w hd))
    (irr_drop hS₁ hC₁ hI₁ hc₀ hsc₁) (irr_drop hS₂ hC₂ hI₂ hc₀ hsc₂)
  exact glue C v hc₀ hS₁ hS₂ hC₁ hC₂ hI₁ hI₂ hk₁ hk₂ hsc hX'

theorem stable_graph : ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (ι : Type) (C : ι → Subalgebra ℂ (Module.End ℂ V)) (U₁ U₂ : Submodule ℂ V), FiniteDimensional ℂ U₁ → U₁ ≠ ⊥ → U₂ ≠ ⊥ → (∀ v, ∀ c ∈ C v, ∀ x ∈ U₁, c x ∈ U₁) → (∀ v, ∀ c ∈ C v, ∀ x ∈ U₂, c x ∈ U₂) → (∀ v w, v ≠ w → ∀ c ∈ C v, ∀ d ∈ C w, (∀ x ∈ U₁, c (d x) = d (c x)) ∧ (∀ x ∈ U₂, c (d x) = d (c x))) → (∀ v, ∀ c ∈ C v, (∀ x ∈ U₁, c x = 0) ↔ (∀ x ∈ U₂, c x = 0)) → (∀ Y ≤ U₁, (∀ v, ∀ c ∈ C v, ∀ x ∈ Y, c x ∈ Y) → Y = ⊥ ∨ Y = U₁) → (∀ Y ≤ U₂, (∀ v, ∀ c ∈ C v, ∀ x ∈ Y, c x ∈ Y) → Y = ⊥ ∨ Y = U₂) → ∃ X : Submodule ℂ (V × V), X ≠ ⊥ ∧ (∀ z ∈ X, z.1 ∈ U₁ ∧ z.2 ∈ U₂) ∧ (∀ v, ∀ c ∈ C v, ∀ z ∈ X, (c z.1, c z.2) ∈ X) ∧ (∀ u, ((0 : V), u) ∈ X → u = 0) ∧ (∀ u, (u, (0 : V)) ∈ X → u = 0) := by
  intro V _ _ ι C U₁ U₂ hfd h₁ h₂ hS₁ hS₂ hCm hK hI₁ hI₂
  exact main_ind (finrank ℂ U₁) C U₁ U₂ hfd rfl h₁ h₂ hS₁ hS₂
    (fun v w h c hc d hd x hx => (hCm v w h c hc d hd).1 x hx)
    (fun v w h c hc d hd x hx => (hCm v w h c hc d hd).2 x hx) hK hI₁ hI₂

end GlobalTheory.CommDet
