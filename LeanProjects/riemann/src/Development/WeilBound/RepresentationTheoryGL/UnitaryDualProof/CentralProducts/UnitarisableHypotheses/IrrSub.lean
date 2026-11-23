import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.SmoothPartStable

noncomputable section

open Classical

namespace PositivityTheory.RgUd.Prod.Asm

open GlobalTheory.PRep

section Gen

variable {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V)

theorem mem_fixed_iff (K : Subgroup G) (v : V) : v ∈ fixed ρ K ↔ ∀ k : K, ρ (k : G) v = v := by
  show (∀ h : K, ρ (h : G) v = ((1 : K →* ℂˣ) h : ℂ) • v) ↔ _
  simp

def genSub (M : Submodule ℂ V) : Subrepresentation ρ where
  toSubmodule := Submodule.span ℂ {w | ∃ g : G, ∃ x ∈ M, w = ρ g x}
  apply_mem_toSubmodule := by
    intro g v hv
    have : Submodule.span ℂ {w | ∃ g : G, ∃ x ∈ M, w = ρ g x} ≤
        (Submodule.span ℂ {w | ∃ g : G, ∃ x ∈ M, w = ρ g x}).comap (ρ g) := by
      refine Submodule.span_le.2 ?_
      intro w hw
      obtain ⟨h, x, hx, rfl⟩ := hw
      rw [SetLike.mem_coe, Submodule.mem_comap]
      refine Submodule.subset_span ⟨g * h, x, hx, ?_⟩
      simp [map_mul]
    exact this hv

theorem le_genSub (M : Submodule ℂ V) : M ≤ (genSub ρ M).toSubmodule := by
  intro x hx
  exact Submodule.subset_span ⟨1, x, hx, by simp⟩

theorem genSub_le (M : Submodule ℂ V) (U : Subrepresentation ρ) (h : M ≤ U.toSubmodule) :
    (genSub ρ M).toSubmodule ≤ U.toSubmodule := by
  refine Submodule.span_le.2 ?_
  rintro w ⟨g, x, hx, rfl⟩
  exact U.apply_mem_toSubmodule g (h hx)

theorem fixed_split (U C : Subrepresentation ρ) (hUC : U.toSubmodule ⊓ C.toSubmodule = ⊥) (g : G)
    {u c : V} (hu : u ∈ U.toSubmodule) (hc : c ∈ C.toSubmodule) (h : ρ g (u + c) = u + c) :
    ρ g u = u := by
  have h1 : ρ g u - u = c - ρ g c := by
    rw [map_add] at h
    rw [sub_eq_sub_iff_add_eq_add, h, add_comm]
  have h2 : ρ g u - u ∈ U.toSubmodule ⊓ C.toSubmodule := by
    refine ⟨sub_mem (U.apply_mem_toSubmodule g hu) hu, ?_⟩
    rw [h1]
    exact sub_mem hc (C.apply_mem_toSubmodule g hc)
  rw [hUC] at h2
  exact sub_eq_zero.1 ((Submodule.mem_bot ℂ).1 h2)

theorem irreducible_of_fixed (K : Subgroup G)
    (hcompl : ∀ S : Subrepresentation ρ, ∃ T : Subrepresentation ρ, IsCompl S.toSubmodule T.toSubmodule)
    (W : Subrepresentation ρ) (h1 : fixed ρ K ⊓ W.toSubmodule ≠ ⊥)
    (h2 : ∀ U : Subrepresentation ρ, U.toSubmodule ≤ W.toSubmodule → fixed ρ K ⊓ U.toSubmodule ≠ ⊥ →
      fixed ρ K ⊓ W.toSubmodule ≤ U.toSubmodule)
    (h3 : ∀ U : Subrepresentation ρ, fixed ρ K ⊓ W.toSubmodule ≤ U.toSubmodule →
      W.toSubmodule ≤ U.toSubmodule) :
    W.toRepresentation.IsIrreducible := by
  obtain ⟨w, hwF, hwW, hw0⟩ : ∃ w, w ∈ fixed ρ K ∧ w ∈ W.toSubmodule ∧ w ≠ 0 := by
    by_contra hcon
    push Not at hcon
    apply h1
    rw [Submodule.eq_bot_iff]
    intro x hx
    exact hcon x hx.1 hx.2
  refine { exists_pair_ne := ⟨⊥, ⊤, ?_⟩, eq_bot_or_eq_top := ?_ }
  · intro h
    have h1' : (⟨w, hwW⟩ : W.toSubmodule) ∈ (⊤ : Subrepresentation W.toRepresentation).toSubmodule :=
      Submodule.mem_top
    rw [← h] at h1'
    have h2' : (⟨w, hwW⟩ : W.toSubmodule) = 0 := (Submodule.mem_bot ℂ).1 h1'
    exact hw0 (congrArg Subtype.val h2')
  · intro U
    let U' : Subrepresentation ρ :=
      { toSubmodule := U.toSubmodule.map W.toSubmodule.subtype
        apply_mem_toSubmodule := by
          intro g v hv
          obtain ⟨u, hu, rfl⟩ := Submodule.mem_map.1 hv
          exact Submodule.mem_map.2 ⟨W.toRepresentation g u, U.apply_mem_toSubmodule g hu, rfl⟩ }
    have hU'le : U'.toSubmodule ≤ W.toSubmodule := by
      intro v hv
      obtain ⟨u, _, rfl⟩ := Submodule.mem_map.1 hv
      exact u.2
    by_cases hF : fixed ρ K ⊓ U'.toSubmodule = ⊥
    · left
      obtain ⟨C, hC⟩ := hcompl U'
      have hFC : fixed ρ K ⊓ W.toSubmodule ≤ C.toSubmodule := by
        rintro x ⟨hxF, hxW⟩
        have hx : x ∈ U'.toSubmodule ⊔ C.toSubmodule := by
          rw [hC.sup_eq_top]
          exact Submodule.mem_top
        obtain ⟨u, hu, c, hc, rfl⟩ := Submodule.mem_sup.1 hx
        have huF : u ∈ fixed ρ K := (mem_fixed_iff ρ K u).2 fun k =>
          fixed_split ρ U' C hC.inf_eq_bot k hu hc ((mem_fixed_iff ρ K _).1 hxF k)
        have hu0 : u ∈ fixed ρ K ⊓ U'.toSubmodule := ⟨huF, hu⟩
        rw [hF] at hu0
        rw [(Submodule.mem_bot ℂ).1 hu0, zero_add]
        exact hc
      have hWC := h3 C hFC
      apply Subrepresentation.ext
      show U.toSubmodule = (⊥ : Submodule ℂ W.toSubmodule)
      rw [Submodule.eq_bot_iff]
      intro u hu
      have hm : (u : V) ∈ U'.toSubmodule ⊓ C.toSubmodule :=
        ⟨Submodule.mem_map_of_mem hu, hWC u.2⟩
      rw [hC.inf_eq_bot] at hm
      exact Subtype.ext ((Submodule.mem_bot ℂ).1 hm)
    · right
      have hWU := h3 U' (h2 U' hU'le hF)
      apply Subrepresentation.ext
      show U.toSubmodule = (⊤ : Submodule ℂ W.toSubmodule)
      rw [eq_top_iff]
      intro x _
      obtain ⟨u, hu, hux⟩ := Submodule.mem_map.1 (hWU x.2)
      have : u = x := Subtype.ext hux
      rw [← this]
      exact hu

end Gen

theorem exists_irreducible_le {G V : Type} [Group G] [TopologicalSpace G] [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ G V)
    (hsmall : ∀ U ∈ nhds (1 : G), ∃ K : Subgroup G, IsOpen (K : Set G) ∧ IsCompact (K : Set G) ∧ (K : Set G) ⊆ U)
    (hA : GlobalTheory.PRep.IsAdmissible ρ)
    (hcompl : ∀ S : Subrepresentation ρ, ∃ T : Subrepresentation ρ, IsCompl S.toSubmodule T.toSubmodule)
    (S : Subrepresentation ρ) (hS : S ≠ ⊥) :
    ∃ S₀ : Subrepresentation ρ, S₀ ≠ ⊥ ∧ S₀.toSubmodule ≤ S.toSubmodule ∧ S₀.toRepresentation.IsIrreducible := by
  obtain ⟨v, hvS, hv0⟩ : ∃ v ∈ S.toSubmodule, v ≠ 0 := by
    by_contra hcon
    push Not at hcon
    apply hS
    apply Subrepresentation.ext
    show S.toSubmodule = (⊥ : Submodule ℂ V)
    rw [Submodule.eq_bot_iff]
    exact hcon
  obtain ⟨K, hKo, hKc, hKv⟩ := hsmall {g | ρ g v = v} ((hA.1 v).mem_nhds (by simp))
  have hFd : FiniteDimensional ℂ (fixed ρ K) := hA.2 K hKo hKc
  have hvF : v ∈ fixed ρ K := (mem_fixed_iff ρ K v).2 fun k => hKv k.2
  have hex : ∃ n, ∃ W : Subrepresentation ρ, W.toSubmodule ≤ S.toSubmodule ∧
      fixed ρ K ⊓ W.toSubmodule ≠ ⊥ ∧ Module.finrank ℂ (fixed ρ K ⊓ W.toSubmodule : Submodule ℂ V) = n := by
    refine ⟨_, S, le_rfl, ?_, rfl⟩
    intro h
    have : v ∈ fixed ρ K ⊓ S.toSubmodule := ⟨hvF, hvS⟩
    rw [h] at this
    exact hv0 ((Submodule.mem_bot ℂ).1 this)
  obtain ⟨W, hWS, hW0, hWn⟩ := Nat.find_spec hex
  set W₀ := genSub ρ (fixed ρ K ⊓ W.toSubmodule) with hW₀def
  have hW₀W : W₀.toSubmodule ≤ W.toSubmodule := genSub_le ρ _ W inf_le_right
  have hF₀ : fixed ρ K ⊓ W₀.toSubmodule = fixed ρ K ⊓ W.toSubmodule :=
    le_antisymm (inf_le_inf_left _ hW₀W) (le_inf inf_le_left (le_genSub ρ _))
  refine ⟨W₀, ?_, hW₀W.trans hWS, ?_⟩
  · intro h
    apply hW0
    rw [← hF₀, h]
    exact inf_bot_eq _
  · refine irreducible_of_fixed ρ K hcompl W₀ (by rwa [hF₀]) ?_ ?_
    · intro U hU hUne
      have hmin := Nat.find_min' hex ⟨U, hU.trans (hW₀W.trans hWS), hUne, rfl⟩
      rw [← hWn] at hmin
      have : FiniteDimensional ℂ (fixed ρ K ⊓ W.toSubmodule : Submodule ℂ V) :=
        Submodule.finiteDimensional_of_le inf_le_left
      have hle : fixed ρ K ⊓ U.toSubmodule ≤ fixed ρ K ⊓ W.toSubmodule := hF₀ ▸ inf_le_inf_left _ hU
      have heq := Submodule.eq_of_le_of_finrank_le hle hmin
      rw [hF₀, ← heq]
      exact inf_le_right
    · intro U hU
      rw [hF₀] at hU
      exact genSub_le ρ _ U hU

end PositivityTheory.RgUd.Prod.Asm
