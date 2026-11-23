import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SimpleOver

open scoped TensorProduct

namespace GlobalTheory.TensHead

section HeadKill

variable {W : Type} [AddCommGroup W] [Module ℂ W]

def MinStab (A : Set (Module.End ℂ W)) (T : Submodule ℂ W) : Prop :=
  Stab A T ∧ ∀ U : Submodule ℂ W, Stab A U → U ≤ T → U = ⊥ ∨ U = T

theorem MinStab.map {A : Set (Module.End ℂ W)} {T : Submodule ℂ W} (hT : MinStab A T)
    (b : Module.End ℂ W) (hb : ∀ a ∈ A, a * b = b * a) : MinStab A (T.map b) := by
  obtain ⟨hTs, hTmin⟩ := hT
  have hcomm' : ∀ a ∈ A, ∀ x, a (b x) = b (a x) := fun a ha x =>
    LinearMap.congr_fun (hb a ha) x
  refine ⟨?_, ?_⟩
  · intro a ha y hy
    obtain ⟨x, hx, rfl⟩ := Submodule.mem_map.mp hy
    rw [hcomm' a ha x]
    exact Submodule.mem_map_of_mem (hTs a ha x hx)
  · intro U hU hUle
    have hU' : Stab A (T ⊓ U.comap b) := by
      intro a ha x hx
      refine ⟨hTs a ha x hx.1, ?_⟩
      show b (a x) ∈ U
      rw [← hcomm' a ha x]
      exact hU a ha (b x) hx.2
    rcases hTmin _ hU' inf_le_left with h | h
    · left
      rw [eq_bot_iff]
      intro u hu
      obtain ⟨x, hx, rfl⟩ := Submodule.mem_map.mp (hUle hu)
      have hx' : x ∈ T ⊓ U.comap b := ⟨hx, hu⟩
      rw [h] at hx'
      rw [(Submodule.mem_bot ℂ).mp hx', map_zero]
      exact Submodule.zero_mem _
    · right
      refine le_antisymm hUle ?_
      rw [Submodule.map_le_iff_le_comap]
      intro x hx
      have hx' : x ∈ T ⊓ U.comap b := by rw [h]; exact hx
      exact hx'.2

theorem exists_stab_compl {A : Set (Module.End ℂ W)}
    (htop : sSup {T | MinStab A T} = ⊤) (K : Submodule ℂ W) (hK : Stab A K) :
    ∃ C : Submodule ℂ W, Stab A C ∧ C ⊓ K = ⊥ ∧ C ⊔ K = ⊤ := by
  have hsup : ∀ N N' : Submodule ℂ W, Stab A N → Stab A N' → Stab A (N ⊔ N') := by
    intro N N' hN hN' a ha x hx
    obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.mp hx
    rw [map_add]
    exact Submodule.add_mem_sup (hN a ha y hy) (hN' a ha z hz)
  let S : Set (Submodule ℂ W) := {C | Stab A C ∧ C ⊓ K = ⊥}
  obtain ⟨C, hCmax⟩ : ∃ C, Maximal (· ∈ S) C := by
    refine zorn_le₀ S ?_
    intro c hcS hc
    rcases c.eq_empty_or_nonempty with rfl | hne
    · refine ⟨⊥, ⟨?_, bot_inf_eq _⟩, by simp⟩
      intro a _ x hx
      rw [(Submodule.mem_bot ℂ).mp hx, map_zero]
      exact Submodule.zero_mem _
    · refine ⟨sSup c, ⟨?_, ?_⟩, fun z hz => le_sSup hz⟩
      · intro a ha x hx
        rw [Submodule.mem_sSup_of_directed hne hc.directedOn] at hx ⊢
        obtain ⟨y, hy, hxy⟩ := hx
        exact ⟨y, hy, (hcS hy).1 a ha x hxy⟩
      · rw [eq_bot_iff]
        intro x hx0
        obtain ⟨hx, hxK⟩ := Submodule.mem_inf.mp hx0
        rw [Submodule.mem_sSup_of_directed hne hc.directedOn] at hx
        obtain ⟨y, hy, hxy⟩ := hx
        have hx' : x ∈ y ⊓ K := ⟨hxy, hxK⟩
        rwa [(hcS hy).2] at hx'
  obtain ⟨⟨hCs, hCK⟩, hCm⟩ := hCmax
  refine ⟨C, hCs, hCK, ?_⟩
  by_contra hne
  have hex : ∃ T, MinStab A T ∧ ¬ T ≤ C ⊔ K := by
    by_contra h
    simp only [not_exists, not_and, not_not] at h
    exact hne (top_unique (by rw [← htop]; exact sSup_le fun T hT => h T hT))
  obtain ⟨T, ⟨hTs, hTmin⟩, hTn⟩ := hex
  have hI : Stab A (T ⊓ (C ⊔ K)) := fun a ha x hx =>
    ⟨hTs a ha x hx.1, hsup C K hCs hK a ha x hx.2⟩
  rcases hTmin _ hI inf_le_left with h | h
  · have hmem : C ⊔ T ∈ S := by
      refine ⟨hsup C T hCs hTs, ?_⟩
      rw [eq_bot_iff]
      intro x hx0
      obtain ⟨hx, hxK⟩ := Submodule.mem_inf.mp hx0
      obtain ⟨c, hc, t, ht, rfl⟩ := Submodule.mem_sup.mp hx
      have ht' : t ∈ T ⊓ (C ⊔ K) := by
        refine ⟨ht, ?_⟩
        simpa using Submodule.sub_mem _ (Submodule.mem_sup_right hxK : c + t ∈ C ⊔ K)
          (Submodule.mem_sup_left hc : c ∈ C ⊔ K)
      have ht0 : t = 0 := by
        rw [h] at ht'
        exact (Submodule.mem_bot ℂ).mp ht'
      subst ht0
      rw [add_zero] at hxK ⊢
      have hc' : c ∈ C ⊓ K := ⟨hc, hxK⟩
      rwa [hCK] at hc'
    have hle : C ⊔ T ≤ C := hCm hmem le_sup_left
    exact hTn ((le_sup_right.trans hle).trans le_sup_left)
  · exact hTn (inf_eq_left.mp h)

end HeadKill

theorem le_ker_of_simple_commuting {M W : Type} [AddCommGroup M] [Module ℂ M] [AddCommGroup W]
    [Module ℂ W]
    (Op : Set (Module.End ℂ M)) (Rel K : Submodule ℂ M) (φ : M →ₗ[ℂ] W)
    (act : Module.End ℂ M → Module.End ℂ W) (B : Set (Module.End ℂ W))
    (hL : ∃ L : ℕ, ∀ (m : ℕ) (N : Fin m → Submodule ℂ M), StrictMono N →
        (∀ j, Rel ≤ N j ∧ ∀ g ∈ Op, ∀ x ∈ N j, g x ∈ N j) → m ≤ L)
    (hmax : ∀ N : Submodule ℂ M, Rel ≤ N → Stab Op N → N ≠ ⊤ → N ≤ K)
    (hKtop : K ≠ ⊤) (hK : Stab Op K) (hRel : Rel ≤ LinearMap.ker φ)
    (hφ : ∀ g ∈ Op, φ ∘ₗ g = act g ∘ₗ φ)
    (hcomm : ∀ g ∈ Op, ∀ b ∈ B, act g * b = b * act g)
    (hsimple : ∀ U : Submodule ℂ W, Stab (act '' Op ∪ B) U → U = ⊥ ∨ U = ⊤) :
    K ≤ LinearMap.ker φ := by
  classical
  have hint : ∀ g ∈ Op, ∀ x, φ (g x) = act g (φ x) := fun g hg x =>
    LinearMap.congr_fun (hφ g hg) x
  by_cases hφ0 : LinearMap.range φ = ⊥
  · intro x _
    have hx : φ x ∈ LinearMap.range φ := LinearMap.mem_range_self φ x
    rw [hφ0] at hx
    exact (Submodule.mem_bot ℂ).mp hx
  have hrange : Stab (act '' Op) (LinearMap.range φ) := by
    intro a ha y hy
    obtain ⟨g, hg, rfl⟩ := ha
    obtain ⟨x, rfl⟩ := LinearMap.mem_range.mp hy
    exact LinearMap.mem_range.mpr ⟨g x, hint g hg x⟩
  have hcomap : ∀ U : Submodule ℂ W, Stab (act '' Op) U → Stab Op (U.comap φ) := by
    intro U hU g hg x hx
    show φ (g x) ∈ U
    rw [hint g hg x]
    exact hU _ ⟨g, hg, rfl⟩ _ hx
  have hRelc : ∀ U : Submodule ℂ W, Rel ≤ U.comap φ := by
    intro U x hx
    show φ x ∈ U
    rw [LinearMap.mem_ker.mp (hRel hx)]
    exact U.zero_mem
  obtain ⟨L, hL⟩ := hL
  let P : Set (Submodule ℂ W) := {U | U ≤ LinearMap.range φ ∧ Stab (act '' Op) U ∧ U ≠ ⊥}
  have hwf : P.WellFoundedOn (· < ·) := by
    rw [Set.wellFoundedOn_iff_no_descending_seq]
    intro f hf
    have hlt : ∀ m n : ℕ, m < n → f n < f m := fun m n h => f.map_rel_iff.mpr h
    have hmono : StrictMono (fun i : Fin (L + 1) => (f (L - i.val)).comap φ) := by
      intro i j hij
      have hij' : (i : ℕ) < j := hij
      have hj := j.isLt
      have hlt' : f (L - i.val) < f (L - j.val) := hlt _ _ (by omega)
      show (f (L - i.val)).comap φ < (f (L - j.val)).comap φ
      refine lt_of_le_of_ne (Submodule.comap_mono hlt'.le) ?_
      intro heq
      have hmap := congrArg (Submodule.map φ) heq
      rw [Submodule.map_comap_eq_self (hf _).1, Submodule.map_comap_eq_self (hf _).1] at hmap
      exact hlt'.ne hmap
    have hbound := hL (L + 1) _ hmono (fun j => ⟨hRelc _, hcomap _ (hf _).2.1⟩)
    omega
  have hPne : LinearMap.range φ ∈ P := ⟨le_rfl, hrange, hφ0⟩
  obtain ⟨T, hTP, hTmin⟩ := (Set.wellFoundedOn_iff.mp hwf).has_min P ⟨_, hPne⟩
  have hTms : MinStab (act '' Op) T := by
    refine ⟨hTP.2.1, fun U hU hUT => ?_⟩
    by_cases hU0 : U = ⊥
    · exact Or.inl hU0
    · right
      by_contra hne
      have hUP : U ∈ P := ⟨hUT.trans hTP.1, hU, hU0⟩
      exact hTmin U hUP ⟨lt_of_le_of_ne hUT hne, hUP, hTP⟩
  have hbcomm : ∀ b ∈ B, ∀ a ∈ act '' Op, a * b = b * a := by
    rintro b hb _ ⟨g, hg, rfl⟩
    exact hcomm g hg b hb
  have hstop : sSup {T | MinStab (act '' Op) T} = ⊤ := by
    have hst : Stab (act '' Op ∪ B) (sSup {T | MinStab (act '' Op) T}) := by
      intro a ha
      rcases ha with ha | ha
      · have hle : sSup {T | MinStab (act '' Op) T} ≤ (sSup {T | MinStab (act '' Op) T}).comap a :=
          sSup_le fun T' hT' y hy => (le_sSup hT' : T' ≤ _) (hT'.1 a ha y hy)
        exact fun x hx => hle hx
      · have hle : sSup {T | MinStab (act '' Op) T} ≤ (sSup {T | MinStab (act '' Op) T}).comap a :=
          sSup_le fun T' hT' y hy =>
            (le_sSup (MinStab.map hT' a (hbcomm a ha)) : T'.map a ≤ _) (Submodule.mem_map_of_mem hy)
        exact fun x hx => hle hx
    rcases hsimple _ hst with h | h
    · exact absurd (eq_bot_iff.mpr ((le_sSup (show T ∈ {T | MinStab (act '' Op) T} from hTms)).trans h.le)) hTP.2.2
    · exact h
  have hKs : Stab (act '' Op) (K.map φ) := by
    intro a ha y hy
    obtain ⟨g, hg, rfl⟩ := ha
    obtain ⟨k, hk, rfl⟩ := Submodule.mem_map.mp hy
    rw [← hint g hg k]
    exact Submodule.mem_map_of_mem (hK g hg k hk)
  obtain ⟨C, hCs, hCK, hCtop⟩ := exists_stab_compl hstop (K.map φ) hKs
  have hNK : C.comap φ ⊔ K = ⊤ := by
    rw [eq_top_iff]
    intro m _
    have hm : φ m ∈ C ⊔ K.map φ := by rw [hCtop]; exact Submodule.mem_top
    obtain ⟨c, hc, y, hy, hcy⟩ := Submodule.mem_sup.mp hm
    obtain ⟨k, hk, rfl⟩ := Submodule.mem_map.mp hy
    have hmk : m - k ∈ C.comap φ := by
      show φ (m - k) ∈ C
      rw [map_sub, ← hcy, add_sub_cancel_right]
      exact hc
    simpa using Submodule.add_mem_sup hmk hk
  by_cases hN : C.comap φ = ⊤
  · intro k hk
    have h1 : k ∈ C.comap φ := by rw [hN]; exact Submodule.mem_top
    have h2 : φ k ∈ C ⊓ K.map φ := ⟨h1, Submodule.mem_map_of_mem hk⟩
    rw [hCK] at h2
    exact (Submodule.mem_bot ℂ).mp h2
  · exact absurd (top_unique (hNK.symm.le.trans
      (sup_le (hmax _ (hRelc C) (hcomap C hCs) hN) le_rfl))) hKtop

end GlobalTheory.TensHead
