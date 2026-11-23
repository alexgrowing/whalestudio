import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalMaximality.LiftFactorization

set_option autoImplicit false

noncomputable section

open GlobalTheory.PD GlobalTheory.WH

namespace UpperTheory.Gal.productCup_of_system

private theorem wd_single {σ E : Type} [LinearOrder σ] [Fintype σ] [AddCommGroup E] [Module ℂ E]
    (w : σ → Module.End ℂ E) (T : Finset σ) (v : E) :
    wd w (Pi.single T v) =
      ∑ i ∈ Tᶜ, Pi.single (insert i T) (GlobalTheory.cubeSign (insert i T) i • w i v) := by
  funext t
  have hl : wd w (Pi.single T v) t =
      ∑ i ∈ t, GlobalTheory.cubeSign t i • w i ((Pi.single T v : Finset σ → E) (t.erase i)) := by
    simp [wd, LinearMap.pi_apply, LinearMap.sum_apply]
  have L : ∑ i ∈ t, GlobalTheory.cubeSign t i • w i ((Pi.single T v : Finset σ → E) (t.erase i)) =
      ∑ i, if i ∈ t ∧ t.erase i = T then GlobalTheory.cubeSign t i • w i v else 0 := by
    rw [← Finset.sum_subset (Finset.subset_univ t) (fun i _ hi => by simp [hi])]
    refine Finset.sum_congr rfl fun i hi => ?_
    by_cases h : t.erase i = T
    · simp [hi, h]
    · simp [hi, h, Pi.single_eq_of_ne h]
  have Rr : (∑ i ∈ Tᶜ, (Pi.single (insert i T) (GlobalTheory.cubeSign (insert i T) i • w i v) :
      Finset σ → E)) t =
      ∑ i, if i ∉ T ∧ t = insert i T then GlobalTheory.cubeSign t i • w i v else 0 := by
    rw [Finset.sum_apply, ← Finset.sum_subset (Finset.subset_univ Tᶜ)
      (fun i _ hi => by simp at hi; simp [hi])]
    refine Finset.sum_congr rfl fun i hi => ?_
    have hi' : i ∉ T := by simpa using hi
    by_cases h : t = insert i T
    · subst h; simp [hi']
    · simp [hi', h, Pi.single_eq_of_ne h]
  rw [hl, L, Rr]
  refine Finset.sum_congr rfl fun i _ => ?_
  have : (i ∈ t ∧ t.erase i = T) ↔ (i ∉ T ∧ t = insert i T) := by
    constructor
    · rintro ⟨h1, rfl⟩
      exact ⟨Finset.notMem_erase _ _, (Finset.insert_erase h1).symm⟩
    · rintro ⟨h1, rfl⟩
      exact ⟨Finset.mem_insert_self _ _, Finset.erase_insert h1⟩
  simp only [this]

private theorem sm_dec {S E : Type} [CommRing S] [Algebra ℂ S] [AddCommGroup E] [Module ℂ E]
    (act : S →ₐ[ℂ] Module.End ℂ E) (M : Submodule ℂ E) {d : ℕ} (f : Fin d → S) {x : E}
    (hx : x ∈ sm act M (Set.range f)) :
    ∃ g : Fin d → E, (∀ j, g j ∈ M) ∧ x = ∑ j, act (f j) (g j) := by
  unfold sm at hx
  rw [iSup_range] at hx
  refine Submodule.iSup_induction _ (motive := fun x => ∃ g : Fin d → E, (∀ j, g j ∈ M) ∧
    x = ∑ j, act (f j) (g j)) hx ?_ ?_ ?_
  · intro j x hx
    obtain ⟨m, hm, rfl⟩ := hx
    refine ⟨Pi.single j m, fun i => ?_, ?_⟩
    · by_cases h : i = j
      · subst h; simpa using hm
      · simp [Pi.single_eq_of_ne h]
    · rw [Finset.sum_eq_single j]
      · simp
      · intro b _ hb
        simp [Pi.single_eq_of_ne hb]
      · simp
  · exact ⟨0, fun _ => M.zero_mem, by simp⟩
  · rintro x y ⟨g, hg, rfl⟩ ⟨g', hg', rfl⟩
    exact ⟨g + g', fun j => M.add_mem (hg j) (hg' j), by
      simp [Finset.sum_add_distrib]⟩

private theorem single_mem {σ E : Type} [LinearOrder σ] [AddCommGroup E] [Module ℂ E]
    (M : Submodule ℂ E) (w : σ → Module.End ℂ E) {T : Finset σ} {v : E} {d : ℕ}
    (hT : T.card = d) (hv : v ∈ M) :
    (Pi.single T v : Finset σ → E) ∈ (acx (fun _ => M) w).C d := by
  simp only [acx, Submodule.mem_pi]
  intro s _
  by_cases h : s = T
  · subst h; simp [hT, hv]
  · simp [Pi.single_eq_of_ne h]

theorem koszulTwoExact_of_gl2 : FiltrationCocycleLiftCriterion → SubQEx → KoszulCocycleExistsWithPrescribedComponent := by
  intro gl2 subq S E _ _ _ _ act κ _ _ R M r d e hst hr hke m hm hsm
  obtain ⟨Q, hQ⟩ : ∃ Q, Q = img e := ⟨_, rfl⟩
  have hcard : Q.card = d := by simp [hQ, img]
  have hQmem : ∀ j, e j ∈ Q := fun j => by simp [hQ, img]
  have qex : QEx (fun _ => M) (fun l => act (r l)) Q d := hQ ▸ subq S E act κ M r d e hke
  have wok : WOk (fun _ : Finset κ => M) (fun l => act (r l)) :=
    ⟨fun i j => by
      show act (r i) * act (r j) = act (r j) * act (r i)
      rw [← map_mul, ← map_mul, mul_comm], fun s i _ x hx => hst _ (hr i) _ hx⟩
  choose g hgM hg using fun l => sm_dec act M (fun j => r (e j)) (hsm l)
  have hTcard : ∀ l, l ∉ Q → ∀ j, ((insert l Q).erase (e j)).card = d := fun l hl j => by
    rw [Finset.card_erase_of_mem (Finset.mem_insert_of_mem (hQmem j)), Finset.card_insert_of_notMem hl,
      hcard]
    rfl
  have hTQ : ∀ l, l ∉ Q → ∀ j, ((insert l Q).erase (e j)) ∩ Q = Q.erase (e j) := fun l hl j => by
    ext i
    simp only [Finset.mem_inter, Finset.mem_erase, Finset.mem_insert]
    constructor
    · rintro ⟨⟨h1, _⟩, h3⟩
      exact ⟨h1, h3⟩
    · rintro ⟨h1, h2⟩
      exact ⟨⟨h1, Or.inr h2⟩, h2⟩
  have hterm : ∀ l, l ∉ Q → ∀ j (v : E),
      wd (wOn Q fun l => act (r l)) (Pi.single ((insert l Q).erase (e j)) v) =
        Pi.single (insert l Q) (GlobalTheory.cubeSign (insert l Q) (e j) • act (r (e j)) v) := by
    intro l hl j v
    have hmem : e j ∈ insert l Q := Finset.mem_insert_of_mem (hQmem j)
    rw [wd_single, Finset.sum_eq_single (e j)]
    · rw [Finset.insert_erase hmem]
      simp [wOn, hQmem j]
    · intro i hi hne
      have hiQ : i ∉ Q := by
        intro h
        apply (Finset.mem_compl.1 hi)
        exact Finset.mem_erase.2 ⟨hne, Finset.mem_insert_of_mem h⟩
      simp [wOn, hiQ]
    · intro h
      exact absurd (Finset.mem_compl.2 (Finset.notMem_erase _ _)) h
  have hsum : ∀ (t : Finset κ) (f : Fin d → E),
      (Pi.single t (∑ j, f j) : Finset κ → E) = ∑ j, Pi.single t (f j) := fun t f =>
    map_sum (AddMonoidHom.single (fun _ : Finset κ => E) t) f Finset.univ
  have hy : ∃ y ∈ (acx (fun _ => M) (fun l => act (r l))).C d, Lev Q (· = (d : ℤ) - 1) y ∧
      wd (wOn Q fun l => act (r l)) y = wd (wOn Qᶜ fun l => act (r l)) (Pi.single Q m) := by
    refine ⟨∑ l ∈ Qᶜ, ∑ j, Pi.single ((insert l Q).erase (e j))
        ((GlobalTheory.cubeSign (insert l Q) l * GlobalTheory.cubeSign (insert l Q) (e j)) • g l j), ?_, ?_, ?_⟩
    · refine Submodule.sum_mem _ fun l hl => Submodule.sum_mem _ fun j _ => ?_
      have hl' : l ∉ Q := by simpa using hl
      exact single_mem M _ (hTcard l hl' j) (Submodule.smul_of_tower_mem _ _ (hgM l j))
    · intro s hs
      rw [Finset.sum_apply]
      refine Finset.sum_eq_zero fun l hl => ?_
      have hl' : l ∉ Q := by simpa using hl
      rw [Finset.sum_apply]
      refine Finset.sum_eq_zero fun j _ => ?_
      have : s ≠ (insert l Q).erase (e j) := by
        rintro rfl
        apply hs
        rw [hTQ l hl' j, Finset.card_erase_of_mem (hQmem j), hcard]
        have : 1 ≤ d := by
          rw [← hcard]
          exact Finset.card_pos.2 ⟨_, hQmem j⟩
        omega
      exact Pi.single_eq_of_ne this _
    · rw [wd_single, map_sum]
      refine Finset.sum_congr rfl fun l hl => ?_
      have hl' : l ∉ Q := by simpa using hl
      have hlc : l ∈ Qᶜ := hl
      rw [map_sum]
      simp only [hterm l hl']
      rw [← hsum]
      congr 1
      have hw : wOn Qᶜ (fun l => act (r l)) l m = ∑ j, act (r (e j)) (g l j) := by
        simpa [wOn, hl'] using hg l
      rw [hw, Finset.smul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [map_zsmul, smul_smul, mul_comm, mul_assoc, GlobalTheory.cubeSign_mul_self, mul_one]
  obtain ⟨c, hc, hlev⟩ := gl2 κ E (fun _ => M) (fun l => act (r l)) Q d d wok qex
    (Pi.single Q m) (single_mem M _ hcard hm)
    (by
      intro s hs
      have : s ≠ Q := by
        rintro rfl
        simp [hcard] at hs
      exact Pi.single_eq_of_ne this _)
    (by
      rw [wd_single]
      refine Finset.sum_eq_zero fun i hi => ?_
      have : i ∉ Q := by simpa using hi
      simp [wOn, this])
    hy
  refine ⟨c, hc, ?_⟩
  have h := hlev Q (by simp [hcard])
  rw [hQ] at h
  have h' : c (img e) - (Pi.single (img e) m : Finset κ → E) (img e) = 0 := h
  simpa [sub_eq_zero] using h'

end UpperTheory.Gal.productCup_of_system

end
