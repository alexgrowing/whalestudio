import Mathlib
import Formalism.WachLatticeTwists.LatticeDualFibres.FibreDualStable
import Formalism.GaloisCohomology.LocalTateDualityK
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FactorMemCocyclesPowQuot
open Formalism.RepresentationBoundsCohomology.LOC ReciprocityTheory.Gal GlobalTheory.LocDualInt
open Formalism.NG (KO)

noncomputable section

namespace GlobalTheory.CocycleLimit

theorem exists_continuous_cocycle_lift_of_compatible : ∀ {O : Type} [CommRing O] {G : Type} [Group G] [TopologicalSpace G] {M : Type} [AddCommGroup M] [Module O M] [TopologicalSpace M] [IsTopologicalAddGroup M] [ContinuousConstSMul O M] [T2Space M] [CompactSpace M] (ρ : Representation O G M) (a : O) (r : ℕ), (∀ n : ℕ, IsOpen ((powSub (M := M) a n : Submodule O M) : Set M)) → (∀ U ∈ nhds (0 : M), ∃ n : ℕ, ((powSub (M := M) a n : Submodule O M) : Set M) ⊆ U) → ∀ w : ℕ → G → M, (∀ k, (fun g => (Submodule.Quotient.mk (w k g) : M ⧸ powSub (M := M) a (r + k))) ∈ Z1 (quotRep ρ a (r + k))) → (∀ k g, w (k + 1) g - w k g ∈ powSub (M := M) a (r + k)) → ∃ e ∈ Z1 ρ, ∀ k g, e g - w k g ∈ powSub (M := M) a (r + k) := by
  intro O _ G _ _ M _ _ _ _ _ _ _ ρ a r hopen hbasis w hw hstep
  set N : ℕ → Submodule O M := fun n => powSub (M := M) a n with hN

  have hclosedN : ∀ n, IsClosed ((N n : Submodule O M) : Set M) := fun n =>
    AddSubgroup.isClosed_of_isOpen (N n).toAddSubgroup (hopen n)

  have hex : ∀ g, ∃ x, ∀ k, x - w k g ∈ N (r + k) := by
    intro g
    let C : ℕ → Set M := fun k => {x | x - w k g ∈ N (r + k)}
    have hsub : ∀ k, C (k + 1) ⊆ C k := by
      intro k x hx
      have h1 : x - w (k + 1) g ∈ N (r + k) :=
        powSub_anti a (by omega : r + k ≤ r + (k + 1)) hx
      have h2 := hstep k g
      show x - w k g ∈ N (r + k)
      have : x - w k g = (x - w (k + 1) g) + (w (k + 1) g - w k g) := by abel
      rw [this]; exact (N (r + k)).add_mem h1 h2
    have hne : ∀ k, (C k).Nonempty := fun k => ⟨w k g, by simp [C, (N (r + k)).zero_mem]⟩
    have hcl : ∀ k, IsClosed (C k) := fun k =>
      (hclosedN (r + k)).preimage (continuous_id.sub continuous_const)
    obtain ⟨x, hx⟩ := IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed C hsub hne
      (hcl 0).isCompact hcl
    exact ⟨x, fun k => Set.mem_iInter.1 hx k⟩
  choose e he using hex

  have hzero : ∀ x : M, (∀ k, x ∈ N (r + k)) → x = 0 := by
    intro x hx
    by_contra hne
    obtain ⟨n, hn⟩ := hbasis ({x}ᶜ) (isOpen_compl_singleton.mem_nhds (Ne.symm hne))
    have : x ∈ N (r + n) := hx n
    exact hn (powSub_anti a (by omega : n ≤ r + n) this) rfl

  have hcoc : ∀ k g h, w k (g * h) - (w k g + ρ g (w k h)) ∈ N (r + k) := by
    intro k g h
    have := (hw k).2 g h
    simp only [quotRep_mk] at this
    rw [← Submodule.Quotient.mk_add] at this
    exact (Submodule.Quotient.eq _).1 this
  refine ⟨e, ⟨?_, ?_⟩, fun k g => he g k⟩
  ·
    rw [continuous_iff_continuousAt]
    intro g0 U hU
    have hV : {y : M | y + e g0 ∈ U} ∈ nhds (0 : M) :=
      (continuous_add_right (e g0)).continuousAt.preimage_mem_nhds (by simpa using hU)
    obtain ⟨n, hn⟩ := hbasis _ hV
    let q : G → M ⧸ powSub (M := M) a (r + n) := fun g => Submodule.Quotient.mk (w n g)
    have hq : Continuous q := (hw n).1
    have hsing : IsOpen ({q g0} : Set (M ⧸ powSub (M := M) a (r + n))) := by
      rw [← (Submodule.isOpenQuotientMap_mkQ (powSub (M := M) a (r + n))).isQuotientMap.isOpen_preimage]
      have : (Submodule.mkQ (powSub (M := M) a (r + n))) ⁻¹' {q g0} =
          (fun y => y - w n g0) ⁻¹' ((N (r + n) : Submodule O M) : Set M) := by
        ext y
        simp only [Set.mem_preimage, Set.mem_singleton_iff, Submodule.mkQ_apply, q,
          SetLike.mem_coe, N]
        exact Submodule.Quotient.eq _
      rw [this]
      exact (hopen (r + n)).preimage (continuous_id.sub continuous_const)
    have hS : q ⁻¹' {q g0} ∈ nhds g0 := (hsing.preimage hq).mem_nhds rfl
    show e ⁻¹' U ∈ nhds g0
    refine Filter.mem_of_superset hS ?_
    intro g hg
    have hg' : w n g - w n g0 ∈ N (r + n) := (Submodule.Quotient.eq _).1 hg
    have hmem : e g - e g0 ∈ N (r + n) := by
      have : e g - e g0 = (e g - w n g) + (w n g - w n g0) - (e g0 - w n g0) := by abel
      rw [this]
      exact (N (r + n)).sub_mem ((N (r + n)).add_mem (he g n) hg') (he g0 n)
    have := hn (powSub_anti a (by omega : n ≤ r + n) hmem)
    simpa using this
  ·
    intro g h
    rw [← sub_eq_zero]
    apply hzero
    intro k
    have : e (g * h) - (e g + ρ g (e h)) =
        (e (g * h) - w k (g * h)) - (e g - w k g) - ρ g (e h - w k h) +
          (w k (g * h) - (w k g + ρ g (w k h))) := by
      rw [map_sub]; abel
    rw [this]
    refine (N (r + k)).add_mem ((N (r + k)).sub_mem ((N (r + k)).sub_mem (he _ k) (he _ k))
      (powSub_stable ρ a _ g _ (he h k))) (hcoc k g h)

end GlobalTheory.CocycleLimit
