import Mathlib
import ReciprocityTheory.ReductiveGroups.TraceFormulas.LatDefs
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.H2EquivOfTorsionCharacter
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ContinuousTwoCocycleMultipleOfFundamental
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicCoboundaryOfDivisible
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FactorMemCocyclesPowQuot
open ReciprocityTheory.Gal Formalism.RepresentationBoundsCohomology.LOC ReciprocityTheory.ChartRestriction.T2 GlobalTheory.LocDualInt

namespace GlobalTheory.PadicH2SeparatedDVR

open GlobalTheory.LocDualInt

theorem discrete_quot {O : Type} [CommRing O] [TopologicalSpace O] [IsTopologicalRing O]
    (P : Submodule O O) (hP : IsOpen (P : Set O)) : DiscreteTopology (O ⧸ P) := by
  rw [discreteTopology_iff_isOpen_singleton]
  intro q
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective P q
  have hq := (Submodule.isOpenQuotientMap_mkQ P).isQuotientMap
  rw [← hq.isOpen_preimage]
  have : (P.mkQ ⁻¹' {Submodule.Quotient.mk x}) = (fun y => y - x) ⁻¹' (P : Set O) := by
    ext y
    simp only [Set.mem_preimage, Set.mem_singleton_iff, Submodule.mkQ_apply, SetLike.mem_coe]
    exact Submodule.Quotient.eq P
  rw [this]
  exact hP.preimage (continuous_sub_right x)

theorem continuous_mk {O : Type} [CommRing O] [TopologicalSpace O] [IsTopologicalRing O]
    (P : Submodule O O) : Continuous (Submodule.Quotient.mk : O → O ⧸ P) :=
  (Submodule.isOpenQuotientMap_mkQ P).continuous

theorem d1_mk {O : Type} [CommRing O] {G : Type} [Group G] (ε : G →* Oˣ) (ϖ : O) (n : ℕ)
    (b : G → O) :
    d1 (quotRep (twist ε O) ϖ n) (fun g => Submodule.Quotient.mk (b g)) =
      fun p => Submodule.Quotient.mk (d1 (twist ε O) b p) := by
  funext p
  show quotRep (twist ε O) ϖ n p.1 (Submodule.Quotient.mk (b p.2)) - Submodule.Quotient.mk (b (p.1 * p.2))
      + Submodule.Quotient.mk (b p.1) = Submodule.Quotient.mk ((twist ε O) p.1 (b p.2) - b (p.1 * p.2) + b p.1)
  rw [quotRep_mk, Submodule.Quotient.mk_add, Submodule.Quotient.mk_sub]

theorem separated_dvr_second_cohomology_mem : ∀ {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [TopologicalSpace O] [IsTopologicalRing O] [CompactSpace O] [T2Space O] {G : Type} [Group G] [TopologicalSpace G] (ε : G →* Oˣ) (ϖ : O), (∀ n : ℕ, IsOpen ((powSub (M := O) ϖ n : Submodule O O) : Set O)) → (∀ U ∈ nhds (0 : O), ∃ n : ℕ, ((powSub (M := O) ϖ n : Submodule O O) : Set O) ⊆ U) → (∀ n : ℕ, (Z1 (quotRep (twist ε O) ϖ n) : Set (G → O ⧸ powSub (M := O) ϖ n)).Finite) → ∀ (w : G × G → O), w ∈ Z2 (twist ε O) → (∀ n : ℕ, ∃ b : G → O ⧸ powSub (M := O) ϖ n, Continuous b ∧ ∀ g h : G, d1 (quotRep (twist ε O) ϖ n) b (g, h) = Submodule.Quotient.mk (w (g, h))) → w ∈ B2 (twist ε O) := by
  intro O _ _ _ _ _ _ _ G _ _ ε ϖ hopen hbasis hfin w hw hmod
  haveI hdisc : ∀ n : ℕ, DiscreteTopology (O ⧸ powSub (M := O) ϖ n) := fun n => discrete_quot _ (hopen n)
  let α : ∀ s : ℕ, Set (G → O ⧸ powSub (M := O) ϖ s) := fun s =>
    {β | Continuous β ∧ d1 (quotRep (twist ε O) ϖ s) β = fun p => Submodule.Quotient.mk (w p)}
  have hα : ∀ s, (α s).Finite := by
    intro s
    rcases Set.eq_empty_or_nonempty (α s) with h | ⟨c, hc⟩
    · rw [h]; exact Set.finite_empty
    refine ((hfin s).image (fun f => f + c)).subset ?_
    rintro β ⟨hβ, hd⟩
    refine ⟨β - c, ⟨hβ.sub hc.1, fun g h => ?_⟩, by simp⟩
    have e : d1 (quotRep (twist ε O) ϖ s) (β - c) (g, h) = 0 := by
      rw [map_sub, hd, hc.2, sub_self]; rfl
    have e2 : quotRep (twist ε O) ϖ s g ((β - c) h) - (β - c) (g * h) + (β - c) g = 0 := e
    have : (β - c) g + quotRep (twist ε O) ϖ s g ((β - c) h) - (β - c) (g * h) = 0 := by
      rw [← e2]; abel
    exact (sub_eq_zero.1 this).symm
  let T : ℕ → Set (G → O) := fun r =>
    ⋂ s, ⋂ (_ : s ≤ r), (fun (b : G → O) g =>
      (Submodule.Quotient.mk (b g) : O ⧸ powSub (M := O) ϖ s)) ⁻¹' α s
  have hcl : ∀ r, IsClosed (T r) := fun r =>
    isClosed_iInter fun s => isClosed_iInter fun _ => (hα s).isClosed.preimage
      (continuous_pi fun g => (continuous_mk _).comp (continuous_apply g))
  have hne : ∀ r, (T r).Nonempty := by
    intro r
    obtain ⟨β, hβc, hβ⟩ := hmod r
    refine ⟨fun g => qlift (β g), Set.mem_iInter₂.2 fun s hs => ⟨?_, ?_⟩⟩
    · have e : (fun g => (Submodule.Quotient.mk (qlift (β g)) : O ⧸ powSub (M := O) ϖ s)) =
          fun g => Submodule.factor (powSub_anti (M := O) ϖ hs) (β g) := by
        funext g
        conv_rhs => rw [← mk_qlift (β g)]
        rfl
      show Continuous (fun g => (Submodule.Quotient.mk (qlift (β g)) : O ⧸ powSub (M := O) ϖ s))
      rw [e]
      exact (continuous_factor ϖ hs).comp hβc
    · rw [d1_mk]
      funext p
      have h1 : (Submodule.Quotient.mk (d1 (twist ε O) (fun g => qlift (β g)) p) :
          O ⧸ powSub (M := O) ϖ r) = Submodule.Quotient.mk (w p) := by
        rw [← congrFun (d1_mk ε ϖ r (fun g => qlift (β g))) p]
        have : (fun g => (Submodule.Quotient.mk (qlift (β g)) : O ⧸ powSub (M := O) ϖ r)) = β :=
          funext fun g => mk_qlift _
        rw [this]
        exact hβ p.1 p.2
      rw [Submodule.Quotient.eq] at h1 ⊢
      exact powSub_anti ϖ hs h1
  have hdec : ∀ r, T (r + 1) ⊆ T r := fun r b hb =>
    Set.mem_iInter₂.2 fun s hs => Set.mem_iInter₂.1 hb s (hs.trans (Nat.le_succ r))
  obtain ⟨b, hb⟩ := IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed T hdec hne
    (hcl 0).isCompact hcl
  have hb' : ∀ s, (fun g => (Submodule.Quotient.mk (b g) : O ⧸ powSub (M := O) ϖ s)) ∈ α s :=
    fun s => Set.mem_iInter₂.1 (Set.mem_iInter.1 hb s) s le_rfl
  have hbc : Continuous b := by
    rw [continuous_iff_continuousAt]
    intro x V hV
    have hW : (fun u => u + b x) ⁻¹' V ∈ nhds (0 : O) := by
      apply (continuous_add_const (b x)).continuousAt.preimage_mem_nhds
      simpa using hV
    obtain ⟨n, hn⟩ := hbasis _ hW
    have hloc : {y | (Submodule.Quotient.mk (b y) : O ⧸ powSub (M := O) ϖ n) =
        Submodule.Quotient.mk (b x)} ∈ nhds x :=
      ((isOpen_discrete {(Submodule.Quotient.mk (b x) : O ⧸ powSub (M := O) ϖ n)}).preimage
        (hb' n).1).mem_nhds rfl
    show b ⁻¹' V ∈ nhds x
    refine Filter.mem_of_superset hloc fun y hy => ?_
    have hy' : b y - b x ∈ powSub (M := O) ϖ n := (Submodule.Quotient.eq _).1 hy
    have := hn hy'
    simpa using this
  refine ⟨b, hbc, ?_⟩
  funext p
  have hall : ∀ n : ℕ, d1 (twist ε O) b p - w p ∈ powSub (M := O) ϖ n := by
    intro n
    have := congrFun (hb' n).2 p
    rw [d1_mk] at this
    exact (Submodule.Quotient.eq _).1 this
  by_contra hne'
  have hd : d1 (twist ε O) b p - w p ≠ 0 := sub_ne_zero.2 hne'
  obtain ⟨n, hn⟩ := hbasis _ (isOpen_compl_singleton.mem_nhds (Ne.symm hd))
  exact hn (hall n) rfl

end GlobalTheory.PadicH2SeparatedDVR
