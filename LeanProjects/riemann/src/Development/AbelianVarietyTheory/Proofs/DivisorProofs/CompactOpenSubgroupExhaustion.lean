import Development.AbelianVarietyTheory.Definitions.Divisors.UnipVal
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicIsNonarchimedeanLocalField
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FourierTransformInversionLocalFieldPi

open MeasureTheory Matrix GlobalTheory.KSp GlobalTheory.SplitUnitary
open GlobalTheory.WeilM (UG IsQuad IsHerm ResEtaPow)
open GlobalTheory.SplitWeil (SB nabs)
open scoped Topology

namespace GlobalTheory.KSp.GoodSpace

open GlobalTheory.SplitWeil GlobalTheory.SplitWeil.FourierPi ValuativeRel

theorem good_of_addEquiv {X Y : Type} [AddCommGroup X] [TopologicalSpace X] [AddCommGroup Y] [TopologicalSpace Y]
    (f : X ≃+ Y) (hf : Continuous f) (hg : Continuous f.symm) (h : Good Y) : Good X := by
  let H : X ≃ₜ Y := { toEquiv := f.toEquiv, continuous_toFun := hf, continuous_invFun := hg }
  haveI := h.grp; haveI := h.t2; haveI := h.lc; haveI := h.sc
  refine ⟨?_, H.isEmbedding.t2Space, H.isClosedEmbedding.locallyCompactSpace, H.isInducing.secondCountableTopology,
    ?_, ?_⟩
  · haveI : ContinuousAdd X := by
      refine ⟨?_⟩
      have : (fun p : X × X => p.1 + p.2) = fun p => f.symm (f p.1 + f p.2) := by
        funext p; simp
      rw [this]; exact hg.comp ((hf.comp continuous_fst).add (hf.comp continuous_snd))
    haveI : ContinuousNeg X := by
      refine ⟨?_⟩
      have : (fun x : X => -x) = fun x => f.symm (-f x) := by funext x; simp
      rw [this]; exact hg.comp hf.neg
    exact {}
  · intro K hK
    obtain ⟨L, hLc, hLo, hKL⟩ := h.large (f '' K) (hK.image hf)
    refine ⟨L.comap f.toAddMonoidHom, ?_, ?_, ?_⟩
    · have : ((L.comap f.toAddMonoidHom : AddSubgroup X) : Set X) = H ⁻¹' (L : Set Y) := rfl
      rw [this]; exact H.isCompact_preimage.mpr hLc
    · exact hLo.preimage hf
    · intro x hx; exact hKL ⟨x, hx, rfl⟩
  · intro U hU
    have hU' : f.symm ⁻¹' U ∈ 𝓝 (0 : Y) := by
      apply hg.continuousAt.preimage_mem_nhds; simpa using hU
    obtain ⟨L, hLc, hLo, hLU⟩ := h.small _ hU'
    refine ⟨L.comap f.toAddMonoidHom, ?_, hLo.preimage hf, ?_⟩
    · have : ((L.comap f.toAddMonoidHom : AddSubgroup X) : Set X) = H ⁻¹' (L : Set Y) := rfl
      rw [this]; exact H.isCompact_preimage.mpr hLc
    · intro x hx
      have := hLU hx
      simpa using this

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]

def boxSub (n : Type) [Fintype n] [DecidableEq n] (s : Fˣ) : AddSubgroup (n → F) where
  carrier := box n s
  zero_mem' := fun i _ => by simp [cball]
  add_mem' := fun ha hb i _ => add_mem_cball (ha i trivial) (hb i trivial)
  neg_mem' := fun ha i _ => neg_mem_cball (ha i trivial)

theorem cball_mono {s t : Fˣ} (h : valuation F (s : F) ≤ valuation F (t : F)) : cball s ⊆ cball t :=
  fun x hx => show valuation F x ≤ valuation F (t : F) from le_trans hx h

theorem mem_some_cball (y : F) : ∃ s : Fˣ, y ∈ cball s := by
  by_cases hy : y = 0
  · exact ⟨1, by simp [cball, hy]⟩
  · exact ⟨Units.mk0 y hy, by simp [cball]⟩

theorem mem_some_box (n : Type) [Fintype n] [DecidableEq n] (x : n → F) : ∃ s : Fˣ, x ∈ box n s := by
  rcases isEmpty_or_nonempty n with hn | hn
  · exact ⟨1, fun i => isEmptyElim i⟩
  · choose u hu using fun i => mem_some_cball (x i)
    obtain ⟨j, hj⟩ := Finite.exists_max fun i => valuation F (u i : F)
    exact ⟨u j, fun i _ => cball_mono (hj i) (hu i)⟩

theorem good_pi (n : Type) [Fintype n] [DecidableEq n] : Good (n → F) := by
  haveI := secondCountable F
  haveI := t2Space F
  refine ⟨inferInstance, inferInstance, inferInstance, inferInstance, ?_, ?_⟩
  · intro K hK
    obtain ⟨s, hs⟩ := hK.elim_directed_cover (fun s : Fˣ => box n s) (fun s => isOpen_box s)
      (fun x _ => Set.mem_iUnion.mpr (mem_some_box n x)) (by
        intro s t
        rcases le_total (valuation F (s : F)) (valuation F (t : F)) with h | h
        · exact ⟨t, fun x hx i _ => cball_mono h (hx i trivial), le_rfl⟩
        · exact ⟨s, le_rfl, fun x hx i _ => cball_mono h (hx i trivial)⟩)
    exact ⟨boxSub n s, isCompact_box s, isOpen_box s, hs⟩
  · intro U hU
    obtain ⟨s, hs⟩ := exists_box_subset hU
    exact ⟨boxSub n s, isCompact_box s, isOpen_box s, hs⟩

end GlobalTheory.KSp.GoodSpace

theorem GlobalTheory.KSp.good_of_finiteDimensional : ∀ (F : Type) [Field F] [CharZero F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] (V : Type) [AddCommGroup V] [Module F V] [FiniteDimensional F V]
    [TopologicalSpace V] [IsModuleTopology F V], Good V := by
  intro F _ _ _ _ _ V _ _ _ _ _
  haveI := IsModuleTopology.topologicalAddGroup F V
  let b := Module.finBasis F V
  let e := b.equivFun
  exact GlobalTheory.KSp.GoodSpace.good_of_addEquiv e.toAddEquiv
    (IsModuleTopology.continuous_of_linearMap (R := F) e.toLinearMap)
    (IsModuleTopology.continuous_of_linearMap (R := F) e.symm.toLinearMap)
    (GlobalTheory.KSp.GoodSpace.good_pi _)
