import Mathlib

open TopologicalSpace Order

namespace GlobalTheory.DimDrop

theorem length_le_topologicalKrullDim_of_last_subset {X : Type} [TopologicalSpace X] (Z : Set X)
    (q : LTSeries (IrreducibleCloseds X)) (h : (q.last : Set X) ⊆ Z) :
    (q.length : WithBot ℕ∞) ≤ topologicalKrullDim Z := by
  have hsub : ∀ i, (q i : Set X) ⊆ Z := fun i x hx => h (q.monotone (Fin.le_last i) hx)
  have irr : ∀ i, IsIrreducible (Subtype.val ⁻¹' (q i : Set X) : Set Z) := by
    intro i
    haveI : IrreducibleSpace (q i : Set X) := Subtype.irreducibleSpace (q i).isIrreducible
    have := (IrreducibleSpace.isIrreducible_univ (q i : Set X)).image (Set.inclusion (hsub i))
      (continuous_inclusion (hsub i)).continuousOn
    rw [Set.image_univ, Set.range_inclusion] at this
    exact this
  let f : Fin (q.length + 1) → IrreducibleCloseds Z := fun i =>
    ⟨Subtype.val ⁻¹' (q i : Set X), irr i, (q i).isClosed.preimage continuous_subtype_val⟩
  have hf : ∀ i j, f i = f j → q i = q j := by
    intro i j e
    have e' : (Subtype.val ⁻¹' (q i : Set X) : Set Z) = Subtype.val ⁻¹' (q j : Set X) :=
      congrArg SetLike.coe e
    have e'' := congrArg (Set.image (Subtype.val : Z → X)) e'
    rw [Subtype.image_preimage_coe, Subtype.image_preimage_coe,
      Set.inter_eq_right.2 (hsub i), Set.inter_eq_right.2 (hsub j)] at e''
    exact SetLike.coe_injective e''
  let p : LTSeries (IrreducibleCloseds Z) :=
    { length := q.length
      toFun := f
      step := fun i => by
        have hs : q i.castSucc < q i.succ := q.step i
        show f i.castSucc < f i.succ
        refine lt_of_le_of_ne ?_ fun e => hs.ne (hf _ _ e)
        intro x hx
        exact hs.le hx }
  exact LTSeries.length_le_krullDim p

theorem topologicalKrullDim_lt_of_isClosed (S : Type) [TopologicalSpace S] [NoetherianSpace S]
    (C : Set S) (d : ℕ) (hC : IsClosed C) (hS : topologicalKrullDim S ≤ d)
    (hZ : ∀ Z ∈ irreducibleComponents S, (d : WithBot ℕ∞) ≤ topologicalKrullDim Z → ¬ Z ⊆ C) :
    topologicalKrullDim C < d := by
  by_contra hlt
  rw [not_lt] at hlt
  obtain ⟨p, hp⟩ := le_krullDim_iff.1 hlt
  let q : LTSeries (IrreducibleCloseds S) :=
    p.map (IrreducibleCloseds.map Subtype.val continuous_subtype_val)
      (IrreducibleCloseds.map_strictMono_of_isInducing Topology.IsInducing.subtypeVal)
  have hql : q.length = d := hp
  have hWC : (q.last : Set S) ⊆ C := by
    show closure (Subtype.val '' (p.last : Set C)) ⊆ C
    refine closure_minimal ?_ hC
    rintro _ ⟨x, -, rfl⟩
    exact x.2
  obtain ⟨Z, hZc, hWZ⟩ :=
    exists_mem_irreducibleComponents_subset_of_isIrreducible _ q.last.isIrreducible
  by_cases hEq : (q.last : Set S) = Z
  · refine hZ Z hZc ?_ (hEq ▸ hWC)
    have := length_le_topologicalKrullDim_of_last_subset Z q hEq.le
    rwa [hql] at this
  · let Zt : IrreducibleCloseds S := ⟨Z, hZc.1, isClosed_of_mem_irreducibleComponents Z hZc⟩
    have hlt' : q.last < Zt := lt_of_le_of_ne hWZ fun e => hEq (congrArg SetLike.coe e)
    have h1 := LTSeries.length_le_krullDim (q.snoc Zt hlt')
    have h2 : ((d + 1 : ℕ) : WithBot ℕ∞) ≤ (d : WithBot ℕ∞) := by
      have e : (q.snoc Zt hlt').length = d + 1 := by simp [hql]
      rw [e] at h1
      exact h1.trans hS
    norm_cast at h2
    omega

theorem finite_of_topologicalKrullDim_nonpos (S : Type) [TopologicalSpace S] [NoetherianSpace S]
    [T0Space S] (h : topologicalKrullDim S ≤ 0) : Finite S := by
  have hm := Order.krullDim_nonpos_iff_forall_isMax.1 h
  have hcomp : ∀ x : S, closure ({x} : Set S) ∈ irreducibleComponents S := by
    intro x
    refine ⟨isIrreducible_singleton.closure, fun T hT hle => ?_⟩
    have := hm ⟨closure {x}, isIrreducible_singleton.closure, isClosed_closure⟩
      (b := ⟨closure T, hT.closure, isClosed_closure⟩) (fun y hy => subset_closure (hle hy))
    exact subset_closure.trans this
  haveI : Finite (irreducibleComponents S) :=
    NoetherianSpace.finite_irreducibleComponents.to_subtype
  exact Finite.of_injective (fun x => (⟨closure {x}, hcomp x⟩ : irreducibleComponents S))
    fun x y hxy => (inseparable_iff_closure_eq.2 (congrArg Subtype.val hxy)).eq

theorem dim_drop : ∀ (S : Type) [TopologicalSpace S] [NoetherianSpace S],
    (∀ (C : Set S) (d : ℕ), IsClosed C → topologicalKrullDim S ≤ d →
      (∀ Z ∈ irreducibleComponents S, (d : WithBot ℕ∞) ≤ topologicalKrullDim Z → ¬ Z ⊆ C) →
      topologicalKrullDim C < d) ∧
    (T0Space S → topologicalKrullDim S ≤ 0 → Finite S) := by
  intro S _ _
  exact ⟨fun C d hC hS hZ => topologicalKrullDim_lt_of_isClosed S C d hC hS hZ,
    fun _ h => finite_of_topologicalKrullDim_nonpos S h⟩

end GlobalTheory.DimDrop
