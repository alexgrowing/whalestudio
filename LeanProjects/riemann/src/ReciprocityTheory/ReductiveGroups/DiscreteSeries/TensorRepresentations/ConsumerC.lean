import ReciprocityTheory.ReductiveGroups.DiscreteSeries.HighestWeights.PieriRules.CartanKType
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.HighestWeights.PieriRules.ExpEntryHasDerivAt
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.HighestWeights.PieriRules.StdExpEntryHasDerivAt
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.HighestWeights.Unique
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.HighestWeights.PieriRules.TensRepB
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.HighestWeights.ContinuousRepresentations.URepCompRed
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.Bridge

noncomputable section

open Finset Matrix

namespace ReciprocityTheory.ChartRestriction.DS

variable {n : ℕ}

theorem cns_kType_iso {ε : Fin n → Bool} {Λ₁ Λ₂ : Fin n → ℝ} (h : Λ₁ = Λ₂) (T₁ : S7.KType ε Λ₁)
    (T₂ : S7.KType ε Λ₂) : ∃ φ : T₁.V ≃ₗᵢ[ℂ] T₂.V, ∀ k v, φ (T₁.op k v) = T₂.op k (φ v) := by
  subst h
  obtain ⟨φ, hφ, -⟩ := HW.kType_unique T₁ T₂
  exact ⟨φ, hφ⟩

theorem cns_kt_weight_eq {ε : Fin n → Bool} {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {Λ₁ Λ₂ : Fin n → ℝ} {S₁ : Submodule ℂ H}
    (h₁ : Formalism.MainNotions.S.IsKTypeOf ε σ Λ₁ S₁) (h₂ : Formalism.MainNotions.S.IsKTypeOf ε σ Λ₂ ⊤) : Λ₁ = Λ₂ := by
  obtain ⟨-, hst1, -, ⟨v1, hv1S, hv10, hv1w⟩, hdom1⟩ := h₁
  obtain ⟨-, -, hirr2, ⟨v2, -, hv20, hv2w⟩, hdom2⟩ := h₂
  have hS1 : S₁ = ⊤ := by
    rcases hirr2 S₁ le_top hst1 with h | h
    · rw [h] at hv1S
      exact absurd ((Submodule.mem_bot ℂ).1 hv1S) hv10
    · exact h
  have c1 : Formalism.MainNotions.S.CDom ε Λ₁ Λ₂ := hdom2 Λ₁ v1 Submodule.mem_top hv10 hv1w
  have c2 : Formalism.MainNotions.S.CDom ε Λ₂ Λ₁ := hdom1 Λ₂ v2 (hS1 ▸ Submodule.mem_top) hv20 hv2w
  exact cdom_antisymm ε c1 c2

theorem cns_cpt_dec {ε : Fin n → Bool} {Λ : Fin n → ℝ} (T : S7.KType ε Λ)
    (ρ : S7.KG ε →* unitary (Matrix (Fin n) (Fin n) ℂ))
    (dρ : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] Matrix (Fin n) (Fin n) ℂ)
    (hc : Continuous (fun k : S7.KG ε => ((ρ k : unitary (Matrix (Fin n) (Fin n) ℂ)) : Matrix (Fin n) (Fin n) ℂ)))
    (hd : ∀ X, inK ε X → ∀ γ : ℝ → S7.KG ε, (∀ t : ℝ, S7.toMK (γ t) = NormedSpace.exp ((t : ℂ) • X)) →
      ∀ i j, HasDerivAt (fun t : ℝ => ((ρ (γ t) : unitary (Matrix (Fin n) (Fin n) ℂ)) :
        Matrix (Fin n) (Fin n) ℂ) i j) (dρ X i j) 0)
    (γw : Fin n → Fin n → ℝ) (hinj : Function.Injective γw)
    (hP1 : ∀ (ν : Fin n → ℝ) (x : PiLp 2 (fun _ : Fin n => T.V)), x ≠ 0 →
      Formalism.REAL.KHighest ε (HW.tensAct (HW.kunits T) (fun a b => dρ (Matrix.single a b 1))) ν x →
      ∃ s, ν = Λ + γw s ∧ HW.KDom ε (Λ + γw s))
    (hP2 : ∀ s, Module.finrank ℂ (HW.khwSub ε (HW.tensAct (HW.kunits T) (fun a b => dρ (Matrix.single a b 1)))
      (Λ + γw s)) ≤ 1)
    (hP3 : ∀ s, HW.KDom ε (Λ + γw s) → ∃ x : PiLp 2 (fun _ : Fin n => T.V), x ≠ 0 ∧
      Formalism.REAL.KHighest ε (HW.tensAct (HW.kunits T) (fun a b => dρ (Matrix.single a b 1))) (Λ + γw s) x)
    (Sm : Finset (Fin n)) (hSm : ∀ s, s ∈ Sm ↔ HW.KDom ε (Λ + γw s))
    (Λs : Fin n → Fin n → ℝ) (hΛs : ∀ s ∈ Sm, Λs s = Λ + γw s) (Ts : ∀ s, S7.KType ε (Λs s)) :
    ∃ j : ∀ s, (Ts s).V →ₗ[ℂ] PiLp 2 (fun _ : Fin n => T.V),
      (∀ s ∈ Sm, ∀ v w, inner ℂ (j s v) (j s w) = inner ℂ v w) ∧
      (∀ s ∈ Sm, ∀ k v, j s ((Ts s).op k v) = HW.tensOp T ρ k (j s v)) ∧
      (∀ s ∈ Sm, ∀ s' ∈ Sm, s ≠ s' → ∀ v v', inner ℂ (j s v) (j s' v') = 0) ∧
      ∀ x, ∃ v : ∀ s, (Ts s).V, x = ∑ s ∈ Sm, j s (v s) := by
  classical
  let R : HW.KRep ε :=
    { V := PiLp 2 (fun _ : Fin n => T.V), τ := HW.tensTau T ρ, cont := HW.tensTau_cont T ρ hc,
      dτ := HW.tensD T dρ, hasDeriv := fun X hX γ hγ => HW.tensD_hasDeriv T ρ dρ hX γ hγ (hd X hX γ hγ) }
  have hRu : R.units = HW.tensAct (HW.kunits T) (fun a b => dρ (Matrix.single a b 1)) :=
    HW.tensKRep_units T ρ dρ hc hd
  have hRop : ∀ k, R.op k = HW.tensOp T ρ k := fun k => rfl
  obtain ⟨hrelR, hunitR⟩ := HW.kRepRel n ε R
  obtain ⟨m, x, μ, hx, horth, htop, -, -, hT⟩ := HW.compRed n ε R
  rw [hRu] at hrelR hunitR hx horth htop hT
  choose idx hidx hdom using fun i => hP1 (μ i) (x i) (hx i).1 (hx i).2
  have hidx_inj : Function.Injective idx := by
    intro i i' hii
    by_contra hne
    have hk : x i ∈ HW.khwSub ε (HW.tensAct (HW.kunits T) (fun a b => dρ (Matrix.single a b 1)))
        (Λ + γw (idx i)) := (HW.count_mem_khwSub_iff _ _ _ _).2 (by rw [← hidx i]; exact (hx i).2)
    have hk' : x i' ∈ HW.khwSub ε (HW.tensAct (HW.kunits T) (fun a b => dρ (Matrix.single a b 1)))
        (Λ + γw (idx i)) := (HW.count_mem_khwSub_iff _ _ _ _).2 (by rw [hii, ← hidx i']; exact (hx i').2)
    exact HW.count_not_two_of_finrank_le_one _ (hP2 (idx i)) hk hk' (hx i).1 (hx i').1
      (horth i i' hne _ (HW.count_mem_kSpan_self _ _ _) _ (HW.count_mem_kSpan_self _ _ _))
  have hpiece : ∀ (ν : Fin n → ℝ) (y : PiLp 2 (fun _ : Fin n => T.V)), y ≠ 0 →
      Formalism.REAL.KHighest ε (HW.tensAct (HW.kunits T) (fun a b => dρ (Matrix.single a b 1))) ν y →
      ∃ k, μ k = ν := by
    intro ν y hy0 hy
    by_contra hno
    push Not at hno
    apply hy0
    refine HW.count_eq_zero_of_orth _ htop y fun k z hz => ?_
    exact Formalism.REAL.kOrth _ n ε _ ν (μ k) y (x k) hrelR hunitR hy (hx k).2 (hno k).symm y
      (HW.count_mem_kSpan_self _ _ _) z hz
  have hsurj : ∀ s ∈ Sm, ∃ i, idx i = s := by
    intro s hs
    obtain ⟨y, hy0, hy⟩ := hP3 s ((hSm s).1 hs)
    obtain ⟨i, hi⟩ := hpiece _ y hy0 hy
    exact ⟨i, hinj (add_left_cancel ((hidx i).symm.trans hi))⟩
  have hmem : ∀ i, idx i ∈ Sm := fun i => (hSm _).2 (hdom i)
  have hj : ∀ s, ∃ js : (Ts s).V →ₗ[ℂ] PiLp 2 (fun _ : Fin n => T.V), s ∈ Sm → ∃ i, idx i = s ∧
      (∀ v, js v ∈ Formalism.REAL.kSpan ε (HW.tensAct (HW.kunits T) (fun a b => dρ (Matrix.single a b 1))) (x i)) ∧
      (∀ y ∈ Formalism.REAL.kSpan ε (HW.tensAct (HW.kunits T) (fun a b => dρ (Matrix.single a b 1))) (x i),
        ∃ v, js v = y) ∧
      (∀ v w, inner ℂ (js v) (js w) = inner ℂ v w) ∧
      (∀ k v, js ((Ts s).op k v) = HW.tensOp T ρ k (js v)) := by
    intro s
    by_cases hs : s ∈ Sm
    · obtain ⟨i, hi⟩ := hsurj s hs
      obtain ⟨Tk, φ, -, hφ, -, -⟩ := hT i
      obtain ⟨ψ, hψ⟩ := cns_kType_iso (show Λs s = μ i by rw [hΛs s hs, hidx i, hi]) (Ts s) Tk
      refine ⟨(Formalism.REAL.kSpan ε (HW.tensAct (HW.kunits T) (fun a b => dρ (Matrix.single a b 1))) (x i)).subtype
        ∘ₗ φ.toLinearEquiv.toLinearMap ∘ₗ ψ.toLinearEquiv.toLinearMap, fun _ => ⟨i, hi, ?_, ?_, ?_, ?_⟩⟩
      · intro v
        exact (φ (ψ v)).2
      · intro y hy
        refine ⟨ψ.symm (φ.symm ⟨y, hy⟩), ?_⟩
        show (φ (ψ (ψ.symm (φ.symm ⟨y, hy⟩)))).1 = y
        rw [LinearIsometryEquiv.apply_symm_apply, LinearIsometryEquiv.apply_symm_apply]
      · intro v w
        show inner ℂ (φ (ψ v)).1 (φ (ψ w)).1 =
          inner ℂ v w
        rw [← Submodule.coe_inner, LinearIsometryEquiv.inner_map_map, LinearIsometryEquiv.inner_map_map]
      · intro k v
        show (φ (ψ ((Ts s).op k v))).1 = HW.tensOp T ρ k (φ (ψ v)).1
        rw [hψ, hφ, hRop]
    · exact ⟨0, fun h => absurd h hs⟩
  choose j hj using hj
  refine ⟨j, fun s hs => (hj s hs).choose_spec.2.2.2.1, fun s hs => (hj s hs).choose_spec.2.2.2.2,
    fun s hs s' hs' hne v v' => ?_, fun y => ?_⟩
  · obtain ⟨i, hi, hin, -⟩ := hj s hs
    obtain ⟨i', hi', hin', -⟩ := hj s' hs'
    have hii : i ≠ i' := fun h => hne (hi.symm.trans (h ▸ hi'))
    exact horth i i' hii _ (hin v) _ (hin' v')
  · have hy : y ∈ ⨆ i ∈ (univ : Finset (Fin m)),
        Formalism.REAL.kSpan ε (HW.tensAct (HW.kunits T) (fun a b => dρ (Matrix.single a b 1))) (x i) := by
      have e : (⨆ i ∈ (univ : Finset (Fin m)),
          Formalism.REAL.kSpan ε (HW.tensAct (HW.kunits T) (fun a b => dρ (Matrix.single a b 1))) (x i)) =
          ⨆ i, Formalism.REAL.kSpan ε (HW.tensAct (HW.kunits T) (fun a b => dρ (Matrix.single a b 1))) (x i) := by
        simp
      rw [e, htop]
      exact Submodule.mem_top
    obtain ⟨μf, hμf⟩ := (Submodule.mem_iSup_finset_iff_exists_sum _ y).1 hy
    have hv : ∀ s, ∃ v : (Ts s).V, s ∈ Sm → ∀ i, idx i = s → j s v = (μf i : PiLp 2 (fun _ : Fin n => T.V)) := by
      intro s
      by_cases hs : s ∈ Sm
      · obtain ⟨i, hi, -, hsur, -⟩ := hj s hs
        obtain ⟨v, hv⟩ := hsur _ (μf i).2
        refine ⟨v, fun _ i' hi' => ?_⟩
        have : i' = i := hidx_inj (hi'.trans hi.symm)
        subst this
        exact hv
      · exact ⟨0, fun h => absurd h hs⟩
    choose v hv using hv
    refine ⟨v, ?_⟩
    rw [← hμf]
    exact Finset.sum_bij (fun a _ => idx a) (fun a _ => hmem a) (fun a _ b _ h => hidx_inj h)
      (fun b hb => let ⟨a, ha⟩ := hsurj b hb; ⟨a, mem_univ _, ha⟩)
      (fun a _ => (hv (idx a) (hmem a) a rfl).symm)

end ReciprocityTheory.ChartRestriction.DS
