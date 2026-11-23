import Formalism.SharpRestriction.GrowthBounds.RootWeights.CrCCommApply

noncomputable section

open Finset

namespace Formalism.MainNotions.G.GLWeightTheory

open Formalism.MainNotions.G Formalism.MainNotions.CovariantDegrees

attribute [local instance 100] LieRing.ofAssociativeRing

variable {n : ℕ} {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

def cr_WS (E : GLOps n K V) (S : Set (Fin n → ℤ)) : Submodule K V := ⨆ ν ∈ S, weightSp E ν

theorem cr_WS_mono (E : GLOps n K V) {S S' : Set (Fin n → ℤ)} (h : S ⊆ S') : cr_WS E S ≤ cr_WS E S' := by
  unfold cr_WS
  exact biSup_mono fun i hi => h hi

theorem cr_WS_of_mem (E : GLOps n K V) {S : Set (Fin n → ℤ)} {ν : Fin n → ℤ} (h : ν ∈ S) :
    weightSp E ν ≤ cr_WS E S := by
  unfold cr_WS
  exact le_iSup₂ (f := fun ν (_ : ν ∈ S) => weightSp E ν) ν h

theorem cr_wt_disj [CharZero K] (E : GLOps n K V) {ν ν' : Fin n → ℤ} (hne : ν ≠ ν') {x : V}
    (h1 : x ∈ weightSp E ν) (h2 : x ∈ weightSp E ν') : x = 0 := by
  obtain ⟨a, ha⟩ := Function.ne_iff.1 hne
  have e1 := (v2rep_mem_weightSp E ν x).1 h1 a
  have e2 := (v2rep_mem_weightSp E ν' x).1 h2 a
  have e3 : ((ν a : K) - (ν' a : K)) • x = 0 := by rw [sub_smul, ← e1, ← e2, sub_self]
  rcases smul_eq_zero.1 e3 with h | h
  · exact absurd (Int.cast_injective (sub_eq_zero.1 h)) ha
  · exact h

theorem cr_wt_diag_stable (E : GLOps n K V) (ν : Fin n → ℤ) (a : Fin n) (x : V) (hx : x ∈ weightSp E ν) :
    E a a x ∈ weightSp E ν := by
  rw [(v2rep_mem_weightSp E ν x).1 hx a]
  exact Submodule.smul_mem _ _ hx

theorem cr_WS_mem [CharZero K] (E : GLOps n K V) {S : Set (Fin n → ℤ)} {ν0 : Fin n → ℤ} {z : V}
    (hz : z ∈ cr_WS E S) (hz0 : z ∈ weightSp E ν0) (hne : z ≠ 0) : ν0 ∈ S := by
  classical
  obtain ⟨f, hf, rfl⟩ := (Submodule.mem_iSup_iff_exists_finsupp _ _).1 hz
  have hf' : ∀ ν, f ν ∈ weightSp E ν := fun ν => (iSup_le fun _ => le_rfl : (⨆ (_ : ν ∈ S), weightSp E ν) ≤ _) (hf ν)
  have h := v2rep_comp_mem E (weightSp E ν0) (fun a x hx => cr_wt_diag_stable E ν0 a x hx) f.support
    (fun ν => f ν) (fun ν _ => hf' ν) hz0
  have hsupp : ∀ ν ∈ f.support, ν = ν0 := by
    intro ν hν
    by_contra hh
    exact (Finsupp.mem_support_iff.1 hν) (cr_wt_disj E hh (hf' ν) (h ν hν))
  by_contra hS
  have h0 : f ν0 = 0 := by
    have := hf ν0
    simpa [hS] using this
  apply hne
  refine Finset.sum_eq_zero fun ν hν => ?_
  rw [hsupp ν hν]
  exact h0

def cr_Low (lam : Fin n → ℤ) : Set (Fin n → ℤ) := {ν | lam - ν ∈ cr_Pos n ∧ 0 < weightHeight' (lam - ν)}

def weightsBelow (lam : Fin n → ℤ) : Set (Fin n → ℤ) := {ν | lam - ν ∈ cr_Pos n}

theorem cr_Low_sub (lam : Fin n → ℤ) : cr_Low lam ⊆ weightsBelow lam := fun _ hν => hν.1

theorem cr_lower (E : GLOps n K V) (hR : SatisfiesGLRelations E) (lam : Fin n → ℤ) (a b : Fin n) (h : b < a) :
    cr_WS E (weightsBelow lam) ≤ (cr_WS E (cr_Low lam)).comap (E a b) := by
  refine iSup₂_le fun ν hν x hx => ?_
  show E a b x ∈ cr_WS E (cr_Low lam)
  refine cr_WS_of_mem E ?_ (v2rep_shift E hR a b ν x hx)
  have e : lam - (ν + rootW a b) = (lam - ν) + rootW b a := by
    ext c; simp only [rootW, Pi.sub_apply, Pi.add_apply]; ring
  refine ⟨?_, ?_⟩
  · rw [e]; exact add_mem hν (cr_root_mem b a h)
  · rw [e, cr_ht_add]
    have h1 := cr_Pos_ht hν
    have h2 := cr_ht_root b a h
    omega

theorem cr_Y_le (E : GLOps n K V) (hR : SatisfiesGLRelations E) (lam : Fin n → ℤ) (v : V) (hv : IsHWV E lam v) (k : ℕ) :
    cyclicLevelSubmodule E v k ≤ Submodule.span K {v} ⊔ cr_WS E (cr_Low lam) := by
  have hv0 : Submodule.span K {v} ⊔ cr_WS E (cr_Low lam) ≤ cr_WS E (weightsBelow lam) := by
    refine sup_le ?_ (cr_WS_mono E (cr_Low_sub lam))
    rw [Submodule.span_singleton_le_iff_mem]
    refine cr_WS_of_mem E ?_ hv.2.1
    show lam - lam ∈ cr_Pos n
    rw [sub_self]; exact zero_mem _
  induction k with
  | zero => exact le_sup_left
  | succ k ih =>
    refine sup_le ih ?_
    refine iSup_le fun ab => iSup_le fun hab => ?_
    rw [Submodule.map_le_iff_le_comap]
    refine (ih.trans hv0).trans ((cr_lower E hR lam ab.1 ab.2 hab).trans ?_)
    exact Submodule.comap_mono le_sup_right

theorem cr_isoIn_le (E : GLOps n K V) (hR : SatisfiesGLRelations E) (Wx : Submodule K V) (lam : Fin n → ℤ) :
    isotypicPartIn E Wx lam ≤ (Wx ⊓ weightSp E lam) ⊔ cr_WS E (cr_Low lam) := by
  refine Submodule.span_le.2 ?_
  rintro x ⟨u, hu, v, hvW, hv, rfl⟩
  obtain ⟨k, hk⟩ := v2rep_Umon_Y E hR lam v hv u hu 0 v (Submodule.mem_span_singleton_self v)
  have hle : Submodule.span K {v} ⊔ cr_WS E (cr_Low lam) ≤ (Wx ⊓ weightSp E lam) ⊔ cr_WS E (cr_Low lam) := by
    refine sup_le_sup_right ?_ _
    rw [Submodule.span_singleton_le_iff_mem]
    exact ⟨hvW, hv.2.1⟩
  exact hle (cr_Y_le E hR lam v hv k hk)

theorem isotypic_component_le_lower_weights (E : GLOps n K V) (hR : SatisfiesGLRelations E) (Wx : Submodule K V) (lam : Fin n → ℤ) :
    isotypicPartIn E Wx lam ≤ cr_WS E (weightsBelow lam) := by
  refine (cr_isoIn_le E hR Wx lam).trans (sup_le ?_ (cr_WS_mono E (cr_Low_sub lam)))
  refine inf_le_right.trans (cr_WS_of_mem E ?_)
  show lam - lam ∈ cr_Pos n
  rw [sub_self]; exact zero_mem _

theorem cr_dom [CharZero K] [FiniteDimensional K V] (E : GLOps n K V) (rel : SatisfiesGLRelations E) {mu : Fin n → ℤ} {v : V}
    (hne : v ≠ 0) (hv : v ∈ weightSp E mu) (a b : Fin n) (hab : a ≠ b) (he : E a b v = 0) : mu b ≤ mu a := by
  have hba : b ≠ a := hab.symm
  have hef : E a b * E b a - E b a * E a b = E a a - E b b := by
    have := rel a b b a
    simpa using this
  have h1 : E a a * E a b - E a b * E a a = E a b := by
    have := rel a a a b
    simpa [hba] using this
  have h2 : E b b * E a b - E a b * E b b = - E a b := by
    have := rel b b a b
    simpa [hba] using this
  have h3 : E a a * E b a - E b a * E a a = - E b a := by
    have := rel a a b a
    simpa [hab] using this
  have h4 : E b b * E b a - E b a * E b b = E b a := by
    have := rel b b b a
    simpa [hab] using this
  have hva : E a a v = (mu a : K) • v := (v2rep_mem_weightSp E mu v).1 hv a
  have hvb : E b b v = (mu b : K) • v := (v2rep_mem_weightSp E mu v).1 hv b
  have hhf : (E a a - E b b) * E b a - E b a * (E a a - E b b) = -(2 • E b a) := by
    have : (E a a - E b b) * E b a - E b a * (E a a - E b b) =
        (E a a * E b a - E b a * E a a) - (E b b * E b a - E b a * E b b) := by noncomm_ring
    rw [this, h3, h4, two_smul]; abel
  have hhe : (E a a - E b b) * E a b - E a b * (E a a - E b b) = 2 • E a b := by
    have : (E a a - E b b) * E a b - E a b * (E a a - E b b) =
        (E a a * E a b - E a b * E a a) - (E b b * E a b - E a b * E b b) := by noncomm_ring
    rw [this, h1, h2, two_smul]; abel
  have hhv : (E a a - E b b) v = ((mu a : K) - (mu b : K)) • v := by
    rw [LinearMap.sub_apply, hva, hvb, sub_smul]
  by_cases hh0 : E a a - E b b = 0
  · rw [hh0, LinearMap.zero_apply] at hhv
    rcases smul_eq_zero.1 hhv.symm with h | h
    · exact (Int.cast_injective (sub_eq_zero.1 h)).ge
    · exact absurd h hne
  have t : IsSl2Triple (E a a - E b b) (E a b) (E b a) :=
    { h_ne_zero := hh0
      lie_e_f := by rw [Ring.lie_def]; exact hef
      lie_h_e_nsmul := by rw [Ring.lie_def]; exact hhe
      lie_h_f_nsmul := by rw [Ring.lie_def]; exact hhf }
  have P : t.HasPrimitiveVectorWith v ((mu a : K) - (mu b : K)) :=
    { ne_zero := hne
      lie_h := by rw [Module.End.lie_apply]; exact hhv
      lie_e := by rw [Module.End.lie_apply]; exact he }
  obtain ⟨m, hm⟩ := P.exists_nat
  have : ((mu a - mu b : ℤ) : K) = ((m : ℤ) : K) := by push_cast; exact hm
  have := Int.cast_injective this
  omega

theorem cr_hwv_dom [CharZero K] [FiniteDimensional K V] (E : GLOps n K V) (rel : SatisfiesGLRelations E) {mu : Fin n → ℤ} {v : V}
    (hv : IsHWV E mu v) : Dominant mu := by
  intro a b hab
  rcases hab.lt_or_eq with h | h
  · exact cr_dom E rel hv.1 hv.2.1 a b h.ne (hv.2.2 a b h)
  · rw [h]

theorem cr_isoIn_dom [CharZero K] [FiniteDimensional K V] (E : GLOps n K V) (rel : SatisfiesGLRelations E) (Wx : Submodule K V)
    {mu : Fin n → ℤ} {x : V} (hx : x ∈ isotypicPartIn E Wx mu) (hne : x ≠ 0) : Dominant mu := by
  by_contra hd
  apply hne
  have : isotypicPartIn E Wx mu = ⊥ := by
    rw [isotypicPartIn, Submodule.span_eq_bot]
    rintro y ⟨u, _, v, _, hv, rfl⟩
    exact absurd (cr_hwv_dom E rel hv) hd
  rw [this] at hx
  exact (Submodule.mem_bot K).1 hx

end Formalism.MainNotions.G.GLWeightTheory
