import Formalism.SharpRestriction.GrowthBounds.RootWeights.IsotypicProjectorFixedMem
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.IsotypicStableUnderOperators

noncomputable section

open Finset

namespace Formalism.MainNotions.G.GLWeightTheory

open Formalism.MainNotions.G Formalism.MainNotions.CovariantDegrees

section

variable {n : ℕ} {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

theorem mem_weightSpace_iff_diagonal (E : GLOps n K V) (mu : Fin n → ℤ) (x : V) :
    x ∈ weightSp E mu ↔ ∀ a, E a a x = (mu a : K) • x := by
  simp [weightSp, Submodule.mem_iInf, LinearMap.mem_ker, sub_eq_zero]

theorem weightSpace_disjoint [CharZero K] (E : GLOps n K V) {mu ka : Fin n → ℤ} (h : mu ≠ ka) {x : V}
    (h1 : x ∈ weightSp E mu) (h2 : x ∈ weightSp E ka) : x = 0 := by
  obtain ⟨a, ha⟩ := Function.ne_iff.1 h
  have e1 := (mem_weightSpace_iff_diagonal E mu x).1 h1 a
  have e2 := (mem_weightSpace_iff_diagonal E ka x).1 h2 a
  rw [e1] at e2
  have e3 : ((mu a : K) - (ka a : K)) • x = 0 := by rw [sub_smul, e2, sub_self]
  rcases smul_eq_zero.1 e3 with h0 | h0
  · exact absurd (by exact_mod_cast sub_eq_zero.1 h0) ha
  · exact h0

open Classical in

def lagrangeFactor (E : GLOps n K V) (mu nu : Fin n → ℤ) : Module.End K V :=
  if h : nu = mu then 1 else
    (((mu (Classical.choose (Function.ne_iff.1 h)) : K) - (nu (Classical.choose (Function.ne_iff.1 h)) : K))⁻¹) •
      (E (Classical.choose (Function.ne_iff.1 h)) (Classical.choose (Function.ne_iff.1 h)) -
        (nu (Classical.choose (Function.ne_iff.1 h)) : K) • (1 : Module.End K V))

theorem lagrange_factor_acts_scalar (E : GLOps n K V) (mu nu ka : Fin n → ℤ) {x : V} (hx : x ∈ weightSp E ka) :
    ∃ c : K, lagrangeFactor E mu nu x = c • x := by
  unfold lagrangeFactor
  split_ifs with h
  · exact ⟨1, by simp⟩
  · set a := Classical.choose (Function.ne_iff.1 h)
    refine ⟨((mu a : K) - (nu a : K))⁻¹ * ((ka a : K) - (nu a : K)), ?_⟩
    simp only [LinearMap.smul_apply, LinearMap.sub_apply, Module.End.one_apply]
    rw [(mem_weightSpace_iff_diagonal E ka x).1 hx a, ← sub_smul, smul_smul]

theorem lagrange_factor_fixes_weight [CharZero K] (E : GLOps n K V) (mu nu : Fin n → ℤ) {x : V} (hx : x ∈ weightSp E mu) :
    lagrangeFactor E mu nu x = x := by
  unfold lagrangeFactor
  split_ifs with h
  · simp
  · have ha := Classical.choose_spec (Function.ne_iff.1 h)
    set a := Classical.choose (Function.ne_iff.1 h)
    simp only [LinearMap.smul_apply, LinearMap.sub_apply, Module.End.one_apply]
    rw [(mem_weightSpace_iff_diagonal E mu x).1 hx a, ← sub_smul, smul_smul, inv_mul_cancel₀, one_smul]
    intro h0
    exact ha (by exact_mod_cast (sub_eq_zero.1 h0).symm)

theorem lagrange_factor_kills_other (E : GLOps n K V) {mu nu : Fin n → ℤ} (h : nu ≠ mu) {x : V} (hx : x ∈ weightSp E nu) :
    lagrangeFactor E mu nu x = 0 := by
  unfold lagrangeFactor
  rw [dif_neg h]
  set a := Classical.choose (Function.ne_iff.1 h)
  simp only [LinearMap.smul_apply, LinearMap.sub_apply, Module.End.one_apply]
  rw [(mem_weightSpace_iff_diagonal E nu x).1 hx a, sub_self, smul_zero]

theorem lagrange_factor_preserves_stable (E : GLOps n K V) (mu nu : Fin n → ℤ) (U : Submodule K V)
    (hU : ∀ a, ∀ x ∈ U, E a a x ∈ U) {x : V} (hx : x ∈ U) : lagrangeFactor E mu nu x ∈ U := by
  unfold lagrangeFactor
  split_ifs with h
  · simpa using hx
  · simp only [LinearMap.smul_apply, LinearMap.sub_apply, Module.End.one_apply]
    exact U.smul_mem _ (U.sub_mem (hU _ x hx) (U.smul_mem _ hx))

def lagrangeProjector (E : GLOps n K V) (mu : Fin n → ℤ) (L : List (Fin n → ℤ)) : Module.End K V :=
  (L.map fun nu => lagrangeFactor E mu nu).prod

theorem lagrange_projector_acts_scalar (E : GLOps n K V) (mu ka : Fin n → ℤ) (L : List (Fin n → ℤ)) {x : V}
    (hx : x ∈ weightSp E ka) : ∃ c : K, lagrangeProjector E mu L x = c • x := by
  induction L with
  | nil => exact ⟨1, by simp [lagrangeProjector]⟩
  | cons nu L ih =>
    obtain ⟨c, hc⟩ := ih
    obtain ⟨d, hd⟩ := lagrange_factor_acts_scalar E mu nu ka hx
    refine ⟨c * d, ?_⟩
    have : lagrangeProjector E mu (nu :: L) x = lagrangeFactor E mu nu (lagrangeProjector E mu L x) := by
      simp [lagrangeProjector, Module.End.mul_apply]
    rw [this, hc, map_smul, hd, smul_smul]

theorem lagrange_projector_fixes_weight [CharZero K] (E : GLOps n K V) (mu : Fin n → ℤ) (L : List (Fin n → ℤ)) {x : V}
    (hx : x ∈ weightSp E mu) : lagrangeProjector E mu L x = x := by
  induction L with
  | nil => simp [lagrangeProjector]
  | cons nu L ih =>
    have : lagrangeProjector E mu (nu :: L) x = lagrangeFactor E mu nu (lagrangeProjector E mu L x) := by
      simp [lagrangeProjector, Module.End.mul_apply]
    rw [this, ih, lagrange_factor_fixes_weight E mu nu hx]

theorem lagrange_projector_kills_other (E : GLOps n K V) {mu ka : Fin n → ℤ} (h : ka ≠ mu) (L : List (Fin n → ℤ)) (hL : ka ∈ L)
    {x : V} (hx : x ∈ weightSp E ka) : lagrangeProjector E mu L x = 0 := by
  induction L with
  | nil => simp at hL
  | cons nu L ih =>
    have e : lagrangeProjector E mu (nu :: L) x = lagrangeFactor E mu nu (lagrangeProjector E mu L x) := by
      simp [lagrangeProjector, Module.End.mul_apply]
    rw [e]
    rcases List.mem_cons.1 hL with rfl | hL'
    · obtain ⟨c, hc⟩ := lagrange_projector_acts_scalar E mu ka L hx
      rw [hc, map_smul, lagrange_factor_kills_other E h hx, smul_zero]
    · rw [ih hL', map_zero]

theorem lagrange_projector_preserves_stable (E : GLOps n K V) (mu : Fin n → ℤ) (L : List (Fin n → ℤ)) (U : Submodule K V)
    (hU : ∀ a, ∀ x ∈ U, E a a x ∈ U) {x : V} (hx : x ∈ U) : lagrangeProjector E mu L x ∈ U := by
  induction L with
  | nil => simpa [lagrangeProjector] using hx
  | cons nu L ih =>
    have e : lagrangeProjector E mu (nu :: L) x = lagrangeFactor E mu nu (lagrangeProjector E mu L x) := by
      simp [lagrangeProjector, Module.End.mul_apply]
    rw [e]
    exact lagrange_factor_preserves_stable E mu nu U hU ih

end

section

variable {n : ℕ} {K V : Type*} [Field K] [CharZero K] [AddCommGroup V] [Module K V]

theorem sum_lagrange_projectors_eq_self (E : GLOps n K V) (t : Finset (Fin n → ℤ))
    (ht : (⊤ : Submodule K V) ≤ ⨆ mu ∈ t, weightSp E mu) (x : V) :
    ∑ mu ∈ t, lagrangeProjector E mu t.toList x = x := by
  have hx : x ∈ ⨆ mu ∈ t, weightSp E mu := ht Submodule.mem_top
  refine Submodule.iSup_induction (fun mu => ⨆ (_ : mu ∈ t), weightSp E mu)
    (motive := fun x => ∑ mu ∈ t, lagrangeProjector E mu t.toList x = x) hx ?_ ?_ ?_
  · intro ka y hy
    by_cases hk : ka ∈ t
    · have hy' : y ∈ weightSp E ka := by simpa [hk] using hy
      rw [Finset.sum_eq_single ka]
      · exact lagrange_projector_fixes_weight E ka _ hy'
      · intro mu _ hne
        exact lagrange_projector_kills_other E (Ne.symm hne) _ (by simpa using hk) hy'
      · intro h; exact absurd hk h
    · have : y = 0 := by simpa [hk] using hy
      simp [this]
  · simp
  · intro y z hy hz
    simp only [map_add, Finset.sum_add_distrib, hy, hz]

theorem lagrange_projector_mem_weightSpace (E : GLOps n K V) (t : Finset (Fin n → ℤ))
    (ht : (⊤ : Submodule K V) ≤ ⨆ mu ∈ t, weightSp E mu) (mu : Fin n → ℤ) (x : V) :
    lagrangeProjector E mu t.toList x ∈ weightSp E mu := by
  have hx : x ∈ ⨆ mu ∈ t, weightSp E mu := ht Submodule.mem_top
  refine Submodule.iSup_induction (fun mu => ⨆ (_ : mu ∈ t), weightSp E mu)
    (motive := fun x => lagrangeProjector E mu t.toList x ∈ weightSp E mu) hx ?_ ?_ ?_
  · intro ka y hy
    by_cases hk : ka ∈ t
    · have hy' : y ∈ weightSp E ka := by simpa [hk] using hy
      by_cases hkm : ka = mu
      · subst hkm
        rw [lagrange_projector_fixes_weight E ka _ hy']; exact hy'
      · rw [lagrange_projector_kills_other E hkm _ (by simpa using hk) hy']; exact Submodule.zero_mem _
    · have : y = 0 := by simpa [hk] using hy
      simp [this]
  · simp
  · intro y z hy hz
    rw [map_add]; exact Submodule.add_mem _ hy hz

theorem nonzero_weight_mem_support (E : GLOps n K V) (t : Finset (Fin n → ℤ))
    (ht : (⊤ : Submodule K V) ≤ ⨆ mu ∈ t, weightSp E mu) {ka : Fin n → ℤ} {y : V}
    (hy : y ∈ weightSp E ka) (h0 : y ≠ 0) : ka ∈ t := by
  by_contra hk
  apply h0
  rw [← sum_lagrange_projectors_eq_self E t ht y]
  apply Finset.sum_eq_zero
  intro mu hmu
  obtain ⟨c, hc⟩ := lagrange_projector_acts_scalar E mu ka t.toList hy
  have h1 := lagrange_projector_mem_weightSpace E t ht mu y
  have h2 : lagrangeProjector E mu t.toList y ∈ weightSp E ka := by rw [hc]; exact Submodule.smul_mem _ _ hy
  exact weightSpace_disjoint E (by rintro rfl; exact hk hmu) h1 h2

theorem stable_subspace_has_weight_vector (E : GLOps n K V) (t : Finset (Fin n → ℤ))
    (ht : (⊤ : Submodule K V) ≤ ⨆ mu ∈ t, weightSp E mu) (U : Submodule K V)
    (hU : ∀ a, ∀ x ∈ U, E a a x ∈ U) (hne : U ≠ ⊥) :
    ∃ mu ∈ t, ∃ x ∈ U, x ≠ 0 ∧ x ∈ weightSp E mu := by
  obtain ⟨x, hx, h0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  by_contra hcon
  push Not at hcon
  apply h0
  rw [← sum_lagrange_projectors_eq_self E t ht x]
  apply Finset.sum_eq_zero
  intro mu hmu
  by_contra hP
  exact hcon mu hmu _ (lagrange_projector_preserves_stable E mu _ U hU hx) hP (lagrange_projector_mem_weightSpace E t ht mu x)

omit [CharZero K] in
theorem raising_shifts_weight_by_root (E : GLOps n K V)
    (hrel : ∀ a b c d, E a b * E c d - E c d * E a b = (if b = c then E a d else 0) - (if d = a then E c b else 0))
    {a b : Fin n} (hab : a ≠ b) {mu : Fin n → ℤ} {x : V} (hx : x ∈ weightSp E mu) :
    E a b x ∈ weightSp E (mu + rootW a b) := by
  rw [mem_weightSpace_iff_diagonal] at hx ⊢
  intro c
  have h := congrArg (fun f : Module.End K V => f x) (hrel c c a b)
  simp only [LinearMap.sub_apply, Module.End.mul_apply] at h
  rw [hx c, map_smul, sub_eq_iff_eq_add] at h
  rw [h]
  by_cases hca : c = a
  · subst hca
    have hbc : ¬ b = c := fun h => hab h.symm
    simp only [if_true, if_neg hbc, LinearMap.zero_apply, sub_zero, rootW, Pi.add_apply, Pi.sub_apply,
      Pi.single_eq_same, Pi.single_eq_of_ne hab]
    push_cast
    rw [add_smul, one_smul, add_comm]
  · by_cases hcb : c = b
    · subst hcb
      simp only [if_neg hca, if_true, LinearMap.zero_apply, zero_sub, rootW, Pi.add_apply, Pi.sub_apply,
        Pi.single_eq_same, Pi.single_eq_of_ne hca]
      push_cast
      rw [add_smul, neg_smul, one_smul, add_comm]
    · have hbc : ¬ b = c := fun h => hcb h.symm
      simp only [if_neg hca, if_neg hbc, LinearMap.zero_apply, sub_zero, rootW, Pi.add_apply, Pi.sub_apply,
        Pi.single_eq_of_ne hca, Pi.single_eq_of_ne hcb, zero_add, add_zero]

def weightHeight (mu : Fin n → ℤ) : ℤ := ∑ c : Fin n, ((c : ℕ) : ℤ) * mu c

theorem weightHeight_add_root (mu : Fin n → ℤ) (a b : Fin n) :
    weightHeight (mu + rootW a b) = weightHeight mu + ((a : ℕ) : ℤ) - ((b : ℕ) : ℤ) := by
  simp [weightHeight, rootW, mul_add, mul_sub, Finset.sum_add_distrib, Finset.sum_sub_distrib, Pi.single_apply]
  ring

theorem exists_highest_weight_vector (E : GLOps n K V)
    (hrel : ∀ a b c d, E a b * E c d - E c d * E a b = (if b = c then E a d else 0) - (if d = a then E c b else 0))
    (t : Finset (Fin n → ℤ)) (ht : (⊤ : Submodule K V) ≤ ⨆ mu ∈ t, weightSp E mu) (U : Submodule K V)
    (hU : ∀ a b, ∀ x ∈ U, E a b x ∈ U) (hne : U ≠ ⊥) : ∃ mu, ∃ x ∈ U, IsHWV E mu x := by
  classical
  have hT : (t.filter (fun mu => ∃ x ∈ U, x ≠ 0 ∧ x ∈ weightSp E mu)).Nonempty := by
    obtain ⟨mu, hmu, h⟩ := stable_subspace_has_weight_vector E t ht U (fun a => hU a a) hne
    exact ⟨mu, Finset.mem_filter.2 ⟨hmu, h⟩⟩
  obtain ⟨mu, hmu, hmin⟩ := Finset.exists_min_image _ weightHeight hT
  obtain ⟨_, x, hxU, hx0, hxw⟩ := Finset.mem_filter.1 hmu
  refine ⟨mu, x, hxU, hx0, hxw, fun a b hab => ?_⟩
  by_contra hy
  have hw := raising_shifts_weight_by_root E hrel (ne_of_lt hab) hxw
  have hin := nonzero_weight_mem_support E t ht hw hy
  have h1 := hmin _ (Finset.mem_filter.2 ⟨hin, _, hU a b x hxU, hy, hw⟩)
  rw [weightHeight_add_root] at h1
  have h2 : ((a : ℕ) : ℤ) < ((b : ℕ) : ℤ) := by exact_mod_cast hab
  omega

omit [CharZero K] in
theorem isotypic_stable_under_operators (E : GLOps n K V) (mu : Fin n → ℤ) (a b : Fin n) {x : V} (hx : x ∈ isoSub E mu) :
    E a b x ∈ isoSub E mu := by
  first | exact UpperTheory.Reformulated.B.Qf30.isotypic_stable_under_operators .. | (apply UpperTheory.Reformulated.B.Qf30.isotypic_stable_under_operators <;> assumption) | (intros; apply UpperTheory.Reformulated.B.Qf30.isotypic_stable_under_operators <;> assumption) | (apply @UpperTheory.Reformulated.B.Qf30.isotypic_stable_under_operators <;> assumption) | (intros; apply @UpperTheory.Reformulated.B.Qf30.isotypic_stable_under_operators <;> assumption) | (apply @UpperTheory.Reformulated.B.Qf30.isotypic_stable_under_operators <;> first | assumption | infer_instance) | exact @UpperTheory.Reformulated.B.Qf30.isotypic_stable_under_operators n K V ‹_› ‹_› ‹_› E mu a b x hx | exact @UpperTheory.Reformulated.B.Qf30.isotypic_stable_under_operators n K V ‹_› ‹_› ‹_› E mu a b x | exact @UpperTheory.Reformulated.B.Qf30.isotypic_stable_under_operators n K V ‹_› ‹_› ‹_› E mu a b | exact @UpperTheory.Reformulated.B.Qf30.isotypic_stable_under_operators n K V ‹_› ‹_› ‹_› E mu a | exact @UpperTheory.Reformulated.B.Qf30.isotypic_stable_under_operators n K V ‹_› ‹_› ‹_› E mu | exact @UpperTheory.Reformulated.B.Qf30.isotypic_stable_under_operators n K V ‹_› ‹_› ‹_› E | exact @UpperTheory.Reformulated.B.Qf30.isotypic_stable_under_operators n K V ‹_› ‹_› ‹_› | exact @UpperTheory.Reformulated.B.Qf30.isotypic_stable_under_operators n K V ‹_› ‹_› | exact @UpperTheory.Reformulated.B.Qf30.isotypic_stable_under_operators n K V ‹_› | exact @UpperTheory.Reformulated.B.Qf30.isotypic_stable_under_operators n K V | exact @UpperTheory.Reformulated.B.Qf30.isotypic_stable_under_operators n K | exact @UpperTheory.Reformulated.B.Qf30.isotypic_stable_under_operators n

end

theorem isotypic_subspaces_span_top (D : Formalism.BasicNotions.D7) (h2 : adm2 D) (K V : Type) [Field K] [CharZero K] [AddCommGroup V]
    [Module K V] [FiniteDimensional K V] (n : ℕ) (E : GLOps n K V) (hE : IsGLRep E) :
    (⨆ mu : Fin n → ℤ, isoSub E mu) = ⊤ := by
  obtain ⟨hrel, _, hw⟩ := hE
  have hst : ∀ a b, ∀ x ∈ (⨆ mu : Fin n → ℤ, isoSub E mu), E a b x ∈ (⨆ mu : Fin n → ℤ, isoSub E mu) := by
    intro a b x hx
    refine Submodule.iSup_induction (fun mu => isoSub E mu)
      (motive := fun x => E a b x ∈ (⨆ mu : Fin n → ℤ, isoSub E mu)) hx ?_ ?_ ?_
    · intro mu y hy
      exact Submodule.mem_iSup_of_mem mu (isotypic_stable_under_operators E mu a b hy)
    · simp
    · intro y z hy hz
      rw [map_add]; exact Submodule.add_mem _ hy hz
  obtain ⟨W', hc, hW'⟩ := h2 K V n E ⟨hrel, ‹_›, hw⟩ _ hst
  obtain ⟨t, ht⟩ := CompleteLattice.IsCompactElement.exists_finset_of_le_iSup (Submodule K V)
    ((Submodule.fg_iff_compact (⊤ : Submodule K V)).1 Module.Finite.fg_top)
    (fun mu => weightSp E mu) (le_of_eq hw.symm)
  have hbot : W' = ⊥ := by
    by_contra hne
    obtain ⟨mu, x, hxW, hx⟩ := exists_highest_weight_vector E hrel t ht W' hW' hne
    have h1 : x ∈ (⨆ mu : Fin n → ℤ, isoSub E mu) :=
      Submodule.mem_iSup_of_mem mu (Submodule.subset_span ⟨1, Submonoid.one_mem _, x, hx, rfl⟩)
    have h0 : x ∈ (⨆ mu : Fin n → ℤ, isoSub E mu) ⊓ W' := ⟨h1, hxW⟩
    rw [hc.inf_eq_bot] at h0
    exact hx.1 (by simpa using h0)
  have := hc.sup_eq_top
  rwa [hbot, sup_bot_eq] at this

theorem isotypic_projector_fixed_mem (D : Formalism.BasicNotions.D7) (h2 : adm2 D) : IsotypicProjectorFixedMem := by
  intro K V _ _ _ _ _ n E hE lam e he Y hY
  have hY' : Y ∈ (⨆ mu : Fin n → ℤ, isoSub E mu) := by
    rw [isotypic_subspaces_span_top D h2 K V n E hE]; exact Submodule.mem_top
  rw [← hY]
  refine Submodule.iSup_induction (fun mu => isoSub E mu) (motive := fun y => e y ∈ isoSub E lam) hY' ?_ ?_ ?_
  · intro mu y hy
    by_cases hm : mu = lam
    · subst hm
      rw [he.1 y hy]; exact hy
    · rw [he.2 mu hm y hy]; exact Submodule.zero_mem _
  · simp
  · intro y z hy hz
    rw [map_add]; exact Submodule.add_mem _ hy hz

end Formalism.MainNotions.G.GLWeightTheory
