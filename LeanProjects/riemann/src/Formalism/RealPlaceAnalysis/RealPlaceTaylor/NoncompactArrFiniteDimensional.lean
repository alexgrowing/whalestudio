import Formalism.RealPlaceAnalysis.StatementU
import Formalism.RealPlaceAnalysis.ThirdArithmeticHolds

open scoped InnerProductSpace
open Finset

noncomputable section

namespace Formalism.REAL

section U2
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] {n : ℕ}

theorem fin_one_update_eq_const (α : Fin 1 → Fin n × Fin n) (x : Fin n × Fin n) :
    Function.update α 0 x = fun _ => x := by
  funext i; rw [Fin.fin_one_eq_zero i]; simp

theorem fin_one_fun_eq_const_apply_zero (α : Fin 1 → Fin n × Fin n) : α = fun _ => α 0 := by
  funext i; rw [Fin.fin_one_eq_zero i]

theorem factorAction_apply_general {j : ℕ} (i : Fin j) (c d : Fin n) (F : Arr V n j) (α : Fin j → Fin n × Fin n) :
    factorAction i c d F α = (if (α i).1 = c then F (Function.update α i (d, (α i).2)) else 0) -
      (if (α i).2 = d then F (Function.update α i ((α i).1, c)) else 0) := by
  simp only [factorAction, arrTo, arrOf, LinearMap.comp_apply, LinearEquiv.coe_coe]
  by_cases h1 : (α i).1 = c <;> by_cases h2 : (α i).2 = d <;> simp [h1, h2]

theorem pointwise_operator_apply_general {j : ℕ} (E : Fin n → Fin n → Module.End ℂ V) (c d : Fin n) (F : Arr V n j)
    (α : Fin j → Fin n × Fin n) : ptE E c d F α = E c d (F α) := by
  simp [ptE, arrTo, arrOf]

theorem arr_operator_one_apply (E : Fin n → Fin n → Module.End ℂ V) (c d : Fin n) (F : Arr V n 1)
    (a b : Fin n) :
    arrE E 1 c d F (fun _ => (a, b)) =
      ((if a = c then F (fun _ => (d, b)) else 0) - (if b = d then F (fun _ => (a, c)) else 0))
        + E c d (F (fun _ => (a, b))) := by
  simp only [arrE, LinearMap.add_apply, Fin.sum_univ_one, PiLp.add_apply, factorAction_apply_general,
    pointwise_operator_apply_general, fin_one_update_eq_const]

theorem mem_noncompact_arr_iff_general {ε : Fin n → Bool} {E : Fin n → Fin n → Module.End ℂ V} {u : V} {j : ℕ}
    (F : Arr V n j) :
    F ∈ arrV0 ε E u j ↔ ∀ α, F α ∈ (if ∀ i, ε (α i).1 ≠ ε (α i).2 then kSpan ε E u else ⊥) := by
  simp [arrV0, arrOf]

theorem noncompact_arr_one_values {ε : Fin n → Bool} {E : Fin n → Fin n → Module.End ℂ V} {u : V} {F : Arr V n 1}
    (hF : F ∈ arrV0 ε E u 1) (a b : Fin n) :
    (ε a ≠ ε b → F (fun _ => (a, b)) ∈ kSpan ε E u) ∧ (ε a = ε b → F (fun _ => (a, b)) = 0) := by
  have h := (mem_noncompact_arr_iff_general F).mp hF (fun _ => (a, b))
  constructor
  · intro hne
    rwa [if_pos (fun _ => hne)] at h
  · intro he
    rw [if_neg (fun h' => h' 0 he), Submodule.mem_bot] at h
    exact h

theorem mem_noncompact_arr_one {ε : Fin n → Bool} {E : Fin n → Fin n → Module.End ℂ V} {u : V} {F : Arr V n 1}
    (h1 : ∀ a b, ε a ≠ ε b → F (fun _ => (a, b)) ∈ kSpan ε E u)
    (h2 : ∀ a b, ε a = ε b → F (fun _ => (a, b)) = 0) : F ∈ arrV0 ε E u 1 := by
  rw [mem_noncompact_arr_iff_general]
  intro α
  rw [fin_one_fun_eq_const_apply_zero α]
  by_cases h : ε (α 0).1 = ε (α 0).2
  · rw [if_neg (fun h' => h' 0 h), Submodule.mem_bot]; exact h2 _ _ h
  · rw [if_pos (fun _ => h)]; exact h1 _ _ h

theorem compact_highest_weight_unique (hl : KLow) (hw : KWtOrth) {ε : Fin n → Bool}
    {E : Fin n → Fin n → Module.End ℂ V} {Λ ν : Fin n → ℝ} {u y : V}
    (hg : GlRel E) (hu : IsUnitary ε E) (hΛ : KHighest ε E Λ u) (hy : y ∈ kSpan ε E u)
    (hyh : KHighest ε E ν y) (hy0 : y ≠ 0) : ν = Λ := by
  by_contra hne
  have hk := isUnitary_kUnit ε E hu
  obtain ⟨hspan, -⟩ := hl V n ε E Λ u (glRel_kRel ε E hg) hΛ
  rw [hspan] at hy
  have key : ∀ z ∈ lowSpan ε E u, ⟪z, y⟫_ℂ = 0 := by
    intro z hz
    induction hz using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨w, hw', rfl⟩ := hx
      cases w with
      | nil => simpa [ew] using hw V n ε E Λ ν u y hk hΛ.1 hyh.1 (Ne.symm hne)
      | cons p w =>
        have hp := hw' p (List.mem_cons_self ..)
        simp only [ew, Module.End.mul_apply]
        rw [hk p.1 p.2 hp.1, hyh.2 p.2 p.1 hp.2 hp.1.symm, inner_zero_right]
    | zero => simp
    | add x z _ _ hx hz => rw [inner_add_left, hx, hz, add_zero]
    | smul c x _ hx => rw [inner_smul_left, hx, mul_zero]
  exact hy0 (inner_self_eq_zero.mp (key y hy))

end U2

section U2b
theorem hVCoeff_of (hl : KLow) (hw : KWtOrth) (ha : ArrModule) : HVCoeff := by
  intro V _ _ n ε E Λ μ u F hg hu hΛ hF hFh hF0
  classical
  set f : Fin n × Fin n → V := fun p => F (fun _ => p) with hf
  have hnz : ∃ p, f p ≠ 0 := by
    by_contra h
    push Not at h
    apply hF0
    apply PiLp.ext
    intro α
    rw [fin_one_fun_eq_const_apply_zero α]
    simpa [hf] using h (α 0)
  obtain ⟨⟨a, b⟩, hpP, hmax⟩ := (univ.filter (fun p => f p ≠ 0)).exists_max_image
    (fun p : Fin n × Fin n => ((p.1 : ℕ) : ℤ) - ((p.2 : ℕ) : ℤ))
    (by obtain ⟨p, hp⟩ := hnz; exact ⟨p, by simp [hp]⟩)
  have hzero : ∀ q : Fin n × Fin n, ((a : ℕ) : ℤ) - ((b : ℕ) : ℤ) < ((q.1 : ℕ) : ℤ) - ((q.2 : ℕ) : ℤ) →
      f q = 0 := by
    intro q hq
    by_contra h
    have := hmax q (by simp [h])
    simp only at this
    omega
  have hab0 : f (a, b) ≠ 0 := by simpa using hpP
  have hval := noncompact_arr_one_values hF
  have hne : ε a ≠ ε b := fun h => hab0 ((hval a b).2 h)
  have hab : a ≠ b := fun h => hne (h ▸ rfl)
  refine ⟨a, b, hne, ?_⟩
  have hwt : IsWeight E (μ - root a b) (f (a, b)) := by
    intro c
    have h1 := congrArg (fun G : Arr V n 1 => G (fun _ => (a, b))) (hFh.1 c)
    simp only at h1
    rw [arr_operator_one_apply, PiLp.smul_apply] at h1
    by_cases hac : a = c
    · subst hac
      have hbc : b ≠ a := Ne.symm hab
      simp only [if_true, if_neg hbc, sub_zero] at h1
      have : ((μ - root a b) a : ℝ) = μ a - 1 := by
        simp [root, Pi.single_apply, hbc]
      rw [this]
      push_cast
      rw [sub_smul, one_smul, ← h1]
      simp [hf]
    · by_cases hbc : b = c
      · subst hbc
        simp only [if_neg hac, if_true, zero_sub] at h1
        have : ((μ - root a b) b : ℝ) = μ b + 1 := by
          simp [root, Pi.single_apply, hab]
        rw [this]
        push_cast
        rw [add_smul, one_smul, ← h1]
        simp [hf]
      · simp only [if_neg hac, if_neg hbc, sub_zero, zero_add] at h1
        have : ((μ - root a b) c : ℝ) = μ c := by
          simp [root, Pi.single_apply, Ne.symm hac, Ne.symm hbc]
        rw [this]
        exact h1
  have hhi : ∀ c d, c < d → ε c = ε d → E c d (f (a, b)) = 0 := by
    intro c d hcd hcomp
    have hcd' := Fin.lt_iff_val_lt_val.mp hcd
    have h1 := congrArg (fun G : Arr V n 1 => G (fun _ => (a, b))) (hFh.2 c d hcd hcomp)
    simp only at h1
    rw [arr_operator_one_apply, PiLp.zero_apply] at h1
    have e1 : (if a = c then F (fun _ => (d, b)) else 0) = 0 := by
      split_ifs with h
      · subst h
        exact hzero (d, b) (by simp only; omega)
      · rfl
    have e2 : (if b = d then F (fun _ => (a, c)) else 0) = 0 := by
      split_ifs with h
      · subst h
        exact hzero (a, c) (by simp only; omega)
      · rfl
    rw [e1, e2, sub_zero, zero_add] at h1
    exact h1
  have hν := compact_highest_weight_unique hl hw hg hu hΛ ((hval a b).1 hne) ⟨hwt, hhi⟩ hab0
  rw [← hν]
  simp
end U2b

section U2c
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] {n : ℕ}

theorem mem_compact_span_self_general {W : Type} [AddCommGroup W] [Module ℂ W] {ε : Fin n → Bool}
    {F : Fin n → Fin n → Module.End ℂ W} (x : W) : x ∈ kSpan ε F x :=
  Submodule.mem_sInf.mpr fun _ hS => hS.1

theorem compact_span_stable_general {W : Type} [AddCommGroup W] [Module ℂ W] {ε : Fin n → Bool}
    {F : Fin n → Fin n → Module.End ℂ W} (x : W) : KStable ε F (kSpan ε F x) := by
  intro a b hab y hy
  rw [kSpan, Submodule.mem_sInf] at hy ⊢
  intro S hS
  exact hS.2 a b hab y (hy S hS)

theorem compact_span_le_of_stable {W : Type} [AddCommGroup W] [Module ℂ W] {ε : Fin n → Bool}
    {F : Fin n → Fin n → Module.End ℂ W} {S : Submodule ℂ W} {x : W} (hS : KStable ε F S)
    (hx : x ∈ S) : kSpan ε F x ≤ S :=
  sInf_le ⟨hx, hS⟩

theorem compact_span_zero_le {W : Type} [AddCommGroup W] [Module ℂ W] {ε : Fin n → Bool}
    {F : Fin n → Fin n → Module.End ℂ W} (M : Submodule ℂ W) : kSpan ε F 0 ≤ M := by
  refine le_trans (compact_span_le_of_stable (S := ⊥) ?_ (Submodule.zero_mem _)) bot_le
  intro a b _ x hx
  rw [Submodule.mem_bot] at hx ⊢
  rw [hx, map_zero]

theorem isotypic_part_le_of_forall {W : Type} [AddCommGroup W] [Module ℂ W] {ε : Fin n → Bool}
    {F : Fin n → Fin n → Module.End ℂ W} {T : Set (Fin n → ℝ)} {S M : Submodule ℂ W}
    (h : ∀ y ∈ S, ∀ μ ∈ T, KHighest ε F μ y → kSpan ε F y ≤ M) : isoPart ε F T S ≤ M :=
  iSup₂_le fun y hy => h y hy.1 hy.2.choose hy.2.choose_spec.1 hy.2.choose_spec.2

theorem compact_span_le_isotypic_part {W : Type} [AddCommGroup W] [Module ℂ W] {ε : Fin n → Bool}
    {F : Fin n → Fin n → Module.End ℂ W} {T : Set (Fin n → ℝ)} {S : Submodule ℂ W} {y : W}
    {μ : Fin n → ℝ} (hy : y ∈ S) (hμ : μ ∈ T) (hyh : KHighest ε F μ y) :
    kSpan ε F y ≤ isoPart ε F T S :=
  le_iSup₂_of_le (f := fun y (_ : y ∈ S ∧ ∃ μ ∈ T, KHighest ε F μ y) => kSpan ε F y) y
    ⟨hy, μ, hμ, hyh⟩ le_rfl

theorem theta_map_word_sum_apply {j : ℕ} (E : Fin n → Fin n → Module.End ℂ V) (F : Arr V n j) :
    thetaA E j F = ∑ α : Fin j → Fin n × Fin n, ew E (List.ofFn α).reverse (F α) := by
  simp [thetaA, arrOf]

theorem root_injective_of_ne {a b a' b' : Fin n} (hab : a ≠ b) (h : root a b = root a' b') :
    a = a' ∧ b = b' := by
  have hba : b ≠ a := Ne.symm hab
  have h1 := congrFun h a
  have h2 := congrFun h b
  simp only [root, Pi.sub_apply, Pi.single_apply, if_pos rfl, if_neg hab, if_neg hba] at h1 h2
  have e1 : a = a' := by
    by_contra e1
    rw [if_neg e1] at h1
    split_ifs at h1 <;> norm_num at h1
  subst e1
  refine ⟨rfl, ?_⟩
  by_contra e4
  rw [if_neg hba, if_neg e4] at h2
  norm_num at h2

theorem noncompact_arr_one_compact_stable {ε : Fin n → Bool} {E : Fin n → Fin n → Module.End ℂ V} {u : V} :
    KStable ε (arrE E 1) (arrV0 ε E u 1) := by
  intro c d hcd F hF
  have hval := noncompact_arr_one_values hF
  have hks := compact_span_stable_general (ε := ε) (F := E) u
  apply mem_noncompact_arr_one
  · intro a b hne
    rw [arr_operator_one_apply]
    refine Submodule.add_mem _ (Submodule.sub_mem _ ?_ ?_) (hks c d hcd _ ((hval a b).1 hne))
    · split_ifs with h
      · subst h; exact (hval d b).1 (by rw [← hcd]; exact hne)
      · exact Submodule.zero_mem _
    · split_ifs with h
      · subst h; exact (hval a c).1 (by rw [hcd]; exact hne)
      · exact Submodule.zero_mem _
  · intro a b he
    rw [arr_operator_one_apply, (hval a b).2 he, map_zero, add_zero]
    have e1 : (if a = c then F (fun _ => (d, b)) else 0) = 0 := by
      split_ifs with h
      · subst h; exact (hval d b).2 (by rw [← hcd]; exact he)
      · rfl
    have e2 : (if b = d then F (fun _ => (a, c)) else 0) = 0 := by
      split_ifs with h
      · subst h; exact (hval a c).2 (by rw [hcd]; exact he)
      · rfl
    rw [e1, e2, sub_zero]

theorem noncompact_arr_finite_dimensional {j : ℕ} {ε : Fin n → Bool} {E : Fin n → Fin n → Module.End ℂ V} {u : V}
    (hfd : FiniteDimensional ℂ (kSpan ε E u)) : FiniteDimensional ℂ (arrV0 ε E u j) := by
  have hmem : ∀ (F : arrV0 ε E u j) (α : Fin j → Fin n × Fin n),
      ((LinearMap.proj (R := ℂ) (φ := fun _ : Fin j → Fin n × Fin n => V) α ∘ₗ arrOf V n j) ∘ₗ
        (arrV0 ε E u j).subtype) F ∈ kSpan ε E u := by
    intro F α
    have h := (mem_noncompact_arr_iff_general (F : Arr V n j)).mp F.2 α
    change ((F : Arr V n j) α) ∈ _
    split_ifs at h
    · exact h
    · rw [Submodule.mem_bot] at h
      rw [h]; exact Submodule.zero_mem _
  let φ : arrV0 ε E u j →ₗ[ℂ] ((Fin j → Fin n × Fin n) → kSpan ε E u) :=
    LinearMap.pi fun α => LinearMap.codRestrict (kSpan ε E u)
      ((LinearMap.proj (R := ℂ) (φ := fun _ : Fin j → Fin n × Fin n => V) α ∘ₗ arrOf V n j) ∘ₗ
        (arrV0 ε E u j).subtype) (fun F => hmem F α)
  have hinj : Function.Injective φ := by
    intro F G hFG
    apply Subtype.ext
    apply PiLp.ext
    intro α
    have := congrArg (fun h => ((h α : kSpan ε E u) : V)) hFG
    simpa [φ, arrOf] using this
  exact Module.Finite.of_injective φ hinj

end U2c

section U2d

theorem typesSplit_of (hv : HVCoeff) (hi : KIsoSplit) (ha : ArrModule) : TypesSplit := by
  intro V _ _ n ε E Λ u hg hu hΛ hfd
  have hA := (ha V n ε E 1).1 hg
  have hKU := (ha V n ε E 1).2 hu
  have hKR := glRel_kRel ε _ hA.1
  have := noncompact_arr_finite_dimensional (j := 1) hfd
  obtain ⟨h1, h2⟩ := hi (Arr V n 1) n ε (arrE E 1) (arrV0 ε E u 1)
    {μ | ∃ a b, a < b ∧ ε a ≠ ε b ∧ μ = Λ + root a b} inferInstance hKR hKU noncompact_arr_one_compact_stable
  have heq : isoPart ε (arrE E 1) {μ | ∃ a b, a < b ∧ ε a ≠ ε b ∧ μ = Λ + root a b}ᶜ
      (arrV0 ε E u 1) = Vminus ε E Λ u := by
    apply le_antisymm
    · apply isotypic_part_le_of_forall
      intro y hy μ hμ hyh
      by_cases hy0 : y = 0
      · subst hy0; exact compact_span_zero_le _
      · obtain ⟨a, b, hne, rfl⟩ := hv V n ε E Λ μ u y hg hu hΛ hy hyh hy0
        apply compact_span_le_isotypic_part hy _ hyh
        have hab : a ≠ b := fun h => hne (h ▸ rfl)
        rcases lt_or_gt_of_ne hab with h | h
        · exact absurd ⟨a, b, h, hne, rfl⟩ hμ
        · exact ⟨a, b, h, hne, rfl⟩
    · apply isotypic_part_le_of_forall
      intro y hy μ hμ hyh
      apply compact_span_le_isotypic_part hy _ hyh
      rintro ⟨a', b', h', hne', heq'⟩
      obtain ⟨a, b, h, hne, rfl⟩ := hμ
      obtain ⟨e1, e2⟩ := root_injective_of_ne (ne_of_gt h) (add_left_cancel heq')
      subst e1; subst e2
      exact absurd h (not_lt.mpr h'.le)
  refine ⟨fun F hF G hG => h1 F hF G (heq ▸ hG), ?_⟩
  rw [← heq]
  exact h2

theorem root_swap' {n : ℕ} (a b : Fin n) : root a b = -root b a := by
  unfold root; abel

end U2d

section U2e
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] {n : ℕ}

theorem positions_one_apply (c d : Fin n) (G : Arr V n 1) (a b : Fin n) :
    positionsE V n 1 c d G (fun _ => (a, b)) =
      (if a = c then G (fun _ => (d, b)) else 0) - (if b = d then G (fun _ => (a, c)) else 0) := by
  simp only [positionsE, Fin.sum_univ_one, factorAction_apply_general,
    fin_one_update_eq_const]

theorem CasK_apply {j : ℕ} {ε : Fin n → Bool} (X : Fin n → Fin n → Module.End ℂ (Arr V n j))
    (G : Arr V n j) (α : Fin j → Fin n × Fin n) :
    CasK ε X G α = ∑ c, ∑ d, if ε c = ε d then X c d (X d c G) α else 0 := by
  simp only [CasK, LinearMap.sum_apply, WithLp.ofLp_sum, Finset.sum_apply]
  refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun d _ => ?_
  split_ifs <;> simp

theorem bool_trichotomy_of_ne : ∀ x y z : Bool, x ≠ y → (z = x ∧ z ≠ y) ∨ (z = y ∧ z ≠ x) := by decide

theorem compact_casimir_positions_one {ε : Fin n → Bool} (F : Arr V n 1)
    (hz : ∀ a b, ε a = ε b → F (fun _ => (a, b)) = 0) :
    CasK ε (positionsE V n 1) F = (n : ℂ) • F := by
  apply PiLp.ext
  intro α
  rw [fin_one_fun_eq_const_apply_zero α, PiLp.smul_apply]
  obtain ⟨a, b⟩ := α 0
  rw [CasK_apply]
  by_cases hab : ε a = ε b
  · rw [hz a b hab, smul_zero]
    apply Finset.sum_eq_zero
    intro c _
    apply Finset.sum_eq_zero
    intro d _
    split_ifs with hcd
    · simp only [positions_one_apply]
      have hd : ∀ x, F (fun _ => (x, x)) = 0 := fun x => hz x x rfl
      by_cases h1 : a = c <;> by_cases h2 : b = d
      · subst h1; subst h2; simp [hz _ _ hab, hd]
      · subst h1; simp [hz _ _ hab, hd, h2]
      · subst h2; simp [hz _ _ hab, hd, h1]
      · simp [h1, h2]
    · rfl
  · have key : ∀ c d, (if ε c = ε d then positionsE V n 1 c d (positionsE V n 1 d c F) (fun _ => (a, b))
        else 0) = (if c = a then (if ε d = ε a then F (fun _ => (a, b)) else 0) else 0) +
          (if d = b then (if ε c = ε b then F (fun _ => (a, b)) else 0) else 0) := by
      intro c d
      have hab' : a ≠ b := fun h => hab (h ▸ rfl)
      by_cases hcd : ε c = ε d
      · rw [if_pos hcd]
        simp only [positions_one_apply]
        by_cases h1 : c = a
        · subst h1
          have hbd : b ≠ d := by rintro rfl; exact hab hcd
          simp [hbd, Ne.symm hbd, Ne.symm hab', hcd.symm]
        · by_cases h2 : d = b
          · subst h2
            simp [h1, Ne.symm h1, hab', hcd]
          · simp [h1, Ne.symm h1, h2, Ne.symm h2]
      · rw [if_neg hcd]
        have e1 : (if c = a then (if ε d = ε a then F (fun _ => (a, b)) else 0) else 0) = 0 := by
          split_ifs with h1 h2
          · subst h1; exact absurd h2.symm hcd
          · rfl
          · rfl
        have e2 : (if d = b then (if ε c = ε b then F (fun _ => (a, b)) else 0) else 0) = 0 := by
          split_ifs with h1 h2
          · subst h1; exact absurd h2 hcd
          · rfl
          · rfl
        rw [e1, e2, add_zero]
    simp only [key, Finset.sum_add_distrib, Finset.sum_ite_irrel, Finset.sum_const_zero,
      Finset.sum_ite_eq', Finset.mem_univ, if_true]
    rw [← Finset.sum_add_distrib]
    have : ∀ d : Fin n, ((if ε d = ε a then F (fun _ => (a, b)) else 0) +
        (if ε d = ε b then F (fun _ => (a, b)) else 0)) = F (fun _ => (a, b)) := by
      intro d
      rcases bool_trichotomy_of_ne (ε a) (ε b) (ε d) hab with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · rw [if_pos h1, if_neg h2, add_zero]
      · rw [if_neg h2, if_pos h1, zero_add]
    simp only [this, Finset.sum_const, Finset.card_univ, Fintype.card_fin]
    rw [Nat.cast_smul_eq_nsmul]

end U2e

section U2f
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] {n : ℕ}

theorem re_inner_self_eq_norm_sq {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℂ W] (x : W) :
    (⟪x, x⟫_ℂ).re = ‖x‖ ^ 2 := by
  have := @norm_sq_eq_re_inner ℂ _ _ _ _ x
  rw [this]
  simp

theorem omega_eigenvalue_on_span (hk : KCasSpan) (hca : CasArr) (ha : ArrModule) {ε : Fin n → Bool}
    {E : Fin n → Fin n → Module.End ℂ V} {Λ μ : Fin n → ℝ} {u : V} {y : Arr V n 1}
    (hg : GlRel E) (hΛ : KHighest ε E Λ u) (hy : y ∈ arrV0 ε E u 1)
    (hyh : KHighest ε (arrE E 1) μ y) {G : Arr V n 1} (hG : G ∈ kSpan ε (arrE E 1) y) :
    OmS ε E (0 : Fin 1) G = (((ckv ε μ - n - ckv ε Λ) / 2 : ℝ) : ℂ) • G := by
  have hKR := glRel_kRel ε _ ((ha V n ε E 1).1 hg).1
  have hGS : G ∈ arrV0 ε E u 1 := compact_span_le_of_stable noncompact_arr_one_compact_stable hy hG
  have h1 := (hca V n ε E Λ u 1).1 hg hΛ G hGS
  have h2 := hk (Arr V n 1) n ε (arrE E 1) μ y hKR hyh G hG
  have h3 := compact_casimir_positions_one G (fun a b h => (noncompact_arr_one_values hGS a b).2 h)
  rw [h2, h3, Fin.sum_univ_one] at h1
  have h4 : (2 : ℂ) • OmS ε E (0 : Fin 1) G = ((ckv ε μ : ℂ) - n - ckv ε Λ) • G := by
    rw [sub_smul, sub_smul, h1]; abel
  calc OmS ε E (0 : Fin 1) G = (1 / 2 : ℂ) • ((2 : ℂ) • OmS ε E (0 : Fin 1) G) := by
        rw [smul_smul]; norm_num
    _ = (((ckv ε μ - n - ckv ε Λ) / 2 : ℝ) : ℂ) • G := by
        rw [h4, smul_smul]; congr 1; push_cast; ring

theorem omPlus_of (hd : KDecomp) (ho : KOrth) (hk : KCasSpan) (hca : CasArr) (ha : ArrModule) :
    OmPlus := by
  intro V _ _ n ε E lam g u hg hu hΛ hfd hgap F hF
  classical
  have hA := (ha V n ε E 1).1 hg
  have hKU := (ha V n ε E 1).2 hu
  have hKR := glRel_kRel ε _ hA.1
  let ι := {p : Fin n × Fin n // p.1 < p.2 ∧ ε p.1 ≠ ε p.2}
  let W : ι → Submodule ℂ (Arr V n 1) := fun p =>
    isoPart ε (arrE E 1) {LamOf ε lam + root p.1.1 p.1.2} (arrV0 ε E u 1)
  let c : ι → ℝ := fun p => (ckv ε (LamOf ε lam + root p.1.1 p.1.2) - n - ckv ε (LamOf ε lam)) / 2
  have hcge : ∀ p : ι, g - 2 * n ≤ c p := by
    intro p
    have h1 := omEigen n ε lam p.1.1 p.1.2 (ne_of_lt p.2.1)
    have h2 := uGap n ε lam g p.1.1 p.1.2 p.2.1 p.2.2 (hgap _ _ p.2.1 p.2.2)
    simp only [c, ckv, LamOf]
    linarith
  have hWeig : ∀ p : ι, ∀ G ∈ W p, OmS ε E (0 : Fin 1) G = (c p : ℂ) • G := by
    intro p
    have hle : W p ≤ LinearMap.ker (OmS ε E (0 : Fin 1) - (c p : ℂ) • LinearMap.id) := by
      apply isotypic_part_le_of_forall
      intro y hy μ hμ hyh G hG
      rw [Set.mem_singleton_iff] at hμ
      subst hμ
      rw [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply,
        sub_eq_zero]
      exact omega_eigenvalue_on_span hk hca ha hg hΛ hy hyh hG
    intro G hG
    have := hle hG
    rwa [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply,
      sub_eq_zero] at this
  have hWorth : ∀ p q : ι, p ≠ q → ∀ G ∈ W p, ∀ H ∈ W q, ⟪G, H⟫_ℂ = 0 := by
    intro p q hpq
    have hμ : LamOf ε lam + root p.1.1 p.1.2 ≠ LamOf ε lam + root q.1.1 q.1.2 := by
      intro h
      obtain ⟨e1, e2⟩ := root_injective_of_ne (ne_of_lt p.2.1) (add_left_cancel h)
      exact hpq (Subtype.ext (Prod.ext e1 e2))
    have step : W p ≤ (W q)ᗮ := by
      apply isotypic_part_le_of_forall
      intro y hy μ hμ' hyh
      rw [Set.mem_singleton_iff] at hμ'
      subst hμ'
      have hq : W q ≤ (kSpan ε (arrE E 1) y)ᗮ := by
        apply isotypic_part_le_of_forall
        intro y' hy' μ' hμ'' hyh' H hH
        rw [Set.mem_singleton_iff] at hμ''
        subst hμ''
        rw [Submodule.mem_orthogonal]
        intro G hG
        exact ho (Arr V n 1) n ε (arrE E 1) _ _ y y' hKR hKU hyh hyh' hμ G hG H hH
      intro G hG
      rw [Submodule.mem_orthogonal]
      intro H hH
      have := hq hH
      rw [Submodule.mem_orthogonal] at this
      exact inner_eq_zero_symm.mp (this G hG)
    intro G hG H hH
    have := step hG
    rw [Submodule.mem_orthogonal] at this
    exact inner_eq_zero_symm.mp (this H hH)
  have hsup : Vplus ε E (LamOf ε lam) u ≤ ⨆ p : ι, W p := by
    apply isotypic_part_le_of_forall
    intro y hy μ hμ hyh
    obtain ⟨a, b, hab, hne, rfl⟩ := hμ
    exact le_trans (compact_span_le_isotypic_part hy (Set.mem_singleton _) hyh) (le_iSup W ⟨(a, b), hab, hne⟩)
  obtain ⟨f, hfW, hfs⟩ : ∃ f : ι → Arr V n 1, (∀ p, f p ∈ W p) ∧ F = ∑ p, f p := by
    refine Submodule.iSup_induction W (motive := fun x => ∃ f : ι → Arr V n 1,
      (∀ p, f p ∈ W p) ∧ x = ∑ p, f p) (hsup hF) ?_ ?_ ?_
    · intro p x hx
      refine ⟨Pi.single p x, fun q => ?_, by simp⟩
      by_cases h : q = p
      · subst h; simpa using hx
      · simp [h]
    · exact ⟨0, fun _ => Submodule.zero_mem _, by simp⟩
    · rintro x y ⟨f1, h1, e1⟩ ⟨f2, h2, e2⟩
      exact ⟨f1 + f2, fun p => Submodule.add_mem _ (h1 p) (h2 p),
        by rw [e1, e2, ← Finset.sum_add_distrib]; rfl⟩
  have hort : ∀ p q : ι, p ≠ q → ⟪f p, f q⟫_ℂ = 0 := fun p q h =>
    hWorth p q h _ (hfW p) _ (hfW q)
  have hOm : OmS ε E (0 : Fin 1) F = ∑ q, (c q : ℂ) • f q := by
    rw [hfs, map_sum]
    exact Finset.sum_congr rfl fun q _ => hWeig q _ (hfW q)
  have e1 : ⟪F, OmS ε E (0 : Fin 1) F⟫_ℂ = ∑ p, (c p : ℂ) * ⟪f p, f p⟫_ℂ := by
    rw [hOm, hfs, sum_inner]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [inner_sum]
    rw [Finset.sum_eq_single p (fun q _ hq => by rw [inner_smul_right, hort p q (Ne.symm hq),
      mul_zero]) (by simp), inner_smul_right]
  have e2 : ⟪F, F⟫_ℂ = ∑ p, ⟪f p, f p⟫_ℂ := by
    conv_lhs => rw [hfs]
    rw [sum_inner]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [inner_sum, Finset.sum_eq_single p (fun q _ hq => hort p q (Ne.symm hq)) (by simp)]
  have hn : ‖F‖ ^ 2 = ∑ p, ‖f p‖ ^ 2 := by
    rw [← re_inner_self_eq_norm_sq, e2, Complex.re_sum]
    exact Finset.sum_congr rfl fun p _ => re_inner_self_eq_norm_sq (f p)
  have hre : (⟪F, OmS ε E (0 : Fin 1) F⟫_ℂ).re = ∑ p, c p * ‖f p‖ ^ 2 := by
    rw [e1, Complex.re_sum]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [Complex.re_ofReal_mul, re_inner_self_eq_norm_sq]
  rw [hre, hn, Finset.mul_sum]
  exact Finset.sum_le_sum fun p _ => mul_le_mul_of_nonneg_right (hcge p) (sq_nonneg _)

end U2f

end Formalism.REAL
