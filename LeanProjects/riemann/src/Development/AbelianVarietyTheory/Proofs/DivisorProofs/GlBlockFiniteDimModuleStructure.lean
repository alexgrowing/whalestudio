import Mathlib
import Formalism.SharpRestriction.Divisibility.SchurIrreducible
import Development.AbelianVarietyTheory.Definitions.Foundations.IsFockIPOfFockData
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HighestWeightTensor

open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.TensorHW

noncomputable section

namespace GlobalTheory.BlockReps

variable {p q : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V] {act : Mat p q →ₗ[ℂ] Module.End ℂ V}

lemma proj_fin {W : Submodule ℂ V} (hW : KStable act W) {ν : Ix p q → ℚ} (F : Finset (Ix p q → ℚ))
    (hF : ν ∉ F) :
    ∀ y ∈ wtSub act ν, ∀ z ∈ ⨆ μ ∈ F, wtSub act μ, y + z ∈ W → y ∈ W := by
  classical
  induction F using Finset.induction_on with
  | empty =>
    intro y _ z hz h
    simp at hz
    simpa [hz] using h
  | insert μ F hμ ih =>
    intro y hy z hz h
    rw [Finset.iSup_insert] at hz
    obtain ⟨z1, h1, z2, h2, rfl⟩ := Submodule.mem_sup.1 hz
    rw [Finset.mem_insert, not_or] at hF
    obtain ⟨a, ha⟩ := Function.ne_iff.1 hF.1
    have hc : (((ν a : ℚ) : ℂ) - ((μ a : ℚ) : ℂ)) ≠ 0 := by exact_mod_cast sub_ne_zero.2 ha
    have h3 : act (Eab a a) z2 ∈ ⨆ μ ∈ F, wtSub act μ := by
      have : (⨆ μ ∈ F, wtSub act μ) ≤ (⨆ μ ∈ F, wtSub act μ).comap (act (Eab a a)) :=
        iSup₂_le fun κ hκ x hx => by
          rw [Submodule.mem_comap, mem_wt.1 hx a]
          exact Submodule.smul_mem _ _
            ((le_iSup₂_of_le (f := fun μ (_ : μ ∈ F) => wtSub act μ) κ hκ le_rfl :
              wtSub act κ ≤ _) hx)
      exact this h2
    have := ih hF.2 ((((ν a : ℚ) : ℂ) - ((μ a : ℚ) : ℂ)) • y) (Submodule.smul_mem _ _ hy)
      (act (Eab a a) z2 - ((μ a : ℚ) : ℂ) • z2) (sub_mem h3 (Submodule.smul_mem _ _ h2)) (by
        convert W.sub_mem (hW _ (isKC_Eab (same_refl a)) _ h) (W.smul_mem ((μ a : ℚ) : ℂ) h) using 1
        rw [map_add, map_add, mem_wt.1 hy, mem_wt.1 h1]
        module)
    exact (W.smul_mem_iff hc).1 this

lemma wt_indep : iSupIndep (wtSub act) := by
  classical
  intro ν
  rw [Submodule.disjoint_def]
  intro y hy hz
  obtain ⟨s, hs⟩ := Submodule.mem_iSup_iff_exists_finset.1 hz
  have hle : (⨆ i ∈ s, ⨆ (_ : i ≠ ν), wtSub act i) ≤ ⨆ i ∈ s.erase ν, wtSub act i :=
    iSup₂_le fun i hi => iSup_le fun hne =>
      le_iSup₂_of_le (f := fun μ (_ : μ ∈ s.erase ν) => wtSub act μ) i
        (Finset.mem_erase.2 ⟨hne, hi⟩) le_rfl
  have hb : KStable act (⊥ : Submodule ℂ V) := by
    intro Z _ w hw
    rw [Submodule.mem_bot] at hw ⊢
    rw [hw, map_zero]
  exact proj_fin hb (s.erase ν) (by simp) y hy (-y) (neg_mem (hle hs)) (by simp)

lemma decomp {W : Submodule ℂ V} (hW : KStable act W) {x : V} (hx : x ∈ W)
    (h : x ∈ ⨆ μ, wtSub act μ) : x ∈ ⨆ μ, W ⊓ wtSub act μ := by
  classical
  obtain ⟨F, hF⟩ := Submodule.mem_iSup_iff_exists_finset.1 h
  clear h
  induction F using Finset.induction_on generalizing x with
  | empty =>
    simp at hF
    simp [hF]
  | insert μ F hμ ih =>
    rw [Finset.iSup_insert] at hF
    obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.1 hF
    have hyW := proj_fin hW F hμ y hy z hz hx
    exact add_mem (Submodule.mem_iSup_of_mem μ ⟨hyW, hy⟩) (ih ((W.add_mem_iff_right hyW).1 hx) hz)

lemma finite_wts (W : Submodule ℂ V) [FiniteDimensional ℂ W] :
    {μ | W ⊓ wtSub act μ ≠ ⊥}.Finite := by
  have hi : iSupIndep fun μ => (wtSub act μ).comap W.subtype := by
    intro ν
    rw [Submodule.disjoint_def]
    intro y hy hz
    have hle : (⨆ j, ⨆ (_ : j ≠ ν), (wtSub act j).comap W.subtype) ≤
        (⨆ j, ⨆ (_ : j ≠ ν), wtSub act j).comap W.subtype :=
      iSup₂_le fun j hj => Submodule.comap_mono
        (le_iSup₂_of_le (f := fun j (_ : j ≠ ν) => wtSub act j) j hj le_rfl)
    exact Subtype.ext (Submodule.disjoint_def.1 (wt_indep (act := act) ν) (y : V) hy (hle hz))
  refine (WellFoundedGT.finite_ne_bot_of_iSupIndep hi).subset fun μ hμ => ?_
  obtain ⟨x, hx, h0⟩ := (Submodule.ne_bot_iff _).1 hμ
  exact (Submodule.ne_bot_iff _).2 ⟨⟨x, hx.1⟩, hx.2, fun h => h0 (congrArg Subtype.val h)⟩

lemma Eab_mul (a b c d : Ix p q) : Eab a b * Eab c d = if b = c then Eab a d else 0 := by
  split_ifs with h
  · subst h; simp [Eab]
  · simp [Eab, Matrix.single_mul_single_of_ne _ _ _ _ h]

def root (a b : Ix p q) : Ix p q → ℚ := fun c => (if c = a then 1 else 0) - (if c = b then 1 else 0)

lemma shift (hL : IsKLieAct act) {a b : Ix p q} (hab : sameBlock a b) {μ : Ix p q → ℚ} {x : V}
    (hx : x ∈ wtSub act μ) : act (Eab a b) x ∈ wtSub act (μ + root a b) := by
  rw [mem_wt] at hx ⊢
  intro c
  rw [lie_apply hL (isKC_Eab (same_refl c)) (isKC_Eab hab), hx, Eab_mul, Eab_mul, map_smul]
  simp only [Pi.add_apply, root, eq_comm (a := b) (b := c)]
  by_cases h1 : c = a <;> by_cases h2 : c = b
  · subst h1; subst h2; simp
  · subst h1; simp [h2, add_smul]
  · subst h2; simp [h1, add_smul]
  · simp [h1, h2]

lemma posC_ne {a b : Ix p q} (h : posC a b) : a ≠ b := by
  rintro rfl
  cases a <;> simp [posC] at h

lemma posC_asymm {a b : Ix p q} (h : posC a b) : ¬ posC b a := by
  cases a <;> cases b <;> simp_all [posC, le_of_lt]

lemma posC_trans {a b c : Ix p q} (h : posC a b) (h' : posC b c) : posC a c := by
  cases a <;> cases b <;> cases c <;> simp_all only [posC] <;> exact lt_trans h h'

lemma raise_lower (hL : IsKLieAct act) {a b : Ix p q} (hab : posC a b) {κ : Ix p q → ℚ} {y : V}
    (hy : y ∈ wtSub act κ) :
    act (Eab a b) (act (Eab b a) y) =
      act (Eab b a) (act (Eab a b) y) + (((κ a : ℚ) : ℂ) - ((κ b : ℚ) : ℂ)) • y := by
  rw [lie_apply hL (isKC_Eab (same_of_pos hab)) (isKC_Eab (same_of_pos' hab)), Eab_mul, Eab_mul,
    if_pos rfl, if_pos rfl, map_sub, LinearMap.sub_apply, mem_wt.1 hy, mem_wt.1 hy, sub_smul]

def pair (l μ : Ix p q → ℚ) : ℚ := ∑ x, l x * μ x

lemma pair_root (l μ : Ix p q → ℚ) (a b : Ix p q) :
    pair l (μ + root a b) = pair l μ + (l a - l b) := by
  simp [pair, root, mul_add, mul_sub, Finset.sum_add_distrib, Finset.sum_sub_distrib]

def Below (ν μ : Ix p q → ℚ) : Prop :=
  ∀ l : Ix p q → ℚ, (∀ a b, posC a b → l b < l a) → pair l ν < pair l μ

open Classical in

def rho (p q : ℕ) : Ix p q → ℚ :=
  fun x => ∑ c, ((if posC x c then 1 else 0) - (if posC c x then 1 else 0))

lemma rho_lt {a b : Ix p q} (h : posC a b) : rho p q b < rho p q a := by
  refine Finset.sum_lt_sum (fun c _ => ?_) ⟨a, Finset.mem_univ _, ?_⟩
  · have t1 : posC b c → posC a c := posC_trans h
    have t2 : posC c a → posC c b := fun h' => posC_trans h' h
    by_cases h1 : posC b c <;> by_cases h2 : posC c a <;> by_cases h3 : posC a c <;>
      by_cases h4 : posC c b <;> simp_all
  · have h1 : ¬ posC a a := fun h => posC_ne h rfl
    simp [h, h1, posC_asymm h]

open Classical in

def casVal (μ : Ix p q → ℚ) : ℚ :=
  ∑ a, ∑ b, ((if a = b then μ a * μ a else 0) + (if posC a b then μ a - μ b else 0))

lemma casVal_eq (μ : Ix p q → ℚ) : casVal μ = pair μ μ + pair (rho p q) μ := by
  classical
  have h : ∀ a b : Ix p q, (if posC a b then μ a - μ b else 0) =
      (if posC a b then 1 else 0) * μ a - (if posC a b then 1 else 0) * μ b := by
    intro a b; split_ifs <;> simp
  simp only [casVal, pair, rho, Finset.sum_add_distrib, Finset.sum_ite_eq, Finset.mem_univ, if_true,
    Finset.sum_mul, sub_mul, Finset.sum_sub_distrib]
  congr 1
  rw [Finset.sum_comm (f := fun x c => (if posC c x then (1 : ℚ) else 0) * μ x),
    ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun b _ => ?_
  convert h a b

lemma casVal_lt {μ ν : Ix p q → ℚ} (hμ : ∀ a b, posC a b → ∃ k : ℕ, μ a - μ b = k)
    (hν : ∀ a b, posC a b → ∃ k : ℕ, ν a - ν b = k) (h : Below ν μ) : casVal ν < casVal μ := by
  have := h (μ + ν + rho p q) fun a b hab => by
    obtain ⟨k, hk⟩ := hμ a b hab
    obtain ⟨l, hl⟩ := hν a b hab
    have := rho_lt hab
    have h1 : (0 : ℚ) ≤ k := Nat.cast_nonneg k
    have h2 : (0 : ℚ) ≤ l := Nat.cast_nonneg l
    simp only [Pi.add_apply]
    linarith
  rw [casVal_eq, casVal_eq]
  simp only [pair, Pi.add_apply, add_mul, Finset.sum_add_distrib] at this ⊢
  have h3 : ∑ x, μ x * ν x = ∑ x, ν x * μ x := Finset.sum_congr rfl fun x _ => mul_comm _ _
  linarith

lemma exists_max (hL : IsKLieAct act) {W : Submodule ℂ V} [FiniteDimensional ℂ W] (hW : KStable act W)
    (S : Submodule ℂ V) (P : (Ix p q → ℚ) → Prop)
    (hP : ∀ μ a b, posC a b → P μ → P (μ + root a b))
    (h : ∃ μ, P μ ∧ ¬ W ⊓ wtSub act μ ≤ S) :
    ∃ μ, P μ ∧ ¬ W ⊓ wtSub act μ ≤ S ∧
      ∀ x ∈ W ⊓ wtSub act μ, ∀ a b, posC a b → act (Eab a b) x ∈ S := by
  have hf : {μ | P μ ∧ ¬ W ⊓ wtSub act μ ≤ S}.Finite :=
    (finite_wts (act := act) W).subset fun μ hμ h0 => hμ.2 (h0 ▸ bot_le)
  obtain ⟨μ, hμ, hmax⟩ := Set.exists_max_image _ (pair (rho p q)) hf h
  refine ⟨μ, hμ.1, hμ.2, fun x hx a b hab => ?_⟩
  by_contra hn
  have := hmax (μ + root a b) ⟨hP μ a b hab hμ.1, fun hle =>
    hn (hle ⟨hW _ (isKC_Eab (same_of_pos hab)) _ hx.1, shift hL (same_of_pos hab) hx.2⟩)⟩
  rw [pair_root] at this
  linarith [rho_lt hab]

lemma dominant (hL : IsKLieAct act) {W : Submodule ℂ V} [FiniteDimensional ℂ W] (hW : KStable act W)
    {S : Submodule ℂ V} (hS : KStable act S) {μ : Ix p q → ℚ} {x : V} (hx : x ∈ W ⊓ wtSub act μ)
    (hxS : x ∉ S) {a b : Ix p q} (hab : posC a b) (he : act (Eab a b) x ∈ S) :
    ∃ k : ℕ, μ a - μ b = k := by
  classical
  have hf := isKC_Eab (same_of_pos' hab)
  have hne := posC_ne hab
  let u : ℕ → V := fun k => (act (Eab b a))^[k] x
  have hu : ∀ k, u (k + 1) = act (Eab b a) (u k) := fun k => Function.iterate_succ_apply' _ _ _
  have hw : ∀ k : ℕ, u k ∈ W ⊓ wtSub act (μ + (k : ℚ) • root b a) := by
    intro k
    induction k with
    | zero => simpa [u] using hx
    | succ k ih =>
      rw [hu, Nat.cast_succ, add_smul, one_smul, ← add_assoc]
      exact ⟨hW _ hf _ ih.1, shift hL (same_of_pos' hab) ih.2⟩
  have hex : ∃ k, u k ∈ S := by
    by_contra hn
    push Not at hn
    refine Set.infinite_of_injective_forall_mem (f := fun k : ℕ => μ + (k : ℚ) • root b a)
      (s := {μ | W ⊓ wtSub act μ ≠ ⊥})
      (fun k l hkl => ?_) (fun k h0 => hn k ?_) (finite_wts (act := act) W)
    · have := congrFun hkl a
      simpa [root, hne] using this
    · have := hw k
      rw [h0, Submodule.mem_bot] at this
      rw [this]; exact S.zero_mem
  have hel : ∀ k : ℕ, act (Eab a b) (u (k + 1)) = act (Eab b a) (act (Eab a b) (u k)) +
      (((μ a : ℚ) : ℂ) - ((μ b : ℚ) : ℂ) - 2 * k) • u k := by
    intro k
    rw [hu, raise_lower hL hab (hw k).2]
    congr 2
    simp [root, hne, hne.symm]
    ring
  have key : ∀ k : ℕ, act (Eab a b) (u (k + 1)) -
      (((k : ℂ) + 1) * (((μ a : ℚ) : ℂ) - ((μ b : ℚ) : ℂ) - k)) • u k ∈ S := by
    intro k
    induction k with
    | zero => rw [hel]; simpa [u] using hS _ hf _ he
    | succ k ih =>
      rw [hel]
      convert hS _ hf _ ih using 1
      rw [map_sub, map_smul, ← hu]
      push_cast
      module
  obtain ⟨n, hn⟩ : ∃ n, Nat.find hex = n + 1 :=
    Nat.exists_eq_succ_of_ne_zero fun h0 => hxS (by have := Nat.find_spec hex; rwa [h0] at this)
  have h1 : u (n + 1) ∈ S := hn ▸ Nat.find_spec hex
  have h2 : u n ∉ S := Nat.find_min hex (by omega)
  have h3 := (S.sub_mem_iff_right (hS _ (isKC_Eab (same_of_pos hab)) _ h1)).1 (key n)
  refine ⟨n, ?_⟩
  by_contra hc
  refine h2 ((S.smul_mem_iff (mul_ne_zero (Nat.cast_add_one_ne_zero n) ?_)).1 h3)
  exact_mod_cast sub_ne_zero.2 hc

def unitK (act : Mat p q →ₗ[ℂ] Module.End ℂ V) (a b : Ix p q) : Module.End ℂ V :=
  if sameBlock a b then act (Eab a b) else 0

def casK (act : Mat p q →ₗ[ℂ] Module.End ℂ V) : Module.End ℂ V :=
  ∑ a, ∑ b, unitK act a b * unitK act b a

lemma unitK_comm (hL : IsKLieAct act) {a b : Ix p q} (hab : sameBlock a b) (c d : Ix p q) :
    act (Eab a b) * unitK act c d - unitK act c d * act (Eab a b) =
      (if b = c then unitK act a d else 0) - (if d = a then unitK act c b else 0) := by
  by_cases hcd : sameBlock c d
  · rw [unitK, if_pos hcd, ← hL _ _ (isKC_Eab hab) (isKC_Eab hcd), Eab_mul, Eab_mul, map_sub]
    congr 1
    · split_ifs with h
      · subst h
        rw [unitK, if_pos]
        cases a <;> cases b <;> cases d <;> simp_all [sameBlock]
      · simp
    · split_ifs with h
      · subst h
        rw [unitK, if_pos]
        cases c <;> cases b <;> cases d <;> simp_all [sameBlock]
      · simp
  · have h1 : (if b = c then unitK act a d else 0) = 0 := by
      split_ifs with h
      · subst h
        rw [unitK, if_neg]
        cases a <;> cases b <;> cases d <;> simp_all [sameBlock]
      · rfl
    have h2 : (if d = a then unitK act c b else 0) = 0 := by
      split_ifs with h
      · subst h
        rw [unitK, if_neg]
        cases c <;> cases b <;> cases d <;> simp_all [sameBlock]
      · rfl
    rw [h1, h2, unitK, if_neg hcd]
    simp

lemma casK_comm (hL : IsKLieAct act) {a b : Ix p q} (hab : sameBlock a b) :
    Commute (act (Eab a b)) (casK act) := by
  have h : ∀ c d, act (Eab a b) * (unitK act c d * unitK act d c) -
      unitK act c d * unitK act d c * act (Eab a b) =
      ((if b = c then unitK act a d * unitK act d c else 0) -
        (if d = a then unitK act c b * unitK act d c else 0)) +
      ((if b = d then unitK act c d * unitK act a c else 0) -
        (if c = a then unitK act c d * unitK act d b else 0)) := by
    intro c d
    have e : act (Eab a b) * (unitK act c d * unitK act d c) -
        unitK act c d * unitK act d c * act (Eab a b) =
        (act (Eab a b) * unitK act c d - unitK act c d * act (Eab a b)) * unitK act d c +
        unitK act c d * (act (Eab a b) * unitK act d c - unitK act d c * act (Eab a b)) := by
      noncomm_ring
    rw [e, unitK_comm hL hab, unitK_comm hL hab]
    simp only [sub_mul, mul_sub, ite_mul, mul_ite, zero_mul, mul_zero]
  rw [Commute, SemiconjBy, ← sub_eq_zero, casK, Finset.mul_sum, Finset.sum_mul, ← Finset.sum_sub_distrib]
  simp only [Finset.mul_sum, Finset.sum_mul, ← Finset.sum_sub_distrib, h]
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_ite_eq, Finset.sum_ite_eq',
    Finset.mem_univ, if_true, Finset.sum_ite_irrel, Finset.sum_const_zero]
  abel

lemma unitK_mem {S : Submodule ℂ V} (hS : KStable act S) (a b : Ix p q) {x : V} (hx : x ∈ S) :
    unitK act a b x ∈ S := by
  rw [unitK]
  split_ifs with h
  · exact hS _ (isKC_Eab h) _ hx
  · simp

lemma casK_mem {S : Submodule ℂ V} (hS : KStable act S) {x : V} (hx : x ∈ S) : casK act x ∈ S := by
  simp only [casK, LinearMap.sum_apply, Module.End.mul_apply]
  exact S.sum_mem fun a _ => S.sum_mem fun b _ => unitK_mem hS _ _ (unitK_mem hS _ _ hx)

lemma casK_wt (hL : IsKLieAct act) {μ : Ix p q → ℚ} {x : V} (hx : x ∈ wtSub act μ) :
    casK act x ∈ wtSub act μ := by
  rw [mem_wt] at hx ⊢
  intro a
  rw [← Module.End.mul_apply, (casK_comm hL (same_refl a)).eq, Module.End.mul_apply, hx, map_smul]

lemma casK_mod (hL : IsKLieAct act) {S : Submodule ℂ V} (hS : KStable act S) {μ : Ix p q → ℚ} {x : V}
    (hx : x ∈ wtSub act μ) (he : ∀ a b, posC a b → act (Eab a b) x ∈ S) :
    casK act x - ((casVal μ : ℚ) : ℂ) • x ∈ S := by
  simp only [casK, casVal, LinearMap.sum_apply, Module.End.mul_apply, Rat.cast_sum, Finset.sum_smul,
    ← Finset.sum_sub_distrib]
  refine S.sum_mem fun a _ => S.sum_mem fun b _ => ?_
  by_cases hab : sameBlock a b
  · rcases same_tri hab with rfl | h | h
    · have h1 : ¬ posC a a := fun h => posC_ne h rfl
      simp [unitK, hab, h1, mem_wt.1 hx a, mul_smul]
    · rw [unitK, unitK, if_pos hab, if_pos (same_of_pos' h), raise_lower hL h hx, if_neg (posC_ne h),
        if_pos h]
      simpa using hS _ (isKC_Eab (same_of_pos' h)) _ (he a b h)
    · rw [unitK, unitK, if_pos hab, if_pos (same_of_pos h), if_neg (posC_ne h).symm,
        if_neg (posC_asymm h)]
      simpa using hS _ (isKC_Eab hab) _ (he b a h)
  · have h1 : a ≠ b := by rintro rfl; exact hab (same_refl a)
    have h2 : ¬ posC a b := fun h => hab (same_of_pos h)
    simp [unitK, hab, h1, h2]

lemma stable_bot : KStable act (⊥ : Submodule ℂ V) := by
  intro Z _ w hw
  rw [Submodule.mem_bot] at hw ⊢
  rw [hw, map_zero]

lemma stable_inf {A B : Submodule ℂ V} (hA : KStable act A) (hB : KStable act B) :
    KStable act (A ⊓ B) := fun Z hZ w hw => ⟨hA Z hZ w hw.1, hB Z hZ w hw.2⟩

lemma stable_sup {A B : Submodule ℂ V} (hA : KStable act A) (hB : KStable act B) :
    KStable act (A ⊔ B) := by
  intro Z hZ w hw
  obtain ⟨x, hx, y, hy, rfl⟩ := Submodule.mem_sup.1 hw
  rw [map_add]
  exact Submodule.add_mem_sup (hA Z hZ x hx) (hB Z hZ y hy)

lemma casK_hw (hL : IsKLieAct act) {μ : Ix p q → ℚ} {x : V} (hx : x ∈ hwSub act μ) :
    casK act x = ((casVal μ : ℚ) : ℂ) • x := by
  have := casK_mod hL stable_bot hx.1 fun a b hab => (mem_hw.1 hx).2 a b hab
  rwa [Submodule.mem_bot, sub_eq_zero] at this

lemma stable_ker (hL : IsKLieAct act) (c : ℂ) (n : ℕ) :
    KStable act (LinearMap.ker ((casK act - c • 1) ^ n)) := by
  intro Z hZ w hw
  refine kc_ind act _ w (fun a b hab => ?_) hZ
  have : Commute (act (Eab a b)) ((casK act - c • 1) ^ n) :=
    ((casK_comm hL hab).sub_right ((Commute.one_right _).smul_right c)).pow_right n
  rw [LinearMap.mem_ker] at hw ⊢
  rw [← Module.End.mul_apply, ← this.eq, Module.End.mul_apply, hw, map_zero]

lemma casVal_of_ker (hL : IsKLieAct act) {ν : Ix p q → ℚ} {w : V} (hw : IsHW act ν w) {c : ℚ} {n : ℕ}
    (h : w ∈ LinearMap.ker ((casK act - (c : ℂ) • 1) ^ n)) : casVal ν = c := by
  have h1 : ∀ n : ℕ, ((casK act - (c : ℂ) • 1) ^ n) w = (((casVal ν : ℚ) : ℂ) - c) ^ n • w := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [pow_succ', Module.End.mul_apply, ih, map_smul, pow_succ, mul_smul]
      simp [casK_hw hL hw.2, sub_smul]
  rw [LinearMap.mem_ker, h1, smul_eq_zero] at h
  have := sub_eq_zero.1 (eq_zero_of_pow_eq_zero (h.resolve_right hw.1))
  exact_mod_cast this

lemma hw_dominant (hL : IsKLieAct act) {W : Submodule ℂ V} [FiniteDimensional ℂ W] (hW : KStable act W)
    {μ : Ix p q → ℚ} {v : V} (hv : v ∈ W) (h : IsHW act μ v) {a b : Ix p q} (hab : posC a b) :
    ∃ k : ℕ, μ a - μ b = k :=
  dominant hL hW stable_bot ⟨hv, h.2.1⟩ h.1 hab ((mem_hw.1 h.2).2 a b hab)

lemma hw_of_ker (hL : IsKLieAct act) {W : Submodule ℂ V} [FiniteDimensional ℂ W] (hW : KStable act W)
    {μ : Ix p q → ℚ} (hμ : ∀ a b, posC a b → ∃ k : ℕ, μ a - μ b = k) {x : V}
    (hx : x ∈ W ⊓ wtSub act μ) {n : ℕ}
    (hk : x ∈ LinearMap.ker ((casK act - ((casVal μ : ℚ) : ℂ) • 1) ^ n)) : x ∈ hwSub act μ := by
  refine mem_hw.2 ⟨mem_wt.1 hx.2, fun a b hab => ?_⟩
  by_contra hne
  set Y := W ⊓ LinearMap.ker ((casK act - ((casVal μ : ℚ) : ℂ) • 1) ^ n) with hY
  have hYs : KStable act Y := stable_inf hW (stable_ker hL _ _)
  haveI : FiniteDimensional ℂ Y := Submodule.finiteDimensional_of_le inf_le_left
  obtain ⟨ν, h1, h2, h3⟩ := exists_max hL hYs ⊥ (fun ν => Below μ ν)
    (fun ν c d hcd h l hl => by
      rw [pair_root]; linarith [h l hl, hl c d hcd])
    ⟨μ + root a b, fun l hl => by rw [pair_root]; linarith [hl a b hab], fun hle =>
      hne (hle ⟨hYs _ (isKC_Eab (same_of_pos hab)) _ ⟨hx.1, hk⟩, shift hL (same_of_pos hab) hx.2⟩)⟩
  obtain ⟨w, hw, h0⟩ := SetLike.not_le_iff_exists.1 h2
  have hhw : IsHW act ν w := ⟨h0, mem_hw.2 ⟨mem_wt.1 hw.2, h3 w hw⟩⟩
  exact (casVal_lt (fun c d hcd => hw_dominant hL hYs hw.1 hhw hcd) hμ h1).ne'
    (casVal_of_ker hL hhw hw.1.2)

lemma le_of_hw (hL : IsKLieAct act) {W : Submodule ℂ V} [FiniteDimensional ℂ W] (hW : KStable act W)
    (hd : ∀ v ∈ W, v ∈ ⨆ μ, wtSub act μ) {S : Submodule ℂ V} (hS : KStable act S)
    (h : ∀ μ v, v ∈ W → IsHW act μ v → v ∈ S) : W ≤ S := by
  by_contra hn
  obtain ⟨μ, -, h2, h3⟩ := exists_max hL hW S (fun _ => True) (fun _ _ _ _ _ => trivial) (by
    by_contra hh
    push Not at hh
    exact hn fun x hx => (iSup_le fun μ => hh μ trivial : (⨆ μ, W ⊓ wtSub act μ) ≤ S)
      (decomp hW hx (hd x hx)))
  obtain ⟨x, hx, hxS⟩ := SetLike.not_le_iff_exists.1 h2
  have hμ : ∀ a b, posC a b → ∃ k : ℕ, μ a - μ b = k := fun a b hab =>
    dominant hL hW hS hx hxS hab (h3 x hx a b hab)
  set Y := W ⊓ wtSub act μ with hY
  haveI : FiniteDimensional ℂ Y := Submodule.finiteDimensional_of_le inf_le_left
  set T : Module.End ℂ V := casK act - ((casVal μ : ℚ) : ℂ) • 1 with hT
  have hTY : ∀ y ∈ Y, T y ∈ Y := fun y hy =>
    Y.sub_mem ⟨casK_mem hW hy.1, casK_wt hL hy.2⟩ (Y.smul_mem _ hy)
  have hTS : ∀ y ∈ Y, T y ∈ S := fun y hy => casK_mod hL hS hy.2 (h3 y hy)
  obtain ⟨n, hc, hn1⟩ := ((LinearMap.eventually_codisjoint_ker_pow_range_pow (T.restrict hTY)).and
    (Filter.eventually_ge_atTop 1)).exists
  have hm : (⟨x, hx⟩ : Y) ∈ LinearMap.ker (T.restrict hTY ^ n) ⊔ LinearMap.range (T.restrict hTY ^ n) := by
    rw [codisjoint_iff.1 hc]; trivial
  obtain ⟨y, hy, z, ⟨t, rfl⟩, hyz⟩ := Submodule.mem_sup.1 hm
  have hz : ((T.restrict hTY ^ n) t : V) ∈ S := by
    obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le' hn1
    rw [pow_succ', Module.End.mul_apply]
    exact hTS _ (Subtype.prop _)
  have hy' : (y : V) ∈ hwSub act μ := by
    refine hw_of_ker hL hW hμ y.2 (n := n) ?_
    rw [LinearMap.mem_ker, Module.End.pow_restrict] at hy
    exact congrArg Subtype.val hy
  have hyS : (y : V) ∈ S := by
    by_cases h0 : (y : V) = 0
    · rw [h0]; exact S.zero_mem
    · exact h μ y y.2.1 ⟨h0, hy'⟩
  have := S.add_mem hyS hz
  rw [← Submodule.coe_add, hyz] at this
  exact hxS this

def gen (act : Mat p q →ₗ[ℂ] Module.End ℂ V) (v : V) : Submodule ℂ V :=
  sInf {N | v ∈ N ∧ KStable act N}

lemma mem_gen (v : V) : v ∈ gen act v := Submodule.mem_sInf.2 fun _ h => h.1

lemma stable_gen (v : V) : KStable act (gen act v) := fun Z hZ w hw =>
  Submodule.mem_sInf.2 fun M hM => hM.2 Z hZ w (Submodule.mem_sInf.1 hw M hM)

lemma gen_le {v : V} {N : Submodule ℂ V} (hv : v ∈ N) (hN : KStable act N) : gen act v ≤ N :=
  sInf_le ⟨hv, hN⟩

lemma gen_le_of_lower (hL : IsKLieAct act) {μ : Ix p q → ℚ} {v : V}
    (hv : v ∈ hwSub act μ) (N : Submodule ℂ V)
    (hvN : v ∈ N) (hN : ∀ a b, posC a b → ∀ y ∈ N, act (Eab b a) y ∈ N) : gen act v ≤ N := by
  rw [mem_hw] at hv
  set S : Set (Submodule ℂ V) :=
    {N | v ∈ N ∧ ∀ a b, posC a b → ∀ y ∈ N, act (Eab b a) y ∈ N} with hS
  have hG : sInf S ∈ S := by
    refine ⟨Submodule.mem_sInf.2 fun M hM => hM.1, fun a b hab y hy => ?_⟩
    exact Submodule.mem_sInf.2 fun M hM => hM.2 a b hab y (Submodule.mem_sInf.1 hy M hM)
  have hG' : (sInf S ⊓ ⨅ (Z : Mat p q) (_ : IsKC Z), (sInf S).comap (act Z)) ∈ S := by
    constructor
    · simp only [Submodule.mem_inf, Submodule.mem_iInf, Submodule.mem_comap]
      refine ⟨hG.1, fun Z hZ => kc_ind act _ v (fun a b hab => ?_) hZ⟩
      rcases same_tri hab with rfl | h | h
      · rw [hv.1]; exact Submodule.smul_mem _ _ hG.1
      · rw [hv.2 a b h]; exact Submodule.zero_mem _
      · exact hG.2 b a h v hG.1
    · intro a b hab y hy
      simp only [Submodule.mem_inf, Submodule.mem_iInf, Submodule.mem_comap] at hy ⊢
      refine ⟨hG.2 a b hab y hy.1, fun Z hZ => ?_⟩
      have hE := isKC_Eab (same_of_pos' hab)
      rw [lie_apply hL hZ hE]
      exact Submodule.add_mem _ (hG.2 a b hab _ (hy.2 Z hZ)) (hy.2 _ (isKC_comm hZ hE))
  have hK : KStable act (sInf S) := by
    intro Z hZ w hw
    have := sInf_le hG' hw
    simp only [Submodule.mem_inf, Submodule.mem_iInf, Submodule.mem_comap] at this
    exact this.2 Z hZ
  exact (gen_le hG.1 hK).trans (sInf_le (show N ∈ S from ⟨hvN, hN⟩))

lemma hw_unique (hL : IsKLieAct act) {W : Submodule ℂ V} [FiniteDimensional ℂ W] (hW : KStable act W)
    {μ ν : Ix p q → ℚ} {v w : V} (hvW : v ∈ W) (hv : IsHW act μ v) (hwv : w ∈ gen act v)
    (hw : IsHW act ν w) : ν = μ ∧ w ∈ ℂ ∙ v := by
  set Q : Submodule ℂ V := ⨆ (κ : Ix p q → ℚ) (_ : Below κ μ), wtSub act κ with hQ
  have hin : ∀ κ, Below κ μ → wtSub act κ ≤ Q := fun κ hκ =>
    le_iSup₂_of_le (f := fun (κ : Ix p q → ℚ) (_ : Below κ μ) => wtSub act κ) κ hκ le_rfl
  have hle : gen act v ≤ (ℂ ∙ v) ⊔ Q := by
    refine gen_le_of_lower hL hv.2 _ (Submodule.mem_sup_left (Submodule.mem_span_singleton_self v))
      fun a b hab y hy => Submodule.mem_sup_right ?_
    have : (ℂ ∙ v) ⊔ Q ≤ Q.comap (act (Eab b a)) := by
      refine sup_le ?_ (iSup₂_le fun κ hκ x hx => ?_)
      · rw [Submodule.span_singleton_le_iff_mem]
        refine hin _ (fun l hl => ?_) (shift hL (same_of_pos' hab) hv.2.1)
        rw [pair_root]; linarith [hl a b hab]
      · refine hin _ (fun l hl => ?_) (shift hL (same_of_pos' hab) hx)
        rw [pair_root]; linarith [hl a b hab, hκ l hl]
    exact this hy
  have hc : casVal ν = casVal μ := by
    refine casVal_of_ker hL hw (n := 1) (gen_le ?_ (stable_ker hL _ _) hwv)
    simp [casK_hw hL hv.2]
  have hnb : ¬ Below ν μ := fun h =>
    (casVal_lt (fun a b hab => hw_dominant hL hW hvW hv hab)
      (fun a b hab => hw_dominant hL hW (gen_le hvW hW hwv) hw hab) h).ne hc
  have hQle : Q ≤ ⨆ (κ : Ix p q → ℚ) (_ : κ ≠ ν), wtSub act κ :=
    iSup₂_le fun κ hκ => le_iSup₂_of_le (f := fun (κ : Ix p q → ℚ) (_ : κ ≠ ν) => wtSub act κ) κ
      (by rintro rfl; exact hnb hκ) le_rfl
  have hsp : (ℂ ∙ v) ≤ wtSub act μ := (Submodule.span_singleton_le_iff_mem _ _).2 hv.2.1
  have hνμ : ν = μ := by
    by_contra hne
    refine hw.1 (Submodule.disjoint_def.1 (wt_indep (act := act) ν) w hw.2.1 (sup_le ?_ hQle (hle hwv)))
    exact hsp.trans (le_iSup₂_of_le (f := fun (κ : Ix p q → ℚ) (_ : κ ≠ ν) => wtSub act κ) μ
      (Ne.symm hne) le_rfl)
  subst hνμ
  refine ⟨rfl, ?_⟩
  obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.1 (hle hwv)
  have : z = 0 := Submodule.disjoint_def.1 (wt_indep (act := act) ν) z
    ((Submodule.add_mem_iff_right _ (hsp hy)).1 hw.2.1) (hQle hz)
  simpa [this] using hy

lemma exists_hw (hL : IsKLieAct act) {W : Submodule ℂ V} [FiniteDimensional ℂ W] (hW : KStable act W)
    (hd : ∀ v ∈ W, v ∈ ⨆ μ, wtSub act μ) (h : W ≠ ⊥) : ∃ μ v, v ∈ W ∧ IsHW act μ v := by
  by_contra hn
  push Not at hn
  exact h (le_bot_iff.1 (le_of_hw hL hW hd stable_bot fun μ v hv hh => (hn μ v hv hh).elim))

lemma gen_irred (hL : IsKLieAct act) {W : Submodule ℂ V} [FiniteDimensional ℂ W] (hW : KStable act W)
    (hd : ∀ v ∈ W, v ∈ ⨆ μ, wtSub act μ) {μ : Ix p q → ℚ} {v : V} (hvW : v ∈ W) (hv : IsHW act μ v)
    (U : Submodule ℂ V) (hU : KStable act U) (hle : U ≤ gen act v) : U = ⊥ ∨ v ∈ U := by
  rw [or_iff_not_imp_left]
  intro h0
  have hUW : U ≤ W := hle.trans (gen_le hvW hW)
  haveI : FiniteDimensional ℂ U := Submodule.finiteDimensional_of_le hUW
  obtain ⟨ν, w, hwU, hw⟩ := exists_hw hL hU (fun x hx => hd x (hUW hx)) h0
  obtain ⟨s, rfl⟩ := Submodule.mem_span_singleton.1 (hw_unique hL hW hvW hv (hle hwU) hw).2
  exact (U.smul_mem_iff (left_ne_zero_of_smul hw.1)).1 hwU

lemma ofType_hw (hL : IsKLieAct act) {W : Submodule ℂ V} [FiniteDimensional ℂ W] (hW : KStable act W)
    {μ : Ix p q → ℚ} {v : V} (hvW : v ∈ W) (hv : IsHW act μ v) : OfType act μ v :=
  ⟨gen act v, Submodule.finiteDimensional_of_le (gen_le hvW hW), mem_gen v, stable_gen v,
    fun _ _ hw hh => (hw_unique hL hW hvW hv hw hh).1⟩

lemma exists_max_image_of_bddAbove_finrank (W : Submodule ℂ V) [FiniteDimensional ℂ W]
    (P : Submodule ℂ V → Prop) (h : P ⊥) :
    ∃ U, (U ≤ W ∧ P U) ∧ ∀ U', U' ≤ W → U ≤ U' → P U' → U' ≤ U := by
  obtain ⟨A, hA, hmax⟩ := (wellFounded_gt (α := Submodule ℂ W)).has_min
    {A | P (A.map W.subtype)} ⟨⊥, by simpa using h⟩
  refine ⟨A.map W.subtype, ⟨Submodule.map_subtype_le _ _, hA⟩, fun U' h1 h2 h3 => ?_⟩
  have e : (U'.comap W.subtype).map W.subtype = U' := by
    rw [Submodule.map_comap_subtype, inf_eq_right.2 h1]
  have h4 : A ≤ U'.comap W.subtype := Submodule.map_le_iff_le_comap.1 h2
  have h5 := hmax (U'.comap W.subtype) (by rw [Set.mem_setOf_eq, e]; exact h3)
  rw [← e]
  exact Submodule.map_mono (eq_of_le_of_not_lt h4 h5).ge

lemma exists_compl (hL : IsKLieAct act) {W : Submodule ℂ V} [FiniteDimensional ℂ W] (hW : KStable act W)
    (hd : ∀ v ∈ W, v ∈ ⨆ μ, wtSub act μ) (U : Submodule ℂ V) (hUW : U ≤ W) (hU : KStable act U) :
    ∃ U' : Submodule ℂ V, KStable act U' ∧ U ⊓ U' = ⊥ ∧ U ⊔ U' = W := by
  obtain ⟨U', ⟨h1, h2, h3⟩, hmax⟩ := exists_max_image_of_bddAbove_finrank W
    (fun U' => KStable act U' ∧ Disjoint U U') ⟨stable_bot, disjoint_bot_right⟩
  refine ⟨U', h2, h3.eq_bot, le_antisymm (sup_le hUW h1)
    (le_of_hw hL hW hd (stable_sup hU h2) fun μ v hvW hv => ?_)⟩
  rcases gen_irred hL hW hd hvW hv ((U ⊔ U') ⊓ gen act v)
    (stable_inf (stable_sup hU h2) (stable_gen v)) inf_le_right with h | h
  · have := hmax (U' ⊔ gen act v) (sup_le h1 (gen_le hvW hW)) le_sup_left
      ⟨stable_sup h2 (stable_gen v), h3.disjoint_sup_right_of_disjoint_sup_left (disjoint_iff.2 h)⟩
    exact Submodule.mem_sup_right (this (Submodule.mem_sup_right (mem_gen v)))
  · exact h.1

theorem finite_module_structure : ∀ (p q : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (act : Mat p q →ₗ[ℂ] Module.End ℂ V), IsKLieAct act → ∀ W : Submodule ℂ V, FiniteDimensional ℂ W → KStable act W → (∀ v ∈ W, v ∈ ⨆ μ : Ix p q → ℚ, wtSub act μ) → (∀ U : Submodule ℂ V, U ≤ W → KStable act U → ∃ U' : Submodule ℂ V, KStable act U' ∧ U ⊓ U' = ⊥ ∧ U ⊔ U' = W) ∧ (W ≠ ⊥ → ∃ μ v, v ∈ W ∧ IsHW act μ v) ∧ (∀ v ∈ W, v ∈ ⨆ μ : Ix p q → ℚ, Submodule.span ℂ {w | w ∈ W ∧ OfType act μ w}) ∧ (∀ μ v, v ∈ W → IsHW act μ v → (∀ a b, posC a b → ∃ k : ℕ, μ a - μ b = k) ∧ OfType act μ v ∧ ∀ U : Submodule ℂ V, KStable act U → U ≤ sInf {N | v ∈ N ∧ KStable act N} → U = ⊥ ∨ v ∈ U) := by
  intro p q V _ _ act hL W _ hW hd
  refine ⟨exists_compl hL hW hd, exists_hw hL hW hd, ?_, fun μ v hvW hv =>
    ⟨fun a b hab => hw_dominant hL hW hvW hv hab, ofType_hw hL hW hvW hv, gen_irred hL hW hd hvW hv⟩⟩
  refine le_of_hw hL hW hd (fun Z hZ => ?_) fun μ v hvW hv =>
    Submodule.mem_iSup_of_mem μ (Submodule.subset_span ⟨hvW, ofType_hw hL hW hvW hv⟩)
  refine (iSup_le fun μ => Submodule.span_le.2 ?_ :
    (⨆ μ : Ix p q → ℚ, Submodule.span ℂ {w | w ∈ W ∧ OfType act μ w}) ≤
      (⨆ μ : Ix p q → ℚ, Submodule.span ℂ {w | w ∈ W ∧ OfType act μ w}).comap (act Z))
  rintro w ⟨hwW, M, h1, h2, h3, h4⟩
  exact Submodule.mem_iSup_of_mem μ (Submodule.subset_span ⟨hW Z hZ w hwW, M, h1, h3 Z hZ w h2, h3, h4⟩)

end GlobalTheory.BlockReps
