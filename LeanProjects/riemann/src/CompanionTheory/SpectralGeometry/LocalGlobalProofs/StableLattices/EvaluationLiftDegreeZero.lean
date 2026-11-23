import Mathlib
import CompanionTheory.RealGroups.DiscreteSeries.DiscreteSeriesClassification.DiscreteSeriesExhaustion.FarRegularity.LKTExists
import CompanionTheory.HarishChandraModules.LowKTypeMultiplicity.EigenspaceCyclicDensity.LowKTypeMultiplicityOneUnconditional
import CompanionTheory.HarishChandraModules.LowKTypeMultiplicity.EigenspaceCyclicDensity.CreationOperators.DifferentialCommutesWeightOperator

open Finset

noncomputable section

namespace GlobalTheory.CompanionTheory.GenCOUP

open CompanionTheory.RgExh.U CompanionTheory.D.LK CompanionTheory.D.LK.Car
open Formalism.REAL (GlRel)
open CompanionTheory.D.DSIC (KRel)

variable {n : ℕ} {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

theorem deg_of (j : ℕ) {x : Cn n V} {y : Cn n W} (hx : CompanionTheory.RgExh.U.Deg j x) (h : ∀ A, x A = 0 → y A = 0) :
    CompanionTheory.RgExh.U.Deg j y := fun A hA => hx A fun h0 => hA (h A h0)

theorem supp_of {P : Pos n → Prop} {x : Cn n V} {y : Cn n W} (hx : SuppIn P x) (h : ∀ A, x A = 0 → y A = 0) :
    SuppIn P y := fun A hA => hx A fun h0 => hA (h A h0)

theorem deg_add {j : ℕ} {x y : Cn n V} (hx : CompanionTheory.RgExh.U.Deg j x) (hy : CompanionTheory.RgExh.U.Deg j y) :
    CompanionTheory.RgExh.U.Deg j (x + y) := fun A hA => by
  by_cases h : x A = 0
  · exact hy A fun h' => hA (by simp [h, h'])
  · exact hx A h

theorem supp_add {P : Pos n → Prop} {x y : Cn n V} (hx : SuppIn P x) (hy : SuppIn P y) :
    SuppIn P (x + y) := fun A hA => by
  by_cases h : x A = 0
  · exact hy A fun h' => hA (by simp [h, h'])
  · exact hx A h

theorem deg_sub {j : ℕ} {x y : Cn n V} (hx : CompanionTheory.RgExh.U.Deg j x) (hy : CompanionTheory.RgExh.U.Deg j y) :
    CompanionTheory.RgExh.U.Deg j (x - y) := fun A hA => by
  by_cases h : x A = 0
  · exact hy A fun h' => hA (by simp [h, h'])
  · exact hx A h

theorem supp_sub {P : Pos n → Prop} {x y : Cn n V} (hx : SuppIn P x) (hy : SuppIn P y) :
    SuppIn P (x - y) := fun A hA => by
  by_cases h : x A = 0
  · exact hy A fun h' => hA (by simp [h, h'])
  · exact hx A h

theorem deg_iff (j : ℕ) (x : Cn n V) : CompanionTheory.RgExh.U.Deg j x ↔ CompanionTheory.D.LK.Sup (allT n) ∅ j x := by
  constructor
  · intro h A hA
    refine ⟨filter_false_of_mem fun i _ hc => hc rfl, ?_⟩
    rw [filter_true_of_mem fun i _ => rfl]
    exact h A hA
  · intro h A hA
    have := (h A hA).2
    rwa [filter_true_of_mem fun i _ => rfl] at this

theorem bd_deg (E : Fin n → Fin n → Module.End ℂ V) {j : ℕ} {x : Cn n V} (h : CompanionTheory.RgExh.U.Deg (j + 1) x) :
    CompanionTheory.RgExh.U.Deg j (bd (allT n) E x) :=
  (deg_iff _ _).2 ((differential_bounded_support n (allT n) V E).1 ∅ j x ((deg_iff _ _).1 h))

theorem bd_supp (lev : Fin n → ℕ) (E : Fin n → Fin n → Module.End ℂ V) {x : Cn n V}
    (h : SuppIn (inU lev) x) : SuppIn (inU lev) (bd (allT n) E x) := by
  intro A hA i hi
  rcases bd_ne (allT n) E x A hA with ⟨i', _, h1⟩ | ⟨i', j, k, ht, h1⟩
  · exact h _ (ann_ne h1).2 i (mem_insert_of_mem hi)
  · obtain ⟨h2, h3, h4, h5⟩ := tri_ne h1
    by_cases hk : i = k
    · subst hk
      obtain ⟨-, -, t1, t2, t3⟩ := ht
      have u1 : inU lev i' := h _ h5 i' (mem_insert_self _ _)
      have u2 : inU lev j := h _ h5 j (mem_insert_of_mem (mem_insert_self _ _))
      show lev i.1.1 < lev i.1.2
      rw [t2, t3]
      have : lev i'.1.2 = lev j.1.1 := by rw [t1]
      have u1' : lev i'.1.1 < lev i'.1.2 := u1
      have u2' : lev j.1.1 < lev j.1.2 := u2
      omega
    · exact h _ h5 i (mem_insert_of_mem (mem_insert_of_mem (mem_erase.2 ⟨hk, hi⟩)))

theorem lift_adL (φ : V →ₗ[ℂ] W) (p q : Fin n) (x : Cn n V) :
    lift n φ (adL p q x) = adL p q (lift n φ x) := by
  simp only [adL, LinearMap.sum_apply, LinearMap.smul_apply, Module.End.mul_apply, map_sum, map_smul, lift_cre,
    lift_ann]

theorem lift_lF (φ : V →ₗ[ℂ] W) (E : Fin n → Fin n → Module.End ℂ V) (F : Fin n → Fin n → Module.End ℂ W)
    (h : ∀ a b x, φ (E a b x) = F a b (φ x)) (p q : Fin n) (x : Cn n V) :
    lift n φ (lF E p q x) = lF F p q (lift n φ x) := by
  simp only [lF, LinearMap.add_apply, map_add, lift_adL]
  congr 1
  funext A
  simp [h]

theorem lift_evLc (lev : Fin n → ℕ) (φ : V →ₗ[ℂ] W) (E : Fin n → Fin n → Module.End ℂ V)
    (F : Fin n → Fin n → Module.End ℂ W) (h : ∀ a b x, φ (E a b x) = F a b (φ x))
    (b : FreeAlgebra ℂ (Fin n × Fin n)) (x : Cn n V) :
    lift n φ (evLc lev E b x) = evLc lev F b (lift n φ x) :=
  free_inter (lift n φ) _ _ (fun p y => by
    split_ifs
    · exact lift_lF φ E F h _ _ y
    · simp) b x

theorem lift_ev (φ : V →ₗ[ℂ] W) (E : Fin n → Fin n → Module.End ℂ V)
    (F : Fin n → Fin n → Module.End ℂ W) (h : ∀ a b x, φ (E a b x) = F a b (φ x))
    (a : FreeAlgebra ℂ (Fin n × Fin n)) (z : Cn n V) :
    lift n φ (lift n (ev E a) z) = lift n (ev F a) (lift n φ z) := by
  funext A
  exact free_inter φ _ _ (fun p y => h p.1 p.2 y) a _

theorem bd_lift_comm (lev : Fin n → ℕ) (E : Fin n → Fin n → Module.End ℂ V) (T : Module.End ℂ V)
    (hT : ∀ i : Pos n, inU lev i → Commute (E i.1.1 i.1.2) T) {x : Cn n V} (hx : SuppIn (inU lev) x) :
    bd (allT n) E (lift n T x) = lift n T (bd (allT n) E x) := by
  funext A
  rw [lift_apply, bd_apply, bd_apply, map_add, map_sum, map_sum]
  congr 1
  · refine Finset.sum_congr rfl fun i _ => ?_
    rw [if_pos rfl, if_pos rfl]
    by_cases hi : inU lev i
    · have e : ann i (lift n T x) A = T (ann i x A) := congrFun (lift_ann T i x).symm A
      rw [e]
      exact (LinearMap.congr_fun (hT i hi).eq _)
    · have e : ann i x A = 0 := by
        by_contra h0
        exact hi (hx _ (ann_ne h0).2 i (mem_insert_self _ _))
      have e' : ann i (lift n T x) A = 0 := by
        rw [show ann i (lift n T x) A = T (ann i x A) from congrFun (lift_ann T i x).symm A, e, map_zero]
      rw [e, e', map_zero, map_zero]
  · refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    split_ifs
    · rw [← lift_ann, ← lift_ann, ← lift_cre]; rfl
    · exact (map_zero _).symm

theorem adC_U {lev : Fin n → ℕ} {p q : Fin n} (hpq : lev p = lev q) {i k : Pos n} (hi : inU lev i)
    (h : adC p q i k ≠ 0) : inU lev k := by
  have hi' : lev i.1.1 < lev i.1.2 := hi
  show lev k.1.1 < lev k.1.2
  by_cases h1 : q = i.1.1 ∧ k.1 = (p, i.1.2)
  · rw [h1.2]; simp only []; rw [hpq, h1.1]; exact hi'
  · by_cases h2 : i.1.2 = p ∧ k.1 = (i.1.1, q)
    · rw [h2.2]; simp only []; rw [← hpq, ← h2.1]; exact hi'
    · exact absurd (by simp [adC, h1, h2]) h

theorem adL_apply (p q : Fin n) (x : Cn n V) (A : Finset (Pos n)) :
    adL p q x A = ∑ i : Pos n, ∑ k : Pos n, adC p q i k • cre k (ann i x) A := by
  simp only [adL, LinearMap.sum_apply, LinearMap.smul_apply, Module.End.mul_apply, Finset.sum_apply, Pi.smul_apply]

theorem adL_ne {p q : Fin n} {x : Cn n V} {A : Finset (Pos n)} (h : adL p q x A ≠ 0) :
    ∃ i k, adC p q i k ≠ 0 ∧ k ∈ A ∧ i ∉ A.erase k ∧ x (insert i (A.erase k)) ≠ 0 := by
  rw [adL_apply] at h
  obtain ⟨i, -, hi⟩ := exists_ne_zero_of_sum_ne_zero h
  obtain ⟨k, -, hk⟩ := exists_ne_zero_of_sum_ne_zero hi
  have h1 : adC p q i k ≠ 0 := fun e => hk (by rw [e, zero_smul])
  have h2 : cre k (ann i x) A ≠ 0 := fun e => hk (by rw [e, smul_zero])
  obtain ⟨h3, h4⟩ := cre_ne h2
  obtain ⟨h5, h6⟩ := ann_ne h4
  exact ⟨i, k, h1, h3, h5, h6⟩

theorem lF_supp {lev : Fin n → ℕ} (E : Fin n → Fin n → Module.End ℂ V) {p q : Fin n} (hpq : lev p = lev q)
    {x : Cn n V} (hx : SuppIn (inU lev) x) : SuppIn (inU lev) (lF E p q x) := by
  intro A hA l hl
  by_cases h : x A = 0
  · have h2 : adL p q x A ≠ 0 := fun e => hA (by simp [lF, h, e])
    obtain ⟨i, k, h3, h4, h5, h6⟩ := adL_ne h2
    by_cases hk : l = k
    · subst hk
      exact adC_U hpq (hx _ h6 i (mem_insert_self _ _)) h3
    · exact hx _ h6 l (mem_insert_of_mem (mem_erase.2 ⟨hk, hl⟩))
  · by_cases h2 : adL p q x A = 0
    · exact hx A h l hl
    · obtain ⟨i, k, h3, h4, h5, h6⟩ := adL_ne h2
      by_cases hk : l = k
      · subst hk
        exact adC_U hpq (hx _ h6 i (mem_insert_self _ _)) h3
      · exact hx _ h6 l (mem_insert_of_mem (mem_erase.2 ⟨hk, hl⟩))

theorem lF_deg (E : Fin n → Fin n → Module.End ℂ V) (p q : Fin n) {j : ℕ} {x : Cn n V}
    (hx : CompanionTheory.RgExh.U.Deg j x) : CompanionTheory.RgExh.U.Deg j (lF E p q x) := by
  intro A hA
  by_cases h : x A = 0
  · have h2 : adL p q x A ≠ 0 := fun e => hA (by simp [lF, h, e])
    obtain ⟨i, k, h3, h4, h5, h6⟩ := adL_ne h2
    have := hx _ h6
    rw [card_insert_of_notMem h5, card_erase_of_mem h4] at this
    have : 0 < A.card := card_pos.2 ⟨k, h4⟩
    omega
  · exact hx A h

theorem adjoint_left_degree_zero (p q : Fin n) {x : Cn n V} (hx : CompanionTheory.RgExh.U.Deg 0 x) : adL p q x = 0 := by
  funext A
  by_contra h
  obtain ⟨i, k, h3, h4, h5, h6⟩ := adL_ne h
  have := hx _ h6
  rw [card_insert_of_notMem h5] at this
  omega

theorem evaluation_lift_degree_zero (lev : Fin n → ℕ) (E : Fin n → Fin n → Module.End ℂ V) (b : FreeAlgebra ℂ (Fin n × Fin n)) :
    ∀ x : Cn n V, CompanionTheory.RgExh.U.Deg 0 x → CompanionTheory.RgExh.U.Deg 0 (evLc lev E b x) ∧
      evLc lev E b x = lift n (evL lev E b) x := by
  induction b using FreeAlgebra.induction with
  | grade0 r =>
    intro x hx
    simp only [AlgHom.commutes, Module.algebraMap_end_apply]
    refine ⟨deg_of 0 hx fun A h => by simp [h], by funext A; simp [Module.algebraMap_end_apply]⟩
  | grade1 c =>
    intro x hx
    simp only [evLc, evL, FreeAlgebra.lift_ι_apply]
    split_ifs
    · refine ⟨lF_deg E _ _ hx, ?_⟩
      simp [lF, adjoint_left_degree_zero _ _ hx]
    · refine ⟨fun A h => absurd rfl h, ?_⟩
      funext A; simp
  | mul a b ha hb =>
    intro x hx
    obtain ⟨h1, h2⟩ := hb x hx
    obtain ⟨h3, h4⟩ := ha _ h1
    simp only [map_mul, Module.End.mul_apply]
    refine ⟨h3, ?_⟩
    rw [h4, h2]; funext A; simp
  | add a b ha hb =>
    intro x hx
    obtain ⟨h1, h2⟩ := ha x hx
    obtain ⟨h3, h4⟩ := hb x hx
    simp only [map_add, LinearMap.add_apply]
    refine ⟨deg_add h1 h3, ?_⟩
    rw [h2, h4]; funext A; simp

section Acyc

variable {Z : Type} [AddCommGroup Z] [Module ℂ Z]

theorem acycU (lev : Fin n → ℕ) (E : Fin n → Fin n → Module.End ℂ Z) (a d : Pos n → Module.End ℂ Z)
    (Fil : ℕ → Submodule ℂ Z) (hE : GlRel E) (hF : Filt (inU lev) E a d Fil) (j : ℕ) (x : Cn n Z)
    (hxs : SuppIn (inU lev) x) (hxd : CompanionTheory.RgExh.U.Deg (j + 1) x) (hcyc : bd (allT n) E x = 0) :
    ∃ t : Cn n Z, SuppIn (inU lev) t ∧ CompanionTheory.RgExh.U.Deg (j + 2) t ∧ bd (allT n) E t = x := by
  let I := {i : Pos n // inU lev i}
  have hS : bd (allT n) E * bd (allT n) E = 0 := koszul_differential_sq_zero n (allT n) Z E fun a b c d _ _ => hE a b c d
  let H : Module.End ℂ (Cn n Z) := ∑ i : I, (lift n (d i.1) : Module.End ℂ (Cn n Z)) * cre i.1
  let Da : Module.End ℂ (Cn n Z) := ∑ i : I, (lift n (a i.1) : Module.End ℂ (Cn n Z)) * ann i.1
  let N : Module.End ℂ Z := ∑ i : I, a i.1 * d i.1
  let G : ℕ → Submodule ℂ Z := fun k => Nat.casesOn k ⊥ Fil
  have hda : ∀ i j : I, d i.1 * a j.1 - a j.1 * d i.1 = if i = j then 1 else 0 := fun i j => by
    rw [hF.da i.1 j.1 i.2]; simp only [Subtype.ext_iff (a1 := i)]
  have hdG : ∀ i k, ∀ z ∈ G (k + 1), d i z ∈ G k := fun i k z hz => by
    cases k with
    | zero => exact hF.d_zero i z hz
    | succ k => exact hF.d_mem i k z hz
  have hNG : ∀ k, ∀ z ∈ G k, N z ∈ G k := fun k z hz => by
    cases k with
    | zero => obtain rfl : z = 0 := hz; simp
    | succ k =>
      rw [LinearMap.sum_apply]
      refine Submodule.sum_mem _ fun i _ => ?_
      cases k with
      | zero => rw [Module.End.mul_apply, hF.d_zero _ z hz, map_zero]; exact Submodule.zero_mem _
      | succ k => exact hF.a_mem _ k _ (hF.d_mem _ k z hz)
  have hrG : ∀ i k, ∀ z ∈ G k, E i.1.1 i.1.2 z - a i z ∈ G k := fun i k z hz => by
    cases k with
    | zero => obtain rfl : z = 0 := hz; simp
    | succ k => exact hF.r_mem i k z hz
  have hGf : ∀ k, G k ≤ GlobalTheory.CompanionTheory.DSICKoszul.filt (fun i : I => d i.1) k := fun k => by
    induction k with
    | zero => exact bot_le
    | succ k ih => exact fun z hz => (GlobalTheory.CompanionTheory.DSICKoszul.mem_filt_succ _ _ _).2 fun i => ih (hdG _ k z hz)
  have hGm : ∀ k, G k ≤ G (k + 1) := fun k => by
    cases k with
    | zero => exact bot_le
    | succ k => exact hF.mono (Nat.le_succ k)
  have hH : ∀ (y : Cn n Z) A, H y A = ∑ i : I, d i.1 (cre i.1 y A) := fun y A => by
    simp only [H, LinearMap.sum_apply, Finset.sum_apply]; rfl
  have hHG : ∀ k (y : Cn n Z), (∀ A, y A ∈ G (k + 1)) → ∀ A, H y A ∈ G k := fun k y hy A => by
    rw [hH]; exact Submodule.sum_mem _ fun i _ => hdG _ k _ (cre_mem hy _ _)
  have hρ : ∀ k (y : Cn n Z), (∀ A, y A ∈ G k) → SuppIn (inU lev) y → ∀ A, (bd (allT n) E y - Da y) A ∈ G k :=
      fun k y hy hys A => by
    have e : Da y A = ∑ i : Pos n, if inU lev i then a i (ann i y A) else 0 := by
      rw [← Finset.sum_filter, Finset.sum_subtype (p := inU lev) _ (by simp)]
      simp only [Da, LinearMap.sum_apply, Finset.sum_apply]; rfl
    rw [Pi.sub_apply, bd_apply, e, add_sub_right_comm, ← Finset.sum_sub_distrib]
    refine Submodule.add_mem _ (Submodule.sum_mem _ fun i _ => ?_) (Submodule.sum_mem _ fun i _ =>
      Submodule.sum_mem _ fun j _ => Submodule.sum_mem _ fun k _ => ?_)
    · rw [if_pos rfl]
      by_cases hi : inU lev i
      · rw [if_pos hi]
        exact hrG i _ _ (ann_mem hy _ _)
      · have e0 : ann i y A = 0 := by
          by_contra h0
          exact hi (hys _ (ann_ne h0).2 i (mem_insert_self _ _))
        rw [if_neg hi, e0]
        simp
    · split_ifs
      · exact cre_mem (ann_mem (ann_mem hy _) _) _ _
      · exact Submodule.zero_mem _
  have hom : Da * H + H * Da =
      ∑ i : I, (lift n (a i.1) : Module.End ℂ (Cn n Z)) * lift n (d i.1) + ∑ i : I, cre i.1 * ann i.1 := by
    refine GlobalTheory.CompanionTheory.DSICKoszul.homotopy_ring (fun i : I => (lift n (a i.1) : Module.End ℂ (Cn n Z))) (fun i => lift n (d i.1))
      (fun i => ann i.1) (fun i => cre i.1) (fun i j => LinearMap.ext fun y => (lift_ann _ _ y).symm)
      (fun i j => LinearMap.ext fun y => (lift_cre _ _ y).symm) (fun i j => ?_) (fun i j => ?_)
    · refine LinearMap.ext fun y => funext fun A => ?_
      have e := congrArg (fun T : Module.End ℂ Z => T (y A)) (hda i j)
      by_cases h : i = j
      · simpa [h] using e
      · simpa [h] using e
    · rw [ann_cre]; simp only [Subtype.ext_iff (a1 := i)]
  have hHs : ∀ y : Cn n Z, SuppIn (inU lev) y → CompanionTheory.RgExh.U.Deg (j + 1) y →
      SuppIn (inU lev) (H y) ∧ CompanionTheory.RgExh.U.Deg (j + 2) (H y) := fun y hys hyd => by
    have key : ∀ A, H y A ≠ 0 → ∃ i : I, i.1 ∈ A ∧ y (A.erase i.1) ≠ 0 := fun A hA => by
      rw [hH] at hA
      obtain ⟨i, -, hi⟩ := exists_ne_zero_of_sum_ne_zero hA
      exact ⟨i, cre_ne (fun h => hi (by rw [h, map_zero]) : cre i.1 y A ≠ 0)⟩
    refine ⟨fun A hA l hl => ?_, fun A hA => ?_⟩
    · obtain ⟨i, h1, h2⟩ := key A hA
      by_cases e : l = i.1
      · exact e ▸ i.2
      · exact hys _ h2 l (mem_erase.2 ⟨e, hl⟩)
    · obtain ⟨i, h1, h2⟩ := key A hA
      have := hyd _ h2
      have h3 := card_erase_add_one h1
      omega
  have hΔ : ∀ y : Cn n Z, SuppIn (inU lev) y → CompanionTheory.RgExh.U.Deg (j + 1) y → bd (allT n) E y = 0 → ∀ A,
      bd (allT n) E (H y) A =
      N (y A) + ((j + 1 : ℕ) : ℂ) • y A + ((bd (allT n) E (H y) - Da (H y)) A + H (bd (allT n) E y - Da y) A) := by
    intro y hys hyd hc A
    have e := congrArg (fun T : Module.End ℂ (Cn n Z) => T y A) hom
    simp only [LinearMap.add_apply, Module.End.mul_apply, Pi.add_apply, LinearMap.sum_apply, Finset.sum_apply,
      cre_ann_apply, lift_apply] at e
    have e2 : (∑ i : I, if i.1 ∈ A then y A else 0) = ((j + 1 : ℕ) : ℂ) • y A := by
      by_cases h : y A = 0
      · simp [h]
      · rw [← hyd A h, ← Finset.sum_subtype (univ.filter (inU lev)) (p := inU lev) (by simp)
          (fun i => if i ∈ A then y A else 0), ← Finset.sum_filter, Finset.sum_const, Nat.cast_smul_eq_nsmul]
        congr 2
        ext i
        simp only [mem_filter, mem_univ, true_and]
        exact ⟨fun h' => h'.2, fun h' => ⟨hys A h i h', h'⟩⟩
    have e3 : N (y A) = ∑ i : I, a i.1 (d i.1 (y A)) := by simp only [N, LinearMap.sum_apply]; rfl
    rw [e3, ← e2, ← e, hc, zero_sub, map_neg, Pi.sub_apply, Pi.neg_apply]
    abel
  have main : ∀ k (y : Cn n Z), (∀ A, y A ∈ G k) → SuppIn (inU lev) y → CompanionTheory.RgExh.U.Deg (j + 1) y →
      bd (allT n) E y = 0 →
      ∃ t : Cn n Z, SuppIn (inU lev) t ∧ CompanionTheory.RgExh.U.Deg (j + 2) t ∧ bd (allT n) E t = y := by
    intro k
    induction k with
    | zero =>
      exact fun y hy _ _ _ => ⟨0, fun _ h => absurd rfl h, fun _ h => absurd rfl h, by
        rw [map_zero]; exact (funext hy).symm⟩
    | succ k ihk =>
      have inner : ∀ m (y : Cn n Z), (∀ A, y A ∈ G (k + 1)) →
          (∀ A, y A ∈ GlobalTheory.CompanionTheory.DSICKoszul.filt (fun i : I => d i.1) m ⊔ G k) →
          SuppIn (inU lev) y → CompanionTheory.RgExh.U.Deg (j + 1) y → bd (allT n) E y = 0 →
          ∃ t : Cn n Z, SuppIn (inU lev) t ∧ CompanionTheory.RgExh.U.Deg (j + 2) t ∧ bd (allT n) E t = y := by
        intro m
        induction m with
        | zero => exact fun y _ hy => ihk y fun A => by simpa [GlobalTheory.CompanionTheory.DSICKoszul.filt] using hy A
        | succ m ih =>
          intro y hy1 hy2 hs hd hc
          have hne : ((m : ℂ) + (j + 1 : ℕ)) ≠ 0 := by exact_mod_cast (by omega : m + (j + 1) ≠ 0)
          have hHy := hHs y hs hd
          have hbs : SuppIn (inU lev) (bd (allT n) E y) := bd_supp lev E hs
          have hL : ∀ A, (bd (allT n) E (H y) - Da (H y)) A + H (bd (allT n) E y - Da y) A ∈ G k := fun A =>
            Submodule.add_mem _ (hρ k _ (hHG k y hy1) hHy.1 A) (hHG k _ (hρ (k + 1) y hy1 hs) A)
          have hw : ∀ A, (bd (allT n) E (H y) - ((m : ℂ) + (j + 1 : ℕ)) • y) A =
              (N (y A) - (m : ℂ) • y A) + ((bd (allT n) E (H y) - Da (H y)) A + H (bd (allT n) E y - Da y) A) :=
              fun A => by
            rw [Pi.sub_apply, hΔ y hs hd hc A, Pi.smul_apply, add_smul]
            abel
          have hsm : ∀ c : ℂ, ∀ A, y A = 0 → (c • y) A = 0 := fun c A h => by simp [h]
          obtain ⟨t, ht, ht2, hbt⟩ := ih (bd (allT n) E (H y) - ((m : ℂ) + (j + 1 : ℕ)) • y)
            (fun A => by
              rw [hw]
              exact Submodule.add_mem _ (Submodule.sub_mem _ (hNG (k + 1) _ (hy1 A)) (Submodule.smul_mem _ _ (hy1 A)))
                (hGm k (hL A)))
            (fun A => by
              rw [hw]
              obtain ⟨u, hu, g, hg, e⟩ := Submodule.mem_sup.1 (hy2 A)
              refine Submodule.add_mem _ ?_ (Submodule.mem_sup_right (hL A))
              rw [← e, map_add, smul_add, add_sub_add_comm]
              exact Submodule.add_mem_sup
                (GlobalTheory.CompanionTheory.DSICKoszul.euler_filt (fun i : I => a i.1) _ (fun i j => hF.d_comm _ _) hda m u hu)
                (Submodule.sub_mem _ (hNG _ _ hg) (Submodule.smul_mem _ _ hg)))
            (supp_sub (bd_supp lev E hHy.1) (supp_of hs (hsm _)))
            (deg_sub (bd_deg E hHy.2) (deg_of _ hd (hsm _)))
            (by
              rw [map_sub, map_smul, hc, smul_zero, sub_zero]
              exact LinearMap.congr_fun hS _)
          have hsub : ∀ A, (H y - t) A = 0 → (((m : ℂ) + (j + 1 : ℕ))⁻¹ • (H y - t)) A = 0 := fun A h => by
            simp [h]
          refine ⟨((m : ℂ) + (j + 1 : ℕ))⁻¹ • (H y - t), supp_of (supp_sub hHy.1 ht) hsub,
            deg_of _ (deg_sub hHy.2 ht2) hsub, ?_⟩
          rw [map_smul, map_sub, hbt, sub_sub_cancel, smul_smul, inv_mul_cancel₀ hne, one_smul]
      exact fun y hy => inner (k + 1) y hy fun A => Submodule.mem_sup_left (hGf _ (hy A))
  choose f hf using hF.exh
  exact main ((univ.sup fun A => f (x A)) + 1) x
    (fun A => hF.mono (Finset.le_sup (f := fun A => f (x A)) (mem_univ A)) (hf _)) hxs hxd hcyc

end Acyc

open scoped TensorProduct in

theorem coverU (lev : Fin n → ℕ) (E : Fin n → Fin n → Module.End ℂ V) (hE : GlRel E) :
    ∃ (Y : Type) (_ : AddCommGroup Y) (_ : Module ℂ Y) (EY : Fin n → Fin n → Module.End ℂ Y) (π : Y →ₗ[ℂ] V),
      GlRel EY ∧ Function.Surjective π ∧ (∀ a b y, π (EY a b y) = E a b (π y)) ∧
      ∀ (j : ℕ) (x : Cn n Y), SuppIn (inU lev) x → CompanionTheory.RgExh.U.Deg (j + 1) x → bd (allT n) EY x = 0 →
        ∃ t : Cn n Y, SuppIn (inU lev) t ∧ CompanionTheory.RgExh.U.Deg (j + 2) t ∧ bd (allT n) EY t = x := by
  obtain ⟨Z, _, _, M, χ, z₀, a, d, Fil, hM, h1, h0, hF⟩ := free_all n n
  let S : ℕ → Set (V ⊗[ℂ] Z) := fun k => {t | ∃ v z, z ∈ Fil k ∧ t = v ⊗ₜ z}
  have hin : ∀ {k : ℕ} (v : V) {z : Z}, z ∈ Fil k → v ⊗ₜ[ℂ] z ∈ Submodule.span ℂ (S k) :=
    fun v _ hz => Submodule.subset_span ⟨_, _, hz, rfl⟩
  have hmap : ∀ (T : Module.End ℂ (V ⊗[ℂ] Z)) (k : ℕ) (Q : Submodule ℂ (V ⊗[ℂ] Z)),
      (∀ v z, z ∈ Fil k → T (v ⊗ₜ z) ∈ Q) → ∀ t ∈ Submodule.span ℂ (S k), T t ∈ Q := by
    intro T k Q h
    refine fun t ht => (Submodule.span_le (p := Q.comap T)).2 ?_ ht
    rintro _ ⟨v, z, hz, rfl⟩
    exact h v z hz
  have hm : Monotone fun k => Submodule.span ℂ (S k) := fun k l hkl =>
    Submodule.span_mono (by rintro _ ⟨v, z, hz, rfl⟩; exact ⟨v, z, hF.mono hkl hz, rfl⟩)
  have hG : GlRel fun c e => ((E c e).rTensor Z + (M c e).lTensor V : Module.End ℂ (V ⊗[ℂ] Z)) :=
    fun a b c d => kRel_tens (ε := allT n) (fun a b c d _ _ => hE a b c d) hM a b c d rfl rfl
  refine ⟨V ⊗[ℂ] Z, inferInstance, inferInstance, fun c e => (E c e).rTensor Z + (M c e).lTensor V,
    (TensorProduct.rid ℂ V).toLinearMap ∘ₗ χ.lTensor V, hG, fun v => ⟨v ⊗ₜ z₀, by simp [h1]⟩,
    fun c e t => ?_, acycU lev _ (fun i => (a i).lTensor V) (fun i => (d i).lTensor V)
      (fun k => Submodule.span ℂ (S k)) hG ⟨?_, ?_, ?_, hm, ?_, ?_, ?_, ?_, ?_⟩⟩
  · induction t using TensorProduct.induction_on with
    | zero => simp
    | tmul v f => simp [h0]
    | add p q hp hq => simp only [map_add, hp, hq]
  · exact fun i j => (hF.a_comm i j).map (Module.End.lTensorAlgHom ℂ Z V)
  · exact fun i j => (hF.d_comm i j).map (Module.End.lTensorAlgHom ℂ Z V)
  · intro i j _
    have := congrArg (Module.End.lTensorAlgHom ℂ Z V) (hF.da i j i.1.1.2)
    rw [map_sub, map_mul, map_mul, apply_ite (Module.End.lTensorAlgHom ℂ Z V), map_one, map_zero] at this
    exact this
  · intro t
    induction t using TensorProduct.induction_on with
    | zero => exact ⟨0, Submodule.zero_mem _⟩
    | tmul v z =>
      obtain ⟨k, hk⟩ := hF.exh z
      exact ⟨_, hin v hk⟩
    | add p q hp hq =>
      obtain ⟨k, hk⟩ := hp
      obtain ⟨l, hl⟩ := hq
      exact ⟨max k l, Submodule.add_mem _ (hm (le_max_left _ _) hk) (hm (le_max_right _ _) hl)⟩
  · exact fun i k => hmap _ k _ fun v z hz => hin v (hF.a_mem i _ z hz)
  · intro i k
    refine hmap (((E i.1.1 i.1.2).rTensor Z + (M i.1.1 i.1.2).lTensor V) - (a i).lTensor V) k _ fun v z hz => ?_
    have e : (((E i.1.1 i.1.2).rTensor Z + (M i.1.1 i.1.2).lTensor V) - (a i).lTensor V :
        Module.End ℂ (V ⊗[ℂ] Z)) (v ⊗ₜ z) = E i.1.1 i.1.2 v ⊗ₜ z + v ⊗ₜ (M i.1.1 i.1.2 z - a i z) := by
      simp only [LinearMap.sub_apply, LinearMap.add_apply, LinearMap.rTensor_tmul, LinearMap.lTensor_tmul,
        TensorProduct.tmul_sub]
      abel
    rw [e]
    exact Submodule.add_mem _ (hin _ hz) (hin _ (hF.r_mem i _ z hz))
  · exact fun i k => hmap _ _ _ fun v z hz => hin v (hF.d_mem i _ z hz)
  · exact fun i => hmap _ _ ⊥ fun v z hz => by simp [hF.d_zero i z hz]

section Car

variable {R : Type} [Ring R] [Algebra ℂ R] {ι : Type} [Fintype ι] [DecidableEq ι]

theorem quad_ann (a b : ι → R) (haa : ∀ i j, a i * a j + a j * a i = 0)
    (hab : ∀ i j, a i * b j + b j * a i = if i = j then 1 else 0) (c : ι → ι → ℂ) (m : ι) :
    (∑ i, ∑ k, c i k • (b k * a i)) * a m - a m * (∑ i, ∑ k, c i k • (b k * a i)) = - ∑ l, c l m • a l := by
  have t : ∀ i k, (b k * a i) * a m - a m * (b k * a i) = if m = k then - a i else 0 := by
    intro i k
    have e1 : a m * b k = (if m = k then 1 else 0) - b k * a m := eq_sub_of_add_eq (hab m k)
    have e2 : a i * a m = - (a m * a i) := eq_neg_of_add_eq_zero_left (haa i m)
    rw [← mul_assoc (a m), e1, mul_assoc, e2]
    split_ifs <;> noncomm_ring
  simp only [Finset.sum_mul, Finset.mul_sum, ← Finset.sum_sub_distrib, smul_mul_assoc, mul_smul_comm, ← smul_sub, t]
  simp [Finset.sum_neg_distrib]

theorem quad_cre (a b : ι → R) (hbb : ∀ i j, b i * b j + b j * b i = 0)
    (hab : ∀ i j, a i * b j + b j * a i = if i = j then 1 else 0) (c : ι → ι → ℂ) (m : ι) :
    (∑ i, ∑ k, c i k • (b k * a i)) * b m - b m * (∑ i, ∑ k, c i k • (b k * a i)) = ∑ k, c m k • b k := by
  have t : ∀ i k, (b k * a i) * b m - b m * (b k * a i) = if i = m then b k else 0 := by
    intro i k
    have e1 : a i * b m = (if i = m then 1 else 0) - b m * a i := eq_sub_of_add_eq (hab i m)
    have e2 : b k * b m = - (b m * b k) := eq_neg_of_add_eq_zero_left (hbb k m)
    rw [mul_assoc, e1, mul_sub, ← mul_assoc (b k), e2]
    split_ifs <;> noncomm_ring
  simp only [Finset.sum_mul, Finset.mul_sum, ← Finset.sum_sub_distrib, smul_mul_assoc, mul_smul_comm, ← smul_sub, t]
  rw [Finset.sum_eq_single m]
  · simp
  · intro i _ hi; simp [hi]
  · simp

end Car

section Car2

theorem triple_comm {R : Type} [Ring R] (A x y z Sx Sy Sz : R) (hx : A * x = x * A + Sx) (hy : A * y = y * A - Sy)
    (hz : A * z = z * A - Sz) : A * (x * y * z) - x * y * z * A = Sx * y * z - x * Sy * z - x * y * Sz := by
  have e1 : A * (x * y * z) = (A * x) * y * z := by simp only [mul_assoc]
  have e2 : (x * A + Sx) * y * z = x * (A * y) * z + Sx * y * z := by noncomm_ring
  have e3 : x * (y * A - Sy) * z = x * y * (A * z) - x * Sy * z := by noncomm_ring
  rw [e1, hx, e2, hy, e3, hz]
  noncomm_ring

variable {R : Type} [Ring R] [Algebra ℂ R] {ι : Type} [Fintype ι] [DecidableEq ι]

theorem cubic_comm (a b : ι → R) (haa : ∀ i j, a i * a j + a j * a i = 0)
    (hbb : ∀ i j, b i * b j + b j * b i = 0)
    (hab : ∀ i j, a i * b j + b j * a i = if i = j then 1 else 0) (c : ι → ι → ℂ) (t : ι → ι → ι → ℂ)
    (h : ∀ I J κ, ∑ k, t I J k * c k κ = ∑ j, t I j κ * c J j + ∑ i, t i J κ * c I i) :
    Commute (∑ i, ∑ k, c i k • (b k * a i)) (∑ i, ∑ j, ∑ k, t i j k • (b k * a j * a i)) := by
  set A := ∑ i, ∑ k, c i k • (b k * a i) with hA
  have h1 : ∀ m, A * a m = a m * A - ∑ l, c l m • a l := fun m => by
    have := quad_ann a b haa hab c m
    rw [← hA] at this
    rw [sub_eq_add_neg, ← this]; abel
  have h2 : ∀ m, A * b m = b m * A + ∑ k, c m k • b k := fun m => by
    have := quad_cre a b hbb hab c m
    rw [← hA] at this
    rw [← this]; abel
  have tr : ∀ i j k, A * (b k * a j * a i) - (b k * a j * a i) * A =
      (∑ k', c k k' • (b k' * a j * a i)) - (∑ l, c l j • (b k * a l * a i)) - ∑ l, c l i • (b k * a j * a l) := by
    intro i j k
    rw [triple_comm A _ _ _ _ _ _ (h2 k) (h1 j) (h1 i)]
    simp only [Finset.sum_mul, Finset.mul_sum, smul_mul_assoc, mul_smul_comm]
  let F : ι → ι → ι → R := fun i j k => b k * a j * a i
  have S1 : ∑ i, ∑ j, ∑ k, t i j k • (∑ k', c k k' • F i j k') =
      ∑ i, ∑ j, ∑ k, (∑ k', t i j k' * c k' k) • F i j k := by
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    simp only [Finset.smul_sum, smul_smul, Finset.sum_smul]
    exact Finset.sum_comm
  have S2 : ∑ i, ∑ j, ∑ k, t i j k • (∑ l, c l j • F i l k) =
      ∑ i, ∑ j, ∑ k, (∑ j', t i j' k * c j j') • F i j k := by
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [Finset.smul_sum, smul_smul, Finset.sum_smul]
    exact (Finset.sum_congr rfl fun j _ => Finset.sum_comm).trans
      (Finset.sum_comm.trans (Finset.sum_congr rfl fun l _ => Finset.sum_comm))
  have S3 : ∑ i, ∑ j, ∑ k, t i j k • (∑ l, c l i • F l j k) =
      ∑ i, ∑ j, ∑ k, (∑ i', t i' j k * c i i') • F i j k := by
    simp only [Finset.smul_sum, smul_smul, Finset.sum_smul]
    exact (Finset.sum_congr rfl fun i _ => (Finset.sum_congr rfl fun j _ => Finset.sum_comm).trans
      Finset.sum_comm).trans (Finset.sum_comm.trans (Finset.sum_congr rfl fun l _ =>
        Finset.sum_comm.trans (Finset.sum_congr rfl fun j _ => Finset.sum_comm)))
  have main : A * (∑ i, ∑ j, ∑ k, t i j k • (b k * a j * a i)) - (∑ i, ∑ j, ∑ k, t i j k • (b k * a j * a i)) * A = 0 := by
    have e : A * (∑ i, ∑ j, ∑ k, t i j k • (b k * a j * a i)) - (∑ i, ∑ j, ∑ k, t i j k • (b k * a j * a i)) * A =
        ∑ i, ∑ j, ∑ k, t i j k • (A * (b k * a j * a i) - (b k * a j * a i) * A) := by
      simp only [Finset.mul_sum, Finset.sum_mul, mul_smul_comm, smul_mul_assoc, smul_sub, Finset.sum_sub_distrib]
    rw [e]
    simp only [tr, smul_sub, Finset.sum_sub_distrib]
    have S1' := S1; have S2' := S2; have S3' := S3
    simp only [F] at S1' S2' S3'
    rw [S1', S2', S3', ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
    refine Finset.sum_eq_zero fun j _ => ?_
    rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
    refine Finset.sum_eq_zero fun k _ => ?_
    rw [← sub_smul, ← sub_smul, h]
    simp
  exact sub_eq_zero.1 main

end Car2

section Spec

def uI (lev : Fin n → ℕ) (i : Pos n) : ℂ := if inU lev i then 1 else 0

def cU (lev : Fin n → ℕ) (p q : Fin n) (i k : Pos n) : ℂ := if inU lev i then adC p q i k else 0

def tU (lev : Fin n → ℕ) (i j k : Pos n) : ℂ :=
  if inU lev i ∧ inU lev j ∧ i.1.2 = j.1.1 ∧ k.1.1 = i.1.1 ∧ k.1.2 = j.1.2 then 1 else 0

theorem sum_root {M : Type} [AddCommMonoid M] (f : Pos n → M) (P : Prop) [Decidable P] (x y : Fin n)
    (h : P → x < y) :
    ∑ j : Pos n, (if P ∧ j.1 = (x, y) then f j else 0) = if hP : P then f ⟨(x, y), h hP⟩ else 0 := by
  by_cases hP : P
  · rw [dif_pos hP, Finset.sum_eq_single ⟨(x, y), h hP⟩]
    · simp [hP]
    · intro j _ hj
      refine if_neg fun e => hj (Subtype.ext e.2)
    · simp
  · simp [hP]

theorem sum_cU {M : Type} [AddCommGroup M] [Module ℂ M] {lev : Fin n → ℕ} (hlev : Monotone lev) {p q : Fin n}
    (hpq : lev p = lev q) (g : Pos n → M) (l : Pos n) (hl : inU lev l) :
    ∑ j, cU lev p q l j • g j =
      (if h : q = l.1.1 then g ⟨(p, l.1.2), hlev.reflect_lt (by rw [hpq, h]; exact hl)⟩ else 0) -
      (if h : l.1.2 = p then g ⟨(l.1.1, q), hlev.reflect_lt (by rw [← hpq, ← h]; exact hl)⟩ else 0) := by
  have hlt : lev l.1.1 < lev l.1.2 := hl
  rw [← sum_root g (q = l.1.1) p l.1.2 (fun h => hlev.reflect_lt (by rw [hpq, h]; exact hl)),
    ← sum_root g (l.1.2 = p) l.1.1 q (fun h => hlev.reflect_lt (by rw [← hpq, ← h]; exact hl)),
    ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [cU, if_pos hl, adC, sub_smul, ite_smul, one_smul, zero_smul]

theorem struct_id {lev : Fin n → ℕ} (hlev : Monotone lev) {p q : Fin n} (hpq : lev p = lev q) (I J κ : Pos n) :
    ∑ k, tU lev I J k * cU lev p q k κ =
      ∑ j, tU lev I j κ * cU lev p q J j + ∑ i, tU lev i J κ * cU lev p q I i := by
  have hlt : ∀ {x y : Fin n}, lev x < lev y → x < y := fun h => hlev.reflect_lt h
  by_cases hI : inU lev I
  swap
  · have e1 : ∀ j k, tU lev I j k = 0 := fun j k => if_neg fun h => hI h.1
    have e2 : ∀ k, cU lev p q I k = 0 := fun k => if_neg hI
    simp [e1, e2]
  by_cases hJ : inU lev J
  swap
  · have e1 : ∀ i k, tU lev i J k = 0 := fun i k => if_neg fun h => hJ h.2.1
    have e2 : ∀ k, cU lev p q J k = 0 := fun k => if_neg hJ
    simp [e1, e2]
  obtain ⟨⟨a, b⟩, hab⟩ := I
  obtain ⟨⟨c, d⟩, hcd⟩ := J
  obtain ⟨⟨e, f⟩, hef⟩ := κ
  simp only [] at hab hcd hef
  have hI' : lev a < lev b := hI
  have hJ' : lev c < lev d := hJ
  have L : ∑ k, tU lev ⟨(a, b), hab⟩ ⟨(c, d), hcd⟩ k * cU lev p q k ⟨(e, f), hef⟩ =
      if b = c then (if q = a ∧ e = p ∧ f = d then 1 else 0) - (if d = p ∧ e = a ∧ f = q then 1 else 0) else 0 := by
    have h0 : ∀ h : b = c, a < d := fun h => hlt (by rw [h] at hI'; omega)
    have := sum_root (fun k : Pos n => cU lev p q k ⟨(e, f), hef⟩) (b = c) a d h0
    have e1 : ∀ k : Pos n, tU lev ⟨(a, b), hab⟩ ⟨(c, d), hcd⟩ k * cU lev p q k ⟨(e, f), hef⟩ =
        if b = c ∧ k.1 = (a, d) then cU lev p q k ⟨(e, f), hef⟩ else 0 := fun k => by
      by_cases hc : b = c ∧ k.1 = (a, d)
      · rw [if_pos hc, tU, if_pos ⟨hI, hJ, hc.1, by simp [hc.2], by simp [hc.2]⟩, one_mul]
      · rw [if_neg hc, tU, if_neg, zero_mul]
        rintro ⟨-, -, h1, h2, h3⟩
        exact hc ⟨h1, Prod.ext h2 h3⟩
    simp only [e1]
    rw [this]
    by_cases hbc : b = c
    · rw [dif_pos hbc, if_pos hbc, cU, if_pos (by show lev a < lev d; rw [hbc] at hI'; omega)]
      simp [adC]
    · rw [dif_neg hbc, if_neg hbc]
  have R1 : ∑ j, tU lev ⟨(a, b), hab⟩ j ⟨(e, f), hef⟩ * cU lev p q ⟨(c, d), hcd⟩ j =
      (if q = c ∧ b = p ∧ e = a ∧ f = d then 1 else 0) - (if d = p ∧ b = c ∧ e = a ∧ f = q then 1 else 0) := by
    have := sum_cU hlev hpq (fun j => tU lev ⟨(a, b), hab⟩ j ⟨(e, f), hef⟩) ⟨(c, d), hcd⟩ hJ
    simp only [smul_eq_mul] at this
    simp only [mul_comm (tU lev _ _ _)]
    rw [this]
    congr 1
    · by_cases hq : q = c
      · have hU : lev p < lev d := by rw [hpq, hq]; exact hJ'
        rw [dif_pos hq, tU]
        by_cases h : b = p ∧ e = a ∧ f = d
        · rw [if_pos ⟨hI, hU, h.1, h.2.1, h.2.2⟩, if_pos ⟨hq, h⟩]
        · rw [if_neg fun h' => h ⟨h'.2.2.1, h'.2.2.2.1, h'.2.2.2.2⟩, if_neg fun h' => h h'.2]
      · rw [dif_neg hq, if_neg fun h => hq h.1]
    · by_cases hd : d = p
      · have hU : lev c < lev q := by rw [← hpq, ← hd]; exact hJ'
        rw [dif_pos hd, tU]
        by_cases h : b = c ∧ e = a ∧ f = q
        · rw [if_pos ⟨hI, hU, h.1, h.2.1, h.2.2⟩, if_pos ⟨hd, h⟩]
        · rw [if_neg fun h' => h ⟨h'.2.2.1, h'.2.2.2.1, h'.2.2.2.2⟩, if_neg fun h' => h h'.2]
      · rw [dif_neg hd, if_neg fun h => hd h.1]
  have R2 : ∑ i, tU lev i ⟨(c, d), hcd⟩ ⟨(e, f), hef⟩ * cU lev p q ⟨(a, b), hab⟩ i =
      (if q = a ∧ b = c ∧ e = p ∧ f = d then 1 else 0) - (if b = p ∧ q = c ∧ e = a ∧ f = d then 1 else 0) := by
    have := sum_cU hlev hpq (fun i => tU lev i ⟨(c, d), hcd⟩ ⟨(e, f), hef⟩) ⟨(a, b), hab⟩ hI
    simp only [smul_eq_mul] at this
    simp only [mul_comm (tU lev _ _ _)]
    rw [this]
    congr 1
    · by_cases hq : q = a
      · have hU : lev p < lev b := by rw [hpq, hq]; exact hI'
        rw [dif_pos hq, tU]
        by_cases h : b = c ∧ e = p ∧ f = d
        · rw [if_pos ⟨hU, hJ, h.1, h.2.1, h.2.2⟩, if_pos ⟨hq, h⟩]
        · rw [if_neg fun h' => h ⟨h'.2.2.1, h'.2.2.2.1, h'.2.2.2.2⟩, if_neg fun h' => h h'.2]
      · rw [dif_neg hq, if_neg fun h => hq h.1]
    · by_cases hb : b = p
      · have hU : lev a < lev q := by rw [← hpq, ← hb]; exact hI'
        rw [dif_pos hb, tU]
        by_cases h : q = c ∧ e = a ∧ f = d
        · rw [if_pos ⟨hU, hJ, h.1, h.2.1, h.2.2⟩, if_pos ⟨hb, h⟩]
        · rw [if_neg fun h' => h ⟨h'.2.2.1, h'.2.2.2.1, h'.2.2.2.2⟩, if_neg fun h' => h h'.2]
      · rw [dif_neg hb, if_neg fun h => hb h.1]
  rw [L, R1, R2]
  by_cases h1 : b = c
  · subst h1
    have e1 : (if d = p ∧ b = b ∧ e = a ∧ f = q then (1 : ℂ) else 0) = if d = p ∧ e = a ∧ f = q then 1 else 0 :=
      if_congr (by tauto) rfl rfl
    have e2 : (if q = a ∧ b = b ∧ e = p ∧ f = d then (1 : ℂ) else 0) = if q = a ∧ e = p ∧ f = d then 1 else 0 :=
      if_congr (by tauto) rfl rfl
    have e3 : (if b = p ∧ q = b ∧ e = a ∧ f = d then (1 : ℂ) else 0) = if q = b ∧ b = p ∧ e = a ∧ f = d then 1 else 0 :=
      if_congr (by tauto) rfl rfl
    rw [if_pos rfl, e1, e2, e3]
    ring
  · have t : ∀ (P Q : Prop) [Decidable P] [Decidable Q], (P ↔ Q) → ((if P then (1 : ℂ) else 0) - if Q then 1 else 0) = 0 := by
      intro P Q _ _ h; simp [h]
    simp only [if_neg h1]
    have e0 : ¬(d = p ∧ b = c ∧ e = a ∧ f = q) := fun h => h1 h.2.1
    have e1 : ¬(q = a ∧ b = c ∧ e = p ∧ f = d) := fun h => h1 h.2.1
    rw [if_neg e0, if_neg e1]
    have := t (q = c ∧ b = p ∧ e = a ∧ f = d) (b = p ∧ q = c ∧ e = a ∧ f = d) (by tauto)
    rw [sub_zero, zero_sub, ← sub_eq_add_neg, this]

end Spec

section Ops

def AU (V : Type) [AddCommGroup V] [Module ℂ V] (lev : Fin n → ℕ) (p q : Fin n) : Module.End ℂ (Cn n V) :=
  ∑ i : Pos n, ∑ k : Pos n, cU lev p q i k • (cre k * ann i)

def TU (V : Type) [AddCommGroup V] [Module ℂ V] (lev : Fin n → ℕ) : Module.End ℂ (Cn n V) :=
  ∑ i : Pos n, ∑ j : Pos n, ∑ k : Pos n, tU lev i j k • (cre k * ann j * ann i)

def LU (lev : Fin n → ℕ) (E : Fin n → Fin n → Module.End ℂ V) : Module.End ℂ (Cn n V) :=
  ∑ i : Pos n, uI lev i • ((lift n (E i.1.1 i.1.2) : Module.End ℂ (Cn n V)) * ann i)

theorem ann_zero_of {lev : Fin n → ℕ} {x : Cn n V} (hx : SuppIn (inU lev) x) {i : Pos n} (hi : ¬inU lev i) :
    ann i x = 0 := by
  funext A
  by_contra h
  exact hi (hx _ (ann_ne h).2 i (mem_insert_self _ _))

theorem adL_eq {lev : Fin n → ℕ} {x : Cn n V} (hx : SuppIn (inU lev) x) (p q : Fin n) :
    adL p q x = AU V lev p q x := by
  simp only [adL, AU, LinearMap.sum_apply, LinearMap.smul_apply, Module.End.mul_apply]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => ?_
  by_cases hi : inU lev i
  · simp [cU, hi]
  · simp [ann_zero_of hx hi]

theorem bd_eq {lev : Fin n → ℕ} (E : Fin n → Fin n → Module.End ℂ V) {x : Cn n V} (hx : SuppIn (inU lev) x) :
    bd (allT n) E x = (LU lev E + TU V lev) x := by
  simp only [bd, LU, TU, LinearMap.add_apply, LinearMap.sum_apply, LinearMap.smul_apply, Module.End.mul_apply]
  congr 1
  · refine Finset.sum_congr rfl fun i _ => ?_
    rw [if_pos trivial]
    by_cases hi : inU lev i
    · simp [uI, hi]
    · simp [ann_zero_of hx hi]
  · refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
    by_cases hi : inU lev i
    · by_cases hj : inU lev j
      · by_cases ht : i.1.2 = j.1.1 ∧ k.1.1 = i.1.1 ∧ k.1.2 = j.1.2
        · rw [if_pos ⟨trivial, trivial, ht⟩, tU, if_pos ⟨hi, hj, ht⟩, one_smul]
          rfl
        · rw [if_neg fun h => ht h.2.2, tU, if_neg fun h => ht h.2.2, zero_smul]
          rfl
      · have e : ann j (ann i x) = - ann i (ann j x) := by
          have := LinearMap.congr_fun (ann_ann (V := V) j i) x
          simp only [LinearMap.add_apply, Module.End.mul_apply, LinearMap.zero_apply] at this
          exact eq_neg_of_add_eq_zero_left this
        have e2 : ann j (ann i x) = 0 := by rw [e, ann_zero_of hx hj, map_zero, neg_zero]
        have e3 : tU lev i j k = 0 := if_neg fun h => hj h.2.1
        split_ifs
        · simp [e2, e3]
        · simp [e3]
    · have e3 : tU lev i j k = 0 := if_neg fun h => hi h.1
      have e2 : ann i x = 0 := ann_zero_of hx hi
      split_ifs
      · simp [e2, e3]
      · simp [e3]

theorem lift_comm_ann (T : Module.End ℂ V) (i : Pos n) :
    Commute (lift n T : Module.End ℂ (Cn n V)) (ann i) := LinearMap.ext fun y => lift_ann T i y

theorem lift_comm_cre (T : Module.End ℂ V) (i : Pos n) :
    Commute (lift n T : Module.End ℂ (Cn n V)) (cre i) := LinearMap.ext fun y => lift_cre T i y

theorem lift_mul (S T : Module.End ℂ V) :
    (lift n (S * T) : Module.End ℂ (Cn n V)) = lift n S * lift n T := rfl

theorem lift_sub (S T : Module.End ℂ V) :
    (lift n (S - T) : Module.End ℂ (Cn n V)) = lift n S - lift n T := by
  refine LinearMap.ext fun y => funext fun A => ?_
  simp

theorem lift_comm_AU (T : Module.End ℂ V) (lev : Fin n → ℕ) (p q : Fin n) :
    Commute (lift n T : Module.End ℂ (Cn n V)) (AU V lev p q) :=
  Commute.sum_right _ _ _ fun i _ => Commute.sum_right _ _ _ fun k _ =>
    ((lift_comm_cre T k).mul_right (lift_comm_ann T i)).smul_right _

theorem lift_comm_TU (T : Module.End ℂ V) (lev : Fin n → ℕ) :
    Commute (lift n T : Module.End ℂ (Cn n V)) (TU V lev) :=
  Commute.sum_right _ _ _ fun i _ => Commute.sum_right _ _ _ fun j _ => Commute.sum_right _ _ _ fun k _ =>
    (((lift_comm_cre T k).mul_right (lift_comm_ann T j)).mul_right (lift_comm_ann T i)).smul_right _

theorem AU_comm_TU {lev : Fin n → ℕ} (hlev : Monotone lev) {p q : Fin n} (hpq : lev p = lev q) :
    Commute (AU V lev p q) (TU V lev) :=
  cubic_comm (fun i : Pos n => (ann i : Module.End ℂ (Cn n V))) cre (fun i j => ann_ann i j) (fun i j => cre_cre i j)
    (fun i j => ann_cre i j) (cU lev p q) (tU lev) (struct_id hlev hpq)

theorem gl_ad {lev : Fin n → ℕ} (hlev : Monotone lev) {p q : Fin n} (hpq : lev p = lev q)
    {E : Fin n → Fin n → Module.End ℂ V} (hE : GlRel E) (l : Pos n) (hl : inU lev l) :
    E p q * E l.1.1 l.1.2 - E l.1.1 l.1.2 * E p q = ∑ k, cU lev p q l k • E k.1.1 k.1.2 := by
  rw [sum_cU hlev hpq (fun k => E k.1.1 k.1.2) l hl, hE]
  congr 1

theorem cU_uI {lev : Fin n → ℕ} {p q : Fin n} (hpq : lev p = lev q) (l k : Pos n) :
    uI lev k * cU lev p q l k = cU lev p q l k := by
  by_cases hl : inU lev l
  · by_cases h : adC p q l k = 0
    · simp [cU, hl, h]
    · simp [cU, hl, uI, adC_U hpq hl h]
  · simp [cU, hl]

theorem comm_U {lev : Fin n → ℕ} (hlev : Monotone lev) {p q : Fin n} (hpq : lev p = lev q)
    {E : Fin n → Fin n → Module.End ℂ V} (hE : GlRel E) :
    Commute ((lift n (E p q) : Module.End ℂ (Cn n V)) + AU V lev p q) (LU lev E + TU V lev) := by
  set X : Module.End ℂ (Cn n V) := lift n (E p q) with hX
  set A := AU V lev p q with hA
  set T := TU V lev with hT
  set L : Pos n → Module.End ℂ (Cn n V) := fun i => lift n (E i.1.1 i.1.2) with hL
  have term : ∀ i, (X + A) * (L i * ann i) - (L i * ann i) * (X + A) =
      (X * L i - L i * X) * ann i - L i * ∑ l, cU lev p q l i • ann l := by
    intro i
    have h1 : X * ann i = ann i * X := (lift_comm_ann _ i).eq
    have h2 : A * L i = L i * A := (lift_comm_AU _ lev p q).symm.eq
    have h3 := quad_ann (fun i : Pos n => (ann i : Module.End ℂ (Cn n V))) cre (fun i j => ann_ann i j)
      (fun i j => ann_cre i j) (cU lev p q) i
    have h3' : A * ann i - ann i * A = - ∑ l, cU lev p q l i • ann l := h3
    have e : (X + A) * (L i * ann i) - (L i * ann i) * (X + A) = (X * L i - L i * X) * ann i +
        L i * (A * ann i - ann i * A) + L i * (X * ann i - ann i * X) + (A * L i - L i * A) * ann i := by
      noncomm_ring
    rw [e, h1, h2, h3']
    noncomm_ring
  have c3 : (X + A) * LU lev E - LU lev E * (X + A) = 0 := by
    have e : (X + A) * LU lev E - LU lev E * (X + A) =
        ∑ i, uI lev i • ((X + A) * (L i * ann i) - (L i * ann i) * (X + A)) := by
      simp only [LU, Finset.mul_sum, Finset.sum_mul, mul_smul_comm, smul_mul_assoc, smul_sub, Finset.sum_sub_distrib]
      rfl
    rw [e]
    simp only [term, smul_sub, Finset.sum_sub_distrib]
    have s1 : ∀ i, uI lev i • ((X * L i - L i * X) * ann i) = ∑ k, cU lev p q i k • (L k * ann i) := by
      intro i
      by_cases hi : inU lev i
      · have : X * L i - L i * X = lift n (E p q * E i.1.1 i.1.2 - E i.1.1 i.1.2 * E p q) := by
          rw [lift_sub, lift_mul, lift_mul]
        rw [this, gl_ad hlev hpq hE i hi]
        simp only [uI, if_pos hi, one_smul]
        have : (lift n (∑ k, cU lev p q i k • E k.1.1 k.1.2) : Module.End ℂ (Cn n V)) =
            ∑ k, cU lev p q i k • L k := by
          refine LinearMap.ext fun y => funext fun B => ?_
          simp [hL, LinearMap.sum_apply, Finset.sum_apply]
        rw [this, Finset.sum_mul]
        simp only [smul_mul_assoc]
      · simp [uI, cU, hi]
    simp only [s1]
    rw [sub_eq_zero]
    simp only [Finset.mul_sum, mul_smul_comm, Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => ?_
    rw [cU_uI hpq]
  have c1 : (X + A) * T = T * (X + A) :=
    ((lift_comm_TU _ lev).add_left (AU_comm_TU hlev hpq)).eq
  have : (X + A) * (LU lev E + T) = (LU lev E + T) * (X + A) := by
    rw [mul_add, add_mul (LU lev E) T, c1, sub_eq_zero.1 c3]
  exact this

theorem lF_eq {lev : Fin n → ℕ} (E : Fin n → Fin n → Module.End ℂ V) {x : Cn n V} (hx : SuppIn (inU lev) x)
    (p q : Fin n) : lF E p q x = ((lift n (E p q) : Module.End ℂ (Cn n V)) + AU V lev p q) x := by
  simp only [lF, LinearMap.add_apply, adL_eq hx]

theorem lF_comm {lev : Fin n → ℕ} (hlev : Monotone lev) {p q : Fin n} (hpq : lev p = lev q)
    {E : Fin n → Fin n → Module.End ℂ V} (hE : GlRel E) {x : Cn n V} (hx : SuppIn (inU lev) x) :
    lF E p q (bd (allT n) E x) = bd (allT n) E (lF E p q x) := by
  rw [lF_eq E (bd_supp lev E hx), bd_eq E (lF_supp E hpq hx), lF_eq E hx, bd_eq E hx]
  exact LinearMap.congr_fun (comm_U hlev hpq hE).eq x

theorem evLc_facts {lev : Fin n → ℕ} (hlev : Monotone lev) {E : Fin n → Fin n → Module.End ℂ V} (hE : GlRel E)
    (b : FreeAlgebra ℂ (Fin n × Fin n)) :
    ∀ x : Cn n V, SuppIn (inU lev) x → SuppIn (inU lev) (evLc lev E b x) ∧
      (∀ j, CompanionTheory.RgExh.U.Deg j x → CompanionTheory.RgExh.U.Deg j (evLc lev E b x)) ∧
      bd (allT n) E (evLc lev E b x) = evLc lev E b (bd (allT n) E x) := by
  induction b using FreeAlgebra.induction with
  | grade0 r =>
    intro x hx
    simp only [AlgHom.commutes, Module.algebraMap_end_apply]
    refine ⟨supp_of hx fun A h => by simp [h], fun j hj => deg_of j hj fun A h => by simp [h], by simp⟩
  | grade1 c =>
    intro x hx
    simp only [evLc, FreeAlgebra.lift_ι_apply]
    split_ifs with h
    · exact ⟨lF_supp E h hx, fun j hj => lF_deg E _ _ hj, (lF_comm hlev h hE hx).symm⟩
    · refine ⟨fun A h => absurd rfl h, fun j _ A h => absurd rfl h, by simp⟩
  | mul a b ha hb =>
    intro x hx
    obtain ⟨h1, h2, h3⟩ := hb x hx
    obtain ⟨h4, h5, h6⟩ := ha _ h1
    simp only [map_mul, Module.End.mul_apply]
    exact ⟨h4, fun j hj => h5 j (h2 j hj), by rw [h6, h3]⟩
  | add a b ha hb =>
    intro x hx
    obtain ⟨h1, h2, h3⟩ := ha x hx
    obtain ⟨h4, h5, h6⟩ := hb x hx
    simp only [map_add, LinearMap.add_apply]
    exact ⟨supp_add h1 h4, fun j hj => deg_add (h2 j hj) (h5 j hj), by rw [h3, h6]⟩

end Ops

theorem genCOU : GenCOU := by
  intro n lev a b hlev hab V _ _ E hE j
  induction j generalizing V with
  | zero =>
    intro x hs hd _
    obtain ⟨w, hw⟩ := (hab V E hE).2 (x ∅)
    let w' : Cn n V := fun A => ∑ i : Pos n, if inU lev i ∧ A = {i} then w i else 0
    have key : ∀ A, w' A ≠ 0 → ∃ i : Pos n, inU lev i ∧ A = {i} := fun A hA => by
      obtain ⟨i, -, hi⟩ := exists_ne_zero_of_sum_ne_zero hA
      by_contra hc
      exact hi (if_neg fun h => hc ⟨i, h⟩)
    have hw1 : SuppIn (inU lev) w' := fun A hA l hl => by
      obtain ⟨i, h1, rfl⟩ := key A hA
      rw [mem_singleton.1 hl]
      exact h1
    have hw2 : CompanionTheory.RgExh.U.Deg (0 + 1) w' := fun A hA => by
      obtain ⟨i, h1, rfl⟩ := key A hA
      simp
    refine ⟨w', hw1, hw2, funext fun A => ?_⟩
    rw [(evaluation_lift_degree_zero lev E b x hd).2]
    by_cases hA : A = ∅
    · subst hA
      rw [Pi.sub_apply, lift_apply, lift_apply, hw, bd_apply, Finset.sum_eq_zero (s := univ)
        (f := fun i => ∑ j : Pos n, ∑ k : Pos n, if Tri (allT n) i j k then cre k (ann j (ann i w')) ∅ else 0), add_zero]
      · refine Finset.sum_congr rfl fun i _ => ?_
        rw [if_pos rfl, ann_apply, if_neg (notMem_empty i)]
        have e0 : sg i (∅ : Finset (Pos n)) = 1 := by simp [sg]
        have e1 : w' (insert i ∅) = if inU lev i then w i else 0 := by
          simp only [w']
          rw [Finset.sum_eq_single i]
          · simp
          · intro k _ hk
            refine if_neg fun h => hk ?_
            have := h.2
            simp only [insert_empty_eq, singleton_inj] at this
            exact this.symm
          · simp
        rw [e0, one_smul, e1]
        split_ifs
        · rfl
        · simp
      · refine fun i _ => Finset.sum_eq_zero fun j _ => Finset.sum_eq_zero fun k _ => ?_
        split_ifs
        · simp [cre_apply]
        · rfl
    · have e : x A = 0 := by
        by_contra h
        exact hA (card_eq_zero.1 (hd A h))
      rw [Pi.sub_apply, lift_apply, lift_apply, e, map_zero, map_zero, sub_zero]
      by_contra h
      exact hA (card_eq_zero.1 (bd_deg E hw2 A (Ne.symm h)))
  | succ j ih =>
    intro x hs hd hc
    obtain ⟨Y, _, _, EY, π, hY, hsurj, hπ, hac⟩ := coverU lev E hE
    have hK : ∀ a b, ∀ y ∈ LinearMap.ker π, EY a b y ∈ LinearMap.ker π := by
      intro a b y hy
      rw [LinearMap.mem_ker] at hy ⊢
      rw [hπ, hy, map_zero]
    let EK : Fin n → Fin n → Module.End ℂ (LinearMap.ker π) := fun a b => (EY a b).restrict (hK a b)
    have hι : ∀ a b y, (LinearMap.ker π).subtype (EK a b y) = EY a b ((LinearMap.ker π).subtype y) :=
      fun _ _ _ => rfl
    have hEK : GlRel EK := by
      intro a b c d
      ext y
      have := LinearMap.congr_fun (hY a b c d) (y : Y)
      split_ifs at this ⊢ <;> simpa [EK] using this
    classical
    let x' : Cn n Y := fun A => if x A = 0 then 0 else (hsurj (x A)).choose
    have hz : ∀ A, x A = 0 → x' A = 0 := fun A h => if_pos h
    have hx's : SuppIn (inU lev) x' := supp_of hs hz
    have hx'd : CompanionTheory.RgExh.U.Deg (j + 1) x' := deg_of _ hd hz
    have hπx : lift n π x' = x := by
      funext A
      by_cases hA : x A = 0
      · simp [x', hA]
      · simp only [lift_apply, x', if_neg hA]
        exact (hsurj (x A)).choose_spec
    have hy : ∀ A, bd (allT n) EY x' A ∈ LinearMap.ker π := by
      intro A
      have := congrFun (lift_bd (ε := allT n) π EY E (fun i _ => hπ _ _) x') A
      rw [hπx, hc] at this
      exact this
    let y : Cn n (LinearMap.ker π) := fun A => ⟨_, hy A⟩
    have hιy : lift n (LinearMap.ker π).subtype y = bd (allT n) EY x' := rfl
    have hys : SuppIn (inU lev) y := supp_of (bd_supp lev EY hx's) fun A hA => Subtype.ext hA
    have hyd : CompanionTheory.RgExh.U.Deg j y := deg_of _ (bd_deg EY hx'd) fun A hA => Subtype.ext hA
    have hyb : bd (allT n) EK y = 0 := by
      have := lift_bd (ε := allT n) _ EK EY (fun i _ => hι _ _) y
      rw [hιy, show bd (allT n) EY (bd (allT n) EY x') = 0 from
        LinearMap.congr_fun (koszul_differential_sq_zero n (allT n) Y EY fun a b c d _ _ => hY a b c d) x'] at this
      funext A
      exact Subtype.ext (congrFun this A)
    obtain ⟨w, hws, hwd, hDw⟩ := ih _ EK hEK y hys hyd hyb
    have hpush := congrArg (lift n (LinearMap.ker π).subtype) hDw
    rw [map_sub, lift_ev _ EK EY hι, lift_evLc lev _ EK EY hι, lift_bd (ε := allT n) _ EK EY (fun i _ => hι _ _),
      hιy] at hpush
    obtain ⟨f1, f2, f3⟩ := evLc_facts hlev hY b x' hx's
    have c1 : bd (allT n) EY (lift n (ev EY a) x') = lift n (ev EY a) (bd (allT n) EY x') :=
      bd_lift_comm lev EY _ ((hab Y EY hY).1) hx's
    have hsw : SuppIn (inU lev) (lift n (LinearMap.ker π).subtype w) := supp_of hws fun A h => by simp [h]
    have hdw : CompanionTheory.RgExh.U.Deg (j + 1) (lift n (LinearMap.ker π).subtype w) := deg_of _ hwd fun A h => by simp [h]
    obtain ⟨t, ht, htd, hbt⟩ := hac j (lift n (ev EY a) x' - evLc lev EY b x' - lift n (LinearMap.ker π).subtype w)
      (supp_sub (supp_sub (supp_of hx's fun A h => by simp [h]) f1) hsw)
      (deg_sub (deg_sub (deg_of _ hx'd fun A h => by simp [h]) (f2 _ hx'd)) hdw)
      (by rw [map_sub, map_sub, c1, f3, hpush, sub_self])
    refine ⟨lift n π t, supp_of ht fun A h => by simp [h], deg_of _ htd fun A h => by simp [h], ?_⟩
    have h2 : lift n π (lift n (LinearMap.ker π).subtype w) = 0 := by
      funext A
      exact (w A).2
    rw [← lift_bd π EY E (fun i _ => hπ _ _), hbt, map_sub, map_sub, h2, lift_ev π EY E hπ, lift_evLc lev π EY E hπ,
      hπx, sub_zero]

end GlobalTheory.CompanionTheory.GenCOUP
