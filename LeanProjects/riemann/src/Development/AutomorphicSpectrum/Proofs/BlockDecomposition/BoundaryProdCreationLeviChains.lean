import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.RealDescent.RealLeviDescent.InjectiveDecompositionAction
import CompanionTheory.RealGroups.DiscreteSeries.DiscreteSeriesClassification.DiscreteSeriesExhaustion.FarRegularity.LKTExists
import CompanionTheory.HarishChandraModules.LowKTypeMultiplicity.EigenspaceCyclicDensity.CreationOperators.DifferentialBoundedSupport
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TwLMulSelf
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.BoundaryCreationAnticommutator

open Finset PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD GlobalTheory.CompanionTheory.LvChain
open CompanionTheory.D.LK (Pos)
open scoped InnerProductSpace

noncomputable section

namespace GlobalTheory.CompanionTheory.LvChain.BdProdL

variable {n : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]

theorem creL_sq (k : Lt n) : (creL k * creL k : Module.End ℂ (Cq n V)) = 0 := by
  refine LinearMap.ext fun x => funext fun A => ?_
  simp only [Module.End.mul_apply, LinearMap.zero_apply, Pi.zero_apply, creL_apply]
  by_cases h : k ∈ A <;> simp [h]

theorem creL_anti (i j : Lt n) : (creL i * creL j : Module.End ℂ (Cq n V)) = -(creL j * creL i) :=
  eq_neg_of_add_eq_zero_left (creL_creL i j)

theorem creL_mul_prod_of_mem {k : Pos n} {l : List (Pos n)} (h : k ∈ l) :
    (creL (false, k) * (l.map fun i => (creL (false, i) : Module.End ℂ (Cq n V))).prod : Module.End ℂ (Cq n V)) = 0 := by
  induction l with
  | nil => simp at h
  | cons g t ih =>
    rw [List.map_cons, List.prod_cons]
    by_cases hk : k = g
    · subst hk
      rw [← mul_assoc, creL_sq, zero_mul]
    · have h1 := ih ((List.mem_cons.1 h).resolve_left hk)
      rw [← mul_assoc, creL_anti, neg_mul, mul_assoc, h1, mul_zero, neg_zero]

theorem tri_antiL (l m k e : Lt n) :
    (creL k * annL m * annL l * creL e + creL e * (creL k * annL m * annL l) : Module.End ℂ (Cq n V)) =
      (if l = e then creL k * annL m else 0) - (if m = e then creL k * annL l else 0) := by
  rw [GlobalTheory.CompanionTheory.Cartan.anticommutator_triple_product _ _ _ _ _ _ (annL_creL l e) (annL_creL m e) (creL_creL k e)]
  congr 1
  · split_ifs <;> simp
  · split_ifs <;> simp

open Classical in

theorem part_oneL (S : Lt n → Prop) (E1 E2 : Fin n → Fin n → Module.End ℂ V) {e : Lt n} (he : S e) :
    ((∑ l : Lt n, if S l then (liftL n (xL E1 E2 l) : Module.End ℂ (Cq n V)) * annL l else 0) * creL e +
      creL e * ∑ l : Lt n, if S l then (liftL n (xL E1 E2 l) : Module.End ℂ (Cq n V)) * annL l else 0 :
      Module.End ℂ (Cq n V)) = liftL n (xL E1 E2 e) := by
  rw [Finset.sum_mul, Finset.mul_sum, ← Finset.sum_add_distrib]
  have h : ∀ l : Lt n,
      ((if S l then (liftL n (xL E1 E2 l) : Module.End ℂ (Cq n V)) * annL l else 0) * creL e +
        creL e * (if S l then (liftL n (xL E1 E2 l) : Module.End ℂ (Cq n V)) * annL l else 0) :
        Module.End ℂ (Cq n V)) = if l = e then (liftL n (xL E1 E2 e) : Module.End ℂ (Cq n V)) else 0 := by
    intro l
    by_cases hl : S l
    · rw [if_pos hl, ← mul_assoc (creL e), ← liftL_creL, mul_assoc, mul_assoc, ← mul_add, annL_creL]
      by_cases hi : l = e
      · subst hi; simp
      · simp [hi]
    · have hne : l ≠ e := fun c => hl (c ▸ he)
      simp [hl, hne]
  rw [Finset.sum_congr rfl fun l _ => h l]
  simp

theorem sum_antiL {R : Type*} [Ring R] (T P Q : Lt n → Lt n → Lt n → R) (c : R)
    (h : ∀ i j k, T i j k * c + c * T i j k = P i j k - Q i j k) :
    (∑ i, ∑ j, ∑ k, T i j k) * c + c * ∑ i, ∑ j, ∑ k, T i j k =
      ∑ i, ∑ j, ∑ k, P i j k - ∑ i, ∑ j, ∑ k, Q i j k := by
  simp only [Finset.sum_mul, Finset.mul_sum, ← Finset.sum_add_distrib, h, Finset.sum_sub_distrib]

open Classical in

theorem part_twoL (S : Lt n → Prop) {e : Lt n} (he : S e) :
    ((∑ l : Lt n, ∑ m : Lt n, ∑ k : Lt n,
        if S l ∧ S m ∧ l.2.1.2 = m.2.1.1 ∧ k.1 = xor l.1 m.1 ∧ k.2.1.1 = l.2.1.1 ∧ k.2.1.2 = m.2.1.2 then
          creL k * annL m * annL l else 0) * creL e +
      creL e * ∑ l : Lt n, ∑ m : Lt n, ∑ k : Lt n,
        if S l ∧ S m ∧ l.2.1.2 = m.2.1.1 ∧ k.1 = xor l.1 m.1 ∧ k.2.1.1 = l.2.1.1 ∧ k.2.1.2 = m.2.1.2 then
          creL k * annL m * annL l else 0 : Module.End ℂ (Cq n V)) = adS S e.1 e.2.1.1 e.2.1.2 := by
  have h : ∀ l m k : Lt n,
      ((if S l ∧ S m ∧ l.2.1.2 = m.2.1.1 ∧ k.1 = xor l.1 m.1 ∧ k.2.1.1 = l.2.1.1 ∧ k.2.1.2 = m.2.1.2 then
          creL k * annL m * annL l else 0) * creL e +
        creL e * (if S l ∧ S m ∧ l.2.1.2 = m.2.1.1 ∧ k.1 = xor l.1 m.1 ∧ k.2.1.1 = l.2.1.1 ∧ k.2.1.2 = m.2.1.2 then
          creL k * annL m * annL l else 0) : Module.End ℂ (Cq n V)) =
      (if l = e ∧ S m ∧ e.2.1.2 = m.2.1.1 ∧ k.1 = xor e.1 m.1 ∧ k.2.1 = (e.2.1.1, m.2.1.2) then
        creL k * annL m else 0) -
        (if m = e ∧ S l ∧ l.2.1.2 = e.2.1.1 ∧ k.1 = xor e.1 l.1 ∧ k.2.1 = (l.2.1.1, e.2.1.2) then
        creL k * annL l else 0) := by
    intro l m k
    by_cases ht : S l ∧ S m ∧ l.2.1.2 = m.2.1.1 ∧ k.1 = xor l.1 m.1 ∧ k.2.1.1 = l.2.1.1 ∧ k.2.1.2 = m.2.1.2
    · rw [if_pos ht, tri_antiL]
      obtain ⟨t0, t0', t1, t2, t3, t4⟩ := ht
      congr 1
      · by_cases hi : l = e
        · subst hi
          rw [if_pos rfl, if_pos ⟨rfl, t0', t1, t2, Prod.ext t3 t4⟩]
        · rw [if_neg hi, if_neg fun c => hi c.1]
      · by_cases hj : m = e
        · subst hj
          rw [if_pos rfl, if_pos ⟨rfl, t0, t1, by rw [t2, Bool.xor_comm], Prod.ext t3 t4⟩]
        · rw [if_neg hj, if_neg fun c => hj c.1]
    · rw [if_neg ht, zero_mul, mul_zero, add_zero, if_neg, if_neg, sub_zero]
      · rintro ⟨rfl, c0, c1, c2, c3⟩
        exact ht ⟨c0, he, c1, by rw [c2, Bool.xor_comm], by rw [c3], by rw [c3]⟩
      · rintro ⟨rfl, c0, c1, c2, c3⟩
        exact ht ⟨he, c0, c1, c2, by rw [c3], by rw [c3]⟩
  rw [sum_antiL _ _ _ _ h]
  have s₁ : (∑ l : Lt n, ∑ m : Lt n, ∑ k : Lt n,
      (if l = e ∧ S m ∧ e.2.1.2 = m.2.1.1 ∧ k.1 = xor e.1 m.1 ∧ k.2.1 = (e.2.1.1, m.2.1.2) then
        creL k * annL m else 0 : Module.End ℂ (Cq n V))) =
      ∑ m : Lt n, ∑ k : Lt n,
        (if S m ∧ e.2.1.2 = m.2.1.1 ∧ k.1 = xor e.1 m.1 ∧ k.2.1 = (e.2.1.1, m.2.1.2) then
          creL k * annL m else 0 : Module.End ℂ (Cq n V)) := by
    rw [Finset.sum_eq_single e]
    · simp
    · intro i _ hi
      simp [hi]
    · simp
  have s₂ : (∑ l : Lt n, ∑ m : Lt n, ∑ k : Lt n,
      (if m = e ∧ S l ∧ l.2.1.2 = e.2.1.1 ∧ k.1 = xor e.1 l.1 ∧ k.2.1 = (l.2.1.1, e.2.1.2) then
        creL k * annL l else 0 : Module.End ℂ (Cq n V))) =
      ∑ l : Lt n, ∑ k : Lt n,
        (if S l ∧ l.2.1.2 = e.2.1.1 ∧ k.1 = xor e.1 l.1 ∧ k.2.1 = (l.2.1.1, e.2.1.2) then
          creL k * annL l else 0 : Module.End ℂ (Cq n V)) := by
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_eq_single e]
    · simp
    · intro j _ hj
      simp [hj]
    · simp
  rw [s₁, s₂, ← Finset.sum_sub_distrib]
  unfold adS
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  by_cases hl : S l
  · simp only [hl, true_and, if_true, adCL, sub_smul, ite_smul, one_smul, zero_smul]
  · simp [hl]

theorem cartanL (S : Lt n → Prop) (E1 E2 : Fin n → Fin n → Module.End ℂ V) {e : Lt n} (he : S e) :
    (bdL S E1 E2 * creL e + creL e * bdL S E1 E2 : Module.End ℂ (Cq n V)) =
      liftL n (xL E1 E2 e) + adS S e.1 e.2.1.1 e.2.1.2 := by
  have h₁ := part_oneL S E1 E2 he
  have h₂ := part_twoL (V := V) S he
  unfold bdL
  rw [add_mul, mul_add, add_add_add_comm, h₁, h₂]

theorem term_commL (k i g : Lt n) :
    (creL k * annL i * creL g - creL g * (creL k * annL i) : Module.End ℂ (Cq n V)) =
      if i = g then creL k else 0 := by
  have h1 := annL_creL (V := V) i g
  rw [mul_assoc, eq_sub_of_add_eq h1, mul_sub, ← mul_assoc (creL k) (creL g), creL_anti k g, neg_mul,
    mul_assoc (creL g), sub_neg_eq_add, add_sub_cancel_right]
  split_ifs <;> simp

open Classical in

theorem adS_creL (S : Lt n → Prop) (s : Bool) (p q : Fin n) (g : Lt n) :
    (adS S s p q * creL g - creL g * adS S s p q : Module.End ℂ (Cq n V)) =
      if S g then ∑ k : Lt n, adCL s p q g k • creL k else 0 := by
  have h : (adS S s p q * creL g - creL g * adS S s p q : Module.End ℂ (Cq n V)) =
      ∑ i : Lt n, ∑ k : Lt n, if S i then
        adCL s p q i k • (creL k * annL i * creL g - creL g * (creL k * annL i)) else 0 := by
    unfold adS
    simp only [Finset.sum_mul, Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => ?_
    by_cases hi : S i
    · simp only [hi, if_true, smul_mul_assoc, mul_smul_comm, smul_sub]
    · simp [hi]
  rw [h]
  simp only [term_commL]
  rw [Finset.sum_eq_single g]
  · by_cases hg : S g <;> simp [hg]
  · intro i _ hi
    simp [hi]
  · simp

def lK (lev : Fin n → ℕ) (E1 E2 : Fin n → Fin n → Module.End ℂ V) (p q : Fin n) : Module.End ℂ (Cq n V) :=
  (liftL n (kA E1 E2 p q) : Module.End ℂ (Cq n V)) + adS (inRR lev) false p q

theorem lK_creL (lev : Fin n → ℕ) (E1 E2 : Fin n → Fin n → Module.End ℂ V) (p q : Fin n) (g : Pos n) :
    (lK lev E1 E2 p q * creL (false, g) : Module.End ℂ (Cq n V)) =
      creL (false, g) * lK lev E1 E2 p q + ∑ k : Lt n, adCL false p q (false, g) k • creL k := by
  have h := adS_creL (V := V) (inRR lev) false p q (false, g)
  rw [if_pos (Or.inl rfl)] at h
  rw [← h, lK, add_mul, mul_add, liftL_creL]
  abel

theorem adCL_false (p q : Fin n) (g k : Pos n) :
    adCL false p q (false, g) (false, k) = CompanionTheory.RgExh.U.adC p q g k := by
  simp [adCL, CompanionTheory.RgExh.U.adC]

theorem adCL_true (p q : Fin n) (g k : Pos n) : adCL false p q (false, g) (true, k) = 0 := by
  simp [adCL]

theorem lK_prod (lev : Fin n → ℕ) (E1 E2 : Fin n → Fin n → Module.End ℂ V) (p q : Fin n) (l : List (Pos n))
    (h : ∀ (pre : List (Pos n)) (f : Pos n) (post : List (Pos n)), l = pre ++ f :: post → ∀ k : Pos n,
      CompanionTheory.RgExh.U.adC p q f k ≠ 0 → k ∈ post) :
    (lK lev E1 E2 p q * (l.map fun i => (creL (false, i) : Module.End ℂ (Cq n V))).prod : Module.End ℂ (Cq n V)) =
      (l.map fun i => (creL (false, i) : Module.End ℂ (Cq n V))).prod * lK lev E1 E2 p q := by
  induction l with
  | nil => simp
  | cons g t ih =>
    have ht := ih fun pre f post e k hk => h (g :: pre) f post (by rw [e]; rfl) k hk
    have hz : ((∑ k : Lt n, adCL false p q (false, g) k • creL k) *
        (t.map fun i => (creL (false, i) : Module.End ℂ (Cq n V))).prod : Module.End ℂ (Cq n V)) = 0 := by
      rw [Finset.sum_mul]
      refine Finset.sum_eq_zero fun k _ => ?_
      obtain ⟨b, k⟩ := k
      cases b with
      | true => rw [adCL_true, zero_smul, zero_mul]
      | false =>
        rw [adCL_false]
        by_cases hk : CompanionTheory.RgExh.U.adC p q g k = 0
        · rw [hk, zero_smul, zero_mul]
        · rw [smul_mul_assoc, creL_mul_prod_of_mem (h [] g t rfl k hk), smul_zero]
    rw [List.map_cons, List.prod_cons, ← mul_assoc, lK_creL, add_mul, hz, add_zero, mul_assoc, ht, mul_assoc]

theorem annL_of_supp {P : Lt n → Prop} {l : Lt n} {x : Cq n V} (h : SuppL P x) (hl : ¬P l) : annL l x = 0 := by
  funext A
  rw [annL_apply]
  by_cases hA : l ∈ A
  · simp [hA]
  · have h0 : x (insert l A) = 0 := by
      by_contra h0
      exact hl (h _ h0 l (Finset.mem_insert_self _ _))
    simp [hA, h0]

theorem adS_eq_adLL (lev : Fin n → ℕ) (s : Bool) (p q : Fin n) {x : Cq n V} (hx : SuppL (inUU lev) x) :
    adS (inRR lev) s p q x = adLL lev s p q x := by
  unfold adS adLL
  simp only [LinearMap.sum_apply]
  refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun k _ => ?_
  by_cases hl : inUU lev l
  · rw [if_pos (Or.inr hl), if_pos hl]
  · rw [if_neg hl]
    split_ifs
    · simp [Module.End.mul_apply, annL_of_supp hx hl]
    · rfl

theorem lK_eq_Lv (lev : Fin n → ℕ) (E1 E2 : Fin n → Fin n → Module.End ℂ V) (p q : Fin n) {x : Cq n V}
    (hx : SuppL (inUU lev) x) : lK lev E1 E2 p q x = Lv lev E1 E2 p q x := by
  simp only [lK, Lv, LinearMap.add_apply, adS_eq_adLL lev false p q hx]

theorem cartanK (lev : Fin n → ℕ) (E1 E2 : Fin n → Fin n → Module.End ℂ V) (f : Pos n) :
    (bdL (inRR lev) E1 E2 * creL (false, f) + creL (false, f) * bdL (inRR lev) E1 E2 : Module.End ℂ (Cq n V)) =
      lK lev E1 E2 f.1.1 f.1.2 := by
  rw [cartanL (inRR lev) E1 E2 (e := (false, f)) (Or.inl rfl)]
  simp [lK, xL]

theorem boundary_prod_creation_levi_vanish (lev : Fin n → ℕ) (E1 E2 : Fin n → Fin n → Module.End ℂ V) (x : Cq n V)
    (hs : SuppL (inUU lev) x) (l : List (Pos n)) :
    (∀ (pre : List (Pos n)) (f : Pos n) (post : List (Pos n)), l = pre ++ f :: post → ∀ e ∈ l, ∀ k : Pos n,
      CompanionTheory.RgExh.U.adC e.1.1 e.1.2 f k ≠ 0 → k ∈ post) →
    (∀ e ∈ l, Lv lev E1 E2 e.1.1 e.1.2 x = 0) →
    bdL (inRR lev) E1 E2 (((l.map fun i => (creL (false, i) : Module.End ℂ (Cq n V))).prod : Module.End ℂ (Cq n V)) x) =
      (-1 : ℂ) ^ l.length • ((l.map fun i => (creL (false, i) : Module.End ℂ (Cq n V))).prod : Module.End ℂ (Cq n V))
        (bdL (inRR lev) E1 E2 x) := by
  induction l with
  | nil => intro _ _; simp
  | cons f t ih =>
    intro hcl hx
    have ih' := ih (fun pre g post e a ha k hk =>
      hcl (f :: pre) g post (by rw [e]; rfl) a (List.mem_cons_of_mem _ ha) k hk)
      (fun e he => hx e (List.mem_cons_of_mem _ he))
    have hf : lK lev E1 E2 f.1.1 f.1.2
        (((t.map fun i => (creL (false, i) : Module.End ℂ (Cq n V))).prod : Module.End ℂ (Cq n V)) x) = 0 := by
      have h1 := lK_prod lev E1 E2 f.1.1 f.1.2 t (fun pre g post e k hk =>
        hcl (f :: pre) g post (by rw [e]; rfl) f List.mem_cons_self k hk)
      have h2 := LinearMap.congr_fun h1 x
      simp only [Module.End.mul_apply] at h2
      rw [h2, lK_eq_Lv lev E1 E2 _ _ hs, hx f List.mem_cons_self, map_zero]
    have h3 := LinearMap.congr_fun (cartanK lev E1 E2 f)
      (((t.map fun i => (creL (false, i) : Module.End ℂ (Cq n V))).prod : Module.End ℂ (Cq n V)) x)
    simp only [LinearMap.add_apply, Module.End.mul_apply, hf, ih'] at h3
    simp only [List.map_cons, List.prod_cons, Module.End.mul_apply, List.length_cons, pow_succ, map_smul]
    rw [eq_neg_of_add_eq_zero_left h3, mul_neg_one, neg_smul, map_smul]

theorem bd_prodL : ∀ (n : ℕ) (lev : Fin n → ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (E1 E2 : Fin n → Fin n → Module.End ℂ V)
    (l : List (Pos n)) (x : Cq n V), (∀ e ∈ l, lev e.1.1 = lev e.1.2) →
    (∀ (pre : List (Pos n)) (f : Pos n) (post : List (Pos n)), l = pre ++ f :: post → ∀ e ∈ l, ∀ k : Pos n,
      CompanionTheory.RgExh.U.adC e.1.1 e.1.2 f k ≠ 0 → k ∈ post) →
    SuppL (inUU lev) x → (∀ e ∈ l, Lv lev E1 E2 e.1.1 e.1.2 x = 0) →
    bdL (inRR lev) E1 E2 (((l.map fun i => (creL (false, i) : Module.End ℂ (Cq n V))).prod : Module.End ℂ (Cq n V)) x) =
      (-1 : ℂ) ^ l.length • ((l.map fun i => (creL (false, i) : Module.End ℂ (Cq n V))).prod : Module.End ℂ (Cq n V))
        (bdL (inRR lev) E1 E2 x) :=
  fun _ lev _ _ _ E1 E2 l x _ hcl hs hx => boundary_prod_creation_levi_vanish lev E1 E2 x hs l hcl hx

end GlobalTheory.CompanionTheory.LvChain.BdProdL
