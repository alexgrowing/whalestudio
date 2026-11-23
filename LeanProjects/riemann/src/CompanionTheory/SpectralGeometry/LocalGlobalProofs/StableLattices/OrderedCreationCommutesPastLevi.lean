import Mathlib
import CompanionTheory.RealGroups.DiscreteSeries.DiscreteSeriesClassification.DiscreteSeriesExhaustion.FarRegularity.LKTExists
import CompanionTheory.HarishChandraModules.LowKTypeMultiplicity.EigenspaceCyclicDensity.CreationOperators.DifferentialBoundedSupport

open Finset CompanionTheory.RgExh CompanionTheory.RgExh.U
open CompanionTheory.D.LK (Pos Cn ann cre lift bd om cpt allT LocFin)
open Formalism.REAL (GlRel KHighest IsWeight)
open CompanionTheory.D.DSIC (KUnit)
open scoped InnerProductSpace

noncomputable section

namespace GlobalTheory.CompanionTheory.FarReg.BdProd

variable {n : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]

theorem cre_sq (k : Pos n) : (cre k * cre k : Module.End ℂ (Cn n V)) = 0 := by
  refine LinearMap.ext fun x => funext fun A => ?_
  simp only [Module.End.mul_apply, LinearMap.zero_apply, Pi.zero_apply, CompanionTheory.D.LK.Car.cre_apply]
  by_cases h : k ∈ A <;> simp [h]

theorem cre_anti (i j : Pos n) : (cre i * cre j : Module.End ℂ (Cn n V)) = -(cre j * cre i) :=
  eq_neg_of_add_eq_zero_left (CompanionTheory.D.LK.Car.cre_cre i j)

theorem cre_mul_prod_of_mem {k : Pos n} {l : List (Pos n)} (h : k ∈ l) :
    (cre k * (l.map cre).prod : Module.End ℂ (Cn n V)) = 0 := by
  induction l with
  | nil => simp at h
  | cons g t ih =>
    rw [List.map_cons, List.prod_cons]
    by_cases hk : k = g
    · subst hk
      rw [← mul_assoc, cre_sq, zero_mul]
    · have h1 := ih ((List.mem_cons.1 h).resolve_left hk)
      rw [← mul_assoc, cre_anti, neg_mul, mul_assoc, h1, mul_zero, neg_zero]

theorem term_comm (k i g : Pos n) :
    (cre k * ann i * cre g - cre g * (cre k * ann i) : Module.End ℂ (Cn n V)) = if i = g then cre k else 0 := by
  have h1 := CompanionTheory.D.LK.Car.ann_cre (V := V) i g
  rw [mul_assoc, eq_sub_of_add_eq h1, mul_sub, ← mul_assoc (cre k) (cre g), cre_anti k g, neg_mul, mul_assoc (cre g),
    sub_neg_eq_add, add_sub_cancel_right]
  split_ifs <;> simp

theorem adL_cre (p q : Fin n) (g : Pos n) :
    (adL p q * cre g - cre g * adL p q : Module.End ℂ (Cn n V)) = ∑ k : Pos n, adC p q g k • cre k := by
  have h : (adL p q * cre g - cre g * adL p q : Module.End ℂ (Cn n V)) =
      ∑ i : Pos n, ∑ k : Pos n, adC p q i k • (cre k * ann i * cre g - cre g * (cre k * ann i)) := by
    simp only [adL, Finset.sum_mul, Finset.mul_sum, smul_mul_assoc, mul_smul_comm, smul_sub,
      ← Finset.sum_sub_distrib]
  rw [h]
  simp only [term_comm]
  rw [Finset.sum_eq_single g]
  · simp
  · intro i _ hi
    simp [hi]
  · simp

theorem lF_cre (E : Fin n → Fin n → Module.End ℂ V) (p q : Fin n) (g : Pos n) :
    (lF E p q * cre g : Module.End ℂ (Cn n V)) = cre g * lF E p q + ∑ k : Pos n, adC p q g k • cre k := by
  have h1 : (lift n (E p q) * cre g : Module.End ℂ (Cn n V)) = cre g * lift n (E p q) :=
    LinearMap.ext fun x => CompanionTheory.D.LK.lift_cre (E p q) g x
  rw [← adL_cre, lF, add_mul, mul_add, h1]
  abel

theorem lF_prod (E : Fin n → Fin n → Module.End ℂ V) (p q : Fin n) (l : List (Pos n))
    (h : ∀ (pre : List (Pos n)) (f : Pos n) (post : List (Pos n)), l = pre ++ f :: post → ∀ k : Pos n,
      adC p q f k ≠ 0 → k ∈ post) :
    (lF E p q * (l.map cre).prod : Module.End ℂ (Cn n V)) = (l.map cre).prod * lF E p q := by
  induction l with
  | nil => simp
  | cons g t ih =>
    have ht := ih fun pre f post e k hk => h (g :: pre) f post (by rw [e]; rfl) k hk
    have hz : ((∑ k : Pos n, adC p q g k • cre k) * (t.map cre).prod : Module.End ℂ (Cn n V)) = 0 := by
      rw [Finset.sum_mul]
      refine Finset.sum_eq_zero fun k _ => ?_
      by_cases hk : adC p q g k = 0
      · rw [hk, zero_smul, zero_mul]
      · rw [smul_mul_assoc, cre_mul_prod_of_mem (h [] g t rfl k hk), smul_zero]
    rw [List.map_cons, List.prod_cons, ← mul_assoc, lF_cre, add_mul, hz, add_zero, mul_assoc, ht, mul_assoc]

theorem bd_prod : ∀ (n : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (E : Fin n → Fin n → Module.End ℂ V),
    (∀ e : Pos n, (bd (allT n) E * cre e + cre e * bd (allT n) E : Module.End ℂ (Cn n V)) = lF E e.1.1 e.1.2) →
    ∀ (l : List (Pos n)) (x : Cn n V),
      (∀ (pre : List (Pos n)) (f : Pos n) (post : List (Pos n)), l = pre ++ f :: post → ∀ e ∈ l, ∀ k : Pos n,
        adC e.1.1 e.1.2 f k ≠ 0 → k ∈ post) →
      (∀ e ∈ l, lF E e.1.1 e.1.2 x = 0) →
      bd (allT n) E (((l.map cre).prod : Module.End ℂ (Cn n V)) x) =
        (-1 : ℂ) ^ l.length • ((l.map cre).prod : Module.End ℂ (Cn n V)) (bd (allT n) E x) := by
  intro n V _ _ E hC l x
  induction l with
  | nil => intro _ _; simp
  | cons f t ih =>
    intro hcl hx
    have ih' := ih (fun pre g post e a ha k hk =>
      hcl (f :: pre) g post (by rw [e]; rfl) a (List.mem_cons_of_mem _ ha) k hk)
      (fun e he => hx e (List.mem_cons_of_mem _ he))
    have hf : lF E f.1.1 f.1.2 (((t.map cre).prod : Module.End ℂ (Cn n V)) x) = 0 := by
      have h1 := lF_prod E f.1.1 f.1.2 t (fun pre g post e k hk =>
        hcl (f :: pre) g post (by rw [e]; rfl) f List.mem_cons_self k hk)
      have h2 := LinearMap.congr_fun h1 x
      simp only [Module.End.mul_apply] at h2
      rw [h2, hx f List.mem_cons_self, map_zero]
    have h3 := LinearMap.congr_fun (hC f) (((t.map cre).prod : Module.End ℂ (Cn n V)) x)
    simp only [LinearMap.add_apply, Module.End.mul_apply, hf, ih'] at h3
    simp only [List.map_cons, List.prod_cons, Module.End.mul_apply, List.length_cons, pow_succ, map_smul]
    rw [eq_neg_of_add_eq_zero_left h3, mul_neg_one, neg_smul, map_smul]

end GlobalTheory.CompanionTheory.FarReg.BdProd
