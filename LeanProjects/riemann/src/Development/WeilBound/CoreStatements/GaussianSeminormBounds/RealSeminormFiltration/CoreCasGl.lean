import Development.WeilBound.CoreStatements.GaussianSeminormBounds.RealSeminormFiltration.CoreCas
import Development.WeilBound.CoreStatements.GaussianSeminormBounds.RealSeminormFiltration.CoreCyc

noncomputable section

open ReciprocityTheory.ThetaSummability.Real ReciprocityTheory.ChartRestriction.G.ThK.Real FockH1Action MvPolynomial Matrix
open scoped InnerProductSpace

namespace PositivityTheory.KReal

namespace CasGl

variable {r s : ℕ}

abbrev KI (r s : ℕ) : Type := {ab : Ix r s × Ix r s // sameBlock ab.1 ab.2}

abbrev PIx (r s : ℕ) : Type := {ab : Ix r s × Ix r s // ¬ sameBlock ab.1 ab.2}

theorem sb_iff (a b : Ix r s) : sameBlock a b ↔ a.isLeft = b.isLeft := by
  cases a <;> cases b <;> simp [sameBlock]

def swK (k : KI r s) : KI r s := ⟨(k.1.2, k.1.1), PI.FHS.sameBlock_symm k.2⟩

theorem sum_sub {N : Type} [AddCommMonoid N] (P : Ix r s → Ix r s → Prop) [∀ a b, Decidable (P a b)]
    (F : Ix r s → Ix r s → N) :
    ∑ k : {ab : Ix r s × Ix r s // P ab.1 ab.2}, F k.1.1 k.1.2 = ∑ a, ∑ b, if P a b then F a b else 0 := by
  rw [← Fintype.sum_prod_type' (f := fun a b => if P a b then F a b else 0), ← Finset.sum_filter]
  exact (Finset.sum_subtype (p := fun ab : Ix r s × Ix r s => P ab.1 ab.2)
    (Finset.univ.filter fun ab : Ix r s × Ix r s => P ab.1 ab.2) (by simp) (fun ab => F ab.1 ab.2)).symm

theorem casK_eq_sum {M : Type} [AddCommGroup M] [Module ℂ M] (ρ : Ix r s → Ix r s → Module.End ℂ M) :
    casK ρ = ∑ k : KI r s, ρ k.1.1 k.1.2 * ρ (swK k).1.1 (swK k).1.2 :=
  (sum_sub sameBlock (fun a b => ρ a b * ρ b a)).symm

theorem pc_sum {Z : Mat r s} (hZ : IsPC Z) : ∑ j : PIx r s, Z j.1.1 j.1.2 • Eab j.1.1 j.1.2 = Z := by
  rw [sum_sub (fun a b => ¬ sameBlock a b) (fun a b => Z a b • (Eab a b : Mat r s))]
  conv_rhs => rw [Matrix.matrix_eq_sum_single Z]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  by_cases h : sameBlock a b
  · simp [h, hZ a b h]
  · simp [h, Eab, Matrix.smul_single]

theorem kc_sum {Z : Mat r s} (hZ : IsKC Z) : ∑ j : KI r s, Z j.1.1 j.1.2 • Eab j.1.1 j.1.2 = Z := by
  rw [sum_sub sameBlock (fun a b => Z a b • (Eab a b : Mat r s))]
  conv_rhs => rw [Matrix.matrix_eq_sum_single Z]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  by_cases h : sameBlock a b
  · simp [h, Eab, Matrix.smul_single]
  · simp [h, hZ a b h]

theorem Eab_mul_apply (a b e f : Ix r s) (Z : Mat r s) :
    (Eab a b * Z) e f = if e = a then Z b f else 0 := by
  by_cases h : e = a
  · subst h; simp [Eab]
  · rw [if_neg h]; exact Matrix.single_mul_apply_of_ne _ _ _ _ _ h _

theorem mul_Eab_apply (a b e f : Ix r s) (Z : Mat r s) :
    (Z * Eab a b) e f = if f = b then Z e a else 0 := by
  by_cases h : f = b
  · subst h; simp [Eab]
  · rw [if_neg h]; exact Matrix.mul_single_apply_of_ne _ _ _ _ _ h _

theorem Eab_apply (a b e f : Ix r s) : (Eab a b : Mat r s) e f = if a = e ∧ b = f then 1 else 0 := by
  simp [Eab, Matrix.single_apply]

theorem pc_Eab {a b : Ix r s} (h : ¬ sameBlock a b) : IsPC (Eab a b : Mat r s) := by
  intro e f hef
  rw [Eab_apply]
  split_ifs with h'
  · obtain ⟨rfl, rfl⟩ := h'
    exact absurd hef h
  · rfl

theorem pc_ad {a b : Ix r s} (h : sameBlock a b) {Z : Mat r s} (hZ : IsPC Z) :
    IsPC (Eab a b * Z - Z * Eab a b) := by
  intro e f hef
  have hb : ∀ x y, x.isLeft = y.isLeft → Z x y = 0 := fun x y hxy => hZ x y ((sb_iff x y).mpr hxy)
  rw [sb_iff] at h hef
  rw [Matrix.sub_apply, Eab_mul_apply, mul_Eab_apply]
  by_cases h1 : e = a <;> by_cases h2 : f = b
  · rw [if_pos h1, if_pos h2, hb b f (by rw [← h2]), hb e a (by rw [h1]), sub_zero]
  · rw [if_pos h1, if_neg h2, hb b f (by rw [← h, ← h1, hef]), sub_zero]
  · rw [if_neg h1, if_pos h2, hb e a (by rw [hef, h2, ← h]), sub_zero]
  · rw [if_neg h1, if_neg h2, sub_zero]

theorem kc_mul {Z W : Mat r s} (hZ : IsPC Z) (hW : IsPC W) : IsKC (Z * W) := by
  intro a b hab
  rw [Matrix.mul_apply]
  refine Finset.sum_eq_zero fun x _ => ?_
  by_cases hx : sameBlock a x
  · rw [hZ a x hx, zero_mul]
  · rw [hW x b ?_, mul_zero]
    rw [sb_iff] at hx hab ⊢
    cases a <;> cases x <;> cases b <;> simp_all

def adC (k : KI r s) : Matrix (PIx r s) (PIx r s) ℂ := fun j i =>
  ((Eab k.1.1 k.1.2 * Eab i.1.1 i.1.2 - Eab i.1.1 i.1.2 * Eab k.1.1 k.1.2 : Mat r s)) j.1.1 j.1.2

theorem adC_sw (k : KI r s) : adC (swK k) = (adC k)ᴴ := by
  ext j i
  obtain ⟨⟨a, b⟩, hk⟩ := k
  obtain ⟨⟨c, d⟩, hi⟩ := i
  obtain ⟨⟨e, f⟩, hj⟩ := j
  simp only [adC, swK, Matrix.conjTranspose_apply, Matrix.sub_apply, Eab_mul_apply, Eab_apply]
  clear hk hi hj
  simp only [star_sub, apply_ite star, star_one, star_zero]
  split_ifs <;> subst_vars <;> simp_all
  all_goals
    obtain ⟨h1, h2⟩ := ‹_ ∧ _›
    subst h1
    simp_all

theorem adC_mul (k k' : KI r s) (j i : PIx r s) :
    (adC k * adC k') j i =
      ((Eab k.1.1 k.1.2 * (Eab k'.1.1 k'.1.2 * Eab i.1.1 i.1.2 - Eab i.1.1 i.1.2 * Eab k'.1.1 k'.1.2) -
        (Eab k'.1.1 k'.1.2 * Eab i.1.1 i.1.2 - Eab i.1.1 i.1.2 * Eab k'.1.1 k'.1.2) * Eab k.1.1 k.1.2 :
          Mat r s)) j.1.1 j.1.2 := by
  have hZ : IsPC (Eab k'.1.1 k'.1.2 * Eab i.1.1 i.1.2 - Eab i.1.1 i.1.2 * Eab k'.1.1 k'.1.2 : Mat r s) :=
    pc_ad k'.2 (pc_Eab i.2)
  rw [Matrix.mul_apply]
  conv_rhs => rw [← pc_sum hZ]
  simp only [Finset.mul_sum, Finset.sum_mul, Matrix.smul_mul, Matrix.mul_smul, Matrix.sub_apply,
    Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, adC, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun l _ => ?_
  ring

theorem adad_apply (a b e f : Ix r s) {Z : Mat r s} (hZ : IsPC Z) :
    ((Eab a b * (Eab b a * Z - Z * Eab b a) - (Eab b a * Z - Z * Eab b a) * Eab a b : Mat r s)) e f =
      ((if e = a then 1 else 0) + (if f = b then 1 else 0)) * Z e f := by
  have hd : ∀ x, Z x x = 0 := fun x => hZ x x ((sb_iff x x).mpr rfl)
  simp only [Matrix.sub_apply, Eab_mul_apply, mul_Eab_apply]
  split_ifs <;> subst_vars <;> simp [hd] <;> ring

theorem count_cross {e f : Ix r s} (h : ¬ sameBlock e f) :
    (∑ a : Ix r s, ∑ b : Ix r s, if sameBlock a b then
      ((if e = a then 1 else 0) + (if f = b then 1 else 0) : ℂ) else 0) = (r : ℂ) + s := by
  rcases e with e | e <;> rcases f with f | f <;> simp [sameBlock] at h ⊢ <;>
    simp [Fintype.sum_sum_type, sameBlock, Finset.sum_add_distrib] <;> ring

theorem adC_cas : ∑ k : KI r s, adC k * adC (swK k) =
    ((((r : ℝ) + s : ℝ)) : ℂ) • (1 : Matrix (PIx r s) (PIx r s) ℂ) := by
  ext j i
  rw [Matrix.sum_apply]
  simp only [adC_mul, swK]
  simp only [adad_apply _ _ _ _ (pc_Eab i.2)]
  rw [sum_sub (fun a b => sameBlock a b) (fun a b => ((if j.1.1 = a then 1 else 0) +
    (if j.1.2 = b then 1 else 0)) * (Eab i.1.1 i.1.2 : Mat r s) j.1.1 j.1.2)]
  simp only [← ite_zero_mul, ← Finset.sum_mul]
  rw [count_cross j.2]
  by_cases hij : j = i
  · subst hij; simp [Eab_apply]
  · have : ¬ (i.1.1 = j.1.1 ∧ i.1.2 = j.1.2) := fun h => hij (Subtype.ext (Prod.ext h.1.symm h.2.symm))
    simp [Eab_apply, this, hij]

end CasGl

open CasGl in
theorem cas_bound_gl {r s : ℕ} {M : Type} [AddCommGroup M] [Module ℂ M] (act : Mat r s →ₗ[ℂ] Module.End ℂ M)
    (hL : IsLie act) {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]
    (ρ : Ix r s → Ix r s → Module.End ℂ V) (hadj : AdjK ρ) (c0 : ℝ)
    (hc0 : casK ρ = (c0 : ℂ) • (1 : Module.End ℂ V)) (ι : V →ₗ[ℂ] M)
    (hι : ∀ a b, sameBlock a b → ∀ v, ι (ρ a b v) = act (Eab a b) (ι v))
    (h5 : StarK act (LinearMap.range ι) c0) :
    (∀ x ∈ genG act (LinearMap.range ι),
      casK (units act) x - (c0 : ℂ) • x ∈ LinearMap.range ι → x ∈ LinearMap.range ι) ∧
    ∀ x ∈ genG act (LinearMap.range ι), ∃ F : Submodule ℂ M, FiniteDimensional ℂ F ∧ x ∈ F ∧ KSt (units act) F := by
  have hcas : casK (units act) = ∑ k : KI r s, units act k.1.1 k.1.2 * units act (swK k).1.1 (swK k).1.2 :=
    casK_eq_sum (units act)
  have h1' : ∀ (k : KI r s) (i : PIx r s), units act k.1.1 k.1.2 * act (Eab i.1.1 i.1.2) -
      act (Eab i.1.1 i.1.2) * units act k.1.1 k.1.2 = ∑ j, adC k j i • act (Eab j.1.1 j.1.2) := by
    intro k i
    simp only [units]
    rw [hL, ← pc_sum (pc_ad k.2 (pc_Eab i.2)), map_sum]
    simp only [map_smul]
    rfl
  have h2' : ∀ (i j : PIx r s), act (Eab i.1.1 i.1.2) * act (Eab j.1.1 j.1.2) -
      act (Eab j.1.1 j.1.2) * act (Eab i.1.1 i.1.2) ∈
        Submodule.span ℂ (Set.range (fun k : KI r s => units act k.1.1 k.1.2)) := by
    intro i j
    have hK : IsKC (Eab i.1.1 i.1.2 * Eab j.1.1 j.1.2 - Eab j.1.1 j.1.2 * Eab i.1.1 i.1.2 : Mat r s) := by
      intro a b hab
      rw [Matrix.sub_apply, kc_mul (pc_Eab i.2) (pc_Eab j.2) a b hab,
        kc_mul (pc_Eab j.2) (pc_Eab i.2) a b hab, sub_zero]
    rw [hL, ← kc_sum hK, map_sum]
    refine Submodule.sum_mem _ fun k _ => ?_
    rw [map_smul]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩)
  have hc0' : ∑ k : KI r s, ρ k.1.1 k.1.2 * ρ (swK k).1.1 (swK k).1.2 = (c0 : ℂ) • 1 := by
    rw [← casK_eq_sum]; exact hc0
  have h5' : ∀ t ≤ c0 + ((r : ℝ) + s), ∀ x ∈ Submodule.span ℂ
      {y : M | ∃ (i : PIx r s) (v : V), y = act (Eab i.1.1 i.1.2) (ι v)},
      (∑ k : KI r s, units act k.1.1 k.1.2 * units act (swK k).1.1 (swK k).1.2) x = (t : ℂ) • x → x = 0 := by
    intro t ht x hx hxt
    refine h5 t ht x (Submodule.span_mono ?_ hx) (by rw [hcas]; exact hxt)
    rintro _ ⟨i, v, rfl⟩
    exact ⟨i.1.1, i.1.2, i.2, ι v, LinearMap.mem_range_self ι v, rfl⟩
  have hG : genG act (LinearMap.range ι) = sInf {N : Submodule ℂ M | LinearMap.range ι ≤ N ∧
      (∀ k : KI r s, ∀ x ∈ N, units act k.1.1 k.1.2 x ∈ N) ∧
      ∀ i : PIx r s, ∀ x ∈ N, act (Eab i.1.1 i.1.2) x ∈ N} := by
    simp only [genG]
    congr 1
    ext N
    simp only [Set.mem_setOf_eq]
    constructor
    · rintro ⟨hN, hW⟩
      exact ⟨hN, fun k x hx => hW _ x hx, fun i x hx => hW _ x hx⟩
    · rintro ⟨hN, hk, hp⟩
      refine ⟨hN, fun W x hx => ?_⟩
      have hE : ∀ a b, act (Eab a b) x ∈ N := by
        intro a b
        by_cases hab : sameBlock a b
        · exact hk ⟨(a, b), hab⟩ x hx
        · exact hp ⟨(a, b), hab⟩ x hx
      rw [Matrix.matrix_eq_sum_single W, map_sum, LinearMap.sum_apply]
      refine Submodule.sum_mem _ fun a _ => ?_
      rw [map_sum, LinearMap.sum_apply]
      refine Submodule.sum_mem _ fun b _ => ?_
      have : (Matrix.single a b (W a b) : Mat r s) = W a b • Eab a b := by simp [Eab]
      rw [this, map_smul, LinearMap.smul_apply]
      exact Submodule.smul_mem _ _ (hE a b)
  obtain ⟨k1, k2⟩ := cas_bound (K := KI r s) (I := PIx r s) swK (fun k => rfl)
    (fun k : KI r s => units act k.1.1 k.1.2) (fun i : PIx r s => act (Eab i.1.1 i.1.2)) adC
    ((r : ℝ) + s) c0 h1' h2' adC_sw adC_cas (fun k : KI r s => ρ k.1.1 k.1.2)
    (fun k u v => hadj k.1.1 k.1.2 k.2 u v) hc0' ι (fun k v => hι k.1.1 k.1.2 k.2 v) h5'
    (genG act (LinearMap.range ι)) hG
  refine ⟨fun x hx hx2 => k1 x hx (by rw [← hcas]; exact hx2), fun x hx => ?_⟩
  obtain ⟨F, hF, hxF, hFk⟩ := k2 x hx
  exact ⟨F, hF, hxF, fun a b hab y hy => hFk ⟨(a, b), hab⟩ y hy⟩

end PositivityTheory.KReal

end
