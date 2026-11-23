import Mathlib
import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.IsHermHyperbolic
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.TransvectionIdentitiesUnitary
import Development.AbelianVarietyTheory.Proofs.HermitianTraceForms.ExistsOrthogonalBasisDotProductApplyEq

open scoped Matrix

namespace GlobalTheory.UTrans.ReflChar0

open GlobalTheory.UTrans.Calc

variable {E : Type} [Field E] {n : ℕ} {σ : E →+* E} {G : Matrix (Fin n) (Fin n) E}

theorem hf_sub_smul_left (z x w : Fin n → E) (e : E) :
    hf σ G (z - e • x) w = hf σ G z w - e * hf σ G x w := by
  rw [sub_eq_add_neg, ← neg_smul, hf_add_left, hf_smul_left]
  ring

theorem hf_sub_smul_right (z x w : Fin n → E) (e : E) :
    hf σ G w (z - e • x) = hf σ G w z - σ e * hf σ G w x := by
  rw [sub_eq_add_neg, ← neg_smul, hf_add_right, hf_smul_right, map_neg]
  ring

theorem isU_refl (h : IsHerm σ G) {x : Fin n → E} (hx : hf σ G x x ≠ 0) {u : E} (hu : u * σ u = 1) :
    IsU σ G (tv σ G x ((u - 1) / hf σ G x x)) := by
  apply isU_tv σ G h.invol h.herm
  rw [map_div₀, hf_conj σ G h.invol h.herm, map_sub, map_one]
  field_simp
  linear_combination hu

theorem refl_inv {x : Fin n → E} (hx : hf σ G x x ≠ 0) {u : E} (hu : u * σ u = 1) :
    tv σ G x ((σ u - 1) / hf σ G x x) * tv σ G x ((u - 1) / hf σ G x x) = 1 := by
  rw [tv_mul]
  have : (σ u - 1) / hf σ G x x + (u - 1) / hf σ G x x +
      (σ u - 1) / hf σ G x x * ((u - 1) / hf σ G x x) * hf σ G x x = 0 := by
    field_simp
    linear_combination hu
  rw [this]
  ext a b
  simp [tv]

theorem exists_refl (h : IsHerm σ G) (x z : Fin n → E) (hz : hf σ G z z = hf σ G x x) (e : E)
    (he : σ e = e) (he2 : e * e = 1) (hy : hf σ G (z - e • x) (z - e • x) ≠ 0) :
    ∃ u : E, u * σ u = 1 ∧
      tv σ G (z - e • x) ((u - 1) / hf σ G (z - e • x) (z - e • x)) *ᵥ z = e • x := by
  obtain ⟨a, ha⟩ : ∃ a, a = hf σ G z (z - e • x) := ⟨_, rfl⟩
  have hyy : hf σ G (z - e • x) (z - e • x) = a + σ a := by
    rw [ha, hf_conj σ G h.invol h.herm, hf_sub_smul_left z x (z - e • x), hf_sub_smul_left z x z,
      hf_sub_smul_right z x x, he, hz]
    linear_combination (hf σ G x x) * he2
  have ha0 : a ≠ 0 := by
    intro h0
    exact hy (by rw [hyy, h0]; simp)
  have hca : σ a ≠ 0 := by simpa using ha0
  refine ⟨-σ a / a, ?_, ?_⟩
  · rw [map_div₀, map_neg, h.invol]
    field_simp
  · rw [tv_mulVec, ← ha]
    have : (-σ a / a - 1) / hf σ G (z - e • x) (z - e • x) * a = -1 := by
      rw [div_mul_eq_mul_div, div_eq_iff hy, hyy]
      field_simp
      ring
    rw [this]
    simp

theorem exists_prod_mulVec_eq [CharZero E] (h : IsHerm σ G) (x z : Fin n → E) (hx : hf σ G x x ≠ 0)
    (hz : hf σ G z z = hf σ G x x) :
    ∃ l : List ((Fin n → E) × E),
      (∀ p ∈ l, hf σ G p.1 p.1 ≠ 0 ∧ p.2 * σ p.2 = 1 ∧ p.1 ∈ Submodule.span E {x, z}) ∧
      (l.map fun p => tv σ G p.1 ((p.2 - 1) / hf σ G p.1 p.1)).prod *ᵥ z = x := by
  have hxs : x ∈ Submodule.span E ({x, z} : Set (Fin n → E)) := Submodule.subset_span (by simp)
  have hzs : z ∈ Submodule.span E ({x, z} : Set (Fin n → E)) := Submodule.subset_span (by simp)
  have hmem : ∀ e : E, z - e • x ∈ Submodule.span E ({x, z} : Set (Fin n → E)) := fun e =>
    Submodule.sub_mem _ hzs (Submodule.smul_mem _ _ hxs)
  by_cases h1 : hf σ G (z - (1 : E) • x) (z - (1 : E) • x) = 0
  · have h2 : hf σ G (z - (-1 : E) • x) (z - (-1 : E) • x) ≠ 0 := by
      intro h2
      rw [hf_sub_smul_left, hf_sub_smul_right, hf_sub_smul_right] at h1 h2
      simp only [map_one, map_neg, hz] at h1 h2
      apply hx
      have h4 : (4 : E) * hf σ G x x = 0 := by linear_combination h1 + h2
      exact (mul_eq_zero.1 h4).resolve_left (by norm_num)
    obtain ⟨u, hu, hu'⟩ := exists_refl h x z hz (-1) (by simp) (by simp) h2
    refine ⟨[(x, -1), (z - (-1 : E) • x, u)], ?_, ?_⟩
    · intro p hp
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl
      · exact ⟨hx, by simp, hxs⟩
      · exact ⟨h2, hu, hmem _⟩
    · simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
      rw [← Matrix.mulVec_mulVec, hu', tv_mulVec, hf_smul_left, ← add_smul]
      have : (-1 : E) + (-1 - 1) / hf σ G x x * (-1 * hf σ G x x) = 1 := by
        field_simp
        ring
      rw [this, one_smul]
  · obtain ⟨u, hu, hu'⟩ := exists_refl h x z hz 1 (by simp) (by simp) h1
    refine ⟨[(z - (1 : E) • x, u)], ?_, ?_⟩
    · intro p hp
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
      subst hp
      exact ⟨h1, hu, hmem _⟩
    · simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
      rw [hu', one_smul]

theorem exists_basis [CharZero E] (h : IsHerm σ G) :
    ∃ x : Fin n → Fin n → E, (∀ i, hf σ G (x i) (x i) ≠ 0) ∧
      (∀ i j, i ≠ j → hf σ G (x i) (x j) = 0) ∧ Submodule.span E (Set.range x) = ⊤ := by
  have he : ∀ x y : Fin n → E, hf σ G x y = x ⬝ᵥ G *ᵥ (σ ∘ y) := fun x y =>
    (GlobalTheory.HermDiag.dotProduct_mulVec_comp_eq_sum σ G x y).symm
  obtain ⟨v, hv⟩ :=
    GlobalTheory.HermDiag.exists_orthogonal_basis_dotProduct (c := σ) two_ne_zero h.invol h.herm
  have hd := GlobalTheory.HermDiag.congr_diagonal_of_orthogonal σ v hv
  refine ⟨v, fun i => ?_, fun i j hij => ?_, v.span_eq⟩
  · rw [he]
    exact GlobalTheory.HermDiag.ne_zero_of_congr_diagonal (GlobalTheory.HermDiag.det_of_basis_ne_zero v) hd h.det_ne i
  · rw [he]
    exact hv i j hij

theorem isU_prod (hG : IsHerm σ G) (l : List ((Fin n → E) × E))
    (hl : ∀ p ∈ l, hf σ G p.1 p.1 ≠ 0 ∧ p.2 * σ p.2 = 1) :
    IsU σ G (l.map fun p => tv σ G p.1 ((p.2 - 1) / hf σ G p.1 p.1)).prod := by
  induction l with
  | nil => intro x y; simp
  | cons p l ih =>
    rw [List.map_cons, List.prod_cons]
    have hp := hl p List.mem_cons_self
    exact isU_mul σ G _ _ (isU_refl hG hp.1 hp.2) (ih fun q hq => hl q (List.mem_cons_of_mem _ hq))

theorem exists_inv (hG : IsHerm σ G) (l : List ((Fin n → E) × E))
    (hl : ∀ p ∈ l, hf σ G p.1 p.1 ≠ 0 ∧ p.2 * σ p.2 = 1) :
    ∃ l' : List ((Fin n → E) × E), (∀ p ∈ l', hf σ G p.1 p.1 ≠ 0 ∧ p.2 * σ p.2 = 1) ∧
      (l'.map fun p => tv σ G p.1 ((p.2 - 1) / hf σ G p.1 p.1)).prod *
        (l.map fun p => tv σ G p.1 ((p.2 - 1) / hf σ G p.1 p.1)).prod = 1 := by
  induction l with
  | nil => exact ⟨[], by simp, by simp⟩
  | cons p l ih =>
    obtain ⟨l', h1, h2⟩ := ih fun q hq => hl q (List.mem_cons_of_mem _ hq)
    have hp := hl p List.mem_cons_self
    refine ⟨l' ++ [(p.1, σ p.2)], ?_, ?_⟩
    · intro q hq
      rcases List.mem_append.1 hq with hq | hq
      · exact h1 q hq
      · rw [List.mem_singleton] at hq
        subst hq
        refine ⟨hp.1, ?_⟩
        show σ p.2 * σ (σ p.2) = 1
        rw [hG.invol, mul_comm]
        exact hp.2
    · rw [List.map_append, List.prod_append, List.map_cons, List.map_cons, List.prod_cons,
        List.prod_cons, List.map_nil, List.prod_nil, mul_one, mul_assoc,
        ← mul_assoc (tv σ G _ _), refl_inv hp.1 hp.2, one_mul, h2]

theorem prod_fix (v : Fin n → E) (l : List ((Fin n → E) × E))
    (hl : ∀ p ∈ l, hf σ G v p.1 = 0) :
    (l.map fun p => tv σ G p.1 ((p.2 - 1) / hf σ G p.1 p.1)).prod *ᵥ v = v := by
  induction l with
  | nil => simp
  | cons p l ih =>
    have hp := hl p List.mem_cons_self
    rw [List.map_cons, List.prod_cons, ← Matrix.mulVec_mulVec,
      ih fun q hq => hl q (List.mem_cons_of_mem _ hq), tv_mulVec, hp]
    simp

theorem hf_span {v x z y : Fin n → E} (hx : hf σ G v x = 0) (hz : hf σ G v z = 0)
    (hy : y ∈ Submodule.span E {x, z}) : hf σ G v y = 0 := by
  obtain ⟨a, b, rfl⟩ := Submodule.mem_span_pair.1 hy
  rw [hf_add_right, hf_smul_right, hf_smul_right, hx, hz]
  simp

theorem exists_fix [CharZero E] (hG : IsHerm σ G) {γ : Matrix (Fin n) (Fin n) E} (hγ : IsU σ G γ)
    (x : Fin n → Fin n → E) (h1 : ∀ i, hf σ G (x i) (x i) ≠ 0)
    (h2 : ∀ i j, i ≠ j → hf σ G (x i) (x j) = 0) (k : ℕ) :
    ∃ l : List ((Fin n → E) × E), (∀ p ∈ l, hf σ G p.1 p.1 ≠ 0 ∧ p.2 * σ p.2 = 1) ∧
      ∀ i : Fin n, i.val < k →
        ((l.map fun p => tv σ G p.1 ((p.2 - 1) / hf σ G p.1 p.1)).prod * γ) *ᵥ x i = x i := by
  induction k with
  | zero => exact ⟨[], by simp, by simp⟩
  | succ k ih =>
    obtain ⟨l, hl, hfix⟩ := ih
    by_cases hk : k < n
    · have hU := isU_mul σ G _ _ (isU_prod hG l hl) hγ
      set δ := (l.map fun p => tv σ G p.1 ((p.2 - 1) / hf σ G p.1 p.1)).prod * γ with hδ
      obtain ⟨m, hm, hmx⟩ :=
        exists_prod_mulVec_eq hG (x ⟨k, hk⟩) (δ *ᵥ x ⟨k, hk⟩) (h1 _) (hU _ _)
      refine ⟨m ++ l, ?_, ?_⟩
      · intro p hp
        rcases List.mem_append.1 hp with hp | hp
        · exact ⟨(hm p hp).1, (hm p hp).2.1⟩
        · exact hl p hp
      · intro i hi
        rw [List.map_append, List.prod_append, mul_assoc, ← hδ, ← Matrix.mulVec_mulVec]
        rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hi | hi
        · have hne : i ≠ ⟨k, hk⟩ := fun h => by simp [h] at hi
          rw [hfix i hi]
          refine prod_fix _ m fun p hp => hf_span (h2 _ _ hne) ?_ (hm p hp).2.2
          rw [← h2 _ _ hne, ← hU (x i) (x ⟨k, hk⟩), hfix i hi]
        · have : i = ⟨k, hk⟩ := Fin.ext hi
          rw [this]
          exact hmx
    · exact ⟨l, hl, fun i _ => hfix i (lt_of_lt_of_le i.2 (not_lt.1 hk))⟩

theorem gen_and_witt : ∀ (E : Type) [Field E] [CharZero E] (n : ℕ) (σ : E →+* E) (G : Matrix (Fin n) (Fin n) E), GlobalTheory.UTrans.IsHerm σ G → (∀ γ, GlobalTheory.UTrans.IsU σ G γ → ∃ l : List ((Fin n → E) × E), (∀ p ∈ l, GlobalTheory.UTrans.hf σ G p.1 p.1 ≠ 0 ∧ p.2 * σ p.2 = 1) ∧ γ = (l.map fun p => GlobalTheory.UTrans.tv σ G p.1 ((p.2 - 1) / GlobalTheory.UTrans.hf σ G p.1 p.1)).prod) ∧ ∀ x z : Fin n → E, GlobalTheory.UTrans.hf σ G x x ≠ 0 → GlobalTheory.UTrans.hf σ G z z = GlobalTheory.UTrans.hf σ G x x → ∃ γ, GlobalTheory.UTrans.IsU σ G γ ∧ γ *ᵥ z = x := by
  intro E _ _ n σ G hG
  refine ⟨fun γ hγ => ?_, fun x z hx hz => ?_⟩
  · obtain ⟨x, h1, h2, h3⟩ := exists_basis hG
    obtain ⟨l, hl, hfix⟩ := exists_fix hG hγ x h1 h2 n
    obtain ⟨l', hl', hinv⟩ := exists_inv hG l hl
    refine ⟨l', hl', ?_⟩
    have hone : (l.map fun p => tv σ G p.1 ((p.2 - 1) / hf σ G p.1 p.1)).prod * γ = 1 := by
      apply Matrix.toLin'.injective
      refine LinearMap.ext_on_range h3 fun i => ?_
      rw [Matrix.toLin'_apply, Matrix.toLin'_apply, hfix i i.2, Matrix.one_mulVec]
    rw [← one_mul γ, ← hinv, mul_assoc, hone, mul_one]
  · obtain ⟨l, hl, e⟩ := exists_prod_mulVec_eq hG x z hx hz
    exact ⟨_, isU_prod hG l fun p hp => ⟨(hl p hp).1, (hl p hp).2.1⟩, e⟩

end GlobalTheory.UTrans.ReflChar0
