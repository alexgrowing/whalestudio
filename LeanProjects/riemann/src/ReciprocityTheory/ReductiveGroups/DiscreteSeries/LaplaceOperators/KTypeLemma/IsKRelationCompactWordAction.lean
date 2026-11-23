import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.KTypeLemma.SACommSES
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.KTypeLemma.LowestKTypeVectorExists

noncomputable section

open Finset

namespace ReciprocityTheory.ChartRestriction.DS.Lap.LemK.Cone

open ReciprocityTheory.ChartRestriction.DS

variable {n : ℕ} {M : Type*} [AddCommGroup M] [Module ℂ M] {MM : Type*} [AddCommGroup MM] [Module ℂ MM]
  {ε : Fin n → Bool} {E : Fin n → Fin n → Module.End ℂ M} {V : Submodule ℂ M}

def sC (V : Submodule ℂ M) (a b : Fin n) : Module.End ℂ (KS (n := n) V) :=
  Finsupp.lsum ℂ fun p => if p.2 = b then Finsupp.lsingle (p.1, a) else 0

theorem sC_single (a b : Fin n) (p : List (Fin n × Fin n) × Fin n) (v : V) :
    sC V a b (Finsupp.single p v) = if p.2 = b then Finsupp.single (p.1, a) v else 0 := by
  simp only [sC, Finsupp.lsum_single]; split_ifs <;> rfl

def compactWordAction (ε : Fin n → Bool) (E : Fin n → Fin n → Module.End ℂ M) (V : Submodule ℂ M)
    (hV : IsKStableSub ε E V) (a b : Fin n) : Module.End ℂ (KS (n := n) V) :=
  sA ε E V hV a b - sC V a b

theorem compactWordAction_single (hV : IsKStableSub ε E V) (a b : Fin n) (p : List (Fin n × Fin n) × Fin n) (v : V) :
    compactWordAction ε E V hV a b (Finsupp.single p v) =
      (∑ w' ∈ (adLW a b p.1).support, adLW a b p.1 w' • Finsupp.single (w', p.2) v) +
      (if h : ε a = ε b then Finsupp.single p ⟨E a b v, hV a b h v v.2⟩ else 0) := by
  rw [compactWordAction, LinearMap.sub_apply, sC_single, sub_eq_iff_eq_add]
  simp only [sA, Finsupp.lsum_single, LinearMap.add_apply, LinearMap.sum_apply, LinearMap.smul_apply,
    Finsupp.lsingle_apply]
  congr 1
  · congr 1
    split_ifs <;> rfl
  · split_ifs <;> rfl

theorem sC_mul (a b c d : Fin n) : sC V a b * sC V c d = if b = c then sC V a d else 0 := by
  refine Finsupp.lhom_ext fun p v => ?_
  rw [Module.End.mul_apply, sC_single]
  by_cases h1 : p.2 = d <;> by_cases h2 : b = c <;> simp [h1, h2, sC_single, eq_comm]

theorem compactWordAction_commute (hV : IsKStableSub ε E V) (a b c d : Fin n) :
    compactWordAction ε E V hV a b * sC V c d = sC V c d * compactWordAction ε E V hV a b := by
  refine Finsupp.lhom_ext fun p v => ?_
  rw [Module.End.mul_apply, Module.End.mul_apply, sC_single, compactWordAction_single, map_add, map_sum]
  by_cases h1 : p.2 = d <;> by_cases h : ε a = ε b <;>
    simp only [h1, h, if_true, if_false, dif_pos, dif_neg, not_false_eq_true, compactWordAction_single, map_smul,
      sC_single, map_zero, smul_zero, sum_const_zero, add_zero]

theorem isKRelation_compactWordAction (hV : IsKStableSub ε E V) (hE : IsGlRep E) : IsKRel ε (compactWordAction ε E V hV) := by
  intro a b c d hab hcd
  have h1 := sA_isKRel ε E V hV hE a b c d hab hcd
  have e : ∀ x y, sA ε E V hV x y = compactWordAction ε E V hV x y + sC V x y := fun x y => by simp [compactWordAction]
  rw [e a b, e c d, e a d, e c b] at h1
  simp only [add_mul, mul_add, sC_mul, compactWordAction_commute] at h1
  have h2 : compactWordAction ε E V hV a b * compactWordAction ε E V hV c d - compactWordAction ε E V hV c d * compactWordAction ε E V hV a b =
      ((if b = c then compactWordAction ε E V hV a d + sC V a d else 0) -
        if d = a then compactWordAction ε E V hV c b + sC V c b else 0) -
      ((if b = c then sC V a d else 0) - if d = a then sC V c b else 0) := by
    rw [← h1]; abel
  rw [h2]
  split_ifs <;> abel

theorem sT_sC (a b : Fin n) (x : KS (n := n) V) :
    sT E V (sC V a b x) = Pi.single a (sT E V x b) := by
  induction x using Finsupp.induction_linear with
  | zero => simp
  | add x y h h' => simp only [map_add, h, h', Pi.add_apply, Pi.single_add]
  | single p v =>
    obtain ⟨w, c⟩ := p
    rw [sC_single, sT_single]
    by_cases h : c = b
    · subst h; simp [sT_single]
    · simp [h, Ne.symm h]

theorem sθ_sC (EM : Fin n → Fin n → Module.End ℂ MM) (φ : MM) (ℓ : V →ₗ[ℂ] ℂ) (a b : Fin n)
    (x : KS (n := n) V) : sθ V EM φ ℓ (sC V a b x) = Pi.single a (sθ V EM φ ℓ x b) := by
  induction x using Finsupp.induction_linear with
  | zero => simp
  | add x y h h' => simp only [map_add, h, h', Pi.add_apply, Pi.single_add]
  | single p v =>
    obtain ⟨w, c⟩ := p
    rw [sC_single, sθ_single]
    by_cases h : c = b
    · subst h; simp [sθ_single]
    · simp [h, Ne.symm h]

theorem tensV_eq (E : Fin n → Fin n → Module.End ℂ M) (a b : Fin n) (f : Fin n → M) (c : Fin n) :
    tensV E a b f c = E a b (f c) + (Pi.single a (f b) : Fin n → M) c := by
  simp only [tensV, LinearMap.pi_apply, LinearMap.add_apply, LinearMap.comp_apply, Pi.single_apply]
  split_ifs <;> rfl

theorem contraction_compactWordAction (hV : IsKStableSub ε E V) (hE : IsGlRep E) (a b : Fin n) (hab : ε a = ε b)
    (x : KS (n := n) V) (c : Fin n) : sT E V (compactWordAction ε E V hV a b x) c = E a b (sT E V x c) := by
  rw [compactWordAction, LinearMap.sub_apply, map_sub, sT_sA ε E V hV hE a b hab, sT_sC, Pi.sub_apply, tensV_eq,
    add_sub_cancel_right]

theorem exists_stable (hV : IsKStableSub ε E V) (EM : Fin n → Fin n → Module.End ℂ MM) (φ : MM)
    (ℓ : V →ₗ[ℂ] ℂ) (W0 : Submodule ℂ (KS (n := n) V)) (hW0 : IsKStableSub ε (compactWordAction ε E V hV) W0)
    (hθ : ∀ x ∈ W0, sθ V EM φ ℓ x = 0) :
    ∃ W : Submodule ℂ (KS (n := n) V), W0 ≤ W ∧ IsKStableSub ε (sA ε E V hV) W ∧
      ∀ x ∈ W, sθ V EM φ ℓ x = 0 := by
  let G : Set (KS (n := n) V) := {x | x ∈ W0 ∨ ∃ c d, ∃ y ∈ W0, x = sC V c d y}
  refine ⟨Submodule.span ℂ G, fun x hx => Submodule.subset_span (Or.inl hx), fun a b hab x hx => ?_,
    fun x hx => ?_⟩
  · refine (Submodule.span_le (p := (Submodule.span ℂ G).comap (sA ε E V hV a b))).mpr ?_ hx
    have e : ∀ y, sA ε E V hV a b y = compactWordAction ε E V hV a b y + sC V a b y := fun y => by simp [compactWordAction]
    rintro y (hy | ⟨c, d, y, hy, rfl⟩)
    · show sA ε E V hV a b y ∈ Submodule.span ℂ G
      rw [e]
      exact add_mem (Submodule.subset_span (Or.inl (hW0 a b hab y hy)))
        (Submodule.subset_span (Or.inr ⟨a, b, y, hy, rfl⟩))
    · show sA ε E V hV a b (sC V c d y) ∈ Submodule.span ℂ G
      rw [e, ← Module.End.mul_apply, compactWordAction_commute, ← Module.End.mul_apply (sC V a b), sC_mul]
      refine add_mem (Submodule.subset_span (Or.inr ⟨c, d, _, hW0 a b hab y hy, rfl⟩)) ?_
      split_ifs
      · exact Submodule.subset_span (Or.inr ⟨a, d, y, hy, rfl⟩)
      · exact Submodule.zero_mem _
  · refine (Submodule.span_le (p := LinearMap.ker (sθ V EM φ ℓ))).mpr ?_ hx
    rintro y (hy | ⟨c, d, y, hy, rfl⟩)
    · exact hθ y hy
    · show sθ V EM φ ℓ (sC V c d y) = 0
      rw [sθ_sC, hθ y hy]; simp

theorem verma_weight (EM : Fin n → Fin n → Module.End ℂ MM) (hEM : IsGlRep EM) (φ : MM) (ν : Fin n → ℝ)
    (hlow : ∀ a b, b < a → EM a b φ = 0) (hwt : ∀ a, EM a a φ = ((ν a : ℝ) : ℂ) • φ)
    (hgen : genSub EM (Submodule.span ℂ {φ}) = ⊤) {μ : Fin n → ℝ} {x : MM} (hx0 : x ≠ 0)
    (hx : ∀ a, EM a a x = ((μ a : ℝ) : ℂ) • x) : InRootCone (μ - ν) := by
  by_contra hμ
  refine hx0 (vc_eq_zero_of_mem_span EM (fun β => InRootCone (β - ν)) hμ hx ?_)
  have h1 := vc_genSub_le_mon EM hEM φ ⊥ (fun a b y hy => by simp_all)
    (fun a b h => by simp [hlow a b h]) (fun a => ⟨_, hwt a⟩)
  rw [hgen, sup_bot_eq] at h1
  refine Submodule.span_mono ?_ (h1 Submodule.mem_top)
  intro w hw
  obtain ⟨k, hk⟩ := Set.mem_iUnion.mp hw
  obtain ⟨β, h2, h3, -⟩ := vcMon_weight EM hEM hwt k w hk
  exact ⟨β, h3, h2⟩

end ReciprocityTheory.ChartRestriction.DS.Lap.LemK.Cone
