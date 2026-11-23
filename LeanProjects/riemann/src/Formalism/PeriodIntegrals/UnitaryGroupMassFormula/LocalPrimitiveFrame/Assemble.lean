import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalPrimitiveFrame.StepsTop

noncomputable section

namespace PI.LocFramePrimWork

open NumberField IsDedekindDomain PI.LocFramePrim
open scoped TensorProduct

section Assemble

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (v : HeightOneSpectrum (𝓞 F)) {n : ℕ}

def Assemble_bc (ψ : (Fin n → E) →ₗ[E] E) :
    (Fin n → Fv F v ⊗[F] E) →ₗ[Fv F v ⊗[F] E] Fv F v ⊗[F] E :=
  ∑ i, inclR (F := F) (Fv F v) (ψ fun j => if i = j then 1 else 0) • LinearMap.proj i

theorem Assemble_bc_ratV (ψ : (Fin n → E) →ₗ[E] E) (y : Fin n → E) :
    Assemble_bc v ψ (ratV (F := F) (Fv F v) y) = inclR (F := F) (Fv F v) (ψ y) := by
  conv_rhs => rw [LinearMap.pi_apply_eq_sum_univ ψ y]
  simp only [Assemble_bc, LinearMap.sum_apply, LinearMap.smul_apply,
    LinearMap.coe_proj, Function.eval, ratV, smul_eq_mul, map_sum, map_mul]
  exact Finset.sum_congr rfl fun i _ => mul_comm _ _

theorem Assemble_smul_eq (t : v.adicCompletionIntegers F) (x : Fin n → Fv F v ⊗[F] E) :
    t • x = sc (E := E) v (t : Fv F v) • x := by
  funext i
  change (t : Fv F v) • x i = sc (E := E) v (t : Fv F v) * x i
  rw [Algebra.smul_def]
  rfl

theorem Assemble_smul_eq' (t : v.adicCompletionIntegers F) (y : Fv F v ⊗[F] E) :
    t • y = sc (E := E) v (t : Fv F v) * y := by
  change (t : Fv F v) • y = _
  rw [Algebra.smul_def]
  rfl

theorem Assemble_bc_span (ψ : (Fin n → E) →ₗ[E] E) (Λ : Set (Fin n → E)) (S : Set E)
    (hS : ∀ l ∈ Λ, ψ l ∈ S) (x : Fin n → Fv F v ⊗[F] E) (hx : x ∈ latLoc (E := E) v Λ) :
    Assemble_bc v ψ x ∈ Submodule.span (v.adicCompletionIntegers F) (inclR (F := F) (Fv F v) '' S) := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨l, hl, rfl⟩ := hx
    rw [Assemble_bc_ratV]
    exact Submodule.subset_span ⟨_, hS l hl, rfl⟩
  | zero => rw [map_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | smul t x _ hx =>
    rw [Assemble_smul_eq, map_smul, smul_eq_mul, ← Assemble_smul_eq']
    exact Submodule.smul_mem _ t hx

theorem Assemble_dV_ne_zero : dV v ≠ 0 := by
  unfold dV
  split_ifs with h
  · exact h.choose_spec.1
  · exact one_ne_zero

theorem Assemble_one_mem : (1 : Fv F v ⊗[F] E) ∈ OEv (E := E) v := by
  refine Submodule.subset_span ⟨1, Set.mem_univ _, ?_⟩
  simp [inclR, Algebra.TensorProduct.one_def]

theorem Assemble_OEv_of_mem (y : Fv F v ⊗[F] E)
    (hy : y ∈ Submodule.span (v.adicCompletionIntegers F)
      (inclR (F := F) (Fv F v) '' Set.range ((↑) : 𝓞 E → E))) : y ∈ OEv (E := E) v := by
  have h : inclR (F := F) (Fv F v) '' Set.range ((↑) : 𝓞 E → E) =
      (fun x : 𝓞 E => inclR (F := F) (Fv F v) (x : E)) '' Set.univ := by
    ext y; simp
  rw [h] at hy
  exact hy

theorem Assemble_ratTup_castSucc {r : ℕ} (e : Fin r → Fin n → E) (z : Fin n → E) (a : Fin r) :
    ratTup (F := F) (Fv F v) (Fin.snoc e z : Fin (r + 1) → Fin n → E) (Fin.castSucc a) =
      ratV (F := F) (Fv F v) (e a) := by
  funext i; simp [ratTup, ratV]

theorem Assemble_ratTup_last {r : ℕ} (e : Fin r → Fin n → E) (z : Fin n → E) :
    ratTup (F := F) (Fv F v) (Fin.snoc e z : Fin (r + 1) → Fin n → E) (Fin.last r) =
      ratV (F := F) (Fv F v) z := by
  funext i; simp [ratTup, ratV]

theorem Assemble_alp_castSucc {r : ℕ} (a : Fin r) :
    alp v r (Fin.castSucc a) = (dV v)⁻¹ ^ (r - (a : ℕ)) := by
  simp [alp, a.isLt]

theorem Assemble_alp_last (r : ℕ) : alp v r (Fin.last r) = 1 := by
  simp [alp]

theorem Assemble_sc_one : sc (E := E) v 1 = 1 := rfl

theorem Assemble_ratV_smul (x : E) (y : Fin n → E) :
    inclR (F := F) (Fv F v) x • ratV (F := F) (Fv F v) y = ratV (F := F) (Fv F v) (x • y) := by
  funext i; simp [ratV, map_mul]

theorem Assemble_exp {r : ℕ} (a : Fin r) :
    (-((r : ℤ) - ((a : ℕ) : ℤ))) = -(((r - (a : ℕ) : ℕ)) : ℤ) := by
  rw [Nat.cast_sub a.isLt.le]

theorem primitiveOfDualFunctionals : Assemble := by
  intro F E _ _ _ _ _ v n r Λ Lb e f z hD hΛ hz φ φz p1 p2 p3 p4 p5 p6 p7
  have hLbΛ : Lb ≤ Λ := by rw [hΛ]; exact le_sup_right.trans le_sup_left
  have hAΛ : latSpan (fun a : Fin r => ddE F ^ (-((r : ℤ) - (a : ℕ)))) e ≤ Λ := by
    rw [hΛ]; exact le_sup_left.trans le_sup_left
  have hBΛ : latSpan (fun a : Fin r => (ddE F ^ (-((r : ℤ) - (a : ℕ))))⁻¹) f ≤ Λ := by
    rw [hΛ]; exact le_sup_right
  set X := ratTup (F := F) (Fv F v) (Fin.snoc e z : Fin (r + 1) → Fin n → E) with hX

  have hφΛ : ∀ a : Fin r, ∀ l ∈ Λ,
      φ a l ∈ ((ddE F ^ (-((r : ℤ) - (a : ℕ))) : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) : Set E) := by
    intro a
    let I : Submodule (𝓞 E) E :=
      ((ddE F ^ (-((r : ℤ) - (a : ℕ))) : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) : Submodule (𝓞 E) E)
    have hle : Λ ≤ I.comap ((φ a).restrictScalars (𝓞 E)) := by
      rw [hΛ]
      refine sup_le (sup_le ?_ ?_) ?_
      · rw [latSpan, Submodule.span_le]
        rintro _ ⟨b, x, hx, rfl⟩
        rw [SetLike.mem_coe, Submodule.mem_comap, LinearMap.restrictScalars_apply, map_smul, p1,
          smul_eq_mul]
        by_cases hab : a = b
        · subst hab; rw [if_pos rfl, mul_one]; exact hx
        · simp [hab]
      · intro l hl
        rw [Submodule.mem_comap, LinearMap.restrictScalars_apply, p3 a l hl]
        exact zero_mem _
      · rw [latSpan, Submodule.span_le]
        rintro _ ⟨b, x, hx, rfl⟩
        rw [SetLike.mem_coe, Submodule.mem_comap, LinearMap.restrictScalars_apply, map_smul, p2,
          smul_zero]
        exact zero_mem _
    exact fun l hl => hle hl
  have hφzΛ : ∀ l ∈ Λ, φz l ∈ Set.range ((↑) : 𝓞 E → E) := by
    have hle : Λ ≤ (1 : Submodule (𝓞 E) E).comap (φz.restrictScalars (𝓞 E)) := by
      rw [hΛ]
      refine sup_le (sup_le ?_ ?_) ?_
      · rw [latSpan, Submodule.span_le]
        rintro _ ⟨b, x, hx, rfl⟩
        rw [SetLike.mem_coe, Submodule.mem_comap, LinearMap.restrictScalars_apply, map_smul, p4,
          smul_zero]
        exact zero_mem _
      · intro l hl
        rw [Submodule.mem_comap, LinearMap.restrictScalars_apply, Submodule.mem_one]
        obtain ⟨o, ho⟩ := p7 l hl
        exact ⟨o, ho.symm⟩
      · rw [latSpan, Submodule.span_le]
        rintro _ ⟨b, x, hx, rfl⟩
        rw [SetLike.mem_coe, Submodule.mem_comap, LinearMap.restrictScalars_apply, map_smul, p5,
          smul_zero]
        exact zero_mem _
    intro l hl
    obtain ⟨o, ho⟩ := Submodule.mem_one.1 (hle hl)
    exact ⟨o, ho⟩
  have hunit : ∀ k : ℕ, IsUnit (sc (E := E) v ((dV v)⁻¹ ^ k)) := fun k =>
    (IsUnit.mk0 _ (pow_ne_zero k (inv_ne_zero (Assemble_dV_ne_zero v)))).map
      (algebraMap (Fv F v) (Fv F v ⊗[F] E))
  have hlocF : ∀ i, locF v X i = sc (E := E) v (alp v r i) • X i := fun i => rfl
  refine ⟨fun i => ?_, fun c hc i => ?_⟩
  ·
    induction i using Fin.lastCases with
    | last =>
      rw [hlocF, Assemble_alp_last, Assemble_sc_one, one_smul, hX, Assemble_ratTup_last]
      exact Submodule.subset_span ⟨z, hLbΛ hz, rfl⟩
    | cast a =>
      rw [hlocF, Assemble_alp_castSucc, hX, Assemble_ratTup_castSucc]
      have hy := (hD (r - (a : ℕ)) (sc (E := E) v ((dV v)⁻¹ ^ (r - (a : ℕ))))).2
        ⟨1, Assemble_one_mem v, (mul_one _).symm⟩
      have key : ∀ y ∈ Submodule.span (v.adicCompletionIntegers F) (inclR (F := F) (Fv F v) ''
          ((ddE F ^ (-(((r - (a : ℕ) : ℕ)) : ℤ)) : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) : Set E)),
          y • ratV (F := F) (Fv F v) (e a) ∈ latLoc (E := E) v (Λ : Set (Fin n → E)) := by
        intro y hy
        induction hy using Submodule.span_induction with
        | mem y hy =>
          obtain ⟨x, hx, rfl⟩ := hy
          rw [Assemble_ratV_smul]
          refine Submodule.subset_span ⟨x • e a, hAΛ (Submodule.subset_span ⟨a, x, ?_, rfl⟩), rfl⟩
          show x ∈ ddE F ^ (-((r : ℤ) - ((a : ℕ) : ℤ)))
          rw [Assemble_exp]; exact hx
        | zero => rw [zero_smul]; exact zero_mem _
        | add x y _ _ hx hy => rw [add_smul]; exact add_mem hx hy
        | smul t y _ hy =>
          rw [Assemble_smul_eq', mul_smul, ← Assemble_smul_eq]
          exact Submodule.smul_mem _ t hy
      exact key _ hy
  ·
    have hsum : ∀ ψ : (Fin n → E) →ₗ[E] E, Assemble_bc v ψ (∑ i, c i • locF v X i) =
        (∑ a : Fin r, c (Fin.castSucc a) * sc (E := E) v ((dV v)⁻¹ ^ (r - (a : ℕ))) *
          inclR (F := F) (Fv F v) (ψ (e a))) + c (Fin.last r) * inclR (F := F) (Fv F v) (ψ z) := by
      intro ψ
      rw [map_sum, Fin.sum_univ_castSucc]
      simp only [map_smul, locF, smul_eq_mul, hX, Assemble_ratTup_castSucc, Assemble_ratTup_last,
        Assemble_alp_castSucc, Assemble_alp_last, Assemble_sc_one, one_mul, Assemble_bc_ratV, mul_assoc]
    induction i using Fin.lastCases with
    | last =>
      have h := Assemble_bc_span v φz (Λ : Set (Fin n → E)) _ hφzΛ _ hc
      rw [hsum] at h
      simp only [p4, p6, map_zero, mul_zero, Finset.sum_const_zero, zero_add, map_one,
        mul_one] at h
      exact Assemble_OEv_of_mem v _ h
    | cast a =>
      have h := Assemble_bc_span v (φ a) (Λ : Set (Fin n → E)) _ (hφΛ a) _ hc
      rw [hsum] at h
      simp only [p1, p3 a z hz, map_zero, mul_zero, add_zero, apply_ite (inclR (F := F) (Fv F v)),
        map_one, mul_ite, mul_one, Finset.sum_ite_eq, Finset.mem_univ, if_true] at h
      rw [Assemble_exp] at h
      obtain ⟨p, hp, hcp⟩ := (hD (r - (a : ℕ)) _).1 h
      rw [mul_comm] at hcp
      rw [(hunit _).mul_left_cancel hcp]
      exact hp

end Assemble

end PI.LocFramePrimWork
