import Mathlib
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsFlagBundleForms
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

noncomputable section

set_option linter.unusedSectionVars false

namespace FlagBundleSectionForms

variable {F : Type} [Field F] {Ω : Type} [Field Ω] [Algebra F Ω]
  {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)]

def chartPow (y : (Σ k, ι k) → Ω) (c : ∀ k, ι k) (d : K → ℤ) : Ω :=
  ∏ k, y ⟨k, c k⟩ ^ d k

theorem chartPow_add {y : (Σ k, ι k) → Ω} {c : ∀ k, ι k} (hY : ∀ k, y ⟨k, c k⟩ ≠ 0) (d d' : K → ℤ) :
    chartPow y c (d + d') = chartPow y c d * chartPow y c d' := by
  simp [chartPow, zpow_add₀ (hY _), Finset.prod_mul_distrib]

theorem chartPow_ne_zero {y : (Σ k, ι k) → Ω} {c : ∀ k, ι k} (hY : ∀ k, y ⟨k, c k⟩ ≠ 0) (d : K → ℤ) :
    chartPow y c d ≠ 0 :=
  Finset.prod_ne_zero_iff.2 fun k _ => zpow_ne_zero _ (hY k)

theorem chartPow_natCast (y : (Σ k, ι k) → Ω) (c : ∀ k, ι k) (α : K → ℕ) :
    chartPow y c (fun k => (α k : ℤ)) = ∏ k, y ⟨k, c k⟩ ^ α k := by
  simp [chartPow]

theorem segreVec_pow (y : (Σ k, ι k) → Ω) (c : ∀ k, ι k) (n : ℕ) :
    segreVec y c ^ n = chartPow y c (fun _ => (n : ℤ)) := by
  simp [segreVec, chartPow, Finset.prod_pow]

section Dual

variable {N : ℕ} {E : Type} [AddCommGroup E] [Module Ω E]

theorem exists_flag_dual (y : (Σ k, ι k) → Ω) (B : ChartBundle F (segreVec y) N E)
    (w : Module.Basis (Fin N) Ω E) (b : Fin N → K → ℤ) (hfl : IsFlagFrame y B w b)
    (c : ∀ k, ι k) (hc : segreVec y c ≠ 0) (i : Fin N) :
    ∃ ψ : Module.Dual Ω E, (∀ v ∈ B.lat c, ψ v ∈ chartRing F (segreVec y) c) ∧
      (∀ j, j < i → ψ (w j) = 0) ∧ ψ (w i) = (chartPow y c (b i))⁻¹ := by
  have hY : ∀ k, y ⟨k, c k⟩ ≠ 0 := fun k => (Finset.prod_ne_zero_iff.1 hc) k (Finset.mem_univ _)
  have hp : ∀ j, chartPow y c (b j) ≠ 0 := fun j => chartPow_ne_zero hY _
  have hgr : ∀ (j : Fin N) (s : Ω), (∃ v ∈ B.lat c, (∀ m, j < m → w.repr v m = 0) ∧ w.repr v j = s) ↔
      ∃ r ∈ chartRing F (segreVec y) c, s = r * chartPow y c (b j) := fun j s => by
    have h := hfl.graded c hc j
    rw [Set.ext_iff] at h
    exact h s
  have he : ∀ j : Fin N, ∃ v ∈ B.lat c, (∀ m, j < m → w.repr v m = 0) ∧
      w.repr v j = chartPow y c (b j) := fun j =>
    (hgr j _).2 ⟨1, one_mem _, (one_mul _).symm⟩
  choose e heL heT heD using he

  have hx : ∀ j : Fin N, e j - chartPow y c (b j) • w j ∈
      Submodule.span Ω (w '' {m | (m : ℕ) < j}) := by
    intro j
    rw [w.mem_span_image]
    intro m hm
    simp only [Finset.mem_coe, Finsupp.mem_support_iff] at hm
    simp only [Set.mem_setOf_eq]
    by_contra hjm
    push_neg at hjm
    apply hm
    rcases hjm.lt_or_eq with h | h
    · have hne : j ≠ m := fun h' => (ne_of_lt h) (congrArg Fin.val h')
      simp [heT j m h, Finsupp.single_apply, hne]
    · have : m = j := Fin.ext h.symm
      subst this
      simp [heD]
  have hspan : ∀ m ≤ N, Submodule.span Ω (e '' {j | (j : ℕ) < m}) =
      Submodule.span Ω (w '' {j | (j : ℕ) < m}) := by
    intro m
    induction m with
    | zero => intro _; simp
    | succ m ih =>
      intro hm
      have hS : {j : Fin N | (j : ℕ) < m + 1} = insert (⟨m, hm⟩ : Fin N) {j : Fin N | (j : ℕ) < m} := by
        ext j
        simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Fin.ext_iff]
        omega
      rw [hS, Set.image_insert_eq, Set.image_insert_eq, Submodule.span_insert, Submodule.span_insert,
        ih (by omega)]
      have hxm := hx ⟨m, hm⟩
      apply le_antisymm
      · refine sup_le ?_ le_sup_right
        rw [Submodule.span_singleton_le_iff_mem]
        have := Submodule.add_mem_sup
          (Submodule.smul_mem _ (chartPow y c (b ⟨m, hm⟩)) (Submodule.mem_span_singleton_self (w ⟨m, hm⟩)))
          hxm
        simpa using this
      · refine sup_le ?_ le_sup_right
        rw [Submodule.span_singleton_le_iff_mem]
        have := Submodule.smul_mem _ (chartPow y c (b ⟨m, hm⟩))⁻¹ (Submodule.sub_mem_sup
          (Submodule.mem_span_singleton_self (e ⟨m, hm⟩)) hxm)
        simpa [smul_smul, inv_mul_cancel₀ (hp _)] using this
  have htop : ⊤ ≤ Submodule.span Ω (Set.range e) := by
    have h := hspan N le_rfl
    have hu : {j : Fin N | (j : ℕ) < N} = Set.univ := Set.eq_univ_of_forall fun j => j.isLt
    rw [hu, Set.image_univ, Set.image_univ, w.span_eq] at h
    rw [h]
  have hli : LinearIndependent Ω e :=
    linearIndependent_of_top_le_span_of_card_eq_finrank htop (by rw [Module.finrank_eq_card_basis w])
  let eb := Module.Basis.mk hli htop
  have heb : ⇑eb = e := funext (Module.Basis.mk_apply hli htop)
  have hvan : ∀ x ∈ Submodule.span Ω (w '' {j : Fin N | (j : ℕ) < i}), eb.repr x i = 0 := by
    intro x hx'
    rw [← hspan i i.isLt.le, ← heb, eb.mem_span_image] at hx'
    by_contra h
    exact lt_irrefl (i : ℕ) (hx' (Finsupp.mem_support_iff.2 h))
  have hself : ∀ j m, eb.repr (e j) m = Finsupp.single j 1 m := fun j m => by
    rw [← heb, eb.repr_self]
  have hint : ∀ m ≤ N, ∀ v ∈ B.lat c, (∀ j : Fin N, m ≤ (j : ℕ) → w.repr v j = 0) →
      ∀ j, eb.repr v j ∈ chartRing F (segreVec y) c := by
    intro m
    induction m with
    | zero =>
      intro _ v _ hv j
      have : v = 0 := w.repr.injective (by ext j; simp [hv j (Nat.zero_le _)])
      simp [this]
    | succ m ih =>
      intro hm v hvL hv j
      obtain ⟨r, hr, hrv⟩ := (hgr ⟨m, hm⟩ (w.repr v ⟨m, hm⟩)).1 ⟨v, hvL, fun j hj => hv j hj, rfl⟩
      have hv' : v - r • e ⟨m, hm⟩ ∈ B.lat c := sub_mem hvL (B.stable c r hr _ (heL _))
      have h' := ih (by omega) _ hv' (by
        intro j hj
        rcases hj.lt_or_eq with h | h
        · simp [hv j h, heT ⟨m, hm⟩ j h]
        · have : j = ⟨m, hm⟩ := Fin.ext h.symm
          subst this
          simp [heD, hrv])
      have hsplit : eb.repr v j = eb.repr (v - r • e ⟨m, hm⟩) j + r * eb.repr (e ⟨m, hm⟩) j := by
        rw [map_sub, map_smul, Finsupp.sub_apply, Finsupp.smul_apply, smul_eq_mul, sub_add_cancel]
      rw [hsplit, hself]
      refine add_mem (h' j) (mul_mem hr ?_)
      rw [Finsupp.single_apply]
      split_ifs
      · exact one_mem _
      · exact zero_mem _
  refine ⟨eb.coord i, fun v hv => ?_, fun j hj => ?_, ?_⟩
  · exact hint N le_rfl v hv (fun j hj => absurd j.isLt (by omega)) i
  · exact hvan _ (Submodule.subset_span ⟨j, hj, rfl⟩)
  · have hw : w i = (chartPow y c (b i))⁻¹ • (e i - (e i - chartPow y c (b i) • w i)) := by
      rw [sub_sub_cancel, smul_smul, inv_mul_cancel₀ (hp i), one_smul]
    rw [Module.Basis.coord_apply, hw, map_smul, map_sub, Finsupp.smul_apply, Finsupp.sub_apply,
      hself, hvan _ (hx i)]
    simp

end Dual

section Forms

variable {M N : ℕ} {E : Type} [AddCommGroup E] [Module Ω E] {Φ : Type} [Field Φ] [Algebra Ω Φ]

def liftNat (α : K → ℕ) : Option K → ℕ := fun o => Option.elim o 0 α

def chartMono (M : ℕ) (c : ∀ k, ι k) (α : K → ℕ) : MRing (bundleIdx ι M) F :=
  ∏ k, X (⟨some k, c k⟩ : Σ o, bundleIdx ι M o) ^ α k

theorem chartMono_homog (M : ℕ) (c : ∀ k, ι k) (α : K → ℕ) :
    IsMultiHomog (chartMono (F := F) M c α) (liftNat α) := by
  have h := IsWeightedHomogeneous.prod (R := F) Finset.univ
    (fun k => X (⟨some k, c k⟩ : Σ o, bundleIdx ι M o) ^ α k)
    (fun k => α k • blockWeight (bundleIdx ι M) ⟨some k, c k⟩)
    (fun k _ => (isWeightedHomogeneous_X F _ _).pow (α k))
  have hw : liftNat α = ∑ k, α k • blockWeight (bundleIdx ι M) ⟨some k, c k⟩ := by
    funext o
    cases o with
    | none => simp [liftNat, blockWeight, Finset.sum_apply, Pi.single_apply]
    | some k => simp [liftNat, blockWeight, Finset.sum_apply, Pi.single_apply]
  rw [IsMultiHomog, chartMono, hw]
  exact h

theorem eval_chartMono (y : (Σ k, ι k) → Ω) (w : Module.Basis (Fin N) Ω E) (φ : Fin M → Module.Dual Ω E)
    (t : Fin N → Φ) (c : ∀ k, ι k) (α : K → ℕ) :
    eval₂ ((algebraMap Ω Φ).comp (algebraMap F Ω)) (projCoord y w φ t) (chartMono M c α) =
      algebraMap Ω Φ (∏ k, y ⟨k, c k⟩ ^ α k) := by
  simp [chartMono, eval₂_prod, eval₂_pow, eval₂_X, projCoord, map_prod]

theorem chartRing_forms (y : (Σ k, ι k) → Ω) (w : Module.Basis (Fin N) Ω E)
    (φ : Fin M → Module.Dual Ω E) (t : Fin N → Φ) (c : ∀ k, ι k) (hc : segreVec y c ≠ 0) {u : Ω}
    (hu : u ∈ chartRing F (segreVec y) c) :
    ∃ (n : ℕ) (U : MRing (bundleIdx ι M) F), IsMultiHomog U (liftNat fun _ => n) ∧
      eval₂ ((algebraMap Ω Φ).comp (algebraMap F Ω)) (projCoord y w φ t) U =
        algebraMap Ω Φ (u * segreVec y c ^ n) := by
  have hlift : ∀ n n' : ℕ, liftNat (K := K) (fun _ => n + n') = liftNat (fun _ => n) + liftNat (fun _ => n') := by
    intro n n'; funext o; cases o <;> simp [liftNat]
  have hQ : ∀ n : ℕ, eval₂ ((algebraMap Ω Φ).comp (algebraMap F Ω)) (projCoord y w φ t)
      (chartMono M c (fun _ => n)) = algebraMap Ω Φ (segreVec y c ^ n) := by
    intro n
    rw [eval_chartMono, segreVec, Finset.prod_pow]
  induction hu using Algebra.adjoin_induction with
  | mem z hz =>
    obtain ⟨j, rfl⟩ := hz
    refine ⟨1, chartMono M j (fun _ => 1), chartMono_homog M j _, ?_⟩
    rw [eval_chartMono, pow_one, div_mul_cancel₀ _ hc]
    simp [segreVec]
  | algebraMap r =>
    refine ⟨0, C r, ?_, ?_⟩
    · have h0 : liftNat (K := K) (fun _ => 0) = 0 := by funext o; cases o <;> rfl
      rw [h0]
      exact isWeightedHomogeneous_C _ _
    · simp
  | add z z' _ _ hz hz' =>
    obtain ⟨n, U, hU, hUe⟩ := hz
    obtain ⟨n', U', hU', hUe'⟩ := hz'
    refine ⟨n + n', U * chartMono M c (fun _ => n') + U' * chartMono M c (fun _ => n), ?_, ?_⟩
    · rw [hlift]
      refine (hU.mul (chartMono_homog M c _)).add ?_
      rw [add_comm]
      exact hU'.mul (chartMono_homog M c _)
    · rw [eval₂_add, eval₂_mul, eval₂_mul, hUe, hUe', hQ, hQ, ← map_mul, ← map_mul, ← map_add]
      congr 1
      ring
  | mul z z' _ _ hz hz' =>
    obtain ⟨n, U, hU, hUe⟩ := hz
    obtain ⟨n', U', hU', hUe'⟩ := hz'
    refine ⟨n + n', U * U', ?_, ?_⟩
    · rw [hlift]
      exact hU.mul hU'
    · rw [eval₂_mul, hUe, hUe', ← map_mul]
      congr 1
      ring

theorem eval_eq_zero_of_mem_projIdeal (y : (Σ k, ι k) → Ω) (w : Module.Basis (Fin N) Ω E)
    (φ : Fin M → Module.Dual Ω E) (t : Fin N → Φ) {f : MRing (bundleIdx ι M) F}
    (hf : f ∈ projIdeal F y w φ t) :
    eval₂ ((algebraMap Ω Φ).comp (algebraMap F Ω)) (projCoord y w φ t) f = 0 := by
  have h : (MvPolynomial.eval (fun _ : Option K => (1 : Φ))).comp
      (eval₂Hom (C.comp ((algebraMap Ω Φ).comp (algebraMap F Ω)))
        (fun p => C (projCoord y w φ t p) * X p.1)) =
      eval₂Hom ((algebraMap Ω Φ).comp (algebraMap F Ω)) (projCoord y w φ t) := by
    apply MvPolynomial.ringHom_ext
    · intro r; simp
    · intro p; simp
  rw [projIdeal, RingHom.mem_ker] at hf
  rw [← coe_eval₂Hom, ← h, RingHom.comp_apply, hf, map_zero]

end Forms

end FlagBundleSectionForms

end

end GroundTheory.Heights₂.Heights.NumbersDVR
