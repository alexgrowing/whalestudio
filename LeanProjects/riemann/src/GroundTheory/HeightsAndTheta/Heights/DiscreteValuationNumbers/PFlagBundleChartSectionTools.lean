import Mathlib
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsFlagBundleChartSection
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PFlagBundleSectionFormsTools
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PProjIdealFormValue
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

noncomputable section

set_option linter.unusedSectionVars false

namespace FlagBundleChartSection

open FlagBundleSectionForms (chartPow chartMono liftNat)

variable {F : Type} [Field F] {Ω : Type} [Field Ω] [Algebra F Ω]
  {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type}

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

theorem chartMono_mul (c : ∀ k, ι k) (α α' : K → ℕ) :
    chartMono (F := F) M c α * chartMono M c α' = chartMono M c (α + α') := by
  simp [chartMono, ← Finset.prod_mul_distrib, pow_add]

theorem chartMono_pow_dvd (c : ∀ k, ι k) (δ : K → ℕ) (D : ℕ) :
    chartMono (F := F) M c δ ^ D ∣
      (∏ k, (X ⟨some k, c k⟩ : MRing (bundleIdx ι M) F)) ^ (D * ∑ k, δ k) := by
  rw [chartMono, ← Finset.prod_pow, ← Finset.prod_pow]
  refine Finset.prod_dvd_prod_of_dvd _ _ fun k _ => ?_
  rw [← pow_mul]
  refine pow_dvd_pow _ ?_
  calc δ k * D = D * δ k := Nat.mul_comm _ _
    _ ≤ D * ∑ k, δ k := Nat.mul_le_mul_left D (Finset.single_le_sum (fun _ _ => Nat.zero_le _)
        (Finset.mem_univ k))

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

theorem chartRing_forms_fin (y : (Σ k, ι k) → Ω) (w : Module.Basis (Fin N) Ω E)
    (φ : Fin M → Module.Dual Ω E) (t : Fin N → Φ) (c : ∀ k, ι k) (hc : segreVec y c ≠ 0) {L : ℕ}
    {u : Fin L → Ω} (hu : ∀ l, u l ∈ chartRing F (segreVec y) c) :
    ∃ (n : ℕ) (U : Fin L → MRing (bundleIdx ι M) F), (∀ l, IsMultiHomog (U l) (liftNat fun _ => n)) ∧
      ∀ l, eval₂ ((algebraMap Ω Φ).comp (algebraMap F Ω)) (projCoord y w φ t) (U l) =
        algebraMap Ω Φ (u l * segreVec y c ^ n) := by
  have h := fun l => chartRing_forms (M := M) y w φ t c hc (hu l)
  choose n U hU hUe using h
  refine ⟨∑ l, n l, fun l => U l * chartMono M c (fun _ => ∑ l, n l - n l), fun l => ?_, fun l => ?_⟩
  · have hle : n l ≤ ∑ l, n l := Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ l)
    have hd : liftNat (K := K) (fun _ => ∑ l, n l) =
        liftNat (fun _ => n l) + liftNat (fun _ => ∑ l, n l - n l) := by
      funext o; cases o <;> simp [liftNat]; omega
    rw [hd]
    exact (hU l).mul (chartMono_homog M c _)
  · have hle : n l ≤ ∑ l, n l := Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ l)
    rw [eval₂_mul, hUe, eval_chartMono, ← map_mul]
    congr 1
    rw [Finset.prod_pow, mul_assoc, ← segreVec, ← pow_add, Nat.add_sub_cancel' hle]

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

section New

variable {M N : ℕ} {E : Type} [AddCommGroup E] [Module Ω E] {Φ : Type} [Field Φ] [Algebra Ω Φ]

theorem component_mem_projIdeal (y : (Σ k, ι k) → Ω) (w : Module.Basis (Fin N) Ω E)
    (φ : Fin M → Module.Dual Ω E) (t : Fin N → Φ) {q : MRing (bundleIdx ι M) F}
    (hq : q ∈ projIdeal F y w φ t) (d : Option K → ℕ) :
    weightedHomogeneousComponent (blockWeight (bundleIdx ι M)) d q ∈ projIdeal F y w φ t := by
  classical
  rw [ProjIdealFormValue.proof F Ω K ι y N E w M φ Φ t d _
    (weightedHomogeneousComponent_isWeightedHomogeneous _ _)]
  rw [projIdeal, RingHom.mem_ker, coe_eval₂Hom] at hq
  have hc := congrArg (coeff (Finsupp.equivFunOnFinite.symm d)) hq
  rw [← q.support_sum_monomial_coeff, eval₂_sum, coeff_sum, coeff_zero] at hc
  rw [weightedHomogeneousComponent_apply, eval₂_sum, Finset.sum_filter]
  refine (Finset.sum_congr rfl fun m _ => ?_).trans hc
  rw [ProjIdealFormValue.eval₂_monomial_cone, coeff_C_mul, coeff_monomial, mul_ite, mul_one, mul_zero]
  have hiff : Finsupp.mapDomain Sigma.fst m = Finsupp.equivFunOnFinite.symm d ↔
      Finsupp.weight (blockWeight (bundleIdx ι M)) m = d := by
    rw [Finsupp.ext_iff, funext_iff]
    exact forall_congr' fun o => by rw [ProjIdealFormValue.weight_blockWeight_apply]; rfl
  simp only [hiff]

theorem eval_trunc_eq_zero (y : (Σ k, ι k) → Ω) (w : Module.Basis (Fin N) Ω E)
    (φ : Fin M → Module.Dual Ω E) {t : Fin N → Φ} (ht : AlgebraicIndependent Ω t) (i : ℕ)
    {q : MRing (bundleIdx ι M) F} (hq : q ∈ projIdeal F y w φ (truncCoord t i)) (τ : Fin N → Φ) :
    eval₂ ((algebraMap Ω Φ).comp (algebraMap F Ω)) (projCoord y w φ (truncCoord τ i)) q = 0 := by
  classical
  let G : (Σ o, bundleIdx ι M o) → MvPolynomial (Fin N) Ω := fun p =>
    match p with
    | ⟨none, l⟩ => ∑ j : Fin N, (if (j : ℕ) < i then X j else 0) * C (φ l (w j))
    | ⟨some k, p⟩ => C (y ⟨k, p⟩)
  have key : ∀ τ : Fin N → Φ, eval₂ ((algebraMap Ω Φ).comp (algebraMap F Ω))
      (projCoord y w φ (truncCoord τ i)) q =
      aeval τ (eval₂ (C.comp (algebraMap F Ω)) G q) := by
    intro τ
    have h := eval₂_comp_left (aeval τ : MvPolynomial (Fin N) Ω →ₐ[Ω] Φ).toRingHom
      (C.comp (algebraMap F Ω)) G q
    rw [AlgHom.toRingHom_eq_coe, RingHom.coe_coe] at h
    rw [h]
    congr 1
    · ext r
      simp
    · funext p
      rcases p with ⟨_ | k, p⟩
      · simp [G, projCoord, truncCoord, map_sum, apply_ite]
      · simp [G, projCoord]
  have h0 : eval₂ (C.comp (algebraMap F Ω)) G q = 0 :=
    ht (by rw [map_zero, ← key t]; exact eval_eq_zero_of_mem_projIdeal y w φ _ hq)
  rw [key τ, h0, map_zero]

def substDeg (e d : Option K → ℕ) : Option K → ℕ :=
  fun o => Option.elim o 0 (fun k => d (some k)) + d none * e o

theorem bind₁_isMultiHomog (g : (Σ o, bundleIdx ι M o) → MRing (bundleIdx ι M) F) (e : Option K → ℕ)
    (hs : ∀ k (p : ι k), g ⟨some k, p⟩ = X ⟨some k, p⟩) (hn : ∀ l, IsMultiHomog (g ⟨none, l⟩) e)
    {q : MRing (bundleIdx ι M) F} {d : Option K → ℕ} (hq : IsMultiHomog q d) :
    IsMultiHomog (bind₁ g q) (substDeg e d) := by
  let Λ : (Option K → ℕ) →+ (Option K → ℕ) :=
    { toFun := substDeg e
      map_zero' := by funext o; cases o <;> simp [substDeg]
      map_add' := fun d d' => by funext o; cases o <;> simp [substDeg] <;> ring }
  have hg : ∀ v, IsWeightedHomogeneous (blockWeight (bundleIdx ι M)) (g v) (Λ (blockWeight _ v)) := by
    rintro ⟨_ | k, p⟩
    · have : Λ (blockWeight (bundleIdx ι M) ⟨none, p⟩) = e := by
        funext o; cases o <;> simp [Λ, substDeg, blockWeight]
      rw [this]
      exact hn p
    · have : Λ (blockWeight (bundleIdx ι M) ⟨some k, p⟩) = blockWeight (bundleIdx ι M) ⟨some k, p⟩ := by
        funext o; cases o <;> simp [Λ, substDeg, blockWeight, Pi.single_apply]
      rw [this, show g ⟨some k, p⟩ = X ⟨some k, p⟩ from hs k p]
      exact isWeightedHomogeneous_X F _ _
  rw [← q.support_sum_monomial_coeff, map_sum]
  refine IsWeightedHomogeneous.sum _ _ _ fun m hm => ?_
  have hmd : Finsupp.weight (blockWeight (bundleIdx ι M)) m = d := hq (mem_support_iff.mp hm)
  rw [bind₁_monomial]
  have := (isWeightedHomogeneous_C (blockWeight (bundleIdx ι M)) (coeff m q)).mul
    (IsWeightedHomogeneous.prod m.support (fun v => g v ^ m v) (fun v => m v • Λ (blockWeight _ v))
      (fun v _ => (hg v).pow (m v)))
  rw [zero_add] at this
  have hΛ : substDeg e d = ∑ v ∈ m.support, m v • Λ (blockWeight (bundleIdx ι M) v) := by
    show Λ d = _
    rw [← hmd, Finsupp.weight_apply, Finsupp.sum, map_sum]
    simp only [map_nsmul]
  rw [hΛ]
  exact this

theorem bind₁_scale (u : MRing (bundleIdx ι M) F) {q : MRing (bundleIdx ι M) F} {d : Option K → ℕ}
    (hq : IsMultiHomog q d) :
    bind₁ (fun v => u ^ blockWeight (bundleIdx ι M) v none * X v) q = u ^ d none * q := by
  conv_lhs => rw [← q.support_sum_monomial_coeff]
  conv_rhs => rw [← q.support_sum_monomial_coeff]
  rw [map_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun m hm => ?_
  have hmd : Finsupp.weight (blockWeight (bundleIdx ι M)) m = d := hq (mem_support_iff.mp hm)
  have hs : ∑ v ∈ m.support, blockWeight (bundleIdx ι M) v none * m v = d none := by
    rw [← hmd, Finsupp.weight_apply, Finsupp.sum, Finset.sum_apply]
    refine Finset.sum_congr rfl fun v _ => ?_
    simp [mul_comm]
  rw [bind₁_monomial, monomial_eq, Finsupp.prod]
  simp only [mul_pow, Finset.prod_mul_distrib, ← pow_mul]
  rw [Finset.prod_pow_eq_pow_sum, hs]
  ring

theorem bind₁_sub_mem {σ R : Type*} [CommRing R] (I : Ideal (MvPolynomial σ R)) (g g' : σ → MvPolynomial σ R)
    (h : ∀ v, g' v - g v ∈ I) (q : MvPolynomial σ R) : bind₁ g' q - bind₁ g q ∈ I := by
  induction q using MvPolynomial.induction_on with
  | C r => simp
  | add p q hp hq =>
    rw [map_add, map_add, add_sub_add_comm]
    exact I.add_mem hp hq
  | mul_X p v hp =>
    rw [map_mul, map_mul, bind₁_X_right, bind₁_X_right,
      show bind₁ g' p * g' v - bind₁ g p * g v =
        (bind₁ g' p - bind₁ g p) * g' v + bind₁ g p * (g' v - g v) by ring]
    exact I.add_mem (I.mul_mem_right _ hp) (I.mul_mem_left _ (h v))

theorem isMultiHomog_sub {f g : MRing (bundleIdx ι M) F} {d : Option K → ℕ} (hf : IsMultiHomog f d)
    (hg : IsMultiHomog g d) : IsMultiHomog (f - g) d :=
  (mem_weightedHomogeneousSubmodule F _ _ _).mp (Submodule.sub_mem _
    ((mem_weightedHomogeneousSubmodule F _ _ _).mpr hf) ((mem_weightedHomogeneousSubmodule F _ _ _).mpr hg))

end New

section SectionForm

variable {M N : ℕ} {E : Type} [AddCommGroup E] [Module Ω E] {Φ : Type} [Field Φ] [Algebra Ω Φ]

theorem exists_section_form (y : (Σ k, ι k) → Ω) (B : ChartBundle F (segreVec y) N E)
    (w : Module.Basis (Fin N) Ω E) (b : Fin N → K → ℤ) (hfl : IsFlagFrame y B w b) (a : K → ℤ)
    (φ : Fin M → Module.Dual Ω E) (hφ : IsTwistedDualGens y B a φ) (t : Fin N → Φ) (i : Fin N)
    (c : ∀ k, ι k) (hsc : segreVec y c ≠ 0) :
    ∃ (dl : Option K → ℕ) (β : K → ℕ) (f : MRing (bundleIdx ι M) F), IsMultiHomog f dl ∧
      (fun o => (dl o : ℤ) - liftNat β o) = zetaDeg + liftDeg (b i - a) ∧
      eval₂ ((algebraMap Ω Φ).comp (algebraMap F Ω)) (projCoord y w φ (truncCoord t ((i : ℕ) + 1))) f =
        t i * eval₂ ((algebraMap Ω Φ).comp (algebraMap F Ω))
          (projCoord y w φ (truncCoord t ((i : ℕ) + 1))) (chartMono M c β) := by
  have hY : ∀ k, y ⟨k, c k⟩ ≠ 0 := fun k => (Finset.prod_ne_zero_iff.1 hsc) k (Finset.mem_univ _)
  obtain ⟨ψ, hψint, hψlow, hψi⟩ := exists_flag_dual y B w b hfl c hsc i
  obtain ⟨u, hu, hψ⟩ := hφ.generate c hsc ψ hψint
  have hstar : t i * algebraMap Ω Φ (chartPow y c (b i))⁻¹ =
      ∑ l, algebraMap Ω Φ (u l * chartPow y c (-a)) *
        projCoord y w φ (truncCoord t ((i : ℕ) + 1)) ⟨none, l⟩ := by
    have h1 : ∑ j, truncCoord t ((i : ℕ) + 1) j * algebraMap Ω Φ (ψ (w j)) =
        t i * algebraMap Ω Φ (chartPow y c (b i))⁻¹ := by
      rw [Finset.sum_eq_single i]
      · simp [truncCoord, hψi]
      · intro j _ hji
        rcases lt_or_gt_of_ne hji with h | h
        · simp [hψlow j h]
        · have : ¬ (j : ℕ) < (i : ℕ) + 1 := by
            have : (i : ℕ) < j := h
            omega
          simp [truncCoord, this]
      · simp
    rw [← h1, hψ]
    simp only [projCoord, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul,
      map_sum, map_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun j _ => ?_
    simp only [chartPow, Pi.neg_apply]
    ring
  obtain ⟨n, U, hUh, hUe⟩ := chartRing_forms_fin (M := M) y w φ (truncCoord t ((i : ℕ) + 1)) c hsc hu
  let α : K → ℕ := fun k => (|a k| + |b i k| - a k).toNat
  let β : K → ℕ := fun k => (|a k| + |b i k| + n - b i k).toNat
  have hid : segreVec y c ^ n * ∏ k, y ⟨k, c k⟩ ^ α k =
      (∏ k, y ⟨k, c k⟩ ^ β k) * chartPow y c (b i) * chartPow y c (-a) := by
    rw [segreVec_pow, ← chartPow_natCast, ← chartPow_natCast, ← chartPow_add hY, ← chartPow_add hY,
      ← chartPow_add hY]
    congr 1
    funext k
    have h1 := le_abs_self (a k)
    have h2 := neg_abs_le (a k)
    have h3 := le_abs_self (b i k)
    have h4 := neg_abs_le (b i k)
    simp only [Pi.add_apply, Pi.neg_apply, α, β]
    omega
  let f : MRing (bundleIdx ι M) F := ∑ l, U l * chartMono M c α * X ⟨none, l⟩
  have hg : eval₂ ((algebraMap Ω Φ).comp (algebraMap F Ω)) (projCoord y w φ (truncCoord t ((i : ℕ) + 1)))
      (chartMono M c β) = algebraMap Ω Φ (∏ k, y ⟨k, c k⟩ ^ β k) := eval_chartMono y w φ _ c β
  have hf : eval₂ ((algebraMap Ω Φ).comp (algebraMap F Ω)) (projCoord y w φ (truncCoord t ((i : ℕ) + 1))) f
      = t i * eval₂ ((algebraMap Ω Φ).comp (algebraMap F Ω))
        (projCoord y w φ (truncCoord t ((i : ℕ) + 1))) (chartMono M c β) := by
    rw [hg]
    calc _ = ∑ l, algebraMap Ω Φ (u l * chartPow y c (-a)) *
            projCoord y w φ (truncCoord t ((i : ℕ) + 1)) ⟨none, l⟩ *
            algebraMap Ω Φ ((∏ k, y ⟨k, c k⟩ ^ β k) * chartPow y c (b i)) := by
          simp only [f, eval₂_sum, eval₂_mul, eval₂_X, hUe, eval_chartMono]
          refine Finset.sum_congr rfl fun l _ => ?_
          have hl : algebraMap Ω Φ (u l * segreVec y c ^ n) * algebraMap Ω Φ (∏ k, y ⟨k, c k⟩ ^ α k) =
              algebraMap Ω Φ (u l * chartPow y c (-a)) *
                algebraMap Ω Φ ((∏ k, y ⟨k, c k⟩ ^ β k) * chartPow y c (b i)) := by
            rw [← map_mul, ← map_mul]
            congr 1
            rw [mul_assoc, hid]
            ring
          rw [mul_comm _ (projCoord _ _ _ _ _), mul_assoc, hl]
          ring
      _ = t i * algebraMap Ω Φ (chartPow y c (b i))⁻¹ *
            algebraMap Ω Φ ((∏ k, y ⟨k, c k⟩ ^ β k) * chartPow y c (b i)) := by
          rw [hstar, Finset.sum_mul]
      _ = t i * algebraMap Ω Φ (∏ k, y ⟨k, c k⟩ ^ β k) := by
          have hp : algebraMap Ω Φ (chartPow y c (b i)) ≠ 0 :=
            (map_ne_zero _).2 (chartPow_ne_zero hY _)
          rw [map_inv₀, map_mul]
          field_simp
  refine ⟨fun o => Option.elim o 1 (fun k => n + α k), β, f, ?_, ?_, hf⟩
  · refine IsWeightedHomogeneous.sum _ _ _ fun l _ => ?_
    have h := ((hUh l).mul (chartMono_homog (F := F) M c α)).mul
      (isWeightedHomogeneous_X F (blockWeight (bundleIdx ι M)) ⟨none, l⟩)
    convert h using 1
    funext o
    cases o <;> simp [liftNat, blockWeight]
  · funext o
    cases o with
    | none => simp [liftNat, zetaDeg, liftDeg]
    | some k =>
      have h1 := le_abs_self (a k)
      have h2 := neg_abs_le (a k)
      have h3 := le_abs_self (b i k)
      have h4 := neg_abs_le (b i k)
      simp only [liftNat, zetaDeg, liftDeg, Option.elim, Pi.add_apply, Pi.sub_apply, α, β]
      omega

end SectionForm

end FlagBundleChartSection

end

end GroundTheory.Heights₂.Heights.NumbersDVR
