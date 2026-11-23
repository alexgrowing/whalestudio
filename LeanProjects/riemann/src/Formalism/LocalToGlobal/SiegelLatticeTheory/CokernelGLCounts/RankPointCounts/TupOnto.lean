import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.TupLift
import Formalism.LocalToGlobal.SiegelLatticeTheory.TraceIntegralEstimates.LatSpanLeSpan
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.IdentityCellTrace.TraceOneHolds

noncomputable section

open scoped Classical

namespace Formalism.L2.SG.Pf.TupOnto

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.TermDef
  PI.TermsAtPtFiniteW.HeisW PI.TermsAtPtFiniteW.LeviW

section Mat

variable {E : Type} [Field E] [NumberField E] {n : ℕ}
  (aa : Fin n → FractionalIdeal (nonZeroDivisors (𝓞 E)) E)

def Good (M : Matrix (Fin n) (Fin n) E) : Prop :=
  ∀ c b, ∀ x ∈ (aa b : Submodule (𝓞 E) E), x * M c b ∈ (aa c : Submodule (𝓞 E) E)

theorem good_one : Good aa 1 := by
  intro c b x hx
  by_cases h : c = b
  · subst h
    simpa [Matrix.one_apply_eq] using hx
  · rw [Matrix.one_apply_ne h, mul_zero]
    exact Submodule.zero_mem _

theorem good_zero : Good aa 0 := by
  intro c b x _
  rw [Matrix.zero_apply, mul_zero]
  exact Submodule.zero_mem _

theorem good_add {M N : Matrix (Fin n) (Fin n) E} (hM : Good aa M) (hN : Good aa N) : Good aa (M + N) := by
  intro c b x hx
  rw [Matrix.add_apply, mul_add]
  exact Submodule.add_mem _ (hM c b x hx) (hN c b x hx)

theorem good_mul {M N : Matrix (Fin n) (Fin n) E} (hM : Good aa M) (hN : Good aa N) : Good aa (M * N) := by
  intro c b x hx
  rw [Matrix.mul_apply, Finset.mul_sum]
  refine Submodule.sum_mem _ fun d _ => ?_
  have h := hM c d _ (hN d b x hx)
  rwa [show x * N d b * M c d = x * (M c d * N d b) by ring] at h

theorem good_pow {M : Matrix (Fin n) (Fin n) E} (hM : Good aa M) (k : ℕ) : Good aa (M ^ k) := by
  induction k with
  | zero => rw [pow_zero]; exact good_one aa
  | succ k ih => rw [pow_succ]; exact good_mul aa ih hM

theorem good_sum {M : ℕ → Matrix (Fin n) (Fin n) E} (hM : ∀ k, Good aa (M k)) (t : Finset ℕ) :
    Good aa (∑ k ∈ t, M k) := by
  induction t using Finset.induction_on with
  | empty => rw [Finset.sum_empty]; exact good_zero aa
  | insert k t hk ih => rw [Finset.sum_insert hk]; exact good_add aa (hM k) ih

theorem pow_upper {N : Matrix (Fin n) (Fin n) E} (hN : ∀ c b, b ≤ c → N c b = 0) :
    ∀ k (c b : Fin n), (b : ℕ) < c + k → (N ^ k) c b = 0 := by
  intro k
  induction k with
  | zero =>
    intro c b h
    rw [pow_zero, Matrix.one_apply_ne]
    intro hcb
    subst hcb
    omega
  | succ k ih =>
    intro c b h
    rw [pow_succ, Matrix.mul_apply]
    refine Finset.sum_eq_zero fun d _ => ?_
    by_cases hbd : b ≤ d
    · rw [hN d b hbd, mul_zero]
    · have hdb : (d : ℕ) < b := Fin.lt_iff_val_lt_val.1 (not_le.1 hbd)
      rw [ih c d (by omega), zero_mul]

theorem inv_good {U : Matrix (Fin n) (Fin n) E} (hU0 : ∀ c b, b < c → U c b = 0) (hU1 : ∀ c, U c c = 1)
    (hg : ∀ c b, c < b → ∀ x ∈ (aa b : Submodule (𝓞 E) E), x * U c b ∈ (aa c : Submodule (𝓞 E) E)) :
    Good aa U⁻¹ := by
  set N := U - 1 with hNdef
  have hUN : U = 1 + N := by rw [hNdef]; abel
  have hN0 : ∀ c b, b ≤ c → N c b = 0 := by
    intro c b h
    rw [hNdef, Matrix.sub_apply]
    rcases h.lt_or_eq with h | h
    · rw [hU0 c b h, Matrix.one_apply_ne (ne_of_gt h), sub_zero]
    · subst h
      rw [hU1, Matrix.one_apply_eq, sub_self]
  have hNg : Good aa (-N) := by
    intro c b x hx
    rw [Matrix.neg_apply, mul_neg]
    refine Submodule.neg_mem _ ?_
    rcases lt_or_ge c b with h | h
    · have h' := hg c b h x hx
      rwa [hNdef, Matrix.sub_apply, Matrix.one_apply_ne (ne_of_lt h), sub_zero]
    · rw [hN0 c b h, mul_zero]
      exact Submodule.zero_mem _
  have hNn : N ^ n = 0 := by
    ext c b
    rw [pow_upper hN0 n c b (by have := b.isLt; omega), Matrix.zero_apply]
  have hinv : (∑ k ∈ Finset.range n, (-N) ^ k) * U = 1 := by
    have h := geom_sum_mul (-N) n
    rw [neg_pow, hNn, mul_zero, zero_sub] at h
    rw [hUN]
    have e : (∑ k ∈ Finset.range n, (-N) ^ k) * (1 + N) =
        -((∑ k ∈ Finset.range n, (-N) ^ k) * (-N - 1)) := by noncomm_ring
    rw [e, h, neg_neg]
  rw [Matrix.inv_eq_left_inv hinv]
  exact good_sum aa (M := fun k => (-N) ^ k) (fun k => good_pow aa hNg k) _

end Mat

section Levi

variable {E : Type} [Field E] [NumberField E] [StarRing E] {S : HSpace E} {r : ℕ}
  (e f : Fin r → S.V) (hee : ∀ a b, S.hT (e a) (e b) = 0) (hff : ∀ a b, S.hT (f a) (f b) = 0)
  (hef : ∀ a b, S.hT (e a) (f b) = if a = b then 1 else 0)

include hff hef in
theorem psiF_f' (U U' : Matrix (Fin r) (Fin r) E) (j : Fin r) : psiF e f U U' (f j) = ∑ c, U' c j • f c := by
  simp [psiF, hff, hef, ite_smul]

include hee hff hef in

theorem levi_exists (U : Matrix (Fin r) (Fin r) E) (hdet : U.det = 1) :
    ∃ ν : S.V ≃ₗ[E] S.V, (∀ x y, S.hT (ν x) (ν y) = S.hT x y) ∧ (∀ j, ν (e j) = ∑ c, U c j • e c) ∧
      (∀ j, ν (f j) = ∑ c, (U.conjTranspose)⁻¹ c j • f c) ∧
      (∀ v, (∀ a, S.hT (f a) v = 0) → (∀ a, S.hT (e a) v = 0) → ν v = v) ∧
      (∀ v, (∀ a, S.hT (e a) v = 0) → ν v - v ∈ Submodule.span E (Set.range e)) := by
  have hU' : IsUnit (U.conjTranspose).det := by
    rw [Matrix.det_conjTranspose, hdet, star_one]; exact isUnit_one
  have hUU : ∀ a b, ∑ c, star (U c a) * (U.conjTranspose)⁻¹ c b = if a = b then 1 else 0 := by
    intro a b
    have := congrFun (congrFun (Matrix.mul_nonsing_inv _ hU') a) b
    rw [Matrix.mul_apply] at this
    simpa [Matrix.conjTranspose_apply, Matrix.one_apply] using this
  have hiso := isom_psiF e f hee hff hef U (U.conjTranspose)⁻¹ hUU
  refine ⟨LinearEquiv.ofInjectiveEndo (psiF e f U (U.conjTranspose)⁻¹) (inj_of_isom _ hiso),
    fun x y => hiso x y, fun j => psiF_e e f hef U _ hee j, fun j => psiF_f' e f hff hef U _ j,
    fun v h1 h2 => psiF_fix e f U _ v h1 h2, fun v hv => ?_⟩
  show psiF e f U (U.conjTranspose)⁻¹ v - v ∈ _
  rw [psiF_apply]
  simp only [hv, zero_smul, Finset.sum_const_zero, add_zero, add_sub_cancel_left]
  refine Submodule.sum_mem _ fun a _ => Submodule.smul_mem _ _ (Submodule.sub_mem _
    (Submodule.sum_mem _ fun c _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨c, rfl⟩))
    (Submodule.subset_span ⟨a, rfl⟩))

end Levi

section Eich

variable {E : Type} [Field E] [NumberField E] [StarRing E] {S : HSpace E} {r : ℕ}

theorem eich_exists {T : E} (Λ : Submodule (𝓞 E) S.V) (hUn : Formalism.HermitianLatticesTheory.IsUnimodular S.hT Λ) (F : LFlag S r T)
    (a : Fin r → S.V) (s : Matrix (Fin r) (Fin r) E) (hea : ∀ c d, S.hT (F.fl.e c) (a d) = 0)
    (hs : ∀ c d, s c d + star (s d c) = -S.hT (a c) (a d))
    (hΛ : ∀ v ∈ Λ, nilF F.fl.e a s v ∈ Λ) :
    ∃ n ∈ NLam Λ F, ∀ v, n v = v + nilF F.fl.e a s v := by
  classical
  set N := nilF F.fl.e a s with hNdef
  have h3 : ∀ v, N (N (N v)) = 0 := by
    intro v
    apply PI.TermsAtPtFiniteW.HeisW.nil3 <;>
      first | exact F.fl.e_iso | exact hea | exact hs | assumption
  have hiso : ∀ x y, S.hT (x + N x) (y + N y) = S.hT x y := by
    intro x y
    apply PI.TermsAtPtFiniteW.HeisW.isom_nil <;>
      first | exact F.fl.e_iso | exact hea | exact hs | assumption
  have hker : ∀ i, N (F.fl.e i) = 0 := fun i => by
    apply PI.TermsAtPtFiniteW.HeisW.nil_e <;>
      first | exact F.fl.e_iso | exact hea | exact hs | assumption
  let n : S.V ≃ₗ[E] S.V := LinearEquiv.ofLinear (LinearMap.id + N) (LinearMap.id - N + N ∘ₗ N)
    (LinearMap.ext fun v => by
      simp only [LinearMap.comp_apply, LinearMap.add_apply, LinearMap.sub_apply, LinearMap.id_apply,
        map_add, map_sub, h3]
      abel)
    (LinearMap.ext fun v => by
      simp only [LinearMap.comp_apply, LinearMap.add_apply, LinearMap.sub_apply, LinearMap.id_apply,
        map_add, map_sub, h3]
      abel)
  have hn : ∀ v, n v = v + N v := fun v => rfl
  have hninv : ∀ v, n.symm v = v - N v + N (N v) := fun v => rfl
  refine ⟨n, ?_, hn⟩
  simp only [NLam, Set.mem_setOf_eq]
  refine ⟨?_, ?_, ?_⟩
  · rw [isAutLam_iff]
    refine ⟨fun x y => by rw [hn, hn, hiso], fun x => ⟨fun hx => ?_, fun hx => ?_⟩⟩
    · have hx' : x = n.symm (n x) := (n.symm_apply_apply x).symm
      rw [hx', hninv]
      exact Λ.add_mem (Λ.sub_mem hx (hΛ _ hx)) (hΛ _ (hΛ _ hx))
    · rw [hn]
      exact Λ.add_mem hx (hΛ x hx)
  · intro j x hx
    rw [hn, add_sub_cancel_left]
    have hle : Xflag F (j + 1) ≤ LinearMap.ker N := by
      rw [Xflag, Formalism.MainNotions.S.FlagG.Xa, Submodule.span_le]
      rintro _ ⟨i, -, rfl⟩
      exact hker i
    rw [LinearMap.mem_ker.1 (hle hx)]
    exact Submodule.zero_mem _
  · intro x hx
    have hx' : ∀ c, S.hT (F.fl.e c) x = 0 := by
      intro c
      have h := hx
      simp only [orth, Submodule.mem_iInf, LinearMap.mem_ker] at h
      exact h _ (Submodule.subset_span ⟨c, rfl⟩)
    rw [hn, add_sub_cancel_left, hNdef, nilF_apply]
    refine Submodule.sum_mem _ fun c _ => ?_
    rw [hx' c, zero_smul, zero_add]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨c, rfl⟩)

end Eich

section Split

variable {E : Type} [Field E] [NumberField E] [StarRing E] {S : HSpace E} {r : ℕ}

open Formalism.L2.SG.Saturated

theorem latSpan_map (aa : Fin r → FractionalIdeal (nonZeroDivisors (𝓞 E)) E) (e : Fin r → S.V)
    (φ : S.V →ₗ[E] S.V) (M : Matrix (Fin r) (Fin r) E) (hM : Good aa M) (hφ : ∀ j, φ (e j) = ∑ c, M c j • e c)
    {y : S.V} (hy : y ∈ latSpan aa e) : φ y ∈ latSpan aa e := by
  have hgen : ∀ a, ∀ x ∈ aa a, φ (x • e a) ∈ latSpan aa e := by
    intro a x hx
    rw [map_smul, hφ, Finset.smul_sum]
    refine Submodule.sum_mem _ fun c _ => ?_
    rw [smul_smul]
    exact Submodule.subset_span ⟨c, x * M c a, hM c a x hx, rfl⟩
  have hle : latSpan aa e ≤ (latSpan aa e).comap (φ.restrictScalars (𝓞 E)) := by
    conv_lhs => unfold latSpan
    rw [Submodule.span_le]
    rintro _ ⟨a, x, hx, rfl⟩
    exact hgen a x hx
  exact hle hy

theorem latSpan_le_spanE (aa : Fin r → FractionalIdeal (nonZeroDivisors (𝓞 E)) E) (v : Fin r → S.V) {y : S.V}
    (hy : y ∈ latSpan aa v) : y ∈ Submodule.span E (Set.range v) := by
  have hle : latSpan aa v ≤ (Submodule.span E (Set.range v)).restrictScalars (𝓞 E) := by
    unfold latSpan
    rw [Submodule.span_le]
    rintro _ ⟨a, x, -, rfl⟩
    exact Submodule.smul_mem _ x (Submodule.subset_span ⟨a, rfl⟩)
  exact hle hy

theorem split_mem {Λ A L B : Submodule (𝓞 E) S.V} (h : Λ = A ⊔ L ⊔ B) {v : S.V} (hv : v ∈ Λ) :
    ∃ a ∈ A, ∃ l ∈ L, ∃ b ∈ B, v = a + l + b := by
  subst h
  obtain ⟨al, hal, b, hb, rfl⟩ := Submodule.mem_sup.1 hv
  obtain ⟨a, ha, l, hl, rfl⟩ := Submodule.mem_sup.1 hal
  exact ⟨a, ha, l, hl, b, hb, rfl⟩

theorem frame_symm {n : ℕ} (φ : S.V ≃ₗ[E] S.V) (e : Fin n → S.V) (M N : Matrix (Fin n) (Fin n) E)
    (hMN : M * N = 1) (hφ : ∀ j, φ (e j) = ∑ c, M c j • e c) (j : Fin n) :
    φ.symm (e j) = ∑ c, N c j • e c := by
  rw [LinearEquiv.symm_apply_eq, map_sum]
  simp_rw [map_smul, hφ, Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  simp_rw [← Finset.sum_smul]
  have h : ∀ d, ∑ c, N c j * M d c = (M * N) d j := fun d => by
    rw [Matrix.mul_apply]
    exact Finset.sum_congr rfl fun c _ => mul_comm _ _
  simp_rw [h, hMN, Matrix.one_apply, ite_smul, one_smul, zero_smul]
  simp

theorem hT_span_span (f : Fin r → S.V) (hff : ∀ a b, S.hT (f a) (f b) = 0) {x y : S.V}
    (hx : x ∈ Submodule.span E (Set.range f)) (hy : y ∈ Submodule.span E (Set.range f)) : S.hT x y = 0 := by
  obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun E).1 hx
  obtain ⟨d, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun E).1 hy
  simp [map_sum, hff]

variable {Λ : Submodule (𝓞 E) S.V} (aa : Fin r → FractionalIdeal (nonZeroDivisors (𝓞 E)) E)
  (e f : Fin r → S.V) (L : Submodule (𝓞 E) S.V)
  (hΛeq : Λ = latSpan aa e ⊔ L ⊔ latSpan (fun a => (aa a)⁻¹) f)
  (hee : ∀ a b, S.hT (e a) (e b) = 0) (hff : ∀ a b, S.hT (f a) (f b) = 0)
  (hef : ∀ a b, S.hT (e a) (f b) = if a = b then 1 else 0)
  (hL : ∀ x ∈ L, ∀ a, S.hT (e a) x = 0 ∧ S.hT (f a) x = 0)
  (hint : ∀ x ∈ Λ, ∀ y ∈ Λ, ∃ o : 𝓞 E, (o : E) = S.hT x y)

include hΛeq in
theorem A_le : latSpan aa e ≤ Λ := by
  rw [hΛeq]
  exact le_sup_of_le_left le_sup_left

include hΛeq in
theorem L_le : L ≤ Λ := by
  rw [hΛeq]
  exact le_sup_of_le_left le_sup_right

include hΛeq in
theorem B_le : latSpan (fun a => (aa a)⁻¹) f ≤ Λ := by
  rw [hΛeq]
  exact le_sup_right

include hΛeq hff hL hint in

theorem levi_keeps (hUn : Formalism.HermitianLatticesTheory.IsUnimodular S.hT Λ) (U : Matrix (Fin r) (Fin r) E)
    (hU0 : ∀ c b, b < c → U c b = 0) (hU1 : ∀ c, U c c = 1)
    (hg : ∀ c b, c < b → ∀ x ∈ (aa b : Submodule (𝓞 E) E), x * U c b ∈ (aa c : Submodule (𝓞 E) E))
    (ν : S.V ≃ₗ[E] S.V) (hiso : ∀ x y, S.hT (ν x) (ν y) = S.hT x y) (he : ∀ j, ν (e j) = ∑ c, U c j • e c)
    (hf : ∀ j, ν (f j) = ∑ c, (U.conjTranspose)⁻¹ c j • f c)
    (hfix : ∀ v, (∀ a, S.hT (f a) v = 0) → (∀ a, S.hT (e a) v = 0) → ν v = v) :
    ∀ v ∈ Λ, ν v ∈ Λ := by
  intro v hv
  have hU : Formalism.HermitianLatticesTheory.dual S.hT Λ = Λ := hUn
  have hdualΛ : ∀ x : S.V, (∀ y ∈ Λ, ∃ o : 𝓞 E, (o : E) = S.hT y x) → x ∈ Λ := fun x hx => by
    rw [← hU]
    simp only [Formalism.HermitianLatticesTheory.dual, Formalism.E.hdual, Submodule.mem_iInf, Submodule.mem_comap,
      LinearMap.restrictScalars_apply, Submodule.mem_one]
    intro y hy
    obtain ⟨o, ho⟩ := hx y hy
    exact ⟨o, ho⟩
  have hUgood : Good aa U := by
    intro c b x hx
    rcases lt_trichotomy c b with h | h | h
    · exact hg c b h x hx
    · subst h
      rw [hU1, mul_one]
      exact hx
    · rw [hU0 c b h, mul_zero]
      exact Submodule.zero_mem _
  have hbt : U.BlockTriangular id := by
    intro i j h
    exact hU0 i j h
  have hdet1 : U.det = 1 := by
    rw [Matrix.det_of_upperTriangular hbt]
    simp [hU1]
  have hUi : U * U⁻¹ = 1 := Matrix.mul_nonsing_inv U (by rw [hdet1]; exact isUnit_one)
  have hsymm_e : ∀ j, ν.symm (e j) = ∑ c, U⁻¹ c j • e c := frame_symm ν e U U⁻¹ hUi he
  have hA' : ∀ x ∈ latSpan aa e, ν x ∈ Λ := fun x hx =>
    A_le aa e f L hΛeq (latSpan_map aa e (ν : S.V →ₗ[E] S.V) U hUgood he hx)
  have hAs : ∀ x ∈ latSpan aa e, ν.symm x ∈ Λ := fun x hx =>
    A_le aa e f L hΛeq (latSpan_map aa e (ν.symm : S.V →ₗ[E] S.V) U⁻¹ (inv_good aa hU0 hU1 hg)
      hsymm_e hx)
  have hfixL : ∀ l ∈ L, ν l = l := fun l hl =>
    hfix l (fun i => (hL l hl i).2) (fun i => (hL l hl i).1)
  have hfixLs : ∀ l ∈ L, ν.symm l = l := fun l hl => by
    rw [LinearEquiv.symm_apply_eq, hfixL l hl]
  have hWU : (U.conjTranspose)⁻¹ * U.conjTranspose = 1 := Matrix.nonsing_inv_mul _ (by
    rw [Matrix.det_conjTranspose, hdet1, star_one]
    exact isUnit_one)
  have hsymm_f : ∀ j, ν.symm (f j) = ∑ c, U.conjTranspose c j • f c := frame_symm ν f _ _ hWU hf
  have hfspan : ∀ x ∈ Submodule.span E (Set.range f), ν.symm x ∈ Submodule.span E (Set.range f) := by
    have hle : Submodule.span E (Set.range f) ≤
        (Submodule.span E (Set.range f)).comap (ν.symm : S.V →ₗ[E] S.V) := by
      rw [Submodule.span_le]
      rintro _ ⟨j, rfl⟩
      simp only [SetLike.mem_coe, Submodule.mem_comap, LinearEquiv.coe_coe, hsymm_f]
      exact Submodule.sum_mem _ fun c _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨c, rfl⟩)
    exact fun x hx => hle hx
  obtain ⟨a, ha, l, hl, b, hb, rfl⟩ := split_mem hΛeq hv
  have hbΛ : ν b ∈ Λ := by
    apply hdualΛ
    intro w hw
    obtain ⟨a', ha', l', hl', b', hb', rfl⟩ := split_mem hΛeq hw
    have hbL : b ∈ Λ := B_le aa e f L hΛeq hb
    have hin : ν.symm a' + l' ∈ Λ := Λ.add_mem (hAs a' ha') (L_le aa e f L hΛeq hl')
    obtain ⟨o, ho⟩ := hint _ hin b hbL
    refine ⟨o, ?_⟩
    rw [ho]
    have h0 : S.hT (ν.symm b') b = 0 :=
      hT_span_span f hff (hfspan _ (latSpan_le_spanE _ f hb')) (latSpan_le_spanE _ f hb)
    have hw' : ν.symm (a' + l' + b') = (ν.symm a' + l') + ν.symm b' := by
      rw [map_add, map_add, hfixLs l' hl']
    calc S.hT (ν.symm a' + l') b = S.hT (ν.symm (a' + l' + b')) b := by
          rw [hw', map_add S.hT (ν.symm a' + l') (ν.symm b'), LinearMap.add_apply, h0, add_zero]
      _ = S.hT (ν (ν.symm (a' + l' + b'))) (ν b) := (hiso _ _).symm
      _ = S.hT (a' + l' + b') (ν b) := by rw [LinearEquiv.apply_symm_apply]
  rw [map_add, map_add, hfixL l hl]
  exact Λ.add_mem (Λ.add_mem (hA' a ha) (L_le aa e f L hΛeq hl)) hbΛ

end Split

section Eich2

variable {E : Type} [Field E] [NumberField E] [StarRing E] {S : HSpace E} {r : ℕ}

open Formalism.L2.SG.Saturated

def aE (y₀ : S.V) (v : Fin r → E) : Fin r → S.V := fun c => -(star (v c)) • y₀

def sE (α : E) (y₀ : S.V) (v : Fin r → E) : Matrix (Fin r) (Fin r) E :=
  fun c d => -(α * v c * star (v d) * S.hT y₀ y₀)

theorem hT_aE_left (y₀ : S.V) (v : Fin r → E) (c : Fin r) (x : S.V) :
    S.hT (aE y₀ v c) x = -(v c * S.hT y₀ x) := by
  simp [aE, starRingEnd_apply]

theorem hT_aE_right (y₀ : S.V) (v : Fin r → E) (c : Fin r) (x : S.V) :
    S.hT x (aE y₀ v c) = -(star (v c) * S.hT x y₀) := by
  simp [aE]

theorem sE_herm (α : E) (hα : α + star α = 1) (y₀ : S.V) (v : Fin r → E) (c d : Fin r) :
    sE α y₀ v c d + star (sE α y₀ v d c) = -S.hT (aE y₀ v c) (aE y₀ v d) := by
  rw [hT_aE_left, hT_aE_right]
  have hh : star (S.hT y₀ y₀) = S.hT y₀ y₀ := by
    have h := S.herm.eq y₀ y₀
    rwa [starRingEnd_apply] at h
  simp only [sE, star_neg, star_mul', star_star, hh]
  linear_combination (-(v c * star (v d) * S.hT y₀ y₀)) * hα

theorem nilF_f' (e a f : Fin r → S.V) (s : Matrix (Fin r) (Fin r) E)
    (hef : ∀ c b, S.hT (e c) (f b) = if c = b then 1 else 0) (b : Fin r) (ha : ∀ c, S.hT (a c) (f b) = 0) :
    nilF e a s (f b) = a b + ∑ c, s c b • e c := by
  simp [nilF, hef, ha, ite_smul, add_smul, Finset.sum_add_distrib]

theorem nilF_orth (e a : Fin r → S.V) (s : Matrix (Fin r) (Fin r) E) (x : S.V) (hx : ∀ c, S.hT (e c) x = 0) :
    nilF e a s x = ∑ c, (-(S.hT (a c) x)) • e c := by
  simp [nilF, hx]

theorem mem_aa_mul {I : FractionalIdeal (nonZeroDivisors (𝓞 E)) E} {x : E} (hx : x ∈ I) (o : 𝓞 E) :
    x * (o : E) ∈ I := by
  rw [mul_comm]
  exact Submodule.smul_mem (I : Submodule (𝓞 E) E) o hx

variable {Λ : Submodule (𝓞 E) S.V} (aa : Fin r → FractionalIdeal (nonZeroDivisors (𝓞 E)) E)
  (e f : Fin r → S.V) (L : Submodule (𝓞 E) S.V)
  (hΛeq : Λ = latSpan aa e ⊔ L ⊔ latSpan (fun a => (aa a)⁻¹) f)
  (hee : ∀ a b, S.hT (e a) (e b) = 0)
  (hef : ∀ a b, S.hT (e a) (f b) = if a = b then 1 else 0)
  (hL : ∀ x ∈ L, ∀ a, S.hT (e a) x = 0 ∧ S.hT (f a) x = 0)
  (hint : ∀ x ∈ Λ, ∀ y ∈ Λ, ∃ o : 𝓞 E, (o : E) = S.hT x y)

include hΛeq hee hef hL hint in

theorem eich_keeps (y₀ : S.V) (hy₀ : y₀ ∈ L) (v : Fin r → E) (hv : ∀ c, v c ∈ aa c) (α : 𝓞 E) :
    ∀ w ∈ Λ, nilF e (aE y₀ v) (sE (α : E) y₀ v) w ∈ Λ := by
  intro w hw
  have hsm : ∀ (o : 𝓞 E) (y : S.V), (o : E) • y = o • y := fun o y => algebraMap_smul E o y
  have hyΛ : y₀ ∈ Λ := L_le aa e f L hΛeq hy₀
  have hveΛ : ∀ c, v c • e c ∈ Λ := fun c =>
    A_le aa e f L hΛeq (Submodule.subset_span ⟨c, v c, hv c, rfl⟩)
  have h1 : ∀ c, ∃ o : 𝓞 E, (o : E) = star (v c) * S.hT (e c) w := fun c => by
    obtain ⟨o, ho⟩ := hint _ (hveΛ c) w hw
    refine ⟨o, ?_⟩
    rw [ho]
    simp [starRingEnd_apply]
  choose o1 ho1 using h1
  obtain ⟨o2, ho2⟩ := hint y₀ hyΛ w hw
  obtain ⟨o3, ho3⟩ := hint y₀ hyΛ y₀ hyΛ
  rw [nilF_apply]
  refine Submodule.sum_mem _ fun c _ => Submodule.add_mem _ ?_ ?_
  · have e1 : S.hT (e c) w • aE y₀ v c = -((o1 c : E) • y₀) := by
      rw [aE, smul_smul, ho1, ← neg_smul]
      congr 1
      ring
    rw [e1, hsm]
    exact Λ.neg_mem (Λ.smul_mem _ hyΛ)
  · have hs : ∑ d, sE (α : E) y₀ v c d * S.hT (e d) w =
        -((α : E) * v c * S.hT y₀ y₀) * ∑ d, (o1 d : E) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun d _ => ?_
      rw [ho1, sE]
      ring
    have e2 : PI.TermsAtPtFiniteW.HeisW.kap e (aE y₀ v) (sE (α : E) y₀ v) w c =
        v c * ((o2 - α * o3 * ∑ d, o1 d : 𝓞 E) : E) := by
      unfold PI.TermsAtPtFiniteW.HeisW.kap
      rw [hs, hT_aE_left, ← ho2, ← ho3]
      push_cast
      ring
    rw [e2]
    exact A_le aa e f L hΛeq (Submodule.subset_span ⟨c, _, mem_aa_mul (hv c) _, rfl⟩)

include hΛeq hL hint in

theorem exists_eigenvalueGLOne_eq_cuspidalLabel_gen (hUn : Formalism.HermitianLatticesTheory.IsUnimodular S.hT Λ) (z : S.V) (hzL : z ∈ L) (hzz : S.hT z z ≠ 0)
    (he_z : ∀ a, S.hT (e a) z = 0) (hprim : ∀ c : E, c • z ∈ Λ → ∃ o : 𝓞 E, (o : E) = c) :
    ∃ y₀ ∈ L, S.hT y₀ z = 1 := by
  have hU : Formalism.HermitianLatticesTheory.dual S.hT Λ = Λ := hUn
  have hzΛ : z ∈ Λ := L_le aa e f L hΛeq hzL
  obtain ⟨σ, hσ, hσz⟩ := Formalism.L2.S.Pv.ClassCounting.exists_partner (L := Λ) z hzΛ hzz hint (fun c hc => by
      rw [← hU]
      simp only [Formalism.HermitianLatticesTheory.dual, Formalism.E.hdual, Submodule.mem_iInf, Submodule.mem_comap,
        LinearMap.restrictScalars_apply, Submodule.mem_one]
      intro y hy
      obtain ⟨o, ho⟩ := hc y hy
      exact ⟨o, ho⟩) hprim
  obtain ⟨a, ha, l, hl, b, hb, rfl⟩ := split_mem hΛeq hσ
  refine ⟨l, hl, ?_⟩
  have hzero : ∀ g : Fin r → S.V, (∀ i, S.hT (g i) z = 0) →
      ∀ x ∈ Submodule.span E (Set.range g), S.hT x z = 0 := by
    intro g hg x hx
    obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun E).1 hx
    simp [map_sum, hg]
  have ha0 := hzero e he_z a (latSpan_le_spanE aa e ha)
  have hb0 := hzero f (fun i => (hL z hzL i).2) b (latSpan_le_spanE _ f hb)
  rw [map_add, map_add, LinearMap.add_apply, LinearMap.add_apply, ha0, hb0] at hσz
  simpa using hσz

end Eich2

section D7

attribute [local instance] Formalism.BasicNotions.Host.cmStar

open Formalism.L2.SG.Saturated

theorem aaF_cs (D : D7) (c : Fin D.R.rS) : Formalism.L2.SG.Pf.FibQ.aaF D c.castSucc = aaS D c := by
  simp only [Formalism.L2.SG.Pf.FibQ.aaF, aaS, Fin.coe_castSucc]

theorem aaF_last (D : D7) : Formalism.L2.SG.Pf.FibQ.aaF D (Fin.last D.R.rS) = 1 := by
  simp [Formalism.L2.SG.Pf.FibQ.aaF]

theorem nLamOnto_holds : TupLift.NLamOnto := by
  intro D w G Λ hΛ hT U hU hi
  obtain ⟨f, L, hff, hef, hL, hzL, hΛeq⟩ := Formalism.L2.SG.Closed.IsSplitRow_holds D w G Λ hΛ
  have hUn : Formalism.HermitianLatticesTheory.IsUnimodular (VS D).hT Λ := hΛ.2.1.2.1
  have hint : ∀ x ∈ Λ, ∀ y ∈ Λ, ∃ o : 𝓞 D.host.E, (o : D.host.E) = (VS D).hT x y := by
    intro x hx y hy
    obtain ⟨o, ho⟩ := PI.SRW.pair_int (VS D) hUn hy hx
    exact ⟨o, ho⟩
  let UX : Matrix (Fin D.R.rS) (Fin D.R.rS) D.host.E := fun c a => U c.castSucc a.castSucc
  let v : Fin D.R.rS → D.host.E := fun c => U c.castSucc (Fin.last _)
  have hUX0 : ∀ c b, b < c → UX c b = 0 := fun c b h =>
    (hU c.castSucc b.castSucc).1 (Fin.castSucc_lt_castSucc_iff.2 h)
  have hUX1 : ∀ c, UX c c = 1 := fun c => (hU c.castSucc c.castSucc).2 rfl
  have hgX : ∀ c b, c < b → ∀ x ∈ (aaS D b : Submodule (𝓞 D.host.E) D.host.E),
      x * UX c b ∈ (aaS D c : Submodule (𝓞 D.host.E) D.host.E) := by
    intro c b h x hx
    have := hi c.castSucc b.castSucc (Fin.castSucc_lt_castSucc_iff.2 h) x (by rw [aaF_cs]; exact hx)
    rw [aaF_cs] at this
    exact this
  have hv : ∀ c, v c ∈ aaS D c := by
    intro c
    have := hi c.castSucc (Fin.last _) (Fin.castSucc_lt_last c) 1 (by rw [aaF_last]; exact FractionalIdeal.one_mem_one _)
    rw [aaF_cs, one_mul] at this
    exact this
  have hdetX : UX.det = 1 := by
    rw [Matrix.det_of_isUpperTriangular (fun i j hij => hUX0 i j hij)]
    simp [hUX1]

  obtain ⟨νX, hisoX, heX, hfX, hfixX, horthX⟩ := levi_exists G.e f G.e_iso hff hef UX hdetX
  have hkeepX := levi_keeps (aaS D) G.e f L hΛeq hff hL hint hUn UX hUX0 hUX1 hgX νX hisoX heX hfX hfixX
  have hνX : νX ∈ NLam Λ (lf D G) := by
    refine ⟨⟨hisoX, gmap_of_isom Λ hUn νX hisoX hkeepX⟩, ?_, ?_⟩
    · intro j x hx
      have hx' : x ∈ Submodule.span D.host.E (G.e '' {i | i.1 < j + 1}) := hx
      show νX x - x ∈ Submodule.span D.host.E (G.e '' {i | i.1 < j})
      clear hx
      induction hx' using Submodule.span_induction with
      | mem y hy =>
        obtain ⟨i, hi', rfl⟩ := hy
        simp only [Set.mem_setOf_eq] at hi'
        rw [heX i]
        have e1 : ∑ c, UX c i • G.e c - G.e i = ∑ c, (UX c i - if c = i then 1 else 0) • G.e c := by
          simp [sub_smul, Finset.sum_sub_distrib]
        rw [e1]
        refine Submodule.sum_mem _ fun c _ => ?_
        by_cases hc : c.1 < j
        · exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨c, hc, rfl⟩)
        · have h0 : UX c i - (if c = i then 1 else 0) = 0 := by
            by_cases hci : c = i
            · subst hci; simp [hUX1]
            · rw [if_neg hci, hUX0 c i (lt_of_le_of_ne (Fin.le_iff_val_le_val.2 (by omega)) (Ne.symm hci)),
                sub_zero]
          rw [h0, zero_smul]
          exact Submodule.zero_mem _
      | zero => simp
      | add x y _ _ h h' => rw [map_add, add_sub_add_comm]; exact Submodule.add_mem _ h h'
      | smul c x _ h => rw [map_smul, ← smul_sub]; exact Submodule.smul_mem _ _ h
    · intro x hx
      have hφ : ∀ a, (VS D).hT (G.e a) x = 0 := fun a =>
        (PI.DCRelEquiv.UnitaryGroupMassFormula.mem_orth_iff.mp hx) _ (PI.DCRelEquiv.UnitaryGroupMassFormula.e_mem_X (lf D G) a)
      exact horthX x hφ

  have hzz : (VS D).hT G.z G.z ≠ 0 := by
    rw [G.z_norm]
    exact neg_ne_zero.2 (Nat.cast_ne_zero.2 hT)
  have hprim : ∀ c : D.host.E, c • G.z ∈ Λ → ∃ o : 𝓞 D.host.E, (o : D.host.E) = c := by
    intro c hc
    have hco : c • G.z ∈ orth (VS D) (Xsp (lf D G)) := by
      rw [Formalism.L2.SG.Pf.mem_orth_iff_td]
      intro y hy
      rw [map_smul, Formalism.L2.S.Pv.ClassCounting.orth_span G.e G.z_orth y hy, smul_zero]
    exact hΛ.2.1.2.2.2.2 c ⟨Submodule.mem_sup_left ⟨hc, hco⟩, hco⟩
  obtain ⟨y₀, hy₀, hy₀z⟩ := exists_eigenvalueGLOne_eq_cuspidalLabel_gen (aaS D) G.e f L hΛeq hL hint hUn G.z hzL hzz G.z_orth hprim
  obtain ⟨α, hα⟩ := PI.UnitaryGroupMassFormula.IdCellInSW.traceOne_holds D

  have hea : ∀ c d, (VS D).hT (G.e c) (aE y₀ v d) = 0 := fun c d => by
    rw [hT_aE_right, (hL y₀ hy₀ c).1, mul_zero, neg_zero]
  obtain ⟨νz, hνz, hνzv⟩ := eich_exists Λ hUn (lf D G) (aE y₀ v) (sE (α : D.host.E) y₀ v) hea
    (sE_herm (α : D.host.E) hα y₀ v)
    (eich_keeps (aaS D) G.e f L hΛeq G.e_iso hef hL hint y₀ hy₀ v hv α)
  have hez : ∀ i, νz (G.e i) = G.e i := fun i => by
    rw [hνzv, nil_e G.e _ _ G.e_iso hea i, add_zero]
  have hfc : ∀ i, frame (lf D G) i.castSucc = G.e i := fun i => Formalism.L2.SG.Pf.frame_castSucc_td (lf D G) i
  have hfl : frame (lf D G) (Fin.last _) = G.z := Formalism.L2.SG.Pf.frame_last_td (lf D G)
  refine ⟨νz * νX, Formalism.L2.SG.Pf.nlamPf_mul hνz hνX, fun b => ?_⟩
  rw [Fin.sum_univ_castSucc]
  simp only [hfc, hfl]
  refine Fin.lastCases ?_ (fun j => ?_) b
  · rw [hfl, LinearEquiv.mul_apply, hfixX G.z (fun a => (hL G.z hzL a).2) G.z_orth, hνzv,
      nilF_orth (lf D G).fl.e _ _ G.z G.z_orth, (hU (Fin.last _) (Fin.last _)).2 rfl, one_smul, add_comm]
    congr 1
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [hT_aE_left, hy₀z, mul_one, neg_neg]
  · rw [hfc, LinearEquiv.mul_apply, heX j, map_sum,
      (hU (Fin.last _) j.castSucc).1 (Fin.castSucc_lt_last j), zero_smul, add_zero]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [map_smul, hez]

end D7

section Step

variable {D : D7}

theorem repAtTup_of_glob (M : ∀ p : Formalism.MainNotions.S.LocalSplitGroups.PlF D, Formalism.MainNotions.S.Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep)
    (δ : ∀ p : Formalism.MainNotions.S.LocalSplitGroups.PlF D, (D.s.atP p).Fp) (u u' : D.what₂.Word)
    (F0 : FlagG (VS D) D.R.rS (Formalism.L2.SG.CntLocal.Tn u)) (what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V))
    (hG : Formalism.L2.SG.Pf.TupGlob.GlobMove D M δ u u') : Formalism.L2.SG.Pf.FibPart.RepAtTup M δ u u' F0 what₂ :=
  TupLift.repAtTup_of M δ u u' F0 what₂ hG nLamOnto_holds

end Step

end Formalism.L2.SG.Pf.TupOnto
