import Mathlib
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsHeatZero
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.GCauchyStatement
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.UnitaryActHalfSpaceStatement
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.HermitianWeilActionUnitaryGroupTestFunctionsStatement
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ThHSiegelOperatorStatement

open Matrix Complex NumberField GlobalTheory.SW Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (cc herm)
open scoped ComplexConjugate ComplexOrder Real Classical

namespace GlobalTheory.SW.Emb

noncomputable section

section Corner

variable {R S : Type} [CommRing R] [CommRing S] {N : ℕ}

def cor (c : R) (A : Matrix (Fin N) (Fin N) R) : Matrix (Fin (N + 1)) (Fin (N + 1)) R :=
  Matrix.of fun i j => Fin.cases (Fin.cases c (fun _ => 0) j) (fun i' => Fin.cases 0 (A i') j) i

@[simp] theorem corner_embedding_succ_succ (c : R) (A : Matrix (Fin N) (Fin N) R) : cor c A 0 0 = c := rfl
@[simp] theorem cor_zs (c : R) (A : Matrix (Fin N) (Fin N) R) (j : Fin N) :
    cor c A 0 j.succ = 0 := rfl
@[simp] theorem cor_sz (c : R) (A : Matrix (Fin N) (Fin N) R) (i : Fin N) :
    cor c A i.succ 0 = 0 := rfl
@[simp] theorem cor_ss (c : R) (A : Matrix (Fin N) (Fin N) R) (i j : Fin N) :
    cor c A i.succ j.succ = A i j := rfl

theorem cor_mul (a b : R) (A B : Matrix (Fin N) (Fin N) R) :
    cor a A * cor b B = cor (a * b) (A * B) := by
  ext i j
  refine Fin.cases ?_ (fun i => ?_) i <;> refine Fin.cases ?_ (fun j => ?_) j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_succ]

theorem cor_add (a b : R) (A B : Matrix (Fin N) (Fin N) R) :
    cor a A + cor b B = cor (a + b) (A + B) := by
  ext i j
  refine Fin.cases ?_ (fun i => ?_) i <;> refine Fin.cases ?_ (fun j => ?_) j <;>
    simp

theorem cor_neg (a : R) (A : Matrix (Fin N) (Fin N) R) : -cor a A = cor (-a) (-A) := by
  ext i j
  refine Fin.cases ?_ (fun i => ?_) i <;> refine Fin.cases ?_ (fun j => ?_) j <;>
    simp

theorem cor_one : cor (1 : R) (1 : Matrix (Fin N) (Fin N) R) = 1 := by
  ext i j
  refine Fin.cases ?_ (fun i => ?_) i <;> refine Fin.cases ?_ (fun j => ?_) j <;>
    simp [Matrix.one_apply, Fin.succ_ne_zero, eq_comm (a := (0 : Fin (N + 1)))]

theorem cor_zero : cor (0 : R) (0 : Matrix (Fin N) (Fin N) R) = 0 := by
  ext i j
  refine Fin.cases ?_ (fun i => ?_) i <;> refine Fin.cases ?_ (fun j => ?_) j <;>
    simp

theorem cor_map (f : R →+* S) (a : R) (A : Matrix (Fin N) (Fin N) R) :
    (cor a A).map f = cor (f a) (A.map f) := by
  ext i j
  refine Fin.cases ?_ (fun i => ?_) i <;> refine Fin.cases ?_ (fun j => ?_) j <;>
    simp

theorem cor_conjTranspose (a : ℂ) (A : Matrix (Fin N) (Fin N) ℂ) :
    (cor a A)ᴴ = cor (conj a) Aᴴ := by
  ext i j
  refine Fin.cases ?_ (fun i => ?_) i <;> refine Fin.cases ?_ (fun j => ?_) j <;>
    simp [Matrix.conjTranspose_apply]

theorem cor_mulVec (a : R) (A : Matrix (Fin N) (Fin N) R) (x : R) (v : Fin N → R) :
    cor a A *ᵥ (Fin.cons x v : Fin (N + 1) → R) = (Fin.cons (a * x) (A *ᵥ v) : Fin (N + 1) → R) := by
  ext i
  refine Fin.cases ?_ (fun i => ?_) i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_succ]

theorem cons_dot (x y : R) (v w : Fin N → R) :
    (Fin.cons x v : Fin (N + 1) → R) ⬝ᵥ (Fin.cons y w : Fin (N + 1) → R) = x * y + v ⬝ᵥ w := by
  simp [dotProduct, Fin.sum_univ_succ]

theorem cor_inv (A : Matrix (Fin N) (Fin N) ℂ) (h : A.det ≠ 0) : (cor 1 A)⁻¹ = cor 1 A⁻¹ := by
  apply Matrix.inv_eq_right_inv
  rw [cor_mul, one_mul, Matrix.mul_nonsing_inv A (isUnit_iff_ne_zero.mpr h), cor_one]

theorem det_cor_den (C D : Matrix (Fin N) (Fin N) R) (Z : Matrix (Fin (N + 1)) (Fin (N + 1)) R) :
    (cor 0 C * Z + cor 1 D).det = (C * Z.submatrix Fin.succ Fin.succ + D).det := by
  rw [Matrix.det_succ_row_zero, Fin.sum_univ_succ]
  have e : (cor 0 C * Z + cor 1 D).submatrix Fin.succ (Fin.succAbove 0) = C * Z.submatrix Fin.succ Fin.succ + D := by
    ext i j
    simp [Matrix.mul_apply, Fin.sum_univ_succ]
  rw [e]
  simp [Matrix.mul_apply, Fin.sum_univ_succ]

theorem det_cor_one (D : Matrix (Fin N) (Fin N) R) : (cor 1 D).det = D.det := by
  simpa using det_cor_den (0 : Matrix (Fin N) (Fin N) R) D 0

theorem posDef_cor_one (A : Matrix (Fin N) (Fin N) ℂ) (h : A.PosDef) : (cor 1 A).PosDef := by
  rw [Matrix.posDef_iff_dotProduct_mulVec]
  refine ⟨?_, fun x hx => ?_⟩
  · rw [Matrix.IsHermitian, cor_conjTranspose, h.1.eq]
    simp
  · obtain ⟨a, v, rfl⟩ : ∃ (a : ℂ) (v : Fin N → ℂ), x = Fin.cons a v :=
      ⟨x 0, Fin.tail x, (Fin.cons_self_tail x).symm⟩
    have hs : star (Fin.cons a v : Fin (N + 1) → ℂ) = Fin.cons (star a) (star v) := by
      ext i; refine Fin.cases ?_ (fun i => ?_) i <;> simp
    rw [cor_mulVec, hs, cons_dot, one_mul]
    by_cases hv : v = 0
    · subst hv
      have ha : a ≠ 0 := by
        rintro rfl; exact hx (by ext i; refine Fin.cases ?_ (fun i => ?_) i <;> simp)
      simp only [Matrix.mulVec_zero, dotProduct_zero, add_zero]
      rw [Complex.star_def, ← Complex.normSq_eq_conj_mul_self]
      exact_mod_cast Complex.normSq_pos.mpr ha
    · have h1 : 0 ≤ star a * a := by
        rw [Complex.star_def, ← Complex.normSq_eq_conj_mul_self]; exact_mod_cast Complex.normSq_nonneg a
      exact add_pos_of_nonneg_of_pos h1 (h.dotProduct_mulVec_pos hv)

theorem imH_cor (A : Matrix (Fin N) (Fin N) ℂ) : imH (cor I A) = cor 1 (imH A) := by
  unfold imH
  rw [cor_conjTranspose]
  ext i j
  refine Fin.cases ?_ (fun i => ?_) i <;> refine Fin.cases ?_ (fun j => ?_) j <;> simp
  field_simp
  rw [Complex.I_sq]
  ring

end Corner

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {Ψ : Finset (E →+* ℂ)} {n N : ℕ}

def emb (γ : M2 E N) : M2 E (N + 1) :=
  Matrix.fromBlocks (cor 1 γ.toBlocks₁₁) (cor 0 γ.toBlocks₁₂) (cor 0 γ.toBlocks₂₁)
    (cor 1 γ.toBlocks₂₂)

theorem ccT_cor (a : E) (A : Matrix (Fin N) (Fin N) E) : ccT (cor a A) = cor (cc a) (ccT A) := by
  ext i j
  refine Fin.cases ?_ (fun i => ?_) i <;> refine Fin.cases ?_ (fun j => ?_) j <;>
    simp [ccT, cc]

theorem ccT_fromBlocks {m : ℕ} (A B C D : Matrix (Fin m) (Fin m) E) :
    ccT (Matrix.fromBlocks A B C D) = Matrix.fromBlocks (ccT A) (ccT C) (ccT B) (ccT D) := by
  simp [ccT, Matrix.fromBlocks_map, Matrix.fromBlocks_transpose]

private theorem fromBlocks_cor_mul_fromBlocks_cor {R : Type} [CommRing R] {N : ℕ} (a b c d a' b' c' d' : R)
    (A B C D A' B' C' D' : Matrix (Fin N) (Fin N) R) :
    Matrix.fromBlocks (cor a A) (cor b B) (cor c C) (cor d D) *
        Matrix.fromBlocks (cor a' A') (cor b' B') (cor c' C') (cor d' D') =
      Matrix.fromBlocks (cor (a * a' + b * c') (A * A' + B * C')) (cor (a * b' + b * d') (A * B' + B * D'))
        (cor (c * a' + d * c') (C * A' + D * C')) (cor (c * b' + d * d') (C * B' + D * D')) := by
  rw [Matrix.fromBlocks_multiply]
  simp only [cor_mul, cor_add]

theorem emb_mem {γ : M2 E N} (h : γ ∈ UU E N) : emb γ ∈ UU E (N + 1) := by
  have h' : ccT γ * Matrix.J (Fin N) E * γ = Matrix.J (Fin N) E := h
  rw [← Matrix.fromBlocks_toBlocks γ, ccT_fromBlocks, Matrix.J, Matrix.fromBlocks_multiply,
    Matrix.fromBlocks_multiply] at h'
  obtain ⟨h11, h12, h21, h22⟩ := Matrix.fromBlocks_inj.mp h'
  have hJ : Matrix.J (Fin (N + 1)) E =
      Matrix.fromBlocks (cor 0 0) (cor (-1) (-1)) (cor 1 1) (cor 0 0) := by
    rw [Matrix.J, cor_zero, ← cor_neg, cor_one]
  show ccT (emb γ) * Matrix.J (Fin (N + 1)) E * emb γ = Matrix.J (Fin (N + 1)) E
  rw [hJ, emb, ccT_fromBlocks, ccT_cor, ccT_cor, ccT_cor, ccT_cor, fromBlocks_cor_mul_fromBlocks_cor, fromBlocks_cor_mul_fromBlocks_cor]
  simp only [h11, h12, h21, h22, cc, map_one, map_zero]
  congr 1 <;> congr 1 <;> ring

omit [NumberField E] [IsCMField E] in
theorem hDen_emb_det (γ : M2 E N) (Z : CM Ψ (N + 1) (N + 1)) (τ : Ψ) :
    (hDen Ψ (emb γ) Z τ).det = (hDen Ψ γ (dropZ Ψ Z) τ).det := by
  simp only [hDen, emb, Matrix.toBlocks_fromBlocks₂₁, Matrix.toBlocks_fromBlocks₂₂, cor_map, map_zero, map_one]
  exact det_cor_den _ _ _

def corZ (s : ℂ) (Z : CM Ψ N N) : CM Ψ (N + 1) (N + 1) := fun τ => cor s (Z τ)

def corV (z : CM Ψ n N) : CM Ψ n (N + 1) := fun τ => Matrix.of fun k => Fin.cons 0 (z τ k)

omit [NumberField E] [IsCMField E] in
theorem corZ_mem {Z : CM Ψ N N} (h : Z ∈ Hn Ψ N) : corZ I Z ∈ Hn Ψ (N + 1) := by
  intro τ
  show (imH (cor I (Z τ))).PosDef
  rw [imH_cor]
  exact posDef_cor_one _ (h τ)

omit [NumberField E] [IsCMField E] in
theorem pushZ_corZ (Z : CM Ψ N N) (t : ℝ) :
    pushZ Ψ (corZ I Z) (Pi.single 0 1) t = corZ (I + I * t) Z := by
  funext τ
  ext i j
  refine Fin.cases ?_ (fun i => ?_) i <;> refine Fin.cases ?_ (fun j => ?_) j <;>
    simp [pushZ, corZ, Matrix.vecMulVec_apply, Pi.single_apply, Fin.succ_ne_zero]

omit [NumberField E] [IsCMField E] in
theorem dropZ_corZ (s : ℂ) (Z : CM Ψ N N) : dropZ Ψ (corZ s Z) = Z := by
  funext τ
  ext i j
  simp [dropZ, corZ]

omit [NumberField E] [IsCMField E] in
theorem drop_corV (z : CM Ψ n N) : (fun τ => (corV z τ).submatrix id Fin.succ) = z := by
  funext τ
  ext k a
  simp [corV]

omit [NumberField E] [IsCMField E] in
theorem hDen_emb (γ : M2 E N) (s : ℂ) (Z : CM Ψ N N) (τ : Ψ) :
    hDen Ψ (emb γ) (corZ s Z) τ = cor 1 (hDen Ψ γ Z τ) := by
  simp only [hDen, emb, corZ, Matrix.toBlocks_fromBlocks₂₁, Matrix.toBlocks_fromBlocks₂₂, cor_map, map_zero, map_one,
    cor_mul, cor_add, zero_mul, zero_add]

omit [NumberField E] [IsCMField E] in
theorem hDen'_emb (γ : M2 E N) (s : ℂ) (Z : CM Ψ N N) (τ : Ψ) :
    hDen' Ψ (emb γ) (corZ s Z) τ = cor 1 (hDen' Ψ γ Z τ) := by
  simp only [hDen', emb, corZ, Matrix.toBlocks_fromBlocks₂₁, Matrix.toBlocks_fromBlocks₂₂, cor_map, map_zero, map_one,
    cor_conjTranspose, cor_mul, cor_add, mul_zero, zero_add, map_one]

omit [NumberField E] [IsCMField E] in
theorem hAct_emb (γ : M2 E N) (s : ℂ) (Z : CM Ψ N N) (h : ∀ τ, (hDen Ψ γ Z τ).det ≠ 0) :
    hAct Ψ (emb γ) (corZ s Z) = corZ s (hAct Ψ γ Z) := by
  funext τ
  simp only [hAct]
  rw [hDen_emb, cor_inv _ (h τ)]
  simp only [emb, corZ, Matrix.toBlocks_fromBlocks₁₁, Matrix.toBlocks_fromBlocks₁₂, cor_map, map_zero, map_one,
    cor_mul, cor_add, one_mul, add_zero, mul_one]
  rfl

omit [NumberField E] [IsCMField E] in
theorem hFac_emb (γ : M2 E N) (s : ℂ) (Z : CM Ψ N N) (h : ∀ τ, (hDen Ψ γ Z τ).det ≠ 0)
    (z z' : CM Ψ n N) : hFac Ψ (emb γ) (corZ s Z) (corV z) (corV z') = hFac Ψ γ Z z z' := by
  unfold hFac
  refine Finset.prod_congr rfl fun τ _ => ?_
  rw [hDen_emb, det_cor_one, cor_inv _ (h τ)]
  simp only [emb, Matrix.toBlocks_fromBlocks₂₁, cor_map, map_zero, cor_mul, one_mul]
  congr 3
  refine Finset.sum_congr rfl fun k _ => ?_
  show (Fin.cons 0 (z' τ k) : Fin (N + 1) → ℂ) ⬝ᵥ cor 0 _ *ᵥ (Fin.cons 0 (z τ k) : Fin (N + 1) → ℂ) = _
  rw [cor_mulVec, cons_dot]
  simp

theorem transH_drop (hΨ : IsType Ψ) {γ : M2 E N} (hγ : γ ∈ UU E N)
    {φ ψ : Matrix (Fin n) (Fin (N + 1)) E → ℂ} (hφ : IsSB φ) (hψ : IsSB ψ)
    (h : TransH Ψ (emb γ) φ ψ) : TransH Ψ γ (dropF φ) (dropF ψ) := by
  intro Z hZ z z'
  obtain ⟨hden, hact, -⟩ := (GlobalTheory.T.unitary_act_halfSpace_alt E Ψ N γ hγ).2 Z hZ
  have hdet : ∀ τ, (hDen Ψ γ Z τ).det ≠ 0 := fun τ => (hden τ).1
  have hdet' : ∀ τ, (hDen' Ψ γ Z τ).det ≠ 0 := fun τ h0 =>
    (hden τ).1 (by rw [← (hden τ).2.1, h0, zero_mul])
  obtain ⟨w, hw⟩ : ∃ w : CM Ψ n N, w = fun τ => Matrix.of fun k => (hDen' Ψ γ Z τ)⁻¹ *ᵥ z τ k := ⟨_, rfl⟩
  obtain ⟨w', hw'⟩ : ∃ w' : CM Ψ n N, w' = fun τ => Matrix.of fun k => z' τ k ᵥ* (hDen Ψ γ Z τ)⁻¹ :=
    ⟨_, rfl⟩
  rw [← hw, ← hw']
  have hWφ := (GlobalTheory.T.tendsto_thH_pushZ_atTop_thH_dropF E Ψ hΨ n N φ hφ).2 (corZ I Z) (corZ_mem hZ)
  have hWψ := (GlobalTheory.T.tendsto_thH_pushZ_atTop_thH_dropF E Ψ hΨ n N ψ hψ).2 (corZ I (hAct Ψ γ Z)) (corZ_mem hact)
  have L1 := hWφ.2.2 (corV z) (corV z')
  have L2 := hWψ.2.2 (corV w) (corV w')
  simp only [dropZ_corZ, drop_corV] at L1 L2
  have key : ∀ t : ℝ, 0 ≤ t →
      thH Ψ ψ (pushZ Ψ (corZ I (hAct Ψ γ Z)) (Pi.single 0 1) t) (corV w) (corV w') =
        hFac Ψ γ Z z z' * thH Ψ φ (pushZ Ψ (corZ I Z) (Pi.single 0 1) t) (corV z) (corV z') := by
    intro t ht
    have hmem := hWφ.2.1 t ht
    have e := h _ hmem (corV z) (corV z')
    simp only [pushZ_corZ] at hmem e ⊢
    rw [hAct_emb γ _ Z hdet, hFac_emb γ _ Z hdet] at e
    rw [← e]
    congr 1
    · funext τ
      ext k j
      refine Fin.cases ?_ (fun j => ?_) j <;>
        simp [hw, corV, hDen'_emb, cor_inv _ (hdet' τ), Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
    · funext τ
      ext k j
      refine Fin.cases ?_ (fun j => ?_) j <;>
        simp [hw', corV, hDen_emb, cor_inv _ (hdet τ), Matrix.vecMul, dotProduct, Fin.sum_univ_succ]
  exact tendsto_nhds_unique_of_eventuallyEq L2 (L1.const_mul _) ((Filter.eventually_ge_atTop 0).mono key)

theorem dropF_weil (hΨ : IsType Ψ) (hn : Even n) {γ : M2 E N} (hγ : γ ∈ UU E N)
    {φ : Matrix (Fin n) (Fin (N + 1)) E → ℂ} (hφ : IsSB φ) :
    dropF (weil Ψ (emb γ) φ) = weil Ψ γ (dropF φ) := by
  obtain ⟨hsb, htr, -⟩ := GlobalTheory.T.hermitianWeilAction_unitaryGroup_testFunctions E Ψ hΨ n (N + 1) hn (emb γ) (emb_mem hγ) φ hφ
  have hd := (GlobalTheory.T.tendsto_thH_pushZ_atTop_thH_dropF E Ψ hΨ n N φ hφ).1
  have hdw := (GlobalTheory.T.tendsto_thH_pushZ_atTop_thH_dropF E Ψ hΨ n N _ hsb).1
  exact (GlobalTheory.T.hermitianWeilAction_unitaryGroup_testFunctions E Ψ hΨ n N hn γ hγ (dropF φ) hd).2.2.1 _ hdw (transH_drop hΨ hγ hφ hsb htr)

abbrev up (N : ℕ) : Fin N ⊕ Fin N → Fin (N + 1) ⊕ Fin (N + 1) := Sum.map Fin.succ Fin.succ

def extV (E : Type) [Field E] (N : ℕ) :
    (Fin N ⊕ Fin N → E) →ₗ[E] (Fin (N + 1) ⊕ Fin (N + 1) → E) where
  toFun v := Sum.elim (Fin.cons 0 fun a => v (Sum.inl a)) (Fin.cons 0 fun a => v (Sum.inr a))
  map_add' v w := by
    ext (i | i) <;> refine Fin.cases ?_ (fun i => ?_) i <;> simp
  map_smul' c v := by
    ext (i | i) <;> refine Fin.cases ?_ (fun i => ?_) i <;> simp

omit [IsCMField E] in

theorem botSpan_eq (h : M2 E (N + 1)) (h0 : h (Sum.inr 0) = Pi.single (Sum.inr 0) 1)
    (h1 : ∀ a, h (Sum.inr a) (Sum.inl 0) = 0) :
    botSpan h = (E ∙ Pi.single (Sum.inr 0) 1) ⊔
      (botSpan (h.submatrix (up N) (up N))).map (extV E N) := by
  have key : ∀ b : Fin N, extV E N ((h.submatrix (up N) (up N)) (Sum.inr b)) =
      h (Sum.inr b.succ) - h (Sum.inr b.succ) (Sum.inr 0) • Pi.single (Sum.inr 0) 1 := by
    intro b
    ext (i | i) <;> refine Fin.cases ?_ (fun i => ?_) i <;> simp [extV, h1, Pi.single_apply]
  apply le_antisymm
  · refine Submodule.span_le.mpr ?_
    rintro _ ⟨a, rfl⟩
    show h (Sum.inr a) ∈ _
    induction a using Fin.cases with
    | zero => rw [h0]; exact Submodule.mem_sup_left (Submodule.mem_span_singleton_self _)
    | succ b =>
      have e : h (Sum.inr b.succ) = h (Sum.inr b.succ) (Sum.inr 0) • Pi.single (Sum.inr 0) 1 +
          extV E N ((h.submatrix (up N) (up N)) (Sum.inr b)) := by rw [key]; abel
      rw [e]
      exact Submodule.add_mem _
        (Submodule.mem_sup_left (Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)))
        (Submodule.mem_sup_right (Submodule.mem_map_of_mem (Submodule.subset_span ⟨b, rfl⟩)))
  · refine sup_le ?_ ?_
    · rw [Submodule.span_singleton_le_iff_mem, ← h0]
      exact Submodule.subset_span ⟨0, rfl⟩
    · rw [Submodule.map_le_iff_le_comap]
      refine Submodule.span_le.mpr ?_
      rintro _ ⟨b, rfl⟩
      show extV E N ((h.submatrix (up N) (up N)) (Sum.inr b)) ∈ botSpan h
      rw [key]
      refine Submodule.sub_mem _ (Submodule.subset_span ⟨b.succ, rfl⟩) (Submodule.smul_mem _ _ ?_)
      rw [← h0]
      exact Submodule.subset_span ⟨0, rfl⟩

omit [IsCMField E] in
theorem botSpan_emb (γ : M2 E N) :
    botSpan (emb γ) = (E ∙ Pi.single (Sum.inr 0) 1) ⊔ (botSpan γ).map (extV E N) := by
  have h0 : emb γ (Sum.inr 0) = Pi.single (Sum.inr 0) 1 := by
    ext (j | j) <;> refine Fin.cases ?_ (fun j => ?_) j <;> simp [emb, Pi.single_apply]
  have h1 : ∀ a, emb γ (Sum.inr a) (Sum.inl 0) = 0 := by
    intro a; refine Fin.cases ?_ (fun a => ?_) a <;> simp [emb]
  have hs : (emb γ).submatrix (up N) (up N) = γ := by
    ext (i | i) (j | j) <;>
      simp [emb, Matrix.toBlocks₁₁, Matrix.toBlocks₁₂, Matrix.toBlocks₂₁, Matrix.toBlocks₂₂]
  rw [botSpan_eq (emb γ) h0 h1, hs]

omit [IsCMField E] in
theorem map_botSpan_emb (γ : M2 E N) :
    (botSpan (emb γ)).map (LinearMap.funLeft E E (up N)) = botSpan γ := by
  rw [botSpan_emb, Submodule.map_sup, Submodule.map_span, Set.image_singleton, ← Submodule.map_comp]
  have e1 : LinearMap.funLeft E E (up N) (Pi.single (Sum.inr 0) 1) = 0 := by
    funext j
    rcases j with j | j <;> simp [LinearMap.funLeft_apply, Pi.single_apply, Fin.succ_ne_zero]
  have e2 : (LinearMap.funLeft E E (up N)).comp (extV E N) = LinearMap.id := by
    refine LinearMap.ext fun v => ?_
    funext j
    rcases j with j | j <;> simp [extV, LinearMap.funLeft_apply]
  rw [e1, e2, Submodule.map_id, Submodule.span_singleton_eq_bot.mpr rfl, bot_sup_eq]

omit [IsCMField E] in
theorem botSpan_emb_iff (γ γ' : M2 E N) :
    botSpan (emb γ) = botSpan (emb γ') ↔ botSpan γ = botSpan γ' := by
  constructor
  · intro h
    rw [← map_botSpan_emb γ, h, map_botSpan_emb]
  · intro h
    rw [botSpan_emb, botSpan_emb, h]

omit [IsCMField E] in
theorem botSpan_mul_le {m : ℕ} (a d : Matrix (Fin m) (Fin m) E) (g : M2 E m) :
    botSpan (Matrix.fromBlocks a 0 0 d * g) ≤ botSpan g := by
  refine Submodule.span_le.mpr ?_
  rintro _ ⟨i, rfl⟩
  have e : (Matrix.fromBlocks a 0 0 d * g) (Sum.inr i) = ∑ k, d i k • g (Sum.inr k) := by
    ext j
    simp [Matrix.mul_apply, Fintype.sum_sum_type, Finset.sum_apply]
  show (Matrix.fromBlocks a 0 0 d * g) (Sum.inr i) ∈ botSpan g
  rw [e]
  exact Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩)

omit [NumberField E] [IsCMField E] in

theorem exists_col (v : Fin (N + 1) → E) (hv : v ≠ 0) :
    ∃ b : Matrix (Fin (N + 1)) (Fin (N + 1)) E, IsUnit b.det ∧ ∀ i, b i 0 = v i := by
  obtain ⟨k, hk⟩ : ∃ k, v k ≠ 0 := by
    by_contra hc
    exact hv (funext fun i => by_contra fun hi => hc ⟨i, hi⟩)
  set c : Matrix (Fin (N + 1)) (Fin (N + 1)) E := Matrix.of fun i j =>
    Fin.cases (v (Equiv.swap 0 k i)) (fun j' : Fin N => if i = j'.succ then (1 : E) else 0) j with hcdef
  have hc : c.det = v k := by
    rw [Matrix.det_succ_row_zero, Fin.sum_univ_succ]
    have e : c.submatrix Fin.succ (Fin.succAbove 0) = 1 := by
      ext i j
      simp [hcdef, Matrix.one_apply]
    rw [e]
    simp [hcdef, Fin.succ_ne_zero, eq_comm (a := (0 : Fin (N + 1)))]
  refine ⟨c.submatrix (Equiv.swap 0 k) id, ?_, fun i => ?_⟩
  · rw [Matrix.det_permute, hc]
    refine isUnit_iff_ne_zero.mpr (mul_ne_zero ?_ hk)
    rcases Int.units_eq_one_or (Equiv.Perm.sign (Equiv.swap 0 k)) with hs | hs <;> simp [hs]
  · simp [hcdef]

private theorem ccT_mul_J_mul_apply {m : ℕ} (M : M2 E m) (p q : Fin m ⊕ Fin m) :
    (ccT M * Matrix.J (Fin m) E * M) p q =
      ∑ i, cc (M (Sum.inr i) p) * M (Sum.inl i) q - ∑ i, cc (M (Sum.inl i) p) * M (Sum.inr i) q := by
  simp [Matrix.mul_apply, Matrix.J, ccT, Fintype.sum_sum_type, Matrix.one_apply, sub_eq_add_neg]

private theorem cc_cc_siegel_theta_transformation (x : E) : cc (cc x) = x := by
  have := congrFun (congrFun (Base.ccT_ccT (Matrix.of fun (_ : Unit) (_ : Unit) => x)) ()) ()
  simpa [ccT] using this

theorem sub_mem {h : M2 E (N + 1)} (hh : h ∈ UU E (N + 1))
    (hc : ∀ i, h i (Sum.inl 0) = (Pi.single (Sum.inl 0) 1 : Fin (N + 1) ⊕ Fin (N + 1) → E) i) :
    h (Sum.inr 0) = Pi.single (Sum.inr 0) 1 ∧ h.submatrix (up N) (up N) ∈ UU E N := by
  have hU : ∀ p q, (ccT h * Matrix.J (Fin (N + 1)) E * h) p q = Matrix.J (Fin (N + 1)) E p q := by
    intro p q
    rw [show ccT h * Matrix.J (Fin (N + 1)) E * h = Matrix.J (Fin (N + 1)) E from hh]
  have hl : ∀ i, h (Sum.inl i) (Sum.inl 0) = if i = 0 then 1 else 0 := fun i => by
    rw [hc]; simp [Pi.single_apply]
  have hr : ∀ i, h (Sum.inr i) (Sum.inl 0) = 0 := fun i => by
    rw [hc]; simp [Pi.single_apply]
  have hrow : h (Sum.inr 0) = Pi.single (Sum.inr 0) 1 := by
    funext p
    have e := hU p (Sum.inl 0)
    rw [ccT_mul_J_mul_apply] at e
    simp only [hl, hr, mul_zero, Finset.sum_const_zero, sub_zero, mul_ite, mul_one, Finset.sum_ite_eq',
      Finset.mem_univ, if_true] at e
    have e2 : Matrix.J (Fin (N + 1)) E p (Sum.inl 0) = (Pi.single (Sum.inr 0) 1 : _ → E) p := by
      rcases p with p | p <;> simp [Matrix.J, Matrix.one_apply, Pi.single_apply, eq_comm]
    rw [e2] at e
    have e3 := congrArg cc e
    rw [cc_cc_siegel_theta_transformation] at e3
    rw [e3]
    rcases p with p | p <;> simp [Pi.single_apply, cc]
  refine ⟨hrow, ?_⟩
  have hJ : ∀ p q, Matrix.J (Fin (N + 1)) E (up N p) (up N q) = Matrix.J (Fin N) E p q := by
    rintro (p | p) (q | q) <;> simp [Matrix.J, Matrix.one_apply]
  have z1 : ∀ x : Fin N ⊕ Fin N, (Pi.single (Sum.inr 0) 1 : Fin (N + 1) ⊕ Fin (N + 1) → E) (up N x) = 0 := by
    rintro (x | x) <;> simp [Pi.single_apply, Fin.succ_ne_zero]
  show ccT (h.submatrix (up N) (up N)) * Matrix.J (Fin N) E * h.submatrix (up N) (up N) = Matrix.J (Fin N) E
  ext p q
  have e := hU (up N p) (up N q)
  rw [ccT_mul_J_mul_apply, Fin.sum_univ_succ, Fin.sum_univ_succ, hrow, hJ] at e
  rw [ccT_mul_J_mul_apply, ← e]
  simp [z1, cc]

theorem exists_botSpan {g : M2 E (N + 1)} (hg : g ∈ UU E (N + 1))
    (h0 : ∀ a, g.toBlocks₂₁ a 0 = 0) : ∃ γ ∈ UU E N, botSpan g = botSpan (emb γ) := by
  have hgU := (GlobalTheory.T.unitary_act_halfSpace_alt E (∅ : Finset (E →+* ℂ)) (N + 1) g hg).1
  have h0' : ∀ a, g (Sum.inr a) (Sum.inl 0) = 0 := fun a => by simpa [Matrix.toBlocks₂₁] using h0 a
  obtain ⟨v, hvd⟩ : ∃ v : Fin (N + 1) → E, v = fun i => g (Sum.inl i) (Sum.inl 0) := ⟨_, rfl⟩
  have hv : v ≠ 0 := by
    intro hv0
    refine (isUnit_iff_ne_zero.mp hgU.1) (Matrix.det_eq_zero_of_column_eq_zero (Sum.inl 0) ?_)
    rintro (i | i)
    · have := congrFun hv0 i
      rw [hvd] at this
      simpa using this
    · exact h0' i
  obtain ⟨b, hb, hbv⟩ := exists_col v hv
  have e2 : b * b⁻¹ = 1 := Matrix.mul_nonsing_inv _ hb
  have e1 : ccT b⁻¹ * ccT b = 1 := by rw [← Base.ccT_mul, e2, Base.ccT_one]
  have e0 : ccT (0 : Matrix (Fin (N + 1)) (Fin (N + 1)) E) = 0 := by
    ext i j; simp [ccT, cc]
  obtain ⟨δ, hδd⟩ : ∃ δ : M2 E (N + 1), δ = Matrix.fromBlocks b⁻¹ 0 0 (ccT b) := ⟨_, rfl⟩
  have hδ : δ ∈ UU E (N + 1) := by
    show ccT δ * Matrix.J _ E * δ = Matrix.J _ E
    rw [hδd, ccT_fromBlocks, e0, Base.ccT_ccT, Matrix.J, Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply]
    simp [e1, e2]
  have hh : δ * g ∈ UU E (N + 1) := hgU.2.2.2.2 δ hδ
  have hv' : b *ᵥ Pi.single 0 1 = v := by
    funext i; simp [Matrix.mulVec_single, hbv]
  have hinv : b⁻¹ *ᵥ v = Pi.single 0 1 := by
    rw [← hv', Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hb, Matrix.one_mulVec]
  have hc : ∀ i, (δ * g) i (Sum.inl 0) = (Pi.single (Sum.inl 0) 1 : _ → E) i := by
    rintro (i | i)
    · have := congrFun hinv i
      rw [hvd] at this
      simp only [Matrix.mulVec, dotProduct] at this
      simp [hδd, Matrix.mul_apply, Fintype.sum_sum_type, h0', this, Pi.single_apply]
    · simp [hδd, Matrix.mul_apply, Fintype.sum_sum_type, h0']
  obtain ⟨hrow, hsub⟩ := sub_mem hh hc
  have h1 : ∀ a, (δ * g) (Sum.inr a) (Sum.inl 0) = 0 := fun a => by rw [hc]; simp
  refine ⟨(δ * g).submatrix (up N) (up N), hsub, ?_⟩
  rw [botSpan_emb, ← botSpan_eq (δ * g) hrow h1]
  apply le_antisymm
  · calc botSpan g = botSpan (Matrix.fromBlocks b 0 0 (ccT b⁻¹) * (δ * g)) := by
          rw [← Matrix.mul_assoc, hδd, Matrix.fromBlocks_multiply]
          simp [e1, e2]
      _ ≤ botSpan (δ * g) := botSpan_mul_le _ _ _
  · rw [hδd]
    exact botSpan_mul_le _ _ _

theorem exists_embedding : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Ψ : Finset (E →+* ℂ)), IsType Ψ → ∀ (n N : ℕ), Even n → ∃ ι : M2 E N → M2 E (N + 1), (∀ γ ∈ UU E N, ι γ ∈ UU E (N + 1) ∧ (∀ a, (ι γ).toBlocks₂₁ a 0 = 0) ∧ (∀ (Z : CM Ψ (N + 1) (N + 1)) τ, (hDen Ψ (ι γ) Z τ).det = (hDen Ψ γ (dropZ Ψ Z) τ).det) ∧ (∀ φ : Matrix (Fin n) (Fin (N + 1)) E → ℂ, IsSB φ → dropF (weil Ψ (ι γ) φ) = weil Ψ γ (dropF φ)) ∧ ∀ γ' ∈ UU E N, (botSpan (ι γ) = botSpan (ι γ') ↔ botSpan γ = botSpan γ')) ∧ ∀ g ∈ UU E (N + 1), (∀ a, g.toBlocks₂₁ a 0 = 0) → ∃ γ ∈ UU E N, botSpan g = botSpan (ι γ) := by
  intro E _ _ _ Ψ hΨ n N hn
  refine ⟨emb, fun γ hγ => ⟨emb_mem hγ, fun a => ?_, fun Z τ => hDen_emb_det γ Z τ,
    fun φ hφ => dropF_weil hΨ hn hγ hφ, fun γ' _ => botSpan_emb_iff γ γ'⟩, fun g hg h0 => exists_botSpan hg h0⟩
  refine Fin.cases ?_ (fun a => ?_) a <;> simp [emb]

end

end GlobalTheory.SW.Emb
