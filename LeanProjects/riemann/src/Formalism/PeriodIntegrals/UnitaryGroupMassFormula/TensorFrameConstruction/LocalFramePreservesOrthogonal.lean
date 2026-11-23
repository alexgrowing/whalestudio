import Mathlib
import Formalism.PeriodIntegrals.ScPiExists

noncomputable section

open Matrix
open scoped ComplexOrder

namespace PI.ScPiBuildW.Loc

open PI.ScPiExists

section Basic

variable {n : ℕ} (ε : Fin n → Bool)

lemma hJ_add_left (x x' y : Fin n → ℂ) : hJ ε (x + x') y = hJ ε x y + hJ ε x' y := by
  first | simp only [hJ, star_add, add_dotProduct] | simp [hJ, add_dotProduct]

lemma hJ_add_right (x y y' : Fin n → ℂ) : hJ ε x (y + y') = hJ ε x y + hJ ε x y' := by
  first | simp only [hJ, Matrix.mulVec_add, dotProduct_add] | simp [hJ, Matrix.mulVec_add, dotProduct_add]

lemma hJ_sub_left (x x' y : Fin n → ℂ) : hJ ε (x - x') y = hJ ε x y - hJ ε x' y := by
  first | simp only [hJ, star_sub, sub_dotProduct] | simp [hJ, sub_dotProduct]

lemma hJ_sub_right (x y y' : Fin n → ℂ) : hJ ε x (y - y') = hJ ε x y - hJ ε x y' := by
  first | simp only [hJ, Matrix.mulVec_sub, dotProduct_sub] | simp [hJ, Matrix.mulVec_sub, dotProduct_sub]

lemma hJ_smul_left (c : ℂ) (x y : Fin n → ℂ) : hJ ε (c • x) y = star c * hJ ε x y := by
  first | simp only [hJ, star_smul, smul_dotProduct, smul_eq_mul] | simp [hJ, smul_dotProduct]

lemma hJ_smul_right (c : ℂ) (x y : Fin n → ℂ) : hJ ε x (c • y) = c * hJ ε x y := by
  first | simp only [hJ, Matrix.mulVec_smul, dotProduct_smul, smul_eq_mul] | simp [hJ, Matrix.mulVec_smul, dotProduct_smul]

lemma hJ_zero_left (y : Fin n → ℂ) : hJ ε 0 y = 0 := by
  simp [hJ]

lemma hJ_zero_right (x : Fin n → ℂ) : hJ ε x 0 = 0 := by
  simp [hJ]

lemma hJ_sum_right {ι : Type*} (s : Finset ι) (x : Fin n → ℂ) (c : ι → ℂ) (u : ι → Fin n → ℂ) :
    hJ ε x (∑ i ∈ s, c i • u i) = ∑ i ∈ s, c i * hJ ε x (u i) := by
  classical
  refine Finset.induction_on s (by simp [hJ_zero_right]) ?_
  intro a s ha ih
  rw [Finset.sum_insert ha, Finset.sum_insert ha, hJ_add_right, hJ_smul_right, ih]

lemma hJ_conj (x y : Fin n → ℂ) : hJ ε x y = star (hJ ε y x) := by
  simp only [hJ, Formalism.REAL.Jm, dotProduct, Matrix.mulVec_diagonal, star_sum, Pi.star_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  split_ifs <;> simp <;> ring

lemma hJ_nondeg_right (y : Fin n → ℂ) (h : ∀ x, hJ ε x y = 0) : y = 0 := by
  funext i
  have h1 := h (Pi.single i (1 : ℂ))
  have hs : star (Pi.single i (1 : ℂ) : Fin n → ℂ) = (Pi.single i 1 : Fin n → ℂ) := by
    funext j
    by_cases hj : j = i
    · subst hj
      simp
    · simp [Pi.single_apply, hj]
  have e : hJ ε (Pi.single i 1) y = (if ε i then 1 else -1) * y i := by
    first
      | rw [hJ, hs, single_dotProduct, one_mul, Formalism.REAL.Jm, Matrix.mulVec_diagonal]
      | rw [hJ, hs, Matrix.single_dotProduct, one_mul, Formalism.REAL.Jm, Matrix.mulVec_diagonal]
      | simp [hJ, hs, Formalism.REAL.Jm, Matrix.mulVec_diagonal]
  rw [e] at h1
  simp only [Pi.zero_apply]
  split_ifs at h1 <;> simpa using h1

lemma hJ_nondeg_left (x : Fin n → ℂ) (h : ∀ y, hJ ε x y = 0) : x = 0 :=
  hJ_nondeg_right ε x fun y => by rw [hJ_conj, h y, star_zero]

lemma hJ_unitary {g : Matrix (Fin n) (Fin n) ℂ} (hg : Formalism.REAL.inUJ ε g) (x y : Fin n → ℂ) :
    hJ ε (g *ᵥ x) (g *ᵥ y) = hJ ε x y := by
  have hg' : gᴴ * Formalism.REAL.Jm ε * g = Formalism.REAL.Jm ε := hg
  simp only [hJ]
  rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hg']

lemma hJ_span_left {S : Set (Fin n → ℂ)} {x y : Fin n → ℂ} (hx : x ∈ Submodule.span ℂ S)
    (h : ∀ a ∈ S, hJ ε a y = 0) : hJ ε x y = 0 := by
  induction hx using Submodule.span_induction with
  | mem a ha => exact h a ha
  | zero => exact hJ_zero_left ε y
  | add a b _ _ ha hb => rw [hJ_add_left, ha, hb, add_zero]
  | smul c a _ ha => rw [hJ_smul_left, ha, mul_zero]

lemma hJ_span_right {S : Set (Fin n → ℂ)} {x y : Fin n → ℂ} (hx : x ∈ Submodule.span ℂ S)
    (h : ∀ a ∈ S, hJ ε y a = 0) : hJ ε y x = 0 := by
  induction hx using Submodule.span_induction with
  | mem a ha => exact h a ha
  | zero => exact hJ_zero_right ε y
  | add a b _ _ ha hb => rw [hJ_add_right, ha, hb, add_zero]
  | smul c a _ ha => rw [hJ_smul_right, ha, mul_zero]

end Basic

structure LocFrame (n r k : ℕ) (ε : Fin n → Bool) where
  e : Fin r → Fin n → ℂ
  f : Fin r → Fin n → ℂ
  z : Fin n → ℂ
  w : Fin k → Fin n → ℂ
  hn : n = 2 * r + k + 1
  ee : ∀ a b, hJ ε (e a) (e b) = 0
  ef : ∀ a b, hJ ε (e a) (f b) = if a = b then 1 else 0
  ez : ∀ a, hJ ε (e a) z = 0
  fz : ∀ a, hJ ε (f a) z = 0
  zz : hJ ε z z ≠ 0
  ww : ∀ a b, hJ ε (w a) (w b) = if a = b then 1 else 0
  ew : ∀ c a, hJ ε (e c) (w a) = 0
  fw : ∀ c a, hJ ε (f c) (w a) = 0
  zw : ∀ a, hJ ε z (w a) = 0

namespace LocFrame

variable {n r k : ℕ} {ε : Fin n → Bool} (L : LocFrame n r k ε)

lemma fe (b a : Fin r) : hJ ε (L.f b) (L.e a) = if a = b then 1 else 0 := by
  rw [hJ_conj, L.ef]
  split_ifs <;> simp

lemma we (c : Fin k) (a : Fin r) : hJ ε (L.w c) (L.e a) = 0 := by
  rw [hJ_conj, L.ew, star_zero]

lemma wf (c : Fin k) (a : Fin r) : hJ ε (L.w c) (L.f a) = 0 := by
  rw [hJ_conj, L.fw, star_zero]

lemma wz (c : Fin k) : hJ ε (L.w c) L.z = 0 := by
  rw [hJ_conj, L.zw, star_zero]

lemma ze (a : Fin r) : hJ ε L.z (L.e a) = 0 := by
  rw [hJ_conj, L.ez, star_zero]

lemma zf (a : Fin r) : hJ ε L.z (L.f a) = 0 := by
  rw [hJ_conj, L.fz, star_zero]

def fam : (Fin r ⊕ Fin r) ⊕ (Unit ⊕ Fin k) → Fin n → ℂ :=
  Sum.elim (Sum.elim L.e L.f) (Sum.elim (fun _ => L.z) L.w)

lemma pair (x : Fin n → ℂ) (g : (Fin r ⊕ Fin r) ⊕ (Unit ⊕ Fin k) → ℂ) :
    hJ ε x (∑ i, g i • L.fam i) =
      (∑ a, g (.inl (.inl a)) * hJ ε x (L.e a)) + (∑ a, g (.inl (.inr a)) * hJ ε x (L.f a)) +
        (g (.inr (.inl ())) * hJ ε x L.z + ∑ c, g (.inr (.inr c)) * hJ ε x (L.w c)) := by
  rw [hJ_sum_right]
  simp only [Fintype.sum_sum_type, fam, Sum.elim_inl, Sum.elim_inr, Fintype.sum_unique]
  all_goals rfl

lemma fam_li : LinearIndependent ℂ L.fam := by
  rw [Fintype.linearIndependent_iff]
  intro g hg
  have key : ∀ x, (∑ a, g (.inl (.inl a)) * hJ ε x (L.e a)) + (∑ a, g (.inl (.inr a)) * hJ ε x (L.f a)) +
      (g (.inr (.inl ())) * hJ ε x L.z + ∑ c, g (.inr (.inr c)) * hJ ε x (L.w c)) = 0 := fun x => by
    rw [← L.pair x g, hg, hJ_zero_right]
  have hf : ∀ b, g (.inl (.inr b)) = 0 := fun b => by
    have := key (L.e b)
    simpa [L.ee, L.ef, L.ez, L.ew] using this
  have hz : g (.inr (.inl ())) = 0 := by
    have := key L.z
    have h2 : g (.inr (.inl ())) * hJ ε L.z L.z = 0 := by simpa [L.ze, L.zf, L.zw] using this
    exact (mul_eq_zero.mp h2).resolve_right L.zz
  have hw : ∀ c, g (.inr (.inr c)) = 0 := fun c => by
    have := key (L.w c)
    simpa [L.we, L.wf, L.wz, L.ww] using this
  have he : ∀ b, g (.inl (.inl b)) = 0 := fun b => by
    have := key (L.f b)
    simpa [L.fe, hf, hz, hw] using this
  rintro ((a | a) | (⟨⟩ | c))
  · exact he a
  · exact hf a
  · exact hz
  · exact hw c

lemma fam_span : Submodule.span ℂ (Set.range L.fam) = ⊤ := by
  apply L.fam_li.span_eq_top_of_card_eq_finrank
  simp only [Fintype.card_sum, Fintype.card_fin, Fintype.card_unit, Module.finrank_fin_fun]
  rw [L.hn]
  ring

lemma orth_zero (y : Fin n → ℂ) (he : ∀ a, hJ ε (L.e a) y = 0) (hf : ∀ a, hJ ε (L.f a) y = 0)
    (hz : hJ ε L.z y = 0) (hw : ∀ c, hJ ε (L.w c) y = 0) : y = 0 := by
  apply hJ_nondeg_right ε y
  intro x
  have hx : x ∈ Submodule.span ℂ (Set.range L.fam) := by
    rw [L.fam_span]
    trivial
  apply hJ_span_left ε hx
  rintro _ ⟨((a | a) | (⟨⟩ | c)), rfl⟩
  · exact he a
  · exact hf a
  · exact hz
  · exact hw c

lemma decomp (y : Fin n → ℂ) (he : ∀ a, hJ ε (L.e a) y = 0) (hz : hJ ε L.z y = 0) :
    y = ∑ c, hJ ε (L.w c) y • L.w c + ∑ a, hJ ε (L.f a) y • L.e a := by
  suffices h : y - (∑ c, hJ ε (L.w c) y • L.w c + ∑ a, hJ ε (L.f a) y • L.e a) = 0 from
    sub_eq_zero.mp h
  apply L.orth_zero
  · intro b
    rw [hJ_sub_right, he b, hJ_add_right, hJ_sum_right, hJ_sum_right]
    simp [L.ew, L.ee]
  · intro b
    rw [hJ_sub_right, hJ_add_right, hJ_sum_right, hJ_sum_right]
    simp [L.fw, L.fe]
  · rw [hJ_sub_right, hz, hJ_add_right, hJ_sum_right, hJ_sum_right]
    simp [L.zw, L.ze]
  · intro d
    rw [hJ_sub_right, hJ_add_right, hJ_sum_right, hJ_sum_right]
    simp [L.ww, L.we]

abbrev X : Submodule ℂ (Fin n → ℂ) := spanLt L.e r

lemma e_mem (a : Fin r) : L.e a ∈ L.X :=
  Submodule.subset_span ⟨a, a.isLt, rfl⟩

lemma spanLt_le (a : ℕ) (ha : a ≤ r) : spanLt L.e a ≤ L.X :=
  Submodule.span_mono (Set.image_mono fun b _ => b.isLt)

lemma sum_mem_X (c : Fin r → ℂ) : ∑ a, c a • L.e a ∈ L.X :=
  Submodule.sum_mem _ fun a _ => Submodule.smul_mem _ _ (L.e_mem a)

lemma hJ_X_left {x y : Fin n → ℂ} (hx : x ∈ L.X) (h : ∀ a, hJ ε (L.e a) y = 0) : hJ ε x y = 0 :=
  hJ_span_left ε (S := L.e '' {b | b.1 < r}) hx (by rintro _ ⟨a, _, rfl⟩; exact h a)

lemma hJ_X_right {x y : Fin n → ℂ} (hx : x ∈ L.X) (h : ∀ a, hJ ε y (L.e a) = 0) : hJ ε y x = 0 :=
  hJ_span_right ε (S := L.e '' {b | b.1 < r}) hx (by rintro _ ⟨a, _, rfl⟩; exact h a)

section Grp

variable {g : Matrix (Fin n) (Fin n) ℂ} (hg : Formalism.REAL.inUJ ε g) (hS : InS L.e L.z g)
include hg hS

omit hg in
lemma gX {x : Fin n → ℂ} (hx : x ∈ L.X) : g *ᵥ x ∈ L.X := by
  have key : ∀ a : Fin r, g *ᵥ L.e a ∈ L.X := fun a => by
    have h1 : g *ᵥ L.e a = L.e a + (g - 1) *ᵥ L.e a := by
      rw [Matrix.sub_mulVec, Matrix.one_mulVec]
      abel
    rw [h1]
    exact L.X.add_mem (L.e_mem a) (L.spanLt_le a.1 a.isLt.le (hS.1 a))
  have hx' : x ∈ Submodule.span ℂ (L.e '' {b | b.1 < r}) := hx
  clear hx
  induction hx' using Submodule.span_induction with
  | mem v hv =>
    obtain ⟨a, _, rfl⟩ := hv
    exact key a
  | zero =>
    rw [Matrix.mulVec_zero]
    exact L.X.zero_mem
  | add u v _ _ hu hv =>
    rw [Matrix.mulVec_add]
    exact L.X.add_mem hu hv
  | smul c u _ hu =>
    rw [Matrix.mulVec_smul]
    exact L.X.smul_mem c hu

omit hS in
lemma g_inj {x : Fin n → ℂ} (hx : g *ᵥ x = 0) : x = 0 :=
  hJ_nondeg_right ε x fun x' => by rw [← hJ_unitary ε hg x' x, hx, hJ_zero_right]

lemma g_surj {x : Fin n → ℂ} (hx : x ∈ L.X) : ∃ x' ∈ L.X, g *ᵥ x' = x := by
  let f : L.X →ₗ[ℂ] L.X := (Matrix.mulVecLin g).restrict (fun v hv => L.gX hS hv)
  have hinj : Function.Injective f := by
    intro u v huv
    have h1 : g *ᵥ ((u : Fin n → ℂ) - v) = 0 := by
      rw [Matrix.mulVec_sub, sub_eq_zero]
      exact congrArg Subtype.val huv
    exact Subtype.ext (sub_eq_zero.mp (g_inj hg h1))
  obtain ⟨v, hv⟩ := (LinearMap.injective_iff_surjective.mp hinj) ⟨x, hx⟩
  exact ⟨v, v.2, congrArg Subtype.val hv⟩

lemma g_perp {y : Fin n → ℂ} (hy : ∀ a, hJ ε (L.e a) y = 0) (a : Fin r) : hJ ε (L.e a) (g *ᵥ y) = 0 := by
  obtain ⟨x', hx', hgx⟩ := L.g_surj hg hS (L.e_mem a)
  rw [← hgx, hJ_unitary ε hg]
  exact L.hJ_X_left hx' hy

lemma local_frame_preserves_orthogonal {y : Fin n → ℂ} (hy : ∀ a, hJ ε (L.e a) y = 0) (hz : hJ ε L.z y = 0) :
    hJ ε L.z (g *ᵥ y) = 0 := by
  have h1 : g *ᵥ L.z = L.z + (g - 1) *ᵥ L.z := by
    rw [Matrix.sub_mulVec, Matrix.one_mulVec]
    abel
  have h2 : hJ ε (g *ᵥ L.z) (g *ᵥ y) = 0 := by rw [hJ_unitary ε hg, hz]
  rw [h1, hJ_add_left, L.hJ_X_left hS.2 (L.g_perp hg hS hy), add_zero] at h2
  exact h2

end Grp

def M (g : Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin k) (Fin k) ℂ :=
  fun a b => hJ ε (L.w a) (g *ᵥ L.w b)

lemma gw_decomp {g : Matrix (Fin n) (Fin n) ℂ} (hg : Formalism.REAL.inUJ ε g) (hS : InS L.e L.z g) (b : Fin k) :
    g *ᵥ L.w b = ∑ c, L.M g c b • L.w c + ∑ a, hJ ε (L.f a) (g *ᵥ L.w b) • L.e a :=
  L.decomp _ (L.g_perp hg hS fun a => L.ew a b) (L.local_frame_preserves_orthogonal hg hS (fun a => L.ew a b) (L.zw b))

private lemma mulVec_sum_lemma {ι : Type*} (s : Finset ι) (g : Matrix (Fin n) (Fin n) ℂ) (c : ι → ℂ)
    (u : ι → Fin n → ℂ) : g *ᵥ (∑ i ∈ s, c i • u i) = ∑ i ∈ s, c i • (g *ᵥ u i) := by
  classical
  refine Finset.induction_on s (by simp) ?_
  intro a s ha ih
  rw [Finset.sum_insert ha, Finset.sum_insert ha, Matrix.mulVec_add, Matrix.mulVec_smul, ih]

lemma M_mul {g g' : Matrix (Fin n) (Fin n) ℂ} (hg : Formalism.REAL.inUJ ε g) (hS : InS L.e L.z g)
    (hg' : Formalism.REAL.inUJ ε g') (hS' : InS L.e L.z g') : L.M (g * g') = L.M g * L.M g' := by
  ext c b
  have hXr : ∀ a, hJ ε (L.w c) (g *ᵥ L.e a) = 0 := fun a =>
    L.hJ_X_right (L.gX hS (L.e_mem a)) (fun a' => L.we c a')
  have e1 : L.M (g * g') c b = hJ ε (L.w c) (g *ᵥ (g' *ᵥ L.w b)) := by
    show hJ ε (L.w c) ((g * g') *ᵥ L.w b) = _
    rw [Matrix.mulVec_mulVec]
  rw [e1, L.gw_decomp hg' hS' b, Matrix.mulVec_add, hJ_add_right, mulVec_sum_lemma, mulVec_sum_lemma,
    hJ_sum_right, hJ_sum_right]
  simp only [hXr, mul_zero, Finset.sum_const_zero, add_zero, Matrix.mul_apply]
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [mul_comm]
  rfl

private lemma hJ_sum_left_lemma_2 {ι : Type*} (s : Finset ι) (y : Fin n → ℂ) (c : ι → ℂ)
    (u : ι → Fin n → ℂ) : hJ ε (∑ i ∈ s, c i • u i) y = ∑ i ∈ s, star (c i) * hJ ε (u i) y := by
  classical
  refine Finset.induction_on s (by simp [hJ_zero_left]) ?_
  intro a s ha ih
  rw [Finset.sum_insert ha, Finset.sum_insert ha, hJ_add_left, hJ_smul_left, ih]

lemma M_unitary {g : Matrix (Fin n) (Fin n) ℂ} (hg : Formalism.REAL.inUJ ε g) (hS : InS L.e L.z g) :
    (L.M g)ᴴ * L.M g = 1 := by
  ext a b
  have h1 : hJ ε (g *ᵥ L.w a) (g *ᵥ L.w b) = if a = b then 1 else 0 := by
    rw [hJ_unitary ε hg, L.ww]
  rw [L.gw_decomp hg hS a, hJ_add_left, hJ_sum_left_lemma_2, hJ_sum_left_lemma_2] at h1
  simp only [L.g_perp hg hS (fun a' => L.ew a' b), mul_zero, Finset.sum_const_zero, add_zero] at h1
  rw [Matrix.mul_apply, Matrix.one_apply, ← h1]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [Matrix.conjTranspose_apply]
  rfl

lemma M_N {g : Matrix (Fin n) (Fin n) ℂ} (hN : InN ε L.e L.z g) : L.M g = 1 := by
  ext c b
  have hx := hN.2 (L.w b) (fun a => L.ew a b)
  have h1 : g *ᵥ L.w b = L.w b + (g - 1) *ᵥ L.w b := by
    rw [Matrix.sub_mulVec, Matrix.one_mulVec]
    abel
  show hJ ε (L.w c) (g *ᵥ L.w b) = (1 : Matrix (Fin k) (Fin k) ℂ) c b
  rw [h1, hJ_add_right, L.ww, L.hJ_X_right hx (fun a => L.we c a), add_zero, Matrix.one_apply]

lemma M_one : L.M 1 = 1 := by
  ext a b
  show hJ ε (L.w a) ((1 : Matrix (Fin n) (Fin n) ℂ) *ᵥ L.w b) = (1 : Matrix (Fin k) (Fin k) ℂ) a b
  rw [Matrix.one_mulVec, L.ww, Matrix.one_apply]

lemma M_inUJ {g : Matrix (Fin n) (Fin n) ℂ} (hg : Formalism.REAL.inUJ ε g) (hS : InS L.e L.z g) :
    L.M g ∈ PI.UpqRep.UJset (PI.UpqRep.allPos k) := by
  have hJ1 : PI.UpqRep.Jm (PI.UpqRep.allPos k) = 1 := by
    ext a b
    simp [PI.UpqRep.Jm, PI.UpqRep.allPos, Matrix.diagonal_apply, Matrix.one_apply]
  show (L.M g)ᴴ * PI.UpqRep.Jm (PI.UpqRep.allPos k) * L.M g = PI.UpqRep.Jm (PI.UpqRep.allPos k)
  rw [hJ1, Matrix.mul_one, L.M_unitary hg hS]

end LocFrame

end PI.ScPiBuildW.Loc
