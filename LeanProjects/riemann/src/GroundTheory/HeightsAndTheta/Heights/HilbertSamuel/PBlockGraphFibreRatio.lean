import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsBlockGraphFibreRatio
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4

namespace BlockGraphFibreRatio

set_option linter.unusedSectionVars false

section Cone

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem eval_mConeMap {Ω : Type} [Field Ω] (v : (Σ k, ι k) → Ω) (s : K → Ω) (f : MRing ι) :
    eval s (mConeMap v f) = aeval (fun p => s p.1 * v p) f := by
  induction f using MvPolynomial.induction_on with
  | C a => simp [mConeMap]
  | add f g hf hg => rw [map_add, map_add, map_add, hf, hg]
  | mul_X f p hf =>
    rw [map_mul, map_mul, map_mul, hf]
    simp [mConeMap, mul_comm]

theorem aeval_smul_of_isMultiHomog {Ω : Type} [Field Ω] (v : (Σ k, ι k) → Ω) (s : K → Ω) {f : MRing ι}
    {d : K → ℕ} (hf : IsMultiHomog f d) :
    aeval (fun p => s p.1 * v p) f = (∏ k, s k ^ d k) * aeval v f := by
  rw [← eval_mConeMap, ProjLine.mConeMap_eq_of_isMultiHomog v hf, map_mul, eval_C, map_prod]
  simp only [map_pow, eval_X]
  ring

theorem aeval_eq_zero_of_mem {Ω : Type} [Field Ω] {v : (Σ k, ι k) → Ω} {f : MRing ι}
    (hf : f ∈ mCoordIdeal v) : aeval v f = 0 := by
  have h := eval_mConeMap v (fun _ => 1) f
  rw [show mConeMap v f = 0 from hf] at h
  simpa using h.symm

theorem isMultiHomog_X [DecidableEq K] (k : K) (i : ι k) :
    IsMultiHomog (X ⟨k, i⟩ : MRing ι) (blockDeg k 1) := by
  classical
  intro m hm k'
  rw [support_X, Finset.mem_singleton] at hm
  subst hm
  by_cases hk : k' = k
  · subst hk
    have hs : ∀ b, (Finsupp.single (⟨k', i⟩ : Σ k, ι k) 1 : (Σ k, ι k) →₀ ℕ) ⟨k', b⟩ = if b = i then 1 else 0 := by
      intro b
      by_cases hb : b = i
      · subst hb
        simp
      · rw [if_neg hb, Finsupp.single_apply, if_neg]
        intro h
        exact hb (eq_of_heq (Sigma.mk.inj h).2).symm
    simp [blockDeg, hs]
  · simp [blockDeg, hk, Sigma.ext_iff]

end Cone

section Graph

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
  {K₂ : Type} [Fintype K₂] {ι₂ : K₂ → Type} [∀ k, Fintype (ι₂ k)]

theorem graphMap_rename_inlV (P : Ideal (MRing ι)) (g : (Σ k, ι₂ k) → MRing ι) (f : MRing ι) :
    graphMap P g (rename (inlV (ι₂ := ι₂)) f) = C (Ideal.Quotient.mk P f) := by
  induction f using MvPolynomial.induction_on with
  | C a => simp [graphMap]
  | add f f' hf hf' => rw [map_add, map_add, hf, hf', map_add, map_add]
  | mul_X f p hf =>
    rw [map_mul, map_mul, hf, rename_X, map_mul, map_mul]
    congr 1
    rw [graphMap, eval₂Hom_X']
    rfl

theorem mem_iff_aeval_inl {P : Ideal (MRing ι)} {g : (Σ k, ι₂ k) → MRing ι}
    (G : GenFibre (inrV (ι := ι) (ι₂ := ι₂)) (graphIdeal P g)) (f : MRing ι) :
    f ∈ P ↔ aeval (fun p => G.x' (inlV p)) f = 0 := by
  have h : aeval (fun p => G.x' (inlV p)) f = aeval G.x' (rename inlV f) := by
    rw [aeval_rename]
    rfl
  rw [h, ← RingHom.mem_ker, G.genericFibre_ker_target, graphIdeal, RingHom.mem_ker, graphMap_rename_inlV, C_eq_zero,
    Ideal.Quotient.eq_zero_iff_mem]

end Graph

section Block

variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)] {κ : Type} [Fintype κ]

theorem sub_mem_mCoordIdeal {Ω : Type} [Field Ω] {y : (Σ k, ι k) → Ω} {k₀ : K} {M : Matrix (Ix κ) (ι k₀) ℤ}
    {N : Matrix (ι k₀) (Ix κ) ℤ} {x : Ix κ → Ω} (h : IsBlockImage y k₀ M N x) (i : ι k₀) :
    X ⟨k₀, i⟩ - ∑ j, C (N i j) * blockForms k₀ M j ∈ mCoordIdeal y := by
  have hf : ∀ j, mConeMap y (blockForms k₀ M j) = MvPolynomial.C (x j) * MvPolynomial.X k₀ := by
    intro j
    rw [h.1 j, map_sum, Finset.sum_mul]
    simp [blockForms, mConeMap, map_sum, mul_assoc]
  have hX : mConeMap y (X ⟨k₀, i⟩) = MvPolynomial.C (y ⟨k₀, i⟩) * MvPolynomial.X k₀ := by
    simp [mConeMap]
  rw [mCoordIdeal, RingHom.mem_ker, map_sub, map_sum]
  simp only [map_mul, hf]
  rw [hX, h.2 i, map_sum, Finset.sum_mul, sub_eq_zero]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp [mConeMap, mul_assoc]

def nForm (k₀ : K) (N : Matrix (ι k₀) (Ix κ) ℤ) (l : ι k₀) : MRing (Sum.elim ι (GlobalTheory κ)) :=
  ∑ q : Ix κ, C (N l q) * X (inrV q)

theorem graphMap_nForm {Ω : Type} [Field Ω] {y : (Σ k, ι k) → Ω} {k₀ : K} {M : Matrix (Ix κ) (ι k₀) ℤ}
    {N : Matrix (ι k₀) (Ix κ) ℤ} {x : Ix κ → Ω} (h : IsBlockImage y k₀ M N x) (l : ι k₀) :
    graphMap (mCoordIdeal y) (blockForms k₀ M) (nForm k₀ N l) =
      C (Ideal.Quotient.mk (mCoordIdeal y) (X ⟨k₀, l⟩)) * X () := by
  rw [Ideal.Quotient.eq.2 (sub_mem_mCoordIdeal h l), nForm, map_sum, map_sum, map_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun q _ => ?_
  obtain ⟨⟨⟩, j⟩ := q
  rw [map_mul, graphMap, eval₂Hom_C, eval₂Hom_X']
  change (Int.castRingHom _) (N l ⟨(), j⟩) * (C (Ideal.Quotient.mk (mCoordIdeal y) (blockForms k₀ M ⟨(), j⟩)) * X ()) = _
  simp [mul_assoc]

end Block

end BlockGraphFibreRatio

open BlockGraphFibreRatio in

theorem BlockGraphFibreRatio.proof : BlockGraphFibreRatio.Statement := by
  intro D K _ _ ι _ Ω _ _ κ _ y k₀ M N x hy hB hI G k i j hj
  classical
  set z : (Σ k, ι k) → G.Φ' := fun p => G.x' (inlV p) with hzdef
  have hmem := mem_iff_aeval_inl G
  rw [← hzdef] at hmem
  change z ⟨k, j⟩ ≠ 0 at hj
  change z ⟨k, i⟩ / z ⟨k, j⟩ ∈ _

  have hyj : aeval y (X ⟨k, j⟩ : MRing ι) ≠ 0 := by
    intro h0
    refine hj ?_
    have h1 : (X ⟨k, j⟩ : MRing ι) ∈ mCoordIdeal y := by
      show mConeMap y _ = 0
      rw [ProjLine.mConeMap_eq_of_isMultiHomog y (isMultiHomog_X k j), h0, map_zero, zero_mul]
    simpa using (hmem _).1 h1

  obtain ⟨n, g', h', hg', hh', hh0, hgh⟩ :=
    hB (blockDeg k 1) (X ⟨k, i⟩) (X ⟨k, j⟩) (isMultiHomog_X k i) (isMultiHomog_X k j) hyj
  have hF : (X ⟨k, i⟩ * h' - g' * X ⟨k, j⟩ : MRing ι) ∈ mCoordIdeal y := by
    show mConeMap y _ = 0
    rw [map_sub, map_mul, map_mul, ProjLine.mConeMap_eq_of_isMultiHomog y hh',
      ProjLine.mConeMap_eq_of_isMultiHomog y hg', ProjLine.mConeMap_eq_of_isMultiHomog y (isMultiHomog_X k i),
      ProjLine.mConeMap_eq_of_isMultiHomog y (isMultiHomog_X k j)]
    calc _ = C (aeval y (X ⟨k, i⟩ : MRing ι) * aeval y h' - aeval y g' * aeval y (X ⟨k, j⟩ : MRing ι)) *
          ((∏ k', X k' ^ blockDeg k 1 k') * ∏ k', X k' ^ blockDeg k₀ n k') := by
          rw [map_sub, map_mul, map_mul]
          ring
      _ = 0 := by rw [hgh, sub_self, map_zero, zero_mul]
  have hz := (hmem _).1 hF
  simp only [map_sub, map_mul, aeval_X] at hz
  have hh'z : aeval z h' ≠ 0 := fun h0 => hh0 (aeval_eq_zero_of_mem ((hmem h').2 h0))
  have hratio : z ⟨k, i⟩ / z ⟨k, j⟩ = aeval z g' / aeval z h' := by
    rw [div_eq_div_iff hj hh'z]
    linear_combination hz

  obtain ⟨l, hl⟩ := hy.2.1.2.2 k₀
  have hzl : z ⟨k₀, l⟩ ≠ 0 := fun h0 => hl ((hmem _).2 (by simpa using h0))
  have hw : ∀ a, aeval G.x' (nForm k₀ N a) = algebraMap G.Φ G.Φ' (∑ q, (N a q : G.Φ) * G.x q) := by
    intro a
    simp [nForm, G.compat]
  have hker : ∀ f, aeval G.x' f = 0 ↔ graphMap (mCoordIdeal y) (blockForms k₀ M) f = 0 := by
    intro f
    rw [← RingHom.mem_ker, G.genericFibre_ker_target, graphIdeal, RingHom.mem_ker]
  have hwl : aeval G.x' (nForm k₀ N l) ≠ 0 := by
    intro h0
    rw [hker, graphMap_nForm hI] at h0
    have h1 := congrArg (MvPolynomial.coeff (Finsupp.single () 1)) h0
    rw [coeff_C_mul, coeff_X, if_pos rfl, mul_one, coeff_zero, Ideal.Quotient.eq_zero_iff_mem] at h1
    exact hl h1
  have hcross : ∀ a, aeval G.x' (nForm k₀ N a) * z ⟨k₀, l⟩ = z ⟨k₀, a⟩ * aeval G.x' (nForm k₀ N l) := by
    intro a
    have hX : ∀ p : Σ k, ι k, graphMap (mCoordIdeal y) (blockForms k₀ M) (X (inlV p)) =
        C (Ideal.Quotient.mk (mCoordIdeal y) (X p)) := fun p => by
      rw [← rename_X, graphMap_rename_inlV]
    have h0 := (hker (nForm k₀ N a * X (inlV ⟨k₀, l⟩) - X (inlV ⟨k₀, a⟩) * nForm k₀ N l)).2 (by
      rw [map_sub, map_mul, map_mul, graphMap_nForm hI, graphMap_nForm hI, hX, hX]
      ring)
    rw [map_sub, map_mul, map_mul, aeval_X, aeval_X, sub_eq_zero] at h0
    exact h0
  set c := aeval G.x' (nForm k₀ N l) / z ⟨k₀, l⟩ with hcdef
  have hc : c ≠ 0 := div_ne_zero hwl hzl
  have hwc : ∀ a, aeval G.x' (nForm k₀ N a) = c * z ⟨k₀, a⟩ := by
    intro a
    rw [hcdef, div_mul_eq_mul_div, eq_div_iff hzl, hcross a, mul_comm]

  let s : K → G.Φ' := fun k' => if k' = k₀ then c else 0
  have hs : ∀ f : MRing ι, IsMultiHomog f (blockDeg k₀ n) →
      aeval (fun p => s p.1 * z p) f = c ^ n * aeval z f := by
    intro f hf
    rw [aeval_smul_of_isMultiHomog z s hf, Finset.prod_eq_single k₀]
    · simp [s, blockDeg]
    · intro b _ hb
      simp [s, blockDeg, hb]
    · simp
  have hex : ∀ p : Σ k, ι k, ∃ a : G.Φ, algebraMap G.Φ G.Φ' a = s p.1 * z p := by
    rintro ⟨k', a⟩
    by_cases hk : k' = k₀
    · subst hk
      exact ⟨_, ((hw a).symm.trans (hwc a)).trans (by simp [s])⟩
    · exact ⟨0, by simp [s, hk]⟩
  choose u hu using hex
  have hmap : ∀ f : MRing ι, aeval (fun p => s p.1 * z p) f = algebraMap G.Φ G.Φ' (aeval u f) := by
    intro f
    have hfun : (fun p => s p.1 * z p) = algebraMap G.Φ G.Φ' ∘ u := funext fun p => (hu p).symm
    rw [hfun, aeval_algebraMap_apply]
  refine RingHom.mem_range.2 ⟨aeval u g' / aeval u h', ?_⟩
  rw [map_div₀, ← hmap, ← hmap, hs g' hg', hs h' hh', hratio, mul_div_mul_left _ _ (pow_ne_zero n hc)]

end GroundTheory.Heights₂.Heights.HilbertSamuel

end
