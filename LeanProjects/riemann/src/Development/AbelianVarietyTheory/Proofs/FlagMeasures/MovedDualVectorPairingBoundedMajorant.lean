import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.IsNormalFormStabilizerMeasure
import Formalism.FormalDegreeBessel.FinalG
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.NormLeadingMinorMonomial
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.NormDetInnerLeOfDetEqOne
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.GramSchmidtLengths
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MajorantFlagLengthsInvarianceTorusPositivity
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsotropicLeviEmbeddingHomomorphismProperties
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsotropicStabilizerRadicalStructure

noncomputable section

open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.Amp.NfComp

lemma herm_iso {n : ℕ} {H g : Matrix (Fin n) (Fin n) ℂ} (hg : g ∈ UH H) (v w : Fin n → ℂ) :
    herm H (g *ᵥ v) (g *ᵥ w) = herm H v w := by
  have h : gᴴ * H * g = H := hg
  unfold herm
  rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, h]

lemma Hunit (k r : ℕ) : IsUnit (Hpk k r).det := by
  have := (hpkFacts k r).2.1
  exact Matrix.isUnit_det_of_left_inverse this

lemma G_unit {k r : ℕ} {g : Mat k r} (hg : g ∈ GG k r) : IsUnit g.det :=
  ((uHGroup _ _ (Hunit k r)).2.2 g hg).1

lemma G_inv {k r : ℕ} {g : Mat k r} (hg : g ∈ GG k r) : g⁻¹ ∈ GG k r :=
  ((uHGroup _ _ (Hunit k r)).2.2 g hg).2

lemma G_mul {k r : ℕ} {g h : Mat k r} (hg : g ∈ GG k r) (hh : h ∈ GG k r) : g * h ∈ GG k r :=
  (uHGroup _ _ (Hunit k r)).2.1 g hg h hh

lemma herm_inv_left {k r : ℕ} {g : Mat k r} (hg : g ∈ GG k r) (v w : Fin (2 * r + k + 1) → ℂ) :
    herm (Hpk k r) (g⁻¹ *ᵥ v) w = herm (Hpk k r) v (g *ᵥ w) := by
  rw [← herm_iso hg, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ (G_unit hg), Matrix.one_mulVec]

lemma herm_symm (k r : ℕ) (v w : Fin (2 * r + k + 1) → ℂ) :
    herm (Hpk k r) v w = star (herm (Hpk k r) w v) := by
  unfold herm
  rw [Matrix.star_dotProduct, Matrix.star_mulVec, (hpkFacts k r).1, ← Matrix.dotProduct_mulVec]

lemma herm_e (k r : ℕ) (v : Fin (2 * r + k + 1) → ℂ) (a : Fin r) :
    herm (Hpk k r) v (bvec (eI k r a)) = v (esI k r a) := by
  unfold herm bvec
  have : star (Pi.single (eI k r a) (1 : ℂ) : Fin (2 * r + k + 1) → ℂ) = Pi.single (eI k r a) 1 := by
    rw [Pi.star_single]; simp
  rw [this, single_dotProduct, one_mul, Matrix.mulVec, dotProduct, Finset.sum_eq_single (esI k r a)]
  · have := a.2
    have h : Hpk k r (eI k r a) (esI k r a) = 1 := by
      unfold Hpk eI esI
      rw [if_pos]; constructor <;> simp; omega
    rw [h, one_mul]
  · intro i _ hi
    have := a.2
    have hi' : i.val ≠ 2 * r + k - a.val := fun h => hi (Fin.ext h)
    have h : Hpk k r (eI k r a) i = 0 := by
      unfold Hpk eI
      rw [if_neg, if_neg, if_neg] <;> simp <;> omega
    rw [h, zero_mul]
  · simp

lemma herm_es (k r : ℕ) (v : Fin (2 * r + k + 1) → ℂ) (a : Fin r) :
    herm (Hpk k r) v (bvec (esI k r a)) = v (eI k r a) := by
  unfold herm bvec
  have : star (Pi.single (esI k r a) (1 : ℂ) : Fin (2 * r + k + 1) → ℂ) = Pi.single (esI k r a) 1 := by
    rw [Pi.star_single]; simp
  rw [this, single_dotProduct, one_mul, Matrix.mulVec, dotProduct, Finset.sum_eq_single (eI k r a)]
  · have := a.2
    have h : Hpk k r (esI k r a) (eI k r a) = 1 := by
      unfold Hpk eI esI
      rw [if_neg, if_pos] <;> simp <;> omega
    rw [h, one_mul]
  · intro i _ hi
    have := a.2
    have hi' : i.val ≠ a.val := fun h => hi (Fin.ext h)
    have h : Hpk k r (esI k r a) i = 0 := by
      unfold Hpk esI
      rw [if_neg, if_neg, if_neg] <;> simp <;> omega
    rw [h, zero_mul]
  · simp

lemma herm_smul_left {n : ℕ} (H : Matrix (Fin n) (Fin n) ℂ) (c : ℂ) (v w : Fin n → ℂ) :
    herm H (c • v) w = c * herm H v w := by
  simp [herm, Matrix.mulVec_smul]

lemma eucl_eq {n : ℕ} (v : Fin n → ℂ) : eucl v = ‖(WithLp.toLp 2 v : EuclideanSpace ℂ (Fin n))‖ := by
  rw [EuclideanSpace.norm_eq]; unfold eucl
  simp [Complex.normSq_eq_norm_sq]

lemma inner_toLp {n : ℕ} (v w : Fin n → ℂ) :
    ⟪(WithLp.toLp 2 v : EuclideanSpace ℂ (Fin n)), WithLp.toLp 2 w⟫_ℂ = star v ⬝ᵥ w := by
  rw [EuclideanSpace.inner_toLp_toLp, dotProduct_comm]

lemma inner_H (k r : ℕ) (v w : Fin (2 * r + k + 1) → ℂ) :
    ⟪(WithLp.toLp 2 (Hpk k r *ᵥ w) : EuclideanSpace ℂ (Fin (2 * r + k + 1))), WithLp.toLp 2 v⟫_ℂ =
      herm (Hpk k r) v w := by
  rw [inner_toLp, Matrix.star_mulVec, (hpkFacts k r).1, ← Matrix.dotProduct_mulVec]; rfl

lemma norm_H (k r : ℕ) (w : Fin (2 * r + k + 1) → ℂ) :
    ‖(WithLp.toLp 2 (Hpk k r *ᵥ w) : EuclideanSpace ℂ (Fin (2 * r + k + 1)))‖ = eucl w := by
  rw [eucl_eq, norm_eq_sqrt_re_inner (𝕜 := ℂ), norm_eq_sqrt_re_inner (𝕜 := ℂ), inner_H, inner_toLp]
  unfold herm
  rw [Matrix.mulVec_mulVec, (hpkFacts k r).2.1, Matrix.one_mulVec]

lemma mEmb_e (k r : ℕ) (m : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) (a : Fin r) :
    mEmb k r m *ᵥ bvec (eI k r a) = bvec (eI k r a) := by
  have := a.2
  funext i
  unfold bvec
  rw [Matrix.mulVec_single_one]
  simp only [Matrix.col_apply, mEmb]
  rw [dif_neg (by simp [eI]), Pi.single_apply]

lemma esI_inj (k r : ℕ) : Function.Injective (esI k r) := by
  intro a b h
  have := a.2; have := b.2
  have := congrArg Fin.val h
  simp only [esI] at this
  exact Fin.ext (by omega)

lemma XstJ_eq {k r j : ℕ} {v : Fin (2 * r + k + 1) → ℂ} (hv : v ∈ XstJ k r j) (i : Fin (2 * r + k + 1))
    (hi : ∀ c : Fin r, c.val < j → i ≠ esI k r c) : v i = 0 := by
  unfold XstJ at hv
  induction hv using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨c, rfl⟩ := hx
    exact Pi.single_eq_of_ne (hi c.1 c.2) _
  | zero => rfl
  | add x y _ _ hx hy => simp [hx, hy]
  | smul c x _ hx => simp [hx]

lemma pluck_flag {k r n : ℕ} (hn : n ≤ r) (z : Fin (2 * r + k + 1) → ℂ) (hz : inWb k r z) (x : Mat k r)
    (hx : x ∈ GG k r) (R : ℝ) (hR : Sg k r z x ≤ R) (y : Fin n → Fin (2 * r + k + 1) → ℂ)
    (hy : ∀ a, eucl (y a) ≤ R) :
    ‖(Matrix.of fun a a' : Fin n =>
      herm (Hpk k r) (x⁻¹ *ᵥ bvec (eI k r (Fin.castLE hn a'))) (y a)).det‖ ≤ R ^ n * R ^ n := by
  obtain ⟨uu, h1, h2⟩ := GlobalTheory.Amp.GramFlag.gramSchmidt_lengths k r z x hx
  have hsum : ∀ a : Fin n, ∑ i : Fin n, ((upper uu).submatrix (Fin.castLE hn) (Fin.castLE hn)) i a •
      (WithLp.toLp 2 (x⁻¹ *ᵥ bvec (eI k r (Fin.castLE hn i))) : EuclideanSpace ℂ (Fin (2 * r + k + 1))) =
      WithLp.toLp 2 (∑ b, upper uu b (Fin.castLE hn a) • (x⁻¹ *ᵥ bvec (eI k r b))) := by
    intro a
    rw [WithLp.toLp_sum]
    refine Fintype.sum_of_injective (Fin.castLE hn) (Fin.castLE_injective hn) _ _ ?_ ?_
    · intro b hb
      have hb' : n ≤ b.val := by
        by_contra h
        exact hb ⟨⟨b.val, by omega⟩, rfl⟩
      have ha := a.2
      have : upper uu b (Fin.castLE hn a) = 0 := by
        unfold upper
        rw [dif_neg, if_neg]
        · intro h; have := congrArg Fin.val h; simp at this; omega
        · rw [Fin.lt_def]; simp; omega
      simp [this]
    · intro i; simp
  have hdet : ((upper uu).submatrix (Fin.castLE hn) (Fin.castLE hn)).det = 1 := by
    rw [Matrix.det_of_upperTriangular]
    · simp [upper]
    · intro a b hab
      have hab' : b.val < a.val := hab
      simp only [Matrix.submatrix_apply, upper]
      rw [dif_neg, if_neg]
      · intro h; have := congrArg Fin.val h; simp at this; omega
      · rw [Fin.lt_def]; simp; omega
  have hp := GlobalTheory.PlueckerBound.norm_det_inner_le_of_det_eq_one _ n (fun i => WithLp.toLp 2 (x⁻¹ *ᵥ bvec (eI k r (Fin.castLE hn i))))
    (fun a => WithLp.toLp 2 (Hpk k r *ᵥ y a)) _ hdet (by
      intro a a' h
      rw [hsum, hsum, inner_toLp]
      exact h2 _ _ fun h' => h (Fin.castLE_injective hn h'))
  simp only [inner_H, hsum, norm_H] at hp
  simp only [← eucl_eq] at hp
  refine hp.trans (mul_le_mul ?_ ?_ ?_ ?_)
  · calc _ ≤ ∏ _a : Fin n, R := Finset.prod_le_prod (fun _ _ => Real.sqrt_nonneg _) fun a _ => hy a
      _ = _ := by simp
  · calc _ ≤ ∏ _a : Fin n, R := Finset.prod_le_prod (fun _ _ => Real.sqrt_nonneg _) fun a _ => by
          exact (h1 _).1.trans_le <| (((GlobalTheory.Amp.LInv.lengths_basic k r z hz).2.2 x).2.1 _).2.trans hR
      _ = _ := by simp
  · exact Finset.prod_nonneg fun _ _ => Real.sqrt_nonneg _
  · exact pow_nonneg (zero_le_one.trans (((GlobalTheory.Amp.LInv.lengths_basic k r z hz).2.2 x).1.trans hR)) _

lemma eI_inj (k r : ℕ) : Function.Injective (eI k r) := by
  intro a b h
  have := congrArg Fin.val h
  exact Fin.ext this

lemma inv_e {k r j : ℕ} (hj : j ≤ r) {g : Mat k r} (hg : g ∈ GG k r) (a b : Fin j)
    (hX : g⁻¹ *ᵥ bvec (eI k r (Fin.castLE hj a)) ∈ XstJ k r j)
    (hb : ∀ c : Fin j, Zr k r g (Fin.castLE hj a) (Fin.castLE hj c) ≠ 0 → c = b) :
    g⁻¹ *ᵥ bvec (eI k r (Fin.castLE hj a)) =
      star (Zr k r g (Fin.castLE hj a) (Fin.castLE hj b)) • bvec (esI k r (Fin.castLE hj b)) := by
  funext i
  by_cases hi : ∃ c : Fin j, i = esI k r (Fin.castLE hj c)
  · obtain ⟨c, rfl⟩ := hi
    have h1 : (g⁻¹ *ᵥ bvec (eI k r (Fin.castLE hj a))) (esI k r (Fin.castLE hj c)) =
        star (Zr k r g (Fin.castLE hj a) (Fin.castLE hj c)) := by
      rw [← herm_e k r (g⁻¹ *ᵥ _), herm_inv_left hg, herm_symm, herm_e]
      simp [bvec, Zr]
    rw [h1]
    by_cases hc : c = b
    · subst hc; simp [bvec]
    · have h0 : Zr k r g (Fin.castLE hj a) (Fin.castLE hj c) = 0 := by
        by_contra h; exact hc (hb c h)
      have : esI k r (Fin.castLE hj c) ≠ esI k r (Fin.castLE hj b) := fun h =>
        hc (Fin.castLE_injective hj (esI_inj k r h))
      simp [h0, bvec, Pi.single_eq_of_ne this]
  · push_neg at hi
    rw [XstJ_eq hX i fun c hc => hi ⟨c.val, hc⟩]
    simp [bvec, Pi.single_eq_of_ne (hi b)]

lemma sEl_mem (k r j : ℕ) (β : Fin r → ℕ) (q : PSec k r j × (UToff β → ℂ)) : sEl k r j β q ∈ Nset k r :=
  (nSubgroup k r).2.1 _ (((GlobalTheory.Amp.Rad.radical k r).1 _ _).2.2.2 ((GlobalTheory.Amp.Rad.radical k r).2.1 _ _)).1 _
    ((GlobalTheory.Amp.UEmb.uEmb_hom k r).2.2.2 _).2

lemma sEl_pair (k r j : ℕ) (β : Fin r → ℕ) (q : PSec k r j × (UToff β → ℂ)) (c c' : Fin r) :
    herm (Hpk k r) ((sEl k r j β q)⁻¹ *ᵥ bvec (esI k r c')) (bvec (eI k r c)) = star (upperOff β q.2 c' c) := by
  rw [herm_inv_left (sEl_mem k r j β q).1, herm_symm, herm_es]
  have hu : IsUnit (upperOff β q.2).det := by
    unfold upperOff; rw [((GlobalTheory.Amp.UEmb.uEmb_hom k r).2.2.2 _).1]; exact isUnit_one
  unfold sEl
  rw [← Matrix.mulVec_mulVec, ((GlobalTheory.Amp.UEmb.uEmb_hom k r).2.2.1 _ hu).2.2.1, Matrix.mulVec_sum]
  simp only [Matrix.mulVec_smul, pSec, pOf, ((GlobalTheory.Amp.Rad.radical k r).1 _ _).1]
  congr 1
  rw [Finset.sum_apply, Finset.sum_eq_single c']
  · simp [bvec]
  · intro b _ hb
    have : eI k r c' ≠ eI k r b := fun h => hb (eI_inj k r h).symm
    simp [bvec, Pi.single_eq_of_ne this]
  · simp

lemma upperOff_ne {r : ℕ} {β : Fin r → ℕ} (hβ : Monotone β) (x : UToff β → ℂ) (a b : Fin r)
    (h : upperOff β x a b ≠ 0) : a = b ∨ β a < β b := by
  by_contra hc
  push_neg at hc
  apply h
  unfold upperOff upper
  by_cases h1 : a < b
  · rw [dif_pos h1]
    exact dif_neg (not_not.2 (le_antisymm (hβ h1.le) hc.2))
  · rw [dif_neg h1, if_neg hc.1]

lemma levi_diag_middle_mem_bessel_unitary_eucl {k r : ℕ} {m : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ} (hm : m ∈ UH (Hb k)) (a : Fin r → ℝ)
    (ha : ∀ b, 0 < a b) :
    uEmb k r (Matrix.diagonal fun b => (a b : ℂ)) * mEmb k r m ∈ GG k r ∧ ∀ c : Fin r,
      eucl ((uEmb k r (Matrix.diagonal fun b => (a b : ℂ)) * mEmb k r m)⁻¹ *ᵥ bvec (eI k r c)) = (a c)⁻¹ := by
  have hu : IsUnit (Matrix.diagonal fun b => (a b : ℂ)).det := by
    rw [Matrix.det_diagonal, isUnit_iff_ne_zero]
    exact Finset.prod_ne_zero_iff.2 fun b _ => by exact_mod_cast (ha b).ne'
  obtain ⟨h1, -, h3, -⟩ := (GlobalTheory.Amp.UEmb.uEmb_hom k r).2.2.1 _ hu
  have hG := G_mul h1 ((GlobalTheory.Amp.Rad.radical k r).2.2.2.2 m hm).1
  refine ⟨hG, fun c => ?_⟩
  have h4 : (uEmb k r (Matrix.diagonal fun b => (a b : ℂ)) * mEmb k r m) *ᵥ bvec (eI k r c) =
      (a c : ℂ) • bvec (eI k r c) := by
    rw [← Matrix.mulVec_mulVec, mEmb_e, h3, Finset.sum_eq_single c]
    · simp
    · intro b _ hb; simp [hb]
    · simp
  have hc : (a c : ℂ) ≠ 0 := by exact_mod_cast (ha c).ne'
  have h5 : (uEmb k r (Matrix.diagonal fun b => (a b : ℂ)) * mEmb k r m)⁻¹ *ᵥ bvec (eI k r c) =
      (a c : ℂ)⁻¹ • bvec (eI k r c) := by
    have := congrArg (fun v => (uEmb k r (Matrix.diagonal fun b => (a b : ℂ)) * mEmb k r m)⁻¹ *ᵥ v) h4
    simp only [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ (G_unit hG), Matrix.one_mulVec,
      Matrix.mulVec_smul] at this
    rw [eq_inv_smul_iff₀ hc]; exact this.symm
  rw [h5, eucl_eq, WithLp.toLp_smul, norm_smul]
  simp [bvec, abs_of_pos (ha c)]

lemma Dmin_eq {k r j : ℕ} (hj : j ≤ r) (z z' : Fin (2 * r + k + 1) → ℂ) (g : Mat k r) (l : ℕ) (hl : l ≤ j) :
    Dmin k r z z' g ⟨l, by omega⟩ =
      (((Zr k r g).submatrix (Fin.castLE hj) (Fin.castLE hj)).submatrix (Fin.castLE hl) (Fin.castLE hl)).det := by
  unfold Dmin
  congr 1
  ext a b
  have ha := a.2
  have hb := b.2
  simp only at ha hb
  simp only [Matrix.submatrix_apply, Zhat, fvec]
  rw [dif_pos (by simp; omega), dif_pos (by simp; omega), herm_e]
  simp only [bvec, Matrix.mulVec_single_one, Matrix.col_apply, Zr]
  rfl

theorem herm_sEl_inv_le : ∀ (k r j : ℕ) (hj : j ≤ r) (z z' : (Fin (2 * r + k + 1) → ℂ)), ∀ (g₀ : Mat k r) (β : Fin r → ℕ) (c : ℂ), inWb k r z → inWb k r z' → 0 < Tz k r z → IsNormal0 k r hj β c z z' g₀ → ∀ De R₀ : ℝ, DeOK k r z z' g₀ De → 1 ≤ R₀ → ∀ m ∈ UH (Hb k), ∀ (q : PSec k r j × (UToff β → ℂ)) (a : Fin r → ℝ), (∀ b, 0 < a b) → Sg2 k r z' (sEl k r j β q * (uEmb k r (Matrix.diagonal fun b => (a b : ℂ)) * mEmb k r m)) ≤ R₀ → Sg k r z (g₀ * (sEl k r j β q * (uEmb k r (Matrix.diagonal fun b => (a b : ℂ)) * mEmb k r m))) ≤ R₀ → ∀ b : Fin r, b.val < j → ∀ u : (Fin (2 * r + k + 1) → ℂ), eucl ((uEmb k r (Matrix.diagonal fun b => (a b : ℂ)) * mEmb k r m)⁻¹ *ᵥ u) ≤ R₀ → ‖herm (Hpk k r) ((sEl k r j β q)⁻¹ *ᵥ bvec (esI k r b)) u‖ ≤ R₀ ^ (2 * r) * De := by
  intro k r j hj z z' g₀ β c hz hz' _ hN De R₀ hDe hR m hm q a ha hS' hS b hb u hu
  obtain ⟨hg, -, -, hβ, -, hX, -, hB⟩ := hN
  obtain ⟨w, hw, hwβ, hP⟩ := GlobalTheory.Amp.blockAnti_perm_partialProd j _ _ De hB hDe.1 (fun l hl h => by
    rw [← Dmin_eq hj z z'] at h ⊢
    exact hDe.2 _ (hl.trans hj) h)
  obtain ⟨hg1, he⟩ := levi_diag_middle_mem_bessel_unitary_eucl (r := r) hm a ha
  have hs := sEl_mem k r j β q
  have hlen : ∀ c : Fin r, (a c)⁻¹ ≤ R₀ := by
    intro c
    have hsS : sEl k r j β q ∈ Sset k r z' :=
      ⟨1, ⟨(uHGroup _ _ (Hunit k r)).1, by simp, by simp⟩, _, hs, (one_mul _).symm⟩
    have h1 := (((GlobalTheory.Amp.LInv.lengths_basic k r z' hz').1 _ hg1 _ hsS 1 ⟨(uHGroup _ _ (Hunit k r)).1, one_mem _⟩).1 c.castSucc)
    rw [mul_one, (GlobalTheory.Amp.LInv.lengths_basic k r z' hz').2.1 a ha m hm] at h1
    rw [← h1]
    refine le_trans ?_ hS'
    unfold Sg2
    exact (Finset.le_fold_max _).2 (Or.inr ⟨c.castSucc, Finset.mem_univ _, le_max_left _ _⟩)
  set s := sEl k r j β q with hsdef
  set g₁ := uEmb k r (Matrix.diagonal fun b => (a b : ℂ)) * mEmb k r m with hg₁
  set Z := (Zr k r g₀).submatrix (Fin.castLE hj) (Fin.castLE hj) with hZ
  obtain ⟨b₀, hb₀⟩ := w.surjective ⟨b.val, hb⟩
  have hn : b₀.val + 1 ≤ j := b₀.2
  set ι : Fin (b₀.val + 1) → Fin j := Fin.castLE hn with hι
  let y : Fin (b₀.val + 1) → Fin (2 * r + k + 1) → ℂ := fun i =>
    if i = Fin.last _ then u else bvec (eI k r (Fin.castLE hj (w (ι i))))
  have hp := pluck_flag (hn.trans hj) z hz _ (G_mul hg (G_mul hs.1 hg1)) R₀ hS (fun i => g₁⁻¹ *ᵥ y i) (by
    intro i
    simp only [y]
    split_ifs
    · exact hu
    · rw [he]; exact hlen _)
  have hent : ∀ i i' : Fin (b₀.val + 1),
      herm (Hpk k r) ((g₀ * (s * g₁))⁻¹ *ᵥ bvec (eI k r (Fin.castLE (hn.trans hj) i'))) (g₁⁻¹ *ᵥ y i) =
        star (Z (ι i') (w (ι i'))) * herm (Hpk k r) (s⁻¹ *ᵥ bvec (esI k r (Fin.castLE hj (w (ι i'))))) (y i) := by
    intro i i'
    have h := inv_e hj hg (ι i') (w (ι i')) (hX _ (ι i').2).1 fun c hc => (hw _ _).1 hc
    rw [Matrix.mul_inv_rev, Matrix.mul_inv_rev, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
      herm_iso (G_inv hg1)]
    change herm _ (s⁻¹ *ᵥ (g₀⁻¹ *ᵥ bvec (eI k r (Fin.castLE hj (ι i'))))) _ = _
    rw [h, Matrix.mulVec_smul, herm_smul_left]
    rfl
  simp only [hent] at hp
  rw [Matrix.det_of_lowerTriangular] at hp
  swap
  · intro i i' hii
    have hlt : i < i' := hii
    have hi : i ≠ Fin.last _ := (hlt.trans_le (Fin.le_last _)).ne
    simp only [Matrix.of_apply, y, if_neg hi]
    rw [sEl_pair]
    refine mul_eq_zero_of_right _ (star_eq_zero.2 ?_)
    by_contra h0
    rcases upperOff_ne hβ _ _ _ h0 with h | h
    · exact hlt.ne' (Fin.castLE_injective hn (w.injective (Fin.castLE_injective hj h)))
    · have h1 := hwβ (ι i); have h2 := hwβ (ι i')
      rw [h1, h2] at h
      exact absurd (hβ (show Fin.castLE hj (ι i) ≤ Fin.castLE hj (ι i') from hlt.le)) (not_le.2 h)
  simp only [Matrix.of_apply, Finset.prod_mul_distrib, norm_mul, norm_prod, norm_star] at hp
  have hlast : ∏ i : Fin (b₀.val + 1),
      ‖herm (Hpk k r) (s⁻¹ *ᵥ bvec (esI k r (Fin.castLE hj (w (ι i))))) (y i)‖ =
      ‖herm (Hpk k r) (s⁻¹ *ᵥ bvec (esI k r b)) u‖ := by
    rw [Finset.prod_eq_single (Fin.last _)]
    · have : ι (Fin.last _) = b₀ := rfl
      simp only [y, if_true, this, hb₀]
      rfl
    · intro i _ hi
      simp only [y, if_neg hi]
      rw [sEl_pair]
      simp [upperOff, upper]
    · simp
  have hprod : ∏ i : Fin (b₀.val + 1), ‖Z (ι i) (w (ι i))‖ =
      ∏ a ∈ Finset.univ.filter (fun a : Fin j => a.val < b₀.val + 1), ‖Z a (w a)‖ := by
    refine Finset.prod_bij (fun i _ => ι i) ?_ ?_ ?_ ?_
    · intro i _; exact Finset.mem_filter.2 ⟨Finset.mem_univ _, i.2⟩
    · intro i _ i' _ h; exact Fin.castLE_injective hn h
    · intro c hc
      exact ⟨⟨c.val, (Finset.mem_filter.1 hc).2⟩, Finset.mem_univ _, rfl⟩
    · intro i _; rfl
  rw [hlast, hprod] at hp
  have hP' := hP (b₀.val + 1)
  set P := ∏ a ∈ Finset.univ.filter (fun a : Fin j => a.val < b₀.val + 1), ‖Z a (w a)‖
  have hP0 : 0 < P := Finset.prod_pos fun a _ => norm_pos_iff.2 ((hw _ _).2 rfl)
  have hpow : R₀ ^ (b₀.val + 1) * R₀ ^ (b₀.val + 1) ≤ R₀ ^ (2 * r) := by
    rw [← pow_add]; exact pow_le_pow_right₀ hR (by omega)
  calc _ ≤ R₀ ^ (2 * r) * P⁻¹ := by
        rw [← div_eq_mul_inv, le_div_iff₀' hP0]; exact hp.trans hpow
    _ ≤ _ := mul_le_mul_of_nonneg_left hP' (by positivity)

end GlobalTheory.Amp.NfComp
