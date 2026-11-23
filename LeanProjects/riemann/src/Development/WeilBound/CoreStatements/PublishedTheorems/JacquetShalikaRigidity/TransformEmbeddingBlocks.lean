import Development.WeilBound.CoreStatements.PublishedTheorems.JacquetShalikaRigidity.ColumnConjugationMeasure
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.QuotientAverageMapLatticeEquiv

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open GlobalTheory.CuspGeneric GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DiscSpec PositivityTheory.jumpWindows PositivityTheory.RgJS
open GroundTheory.Automorphic GroundTheory.Automorphic.FourierWhittaker GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.Spherical
open scoped ENNReal ComplexConjugate

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PositivityTheory.AdelicQuotientData

namespace TransformEmbeddingBlocks

variable {E : Type} [Field E] [NumberField E]

theorem pT_succ' (ψ : AddChar (Ad E) ℂ) {a : ℕ} (j d : ℕ) (f : GA E a → ℂ) :
    pT ψ j (d + 1) f = colT ψ j (pT ψ (j + 1) d f) := by
  induction d generalizing f with
  | zero => rfl
  | succ d ih =>
    show pT ψ j (d + 1) (colT ψ (j + (d + 1)) f) = colT ψ j (pT ψ (j + 1) d (colT ψ (j + 1 + d) f))
    rw [ih, show j + 1 + d = j + (d + 1) by omega]

theorem whit_pT (ψ : AddChar (Ad E) ℂ) {a : ℕ} (i d : ℕ) (f : GA E a → ℂ) :
    whit ψ (i + d) f = whit ψ i (pT ψ (i + 1) d f) := by
  induction d generalizing f with
  | zero => rfl
  | succ d ih =>
    show whit ψ (i + d) (colT ψ (i + d + 1) f) = whit ψ i (pT ψ (i + 1) d (colT ψ (i + 1 + d) f))
    rw [ih, show i + 1 + d = i + d + 1 by omega]

theorem good_pT {ψ : AddChar (Ad E) ℂ} (hψ : StdPsi ψ) {a : ℕ} (i d : ℕ) (f : GA E a → ℂ)
    (h : i + d < a) (hf : Good ψ (i + d) f) : Good ψ i (pT ψ (i + 1) d f) := by
  induction d generalizing f with
  | zero => exact hf
  | succ d ih =>
    show Good ψ i (pT ψ (i + 1) d (colT ψ (i + 1 + d) f))
    rw [show i + 1 + d = i + d + 1 by omega]
    exact ih _ (by omega) (GlobalTheory.CuspRep.Generic.good_colT (m := i + d) hψ h hf)

theorem uu_one {a : ℕ} (j : ℕ) : UU j (1 : GA E a) := by
  refine ⟨fun i c h => ?_, fun i => ?_, fun i c _ => rfl⟩
  · exact Matrix.one_apply_ne (ne_of_gt h)
  · exact Matrix.one_apply_eq i

theorem uu_mul {a j : ℕ} {x y : GA E a} (hx : UU j x) (hy : UU j y) : UU j (x * y) := by
  obtain ⟨x1, x2, x3⟩ := hx
  obtain ⟨y1, y2, y3⟩ := hy
  refine ⟨fun i c h => ?_, fun i => ?_, fun i c h => ?_⟩
  · rw [Units.val_mul, Matrix.mul_apply]
    refine Finset.sum_eq_zero fun l _ => ?_
    rcases lt_or_ge l i with hl | hl
    · rw [x1 i l hl, zero_mul]
    · rw [y1 l c (lt_of_lt_of_le h hl), mul_zero]
  · rw [Units.val_mul, Matrix.mul_apply, Finset.sum_eq_single i, x2, y2, one_mul]
    · intro l _ hl
      rcases lt_or_gt_of_ne hl with hl | hl
      · rw [x1 i l hl, zero_mul]
      · rw [y1 l i hl, mul_zero]
    · simp
  · rw [Units.val_mul, Matrix.mul_apply, Finset.sum_eq_single c, y3 c c h, x3 i c h, Matrix.one_apply_eq, mul_one]
    · intro l _ hl
      rw [y3 l c h, Matrix.one_apply_ne hl, mul_zero]
    · simp

theorem blkU_apply {R : Type} [CommRing R] {a r n : ℕ} (x : UnipotentBlockColumnIndex a r n → R) (i c : Fin a) :
    (blkU x).val i c = (1 : Matrix (Fin a) (Fin a) R) i c + ∑ t, if t.1.1 = i ∧ t.1.2 = c then x t else 0 := by
  change (1 + posM Subtype.val x : Matrix (Fin a) (Fin a) R) i c = _
  rw [Matrix.add_apply, posM, Matrix.sum_apply]
  simp only [Matrix.single_apply]

theorem blkU_apply_of {R : Type} [CommRing R] {a r n : ℕ} (x : UnipotentBlockColumnIndex a r n → R) (i c : Fin a)
    (h : ∀ t : UnipotentBlockColumnIndex a r n, ¬ (t.1.1 = i ∧ t.1.2 = c)) :
    (blkU x).val i c = (1 : Matrix (Fin a) (Fin a) R) i c := by
  rw [blkU_apply, Finset.sum_eq_zero, add_zero]
  intro t _
  rw [if_neg (h t)]

theorem uu_blkU {a j i : ℕ} (hj : j ≤ i) (y : UnipotentBlockColumnIndex a i i → Ad E) : UU j (blkU y : GA E a) := by
  refine ⟨fun r c h => ?_, fun r => ?_, fun r c h => ?_⟩
  · rw [blkU_apply_of _ _ _ ?_, Matrix.one_apply_ne (ne_of_gt h)]
    rintro t ⟨e1, e2⟩
    have := t.2
    subst e1 e2
    rw [Fin.lt_def] at h
    omega
  · rw [blkU_apply_of _ _ _ ?_, Matrix.one_apply_eq]
    rintro t ⟨e1, e2⟩
    have := t.2
    have e3 : (t.1.1 : ℕ) = t.1.2 := by rw [e1, e2]
    omega
  · rw [blkU_apply_of _ _ _ ?_]
    rintro t ⟨e1, e2⟩
    have := t.2
    subst e1 e2
    omega

theorem norm_avg_le {G : Type} [AddCommGroup G] [TopologicalSpace G] (Γ : AddSubgroup G) (Φ : G → ℂ) {B : ℝ}
    (hB : 0 ≤ B) (h : ∀ x, ‖Φ x‖ ≤ B) : ‖avg Γ Φ‖ ≤ B := by
  let _ : MeasurableSpace G := borel G
  unfold avg
  split_ifs with hp
  · obtain ⟨-, -, h1⟩ := hp.choose_spec
    have := norm_setIntegral_le_of_norm_le_const (μ := hp.choose.1) (s := hp.choose.2) (f := Φ) (C := B)
      (by rw [h1]; exact ENNReal.one_lt_top) (fun x _ => h x)
    rwa [Measure.real, h1, ENNReal.toReal_one, mul_one] at this
  · simpa using hB

theorem norm_colT_le {ψ : AddChar (Ad E) ℂ} (hψ : StdPsi ψ) {a : ℕ} (n : ℕ) (f : GA E a → ℂ) (x : GA E a) {B : ℝ}
    (hB : 0 ≤ B) (h : ∀ y : UnipotentBlockColumnIndex a n n → Ad E, ‖f (blkU y * x)‖ ≤ B) : ‖colT ψ n f x‖ ≤ B := by
  unfold colT coefF
  refine norm_avg_le _ _ hB fun y => ?_
  rw [norm_mul, hψ.norm, one_mul]
  exact h y

theorem bound_pT {ψ : AddChar (Ad E) ℂ} (hψ : StdPsi ψ) {a : ℕ} (j : ℕ) (x : GA E a) (B : ℝ) (d : ℕ) :
    ∀ f : GA E a → ℂ, (∀ u, UU j u → ‖f (u * x)‖ ≤ B) → ∀ u, UU j u → ‖pT ψ j d f (u * x)‖ ≤ B := by
  induction d with
  | zero => exact fun f hf => hf
  | succ d ih =>
    intro f hf
    refine ih _ fun u hu => ?_
    have hB : 0 ≤ B := (norm_nonneg _).trans (hf 1 (uu_one j))
    refine norm_colT_le hψ _ _ _ hB fun y => ?_
    rw [← mul_assoc]
    exact hf _ (uu_mul (uu_blkU (by omega) y) hu)

theorem mir_mul {R : Type} [CommRing R] {a n : ℕ} {x y : GL (Fin a) R} (hx : Mir n x) (hy : Mir n y) :
    Mir n (x * y) := by
  intro i c h
  rw [Units.val_mul, Matrix.mul_apply]
  rcases h with h | h
  · rw [Finset.sum_eq_single i]
    · rw [hx i i (Or.inl h), Matrix.one_apply_eq, one_mul, hy i c (Or.inl h)]
    · intro l _ hl
      rw [hx i l (Or.inl h), Matrix.one_apply_ne (Ne.symm hl), zero_mul]
    · simp
  · rw [Finset.sum_eq_single c]
    · rw [hy c c (Or.inr h), Matrix.one_apply_eq, mul_one, hx i c (Or.inr h)]
    · intro l _ hl
      rw [hy l c (Or.inr h), Matrix.one_apply_ne hl, mul_zero]
    · simp

theorem mir_blkU {R : Type} [CommRing R] {a j n : ℕ} (hj : j ≤ n) (y : UnipotentBlockColumnIndex a j j → R) : Mir n (blkU y) := by
  intro i c h
  apply blkU_apply_of
  rintro t ⟨e1, e2⟩
  have := t.2
  subst e1 e2
  omega

theorem mir_ratGL {a n : ℕ} (γ : GL (Fin a) E) (h : IsMir n γ) : Mir n (ratGL E a γ) := by
  intro i c hic
  change algebraMap E (Ad E) (γ.val i c) = _
  rw [h i c hic, Matrix.one_apply, Matrix.one_apply]
  split_ifs <;> simp

omit [NumberField E] in
theorem isMir_emb {k m n : ℕ} (ιE : GL (Fin k) E →* GL (Fin m) E) (hιE : IsEmb ιE) (γ : GL (Fin k) E)
    (h : IsMir n γ) : IsMir n (ιE γ) := by
  intro i c hic
  rw [hιE, embM, Matrix.of_apply]
  split_ifs with h2
  · rw [h ⟨i, h2.1⟩ ⟨c, h2.2⟩ hic]
    simp [Matrix.one_apply, Fin.ext_iff]
  · rfl

theorem mir_emb {m n : ℕ} (hkm : n + 1 ≤ m) (ι : GA E (n + 1) →* GA E m) (hι : IsEmb ι)
    (hs : ∀ x : GA E m, GlobalTheory (n + 1) x → ∃ g, x = ι g) (x : GA E m) (hx : Mir n x) :
    ∃ q, Mir n q ∧ x = ι q := by
  obtain ⟨q, rfl⟩ := hs x fun i c h => hx i c (by omega)
  refine ⟨q, fun i c h => ?_, rfl⟩
  have h1 := hx (Fin.castLE hkm i) (Fin.castLE hkm c) (by simpa using h)
  rw [hι, embM, Matrix.of_apply, dif_pos ⟨i.2, c.2⟩] at h1
  convert h1 using 1 <;> first | rfl | (rw [Matrix.one_apply, Matrix.one_apply]; simp only [Fin.ext_iff, Fin.val_castLE])

theorem blkU_zero' {a j : ℕ} : (blkU (0 : UnipotentBlockColumnIndex a j j → Ad E) : GA E a) = 1 := posU_zero _

def sig {k m j : ℕ} (hkm : k ≤ m) (hj : j < k) : UnipotentBlockColumnIndex k j j ≃ UnipotentBlockColumnIndex m j j where
  toFun t := ⟨(Fin.castLE hkm t.1.1, Fin.castLE hkm t.1.2), t.2⟩
  invFun t := ⟨(⟨t.1.1, by have := t.2; omega⟩, ⟨t.1.2, by have := t.2; omega⟩), t.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

@[simp] theorem sig_fst {k m j : ℕ} (hkm : k ≤ m) (hj : j < k) (t : UnipotentBlockColumnIndex k j j) :
    ((sig hkm hj t).1.1 : ℕ) = t.1.1 := rfl

@[simp] theorem sig_snd {k m j : ℕ} (hkm : k ≤ m) (hj : j < k) (t : UnipotentBlockColumnIndex k j j) :
    ((sig hkm hj t).1.2 : ℕ) = t.1.2 := rfl

def eqv {k m j : ℕ} (hkm : k ≤ m) (hj : j < k) : (UnipotentBlockColumnIndex k j j → Ad E) ≃ₜ+ (UnipotentBlockColumnIndex m j j → Ad E) where
  toFun x t := x ((sig hkm hj).symm t)
  invFun y t := y (sig hkm hj t)
  left_inv x := by funext t; simp
  right_inv y := by funext t; simp
  map_add' _ _ := rfl
  continuous_toFun := continuous_pi fun _ => continuous_apply _
  continuous_invFun := continuous_pi fun _ => continuous_apply _

theorem eqv_apply {k m j : ℕ} (hkm : k ≤ m) (hj : j < k) (x : UnipotentBlockColumnIndex k j j → Ad E) :
    eqv hkm hj x = fun t => x ((sig hkm hj).symm t) := rfl

theorem mem_eqv {k m j : ℕ} (hkm : k ≤ m) (hj : j < k) (x : UnipotentBlockColumnIndex k j j → Ad E) :
    eqv hkm hj x ∈ ratV E (UnipotentBlockColumnIndex m j j) ↔ x ∈ ratV E (UnipotentBlockColumnIndex k j j) := by
  simp only [ratV, AddMonoidHom.mem_range]
  constructor
  · rintro ⟨c, hc⟩
    refine ⟨fun t => c (sig hkm hj t), funext fun t => ?_⟩
    have := congrFun hc (sig hkm hj t)
    simpa [eqv_apply] using this
  · rintro ⟨c, rfl⟩
    exact ⟨fun t => c ((sig hkm hj).symm t), rfl⟩

theorem emb_blkU {k m j : ℕ} (hkm : k ≤ m) (hj : j < k) (ι : GA E k →* GA E m) (hι : IsEmb ι)
    (x : UnipotentBlockColumnIndex k j j → Ad E) : ι (blkU x) = blkU (fun t => x ((sig hkm hj).symm t)) := by
  apply Units.ext
  ext i c
  rw [hι, embM, Matrix.of_apply]
  split_ifs with h
  · rw [blkU_apply, blkU_apply]
    congr 1
    · simp [Matrix.one_apply, Fin.ext_iff]
    · refine Fintype.sum_equiv (sig hkm hj) _ _ fun t => ?_
      simp [Fin.ext_iff]
  · symm
    apply blkU_apply_of
    rintro t ⟨e1, e2⟩
    apply h
    have := t.2
    subst e1 e2
    omega

theorem dot_eqv {k m j : ℕ} (hkm : k ≤ m) (hj : j < k) (x : UnipotentBlockColumnIndex k j j → Ad E) :
    dot (eLast m j) (fun t => x ((sig hkm hj).symm t)) = dot (eLast k j) x := by
  unfold dot
  refine (Fintype.sum_equiv (sig hkm hj) _ _ fun t => ?_).symm
  beta_reduce
  rw [Equiv.symm_apply_apply]
  rfl

theorem colT_emb {ψ : AddChar (Ad E) ℂ} (hψ : StdPsi ψ) {k m j : ℕ} (hkm : k ≤ m) (hj : j < k)
    (ι : GA E k →* GA E m) (hι : IsEmb ι) (G : GA E m → ℂ) (hG : Good ψ j G) :
    colT ψ j (fun g => G (ι g)) = fun g => colT ψ j G (ι g) := by
  funext g
  unfold colT coefF
  refine Eq.trans ?_ (avg_equiv _ _ _ _ (isCoLat_ratV E _) (isCoLat_ratV E _) (eqv hkm hj) (mem_eqv hkm hj) _
    (per_coef hψ (eLast m j) hG.cont (GlobalTheory.CuspRep.Generic.hl_of_good hG le_rfl) (ι g)))
  congr 1
  funext x
  rw [eqv_apply, dot_eqv]
  beta_reduce
  rw [map_mul, emb_blkU hkm hj ι hι]

theorem whit_emb {ψ : AddChar (Ad E) ℂ} (hψ : StdPsi ψ) {k m : ℕ} (hkm : k < m) (ι : GA E k →* GA E m)
    (hι : IsEmb ι) (n : ℕ) : n < k → ∀ G : GA E m → ℂ, Good ψ n G →
      whit ψ n (fun g => G (ι g)) = fun g => whit ψ n G (ι g) := by
  induction n with
  | zero => intro _ G _; rfl
  | succ n ih =>
    intro hn G hG
    rw [whit_succ, whit_succ, colT_emb hψ hkm.le hn ι hι G hG]
    exact ih (by omega) _ (GlobalTheory.CuspRep.Generic.good_colT hψ (by omega) hG)

end TransformEmbeddingBlocks

theorem transform_embedding_of : jumpWindows.FourierUniquenessMirabolic → P0 → P1 → P2 → CornerEmbedding → TransformsEmbedding := by
  intro hG11 _ _ _ hK5e E _ _ _ m k hk hkm ψ hψ ι hι φ hφ
  obtain ⟨n, rfl⟩ : ∃ n, k = n + 1 := ⟨k - 1, by omega⟩
  obtain ⟨hR, hE⟩ := hK5e E m (n + 1) hkm.le
  obtain ⟨hcont, -, hsurj, -, -, -, hrat, -⟩ := hE ι hι
  obtain ⟨ιE, hιE⟩ := hR E
  have hm1 : n + (m - (n + 1)) = m - 1 := by omega
  have hgood1 : Good ψ (n + 1) (pT ψ (n + 1 + 1) (m - (n + 1 + 1)) φ) := by
    refine TransformEmbeddingBlocks.good_pT hψ (n + 1) (m - (n + 1 + 1)) φ (by omega) ?_
    rwa [show n + 1 + (m - (n + 1 + 1)) = m - 1 by omega]
  have hgood0 : Good ψ n (pT ψ (n + 1) (m - (n + 1)) φ) := by
    refine TransformEmbeddingBlocks.good_pT hψ n _ φ (by omega) ?_
    rwa [hm1]
  have hwhit : whit ψ (m - 1) φ = whit ψ n (pT ψ (n + 1) (m - (n + 1)) φ) := by
    rw [← TransformEmbeddingBlocks.whit_pT, hm1]
  have hwe := TransformEmbeddingBlocks.whit_emb hψ hkm ι hι n (by omega) _ hgood0
  refine ⟨hgood1, ?_, ?_, ?_, ?_, ?_⟩
  · rw [show m - (n + 1) = m - (n + 1 + 1) + 1 by omega, TransformEmbeddingBlocks.pT_succ']
  · show Pre ψ n _
    refine ⟨hgood0.cont.comp hcont, fun γ hγ g => ?_, fun j hj y g => ?_⟩
    · rw [map_mul, hrat ιE hιE γ]
      exact hgood0.left _ (TransformEmbeddingBlocks.isMir_emb ιE hιE γ hγ) _
    · have : IsEmpty (UnipotentBlockColumnIndex (n + 1) j j) := ⟨fun t => by have := t.2; have := t.1.2.2; omega⟩
      obtain rfl : y = 0 := funext fun t => isEmptyElim t
      rw [TransformEmbeddingBlocks.blkU_zero', one_mul]
      simp [dot]
  · intro g
    show whit ψ n _ g = _
    rw [hwe, hwhit]
  · intro g hg
    by_contra hne
    push Not at hne
    apply hg
    have key := hG11 E m ψ hψ n (pT ψ (n + 1) (m - (n + 1)) φ) (Or.inl (by omega)) hgood0
      {x | ∃ p : GA E (n + 1), Mir n p ∧ x = ι (p * g)} ?_ ?_ ?_ (ι g) ⟨1, fun i c _ => rfl, by rw [one_mul]⟩
    · exact key
    · rintro γ hγ _ ⟨p, hp, rfl⟩
      obtain ⟨q, hq, hq'⟩ := TransformEmbeddingBlocks.mir_emb hkm.le ι hι hsurj _ (TransformEmbeddingBlocks.mir_ratGL γ hγ)
      exact ⟨q * p, TransformEmbeddingBlocks.mir_mul hq hp, by rw [hq', ← map_mul, mul_assoc]⟩
    · rintro j hj y _ ⟨p, hp, rfl⟩
      obtain ⟨q, hq, hq'⟩ := TransformEmbeddingBlocks.mir_emb hkm.le ι hι hsurj _ (TransformEmbeddingBlocks.mir_blkU hj y)
      exact ⟨q * p, TransformEmbeddingBlocks.mir_mul hq hp, by rw [hq', ← map_mul, mul_assoc]⟩
    · rintro _ ⟨p, hp, rfl⟩
      rw [← hwhit]
      exact hne p hp
  · intro j x B hj hjm hB
    have := TransformEmbeddingBlocks.bound_pT hψ j x B (m - j) φ hB 1 (TransformEmbeddingBlocks.uu_one j)
    rwa [one_mul] at this

end PositivityTheory.AdelicQuotientData

end
