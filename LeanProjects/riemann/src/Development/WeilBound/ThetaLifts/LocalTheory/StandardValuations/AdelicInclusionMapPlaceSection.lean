import Development.WeilBound.ThetaLifts.LocalTheory.StandardValuations.LocalSplittingLinearSkew
import Development.WeilBound.ThetaLifts.LocalTheory.UatClosure

set_option linter.unusedSectionVars false

noncomputable section

namespace PositivityTheory.ThKG.Std

open NumberField IsDedekindDomain GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.SplitFlip Matrix
open PositivityTheory.KCo PositivityTheory.ThK.SplitDict PositivityTheory.ThKG.StdDict PositivityTheory.ThKG.Loc MeasureTheory ValuativeRel Topology GlobalTheory.ThK
open GlobalTheory.Doubling (absE)
open scoped TensorProduct

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {v : Pl F}
  {t : E →ₐ[F] Fv F v} {sec : Fv F v × Fv F v → AE F E}

  {n d n₁ d₁ : ℕ} {X : Spc F E n} {W : Spc F E d} {X₁ : Spc F E n₁} {W₁ : Spc F E d₁}

variable (σ t) in

structure PE (J : Matrix (Fin n) (Fin n) E) (J₁ : Matrix (Fin n₁) (Fin n₁) E) (b : GL (Fin n) (Fv F v)) (b₁ : GL (Fin n₁) (Fv F v))
    (ι : Matrix (Fin n) (Fin n₁) E) (sk : Fin n₁ → Fin n) : Prop where
  p1 : (b⁻¹).1 * ι.map t = emb (Fv F v) sk * (b₁⁻¹).1
  p2 : b.1ᵀ * J.map t * ι.map (t.comp σ) = emb (Fv F v) sk * (b₁.1ᵀ * J₁.map t)

variable (σ t) in

structure PX (J : Matrix (Fin n) (Fin n) E) (b : GL (Fin n) (Fv F v)) (x y : Fin n → E) (j₀ j₁ : Fin n) (ε : Fv F v) : Prop where
  x1 : (b⁻¹).1 *ᵥ (fun i => t (x i)) = Pi.single j₀ 1
  y1 : (b⁻¹).1 *ᵥ (fun i => t (y i)) = Pi.single j₁ 1
  x2 : (b.1ᵀ * J.map t) *ᵥ (fun i => t (σ (x i))) = Pi.single j₁ ε
  y2 : (b.1ᵀ * J.map t) *ᵥ (fun i => t (σ (y i))) = Pi.single j₀ 1

theorem pe_one (J : Matrix (Fin n) (Fin n) E) (b : GL (Fin n) (Fv F v)) : PE σ t J J b b 1 id := by
  have : emb (Fv F v) (id : Fin n → Fin n) = 1 := by ext i j; simp [emb, one_apply]
  refine ⟨?_, ?_⟩ <;> rw [this, Matrix.map_one _ (map_zero _) (map_one _), Matrix.mul_one, Matrix.one_mul]

theorem form_swap (hσ : IsCMExt F E σ) {J : Matrix (Fin n) (Fin n) E} {ε : E} (hJ : ∀ i j, σ (J j i) = ε * J i j) (hε : ε * ε = 1)
    (p q : Fin n → E) : form σ J q p = ε * σ (form σ J p q) := by
  simp only [form, dotProduct, mulVec, map_sum, map_mul, hJ, Finset.mul_sum, PositivityTheory.ThK.Vac.sigma_sigma hσ]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  linear_combination (-(q j * J j i * σ (p i))) * hε

theorem plane {B : Base F E} (hσ : IsCMExt F E σ) {H : Plane E n n₁} {i₀ i₁ : ℕ} (h : H.IsAdapted σ B X X₁ i₀ i₁) {ε : E}
    (hJ : ∀ i j, σ (X.J j i) = ε * X.J i j) (hε : ε * ε = 1) (w : B.P) {j₀ j₁ : Fin n} {sk : Fin n₁ → Fin n} (h0 : j₀.1 = i₀)
    (h1 : j₁.1 = i₁) (hs : ∀ j, (sk j).1 = skip i₀ i₁ j) (hi : Function.Injective sk) (hc : ∀ i, i = j₀ ∨ i = j₁ ∨ ∃ j, i = sk j)
    (n01 : j₀ ≠ j₁) (n0 : ∀ j, sk j ≠ j₀) (n1 : ∀ j, sk j ≠ j₁) :
    PE σ (B.τ w) X.J X₁.J (X.bas w) (X₁.bas w) H.ι sk ∧ PX σ (B.τ w) X.J (X.bas w) H.x H.y j₀ j₁ (B.τ w ε) := by
  set t := B.τ w
  set b := X.bas w
  set b₁ := X₁.bas w
  have c0 : ∀ r, b.1 r j₀ = t (H.x r) := (h.bas w j₀).1 h0
  have c1 : ∀ r, b.1 r j₁ = t (H.y r) := (h.bas w j₁).2.1 h1
  have cs : ∀ j r, b.1 r (sk j) = (H.ι.map t * b₁.1) r j := fun j => (h.bas w (sk j)).2.2 j (hs j)
  have e1 : b.1 * emb (Fv F w.1) sk = H.ι.map t * b₁.1 := by
    refine Matrix.ext fun r j => ?_
    rw [← cs]; simp [emb, Matrix.mul_apply]
  have R : ∀ (i : Fin n) (p q : Fin n → E), (∀ r, b.1 r i = t (p r)) →
      ((b.1ᵀ * X.J.map t) *ᵥ fun r => t (σ (q r))) i = t (form σ X.J p q) := fun i p q hp => by
    rw [← mulVec_mulVec]
    simp only [form, dotProduct, mulVec, transpose_apply, hp, map_sum, map_mul, map_apply]
  have S : ∀ (j : Fin n₁) (q : Fin n → E), (∀ u, form σ X.J (H.ι *ᵥ u) q = 0) →
      ((b.1ᵀ * X.J.map t) *ᵥ fun r => t (σ (q r))) (sk j) = 0 := fun j q hq => by
    have a : ∀ k, ((H.ι.map t)ᵀ *ᵥ (X.J.map t *ᵥ fun r => t (σ (q r)))) k = 0 := fun k => by
      have := congrArg t (hq (Pi.single k 1))
      simpa only [form, dotProduct, mulVec, transpose_apply, map_sum, map_mul, map_apply, map_zero, Pi.single_apply, mul_ite, mul_one,
        mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true] using this
    have : ((b.1 * emb (Fv F w.1) sk)ᵀ *ᵥ (X.J.map t *ᵥ fun r => t (σ (q r)))) j = 0 := by
      rw [e1, transpose_mul, ← mulVec_mulVec, show (H.ι.map t)ᵀ *ᵥ _ = 0 from funext a, mulVec_zero]; rfl
    rw [transpose_mul, ← mulVec_mulVec, mulVec_mulVec _ b.1ᵀ] at this
    simpa [emb, mulVec, dotProduct] using this
  have col : ∀ (j : Fin n) (p : Fin n → E), (∀ r, b.1 r j = t (p r)) → (b⁻¹).1 *ᵥ (fun i => t (p i)) = Pi.single j 1 := fun j p hp => by
    rw [show (fun i => t (p i)) = b.1 *ᵥ Pi.single j 1 from funext fun r => by simp [← hp], mulVec_mulVec, Units.inv_mul, one_mulVec]
  have yx : form σ X.J H.y H.x = ε := by rw [form_swap hσ hJ hε, h.xy, map_one, mul_one]
  refine ⟨⟨?_, ?_⟩, col _ _ c0, col _ _ c1, funext fun i => ?_, funext fun i => ?_⟩
  · rw [← Matrix.mul_one (H.ι.map t), ← Units.mul_inv b₁, ← Matrix.mul_assoc (H.ι.map t), ← e1, ← Matrix.mul_assoc, ← Matrix.mul_assoc,
      Units.inv_mul, Matrix.one_mul]
  · refine Matrix.ext fun i k => ?_
    have a : (b.1ᵀ * X.J.map t * H.ι.map (t.comp σ)) i k = ((b.1ᵀ * X.J.map t) *ᵥ fun r => t (σ ((H.ι *ᵥ Pi.single k 1) r))) i := by
      simp [Matrix.mul_apply, mulVec, dotProduct, Pi.single_apply]
    rcases hc i with rfl | rfl | ⟨j, rfl⟩
    · rw [a, R _ _ _ c0, form_swap hσ hJ hε, (h.orth _).1]
      simp [emb, Matrix.mul_apply, fun j => (n0 j).symm]
    · rw [a, R _ _ _ c1, form_swap hσ hJ hε, (h.orth _).2]
      simp [emb, Matrix.mul_apply, fun j => (n1 j).symm]
    · have g : (H.ι.map t)ᵀ * X.J.map t * H.ι.map (t.comp σ) = X₁.J.map t := by
        rw [← h.gram]
        refine Matrix.ext fun p q => ?_
        simp [Matrix.mul_apply]
      have : ((b.1 * emb (Fv F w.1) sk)ᵀ * X.J.map t * H.ι.map (t.comp σ)) j k = (b₁.1ᵀ * X₁.J.map t) j k := by
        rw [e1, transpose_mul, ← g]; simp only [Matrix.mul_assoc]
      rw [transpose_mul, Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc b.1ᵀ] at this
      rw [Matrix.mul_apply (M := emb (Fv F w.1) sk)]
      rw [Matrix.mul_apply] at this
      simpa [emb, hi.eq_iff] using this
  · rcases hc i with rfl | rfl | ⟨j, rfl⟩
    · rw [R _ _ _ c0, h.xx, map_zero, Pi.single_eq_of_ne n01]
    · rw [R _ _ _ c1, yx, Pi.single_eq_same]
    · rw [S _ _ fun u => (h.orth u).1, Pi.single_eq_of_ne (n1 j)]
  · rcases hc i with rfl | rfl | ⟨j, rfl⟩
    · rw [R _ _ _ c0, h.xy, map_one, Pi.single_eq_same]
    · rw [R _ _ _ c1, h.yy, map_zero, Pi.single_eq_of_ne n01.symm]
    · rw [S _ _ fun u => (h.orth u).2, Pi.single_eq_of_ne (n0 j)]

variable {b : GL (Fin n) (Fv F v)} {c : GL (Fin d) (Fv F v)} {b₁ : GL (Fin n₁) (Fv F v)} {c₁ : GL (Fin d₁) (Fv F v)}

theorem adelic_inclusion_map_place_section (h : IsSec σ t sec) {α β : Type} (J : Matrix α β E) : (incM F J).map (piW (t.comp σ)) = J.map (t.comp σ) :=
  Matrix.ext fun i j => incM_map' h J i j

theorem emb_c (h : IsSec σ t sec) {ι ι' jr jc} (a : PE σ t X.J X₁.J b b₁ ι jr) (a' : PE σ t W.J W₁.J c c₁ ι' jc) (z) :
    cW t b c (incM F ι * z * (incM F ι')ᵀ) = ext jr jc (cW t b₁ c₁ z) ∧
      cB σ t X W b c (incM F ι * z * (incM F ι')ᵀ) = ext jr jc (cB σ t X₁ W₁ b₁ c₁ z) := by
  constructor
  · rw [cW, Matrix.map_mul, Matrix.map_mul, transpose_map, incM_map h, incM_map h]
    calc _ = ((b⁻¹).1 * ι.map t) * z.map (piW t) * ((c⁻¹).1 * ι'.map t)ᵀ := by simp only [transpose_mul, Matrix.mul_assoc]
      _ = _ := by rw [a.p1, a'.p1]; simp only [ext, cW, transpose_mul, Matrix.mul_assoc]
  · rw [cB, Matrix.map_mul, Matrix.map_mul, transpose_map, adelic_inclusion_map_place_section h, adelic_inclusion_map_place_section h]
    calc _ = -((b.1ᵀ * X.J.map t * ι.map (t.comp σ)) * z.map (piW (t.comp σ)) * (c.1ᵀ * W.J.map t * ι'.map (t.comp σ))ᵀ) := by
          simp only [transpose_mul, transpose_transpose, Matrix.mul_assoc]
      _ = _ := by
          rw [a.p2, a'.p2]
          simp only [ext, cB, transpose_mul, transpose_transpose, Matrix.mul_assoc, Matrix.mul_neg, Matrix.neg_mul]

variable (t) in

def v1 (b : GL (Fin n) (Fv F v)) (p : Fin n → AE F E) : Fin n → Fv F v := (b⁻¹).1 *ᵥ fun i => piW t (p i)

variable (σ t) in

def v2 (J : Matrix (Fin n) (Fin n) E) (b : GL (Fin n) (Fv F v)) (p : Fin n → AE F E) : Fin n → Fv F v :=
  (b.1ᵀ * J.map t) *ᵥ fun i => piW (t.comp σ) (p i)

theorem rk_c (p : Fin n → AE F E) (q : Fin d → AE F E) : cW t b c (vecMulVec p q) = vecMulVec (v1 t b p) (v1 t c q) ∧
    cB σ t X W b c (vecMulVec p q) = -vecMulVec (v2 σ t X.J b p) (v2 σ t W.J c q) := by
  have e : ∀ π : AE F E →+* Fv F v, (vecMulVec p q).map π = vecMulVec (fun i => π (p i)) fun j => π (q j) := fun π =>
    Matrix.ext fun i j => map_mul π _ _
  constructor
  · rw [cW, e, mul_vecMulVec, vecMulVec_mul, vecMul_transpose]; rfl
  · rw [cB, e, mul_vecMulVec, Matrix.mul_assoc, vecMulVec_mul, show (W.J.map t)ᵀ * c.1 = (c.1ᵀ * W.J.map t)ᵀ by simp, vecMul_transpose]
    rfl

theorem vec_ex (h : IsSec σ t sec) {J : Matrix (Fin n) (Fin n) E} (hJ : IsUnit (J.map t)) (r r' : Fin n → Fv F v) :
    ∃ p, At (evFin F v) p ∧ v1 t b p = r ∧ v2 σ t J b p = r' := by
  obtain ⟨A, hA⟩ := hJ
  refine ⟨fun i => sec ((b.1 *ᵥ r) i, (((A⁻¹).1 * (b⁻¹).1ᵀ) *ᵥ r') i), fun u hu => funext fun i => h.at' _ u hu, ?_, ?_⟩
  · simp only [v1, h.fst]
    rw [mulVec_mulVec, Units.inv_mul, one_mulVec]
  · simp only [v2, h.snd]
    rw [mulVec_mulVec, ← hA, Matrix.mul_assoc, ← Matrix.mul_assoc A.1, Units.mul_inv, Matrix.one_mul, ← transpose_mul, Units.inv_mul,
      transpose_one, one_mulVec]

theorem vec_sub (h : IsSec σ t sec) {J J₁ ι sk} (a : PE σ t J J₁ b b₁ ι sk) (p : Fin n₁ → AE F E) :
    v1 t b (incM F ι *ᵥ p) = emb (Fv F v) sk *ᵥ v1 t b₁ p ∧ v2 σ t J b (incM F ι *ᵥ p) = emb (Fv F v) sk *ᵥ v2 σ t J₁ b₁ p := by
  have e : ∀ π : AE F E →+* Fv F v, (fun i => π ((incM F ι *ᵥ p) i)) = (incM F ι).map π *ᵥ fun i => π (p i) := fun π =>
    funext fun i => RingHom.map_mulVec π _ _ i
  constructor
  · rw [v1, e, incM_map h, mulVec_mulVec, a.p1, ← mulVec_mulVec]; rfl
  · rw [v2, e, adelic_inclusion_map_place_section h, mulVec_mulVec, a.p2, ← mulVec_mulVec]; rfl

theorem vec_ex' (h : IsSec σ t sec) {J J₁ ι sk} (a : PE σ t J J₁ b b₁ ι sk) (hJ : IsUnit (J₁.map t)) (j : Fin n₁) (s s' : Fv F v) :
    ∃ p, At (evFin F v) (incM F ι *ᵥ p) ∧ v1 t b (incM F ι *ᵥ p) = Pi.single (sk j) s ∧
      v2 σ t J b (incM F ι *ᵥ p) = Pi.single (sk j) s' := by
  obtain ⟨p, h0, h1, h2⟩ := vec_ex (b := b₁) h hJ (Pi.single j s) (Pi.single j s')
  have e : ∀ s : Fv F v, emb (Fv F v) sk *ᵥ Pi.single j s = Pi.single (sk j) s := fun s => funext fun i => by
    simp [emb, Pi.single_apply]
  exact ⟨p, fun u hu => by rw [← mulVec_smul, h0 u hu, mulVec_zero], by rw [(vec_sub h a p).1, h1, e], by rw [(vec_sub h a p).2, h2, e]⟩

theorem vec_inc (h : IsSec σ t sec) {J x y j₀ j₁ ε} (a : PX σ t J b x y j₀ j₁ ε) :
    v1 t b (incV F x) = Pi.single j₀ 1 ∧ v2 σ t J b (incV F x) = Pi.single j₁ ε ∧
      v1 t b (incV F y) = Pi.single j₁ 1 ∧ v2 σ t J b (incV F y) = Pi.single j₀ 1 := by
  simp only [v1, v2, incV, (h.inc _).1, (h.inc _).2]
  exact ⟨a.x1, a.x2, a.y1, a.y2⟩

theorem vec_smul {J : Matrix (Fin n) (Fin n) E} (e : AE F E) (p : Fin n → AE F E) :
    v1 t b (e • p) = piW t e • v1 t b p ∧ v2 σ t J b (e • p) = piW (t.comp σ) e • v2 σ t J b p := by
  simp only [v1, v2, ← mulVec_smul, Pi.smul_apply, smul_eq_mul, map_mul]
  exact ⟨rfl, rfl⟩

theorem vmv {k : Type} [Field k] (i : Fin n) (j : Fin d) (a b : k) : vecMulVec (Pi.single i a) (Pi.single j b) = single i j (a * b) := by
  ext p q
  simp only [vecMulVec_apply, Pi.single_apply, single_apply, eq_comm]
  split_ifs <;> simp_all

theorem sneg {k : Type} [Field k] (i : Fin n) (j : Fin d) (a : k) : single i j (-a) = -single i j a := by
  ext p q; simp only [single_apply, Matrix.neg_apply]; split_ifs <;> simp

theorem at_l {p : Fin n → AE F E} (h : At (evFin F v) p) (q : Fin d → AE F E) : At (evFin F v) (vecMulVec p q) := fun u hu => by
  ext i j
  have := congrFun (h u hu) i
  rw [Matrix.smul_apply, vecMulVec_apply, ← smul_mul_assoc, show u • p i = 0 from this, zero_mul]; rfl

theorem at_r (p : Fin n → AE F E) {q : Fin d → AE F E} (h : At (evFin F v) q) : At (evFin F v) (vecMulVec p q) := fun u hu => by
  ext i j
  have := congrFun (h u hu) j
  rw [Matrix.smul_apply, vecMulVec_apply, ← mul_smul_comm, show u • q j = 0 from this, mul_zero]; rfl

theorem col_el (h : IsSec σ t sec) {x y j₀ j₁} (a : PX σ t W.J c x y j₀ j₁ (-1)) {p : Fin n → AE F E} {i s s'}
    (h1 : v1 t b p = Pi.single i s) (h2 : v2 σ t X.J b p = Pi.single i s') :
    cW t b c (vecMulVec p (incV F x)) = single i j₀ s ∧ cB σ t X W b c (vecMulVec p (incV F x)) = single i j₁ s' := by
  rw [(rk_c (σ := σ) (X := X) (W := W) _ _).1, (rk_c _ _).2, h1, h2, (vec_inc h a).1, (vec_inc h a).2.1, vmv, vmv, mul_one, mul_neg_one, sneg, neg_neg]
  exact ⟨rfl, rfl⟩

theorem row_el (h : IsSec σ t sec) {x y i₀ i₁} (a : PX σ t X.J b x y i₀ i₁ 1) {q : Fin d → AE F E} {j s s'}
    (h1 : v1 t c q = Pi.single j s) (h2 : v2 σ t W.J c q = Pi.single j s') :
    cW t b c (vecMulVec (incV F x) q) = single i₀ j s ∧ cB σ t X W b c (vecMulVec (incV F x) q) = single i₁ j (-s') := by
  rw [(rk_c (σ := σ) (X := X) (W := W) _ _).1, (rk_c _ _).2, h1, h2, (vec_inc h a).1, (vec_inc h a).2.1, vmv, vmv, one_mul, one_mul, sneg]
  exact ⟨rfl, rfl⟩

theorem idem_smul (h : IsSec σ t sec) (l : AE F E) : piW t (idem F v • l) = piW t l ∧ piW (t.comp σ) (idem F v • l) = piW (t.comp σ) l := by
  have : evFin F v (idem F v) = 1 := ev_sgl 1
  rw [(h.smul _ _).1, (h.smul _ _).2, this, one_mul, one_mul]
  exact ⟨rfl, rfl⟩

theorem shiftA_c (h : IsSec σ t sec) {H : Plane E n n₁} {H' : Plane E d d₁} {i₀ i₁ j₀ j₁} (a : PX σ t X.J b H.x H.y i₀ i₁ 1)
    (a' : PX σ t W.J c H'.x H'.y j₀ j₁ (-1)) (l : (AE F E)ˣ) :
    cW t b c (idem F v • shiftA H H' l) = single i₀ j₁ (piW t l) ∧
      cB σ t X W b c (idem F v • shiftA H H' l) = single i₁ j₀ (-piW (t.comp σ) l) := by
  have e : idem F v • shiftA H H' l = vecMulVec ((idem F v • (l : AE F E)) • incV F H.x) (incV F H'.y) := by
    rw [shiftA, ← smul_assoc, smul_vecMulVec]
  rw [e, (rk_c (σ := σ) (X := X) (W := W) _ _).1, (rk_c _ _).2, (vec_smul (σ := σ) (J := X.J) _ _).1, (vec_smul (σ := σ) (J := X.J) _ _).2, (vec_inc h a).1, (vec_inc h a).2.1,
    (vec_inc h a').2.2.1, (vec_inc h a').2.2.2, (idem_smul h _).1, (idem_smul h _).2, ← Pi.single_smul, ← Pi.single_smul, vmv, vmv]
  simp [sneg]

theorem shiftB_c (h : IsSec σ t sec) {H : Plane E n n₁} {H' : Plane E d d₁} {i₀ i₁ j₀ j₁} (a : PX σ t X.J b H.x H.y i₀ i₁ 1)
    (a' : PX σ t W.J c H'.x H'.y j₀ j₁ (-1)) (l : (AE F E)ˣ) :
    cB σ t X W b c (idem F v • shiftB σ H H' l) = single i₀ j₁ (piW t l) ∧
      -cW t b c (idem F v • shiftB σ H H' l) = single i₁ j₀ (-piW (t.comp σ) l) := by
  have e : idem F v • shiftB σ H H' l = vecMulVec ((idem F v • cA σ (l : AE F E)) • incV F H.y) (incV F H'.x) := by
    rw [shiftB, ← smul_assoc, smul_vecMulVec]
  rw [e, (rk_c (σ := σ) (X := X) (W := W) _ _).1, (rk_c _ _).2, (vec_smul (σ := σ) (J := X.J) _ _).1, (vec_smul (σ := σ) (J := X.J) _ _).2, (vec_inc h a).2.2.1, (vec_inc h a).2.2.2,
    (vec_inc h a').1, (vec_inc h a').2.1, (idem_smul h _).1, (idem_smul h _).2, (h.conj _).1, (h.conj _).2, ← Pi.single_smul,
    ← Pi.single_smul, vmv, vmv]
  simp [sneg]

theorem inB_mem (h : IsSec σ t sec) {B : Base F E} (hb : IsSplitBasis t X.L b) {K : Subgroup (UA σ X.J)} (hK : IsStab B K) {k}
    (hk : k ∈ K) : inB t b k ∈ GlobalTheory.SplitWeil.KO (Fv F v) (Fin n) := by
  have to' : ∀ z ∈ latHat X, (fun i => piW t (z i)) ∈ splitLat t X.L := fun z hz => by
    induction hz using AddSubgroup.closure_induction with
    | mem z hz =>
      obtain ⟨a, -, ha, x, hx, rfl⟩ := hz
      exact ⟨fun i => evFin F v a ⊗ₜ[F] x i, AddSubgroup.subset_closure ⟨_, ha v, x, hx, rfl⟩, funext fun i => by
        rw [Pi.smul_apply, (h.smul _ _).1, incV, (h.inc _).1]; rfl⟩
    | zero => simp only [Pi.zero_apply, map_zero]; exact zero_mem _
    | add a b _ _ ha hb => simp only [Pi.add_apply, map_add]; exact add_mem ha hb
    | neg a _ ha => simp only [Pi.neg_apply, map_neg]; exact neg_mem ha
  have fr : ∀ y ∈ latLoc F X.L v, ∃ z ∈ latHat X, (fun i => piW t (z i)) = splitVec t y := fun y hy => by
    induction hy using AddSubgroup.closure_induction with
    | mem y hy =>
      obtain ⟨a, ha, x, hx, rfl⟩ := hy
      refine ⟨sgl v a • incV F x, AddSubgroup.subset_closure ⟨sgl v a, map_zero (InfiniteAdeleRing.ringEquiv_mixedSpace F), fun u => ?_,
        x, hx, rfl⟩, funext fun i => by rw [Pi.smul_apply, (h.smul _ _).1, incV, (h.inc _).1, ev_sgl]; rfl⟩
      rcases eq_or_ne u v with rfl | hu
      · rwa [ev_sgl]
      · rw [show evFin F u (sgl v a) = 0 from evalV_singleFin_ne hu a]; exact zero_mem _
    | zero => exact ⟨0, zero_mem _, funext fun _ => (map_zero _).trans (map_zero _).symm⟩
    | add a b _ _ ha hb =>
      obtain ⟨p, p1, p2⟩ := ha
      obtain ⟨q, q1, q2⟩ := hb
      exact ⟨p + q, add_mem p1 q1, funext fun i => by
        rw [Pi.add_apply, map_add, congrFun p2 i, congrFun q2 i]; exact (map_add _ _ _).symm⟩
    | neg a _ ha =>
      obtain ⟨p, p1, p2⟩ := ha
      exact ⟨-p, neg_mem p1, funext fun i => by rw [Pi.neg_apply, map_neg, congrFun p2 i]; exact (map_neg _ _).symm⟩
  have key : ∀ k ∈ K, ∀ i j, (inB t b k).1 i j ∈ 𝒪[Fv F v] := fun k hk i j => by
    obtain ⟨y, hy, e⟩ := (hb (Pi.single j 1)).1 fun i => by rw [Pi.single_apply]; split_ifs; exacts [one_mem _, zero_mem _]
    obtain ⟨z, hz, e'⟩ := fr y hy
    have := hb.mem_iff.1 (to' _ (((hK k).1 hk).2 z hz).1) i
    rw [show (fun i => piW t ((mat k *ᵥ z) i)) = (mat k).map (piW t) *ᵥ fun i => piW t (z i) from
      funext fun i => RingHom.map_mulVec _ _ _ i, e', e, mulVec_mulVec, mulVec_mulVec, mulVec_single_one] at this
    exact (int_iff _).1 this
  refine (mem_KO_iff _).2 ⟨key k hk, ?_⟩
  rw [show (inB t b k)⁻¹ = inB t b k⁻¹ by simp [inB, mul_assoc]]
  exact key _ (inv_mem hk)

end PositivityTheory.ThKG.Std
