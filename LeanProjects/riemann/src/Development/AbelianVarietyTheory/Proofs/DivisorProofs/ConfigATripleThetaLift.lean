import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLocPart
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsLocIsoRefl
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InsP
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSplitPlaceAdelicMatrixGivenComponents
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MatchedMapsGlobalSum
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTensorLatticePointOfIntegralSplitPlaceCoor

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes ValuativeRel
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.StdPairCone GlobalTheory.EvZeroStd
open GlobalTheory.Doubling (absE)

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.EvZeroCoords

section Skip

variable (b a' : ℕ)

theorem skip_lt (j : Fin (b + a')) : skip 0 (b + 1) j < b + 2 + a' := by
  have := j.2; unfold skip; split_ifs <;> omega

theorem skip_ne_zero (j : ℕ) : skip 0 (b + 1) j ≠ 0 := by unfold skip; split_ifs <;> omega

theorem skip_ne_last (j : ℕ) : skip 0 (b + 1) j ≠ b + 1 := by unfold skip; split_ifs <;> omega

theorem skip_inj {j j' : ℕ} (h : skip 0 (b + 1) j = skip 0 (b + 1) j') : j = j' := by
  unfold skip at h; split_ifs at h <;> omega

theorem trichotomy (i : Fin (b + 2 + a')) :
    i.1 = 0 ∨ i.1 = b + 1 ∨ ∃ k : Fin (b + a'), i.1 = skip 0 (b + 1) k := by
  rcases Nat.eq_zero_or_pos i.1 with h | h
  · exact Or.inl h
  by_cases h' : i.1 = b + 1
  · exact Or.inr (Or.inl h')
  right; right
  have hi := i.2
  by_cases h'' : i.1 ≤ b
  · refine ⟨⟨i.1 - 1, by omega⟩, ?_⟩; simp only [skip]; split_ifs <;> omega
  · refine ⟨⟨i.1 - 2, by omega⟩, ?_⟩; simp only [skip]; split_ifs <;> omega

variable {K : Type} [Field K]

theorem mul_insP_apply {m : Type} [Fintype m] (X : Matrix m (Fin (b + 2 + a')) K) (r : m) (j : Fin (b + a')) :
    (X * insP K b a') r j = X r ⟨skip 0 (b + 1) j, skip_lt b a' j⟩ := by
  rw [Matrix.mul_apply, Finset.sum_eq_single ⟨skip 0 (b + 1) j, skip_lt b a' j⟩]
  · simp [insP]
  · intro i _ hi
    simp only [insP, Matrix.of_apply]
    rw [if_neg (fun h => hi (Fin.ext h)), mul_zero]
  · intro h; exact absurd (Finset.mem_univ _) h

theorem insertionMatrix_mul_apply_skip {m : Type} (Y : Matrix (Fin (b + a')) m K) (k : Fin (b + a')) (l : m) :
    (insP K b a' * Y) ⟨skip 0 (b + 1) k, skip_lt b a' k⟩ l = Y k l := by
  rw [Matrix.mul_apply, Finset.sum_eq_single k]
  · simp [insP]
  · intro j _ hj
    simp only [insP, Matrix.of_apply]
    rw [if_neg (fun h => hj (Fin.ext (skip_inj b h).symm)), zero_mul]
  · intro h; exact absurd (Finset.mem_univ _) h

theorem insertionMatrix_mul_apply_eq_zero {m : Type} (Y : Matrix (Fin (b + a')) m K) (i : Fin (b + 2 + a')) (l : m)
    (hi : ∀ k : Fin (b + a'), i.1 ≠ skip 0 (b + 1) k) : (insP K b a' * Y) i l = 0 := by
  rw [Matrix.mul_apply]
  refine Finset.sum_eq_zero fun k _ => ?_
  simp [insP, hi k]

theorem mul_insP_eq {c : Matrix (Fin (b + 2 + a')) (Fin (b + 2 + a')) K} {N : Matrix (Fin (b + 2 + a')) (Fin (b + a')) K}
    (h : ∀ (i : Fin (b + 2 + a')) (j : Fin (b + a')), i.1 = skip 0 (b + 1) j → ∀ r, c r i = N r j) :
    c * insP K b a' = N := by
  ext r j; rw [mul_insP_apply]; exact h _ j rfl r

end Skip

section Forms

variable {F E : Type} [Field F] [Field E] [Algebra F E]

theorem form_swap {σ : E →ₐ[F] E} (hσ : ∀ x, σ (σ x) = x) {n : ℕ} {J : Matrix (Fin n) (Fin n) E}
    (hJ : ∀ i j, σ (J j i) = -J i j) (p q : Fin n → E) : form σ J p q = -σ (form σ J q p) := by
  simp only [form, dotProduct, Matrix.mulVec, map_sum, map_mul, hσ, hJ, Finset.mul_sum, ← Finset.sum_neg_distrib]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

theorem mul_vecMulVec_mul {K : Type} [CommRing K] {m n l o : Type} [Fintype n] [Fintype l]
    (A : Matrix m n K) (p : n → K) (q : l → K) (B : Matrix l o K) :
    A * Matrix.vecMulVec p q * B = Matrix.vecMulVec (A *ᵥ p) (q ᵥ* B) := by
  ext i j
  simp only [Matrix.mul_apply, Matrix.vecMulVec_apply, Matrix.mulVec, Matrix.vecMul, dotProduct, Finset.sum_mul,
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

end Forms

end GlobalTheory.EvZeroCoords

namespace GlobalTheory.EvZeroCoords

section Glob

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem map_emb {v : Pl F} (τ : E →ₐ[F] Fv F v) {p m m₁ : ℕ} (z : Matrix (Fin p) (Fin m₁) (AE F E))
    (ι : Matrix (Fin m) (Fin m₁) E) :
    (incM F (1 : Matrix (Fin p) (Fin p) E) * z * (incM F ι)ᵀ).map (piW τ) = z.map (piW τ) * (ι.map τ)ᵀ := by
  have h1 : incM F (1 : Matrix (Fin p) (Fin p) E) = 1 := by simp [incM]
  have h2 : (incM F ι).map (piW τ) = ι.map τ := by
    ext i j; simp [incM, GlobalTheory.LatFill.piW_inclR]
  rw [h1, Matrix.one_mul, Matrix.map_mul, Matrix.transpose_map, h2]

theorem map_line {v : Pl F} (τ : E →ₐ[F] Fv F v) {p m : ℕ} (y : Fin p → AE F E) (x : Fin m → E) :
    (Matrix.vecMulVec y (incV F x)).map (piW τ) = Matrix.vecMulVec (fun i => piW τ (y i)) (fun j => τ (x j)) := by
  ext i j; simp [Matrix.vecMulVec_apply, incV, GlobalTheory.LatFill.piW_inclR]

end Glob

section Field

variable {F E K : Type} [Field F] [Field E] [Algebra F E] [Field K] [Algebra F K]

theorem row_form (σ : E →ₐ[F] E) (t : E →ₐ[F] K) {n m : ℕ} (J : Matrix (Fin n) (Fin n) E) (x : Fin n → E)
    (ι : Matrix (Fin n) (Fin m) E) (j : Fin m) :
    ∑ r, t (x r) * (J.map t * ι.map (t.comp σ)) r j = t (form σ J x (ι *ᵥ Pi.single j 1)) := by
  simp [form, Matrix.mul_apply, dotProduct, Matrix.mulVec, map_sum, map_mul, Pi.single_apply, Finset.mul_sum]

theorem col_form (σ : E →ₐ[F] E) (t : E →ₐ[F] K) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (x z : Fin n → E) :
    ∑ r, (J.map t *ᵥ fun s => t (σ (x s))) r * t (z r) = t (form σ J z x) := by
  simp [form, dotProduct, Matrix.mulVec, map_sum, map_mul, Finset.mul_sum, Finset.sum_mul, mul_comm, mul_left_comm]

end Field

end GlobalTheory.EvZeroCoords

namespace GlobalTheory.EvZeroCoords

theorem coords_evZero : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    (B : Base F E) (b a' : ℕ) (G : Geo σ (b + 2) a') (G₁ : Geo σ b a') (H : Plane E (b + 2) b)
    (H' : Plane E (b + 2 + a') (b + a')), CfgA B G G₁ H H' → ∀ (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W)
    (om₁ : Rep σ G₁.V G₁.W) (om₁' : Rep σ G₁.V' G₁.W), IsTriple B G X om om' → IsTriple B G₁ X om₁ om₁' → ∀ v : B.P,
      (∀ z : Matrix (Fin a') (Fin (b + a')) (AE F E),
        GlobalTheory.FlipMatch.coX (B.τ v) (G.V'.bas v) (G.W.bas v) (incM F (1 : Matrix (Fin a') (Fin a') E) * z * (incM F H'.ι)ᵀ) =
                     GlobalTheory.FlipMatch.coX (B.τ v) (G₁.V'.bas v) (G₁.W.bas v) z * (insP (Fv F v) b a')ᵀ ∧
        GlobalTheory.FlipMatch.coY σ G.V' G.W (B.τ v) (G.V'.bas v) (G.W.bas v)
                     (incM F (1 : Matrix (Fin a') (Fin a') E) * z * (incM F H'.ι)ᵀ) =
          GlobalTheory.FlipMatch.coY σ G₁.V' G₁.W (B.τ v) (G₁.V'.bas v) (G₁.W.bas v) z * (insP (Fv F v) b a')ᵀ) ∧
      ∀ s r : Fin a' → Fv F v, ∃ y : Fin a' → AE F E, At (evFin F v) (Matrix.vecMulVec y (incV F H'.x)) ∧
        GlobalTheory.FlipMatch.coX (B.τ v) (G.V'.bas v) (G.W.bas v) (Matrix.vecMulVec y (incV F H'.x)) =
          Matrix.vecMulVec s (Pi.single 0 1) ∧
        GlobalTheory.FlipMatch.coY σ G.V' G.W (B.τ v) (G.V'.bas v) (G.W.bas v) (Matrix.vecMulVec y (incV F H'.x)) =
          Matrix.vecMulVec r (Pi.single ⟨b + 1, by omega⟩ 1) := by
  intro F E _ _ _ _ _ σ B b a' G G₁ H H' hC X om om' om₁ om₁' hT hT₁ v
  have hσ : ∀ x, σ (σ x) = x := cm_conj_conj hT.base.cm
  have hA := hC.hH'
  have hbas := hA.bas v
  have hskew : ∀ i j, σ (G.W.J j i) = -G.W.J i j := hT.geo.hW.skew
  set t := B.τ v with ht
  set c := G.W.bas v with hc
  set c₁ := G₁.W.bas v with hc₁
  have hcP : c.1 * insP (Fv F v) b a' = H'.ι.map t * c₁.1 :=
    mul_insP_eq b a' fun i j hij r => (hbas i).2.2 j hij r

  have horthX : ∀ u, form σ G.W.J H'.x (H'.ι *ᵥ u) = 0 := fun u => by
    rw [form_swap hσ hskew, (hA.orth u).1, map_zero, neg_zero]
  have horthY : ∀ u, form σ G.W.J H'.y (H'.ι *ᵥ u) = 0 := fun u => by
    rw [form_swap hσ hskew, (hA.orth u).2, map_zero, neg_zero]
  refine ⟨fun z => ⟨?_, ?_⟩, fun s r => ?_⟩
  · simp only [GlobalTheory.FlipMatch.coX]
    rw [map_emb, hC.eV]
    have key : (c⁻¹).1 * H'.ι.map t = insP (Fv F v) b a' * (c₁⁻¹).1 := by
      calc (c⁻¹).1 * H'.ι.map t = (c⁻¹).1 * (H'.ι.map t * c₁.1) * (c₁⁻¹).1 := by
            rw [Matrix.mul_assoc _ (H'.ι.map t * c₁.1), Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one]
        _ = insP (Fv F v) b a' * (c₁⁻¹).1 := by
            rw [← hcP, ← Matrix.mul_assoc, Units.inv_mul, Matrix.one_mul]
    have keyT := congrArg Matrix.transpose key
    simp only [Matrix.transpose_mul] at keyT
    simp only [Matrix.mul_assoc]
    rw [keyT]
  · simp only [GlobalTheory.FlipMatch.coY]
    rw [map_emb, hC.eV]
    have hgram : (H'.ι.map t)ᵀ * (G.W.J.map t * H'.ι.map (t.comp σ)) = G₁.W.J.map t := by
      rw [← hA.gram, Matrix.map_mul, Matrix.map_mul, Matrix.transpose_map, Matrix.mul_assoc]
      rfl
    have key2 : (c.1)ᵀ * (G.W.J.map t * H'.ι.map (t.comp σ)) = insP (Fv F v) b a' * ((c₁.1)ᵀ * G₁.W.J.map t) := by
      refine Matrix.ext fun i j => ?_
      rcases trichotomy b a' i with h0 | h1 | ⟨k, hk⟩
      · rw [insertionMatrix_mul_apply_eq_zero b a' _ i j (fun k => h0 ▸ (skip_ne_zero b k).symm), Matrix.mul_apply]
        simp only [Matrix.transpose_apply]
        rw [Finset.sum_congr rfl fun r _ => by rw [(hbas i).1 h0 r], row_form, horthX, map_zero]
      · rw [insertionMatrix_mul_apply_eq_zero b a' _ i j (fun k => h1 ▸ (skip_ne_last b k).symm), Matrix.mul_apply]
        simp only [Matrix.transpose_apply]
        rw [Finset.sum_congr rfl fun r _ => by rw [(hbas i).2.1 h1 r], row_form, horthY, map_zero]
      · obtain rfl : i = ⟨skip 0 (b + 1) k, skip_lt b a' k⟩ := Fin.ext hk
        rw [insertionMatrix_mul_apply_skip]
        calc ((c.1)ᵀ * (G.W.J.map t * H'.ι.map (t.comp σ))) ⟨skip 0 (b + 1) k, skip_lt b a' k⟩ j
            = ((H'.ι.map t * c₁.1)ᵀ * (G.W.J.map t * H'.ι.map (t.comp σ))) k j := by
              rw [Matrix.mul_apply, Matrix.mul_apply]
              simp only [Matrix.transpose_apply]
              exact Finset.sum_congr rfl fun r _ => by rw [(hbas _).2.2 k rfl r]
          _ = ((c₁.1)ᵀ * G₁.W.J.map t) k j := by
              rw [Matrix.transpose_mul, Matrix.mul_assoc, hgram]
    have key2T := congrArg Matrix.transpose key2
    simp only [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc] at key2T
    simp only [Matrix.mul_assoc, Matrix.neg_mul]
    rw [key2T]
  · have hdet : (G.V'.J.map t).det ≠ 0 := by
      have h0 := GlobalTheory.HoweNonsplitKer.det_ne_of_sig B G.V'.J hT.geo.hV'.sig
      have e := AlgHom.map_det t G.V'.J
      rw [AlgHom.mapMatrix_apply] at e
      rw [← e]; exact (map_ne_zero t).2 h0
    set wv : Fin a' → Fv F v := (G.V'.J.map t)⁻¹ *ᵥ (((G.V'.bas v)⁻¹).1ᵀ *ᵥ r) with hwv
    obtain ⟨u, hu, hu0, hu1⟩ := GlobalTheory.SplitComps.exists_mat_comps hT.base.cm (v : Pl F) t
      (Matrix.of fun i (_ : Fin 1) => ((G.V'.bas v).1 *ᵥ s) i) (Matrix.of fun i (_ : Fin 1) => wv i)
    have hy0 : (fun i => piW t (u i 0)) = (G.V'.bas v).1 *ᵥ s := funext fun i => by
      have := congrFun (congrFun hu0 i) 0; simpa using this
    have hy1 : (fun i => piW (t.comp σ) (u i 0)) = wv := funext fun i => by
      have := congrFun (congrFun hu1 i) 0; simpa using this
    refine ⟨fun i => u i 0, ?_, ?_, ?_⟩
    · intro a ha
      refine Matrix.ext fun i j => ?_
      have := congrFun (congrFun (hu a ha) i) 0
      simp only [Matrix.smul_apply, Matrix.zero_apply] at this ⊢
      rw [Matrix.vecMulVec_apply, ← smul_mul_assoc, this, zero_mul]
    · simp only [GlobalTheory.FlipMatch.coX]
      rw [map_line, hy0, mul_vecMulVec_mul, Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec,
        Matrix.vecMul_transpose]
      have hq : (fun j => t (H'.x j)) = c.1 *ᵥ Pi.single 0 1 := funext fun r => by
        simp [Matrix.mulVec, dotProduct, Pi.single_apply, (hbas 0).1 (by simp) r]
      rw [hq, Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec]
    · simp only [GlobalTheory.FlipMatch.coY]
      rw [map_line, hy1, Matrix.mul_assoc _ _ c.1, mul_vecMulVec_mul]
      have hv : (fun j => t (σ (H'.x j))) ᵥ* ((G.W.J.map t)ᵀ * c.1) = -Pi.single ⟨b + 1, by omega⟩ 1 := by
        rw [← Matrix.vecMul_vecMul, Matrix.vecMul_transpose]
        funext i
        simp only [Matrix.vecMul, dotProduct, Pi.neg_apply]
        rcases trichotomy b a' i with h0 | h1 | ⟨k, hk⟩
        · rw [Finset.sum_congr rfl fun r _ => by rw [(hbas i).1 h0 r], col_form, hA.xx, map_zero]
          rw [Pi.single_apply, if_neg (fun h => by rw [h] at h0; simp at h0), neg_zero]
        · rw [Finset.sum_congr rfl fun r _ => by rw [(hbas i).2.1 h1 r], col_form, form_swap hσ hskew, hA.xy,
            map_one, map_neg, map_one]
          rw [Pi.single_apply, if_pos (Fin.ext h1)]
        · rw [Pi.single_apply, if_neg (fun h => by rw [h] at hk; exact skip_ne_last b k hk.symm), neg_zero]
          rw [Finset.sum_congr rfl fun r _ => by rw [(hbas i).2.2 k hk r]]
          simp only [Matrix.mul_apply, Finset.mul_sum]
          rw [Finset.sum_comm]
          refine Finset.sum_eq_zero fun l _ => ?_
          simp only [← mul_assoc]
          rw [← Finset.sum_mul]
          have hz : (fun r => H'.ι r l) = H'.ι *ᵥ Pi.single l 1 := by
            funext r; simp [Matrix.mulVec, dotProduct, Pi.single_apply]
          have h3 := col_form σ t G.W.J H'.x (fun r => H'.ι r l)
          rw [hz, (hA.orth _).1, map_zero] at h3
          simp only [Matrix.map_apply]
          rw [h3, zero_mul]
      have hr : ((G.V'.bas v).1ᵀ * G.V'.J.map t) *ᵥ wv = r := by
        rw [hwv, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Matrix.mul_assoc (G.V'.bas v).1ᵀ,
          Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.2 hdet), Matrix.mul_one, ← Matrix.transpose_mul, Units.inv_mul,
          Matrix.transpose_one, Matrix.one_mulVec]
      rw [show (fun j => (t.comp σ) (H'.x j)) = fun j => t (σ (H'.x j)) from rfl, hv, hr]
      refine Matrix.ext fun i j => ?_
      simp [Matrix.vecMulVec_apply]

end GlobalTheory.EvZeroCoords
