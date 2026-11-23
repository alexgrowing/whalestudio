import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConeIntZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HaarOIsAddHaar
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GoodModelEigenContinuous
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CrdQ
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SeesawTypeBTripleHypothesisFormStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ImportsRestExtra
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSplitPlaceAdelicMatrixGivenComponents
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianTensorSkewHermitianSplitSymplecticPair
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HeisenbergOperatorIsotropicTranslationCharSplit
open MeasureTheory Filter NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ConeSoB GlobalTheory.StdPairLoc
open scoped Matrix GlobalTheory.VacAny
attribute [local instance] GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.measFv GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.borelFv

noncomputable section

namespace GlobalTheory.ConeSoB.Chars

open GlobalTheory.FlipMatch (pairM coX coY)

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem iota_schr_char (B : Base F E) {a a' : ℕ} (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W)
    (om' : Rep σ G.V' G.W) (hT : IsTriple B G X om om') {v : Pl F} (t : E →ₐ[F] Fv F v) (ι)
    (hι : G.M'.IsLinBar B.ψ t 1 1 ι) (u : Matrix (Fin a') (Fin (a + a')) (AE F E)) (hu : At (evFin F v) u)
    (hu0 : u.map (piW (t.comp σ)) = 0) (φ) (hφ : φ ∈ SB (Fin a' × Fin (a + a') → Fv F v)) (Z) :
    ι (schr (GlobalTheory.LatVac.psiAt B.ψ v) (GlobalTheory.LatVac.locCo G.M'.co v u) φ) Z =
      GlobalTheory.LatVac.psiAt B.ψ v (-pairM Z (u.map (piW t))) * ι φ Z := by
  obtain ⟨dV, dW⟩ := GlobalTheory.GramDet.gram_det_ne_zero F E σ B a a' G X om om' hT
  have hY : coY σ G.V' G.W t 1 1 u = 0 := by
    simp only [coY, hu0, Matrix.mul_zero, Matrix.zero_mul, neg_zero]
  have hX : coX t 1 1 u = u.map (piW t) := by
    simp [coX]
  have h := (GlobalTheory.HeisFlip.heis_trans_char hT.base.cm G.V' G.W hT.geo.hV'.herm hT.geo.hW.skew dV dW G.M' B.ψ hT.base.std
    t 1 1 u hu (by rw [hY]; simp [pairM]) φ hφ _ (GlobalTheory.SchrSB.schr_mem_SB B.ψ hT.base.std.1 v _ φ hφ)
    (GlobalTheory.VacBridge.rho_acts_locCo G.M'.co B.ψ v u hu φ)).2 ι hι Z
  rw [h, hY, hX, add_zero, GlobalTheory.LatVac.psiAt_apply]

theorem piW_incV {v : Pl F} (t : E →ₐ[F] Fv F v) {n : ℕ} (x : Fin n → E) (i : Fin n) :
    piW t (incV F x i) = t (x i) := GlobalTheory.HTensSplitPair.piW_inclR_eq t (x i)

theorem piW_incM {v : Pl F} (t : E →ₐ[F] Fv F v) {m n : Type} (A : Matrix m n E) :
    (incM F A).map (piW t) = A.map t := Matrix.ext fun i j => GlobalTheory.HTensSplitPair.piW_inclR_eq t (A i j)

theorem mul_mul_transpose_eq_sum {k m n p q : Type} [CommRing k] [Fintype m] [Fintype n] (P : Matrix p m k)
    (U : Matrix m n k) (Q : Matrix q n k) :
    -(P * U * Qᵀ) = ∑ i, ∑ j, Matrix.vecMulVec (fun r => P r i) (fun s => -U i j * Q s j) := by
  ext r s
  simp only [Matrix.neg_apply, Matrix.mul_apply, Matrix.sum_apply, Matrix.vecMulVec_apply, Matrix.transpose_apply,
    Finset.sum_mul]
  rw [Finset.sum_comm, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finset.sum_neg_distrib]
  exact Finset.sum_congr rfl fun j _ => by ring

theorem ev_zero_char_inv : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} (B : Base F E) {a b : ℕ}
    (G : Geo σ a (b + 2)) (G₁ : Geo σ a b) (H : Plane E (b + 2) b) (H' : Plane E (a + (b + 2)) (a + b)), CfgB B G G₁ H H' →
    ∀ (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W) (om₁ : Rep σ G₁.V G₁.W) (om₁' : Rep σ G₁.V' G₁.W),
    IsTriple B G X om om' → IsTriple B G₁ X om₁ om₁' →
    ∀ (L : ((Fin (b + 2) × Fin (a + (b + 2)) → Fv F B.v₁) → ℂ) →ₗ[ℂ] (Fin b × Fin (a + b) → Fv F B.v₁) → ℂ),
    (∀ φ ∈ SB (Fin (b + 2) × Fin (a + (b + 2)) → Fv F B.v₁), L φ ∈ SB (Fin b × Fin (a + b) → Fv F B.v₁)) →
    (∀ z : Matrix (Fin b) (Fin (a + b)) (AE F E), At (evFin F B.v₁) z → ∀ φ ∈ SB (Fin (b + 2) × Fin (a + (b + 2)) → Fv F B.v₁),
      L (schr (GlobalTheory.LatVac.psiAt B.ψ B.v₁) (GlobalTheory.LatVac.locCo G.M'.co B.v₁ (incM F H.ι * z * (incM F H'.ι)ᵀ)) φ) =
        schr (GlobalTheory.LatVac.psiAt B.ψ B.v₁) (GlobalTheory.LatVac.locCo G₁.M'.co B.v₁ z) (L φ)) →
    (∀ u ∈ isoB H H', At (evFin F B.v₁) u → ∀ φ ∈ SB (Fin (b + 2) × Fin (a + (b + 2)) → Fv F B.v₁),
      L (schr (GlobalTheory.LatVac.psiAt B.ψ B.v₁) (GlobalTheory.LatVac.locCo G.M'.co B.v₁ u) φ) = L φ) →
    ∀ ι ι₁, G.M'.IsLinBar B.ψ B.τ₁ 1 1 ι → G₁.M'.IsLinBar B.ψ B.τ₁ 1 1 ι₁ →
    ∀ U : Matrix (Fin (b + 2)) (Fin (a + (b + 2))) (Fv F B.v₁),
      (∀ (r : Fin (a + (b + 2)) → Fv F B.v₁) (c : Fin b → Fv F B.v₁),
        ∑ i, ∑ j, U i j * insS (0 : Matrix (Fin b) (Fin (a + b)) (Fv F B.v₁)) r c 0 i j = 0) →
      ∀ φ ∈ SB (Fin (b + 2) × Fin (a + (b + 2)) → Fv F B.v₁), ∃ φ' ∈ SB (Fin (b + 2) × Fin (a + (b + 2)) → Fv F B.v₁), ι₁ (L φ') 0 = ι₁ (L φ) 0 ∧
        ∀ Z : Matrix (Fin (b + 2)) (Fin (a + (b + 2))) (Fv F B.v₁), ι φ' (GlobalTheory.PlaneBasis.crdP B.τ₁ H * Z * GlobalTheory.PlaneBasis.crdQ B.τ₁ H') =
          GlobalTheory.LatVac.psiAt B.ψ B.v₁ (∑ i, ∑ j, U i j * Z i j) * ι φ (GlobalTheory.PlaneBasis.crdP B.τ₁ H * Z * GlobalTheory.PlaneBasis.crdQ B.τ₁ H') := by
  intro F E _ _ _ _ _ σ B a b G G₁ H H' hC X om om' om₁ om₁' hT hT₁ L hLSB hheis hinv ι ι₁ hι hι₁ U hU
  have hψ : Continuous B.ψ := hT.base.std.1
  obtain ⟨hP, hQ⟩ := GlobalTheory.T.seesaw_type_b_triple_hypothesis_form B G G₁ H H' hC X om om' om₁ om₁' hT hT₁
  let Good : Matrix (Fin (b + 2)) (Fin (a + (b + 2))) (Fv F B.v₁) → Prop := fun M =>
    ∀ φ ∈ SB (Fin (b + 2) × Fin (a + (b + 2)) → Fv F B.v₁), ∃ φ' ∈ SB (Fin (b + 2) × Fin (a + (b + 2)) → Fv F B.v₁),
      ι₁ (L φ') 0 = ι₁ (L φ) 0 ∧ ∀ Z, ι φ' Z = GlobalTheory.LatVac.psiAt B.ψ B.v₁ (-pairM Z M) * ι φ Z
  have g0 : Good 0 := fun φ hφ => ⟨φ, hφ, rfl, fun Z => by simp [pairM]⟩
  have gadd : ∀ M N, Good M → Good N → Good (M + N) := by
    intro M N hM hN φ hφ
    obtain ⟨φ₁, h₁, e₁, f₁⟩ := hM φ hφ
    obtain ⟨φ₂, h₂, e₂, f₂⟩ := hN φ₁ h₁
    refine ⟨φ₂, h₂, e₂.trans e₁, fun Z => ?_⟩
    rw [f₂, f₁, ← mul_assoc, ← AddChar.map_add_eq_mul]
    congr 2
    simp only [pairM, Matrix.add_apply, mul_add, Finset.sum_add_distrib]
    ring
  have gu : ∀ u : Matrix (Fin (b + 2)) (Fin (a + (b + 2))) (AE F E), At (evFin F B.v₁) u →
      u.map (piW (B.τ₁.comp σ)) = 0 →
      (∀ φ ∈ SB (Fin (b + 2) × Fin (a + (b + 2)) → Fv F B.v₁),
        ι₁ (L (schr (GlobalTheory.LatVac.psiAt B.ψ B.v₁) (GlobalTheory.LatVac.locCo G.M'.co B.v₁ u) φ)) 0 = ι₁ (L φ) 0) →
      Good (u.map (piW B.τ₁)) := fun u hu hu0 h φ hφ =>
    ⟨_, GlobalTheory.SchrSB.schr_mem_SB B.ψ hψ B.v₁ _ φ hφ, h φ hφ, iota_schr_char B G X om om' hT B.τ₁ ι hι u hu hu0 φ hφ⟩

  have g1 : ∀ z : Fin (a + (b + 2)) → Fv F B.v₁, Good (Matrix.vecMulVec (fun r => B.τ₁ (H.x r)) z) := by
    intro z
    obtain ⟨w, hw, hw0, hw1⟩ := GlobalTheory.SplitComps.exists_mat_comps hT.base.cm B.v₁ B.τ₁
      (Matrix.of fun (_ : Unit) s => z s) 0
    have hat : At (evFin F B.v₁) (Matrix.vecMulVec (incV F H.x) (w ())) := by
      intro r hr
      ext i j
      have h : r • w () j = 0 := congrFun (congrFun (hw r hr) ()) j
      rw [Matrix.smul_apply, Matrix.vecMulVec_apply, ← mul_smul_comm, h, mul_zero, Matrix.zero_apply]
    have h := gu _ hat (by
      ext i j
      have h : piW (B.τ₁.comp σ) (w () j) = 0 := congrFun (congrFun hw1 ()) j
      rw [Matrix.map_apply, Matrix.vecMulVec_apply, map_mul, h, mul_zero, Matrix.zero_apply])
      fun φ hφ => by rw [hinv _ (Or.inl ⟨_, rfl⟩) hat φ hφ]
    convert h using 1
    ext i j
    have h : piW B.τ₁ (w () j) = z j := congrFun (congrFun hw0 ()) j
    rw [Matrix.map_apply, Matrix.vecMulVec_apply, Matrix.vecMulVec_apply, map_mul, h, piW_incV]

  have g2 : ∀ y : Fin b → Fv F B.v₁, Good (Matrix.vecMulVec (H.ι.map B.τ₁ *ᵥ y) (fun s => B.τ₁ (H'.x s))) := by
    intro y
    obtain ⟨w, hw, hw0, hw1⟩ := GlobalTheory.SplitComps.exists_mat_comps hT.base.cm B.v₁ B.τ₁
      (Matrix.of fun (_ : Unit) s => y s) 0
    have hat : At (evFin F B.v₁) (Matrix.vecMulVec (incM F H.ι *ᵥ w ()) (incV F H'.x)) := by
      intro r hr
      ext i j
      have h : r • w () = 0 := congrFun (hw r hr) ()
      rw [Matrix.smul_apply, Matrix.vecMulVec_apply, ← smul_mul_assoc, ← Pi.smul_apply, ← Matrix.mulVec_smul, h,
        Matrix.mulVec_zero, Pi.zero_apply, zero_mul, Matrix.zero_apply]
    have hm : ∀ (t : E →ₐ[F] Fv F B.v₁) i, piW t ((incM F H.ι *ᵥ w ()) i) = (H.ι.map t *ᵥ (w.map (piW t)) ()) i := by
      intro t i
      rw [RingHom.map_mulVec, piW_incM]
      rfl
    have h := gu _ hat (by
      ext i j
      rw [Matrix.map_apply, Matrix.vecMulVec_apply, map_mul, hm, hw1]
      simp [Matrix.mulVec, dotProduct])
      fun φ hφ => by rw [hinv _ (Or.inr ⟨_, rfl⟩) hat φ hφ]
    convert h using 1
    ext i j
    rw [Matrix.map_apply, Matrix.vecMulVec_apply, Matrix.vecMulVec_apply, map_mul, hm, hw0, piW_incV]
    rfl

  have g3 : ∀ Y : Matrix (Fin b) (Fin (a + b)) (Fv F B.v₁), Good (H.ι.map B.τ₁ * Y * (H'.ι.map B.τ₁)ᵀ) := by
    intro Y
    obtain ⟨w, hw, hw0, hw1⟩ := GlobalTheory.SplitComps.exists_mat_comps hT.base.cm B.v₁ B.τ₁ Y 0
    have hat : At (evFin F B.v₁) (incM F H.ι * w * (incM F H'.ι)ᵀ) := by
      intro r hr
      rw [← Matrix.smul_mul, ← Matrix.mul_smul, hw r hr, Matrix.mul_zero, Matrix.zero_mul]
    have hm : ∀ t : E →ₐ[F] Fv F B.v₁, (incM F H.ι * w * (incM F H'.ι)ᵀ).map (piW t) =
        H.ι.map t * w.map (piW t) * (H'.ι.map t)ᵀ := by
      intro t
      rw [Matrix.map_mul, Matrix.map_mul, Matrix.transpose_map, piW_incM, piW_incM]
    have h := gu _ hat (by rw [hm, hw1, Matrix.mul_zero, Matrix.zero_mul]) fun φ hφ => by
      rw [hheis w hw φ hφ, iota_schr_char B G₁ X om₁ om₁' hT₁ B.τ₁ ι₁ hι₁ w hw hw1 _ (hLSB φ hφ)]
      simp [pairM]
    rwa [hm, hw0] at h

  have hlast : ∀ i j, i.1 = b + 1 → U i j = 0 := by
    intro i j hi
    have h := hU (Pi.single j 1) 0
    rw [Finset.sum_eq_single i, Finset.sum_eq_single j] at h
    · simpa [insS, hi] using h
    · intro j' _ hj'
      simp [insS, hi, hj']
    · simp
    · intro i' _ hi'
      have : i'.1 ≠ b + 1 := fun e => hi' (Fin.ext (e.trans hi.symm))
      simp [insS, this]
    · simp
  have hmid : ∀ (i : Fin (b + 2)) (j : Fin (a + (b + 2))), i.1 ≠ 0 → i.1 ≠ b + 1 → j.1 = a + b + 1 → U i j = 0 := by
    intro i j hi0 hi1 hj
    have h := hU 0 (Pi.single ⟨i.1 - 1, by have := i.2; omega⟩ 1)
    have hja : ¬ j.1 < a := by omega
    have hja' : j.1 ≠ a := by omega
    rw [Finset.sum_eq_single i, Finset.sum_eq_single j] at h
    · simpa [insS, hi0, hi1, hja, hja', dif_pos hj] using h
    · intro j' _ hj'
      have : j'.1 ≠ a + b + 1 := fun e => hj' (Fin.ext (e.trans hj.symm))
      simp [insS, hi0, hi1, this]
    · simp
    · intro i' _ hi'
      refine Finset.sum_eq_zero fun j' _ => ?_
      simp only [insS]
      split_ifs with h1 h2 h3 h4 h5 h6
      any_goals simp
      right
      refine Pi.single_eq_of_ne (fun e => hi' (Fin.ext ?_)) _
      have := congrArg Fin.val e
      simp only at this
      omega
    · simp
  have gall : Good (-(GlobalTheory.PlaneBasis.basV B.τ₁ H * U * (GlobalTheory.PlaneBasis.basW B.τ₁ H')ᵀ)) := by
    rw [mul_mul_transpose_eq_sum]
    refine Finset.sum_induction _ Good gadd g0 fun i _ => Finset.sum_induction _ Good gadd g0 fun j _ => ?_
    by_cases hi0 : i.1 = 0
    · simpa only [GlobalTheory.PlaneBasis.basV, dif_pos hi0] using g1 _
    by_cases hi1 : i.1 = b + 1
    · convert g0 using 1
      ext r s
      simp [hlast i j hi1, Matrix.vecMulVec_apply]
    by_cases hj1 : j.1 = a + b + 1
    · convert g0 using 1
      ext r s
      simp [hmid i j hi0 hi1 hj1, Matrix.vecMulVec_apply]
    by_cases hja : j.1 = a
    · convert g2 (Pi.single ⟨i.1 - 1, by have := i.2; omega⟩ (-U i j)) using 1
      ext r s
      simp only [GlobalTheory.PlaneBasis.basV, GlobalTheory.PlaneBasis.basW, dif_neg hi0, dif_neg hi1, dif_pos hja, Matrix.vecMulVec_apply]
      simp [Matrix.mulVec, dotProduct, Pi.single_apply, mul_assoc]
    by_cases hj : j.1 < a
    · convert g3 (Matrix.single ⟨i.1 - 1, by have := i.2; omega⟩ ⟨j.1, by omega⟩ (-U i j)) using 1
      ext r s
      simp [GlobalTheory.PlaneBasis.basV, GlobalTheory.PlaneBasis.basW, hi0, hi1, hja, hj1, hj, Matrix.vecMulVec_apply, mul_assoc,
        Matrix.mul_apply, Matrix.single, ite_and]
    · convert g3 (Matrix.single ⟨i.1 - 1, by have := i.2; omega⟩ ⟨j.1 - 1, by have := j.2; omega⟩ (-U i j)) using 1
      ext r s
      simp [GlobalTheory.PlaneBasis.basV, GlobalTheory.PlaneBasis.basW, hi0, hi1, hja, hj1, hj, Matrix.vecMulVec_apply, mul_assoc,
        Matrix.mul_apply, Matrix.single, ite_and]
  intro φ hφ
  obtain ⟨φ', hφ', e, f⟩ := gall φ hφ
  refine ⟨φ', hφ', e, fun Z => ?_⟩
  rw [f]
  congr 2
  rw [GlobalTheory.HeisFlip.pairM_mul, GlobalTheory.PlaneBasis.crdP, GlobalTheory.PlaneBasis.crdQ, Matrix.transpose_nonsing_inv,
    Matrix.transpose_transpose, Matrix.transpose_nonsing_inv, Matrix.mul_neg, Matrix.neg_mul, Matrix.mul_assoc,
    Matrix.mul_assoc, Matrix.mul_nonsing_inv _ (by rwa [Matrix.det_transpose]), Matrix.mul_one,
    Matrix.nonsing_inv_mul_cancel_left _ _ hP, GlobalTheory.HeisFlip.pairM_comm, GlobalTheory.HeisFlip.pairM_neg_left, neg_neg]
  rfl

end GlobalTheory.ConeSoB.Chars

end
