import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConeLin
import Development.AbelianVarietyTheory.Definitions.Divisors.PairsOfSquareTriple
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalOperatorMulOfPublished
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalWeilActionCompatibilityStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EvalInvarianceSecondOfPrintsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalPartOperatorUnitaryCompatible
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnipotentRadicalCoordinateHomeomorph
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HTensEqZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HTensVmvLeft

noncomputable section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.LemF
open GlobalTheory.Doubling (absE)

namespace GlobalTheory.ThK.LemF.ConeUnipB

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem symp_iso_right {n d : ℕ} (JX : Matrix (Fin n) (Fin n) E) (JW : Matrix (Fin d) (Fin d) E)
    (x : Fin d → E) (hx : form σ JW x x = 0) (p q : Fin n → AE F E) :
    symp (R := AF F) (cA σ) (-1) (incM F JX) (incM F JW) (Matrix.vecMulVec p (incV F x))
      (Matrix.vecMulVec q (incV F x)) = 0 := by
  have hc : ∀ e : E, cA σ (inclR (F := F) (AF F) e) = inclR (F := F) (AF F) (σ e) := fun e => rfl
  have h0 : (∑ j, incV F x j * ∑ l, incM F JW j l * cA σ (incV F x l)) = 0 := by
    have : (∑ j, incV F x j * ∑ l, incM F JW j l * cA σ (incV F x l)) = inclR (F := F) (AF F) (form σ JW x x) := by
      simp only [incV, incM, Matrix.map_apply, hc, form, dotProduct, Matrix.mulVec, map_sum, map_mul]
    rw [this, hx, map_zero]
  have h1 : hTens (cA σ) (incM F JX) (incM F JW) (Matrix.vecMulVec p (incV F x)) (Matrix.vecMulVec q (incV F x)) = 0 := by
    rw [GlobalTheory.ArchSchB.TensForm.hTens_vmv_right]
    refine Finset.sum_eq_zero fun i _ => ?_
    calc _ = (p i * ∑ k, incM F JX i k * cA σ (q k)) * ∑ j, incV F x j * ∑ l, incM F JW j l * cA σ (incV F x l) := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [Matrix.vecMulVec_apply]
          ring
      _ = 0 := by rw [h0, mul_zero]
  rw [symp, h1, mul_zero, map_zero]

theorem partFin_vecMulVec {n d : ℕ} (v : Pl F) (p : Fin n → AE F E) (w : Fin d → AE F E) :
    partFin v (Matrix.vecMulVec p w) = Matrix.vecMulVec (partFin v p) w := by
  ext i j
  simp only [partFin, Matrix.smul_apply, Matrix.vecMulVec_apply, Pi.smul_apply, smul_mul_assoc]

theorem ev_shift {n d n₁ d₁ : ℕ} {X : Spc F E n} {W : Spc F E d} {X₁ : Spc F E n₁} {W₁ : Spc F E d₁} (B : Base F E)
    (hstd : IsStd B.ψ) (M : Model σ X W) (M₁ : Model σ X₁ W₁) (hM : M.IsGood B.ψ) (hM₁ : M₁.IsGood B.ψ)
    (e : Fn F n d →ₗ[ℂ] Fn F n₁ d₁) {ei ev} (hloc : IsLocPart M M₁ e ei ev) (v : Pl F) (x : Fin d → E)
    (hx : form σ W.J x x = 0) (p q : Fin n → AE F E)
    (hq : ∀ Φ ∈ schA F (Fin n × Fin d), e (M.co.rho B.ψ (partFin v (Matrix.vecMulVec q (incV F x))) Φ) = e Φ)
    {ψ : (Fin n × Fin d → Fv F v) → ℂ} (hψ : ψ ∈ SB (Fin n × Fin d → Fv F v)) :
    ev v (locOp v (M.co.rho B.ψ (partFin v (Matrix.vecMulVec (p + q) (incV F x)))) ψ) =
      ev v (locOp v (M.co.rho B.ψ (partFin v (Matrix.vecMulVec p (incV F x)))) ψ) := by
  set φ := locOp v (M.co.rho B.ψ (partFin v (Matrix.vecMulVec p (incV F x)))) ψ with hφdef
  have hφ : φ ∈ SB (Fin n × Fin d → Fv F v) := locOp_mem _ _ _
  have a1 := (locOp_rho M.co hstd.1 v (Matrix.vecMulVec p (incV F x)) hψ).1
  have a2 := (locOp_rho M.co hstd.1 v (Matrix.vecMulVec q (incV F x)) hφ).1
  have hsum : partFin v (Matrix.vecMulVec (p + q) (incV F x)) =
      partFin v (Matrix.vecMulVec q (incV F x)) + partFin v (Matrix.vecMulVec p (incV F x)) := by
    rw [partFin, partFin, partFin, ← smul_add, add_comm p q, Matrix.add_vecMulVec]
  have h0 : symp (R := AF F) (cA σ) (-1) (incM F X.J) (incM F W.J) (partFin v (Matrix.vecMulVec q (incV F x)))
      (partFin v (Matrix.vecMulVec p (incV F x))) = 0 := by
    rw [partFin_vecMulVec, partFin_vecMulVec]
    exact symp_iso_right X.J W.J x hx _ _
  have e1 : locOp v (M.co.rho B.ψ (partFin v (Matrix.vecMulVec (p + q) (incV F x)))) ψ =
      locOp v (M.co.rho B.ψ (partFin v (Matrix.vecMulVec q (incV F x)))) φ := by
    refine locOp_eq hψ (locOp_mem _ _ _) fun r hr => ?_
    have hr' : Rest (evFin F v) φ r :=
      ⟨hr.1, by rw [← a1 r hr]; exact GlobalTheory.HeisSchA.rho_mem_schA M B.ψ hstd _ _ hr.2⟩
    rw [hsum, ← GlobalTheory.MixW.UnipHeis.rho_rho M.co B.ψ _ _ h0, a1 r hr, a2 r hr']
  have hev : ev v φ ∈ SB (Fin n₁ × Fin d₁ → Fv F v) := by
    rw [← (hloc.2.1 v).2]
    exact Submodule.mem_map_of_mem hφ
  have h := GlobalTheory.ThK.LemF.LocPartLaw.locPart_law B M M₁ hM hM₁ e ei ev hloc v
    (M.co.rho B.ψ (partFin v (Matrix.vecMulVec q (incV F x)))) id 1 (fun Φ hΦ => by rw [hq Φ hΦ, one_smul, id]) φ _ (ev v φ)
    hφ (locOp_mem _ _ _) hev a2 (fun r _ => rfl)
  rw [e1, h, one_smul]

theorem coneLin_unip : GlobalTheory.FunPr.Hypotheses₂ → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (a b : ℕ)
    (G : Geo σ a (b + 2)) (G₁ : Geo σ a b) (H : Plane E (b + 2) b) (H' : Plane E (a + (b + 2)) (a + b)), CfgB B G G₁ H H' →
    ∀ e', IsEv B G.M' G₁.M' H.ι H'.ι (isoB H H') e' → ∀ ei' ev', IsLocPart G.M' G₁.M' e' ei' ev' →
    ∀ X om om' om₁ om₁', IsTriple B G X om om' → IsTriple B G₁ X om₁ om₁' →
    ∀ (v : Pl F) (μ : Measure (idelesAt E (evFin F v))), μ.IsHaarMeasure → ∀ l : ((Fin b × Fin (a + b) → Fv F v) → ℂ) →ₗ[ℂ] ℂ,
      (∀ g₀ ∈ UAt σ G₁.V' (evFin F v), ∀ ψ ∈ SB (Fin b × Fin (a + b) → Fv F v), l (locOp v (om₁' (g₀, 1)) ψ) = l ψ) →
      ∀ φ ∈ SB (Fin (b + 2) × Fin (a + (b + 2)) → Fv F v), ∀ u ∈ unip σ G.V' H, u ∈ UAt σ G.V' (evFin F v) →
        ∀ g ∈ UAt σ G.V' (evFin F v), coneLin B G.M' om' v (ev' v) μ (shiftB σ H H') X.ν ((a - (b + 2)) / 2 + 1) l φ (u * g) = coneLin B G.M' om' v (ev' v) μ (shiftB σ H H') X.ν ((a - (b + 2)) / 2 + 1) l φ g := by
  intro hPr F E _ _ _ _ _ σ B a b G G₁ H H' hC e' he' ei' ev' hloc X om om' om₁ om₁' hT hT₁ v μ _ l hl φ hφ u hu huv g hg
  have hP' := GlobalTheory.ThK.Inhab.pairV' hT
  have hP₁' := GlobalTheory.ThK.Inhab.pairV' hT₁
  have hB := hP'.base
  have hstd : IsStd B.ψ := hB.std
  have h1W : (1 : UA σ G.W.J) ∈ UAt σ G.W (evFin F v) := (UAtSub σ G.W (evFin F v)).one_mem
  have hcomp : locOp v (om' (u * g, 1)) φ = locOp v (om' (u, 1)) (locOp v (om' (g, 1)) φ) := by
    have h := locOpMul hPr F E σ B _ _ G.V' G.W G.M' _ _ om' _ _ _ _ hP' v (u, 1) (g, 1) huv h1W hg h1W φ hφ
    rwa [Prod.mk_mul_mk, mul_one] at h
  have hEv := (GlobalTheory.T.eval_invariance_second_of_hypotheses hPr F E σ B a b G G₁ H H' hC e' he' ei' ev' hloc X om om' om₁ om₁' hT hT₁ v l hl).1 u hu huv

  obtain ⟨w⟩ : Nonempty (InfinitePlace F) := inferInstance
  have hσ : ∀ z, σ (σ z) = z := fun z => (B.emb w).1.injective (by rw [hB.cm.2.2.2, hB.cm.2.2.2, star_star])
  have hdet₁ : G₁.V'.J.det ≠ 0 := by
    have h := GlobalTheory.LeviElem.det_ne_of_sig _ (hP₁'.herm.sig w)
    intro h0
    apply h
    have : (G₁.V'.J.map (B.emb w).1).det = (B.emb w).1 G₁.V'.J.det := (RingHom.map_det (B.emb w).1 _).symm
    rw [this, h0, map_zero]
  obtain ⟨hspan, hdet⟩ := GlobalTheory.UnipChart.span_det σ hσ B hP'.herm.herm hC.hH hdet₁
  have hyp : GlobalTheory.UnipChart.Hyp σ G.V'.J G₁.V'.J H :=
    ⟨hσ, hP'.herm.herm, hC.hH.xx, hC.hH.yy, hC.hH.xy, hC.hH.orth, hC.hH.gram⟩
  obtain ⟨β, c, hy⟩ : ∃ (β : Fin b → AE F E) (c : AE F E),
      mat u⁻¹ *ᵥ incV F H.y = incV F H.y + (incM F H.ι *ᵥ β + c • incV F H.x) :=
    ⟨_, _, hyp.unip_y hspan hdet hP₁'.herm.herm (isUnit_iff_ne_zero.mpr hdet₁) (inv_mem hu)⟩
  set ψ := locOp v (om' (g, 1)) φ with hψdef
  have hψ : ψ ∈ SB (Fin (b + 2) × Fin (a + (b + 2)) → Fv F v) := locOp_mem _ _ _
  have key : ∀ t : (AE F E)ˣ,
      l (ev' v (locOp v (G.M'.co.rho B.ψ (partFin v (shiftB σ H H' t))) (locOp v (om' (u, 1)) ψ))) =
        l (ev' v (locOp v (G.M'.co.rho B.ψ (partFin v (shiftB σ H H' t))) ψ)) := by
    intro t
    have hs : shiftB σ H H' t = Matrix.vecMulVec (cA σ t.1 • incV F H.y) (incV F H'.x) := by
      rw [shiftB, Matrix.smul_vecMulVec]
    have hm := GlobalTheory.T.local_weil_action_compatibility hPr F E σ B _ _ G.V' G.W G.M' _ _ om' _ _ _ _ hP' v u 1 huv h1W
      (mat u⁻¹ * shiftB σ H H' t) ψ hψ
    rw [GlobalTheory.StabHaar.mat_one, Matrix.transpose_one, Matrix.mul_one, ← Matrix.mul_assoc, GlobalTheory.StabHaar.mat_mul_inv,
      Matrix.one_mul] at hm
    rw [← hm, hEv _ (locOp_mem _ _ _)]
    have hw : mat u⁻¹ * shiftB σ H H' t = Matrix.vecMulVec
        ((cA σ t.1 • incV F H.y + incM F H.ι *ᵥ (cA σ t.1 • β)) + (cA σ t.1 * c) • incV F H.x) (incV F H'.x) := by
      rw [hs, Matrix.mul_vecMulVec, Matrix.mulVec_smul, hy, Matrix.mulVec_smul, smul_add, smul_add, smul_smul, add_assoc]
    rw [hw, ev_shift B hstd G.M' G₁.M' hP'.good hP₁'.good e' hloc v H'.x hC.hH'.xx _ _ ?_ hψ,
      ev_shift B hstd G.M' G₁.M' hP'.good hP₁'.good e' hloc v H'.x hC.hH'.xx _ _ ?_ hψ, hs]
    · refine he'.inv _ (Or.inr ⟨partFin v (cA σ t.1 • β), ?_⟩)
      rw [partFin_vecMulVec, partFin, partFin, Matrix.mulVec_smul _ (GlobalTheory.LatVac.liftV v 1)]
    · refine he'.inv _ (Or.inl ⟨partFin v ((cA σ t.1 * c) • incV F H'.x), ?_⟩)
      ext i j
      simp only [partFin, Matrix.smul_apply, Matrix.vecMulVec_apply, Pi.smul_apply, smul_eq_mul, mul_smul_comm]
      congr 1
      ring
  unfold coneLin
  congr 1
  funext t
  rw [hcomp, key t.1]

end GlobalTheory.ThK.LemF.ConeUnipB

end
