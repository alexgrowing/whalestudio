import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnipParLeUnipFlag
import Development.AbelianVarietyTheory.Definitions.Foundations.ConstTermOnMulLeftOfNormalizer
import Development.AbelianVarietyTheory.Definitions.Divisors.IsSquareIntegrableIffMemL2
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.LanglandsSquareIntegrable
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToGAdMat
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HyperbolicPlaneOrthogonalGramRestrictionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsConstAlong
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousToGAd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsInd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsParDec
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryCompactPreimage
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnipotentMemIffWeightRaising
open scoped TensorProduct NNReal Matrix ComplexConjugate
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.DescB GlobalTheory.ThK.FlagCT GlobalTheory.ThK.FlagPar

noncomputable section

namespace GlobalTheory.ThK.LeviPartCpt

open Matrix GlobalTheory.ThK.SquareIntegrability

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

omit [NumberField F] [NumberField E] in

theorem exists_retraction (hσ : ∀ e, σ (σ e) = e) {n n₁ : ℕ} {J : Matrix (Fin n) (Fin n) E}
    {J₁ : Matrix (Fin n₁) (Fin n₁) E} (hsk : ∀ i j, σ (J j i) = -J i j) {x : Fin n → E} {ι : Matrix (Fin n) (Fin n₁) E}
    (horth : ∀ u, form σ J (ι *ᵥ u) x = 0) (hgram : ιᵀ * J * ι.map σ = J₁) (hJ₁ : J₁.det ≠ 0) :
    ∃ π : Matrix (Fin n₁) (Fin n) E, π * ι = 1 ∧ π *ᵥ x = 0 := by
  refine ⟨(J₁⁻¹)ᵀ * (J * ι.map σ)ᵀ, ?_, ?_⟩
  · calc _ = (J₁⁻¹)ᵀ * (ιᵀ * J * ι.map σ)ᵀ := by
          simp only [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc]
      _ = 1 := by
          rw [hgram, ← Matrix.transpose_mul, Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.2 hJ₁), Matrix.transpose_one]
  · have inner : (J * ι.map σ)ᵀ *ᵥ x = 0 := by
      funext j
      have h := GlobalTheory.LeviPlaneSection.form_skew hσ hsk x (ι *ᵥ Pi.single j 1)
      rw [horth, map_zero, neg_zero] at h
      rw [Pi.zero_apply, ← h]
      simp [form, mulVec, dotProduct, Matrix.mul_apply, mul_comm, Pi.single_apply]
    rw [← mulVec_mulVec, inner, mulVec_zero]

def Acts {n n₁ : ℕ} (W : Spc F E n) (W₁ : Spc F E n₁) (H : Plane E n n₁) (g : UA σ W.J) (y : UA σ W₁.J) : Prop :=
  (∃ t : (AE F E)ˣ, mat g *ᵥ incV F H.x = t.1 • incV F H.x) ∧
    ∀ z, ∃ a : AE F E, mat g *ᵥ (incM F H.ι *ᵥ z) = incM F H.ι *ᵥ (mat y *ᵥ z) + a • incV F H.x

variable {n n₁ : ℕ} {W : Spc F E n} {W₁ : Spc F E n₁} {H : Plane E n n₁}

omit [NumberField E] in
theorem Acts.mul {g g' : UA σ W.J} {y y' : UA σ W₁.J} (h : Acts W W₁ H g y) (h' : Acts W W₁ H g' y') :
    Acts W W₁ H (g * g') (y * y') := by
  obtain ⟨⟨t, ht⟩, hz⟩ := h
  obtain ⟨⟨t', ht'⟩, hz'⟩ := h'
  have e : mat (g * g') = mat g * mat g' := rfl
  have e' : mat (y * y') = mat y * mat y' := rfl
  refine ⟨⟨t' * t, by rw [e, ← mulVec_mulVec, ht', mulVec_smul, ht, smul_smul, Units.val_mul]⟩, fun z => ?_⟩
  obtain ⟨p, hp⟩ := hz' z
  obtain ⟨q, hq⟩ := hz (mat y' *ᵥ z)
  refine ⟨q + p * t.1, ?_⟩
  rw [e, e', ← mulVec_mulVec, hp, mulVec_add, mulVec_smul, hq, ht, add_smul, smul_smul, ← mulVec_mulVec z (mat y), add_assoc]

omit [NumberField E] in
theorem Acts.inv {g : UA σ W.J} {y : UA σ W₁.J} (h : Acts W W₁ H g y) : Acts W W₁ H g⁻¹ y⁻¹ := by
  obtain ⟨⟨t, ht⟩, hz⟩ := h
  have e : mat g⁻¹ * mat g = 1 := Units.inv_mul g.1
  have e' : mat y * mat y⁻¹ = 1 := Units.mul_inv y.1
  have hx : mat g⁻¹ *ᵥ incV F H.x = (t⁻¹).1 • incV F H.x := by
    have := congrArg (fun v => (t⁻¹).1 • mat g⁻¹ *ᵥ v) ht
    simp only [mulVec_mulVec, e, one_mulVec, mulVec_smul, smul_smul, Units.inv_mul, one_smul] at this
    exact this.symm
  refine ⟨⟨t⁻¹, hx⟩, fun z => ?_⟩
  obtain ⟨q, hq⟩ := hz (mat y⁻¹ *ᵥ z)
  refine ⟨-(q * (t⁻¹).1), ?_⟩
  have := congrArg (fun v => mat g⁻¹ *ᵥ v) hq
  rw [mulVec_mulVec _ (mat g⁻¹) (mat g), e, one_mulVec, mulVec_add, mulVec_smul, hx, mulVec_mulVec z (mat y), e',
    one_mulVec, smul_smul] at this
  rw [neg_smul, ← sub_eq_add_neg, eq_sub_iff_add_eq]
  exact this.symm

omit [NumberField E] in
theorem Acts.of_levi {t : (AE F E)ˣ} {g : UA σ W.J} {y : UA σ W₁.J} (h : IsLevi (W₁ := W₁) H t y g) :
    Acts W W₁ H g y :=
  ⟨⟨t, h.1⟩, fun z => ⟨0, by rw [zero_smul, add_zero, mulVec_mulVec, mulVec_mulVec, h.2.2]⟩⟩

theorem Acts.of_unip {u : UA σ W.J} (h : u ∈ unip σ W H) : Acts W W₁ H u 1 := by
  obtain ⟨h1, h2⟩ := (GlobalTheory.UnipHaar.RadMem.mem_unip_iff_set σ W H u).1 h
  have e : mat (1 : UA σ W₁.J) = 1 := rfl
  exact ⟨⟨1, by simpa using h1⟩, fun z => by simpa only [e, one_mulVec] using h2 z⟩

omit [NumberField E] in
theorem Acts.mat_eq {π : Matrix (Fin n₁) (Fin n) E} (hπ : π * H.ι = 1) (hπx : π *ᵥ H.x = 0)
    {g : UA σ W.J} {y : UA σ W₁.J} (h : Acts W W₁ H g y) : mat y = incM F π * mat g * incM F H.ι := by
  have h1 : incM F π * incM F H.ι = 1 := by
    rw [incM, incM, ← Matrix.map_mul, hπ]; simp
  have h2 : incM F π *ᵥ incV F H.x = 0 := by
    funext i
    have := congrArg (inclR (F := F) (AF F)) (congrFun hπx i)
    simpa [incM, incV, mulVec, dotProduct, map_sum] using this
  refine Matrix.ext_of_mulVec_single fun j => ?_
  obtain ⟨a, ha⟩ := h.2 (Pi.single j 1)
  rw [← mulVec_mulVec, ← mulVec_mulVec, ha, mulVec_add, mulVec_smul, h2, smul_zero, add_zero, mulVec_mulVec _ (incM F π), h1,
    one_mulVec]

end GlobalTheory.ThK.LeviPartCpt

open GlobalTheory.ThK.LeviPartCpt GlobalTheory.ThK.SquareIntegrability Matrix in

theorem GlobalTheory.ThK.LeviPartCpt.levi_part_mem : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ →
    ∀ (hσ : ∀ x, σ (σ x) = x) (n n₁ : ℕ) (W : Spc F E n) (W₁ : Spc F E n₁) (H : Plane E n n₁), (∀ i j, σ (W.J j i) = -W.J i j) → n = n₁ + 2 →
      form σ W.J H.x H.x = 0 → form σ W.J H.y H.y = 0 → form σ W.J H.x H.y = 1 →
      (∀ u, form σ W.J (H.ι *ᵥ u) H.x = 0 ∧ form σ W.J (H.ι *ᵥ u) H.y = 0) → H.ιᵀ * W.J * H.ι.map σ = W₁.J →
      ∀ (c₀ : E) (hc₀ : c₀ ≠ 0), IsHermND σ (c₀ • W₁.J.map σ) → IsHermND σ (c₀ • W.J.map σ) →
      ∀ M : UA σ W₁.J → UA σ W.J, Continuous M → (∀ h₁, IsLevi (W₁ := W₁) H 1 h₁ (M h₁)) →
      ∀ (r : ℕ) (X' Y' : Matrix (Fin n) (Fin (r + 1)) E), GlobalTheory.SiegelSet.IsWittFrame σ (c₀ • W.J.map σ) X' Y' →
      (∀ k, X' k 0 = H.x k) →
      ∀ K₁ : Subgroup (GAd σ (c₀ • W₁.J.map σ)), GlobalTheory.UAut.IsMaxCpt σ (c₀ • W₁.J.map σ) K₁ →
      ∀ K' : Subgroup (GAd σ (c₀ • W.J.map σ)), K' ≤ infPts σ (c₀ • W.J.map σ) → IsCompact (K' : Set (GAd σ (c₀ • W.J.map σ))) →
      (∀ y ∈ K₁, GlobalTheory.ThK.CuspTransfer.emb hσ W W₁ hc₀ M y ∈ K') →
      ∀ (t : (AE F E)ˣ) (y : GAd σ (c₀ • W₁.J.map σ)) (g : GAd σ (c₀ • W.J.map σ)), GlobalTheory.ThK.InducedCons.IsParDec hσ W W₁ H hc₀ X' M t y g → g ∈ K' → y ∈ K₁ := by
  intro F E _ _ _ _ _ σ hcm hσ n n₁ W W₁ H hsk hn hxx hyy hxy horth hg c₀ hc₀ hJ₁ hJ M hMc hM r X' Y' hW hX K₁ hK₁ K' hKi hKc
    hKK t y g hp hgK
  have h : GLTwo.IsHypPlane σ H W W₁ := ⟨hn, hxx, hyy, hxy, horth, hg⟩
  have hd : W₁.J.det ≠ 0 := fun h0 => hJ₁.2 (by
    have e : (W₁.J.map σ).det = (σ : E →+* E) W₁.J.det := by rw [RingHom.map_det]; rfl
    rw [Matrix.det_smul, e, h0, map_zero, mul_zero])
  obtain ⟨_, _⟩ := GlobalTheory.StdPar.ring_facts (F := F) (E := E)
  obtain ⟨π, hπ, hπx⟩ := exists_retraction hσ hsk (fun u => (horth u).1) hg hd
  let φ := toGAd hσ W.J hc₀
  let φ₁ := toGAd hσ W₁.J hc₀
  let Y : Subgroup (GAd σ (c₀ • W₁.J.map σ)) :=
    { carrier := {y | ∃ g ∈ K', Acts W W₁ H (φ.symm g) (φ₁.symm y)}
      mul_mem' := by
        rintro a b ⟨g, hg, ha⟩ ⟨g', hg', hb⟩
        exact ⟨g * g', mul_mem hg hg', by simpa only [map_mul] using ha.mul hb⟩
      one_mem' := ⟨1, one_mem _, by simpa only [map_one] using Acts.of_unip (one_mem _)⟩
      inv_mem' := by
        rintro a ⟨g, hg, ha⟩
        exact ⟨g⁻¹, inv_mem hg, by simpa only [map_inv] using ha.inv⟩ }
  have hKY : K₁ ≤ Y := fun y hy => ⟨_, hKK y hy, by
    simpa only [CuspTransfer.emb, φ, MulEquiv.symm_apply_apply] using Acts.of_levi (hM (φ₁.symm y))⟩
  have hyY : y ∈ Y := by
    refine ⟨g, hgK, ?_⟩
    obtain ⟨u, hu, m, hm, rfl⟩ := hp
    have hu' : φ.symm u ∈ unip σ W H := by
      rw [h.mem_unip_iff hσ hsk hd hc₀ hW (Nat.succ_pos r) hX]
      simp only [φ, MulEquiv.apply_symm_apply]
      exact hu
    have := ((Acts.of_unip (W₁ := W₁) hu').mul (Acts.of_levi hm)).mul (Acts.of_levi (hM (φ₁.symm y)))
    simpa only [CuspTransfer.emb, φ, map_mul, MulEquiv.symm_apply_apply, one_mul] using this
  have hYi : Y ≤ infPts σ (c₀ • W₁.J.map σ) := by
    rintro a ⟨g, hg, ha⟩
    let f := (Algebra.TensorProduct.map (sndA F) (AlgHom.id F E)).toRingHom
    have h1 : (mat (φ.symm g)).map f = 1 := congrArg Units.val (MonoidHom.mem_ker.1 (hKi hg))
    refine MonoidHom.mem_ker.2 (Units.ext ?_)
    change (mat (φ₁.symm a)).map f = 1
    rw [ha.mat_eq hπ hπx, Matrix.map_mul, Matrix.map_mul, h1, Matrix.mul_one, ← Matrix.map_mul, incM, incM, ← Matrix.map_mul, hπ]
    simp
  have hmat : Continuous fun g : GAd σ (c₀ • W.J.map σ) => mat (φ.symm g) := GlobalTheory.StdPar.continuous_mat
  have hC : IsCompact ((fun g : GAd σ (c₀ • W.J.map σ) => incM F π * mat (φ.symm g) * incM F H.ι) '' K') :=
    hKc.image ((continuous_const.matrix_mul hmat).matrix_mul continuous_const)
  have hS := (GlobalTheory.ThK.UnipDom.isCompact_setOf_mat_mem F E σ n₁ W₁.J _ hC).image (GLTwo.continuous_toGAd hσ W₁.J hc₀).1
  have hYc : IsCompact (Y.topologicalClosure : Set (GAd σ (c₀ • W₁.J.map σ))) := by
    refine hS.of_isClosed_subset Y.isClosed_topologicalClosure (closure_minimal ?_ hS.isClosed)
    rintro a ⟨g, hg, ha⟩
    refine ⟨φ₁.symm a, ⟨⟨g, hg, (ha.mat_eq hπ hπx).symm⟩, ⟨g⁻¹, inv_mem hg, ?_⟩⟩, φ₁.apply_symm_apply a⟩
    simpa only [map_inv] using (ha.inv.mat_eq hπ hπx).symm
  have hle := hK₁.2 (y := Y.topologicalClosure)
    ⟨Y.topologicalClosure_minimal hYi (isClosed_infPts _ _), hYc⟩ (hKY.trans Y.le_topologicalClosure)
  exact hle (Y.le_topologicalClosure hyY)

end
