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
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousOfClosedCoords

open scoped TensorProduct NNReal Matrix ComplexConjugate
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.DescB GlobalTheory.ThK.FlagCT GlobalTheory.ThK.FlagPar

noncomputable section

namespace GlobalTheory.ThK.InducedCons

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem exists_realIdem (σ : E →ₐ[F] E) : ∃ e : AE F E, e * e = e ∧ cA σ e = e ∧
    ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (g : GAd σ J), (HA.mat _ σ J (ofInf σ J (projInf σ J g))).1 =
      (1 - e) • (1 : Matrix (Fin n) (Fin n) (AE F E)) + e • (HA.mat _ σ J g).1 := by
  let j : Ainf F →ₗ[F] AF F := LinearMap.inl F (Ainf F) (Af F)
  have hj : ∀ a b, j (a * b) = j a * j b := fun _ _ => Prod.ext rfl (mul_zero _).symm
  have h : ∀ a : AF F, j (fstA F a) = j 1 * a := fun a => Prod.ext (one_mul a.1).symm (zero_mul a.2).symm
  have key : ∀ z : AF F ⊗[F] E, GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.tensNU j hj (Algebra.TensorProduct.map (fstA F) (AlgHom.id F E) z) =
      GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.tensNU (E := E) j hj 1 * z := fun z => by
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul a x => simp [Algebra.TensorProduct.one_def, h]
    | add x y hx hy => rw [map_add, map_add, hx, hy, mul_add]
  refine ⟨GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.tensNU (E := E) j hj 1, by rw [← map_mul, mul_one], ?_, fun n J g => ?_⟩
  · change Algebra.TensorProduct.map (AlgHom.id (AF F) (AF F)) σ (j 1 ⊗ₜ[F] (1 : E)) = j 1 ⊗ₜ[F] (1 : E)
    rw [Algebra.TensorProduct.map_tmul, map_one σ]
    rfl
  · ext r s
    refine (GlobalTheory.AutFunCompare.mat_extH σ J j hj _ r s).trans ?_
    rw [GlobalTheory.AdelicU.projInf, GlobalTheory.AutFunCompare.mat_mapH, key]
    rfl

def mixUnit {R : Type*} [CommRing R] {e : R} (he : e * e = e) (t : Rˣ) : Rˣ where
  val := (1 - e) + e * t.1
  inv := (1 - e) + e * (t⁻¹).1
  val_inv := by linear_combination (1 - t.1 - (t⁻¹).1 + t.1 * (t⁻¹).1) * he + e * t.mul_inv
  inv_val := by linear_combination (1 - t.1 - (t⁻¹).1 + t.1 * (t⁻¹).1) * he + e * t.mul_inv

theorem mixUnit_one {R : Type*} [CommRing R] {e : R} (he : e * e = e) : mixUnit he 1 = 1 :=
  Units.ext (by simp [mixUnit])

variable {n n₁ : ℕ} {H : Plane E n n₁} {W : Spc F E n} {W₁ : Spc F E n₁} {e : AE F E}

theorem isLevi_mix (he : e * e = e) (hce : cA σ e = e) {t : (AE F E)ˣ} {y y' : UA σ W₁.J} {m m' : UA σ W.J}
    (hm : IsLevi (W₁ := W₁) H t y m) (hy' : mat y' = (1 - e) • (1 : Matrix _ _ (AE F E)) + e • mat y)
    (hm' : mat m' = (1 - e) • (1 : Matrix _ _ (AE F E)) + e • mat m) : IsLevi (W₁ := W₁) H (mixUnit he t) y' m' := by
  refine ⟨?_, ?_, ?_⟩
  · rw [hm', Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, hm.1, smul_smul, ← add_smul]
    rfl
  · rw [hm', Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, hm.2.1, smul_smul, ← add_smul]
    change _ = cA σ ((1 - e) + e * (t⁻¹).1) • _
    rw [map_add, map_sub, map_mul, map_one, hce]
  · rw [hm', hy', Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.smul_mul, Matrix.mul_smul, Matrix.mul_smul,
      Matrix.one_mul, Matrix.mul_one, hm.2.2]

theorem unip_mix {u u' : UA σ W.J} (hu : u ∈ unip σ W H)
    (hu' : mat u' = (1 - e) • (1 : Matrix _ _ (AE F E)) + e • mat u) : u' ∈ unip σ W H := by
  obtain ⟨h1, h2⟩ := GlobalTheory.ThK.CuspTransfer.actsOnFlag_unip hu
  refine Subgroup.subset_closure ⟨?_, fun z => ?_⟩
  · rw [hu', Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, h1, smul_smul, ← add_smul,
      mul_one, sub_add_cancel, one_smul]
  · obtain ⟨a, ha⟩ := h2 z
    refine ⟨e * a, ?_⟩
    rw [hu', Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, ha, Matrix.one_mulVec, smul_add,
      smul_smul, ← add_assoc, ← add_smul, sub_add_cancel, one_smul]

theorem isParDec_realPart : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ →
    ∀ (hσ : ∀ x, σ (σ x) = x) (n n₁ : ℕ) (W : Spc F E n) (W₁ : Spc F E n₁) (H : Plane E n n₁), (∀ i j, σ (W.J j i) = -W.J i j) → n = n₁ + 2 →
      form σ W.J H.x H.x = 0 → form σ W.J H.y H.y = 0 → form σ W.J H.x H.y = 1 →
      (∀ u, form σ W.J (H.ι *ᵥ u) H.x = 0 ∧ form σ W.J (H.ι *ᵥ u) H.y = 0) → H.ιᵀ * W.J * H.ι.map σ = W₁.J →
      ∀ (c₀ : E) (hc₀ : c₀ ≠ 0), IsHermND σ (c₀ • W₁.J.map σ) → IsHermND σ (c₀ • W.J.map σ) →
      ∀ M : UA σ W₁.J → UA σ W.J, Continuous M → (∀ h₁, IsLevi (W₁ := W₁) H 1 h₁ (M h₁)) →
      (∀ γ ∈ ratU σ W₁.J, M γ ∈ ratU σ W.J) →
      ∀ (r : ℕ) (Xf Yf : Matrix (Fin n₁) (Fin r) E), GlobalTheory.SiegelSet.IsWittFrame σ (c₀ • W₁.J.map σ) Xf Yf →
      ∀ X' Y' : Matrix (Fin n) (Fin (r + 1)) E, GlobalTheory.SiegelSet.IsWittFrame σ (c₀ • W.J.map σ) X' Y' →
      (∀ k, X' k 0 = H.x k) → (∀ k, Y' k 0 = c₀⁻¹ * H.y k) →
      (∀ (k : Fin n) (i : Fin r), X' k i.succ = (H.ι * Xf) k i ∧ Y' k i.succ = (H.ι * Yf) k i) → ∀ (t : (AE F E)ˣ) (y : GAd σ (c₀ • W₁.J.map σ)) (g : GAd σ (c₀ • W.J.map σ)), GlobalTheory.ThK.InducedCons.IsParDec hσ W W₁ H hc₀ X' M t y g →
      ∃ t₁ : (AE F E)ˣ, GlobalTheory.ThK.InducedCons.IsParDec hσ W W₁ H hc₀ X' M t₁ (ofInf σ _ (projInf σ _ y)) (ofInf σ _ (projInf σ _ g)) := by
  intro F E _ _ _ _ _ σ hcm hσ n n₁ W W₁ H hsk hn hxx hyy hxy horth hg c₀ hc₀ hJ₁ hJ M _ hM _ r Xf Yf _ X' Y' hW hX _ _ t y g
    ⟨u, hu, m, hm, hdec⟩
  have h : GLTwo.IsHypPlane σ H W W₁ := ⟨hn, hxx, hyy, hxy, horth, hg⟩
  have hd : W₁.J.det ≠ 0 := fun h0 => hJ₁.2 (by
    have e : (W₁.J.map σ).det = (σ : E →+* E) W₁.J.det := by rw [RingHom.map_det]; rfl
    rw [Matrix.det_smul, e, h0, map_zero, mul_zero])
  obtain ⟨e, he, hce, hπ⟩ := exists_realIdem σ
  let φ := GlobalTheory.ThK.SquareIntegrability.toGAd hσ W.J hc₀
  let φ₁ := GlobalTheory.ThK.SquareIntegrability.toGAd hσ W₁.J hc₀
  obtain ⟨u, rfl⟩ := φ.surjective u
  have hu' : u ∈ unip σ W H := (h.mem_unip_iff hσ hsk hd hc₀ hW (Nat.succ_pos r) hX u).2 hu
  refine ⟨mixUnit he t, ofInf σ _ (projInf σ _ (φ u)), ?_, φ.symm (ofInf σ _ (projInf σ _ (φ m))), ?_, ?_⟩
  · have := (h.mem_unip_iff hσ hsk hd hc₀ hW (Nat.succ_pos r) hX (φ.symm (ofInf σ _ (projInf σ _ (φ u))))).1
      (unip_mix hu' (hπ _ _ (φ u)))
    exact this
  · exact isLevi_mix he hce hm (by rw [mat_one, ← add_smul, sub_add_cancel, one_smul]) (hπ _ _ (φ m))
  · have h1 := isLevi_mix (y' := φ₁.symm (ofInf σ _ (projInf σ _ y)))
      (m' := φ.symm (ofInf σ _ (projInf σ _ (φ (M (φ₁.symm y)))))) he hce (hM (φ₁.symm y)) (hπ _ _ y) (hπ _ _ (φ _))
    rw [mixUnit_one] at h1
    have h2 := congrArg φ (h.levi_unique hσ hsk hd h1 (hM _))
    rw [φ.apply_symm_apply] at h2
    rw [hdec, map_mul, map_mul, map_mul, map_mul]
    exact congrArg₂ (· * ·) (congrArg₂ (· * ·) rfl (φ.apply_symm_apply _).symm) h2

end GlobalTheory.ThK.InducedCons

end
