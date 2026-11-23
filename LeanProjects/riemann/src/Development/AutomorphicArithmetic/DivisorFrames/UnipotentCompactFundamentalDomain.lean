import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RatStab
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SetIntegralEqZeroOfMulRight
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HyperbolicPlaneComplementDet
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryFixingVectorPreserves
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianLatticeSelfDualEverywhere
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)
open GlobalTheory.ConeSmallUnf

noncomputable section

namespace UpperTheory.UnipCocptHerm
open GlobalTheory.UAut GlobalTheory.SiegelSet GlobalTheory.ThK.SquareIntegrability GlobalTheory.UnipCocptForm
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

private theorem keyH (σ : E →ₐ[F] E) {n n₁ : ℕ} (J : Matrix (Fin n) (Fin n) E)
    (x y : Fin n → E) (ι : Matrix (Fin n) (Fin n₁) E)
    (hherm : ∀ i j, σ (J j i) = J i j) (hxx : form σ J x x = 0)
    (hyx : form σ J y x ≠ 0) (horth : ∀ u, form σ J (ι *ᵥ u) x = 0 ∧ form σ J (ι *ᵥ u) y = 0)
    (hdec : ∀ v : Fin n → E, ∃ (α β : E) (z : Fin n₁ → E), v = α • x + ι *ᵥ z + β • y) (c : E) (hc : c ≠ 0)
    (M : Matrix (Fin n) (Fin n) (AE F E)) (hU : Mᵀ * incM F J * M.map (cA σ) = incM F J) :
    ((M - 1) * adMat F (Matrix.of fun i (_ : Fin 1) => x i) = 0 ∧
      adMat F (Formalism.UG.cT (σ : E →+* E) (Matrix.of fun i (_ : Fin 1) => x i) * (c • J.map σ)) * (M - 1) = 0 ∧
      ∀ v : Fin n → E, (Formalism.UG.cT (σ : E →+* E) (Matrix.of fun i (_ : Fin 1) => x i) * (c • J.map σ)) *ᵥ v = 0 →
        ∃ a : Fin 1 → AF F ⊗[F] E, (M - 1) *ᵥ (fun i => inclR (F := F) (AF F) (v i)) =
          adMat F (Matrix.of fun i (_ : Fin 1) => x i) *ᵥ a) ↔
    (M *ᵥ incV F x = incV F x ∧ ∀ z, ∃ a : AE F E, M *ᵥ (incM F ι *ᵥ z) = incM F ι *ᵥ z + a • incV F x) := by
  set C : Matrix (Fin n) (Fin 1) E := Matrix.of fun i (_ : Fin 1) => x i with hCdef
  set X : Fin n → AE F E := incV F x with hXdef
  set w : Fin n → E := J *ᵥ fun i => σ (x i) with hwdef
  have hC : ∀ a : Fin 1 → AE F E, adMat F C *ᵥ a = a 0 • X := by
    intro a; ext i
    simp [hCdef, hXdef, adMat, Matrix.mulVec, dotProduct, incV, mul_comm]
  have hMC : (M - 1) * adMat F C = 0 ↔ M *ᵥ X = X := by
    constructor
    · intro h
      have h2 := congrArg (· *ᵥ (fun _ : Fin 1 => (1 : AE F E))) h
      simp only [← Matrix.mulVec_mulVec, hC, one_smul, Matrix.zero_mulVec, Matrix.sub_mulVec, Matrix.one_mulVec] at h2
      exact sub_eq_zero.1 h2
    · intro h
      have hX0 : (M - 1) *ᵥ X = 0 := by rw [Matrix.sub_mulVec, Matrix.one_mulVec, h, sub_self]
      ext i j
      have := congrFun hX0 i
      simpa [Matrix.mul_apply, hCdef, hXdef, adMat, Matrix.mulVec, dotProduct, incV] using this
  have hrow : Formalism.UG.cT (σ : E →+* E) C * (c • J.map σ) = Matrix.of fun (_ : Fin 1) j => c * w j := by
    ext o j
    simp only [Formalism.UG.cT, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, Matrix.smul_apply, smul_eq_mul,
      hCdef, Matrix.of_apply, hwdef, Matrix.mulVec, dotProduct, AlgHom.coe_toRingHom, hherm, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    ring
  have hrowv : ∀ v : Fin n → E, (Matrix.of fun (_ : Fin 1) j => c * w j) *ᵥ v = fun _ => c * form σ J v x := by
    intro v; ext o
    change (fun j => c * w j) ⬝ᵥ v = c * (v ⬝ᵥ w)
    simp only [dotProduct, Finset.mul_sum]
    exact Finset.sum_congr rfl fun k _ => by ring
  rw [hrow, hMC]
  have hX0 : ∀ h : M *ᵥ X = X, (M - 1) *ᵥ X = 0 := fun h => by rw [Matrix.sub_mulVec, Matrix.one_mulVec, h, sub_self]
  constructor
  · rintro ⟨hx, -, h3⟩
    refine ⟨hx, ?_⟩
    have hj : ∀ j : Fin n₁, ∃ a : Fin 1 → AE F E,
        (M - 1) *ᵥ (fun i => inclR (F := F) (AF F) ((ι *ᵥ Pi.single j 1) i)) = adMat F C *ᵥ a :=
      fun j => h3 _ (by rw [hrowv, (horth _).1]; ext; simp)
    choose a ha using hj
    have hcol : (M - 1) * incM F ι = Matrix.of fun i j => a j 0 * X i := by
      ext i j
      have := congrFun (ha j) i
      rw [hC] at this
      simp only [Matrix.mulVec_single_one] at this
      simpa [Matrix.mul_apply, Matrix.mulVec, dotProduct, incM, Matrix.transpose_apply, mul_comm] using this
    intro z
    refine ⟨∑ j, a j 0 * z j, ?_⟩
    have h4 : (M - 1) *ᵥ (incM F ι *ᵥ z) = (∑ j, a j 0 * z j) • X := by
      rw [Matrix.mulVec_mulVec, hcol]
      ext i
      simp only [Matrix.mulVec, dotProduct, Matrix.of_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_mul]
      exact Finset.sum_congr rfl fun j _ => by ring
    calc M *ᵥ (incM F ι *ᵥ z) = incM F ι *ᵥ z + (M - 1) *ᵥ (incM F ι *ᵥ z) := by
          rw [Matrix.sub_mulVec, Matrix.one_mulVec]; abel
      _ = _ := by rw [h4]
  · rintro ⟨hx, hz⟩
    refine ⟨hx, ?_, ?_⟩
    · have hMσ : M.map (cA σ) *ᵥ incV F (fun i => σ (x i)) = incV F (fun i => σ (x i)) := by
        ext i
        have := RingHom.map_mulVec (cA σ).toRingHom M X i
        rw [hx] at this
        simp only [Function.comp_def, hXdef, incV, cA_inclR, AlgHom.coe_toRingHom] at this ⊢
        exact this.symm
      have hW : incM F J *ᵥ incV F (fun i => σ (x i)) = incV F w := by rw [hwdef, incV_mulVec]
      have hMW : Mᵀ *ᵥ incV F w = incV F w := by
        rw [← hW]
        conv_lhs => rw [← hMσ]
        rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
        first | rw [hU] | rw [← Matrix.mul_assoc, hU]
      have hW0 : (M - 1)ᵀ *ᵥ incV F w = 0 := by
        rw [Matrix.transpose_sub, Matrix.transpose_one, Matrix.sub_mulVec, Matrix.one_mulVec, hMW, sub_self]
      ext o k
      have := congrFun hW0 k
      simp only [Matrix.mulVec, dotProduct, Matrix.transpose_apply, incV, Pi.zero_apply] at this
      simp only [Matrix.mul_apply, adMat, Matrix.map_apply, Matrix.of_apply, map_mul, Matrix.zero_apply]
      calc ∑ j, inclR (F := F) (AF F) c * inclR (F := F) (AF F) (w j) * (M - 1) j k
          = inclR (F := F) (AF F) c * ∑ j, (M - 1) j k * inclR (F := F) (AF F) (w j) := by
            rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun j _ => by ring
        _ = 0 := by rw [this, mul_zero]
    · intro v hv
      rw [hrowv] at hv
      have hvx : form σ J v x = 0 := by
        have := congrFun hv 0
        simpa [hc] using this
      obtain ⟨α, β, z, rfl⟩ := hdec v
      have hβ : β = 0 := by
        rw [form_add, form_add, form_smul, form_smul, hxx, (horth z).1] at hvx
        simpa [hyx] using hvx
      subst hβ
      obtain ⟨a, ha⟩ := hz (incV F z)
      refine ⟨fun _ => a, ?_⟩
      rw [hC]
      have e1 : (fun i => inclR (F := F) (AF F) ((α • x + ι *ᵥ z + (0 : E) • y) i)) =
          inclR (F := F) (AF F) α • X + incM F ι *ᵥ incV F z := by
        rw [← incV_mulVec]; ext i; simp [hXdef, incV]
      rw [e1, Matrix.mulVec_add, Matrix.mulVec_smul, hX0 hx, smul_zero, zero_add, Matrix.sub_mulVec, Matrix.one_mulVec, ha]
      simp

private theorem mem_unip_iffH (σ : E →ₐ[F] E) (hσ : ∀ x, σ (σ x) = x) {n n₁ : ℕ} (Y : Spc F E n)
    (H : Plane E n n₁)
    (hherm : ∀ i j, σ (Y.J j i) = Y.J i j) (hxx : form σ Y.J H.x H.x = 0)
    (hyx : form σ Y.J H.y H.x ≠ 0)
    (horth : ∀ u, form σ Y.J (H.ι *ᵥ u) H.x = 0 ∧ form σ Y.J (H.ι *ᵥ u) H.y = 0)
    (hdec : ∀ v : Fin n → E, ∃ (α β : E) (z : Fin n₁ → E), v = α • H.x + H.ι *ᵥ z + β • H.y) (c : E) (hc : c ≠ 0) (g : UA σ Y.J) :
    g ∈ unip σ Y H ↔ toGAd hσ Y.J hc g ∈ unipRad σ (c • Y.J.map σ) (Matrix.of fun i (_ : Fin 1) => H.x i) := by
  have hU : ∀ g : UA σ Y.J, (mat g)ᵀ * incM F Y.J * (mat g).map (cA σ) = incM F Y.J := fun g => g.2
  rw [GlobalTheory.UnipCT.unip_eq]
  constructor
  · intro hm
    apply Subgroup.subset_closure
    exact (keyH σ Y.J H.x H.y H.ι hherm hxx hyx horth hdec c hc (mat g) (hU g)).2 hm
  · intro hm
    have hle : unipRad σ (c • Y.J.map σ) (Matrix.of fun i (_ : Fin 1) => H.x i) ≤
        (GlobalTheory.UnipCT.unipSet σ Y H).map (toGAd hσ Y.J hc).toMonoidHom := by
      refine (Subgroup.closure_le _).2 fun h hh => ?_
      rw [SetLike.mem_coe, Subgroup.mem_map_equiv]
      exact (keyH σ Y.J H.x H.y H.ι hherm hxx hyx horth hdec c hc
        (mat ((toGAd hσ Y.J hc).symm h)) (hU _)).1 hh
    have := hle hm
    rwa [Subgroup.mem_map_equiv, MulEquiv.symm_apply_apply] at this

private theorem isHermND_one (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (hherm : ∀ i j, σ (J j i) = J i j)
    (hJ : J.det ≠ 0) (hσ : ∀ x, σ (σ x) = x) : IsHermND σ ((1 : E) • J.map σ) := by
  refine ⟨fun i j => ?_, ?_⟩
  · have h1 : σ (J i j) = J j i := hherm j i
    have h2 : σ (J j i) = J i j := hherm i j
    simp only [Matrix.smul_apply, Matrix.map_apply, smul_eq_mul, one_mul, h1, h2]
  · have e : (J.map σ).det = (σ : E →+* E) J.det := by rw [RingHom.map_det]; rfl
    rw [one_smul, e]
    exact (map_ne_zero _).2 hJ

end UpperTheory.UnipCocptHerm

end

theorem UpperTheory.unipotent_compact_fundamental_domain :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n n₁ : ℕ) (X : Spc F E n) (X₁ : Spc F E n₁) (H : Plane E n n₁) (j₀ j₁ r s r₁ s₁ : ℕ),
        B.IsGood σ → X.IsHerm σ B r s → X₁.IsHerm σ B r₁ s₁ → H.IsAdapted σ B X X₁ j₀ j₁ →
        ∃ K : Set (unip σ X H), IsCompact K ∧ ∀ u : unip σ X H, ∃ γ ∈ (ratU σ X.J).subgroupOf (unip σ X H), γ * u ∈ K := by
  intro F E _ _ _ _ _ σ B n n₁ X X₁ H j₀ j₁ r s r₁ s₁ hB hX _ hH
  have hσ := GlobalTheory.SiegelSet.sigma_sigma hB.cm
  exact GlobalTheory.UnipCocptForm.cocompact_of_mem σ hB.cm X H 1 one_ne_zero
    (UpperTheory.UnipCocptHerm.isHermND_one σ X.J hX.herm (GlobalTheory.HermSelfDualLoc.det_ne_zero_of_isHerm σ B hX) hσ)
    (GlobalTheory.UnipCocptForm.isIsoCols_smul_map_of_isotropic_pair σ X.J H.x H.y hH.xx hH.xy hσ 1)
    (UpperTheory.UnipCocptHerm.mem_unip_iffH σ hσ X H hX.herm hH.xx (GlobalTheory.UnipLine.form_y_x_ne hH hX) hH.orth
      (GlobalTheory.UnipLine.span_E hH hX) 1 one_ne_zero)
