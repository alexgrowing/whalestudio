import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiffsZeroOfLev
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousLeviIdeleHomExists
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HyperbolicPlaneComplementFormStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IwasawaDecompIsotropicVector
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StabilizerRestrictsToOrthocomp
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.DescB
open GlobalTheory.Doubling (absE)

noncomputable section

namespace GlobalTheory.IwaIsoPlane

open Matrix GlobalTheory.LeviIdeleHom

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem det_ne_zero_of_cartan (B : Base F E) {n : ℕ} (Y : Spc F E n)
    (h : ∀ w, IsCartan (Complex.I • Y.J.map (B.emb w).1) (Y.θ w)) : Y.J.det ≠ 0 := by
  intro hdet
  obtain ⟨w⟩ : Nonempty (InfinitePlace F) := inferInstance
  have hd : (Y.J.map (B.emb w).1).det = 0 := by
    have := RingHom.map_det (B.emb w).1 Y.J
    rw [hdet, map_zero] at this
    exact this.symm
  obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.2 hd
  have hx : star v ≠ 0 := by
    intro h0; apply hv0; rw [← star_star v, h0, star_zero]
  have := (h w).2.2 (star v) hx
  rw [star_star, Matrix.smul_mulVec, hv, smul_zero, dotProduct_zero, Complex.zero_re] at this
  exact lt_irrefl _ this

theorem exists_isLevi_of_hyperbolic_pair (hcm : IsCMExt F E σ) {n n₁ : ℕ} (Y : Spc F E n) (Y₁ : Spc F E n₁) (H : Plane E n n₁)
    (hsk : ∀ i j, σ (Y.J j i) = -Y.J i j) (hxx : form σ Y.J H.x H.x = 0) (hyy : form σ Y.J H.y H.y = 0)
    (hxy : form σ Y.J H.x H.y = 1) (horth : ∀ u, form σ Y.J (H.ι *ᵥ u) H.x = 0 ∧ form σ Y.J (H.ι *ᵥ u) H.y = 0)
    (t : (AE F E)ˣ) : ∃ m : UA σ Y.J, IsLevi (W₁ := Y₁) H t 1 m := by
  have hσ : ∀ e, σ (σ e) = e := sigma_sigma hcm
  obtain ⟨hax, hay, hbx, hby, hxJ, hyJ, haι, hbι⟩ := dual_facts hσ hsk hxx hyy hxy horth
  set aE := Y.J *ᵥ (⇑σ ∘ H.y) with haE
  set bE := -(Y.J *ᵥ (⇑σ ∘ H.x)) with hbE
  set f : E →+* AE F E := inclR (F := F) (AF F) with hf
  have hcf : ∀ {k : ℕ} (v : Fin k → E), ⇑(cA σ) ∘ (f ∘ v) = f ∘ (⇑σ ∘ v) := fun v => funext fun i => cA_inclR σ (v i)
  have hdot : ∀ v w : Fin n → E, (f ∘ v) ⬝ᵥ (f ∘ w) = f (v ⬝ᵥ w) := fun v w => (RingHom.map_dotProduct f v w).symm
  have hneg : ∀ v : Fin n → E, f ∘ (-v) = -(f ∘ v) := fun v => funext fun i => map_neg f (v i)
  have hax' : (f ∘ aE) ⬝ᵥ (f ∘ H.x) = 1 := by rw [hdot, hax, map_one]
  have hay' : (f ∘ aE) ⬝ᵥ (f ∘ H.y) = 0 := by rw [hdot, hay, map_zero]
  have hbx' : (f ∘ bE) ⬝ᵥ (f ∘ H.x) = 0 := by rw [hdot, hbx, map_zero]
  have hby' : (f ∘ bE) ⬝ᵥ (f ∘ H.y) = 1 := by rw [hdot, hby, map_one]
  have haι' : (f ∘ aE) ᵥ* incM F H.ι = 0 := by
    change (f ∘ aE) ᵥ* H.ι.map f = 0
    rw [map_comp_vecMul, haι]; funext i; simp
  have hbι' : (f ∘ bE) ᵥ* incM F H.ι = 0 := by
    change (f ∘ bE) ᵥ* H.ι.map f = 0
    rw [map_comp_vecMul, hbι]; funext i; simp
  let M : (AE F E)ˣ → Matrix (Fin n) (Fin n) (AE F E) := fun t =>
    levM (f ∘ H.x) (f ∘ H.y) (f ∘ aE) (f ∘ bE) t.1 (cA σ (t⁻¹).1)
  have hone : M 1 = 1 := by simp only [M, inv_one, Units.val_one, map_one]; exact levM_one
  have hmul : ∀ t t', M (t * t') = M t * M t' := by
    intro t t'
    simp only [M]
    rw [levM_mul hax' hay' hbx' hby', _root_.mul_inv_rev, Units.val_mul, Units.val_mul, map_mul, mul_comm (cA σ _)]
  have hunit : ∀ t, (M t)ᵀ * incM F Y.J * (M t).map (cA σ) = incM F Y.J := by
    intro t
    have ha' : Y.J.map f *ᵥ ((cA σ).toRingHom ∘ (f ∘ H.y)) = f ∘ aE := by
      change _ *ᵥ (⇑(cA σ) ∘ (f ∘ H.y)) = _
      rw [hcf, map_comp_mulVec]
    have hb' : Y.J.map f *ᵥ ((cA σ).toRingHom ∘ (f ∘ H.x)) = -(f ∘ bE) := by
      change _ *ᵥ (⇑(cA σ) ∘ (f ∘ H.x)) = _
      rw [hcf, map_comp_mulVec, hbE, hneg, neg_neg]
    have hxJ' : (f ∘ H.x) ᵥ* Y.J.map f = (cA σ).toRingHom ∘ (f ∘ bE) := by
      change _ = ⇑(cA σ) ∘ (f ∘ bE)
      rw [map_comp_vecMul, hxJ, hcf]
    have hyJ' : (f ∘ H.y) ᵥ* Y.J.map f = -((cA σ).toRingHom ∘ (f ∘ aE)) := by
      change _ = -(⇑(cA σ) ∘ (f ∘ aE))
      rw [map_comp_vecMul, hyJ, hcf, hneg]
    have h1 : t.1 * (cA σ).toRingHom (cA σ (t⁻¹).1) = 1 := by
      change t.1 * cA σ (cA σ (t⁻¹).1) = 1
      rw [cA_cA hσ, Units.mul_inv]
    have h2 : cA σ (t⁻¹).1 * (cA σ).toRingHom t.1 = 1 := by
      change cA σ (t⁻¹).1 * cA σ t.1 = 1
      rw [← map_mul, Units.inv_mul, map_one]
    exact levM_unitary (cA σ).toRingHom (cA_cA hσ) ha' hb' hxJ' hyJ' hax' hay' hbx' hby' h1 h2
  refine ⟨homOf σ Y.J M hone hmul hunit t, levi_matrix_mulVec_first_vector hax' hbx' _ _, levM_mulVec_y hay' hby' _ _, ?_⟩
  change M t * incM F H.ι = incM F H.ι * 1
  rw [Matrix.mul_one]
  exact levM_mul_fix haι' hbι' _ _

theorem mat_mul'' {n : ℕ} {J : Matrix (Fin n) (Fin n) E} (a b : UA σ J) : mat (a * b) = mat a * mat b := rfl

theorem mat_one'' {n : ℕ} {J : Matrix (Fin n) (Fin n) E} : mat (1 : UA σ J) = 1 := rfl

theorem mat_inv_mul'' {n : ℕ} {J : Matrix (Fin n) (Fin n) E} (a : UA σ J) : mat a⁻¹ * mat a = 1 := by
  rw [← mat_mul'', inv_mul_cancel]; rfl

theorem mat_mul_inv'' {n : ℕ} {J : Matrix (Fin n) (Fin n) E} (a : UA σ J) : mat a * mat a⁻¹ = 1 := by
  rw [← mat_mul'', mul_inv_cancel]; rfl

theorem inv_mulVec_of' {n : ℕ} {J : Matrix (Fin n) (Fin n) E} (a : UA σ J) (c : AE F E) (hc : IsUnit c)
    (v w : Fin n → AE F E) (h : mat a *ᵥ v = c • w) : mat a⁻¹ *ᵥ w = hc.unit⁻¹.1 • v := by
  have : w = hc.unit⁻¹.1 • (mat a *ᵥ v) := by
    rw [h, smul_smul]; simp
  rw [this, Matrix.mulVec_smul, Matrix.mulVec_mulVec, mat_inv_mul'', Matrix.one_mulVec]

end GlobalTheory.IwaIsoPlane
