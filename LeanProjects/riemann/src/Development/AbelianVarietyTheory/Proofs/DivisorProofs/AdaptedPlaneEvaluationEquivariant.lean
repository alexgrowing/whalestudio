import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EvaluationMapAdaptedPlaneContinuous
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdaptedPlaneComplementSplitBasis
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryFixingVectorPreserves
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EigenIntertwinerRestrictionPairStatement

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

noncomputable section

namespace GlobalTheory.UnipThetaTerm

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem inclR_injective : Function.Injective (inclR (F := F) (E := E) (AF F)) :=
  Algebra.TensorProduct.includeRight_injective (AdeleRing.algebraMap_injective (𝓞 F) F)

theorem incM_injective {m k : Type} : Function.Injective (incM (E := E) F : Matrix m k E → Matrix m k (AE F E)) :=
  Matrix.map_injective inclR_injective

theorem incV_injective {m : ℕ} : Function.Injective (incV (E := E) F : (Fin m → E) → Fin m → AE F E) :=
  fun a b h => funext fun i => inclR_injective (congrFun h i)

theorem unip_fix {d d₁ : ℕ} {W : Spc F E d} {H' : Plane E d d₁} (u : UA σ W.J) (hu : u ∈ unip σ W H') :
    mat u *ᵥ incV F H'.x = incV F H'.x := by
  induction hu using Subgroup.closure_induction with
  | mem x hx => exact hx.1
  | one => exact Matrix.one_mulVec _
  | mul x y _ _ hx hy => rw [GlobalTheory.UnipLine.mulVec_mul, hy, hx]
  | inv x _ hx => exact GlobalTheory.UnipLine.inv_mulVec_of_mulVec hx

theorem rat_mat {d : ℕ} {J : Matrix (Fin d) (Fin d) E} (γ : UA σ J) (hγ : γ ∈ ratU σ J) :
    ∃ h : Matrix (Fin d) (Fin d) E, mat γ = incM F h := by
  obtain ⟨g, hg⟩ := Subgroup.mem_subgroupOf.mp hγ
  exact ⟨g.1, by rw [mat, ← hg]; rfl⟩

theorem unitary_of_rat {d : ℕ} {J : Matrix (Fin d) (Fin d) E} (γ : UA σ J) (h : Matrix (Fin d) (Fin d) E)
    (hh : mat γ = incM F h) : hᵀ * J * h.map σ = J := by
  apply incM_injective (F := F)
  have hU : (mat γ)ᵀ * incM F J * (mat γ).map (cA σ) = incM F J := γ.2
  rw [hh] at hU
  rw [← hU]
  have e : (incM F h).map (cA σ) = incM F (h.map σ) := by
    ext i j; simp only [incM, Matrix.map_apply]; exact GlobalTheory.UnipLine.cA_inclR _
  rw [e]
  unfold incM
  rw [Matrix.map_mul, Matrix.map_mul, Matrix.transpose_map]

theorem form_mulVec {d : ℕ} {J h : Matrix (Fin d) (Fin d) E} (hU : hᵀ * J * h.map σ = J) (a b : Fin d → E) :
    form σ J (h *ᵥ a) (h *ᵥ b) = form σ J a b := by
  unfold form
  have e1 : (fun i => σ ((h *ᵥ b) i)) = h.map σ *ᵥ fun i => σ (b i) := by
    funext i; exact RingHom.map_mulVec (σ : E →+* E) h b i
  rw [e1, Matrix.mulVec_mulVec, dotProduct_comm, Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose,
    dotProduct_comm, Matrix.mulVec_mulVec, ← Matrix.mul_assoc, hU]

theorem form_add_left {d : ℕ} (J : Matrix (Fin d) (Fin d) E) (a b c : Fin d → E) :
    form σ J (a + b) c = form σ J a c + form σ J b c := add_dotProduct _ _ _

theorem form_smul_left {d : ℕ} (J : Matrix (Fin d) (Fin d) E) (t : E) (a c : Fin d → E) :
    form σ J (t • a) c = t * form σ J a c := smul_dotProduct _ _ _

theorem vecMulVec_mul_transpose {n d : ℕ} (ξ : Fin n → E) (y : Fin d → E) (h : Matrix (Fin d) (Fin d) E) :
    Matrix.vecMulVec ξ y * hᵀ = Matrix.vecMulVec ξ (h *ᵥ y) := by
  ext i j
  simp only [Matrix.mul_apply, Matrix.vecMulVec_apply, Matrix.transpose_apply, Matrix.mulVec, dotProduct,
    Finset.mul_sum]
  exact Finset.sum_congr rfl fun k _ => by ring

end GlobalTheory.UnipThetaTerm

open GlobalTheory.UnipThetaTerm in

theorem GlobalTheory.UnipThetaTerm.main : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (n d d₁ : ℕ) (X : Spc F E n) (W : Spc F E d) (W₁ : Spc F E d₁) (M : Model σ X W) (M₁ : Model σ X W₁) (H' : Plane E d d₁) (i₀ i₁ : ℕ),
    H'.IsAdapted σ B W W₁ i₀ i₁ → M₁.IsGood B.ψ → ∀ (e₀ : Fn F n d →ₗ[ℂ] Fn F n d₁), IsEv B M M₁ 1 H'.ι (iso0 n H') e₀ → ∀ (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ), IsPair B M χX χW om r s r' s' → ∀ Ψ ∈ schA F (Fin n × Fin d),
      ∀ (ξ : Fin n → E) (γ u : unip σ W H'), γ.1 ∈ ratU σ W.J → thetaSum F (e₀ (M.co.rho B.ψ (Matrix.vecMulVec (incV F ξ) (incV F H'.y)) (om (1, (γ * u).1) Ψ))) = thetaSum F (e₀ (M.co.rho B.ψ (Matrix.vecMulVec (incV F ξ) (incV F H'.y)) (om (1, u.1) Ψ))) := by
  intro hKP F E _ _ _ _ _ σ B n d d₁ X W W₁ M M₁ H' i₀ i₁ hH hM₁ e₀ he χX χW om r s r' s' hP Ψ hΨ ξ γ u hγ
  have hB := hP.base
  have hψ : IsStd B.ψ := hB.std
  have hM := hP.good
  have hW := hP.skew
  have hS := hP.weil.isUSplitting
  have rmem : ∀ (w : Matrix (Fin n) (Fin d) (AE F E)) (Φ : Fn F n d), Φ ∈ schA F (Fin n × Fin d) →
      M.co.rho B.ψ w Φ ∈ schA F (Fin n × Fin d) := fun w Φ hΦ => GlobalTheory.HeisSchA.rho_mem_schA M B.ψ hψ w Φ hΦ
  have hYs : om (1, u.1) Ψ ∈ schA F (Fin n × Fin d) := hS.pres _ _ hΨ
  have hsplit : om (1, (γ * u).1) Ψ = om (1, γ.1) (om (1, u.1) Ψ) := by
    rw [← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk, one_mul]; rfl
  obtain ⟨h, hh⟩ := rat_mat (γ.1⁻¹) (inv_mem hγ)
  have hU := unitary_of_rat _ h hh
  have hfix : h *ᵥ H'.x = H'.x := by
    apply incV_injective (F := F)
    rw [← GlobalTheory.UnipLine.incM_mulVec_incV, ← hh]
    exact unip_fix _ (inv_mem γ.2)
  have hA : Matrix.vecMulVec (incV F ξ) (incV F H'.y) = incM F (Matrix.vecMulVec ξ H'.y) :=
    (GlobalTheory.ThetaExpandInv.incM_vecMulVec ξ H'.y).symm
  have hact : actAB (cA σ) ((1 : UA σ X.J), γ.1) (incM F (Matrix.vecMulVec ξ (h *ᵥ H'.y))) =
      Matrix.vecMulVec (incV F ξ) (incV F H'.y) := by
    have e1 : incM F (Matrix.vecMulVec ξ (h *ᵥ H'.y)) = Matrix.vecMulVec (incV F ξ) (incV F H'.y) * (mat γ.1⁻¹)ᵀ := by
      rw [← vecMulVec_mul_transpose, hh, hA]
      unfold incM
      rw [Matrix.map_mul, Matrix.transpose_map]
    rw [e1]
    show (1 : Matrix (Fin n) (Fin n) (AE F E)) * (Matrix.vecMulVec (incV F ξ) (incV F H'.y) * (mat γ.1⁻¹)ᵀ) * (mat γ.1)ᵀ = _
    rw [Matrix.one_mul, Matrix.mul_assoc, ← Matrix.transpose_mul, ← GlobalTheory.UnipLine.mat_mul, mul_inv_cancel,
      GlobalTheory.UnipLine.mat_one, Matrix.transpose_one, Matrix.mul_one]
  have key1 : M.co.rho B.ψ (Matrix.vecMulVec (incV F ξ) (incV F H'.y)) (om (1, γ.1) (om (1, u.1) Ψ)) =
      om (1, γ.1) (M.co.rho B.ψ (incM F (Matrix.vecMulVec ξ (h *ᵥ H'.y))) (om (1, u.1) Ψ)) := by
    rw [hS.impl _ _ _ hYs, hact]
  rw [hsplit, key1, GlobalTheory.T.eigen_intertwiner_restriction_pair hKP F E σ B n d d₁ X W W₁ M M₁ H' i₀ i₁ hH hM₁ e₀ he χX χW om r s r' s' hP γ.1 γ.2 _
    (rmem _ _ hYs)]
  obtain ⟨a, t, U, hx⟩ := GlobalTheory.ThetaExpandInv.exists_split hH hW.lat (Matrix.vecMulVec ξ (h *ᵥ H'.y))
  have hyx : form σ W.J H'.y H'.x = -1 := by
    rw [GlobalTheory.AdaptedPlaneBasis.form_swap hB.cm hW.skew, hH.xy, map_one]
  have ht : t = ξ := by
    funext i
    have hrow := congrFun hx i
    have l : (Matrix.vecMulVec ξ (h *ᵥ H'.y)) i = ξ i • (h *ᵥ H'.y) := by
      funext j; simp [Matrix.vecMulVec_apply]
    have r : (Matrix.vecMulVec a H'.x + U * H'.ιᵀ + Matrix.vecMulVec t H'.y) i =
        a i • H'.x + H'.ι *ᵥ (U i) + t i • H'.y := by
      funext j
      simp only [Matrix.add_apply, Matrix.vecMulVec_apply, Matrix.mul_apply, Matrix.transpose_apply, Pi.add_apply,
        Pi.smul_apply, smul_eq_mul, Matrix.mulVec, dotProduct]
      congr 1; congr 1
      exact Finset.sum_congr rfl fun k _ => mul_comm _ _
    have e : form σ W.J ((Matrix.vecMulVec ξ (h *ᵥ H'.y)) i) H'.x =
        form σ W.J ((Matrix.vecMulVec a H'.x + U * H'.ιᵀ + Matrix.vecMulVec t H'.y) i) H'.x := by rw [hrow]
    have e2 : form σ W.J (h *ᵥ H'.y) H'.x = -1 := by
      conv_lhs => rw [← hfix]
      rw [form_mulVec hU, hyx]
    rw [l, r, form_add_left, form_add_left, form_smul_left, form_smul_left, form_smul_left, hH.xx, (hH.orth _).1,
      hyx, e2] at e
    linear_combination e
  rw [ht] at hx
  have m1 : M.co.rho B.ψ (incM F (Matrix.vecMulVec ξ H'.y)) (om (1, u.1) Ψ) ∈ schA F (Fin n × Fin d) := rmem _ _ hYs
  have m2 := rmem (incM F (U * H'.ιᵀ)) _ m1
  have hiso : incM F (Matrix.vecMulVec a H'.x) ∈ (iso0 n H' : Set (Matrix (Fin n) (Fin d) (AE F E))) :=
    ⟨incV F a, GlobalTheory.ThetaExpandInv.incM_vecMulVec a H'.x⟩
  rw [hx, add_assoc, ← GlobalTheory.ThetaExpandInv.rho_rat_rho_rat M hψ hM, ← GlobalTheory.ThetaExpandInv.rho_rat_rho_rat M hψ hM,
    he.inv _ hiso _ m2, GlobalTheory.ThetaExpandInv.incM_mul_transpose, he.Heisenberg₂ _ _ m1,
    GlobalTheory.ThetaExpandInv.thetaSum_rho_rat M₁ hψ hM₁, hA]
