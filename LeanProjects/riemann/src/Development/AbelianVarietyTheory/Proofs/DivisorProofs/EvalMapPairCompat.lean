import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnipotentFundamentalDomain
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EigenIntertwinerRestrictionPairStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilRepresentationPreservesSchwartz
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSplittingSplitOm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicTraceSupportedAtSplitPlace

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

noncomputable section

namespace GlobalTheory.ThK.AnisPhase

theorem hTens_vecMulVec {R A : Type} [CommRing R] [CommRing A] [Algebra R A] (c : A →ₐ[R] A) {α β : Type}
    [Fintype α] [Fintype β] (JA : Matrix α α A) (JB : Matrix β β A) (p p' : α → A) (q q' : β → A) :
    hTens c JA JB (Matrix.vecMulVec p q) (Matrix.vecMulVec p' q') =
      (p ⬝ᵥ JA *ᵥ fun k => c (p' k)) * (q ⬝ᵥ JB *ᵥ fun l => c (q' l)) := by
  calc hTens c JA JB (Matrix.vecMulVec p q) (Matrix.vecMulVec p' q')
      = ∑ i, ∑ j, ∑ k, ∑ l, (p i * JA i k * c (p' k)) * (q j * JB j l * c (q' l)) := by
        simp only [hTens, Matrix.vecMulVec_apply, map_mul]
        exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ =>
          Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => by ring
    _ = _ := by
        rw [dotProduct, dotProduct, Finset.sum_mul_sum]
        refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
        simp only [Matrix.mulVec, dotProduct]
        rw [Finset.mul_sum, Finset.mul_sum, Finset.sum_mul_sum]
        exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => by ring

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem form_self_fixed {σ : E →ₐ[F] E} (hσ : ∀ x, σ (σ x) = x) {n : ℕ} {J : Matrix (Fin n) (Fin n) E}
    (hJ : ∀ i j, σ (J j i) = J i j) (ξ : Fin n → E) : σ (form σ J ξ ξ) = form σ J ξ ξ := by
  simp only [form, dotProduct, Matrix.mulVec, map_sum, map_mul, hσ, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [hJ]
  ring

theorem invOf_two_eq : ⅟(2 : AF F) = algebraMap F (AF F) (1 / 2) := by
  apply invOf_eq_right_inv
  rw [← map_ofNat (algebraMap F (AF F)) 2, ← map_mul]
  norm_num

open GlobalTheory.ThK.AnisPhase in

theorem thetaSum_center_phase : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (n d d₁ : ℕ) (X : Spc F E n) (W : Spc F E d) (W₁ : Spc F E d₁) (M : Model σ X W) (M₁ : Model σ X W₁) (H' : Plane E d d₁) (i₀ i₁ : ℕ),
    H'.IsAdapted σ B W W₁ i₀ i₁ → M₁.IsGood B.ψ → ∀ (e₀ : Fn F n d →ₗ[ℂ] Fn F n d₁), IsEv B M M₁ 1 H'.ι (iso0 n H') e₀ → ∀ (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ), IsPair B M χX χW om r s r' s' → ∀ ξ : Fin n → E, form σ X.J ξ ξ ≠ 0 → ∃ κ : F, κ ≠ 0 ∧ ∀ (t : AF F) (z : UA σ W.J), z ∈ unip σ W H' →
      mat z⁻¹ *ᵥ incV F H'.y = incV F H'.y - algebraMap (AF F) (AE F E) t • incV F H'.x → ∀ (u : UA σ W.J), ∀ Ψ ∈ schA F (Fin n × Fin d),
      thetaSum F (e₀ (M.co.rho B.ψ (Matrix.vecMulVec (incV F ξ) (incV F H'.y)) (om (1, z * u) Ψ))) = B.ψ (t * algebraMap F (AF F) κ) * thetaSum F (e₀ (M.co.rho B.ψ (Matrix.vecMulVec (incV F ξ) (incV F H'.y)) (om (1, u) Ψ))) := by
  intro hKP F E _ _ _ _ _ σ B n d d₁ X W W₁ M M₁ H' i₀ i₁ hH hM₁ e₀ hE χX χW om r s r' s' hP ξ hξ
  haveI : FiniteDimensional F E := Module.finite_of_finrank_pos (by rw [hP.base.cm.2.2.1]; norm_num)
  set f : E := form σ X.J ξ ξ with hf
  have hσf : σ f = f := form_self_fixed (GlobalTheory.AdelicU.cm_conj_conj hP.base.cm) hP.herm.herm ξ
  have htr : Algebra.trace F E f ≠ 0 := by
    intro h0
    have h1 := GlobalTheory.SplitAdeleTrace.add_conj_eq_trace hP.base.cm f
    rw [hσf, h0, map_zero, ← two_mul] at h1
    exact hξ ((mul_eq_zero.1 h1).resolve_left two_ne_zero)
  refine ⟨-(Algebra.trace F E f / 2), neg_ne_zero.2 (div_ne_zero htr two_ne_zero), ?_⟩
  intro t z hz hzy u Ψ hΨ
  have hsplit := IsUWeilPair.isUSplitting hP.weil
  have hΦ : om (1, u) Ψ ∈ schA F (Fin n × Fin d) := hsplit.pres (1, u) Ψ hΨ
  have hmul : om (1, z * u) Ψ = om (1, z) (om (1, u) Ψ) := by
    rw [← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk, one_mul]
  set Φ := om (1, u) Ψ with hΦdef
  set C : AE F E := algebraMap (AF F) (AE F E) t with hC
  set wξ := Matrix.vecMulVec (incV F ξ) (incV F H'.y) with hwξ
  set a := Matrix.vecMulVec (-(C • incV F ξ)) (incV F H'.x) with ha
  have hsum : wξ + a = Matrix.vecMulVec (incV F ξ) (mat z⁻¹ *ᵥ incV F H'.y) := by
    rw [hzy]
    ext i j
    simp only [hwξ, ha, Matrix.add_apply, Matrix.vecMulVec_apply, Pi.neg_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
    ring
  have hzz : ((z : GL (Fin d) (AE F E)) : Matrix (Fin d) (Fin d) (AE F E)) * mat z⁻¹ = 1 := by
    simp [mat]
  have hact : actAB (cA σ) ((1 : UA σ X.J), z) (wξ + a) = wξ := by
    rw [hsum, actAB]
    rw [show (((1 : UA σ X.J) : GL (Fin n) (AE F E)) : Matrix (Fin n) (Fin n) (AE F E)) = 1 from rfl, Matrix.one_mul,
      Matrix.vecMulVec_mul, Matrix.vecMul_transpose, Matrix.mulVec_mulVec, hzz, Matrix.one_mulVec]
  have hrho := hsplit.impl (1, z) (wξ + a) Φ hΦ
  rw [hact] at hrho
  have hm1 := GlobalTheory.HeisSchA.rho_mem_schA M B.ψ hP.base.std (wξ + a) Φ hΦ
  have hm2 := GlobalTheory.HeisSchA.rho_mem_schA M B.ψ hP.base.std wξ Φ hΦ
  have h60 := GlobalTheory.T.eigen_intertwiner_restriction_pair hKP F E σ B n d d₁ X W W₁ M M₁ H' i₀ i₁ hH hM₁ e₀ hE χX χW om r s r' s' hP z hz _ hm1
  set S := symp (R := AF F) (cA σ) (-1) (incM F X.J) (incM F W.J) a wξ with hS
  have hcomp : M.co.rho B.ψ a (M.co.rho B.ψ wξ Φ) = B.ψ (⅟2 * S) • M.co.rho B.ψ (a + wξ) Φ := by
    simp only [Darboux.rho]
    rw [schr_schr, hS, M.co.form a wξ, map_add]
  have hρ : M.co.rho B.ψ (wξ + a) Φ = B.ψ (-(⅟2 * S)) • M.co.rho B.ψ a (M.co.rho B.ψ wξ Φ) := by
    rw [hcomp, smul_smul, ← AddChar.map_add_eq_mul, neg_add_cancel, AddChar.map_zero_eq_one, one_smul, add_comm]
  have hinv := hE.inv a ⟨-(C • incV F ξ), rfl⟩ _ hm2
  have e1 : (incV F ξ ⬝ᵥ incM F X.J *ᵥ fun k => cA σ (incV F ξ k)) = inclR (F := F) (AF F) f :=
    GlobalTheory.UnipMass.hA_incV σ X.J ξ ξ
  have e2 : (incV F H'.x ⬝ᵥ incM F W.J *ᵥ fun k => cA σ (incV F H'.y k)) = 1 := by
    rw [show (incV F H'.x ⬝ᵥ incM F W.J *ᵥ fun k => cA σ (incV F H'.y k)) = GlobalTheory.UnipMass.hA σ W.J (incV F H'.x) (incV F H'.y) from rfl,
      GlobalTheory.UnipMass.hA_incV, hH.xy, map_one]
  have e3 : C * inclR (F := F) (AF F) f = t ⊗ₜ[F] f := by
    rw [hC, Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply]
    show (t ⊗ₜ[F] (1 : E)) * ((1 : AF F) ⊗ₜ[F] f) = _
    rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
  have hS' : S = t * algebraMap F (AF F) (Algebra.trace F E f) := by
    rw [hS, symp, ha, hwξ, hTens_vecMulVec, neg_dotProduct, smul_dotProduct, smul_eq_mul, e1, e2, mul_one, neg_one_mul,
      neg_neg, e3, GlobalTheory.SplitAdeleTrace.trace_baseChange_tmul]
  have hphase : -(⅟2 * S) = t * algebraMap F (AF F) (-(Algebra.trace F E f / 2)) := by
    rw [hS', invOf_two_eq, show -(Algebra.trace F E f / 2) = -((1 / 2) * Algebra.trace F E f) by ring, map_neg, map_mul]
    ring
  rw [hmul, ← hrho, h60, hρ, map_smul, hinv, hphase]
  simp only [thetaSum, Pi.smul_apply, smul_eq_mul]
  exact tsum_mul_left

end GlobalTheory.ThK.AnisPhase
