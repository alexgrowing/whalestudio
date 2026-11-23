import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilRepresentationPreservesSchwartz
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaTransformRationalTranslateQuasiInvariant

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

noncomputable section

namespace GlobalTheory.ThetaExpandInv

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem incM_add {m k : Type} (a b : Matrix m k E) : incM F (a + b) = incM F a + incM F b := by
  ext i j; simp [incM, Matrix.map_apply]

theorem incM_vecMulVec {m k : ℕ} (ξ : Fin m → E) (y : Fin k → E) :
    incM F (Matrix.vecMulVec ξ y) = Matrix.vecMulVec (incV F ξ) (incV F y) := by
  ext i j; simp [incM, incV, Matrix.vecMulVec_apply, map_mul]

theorem incM_mul_transpose {n d d₁ : ℕ} (U : Matrix (Fin n) (Fin d₁) E) (ι : Matrix (Fin d) (Fin d₁) E) :
    incM F (U * ιᵀ) = incM F (1 : Matrix (Fin n) (Fin n) E) * incM F U * (incM F ι)ᵀ := by
  have h1 : incM F (1 : Matrix (Fin n) (Fin n) E) = 1 :=
    Matrix.map_one _ (map_zero _) (map_one _)
  rw [h1, Matrix.one_mul]
  unfold incM
  rw [Matrix.map_mul, Matrix.transpose_map]

variable {n d : ℕ} {X : Spc F E n} {W : Spc F E d}

theorem rho_rat_rho_rat (M : Model σ X W) {ψ : AddChar (AF F) ℂ} (hψ : IsStd ψ) (hM : M.IsGood ψ)
    (a b : Matrix (Fin n) (Fin d) E) (Φ : Fn F n d) :
    M.co.rho ψ (incM F a) (M.co.rho ψ (incM F b) Φ) = M.co.rho ψ (incM F (a + b)) Φ := by
  obtain ⟨y₁, z₁, h₁⟩ := hM.rat a
  obtain ⟨y₂, z₂, h₂⟩ := hM.rat b
  have h2 : ⅟(2 : AF F) = algebraMap F (AF F) (1 / 2) := by
    apply invOf_eq_right_inv
    rw [← map_ofNat (algebraMap F (AF F)) 2, ← map_mul]
    norm_num
  unfold Darboux.rho
  rw [incM_add, map_add, GlobalTheory.ThetaQuasiRat.schr_schr, h₁, h₂]
  have hph : ψ (⅟(2 : AF F) * ((fun i => algebraMap F (AF F) (y₁ i)) ⬝ᵥ (fun i => algebraMap F (AF F) (z₂ i)) -
      (fun i => algebraMap F (AF F) (y₂ i)) ⬝ᵥ (fun i => algebraMap F (AF F) (z₁ i)))) = 1 := by
    have e : ⅟(2 : AF F) * ((fun i => algebraMap F (AF F) (y₁ i)) ⬝ᵥ (fun i => algebraMap F (AF F) (z₂ i)) -
        (fun i => algebraMap F (AF F) (y₂ i)) ⬝ᵥ (fun i => algebraMap F (AF F) (z₁ i))) =
        algebraMap F (AF F) (1 / 2 * (y₁ ⬝ᵥ z₂ - y₂ ⬝ᵥ z₁)) := by
      simp only [dotProduct, map_mul, map_sub, map_sum, h2]
    rw [e]; exact hψ.2.1 _
  simp only [hph, one_smul]

theorem thetaSum_rho_rat (M : Model σ X W) {ψ : AddChar (AF F) ℂ} (hψ : IsStd ψ) (hM : M.IsGood ψ)
    (a : Matrix (Fin n) (Fin d) E) (Φ : Fn F n d) : thetaSum F (M.co.rho ψ (incM F a) Φ) = thetaSum F Φ := by
  obtain ⟨y, z, h⟩ := hM.rat a
  unfold Darboux.rho
  rw [h]
  exact GlobalTheory.ThetaQuasiRat.thetaSum_schr_rat F ψ hψ.2.1 y z Φ

theorem exists_split {d₁ : ℕ} {W₁ : Spc F E d₁} {B : Base F E} {H' : Plane E d d₁} {i₀ i₁ : ℕ}
    (hH : H'.IsAdapted σ B W W₁ i₀ i₁) (hL : W.L.IsLattice E) (x : Matrix (Fin n) (Fin d) E) :
    ∃ (s t : Fin n → E) (U : Matrix (Fin n) (Fin d₁) E),
      x = Matrix.vecMulVec s H'.x + U * H'.ιᵀ + Matrix.vecMulVec t H'.y := by
  have hrow : ∀ r : Fin d → E, ∃ (s t : E) (u : Fin d₁ → E), r = s • H'.x + H'.ι *ᵥ u + t • H'.y := by
    let S : Submodule E (Fin d → E) :=
      { carrier := {r | ∃ (s t : E) (u : Fin d₁ → E), r = s • H'.x + H'.ι *ᵥ u + t • H'.y}
        add_mem' := by
          rintro _ _ ⟨s, t, u, rfl⟩ ⟨s', t', u', rfl⟩
          exact ⟨s + s', t + t', u + u', by rw [Matrix.mulVec_add]; module⟩
        zero_mem' := ⟨0, 0, 0, by simp⟩
        smul_mem' := by
          rintro c _ ⟨s, t, u, rfl⟩
          exact ⟨c * s, c * t, c • u, by rw [Matrix.mulVec_smul]; module⟩ }
    have hle : Submodule.span E (W.L : Set (Fin d → E)) ≤ S := by
      refine Submodule.span_le.mpr fun z hz => ?_
      obtain ⟨s, t, u, -, -, -, h⟩ := hH.split z hz
      exact ⟨s, t, u, h⟩
    rw [Submodule.IsLattice.span_eq_top] at hle
    intro r
    exact hle (Submodule.mem_top (x := r))
  choose s t u hu using fun i => hrow (x i)
  refine ⟨s, t, Matrix.of fun i k => u i k, ?_⟩
  ext i j
  have h := congrFun (hu i) j
  rw [h]
  simp only [Matrix.add_apply, Matrix.vecMulVec_apply, Matrix.mul_apply, Matrix.transpose_apply, Matrix.of_apply,
    Pi.add_apply, Pi.smul_apply, smul_eq_mul, Matrix.mulVec, dotProduct]
  congr 2
  exact Finset.sum_congr rfl fun k _ => mul_comm _ _

theorem main : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (n d d₁ : ℕ) (X : Spc F E n) (W : Spc F E d) (W₁ : Spc F E d₁) (M : Model σ X W) (M₁ : Model σ X W₁) (H' : Plane E d d₁) (i₀ i₁ : ℕ),
    H'.IsAdapted σ B W W₁ i₀ i₁ → M₁.IsGood B.ψ → ∀ (e₀ : Fn F n d →ₗ[ℂ] Fn F n d₁), IsEv B M M₁ 1 H'.ι (iso0 n H') e₀ → B.IsGood σ → M.IsGood B.ψ → (∃ r s r' s' : ℕ, X.IsHerm σ B r s ∧ W.IsSkew σ B r' s') →
    ∀ x : Matrix (Fin n) (Fin d) E, ∀ Ψ ∈ schA F (Fin n × Fin d), (∑' ξ : Fin n → E, thetaSum F (e₀ (M.co.rho B.ψ (Matrix.vecMulVec (incV F ξ) (incV F H'.y)) (M.co.rho B.ψ (incM F x) Ψ)))) = (∑' ξ : Fin n → E, thetaSum F (e₀ (M.co.rho B.ψ (Matrix.vecMulVec (incV F ξ) (incV F H'.y)) (Ψ)))) := by
  intro _ F E _ _ _ _ _ σ B n d d₁ X W W₁ M M₁ H' i₀ i₁ hH hM₁ e₀ he hB hM hsig x Ψ hΨ
  obtain ⟨r, s, r', s', -, hW⟩ := hsig
  have hψ : IsStd B.ψ := hB.std
  obtain ⟨a, t, U, hx⟩ := exists_split hH hW.lat x
  have key : ∀ ξ : Fin n → E,
      thetaSum F (e₀ (M.co.rho B.ψ (Matrix.vecMulVec (incV F ξ) (incV F H'.y)) (M.co.rho B.ψ (incM F x) Ψ))) =
        thetaSum F (e₀ (M.co.rho B.ψ (Matrix.vecMulVec (incV F (ξ + t)) (incV F H'.y)) Ψ)) := by
    intro ξ
    have hsum : Matrix.vecMulVec ξ H'.y + x =
        Matrix.vecMulVec a H'.x + (U * H'.ιᵀ + Matrix.vecMulVec (ξ + t) H'.y) := by
      rw [hx, Matrix.add_vecMulVec]; abel
    have hiso : incM F (Matrix.vecMulVec a H'.x) ∈ (iso0 n H' : Set (Matrix (Fin n) (Fin d) (AE F E))) :=
      ⟨incV F a, incM_vecMulVec a H'.x⟩
    rw [← incM_vecMulVec, rho_rat_rho_rat M hψ hM, hsum, ← rho_rat_rho_rat M hψ hM,
      he.inv _ hiso _ (GlobalTheory.HeisSchA.rho_mem_schA M B.ψ hψ _ Ψ hΨ), ← rho_rat_rho_rat M hψ hM,
      incM_mul_transpose, he.Heisenberg₂ _ _ (GlobalTheory.HeisSchA.rho_mem_schA M B.ψ hψ _ Ψ hΨ),
      thetaSum_rho_rat M₁ hψ hM₁, incM_vecMulVec]
  rw [tsum_congr key]
  exact (Equiv.addRight t).tsum_eq
    (fun ξ : Fin n → E => thetaSum F (e₀ (M.co.rho B.ψ (Matrix.vecMulVec (incV F ξ) (incV F H'.y)) Ψ)))

end GlobalTheory.ThetaExpandInv
