import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EigenIntertwinerRestrictionRankStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaSumInvariantRationalUnitaryStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilRepresentationPreservesSchwartz
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SymplecticPairingRankOneStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianFormSurjectiveAdelicStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FourierCoeffZeroOfVanishingStatement

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

noncomputable section
namespace GlobalTheory.ThKIsoMove
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
theorem actAB_vecMulVec {n d : ℕ} {X : Spc F E n} {W : Spc F E d} (γ : UA σ X.J) (y : Fin n → AE F E) (x : Fin d → AE F E) :
    actAB (cA σ) ((γ, 1) : UA σ X.J × UA σ W.J) (Matrix.vecMulVec y x) = Matrix.vecMulVec (mat γ *ᵥ y) x := by
  have h1 : (((1 : UA σ W.J) : GL (Fin d) (AE F E)) : Matrix (Fin d) (Fin d) (AE F E)) = 1 := rfl
  simp only [actAB, h1, Matrix.transpose_one, Matrix.mul_one]
  ext i j
  simp [mat, Matrix.mul_apply, Matrix.vecMulVec_apply, Matrix.mulVec, dotProduct, Finset.sum_mul, mul_assoc]

theorem twist {B : Base F E} {n d : ℕ} {X : Spc F E n} {W : Spc F E d} {M : Model σ X W} {χX χW : Chr F E}
    {om : Rep σ X W} {r s r' s' : ℕ} (hP : IsPair B M χX χW om r s r' s') (γ : UA σ X.J) (hγ : γ ∈ ratU σ X.J) :
    ∃ τ : (Fin n → E) ≃ (Fin n → E), ∀ (v : Fin d → E) (ξ : Fin n → E), ∀ Ψ ∈ schA F (Fin n × Fin d),
      M.co.rho B.ψ (Matrix.vecMulVec (incV F ξ) (incV F v)) (om (γ, 1) Ψ) =
        om (γ, 1) (M.co.rho B.ψ (Matrix.vecMulVec (incV F (τ ξ)) (incV F v)) Ψ) := by
  have hS := hP.weil.isUSplitting
  rw [ratU, Subgroup.mem_subgroupOf] at hγ
  obtain ⟨g₀, hg₀⟩ := hγ
  have hmat : mat γ = (g₀ : Matrix (Fin n) (Fin n) E).map (inclR (F := F) (E := E) (AF F)) := by
    rw [mat, ← hg₀]; rfl
  have hl : ∀ ξ : Fin n → E, (g₀ : Matrix (Fin n) (Fin n) E) *ᵥ (((g₀⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) *ᵥ ξ) = ξ := by
    intro ξ; rw [Matrix.mulVec_mulVec, ← Matrix.GeneralLinearGroup.coe_mul, mul_inv_cancel]; simp
  have hr : ∀ ξ : Fin n → E, ((g₀⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) *ᵥ ((g₀ : Matrix (Fin n) (Fin n) E) *ᵥ ξ) = ξ := by
    intro ξ; rw [Matrix.mulVec_mulVec, ← Matrix.GeneralLinearGroup.coe_mul, inv_mul_cancel]; simp
  refine ⟨⟨fun ξ => ((g₀⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) *ᵥ ξ, fun ξ => (g₀ : Matrix (Fin n) (Fin n) E) *ᵥ ξ, hl, hr⟩, ?_⟩
  intro v ξ Ψ hΨ
  simp only [Equiv.coe_fn_mk]
  rw [hS.impl _ _ Ψ hΨ, actAB_vecMulVec]
  congr 2
  rw [hmat]
  funext i
  have hc : incV F (((g₀⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) *ᵥ ξ) =
      (inclR (F := F) (E := E) (AF F)) ∘ (((g₀⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) *ᵥ ξ) := rfl
  rw [hc, ← RingHom.map_mulVec, hl]
  rfl

theorem rho_comm {n d : ℕ} {X : Spc F E n} {W : Spc F E d} (M : Model σ X W) (ψ : AddChar (AF F) ℂ)
    (u v : Matrix (Fin n) (Fin d) (AE F E)) (Φ : Fn F n d) :
    M.co.rho ψ u (M.co.rho ψ v Φ) = ψ (symp (cA σ) (-1) (incM F X.J) (incM F W.J) u v) • M.co.rho ψ v (M.co.rho ψ u Φ) := by
  rw [M.co.form u v]
  funext x
  simp only [Darboux.rho, schr, Pi.smul_apply, smul_eq_mul]
  set a := M.co.e u
  set b := M.co.e v
  rw [show x + b.1 + a.1 = x + a.1 + b.1 by abel]
  rw [← mul_assoc, ← mul_assoc, ← mul_assoc, ← AddChar.map_add_eq_mul, ← AddChar.map_add_eq_mul, ← AddChar.map_add_eq_mul]
  congr 2
  simp only [add_dotProduct]
  rw [dotProduct_comm a.1 b.2, dotProduct_comm b.1 a.2]
  ring

theorem rho_zero {n d : ℕ} {X : Spc F E n} {W : Spc F E d} (M : Model σ X W) (ψ : AddChar (AF F) ℂ) (Φ : Fn F n d) :
    M.co.rho ψ 0 Φ = Φ := by
  funext x
  simp [Darboux.rho, schr]

theorem isolate {B : Base F E} {n d : ℕ} {X : Spc F E n} {W : Spc F E d} {M : Model σ X W} {χX χW : Chr F E}
    {om : Rep σ X W} {r s r' s' : ℕ} (hP : IsPair B M χX χW om r s r' s') {d₁ : ℕ} {W₁ : Spc F E d₁} {H' : Plane E d d₁}
    {i₀ i₁ : ℕ} (hH : H'.IsAdapted σ B W W₁ i₀ i₁) (D : Fn F n d → ℂ)
    (hD : ∀ c : ℂ, ∀ Ψ ∈ schA F (Fin n × Fin d), D (c • Ψ) = c * D Ψ)
    (hinv : ∀ y : Fin n → AE F E, ∀ Ψ ∈ schA F (Fin n × Fin d), D (M.co.rho B.ψ (Matrix.vecMulVec y (incV F H'.x)) Ψ) = D Ψ)
    (hsum : ∀ Ψ ∈ schA F (Fin n × Fin d), Summable (fun ξ : Fin n → E => D (M.co.rho B.ψ (Matrix.vecMulVec (incV F ξ) (incV F H'.y)) Ψ)) ∧
      ∑' ξ : Fin n → E, D (M.co.rho B.ψ (Matrix.vecMulVec (incV F ξ) (incV F H'.y)) Ψ) = 0) :
    ∀ Ψ ∈ schA F (Fin n × Fin d), D Ψ = 0 := by
  intro Ψ hΨ
  have hψ : IsStd B.ψ := hP.base.std
  have mem : ∀ w Φ, Φ ∈ schA F (Fin n × Fin d) → M.co.rho B.ψ w Φ ∈ schA F (Fin n × Fin d) :=
    fun w Φ hΦ => GlobalTheory.HeisSchA.schr_mem_schA B.ψ hψ _ Φ hΦ
  let a : (Fin n → E) → ℂ := fun ξ => D (M.co.rho B.ψ (Matrix.vecMulVec (incV F ξ) (incV F H'.y)) Ψ)
  have ha : Summable a := (hsum Ψ hΨ).1
  have key : a 0 = 0 := by
    refine GlobalTheory.T.fourier_coeff_zero_of_vanishing F E B.ψ hψ n a ha fun z => ?_
    obtain ⟨y, hy⟩ := GlobalTheory.T.hermitian_form_surjective_adelic F E σ B n r s X hP.base hP.herm z
    have h0 := (hsum _ (mem (Matrix.vecMulVec y (incV F H'.x)) Ψ hΨ)).2
    rw [← h0]
    refine tsum_congr fun ξ => ?_
    rw [rho_comm, hD _ _ (mem _ _ (mem _ _ hΨ)), hinv _ _ (mem _ _ hΨ), GlobalTheory.T.symplectic_pairing_rank_one F E σ B n d d₁ X W W₁ H' i₀ i₁ r s r' s' hP.base hP.herm hP.skew hH, hy]
  have e0 : Matrix.vecMulVec (incV F (0 : Fin n → E)) (incV F H'.y) = 0 := by
    ext i j; simp [incV, Matrix.vecMulVec_apply]
  simpa [a, e0, rho_zero] using key

theorem thetaSum_eval_rat_inv : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (n d d₁ : ℕ) (X : Spc F E n) (W : Spc F E d) (W₁ : Spc F E d₁) (M : Model σ X W) (M₁ : Model σ X W₁) (H' : Plane E d d₁) (i₀ i₁ : ℕ),
    H'.IsAdapted σ B W W₁ i₀ i₁ → M₁.IsGood B.ψ → ∀ (e₀ : Fn F n d →ₗ[ℂ] Fn F n d₁), IsEv B M M₁ 1 H'.ι (iso0 n H') e₀ →
    ∀ (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ), IsPair B M χX χW om r s r' s' → ∀ γ ∈ ratU σ X.J, ∀ Φ ∈ schA F (Fin n × Fin d), thetaSum F (e₀ (om (γ, 1) Φ)) = thetaSum F (e₀ Φ) := by
  intro hK F E _ _ _ _ _ σ B n d d₁ X W W₁ M M₁ H' i₀ i₁ hH hM₁ e₀ he₀ χX χW om r s r' s' hP γ hγ
  have hS := hP.weil.isUSplitting
  have hψ : IsStd B.ψ := hP.base.std
  have pres : ∀ Ψ ∈ schA F (Fin n × Fin d), om (γ, 1) Ψ ∈ schA F (Fin n × Fin d) := fun Ψ hΨ => hS.pres _ Ψ hΨ
  have mem : ∀ w Φ, Φ ∈ schA F (Fin n × Fin d) → M.co.rho B.ψ w Φ ∈ schA F (Fin n × Fin d) :=
    fun w Φ hΦ => GlobalTheory.HeisSchA.schr_mem_schA B.ψ hψ _ Φ hΦ
  obtain ⟨C₀, hC₀, hexp⟩ := GlobalTheory.T.eigen_intertwiner_restriction_rank hK F E σ B n d d₁ X W W₁ M M₁ H' i₀ i₁ hH hM₁ e₀ he₀ hP.base hP.good
    ⟨r, s, r', s', hP.herm, hP.skew⟩
  obtain ⟨τ, hτ⟩ := twist hP γ hγ
  have hinv := GlobalTheory.T.thetaSum_invariant_rational_unitary hK.base F E σ B n d X W M χX χW om r s r' s' hP γ hγ 1 (one_mem _)
  let w : (Fin n → E) → Matrix (Fin n) (Fin d) (AE F E) := fun ξ => Matrix.vecMulVec (incV F ξ) (incV F H'.y)
  let D : Fn F n d → ℂ := fun Ψ => thetaSum F (e₀ (om (γ, 1) Ψ)) - thetaSum F (e₀ Ψ)
  have hD : ∀ c : ℂ, ∀ Ψ ∈ schA F (Fin n × Fin d), D (c • Ψ) = c * D Ψ := by
    intro c Ψ _
    simp only [D, map_smul, thetaSum_smul, mul_sub]
  have hDinv : ∀ y : Fin n → AE F E, ∀ Ψ ∈ schA F (Fin n × Fin d),
      D (M.co.rho B.ψ (Matrix.vecMulVec y (incV F H'.x)) Ψ) = D Ψ := by
    intro y Ψ hΨ
    have h1 : om (γ, 1) (M.co.rho B.ψ (Matrix.vecMulVec y (incV F H'.x)) Ψ) =
        M.co.rho B.ψ (Matrix.vecMulVec (mat γ *ᵥ y) (incV F H'.x)) (om (γ, 1) Ψ) := by
      rw [hS.impl _ _ Ψ hΨ, actAB_vecMulVec]
    simp only [D]
    rw [h1, he₀.inv _ ⟨_, rfl⟩ _ (pres Ψ hΨ), he₀.inv _ ⟨_, rfl⟩ _ hΨ]
  have hDsum : ∀ Ψ ∈ schA F (Fin n × Fin d), Summable (fun ξ : Fin n → E => D (M.co.rho B.ψ (w ξ) Ψ)) ∧
      ∑' ξ : Fin n → E, D (M.co.rho B.ψ (w ξ) Ψ) = 0 := by
    intro Ψ hΨ
    obtain ⟨s1, e1⟩ := hexp Ψ hΨ
    obtain ⟨s2, e2⟩ := hexp _ (pres Ψ hΨ)
    have r2 : ∀ ξ, thetaSum F (e₀ (M.co.rho B.ψ (w ξ) (om (γ, 1) Ψ))) = thetaSum F (e₀ (om (γ, 1) (M.co.rho B.ψ (w (τ ξ)) Ψ))) :=
      fun ξ => by rw [hτ H'.y ξ Ψ hΨ]
    simp only [w] at r2
    simp_rw [r2] at s2 e2
    have s3 : Summable (fun η : Fin n → E => thetaSum F (e₀ (om (γ, 1) (M.co.rho B.ψ (w η) Ψ)))) :=
      (τ.summable_iff (f := fun η : Fin n → E => thetaSum F (e₀ (om (γ, 1) (M.co.rho B.ψ (w η) Ψ))))).1 s2
    have e3 : ∑' η : Fin n → E, thetaSum F (e₀ (om (γ, 1) (M.co.rho B.ψ (w η) Ψ))) =
        ∑' ξ : Fin n → E, thetaSum F (e₀ (om (γ, 1) (M.co.rho B.ψ (w (τ ξ)) Ψ))) :=
      (τ.tsum_eq (fun η : Fin n → E => thetaSum F (e₀ (om (γ, 1) (M.co.rho B.ψ (w η) Ψ))))).symm
    refine ⟨s3.sub s1, ?_⟩
    rw [s3.tsum_sub s1, sub_eq_zero]
    apply mul_left_cancel₀ hC₀
    rw [e3, ← e1]
    simp only [w]
    rw [← e2, hinv Ψ hΨ]
  intro Φ hΦ
  have := isolate hP hH D hD hDinv hDsum Φ hΦ
  exact sub_eq_zero.1 this

end GlobalTheory.ThKIsoMove
