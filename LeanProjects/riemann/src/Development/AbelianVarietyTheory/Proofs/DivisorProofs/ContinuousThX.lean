import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Definitions.Divisors.PairsOfSquareTriple
import Development.AbelianVarietyTheory.Definitions.Divisors.IsPairOfIsTriple
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EisAtMinusRho
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocUnifSum
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RatStab
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilRepresentationPreservesSchwartz
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SecondConfigurationTripleCompatible
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaBasicPropertiesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaEvaluationZeroConeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdaptedPlaneSecondVariableStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdaptedPlaneFirstVariableStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGoodSchrodingerModelStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeCharactersRestrictionEtaStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConfigBTripleEvaluationCompatibleStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConfigBIntermediateModelEvaluationStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EvRhoUnipShift
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RationalLineStabilizerDecompositionStatement

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)
open GlobalTheory.ConeSmallUnf

noncomputable section

namespace GlobalTheory.ConeRearr

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

def thX (B : Base F E) {n n₁ d d₁ : ℕ} {X : Spc F E n} {W : Spc F E d} (M : Model σ X W) (H : Plane E n n₁)
    (H' : Plane E d d₁) (e : Fn F n d →ₗ[ℂ] Fn F n₁ d₁) (om : Rep σ X W) (Φ : Fn F n d)
    (g : UA σ X.J) (h : UA σ W.J) : ℂ :=
  thetaSum F (e (M.co.rho B.ψ (shiftB σ H H' 1) (om (g, h) Φ)))

theorem thetaSum_smul {κ : Type} (c : ℂ) (Φ : (κ → AF F) → ℂ) : thetaSum F (c • Φ) = c * thetaSum F Φ := by
  simp only [thetaSum, Pi.smul_apply, smul_eq_mul, tsum_mul_left]

theorem vecMulVec_mul_transpose {R : Type} [CommRing R] {n d : ℕ} (y : Fin n → R) (x : Fin d → R)
    (N : Matrix (Fin d) (Fin d) R) : Matrix.vecMulVec y x * Nᵀ = Matrix.vecMulVec y (N *ᵥ x) := by
  ext i j
  simp only [Matrix.mul_apply, Matrix.vecMulVec_apply, Matrix.transpose_apply, Matrix.mulVec, dotProduct,
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  ring

theorem ev_law (hK : GlobalTheory.FunPr.Hypotheses₂) {B : Base F E} {a b : ℕ} {G : Geo σ a (b + 2)} {G₁ : Geo σ a b}
    {H : Plane E (b + 2) b} {H' : Plane E (a + (b + 2)) (a + b)} (hC : CfgB B G G₁ H H') {e'}
    (he' : IsEv B G.M' G₁.M' H.ι H'.ι (isoB H H') e') {X om om' om₁ om₁'} (hT : IsTriple B G X om om')
    (hT₁ : IsTriple B G₁ X om₁ om₁')
    {l : (AE F E)ˣ} {g₀ : UA σ G₁.V'.J} {m u : UA σ G.V'.J} (hm : IsLevi H l g₀ m) (hu : u ∈ unip σ G.V' H)
    {t : (AE F E)ˣ} {h₁ : UA σ G₁.W.J} {m' u' : UA σ G.W.J} (hm' : IsLevi H' t h₁ m') (hu' : u' ∈ unip σ G.W H')
    {Ψ : Fn F (b + 2) (a + (b + 2))} (hΨ : Ψ ∈ schA F (Fin (b + 2) × Fin (a + (b + 2)))) :
    e' (om' (u * m, u' * m') Ψ) =
      (((X.ν l : ℂ) * (((absE F E l : ℝ) ^ (((a + (b + 2) : ℕ) : ℝ) / 2) : ℝ) : ℂ)) *
        ((X.α t : ℂ) * (((absE F E t : ℝ) ^ ((b : ℝ) / 2) : ℝ) : ℂ))) • om₁' (g₀, h₁) (e' Ψ) := by
  have pV' := (GlobalTheory.ThK.Check.isPair_of_isTriple hT).2
  have p1 := (GlobalTheory.ThK.Check.isPair_of_isTriple hT₁).2
  obtain ⟨Mm, hMm⟩ := GlobalTheory.T.exists_good_schrodinger_model F E σ B pV'.base b (a + (b + 2)) G₁.V' G.W _ _ _ _ p1.herm pV'.skew
  obtain ⟨omm, hom⟩ := GlobalTheory.T.hecke_characters_restriction_eta hK F E σ B pV'.base b (a + (b + 2)) G₁.V' G.W _ _ _ _ p1.herm pV'.skew Mm hMm
    X.α (X.α / X.β) pV'.hX pV'.hW p1.resX pV'.resW
  have pm : IsPair B Mm X.α (X.α / X.β) omm _ _ _ _ :=
    ⟨pV'.base, p1.herm, pV'.skew, hMm, pV'.hX, pV'.hW, p1.resX, pV'.resW, hom⟩
  obtain ⟨⟨e₁, he₁⟩, law₁⟩ := GlobalTheory.T.adapted_plane_first_variable hK F E σ B _ _ G.V' G.W G.M' X.α (X.α / X.β) om' _ _ _ _ pV' b G₁.V' H 0 (b + 1)
    Mm omm _ _ hC.hH pm
  obtain ⟨e₂, he₂⟩ := ((GlobalTheory.T.theta_evaluation_zero_cone hK).1 F E σ B _ _ G₁.V' G.W Mm X.α (X.α / X.β) omm _ _ _ _ pm (a + b) G₁.V' G₁.W H'
    a (a + b + 1) G₁.M' rfl hC.hH' hT₁.geo.hM').1
  have pres : ∀ (p : UA σ G.V'.J × UA σ G.W.J), ∀ Φ ∈ schA F (Fin (b + 2) × Fin (a + (b + 2))),
      om' p Φ ∈ schA F (Fin (b + 2) × Fin (a + (b + 2))) :=
    fun p Φ hΦ => (IsUWeilPair.isUSplitting hT.weil').pres p Φ hΦ
  have hlaw : ∀ Φ ∈ schA F (Fin (b + 2) × Fin (a + (b + 2))), e₂ (e₁ (om' (u * m, u' * m') Φ)) =
      (((X.ν l : ℂ) * (((absE F E l : ℝ) ^ (((a + (b + 2) : ℕ) : ℝ) / 2) : ℝ) : ℂ)) *
        ((X.α t : ℂ) * (((absE F E t : ℝ) ^ ((b : ℝ) / 2) : ℝ) : ℂ))) • om₁' (g₀, h₁) (e₂ (e₁ Φ)) := by
    intro Φ hΦ
    have k1 := law₁ e₁ he₁ (u' * m') l g₀ m hm u hu Φ hΦ
    have k2 := GlobalTheory.T.adapted_plane_second_variable hK F E σ B _ _ G₁.V' G.W Mm X.α (X.α / X.β) omm _ _ _ _ pm (a + b) G₁.W H' a (a + b + 1) G₁.M' om₁'
      _ _ hC.hH' p1 e₂ he₂ g₀ t h₁ m' hm' u' hu' (e₁ Φ) (he₁.maps Φ hΦ)
    rw [k1, map_smul, k2, smul_smul]
    rfl

  have one : incM F (1 : Matrix (Fin b) (Fin b) E) = 1 := GlobalTheory.ThK.Check.incM_one
  have one' : incM F (1 : Matrix (Fin (a + (b + 2))) (Fin (a + (b + 2))) E) = 1 := GlobalTheory.ThK.Check.incM_one
  have hmaps : ∀ Φ ∈ schA F (Fin (b + 2) × Fin (a + (b + 2))), (e₂ ∘ₗ e₁) Φ ∈ schA F (Fin b × Fin (a + b)) :=
    fun Φ hΦ => he₂.maps _ (he₁.maps Φ hΦ)
  have hheis : ∀ z, ∀ Φ ∈ schA F (Fin (b + 2) × Fin (a + (b + 2))),
      (e₂ ∘ₗ e₁) (G.M'.co.rho B.ψ (incM F H.ι * z * (incM F H'.ι)ᵀ) Φ) = G₁.M'.co.rho B.ψ z ((e₂ ∘ₗ e₁) Φ) := by
    intro z Φ hΦ
    have k1 := he₁.Heisenberg₂ (z * (incM F H'.ι)ᵀ) Φ hΦ
    rw [one', Matrix.transpose_one, Matrix.mul_one, ← Matrix.mul_assoc] at k1
    have k2 := he₂.Heisenberg₂ z (e₁ Φ) (he₁.maps Φ hΦ)
    rw [one, Matrix.one_mul] at k2
    simp only [LinearMap.comp_apply]
    rw [k1, k2]
  have hinv : ∀ u ∈ isoB H H', ∀ Φ ∈ schA F (Fin (b + 2) × Fin (a + (b + 2))),
      (e₂ ∘ₗ e₁) (G.M'.co.rho B.ψ u Φ) = (e₂ ∘ₗ e₁) Φ := by
    intro u hu Φ hΦ
    simp only [LinearMap.comp_apply]
    rcases hu with ⟨z, rfl⟩ | ⟨y, rfl⟩
    · rw [he₁.inv _ ⟨z, rfl⟩ Φ hΦ]
    · have k1 := he₁.Heisenberg₂ (Matrix.vecMulVec y (incV F H'.x)) Φ hΦ
      rw [one', Matrix.transpose_one, Matrix.mul_one, Matrix.mul_vecMulVec] at k1
      rw [k1, he₂.inv _ ⟨y, rfl⟩ _ (he₁.maps Φ hΦ)]
  have hloc : ∃ (ei : SInf F (Fin (b + 2) × Fin (a + (b + 2))) →L[ℂ] SInf F (Fin b × Fin (a + b)))
      (ev : ∀ v : Pl F, ((Fin (b + 2) × Fin (a + (b + 2)) → Fv F v) → ℂ) →ₗ[ℂ] (Fin b × Fin (a + b) → Fv F v) → ℂ),
      (∀ v, ev v (G.M'.vac v) = G₁.M'.vac v ∧ (SB _).map (ev v) = SB _) ∧
      ∀ f φ, (∀ v, φ v ∈ SB _) → (∀ᶠ v in cofinite, φ v = G.M'.vac v) →
        (e₂ ∘ₗ e₁) (pure f φ) = pure (ei f) fun v => ev v (φ v) := by
    obtain ⟨ei₁, ev₁, -, hv₁, hl₁⟩ := he₁.loc
    obtain ⟨ei₂, ev₂, -, hv₂, hl₂⟩ := he₂.loc
    refine ⟨ei₂.comp ei₁, fun v => (ev₂ v).comp (ev₁ v), fun v => ⟨?_, ?_⟩, fun f φ hφ hc => ?_⟩
    · simp [(hv₁ v).1, (hv₂ v).1]
    · rw [Submodule.map_comp, (hv₁ v).2, (hv₂ v).2]
    · have hφ' : ∀ v, ev₁ v (φ v) ∈ SB _ := fun v => by
        rw [← (hv₁ v).2]; exact Submodule.mem_map_of_mem (hφ v)
      have hc' : ∀ᶠ v in cofinite, ev₁ v (φ v) = Mm.vac v := by
        filter_upwards [hc] with v hv; rw [hv, (hv₁ v).1]
      simp only [LinearMap.comp_apply, ContinuousLinearMap.comp_apply]
      rw [hl₁ f φ hφ hc, hl₂ _ _ hφ' hc']

  obtain ⟨c, hc⟩ := GlobalTheory.T.config_b_triple_evaluation_compatible hK F E σ B a b G G₁ H H' hC X om om' om₁ om₁' hT hT₁ e' he' (e₂ ∘ₗ e₁) hmaps hheis hinv hloc
  obtain ⟨Φ₀, hΦ₀, hne⟩ := GlobalTheory.T.config_b_intermediate_model_evaluation hK F E σ B a b G G₁ H H' hC X om om' om₁ om₁' hT hT₁ Mm hMm e₁ he₁ e₂ he₂
  have hc0 : c ≠ 0 := by
    rintro rfl
    apply hne
    have := hc Φ₀ hΦ₀
    simpa using this
  have he'E : ∀ Φ ∈ schA F (Fin (b + 2) × Fin (a + (b + 2))), e' Φ = c⁻¹ • e₂ (e₁ Φ) := by
    intro Φ hΦ
    have := hc Φ hΦ
    simp only [LinearMap.comp_apply] at this
    rw [this, smul_smul, inv_mul_cancel₀ hc0, one_smul]
  rw [he'E _ (pres _ Ψ hΨ), hlaw Ψ hΨ, he'E Ψ hΨ, map_smul, smul_comm]

theorem ev_shift_unip (hK : GlobalTheory.FunPr.Hypotheses₂) {B : Base F E} {a b : ℕ} {G : Geo σ a (b + 2)} {G₁ : Geo σ a b}
    {H : Plane E (b + 2) b} {H' : Plane E (a + (b + 2)) (a + b)} (hC : CfgB B G G₁ H H') {e'}
    (he' : IsEv B G.M' G₁.M' H.ι H'.ι (isoB H H') e') {X om om' om₁ om₁'} (hT : IsTriple B G X om om')
    (hT₁ : IsTriple B G₁ X om₁ om₁')
    {u : UA σ G.V'.J} (hu : u ∈ unip σ G.V' H)
    {Ψ : Fn F (b + 2) (a + (b + 2))} (hΨ : Ψ ∈ schA F (Fin (b + 2) × Fin (a + (b + 2)))) :
    e' (G.M'.co.rho B.ψ (shiftB σ H H' 1) (om' (u, 1) Ψ)) = e' (G.M'.co.rho B.ψ (shiftB σ H H' 1) Ψ) := by
  have hS := IsUWeilPair.isUSplitting hT.weil'
  have hact : actAB (cA σ) ((u, 1) : UA σ G.V'.J × UA σ G.W.J) (mat u⁻¹ * shiftB σ H H' 1) = shiftB σ H H' 1 := by
    have h2 : mat u * mat u⁻¹ = 1 := Units.mul_inv u.1
    show mat u * (mat u⁻¹ * shiftB σ H H' 1) * (1 : Matrix _ _ _)ᵀ = _
    rw [Matrix.transpose_one, Matrix.mul_one, ← Matrix.mul_assoc, h2, Matrix.one_mul]
  have hρ := GlobalTheory.HeisSchA.rho_mem_schA G.M' B.ψ hT.base.std (mat u⁻¹ * shiftB σ H H' 1) _ hΨ
  have h1 := hS.impl (u, 1) (mat u⁻¹ * shiftB σ H H' 1) _ hΨ
  rw [hact] at h1
  have h2 := ev_law hK hC he' hT hT₁ (GlobalTheory.ThK.Check.isLevi_one H) hu (GlobalTheory.ThK.Check.isLevi_one H') (one_mem _) hρ
  simp only [mul_one, map_one, Circle.coe_one, NNReal.coe_one, Real.one_rpow, Complex.ofReal_one, one_smul,
    Prod.mk_one_one, Module.End.one_apply] at h2
  rw [← h1, h2]
  exact GlobalTheory.UnipShiftEv.ev_rho_unip_shift F E σ B a b G G₁ H H' hC hT.base hT.geo e' he' u⁻¹ (inv_mem hu) Ψ hΨ

theorem thX_unip (hK : GlobalTheory.FunPr.Hypotheses₂) {B : Base F E} {a b : ℕ} {G : Geo σ a (b + 2)} {G₁ : Geo σ a b}
    {H : Plane E (b + 2) b} {H' : Plane E (a + (b + 2)) (a + b)} (hC : CfgB B G G₁ H H') {e'}
    (he' : IsEv B G.M' G₁.M' H.ι H'.ι (isoB H H') e') {X om om' om₁ om₁'} (hT : IsTriple B G X om om')
    (hT₁ : IsTriple B G₁ X om₁ om₁')
    {Φ : Fn F (b + 2) (a + (b + 2))} (hΦ : Φ ∈ schA F (Fin (b + 2) × Fin (a + (b + 2))))
    {u : UA σ G.V'.J} (hu : u ∈ unip σ G.V' H) (g : UA σ G.V'.J) (h : UA σ G.W.J) :
    thX B G.M' H H' e' om' Φ (u * g) h = thX B G.M' H H' e' om' Φ g h := by
  have hS := IsUWeilPair.isUSplitting hT.weil'
  have h1 : om' (u * g, h) Φ = om' (u, 1) (om' (g, h) Φ) := by
    rw [← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk, one_mul]
  unfold thX
  rw [h1, ev_shift_unip hK hC he' hT hT₁ hu (hS.pres _ _ hΦ)]

theorem thX_levi (hK : GlobalTheory.FunPr.Hypotheses₂) {B : Base F E} {a b : ℕ} {G : Geo σ a (b + 2)} {G₁ : Geo σ a b}
    {H : Plane E (b + 2) b} {H' : Plane E (a + (b + 2)) (a + b)} (hC : CfgB B G G₁ H H') {e'}
    (he' : IsEv B G.M' G₁.M' H.ι H'.ι (isoB H H') e') {X om om' om₁ om₁'} (hT : IsTriple B G X om om')
    (hT₁ : IsTriple B G₁ X om₁ om₁')
    {Φ : Fn F (b + 2) (a + (b + 2))} (hΦ : Φ ∈ schA F (Fin (b + 2) × Fin (a + (b + 2))))
    {l : (AE F E)ˣ} {g₀ : UA σ G₁.V'.J} {m : UA σ G.V'.J} (hm : IsLevi H l g₀ m) (g : UA σ G.V'.J) (h : UA σ G.W.J) :
    thX B G.M' H H' e' om' Φ (m * g) h =
      ((X.ν l : ℂ) * (((absE F E l : ℝ) ^ (((a + (b + 2) : ℕ) : ℝ) / 2) : ℝ) : ℂ)) *
        theta om₁' (e' (G.M'.co.rho B.ψ (shiftB σ H H' l) (om' (g, h) Φ))) g₀ 1 := by
  have hS := IsUWeilPair.isUSplitting hT.weil'
  have hΨ := hS.pres (g, h) _ hΦ
  have h1 : om' (m * g, h) Φ = om' (m, 1) (om' (g, h) Φ) := by
    rw [← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk, one_mul]
  have hact : actAB (cA σ) ((m, 1) : UA σ G.V'.J × UA σ G.W.J) (shiftB σ H H' l) = shiftB σ H H' 1 := by
    show mat m * shiftB σ H H' l * (1 : Matrix _ _ _)ᵀ = _
    rw [Matrix.transpose_one, Matrix.mul_one, shiftB, shiftB, Matrix.mul_smul, Matrix.mul_vecMulVec, hm.2.1,
      Matrix.smul_vecMulVec, smul_smul, ← map_mul, Units.mul_inv, Units.val_one]
  have hρ := GlobalTheory.HeisSchA.rho_mem_schA G.M' B.ψ hT.base.std (shiftB σ H H' l) _ hΨ
  have h2 := hS.impl (m, 1) (shiftB σ H H' l) _ hΨ
  rw [hact] at h2
  have h3 := ev_law hK hC he' hT hT₁ hm (one_mem _) (GlobalTheory.ThK.Check.isLevi_one H') (one_mem _) hρ
  simp only [mul_one, one_mul, map_one, Circle.coe_one, NNReal.coe_one, Real.one_rpow, Complex.ofReal_one] at h3
  unfold thX theta
  rw [h1, ← h2, h3, thetaSum_smul]

theorem cA_incl (a : E) : cA σ (inclR (F := F) (AF F) a) = inclR (F := F) (AF F) (σ a) := by
  simp [cA, inclR]

theorem thX_rat_right (hK : GlobalTheory.FunPr.Hypotheses₂) {B : Base F E} {a b : ℕ} {G : Geo σ a (b + 2)} {G₁ : Geo σ a b}
    {H : Plane E (b + 2) b} {H' : Plane E (a + (b + 2)) (a + b)} (hC : CfgB B G G₁ H H') {e'}
    (he' : IsEv B G.M' G₁.M' H.ι H'.ι (isoB H H') e') {X om om' om₁ om₁'} (hT : IsTriple B G X om om')
    (hT₁ : IsTriple B G₁ X om₁ om₁')
    {Φ : Fn F (b + 2) (a + (b + 2))} (hΦ : Φ ∈ schA F (Fin (b + 2) × Fin (a + (b + 2))))
    {p : UA σ G.W.J} (hp : p ∈ ratU σ G.W.J) (ξ η : Eˣ) (hη : σ η * ξ = 1)
    (hξ : mat p *ᵥ incV F H'.x = (inclR (F := F) (AF F) (ξ : E)) • incV F H'.x) {m : UA σ G.V'.J}
    (hm : IsLevi (W₁ := G₁.V') H (Units.map (inclR (F := F) (AF F)).toMonoidHom η) 1 m) (g : UA σ G.V'.J) (h : UA σ G.W.J) :
    thX B G.M' H H' e' om' Φ g (p * h) = thX B G.M' H H' e' om' Φ (m * g) h := by
  have hS := IsUWeilPair.isUSplitting hT.weil'
  have hΨ := hS.pres (g, h) _ hΦ
  have pV' := (GlobalTheory.ThK.Check.isPair_of_isTriple hT).2
  have p1 := (GlobalTheory.ThK.Check.isPair_of_isTriple hT₁).2
  obtain ⟨u, hu, h₁, hh₁, m', hm', rfl⟩ := GlobalTheory.T.rational_line_stabilizer_decomposition F E σ B G.W G₁.W H' _ _ _ _ hT.base.cm hT.geo.hW hC.hH' p hp
    (Units.map (inclR (F := F) (AF F)).toMonoidHom ξ) hξ
  rw [thX_levi hK hC he' hT hT₁ hΦ hm]
  set l := Units.map (inclR (F := F) (AF F)).toMonoidHom η with hl
  have h1 : om' (g, u * m' * h) Φ = om' (1, u * m') (om' (g, h) Φ) := by
    rw [← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk, one_mul]
  have hact : actAB (cA σ) ((1, u * m') : UA σ G.V'.J × UA σ G.W.J) (shiftB σ H H' l) = shiftB σ H H' 1 := by
    show (1 : Matrix _ _ _) * shiftB σ H H' l * (mat (u * m'))ᵀ = _
    rw [Matrix.one_mul, shiftB, shiftB, Matrix.smul_mul, vecMulVec_mul_transpose, hξ, Matrix.vecMulVec_smul, smul_smul]
    congr 1
    show cA σ (inclR (F := F) (AF F) (η : E)) * _ = _
    rw [cA_incl, ← map_mul, hη, map_one, Units.val_one, map_one]
  have hρ := GlobalTheory.HeisSchA.rho_mem_schA G.M' B.ψ hT.base.std (shiftB σ H H' l) _ hΨ
  have h2 := hS.impl (1, u * m') (shiftB σ H H' l) _ hΨ
  rw [hact] at h2
  have h3 := ev_law hK hC he' hT hT₁ (GlobalTheory.ThK.Check.isLevi_one H) (one_mem _) hm' hu hρ
  have hα := pV'.hX.2 ξ
  have hν : X.ν l = 1 := pV'.hW.2 η
  have ha1 : absE F E l = 1 := GlobalTheory.Doubling.absE_inclR η
  have ha2 := GlobalTheory.Doubling.absE_inclR (F := F) ξ
  have hinv := ((GlobalTheory.T.theta_basic_properties hK F E σ B _ _ _ _ G₁.M' _ _ om₁' _ _ _ _ p1).1 _ (he'.maps _ hρ)).2.1 1 (one_mem _) h₁ hh₁ 1 1
  simp only [mul_one] at hinv
  rw [hα, ha2] at h3
  simp only [mul_one, one_mul, map_one, Circle.coe_one, NNReal.coe_one, Real.one_rpow, Complex.ofReal_one, one_smul] at h3
  rw [hν, ha1, ← hinv]
  unfold thX theta
  rw [h1, ← h2, h3]
  simp

theorem continuous_thX {B : Base F E} {a b : ℕ} {G : Geo σ a (b + 2)} {G₁ : Geo σ a b}
    {H : Plane E (b + 2) b} {H' : Plane E (a + (b + 2)) (a + b)} (hC : CfgB B G G₁ H H') {e'}
    (he' : IsEv B G.M' G₁.M' H.ι H'.ι (isoB H H') e') {X om om' om₁ om₁'} (hT : IsTriple B G X om om')
    (hT₁ : IsTriple B G₁ X om₁ om₁')
    {Φ : Fn F (b + 2) (a + (b + 2))} (hΦ : Φ ∈ schA F (Fin (b + 2) × Fin (a + (b + 2)))) (h : UA σ G.W.J) :
    Continuous fun g => thX B G.M' H H' e' om' Φ g h := by
  have hψ := hT.base.std
  have hS := IsUWeilPair.isUSplitting hT.weil'
  obtain ⟨l₀, hl₀, hl₀eq⟩ := GlobalTheory.ThetaAdmitted.exists_admitted_form_eq_adelicThetaDistribution_alt F (Fin b × Fin (a + b))
  have hl := GlobalTheory.ConeMeasV.comp_schr_mem_adm hψ (G.M'.co.e (shiftB σ H H' 1))
    (GlobalTheory.ConeMeasV.comp_ev_mem_adm hT.geo.hM' hT₁.geo.hM' he' hl₀)
  have hc := hS.cont _ hl Φ hΦ
  have heq : (fun g => thX B G.M' H H' e' om' Φ g h) =
      fun g => ((l₀ ∘ₗ e') ∘ₗ GlobalTheory.ConeMeasV.schrLin B.ψ (G.M'.co.e (shiftB σ H H' 1))) (om' (g, h) Φ) := by
    funext g
    have h2 := GlobalTheory.ConeMeasV.schr_mem_schA hψ (G.M'.co.e (shiftB σ H H' 1)) (hS.pres (g, h) Φ hΦ)
    exact (hl₀eq _ (he'.maps _ h2)).symm
  rw [heq]
  exact hc.comp (continuous_id.prodMk continuous_const)

end GlobalTheory.ConeRearr

end
