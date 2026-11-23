import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EisAtMinusRho
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocUnifSum
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemCtIntSub
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DisjointLineMid
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NeOfReNe
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsShear
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilRepresentationPreservesSchwartz
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousLeftInvariantDual
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConfigBLeviEvaluationCompatibleStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConfigBEigenStabilizerIntegralStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ReducedTripleIsotropicPlaneStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConfigBStabilizerIdelesHaarThirdStatement
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)
open GlobalTheory.ConeSmallMidJB

noncomputable section

namespace GlobalTheory.ConeSmallMidJBInner

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem isLevi_mul {d d₁ : ℕ} {W : Spc F E d} {W₁ : Spc F E d₁} {H' : Plane E d d₁} {v v' : UA σ W₁.J} {m m' : UA σ W.J}
    (h : IsLevi H' 1 v m) (h' : IsLevi H' 1 v' m') : IsLevi H' 1 (v * v') (m * m') := by
  obtain ⟨h1, h2, h3⟩ := h
  obtain ⟨h1', h2', h3'⟩ := h'
  have hmul : ∀ x y : UA σ W.J, mat (x * y) = mat x * mat y := fun _ _ => rfl
  have hmul₁ : ∀ x y : UA σ W₁.J, mat (x * y) = mat x * mat y := fun _ _ => rfl
  simp only [inv_one, Units.val_one, map_one, one_smul] at h1 h2 h1' h2' ⊢
  refine ⟨?_, ?_, ?_⟩
  · rw [hmul, ← Matrix.mulVec_mulVec, h1', h1]; simp
  · rw [hmul, ← Matrix.mulVec_mulVec, h2', h2]; simp
  · rw [hmul, hmul₁, Matrix.mul_assoc, h3', ← Matrix.mul_assoc, h3, Matrix.mul_assoc]

theorem coneI_levi_pt (hKP : GlobalTheory.ThK.KP) {B : Base F E} {a b : ℕ} {G : Geo σ a (b + 2)} {G₁ : Geo σ a b}
    {H : Plane E (b + 2) b} {H' : Plane E (a + (b + 2)) (a + b)} (hC : CfgB B G G₁ H H') {e'}
    (he : IsEv B G.M' G₁.M' H.ι H'.ι (isoB H H') e') (K : Subgroup (UA σ G.V'.J)) (μK : Measure K) (μ : Measure (AE F E)ˣ)
    {X om om' om₁ om₁'} (hT : IsTriple B G X om om') (hT₁ : IsTriple B G₁ X om₁ om₁') {Φ'}
    (hΦ' : Φ' ∈ PolData B G.M' ⊓ G.M'.So B.ψ B.τ₁) (z : ℂ) (h₁ : UA σ G₁.W.J) (m : UA σ G.W.J) (hL : IsLevi H' 1 h₁ m)
    (h : UA σ G.W.J) :
    GlobalTheory.ConeSmall.coneI B G G₁ H H' e' K μK μ X.ν om' om₁' Φ' z (m * h) =
      ∫ k, ∫ l, G₁.M'.I om₁' (e' (G.M'.co.rho B.ψ (shiftB σ H H' l) (om' (k.1, h) Φ'))) h₁ * (X.ν l : ℂ) * ((absE F E l : ℝ) : ℂ) ^ z ∂μ ∂μK := by
  have hΦs : Φ' ∈ schA F _ := GlobalTheory.ThKContSmall.so_le_schA hT.geo.hM' B.τ₁ (Submodule.mem_inf.1 hΦ').2
  have hW := IsUWeilPair.isUSplitting hT.weil'
  unfold GlobalTheory.ConeSmall.coneI
  refine integral_congr_ae (Filter.Eventually.of_forall fun k => ?_)
  refine integral_congr_ae (Filter.Eventually.of_forall fun l => ?_)
  simp only
  congr 2
  have hΨ : om' (k.1, h) Φ' ∈ schA F _ := hW.pres _ _ hΦs
  have e1 : om' (k.1, m * h) Φ' = om' (1, m) (om' (k.1, h) Φ') := by
    rw [← Module.End.mul_apply, ← map_mul]; simp
  have hact : actAB (cA σ) ((1, m) : UA σ G.V'.J × UA σ G.W.J) (shiftB σ H H' l) = shiftB σ H H' l := by
    have hx : mat m *ᵥ incV F H'.x = incV F H'.x := by simpa using hL.1
    ext i j
    simp only [actAB, shiftB, OneMemClass.coe_one, Units.val_one, Matrix.one_mul, Matrix.smul_mul, Matrix.smul_apply]
    congr 1
    conv_rhs => rw [← hx]
    simp [mat, Matrix.mul_apply, Matrix.vecMulVec_apply, Matrix.mulVec, dotProduct, Finset.mul_sum, mul_comm, mul_left_comm]
    exact Finset.sum_congr rfl fun _ _ => by ring
  have e2 : G.M'.co.rho B.ψ (shiftB σ H H' l) (om' (1, m) (om' (k.1, h) Φ')) =
      om' (1, m) (G.M'.co.rho B.ψ (shiftB σ H H' l) (om' (k.1, h) Φ')) := by
    rw [hW.impl (1, m) (shiftB σ H H' l) _ hΨ, hact]
  have hρ := GlobalTheory.HeisSchA.rho_mem_schA G.M' B.ψ hT.base.std (shiftB σ H H' l) _ hΨ
  rw [e1, e2, GlobalTheory.T.config_b_levi_evaluation_compatible hKP.base F E σ B a b G G₁ H H' hC e' he X om om' om₁ om₁' hT hT₁ h₁ m hL _ hρ]
  simp only [Model.I, theta]
  refine integral_congr_ae (Filter.Eventually.of_forall fun g => ?_)
  simp only
  rw [← Module.End.mul_apply, ← map_mul]
  simp

theorem jb_inner : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (a b : ℕ) (G : Geo σ a (b + 2)) (G₁ : Geo σ a b) (H : Plane E (b + 2) b) (H' : Plane E (a + (b + 2)) (a + b)), CfgB B G G₁ H H' →
    ∀ e', IsEv B G.M' G₁.M' H.ι H'.ι (isoB H H') e' → ∀ (K : Subgroup (UA σ G.V'.J)) (μK : Measure K) (μ : Measure (AE F E)ˣ),
    IsStab B K → μK.IsHaarMeasure → μ.IsHaarMeasure →
    ∀ X om om' om₁ om₁', IsTriple B G X om om' → IsTriple B G₁ X om₁ om₁' →
    ∀ Φ' ∈ PolData B G.M' ⊓ G.M'.So B.ψ B.τ₁, ∀ (V : Spc F E a) (V' : Spc F E b) (W₁' : Spc F E (a + b)), IsTriple B (reG G₁ V V' W₁') X om₁ om₁' →
    ∀ (e : ℕ) (W₂ : Spc F E e) (H₂ : Plane E (a + b) e) (i₀ i₁ : ℕ), H₂.IsAdapted σ B (reG G₁ V V' W₁').W W₂ i₀ i₁ → ∀ emb : UA σ G₁.W.J → UA σ G.W.J, (∀ h₁, IsLevi H' 1 h₁ (emb h₁)) →
    ∃ s₁ : ℝ, ∀ s : ℂ, s₁ < s.re → ∃ Gf : UA σ G.W.J → ℂ,
      (∀ g, IsCT H₂ (fun h₁ => (GlobalTheory.ConeSmall.coneI B G G₁ H H' e' K μK μ X.ν om' om₁' Φ' (s + ((a : ℂ) + 1) / 2)) (emb h₁ * g)) (fun h₁ => Gf (emb h₁ * g))) ∧
      (∀ (t t' : (AE F E)ˣ) (m m' : UA σ G₁.W.J), IsLevi (W₁ := W₂) H₂ t 1 m → IsLevi (W₁ := W₂) H₂ t' 1 m' → ∀ g,
        Gf (emb m' * (emb m * g)) - (X.β t' : ℂ) * ((absE F E t' : ℝ) : ℂ) ^ (((a : ℕ) : ℂ) / 2) * Gf (emb m * g) -
        (X.α t : ℂ) * ((absE F E t : ℝ) : ℂ) ^ (((b : ℕ) : ℂ) / 2) * Gf (emb m' * g) +
        (X.α t : ℂ) * ((absE F E t : ℝ) : ℂ) ^ (((b : ℕ) : ℂ) / 2) * ((X.β t' : ℂ) * ((absE F E t' : ℝ) : ℂ) ^ (((a : ℕ) : ℂ) / 2)) * Gf g = 0) ∧
      (∀ (t t' : (AE F E)ˣ) (m m' : UA σ G₁.W.J), IsLevi (W₁ := W₂) H₂ t 1 m → IsLevi (W₁ := W₂) H₂ t' 1 m' → ∀ g,
        Gf (emb m' * (emb m * g)) - (X.α t' : ℂ) * ((absE F E t' : ℝ) : ℂ) ^ (((b : ℕ) : ℂ) / 2) * Gf (emb m * g) -
        (X.β t : ℂ) * ((absE F E t : ℝ) : ℂ) ^ (((a : ℕ) : ℂ) / 2) * Gf (emb m' * g) +
        (X.β t : ℂ) * ((absE F E t : ℝ) : ℂ) ^ (((a : ℕ) : ℂ) / 2) * ((X.α t' : ℂ) * ((absE F E t' : ℝ) : ℂ) ^ (((b : ℕ) : ℂ) / 2)) * Gf g = 0) := by
  intro hKP F E _ _ _ _ _ σ B a b G G₁ H H' hC e' he K μK μ hK hμK hμ X om om' om₁ om₁' hT hT₁ Φ' hΦ' V V' W₁' hT₂ e W₂ H₂
    i₀ i₁ hH₂ emb hemb
  obtain ⟨s₁, hs₁⟩ := GlobalTheory.T.config_b_stabilizer_ideles_haar_third hKP F E σ B a b G G₁ H H' hC e' he K μK μ hK hμK hμ X om om' om₁ om₁' hT hT₁ Φ' hΦ' V V' W₁' hT₂
    e W₂ H₂ i₀ i₁ hH₂
  refine ⟨s₁, fun s hs => ?_⟩
  have hJ : ∀ (g : UA σ G.W.J) (k : K) (l : (AE F E)ˣ), ∃ c : UA σ G₁.W.J → ℂ, IsCT H₂ (G₁.M'.I om₁' (e' (G.M'.co.rho B.ψ (shiftB σ H H' l) (om' (k.1, g) Φ')))) c ∧
      GlobalTheory.ConeSmallMid.JRel W₂ H₂ X.α (((b : ℕ) : ℂ) / 2) X.β (((a : ℕ) : ℂ) / 2) c ∧
      GlobalTheory.ConeSmallMid.JRel W₂ H₂ X.β (((a : ℕ) : ℂ) / 2) X.α (((b : ℕ) : ℂ) / 2) c := fun g k l =>
    GlobalTheory.T.reduced_triple_isotropic_plane hKP F E σ B a b G₁ X om₁ om₁' hT₁ V V' W₁' hT₂ e W₂ H₂ i₀ i₁ hH₂ _
      (GlobalTheory.T.config_b_eigen_stabilizer_integral hKP F E σ B a b G G₁ H H' hC e' he K μK μ hK hμK hμ X om om' om₁ om₁' hT hT₁ Φ' hΦ' g k l)
  choose C hCT hJ1 hJ2 using fun g => hs₁ s hs g (hJ g)
  have hLv : ∀ (v : UA σ G₁.W.J) (m x : UA σ G.W.J), IsLevi H' 1 v m →
      GlobalTheory.ConeSmall.coneI B G G₁ H H' e' K μK μ X.ν om' om₁' Φ' (s + ((a : ℂ) + 1) / 2) (m * x) =
        ∫ k, ∫ l, G₁.M'.I om₁' (e' (G.M'.co.rho B.ψ (shiftB σ H H' l) (om' (k.1, x) Φ'))) v * (X.ν l : ℂ) * ((absE F E l : ℝ) : ℂ) ^ (s + ((a : ℂ) + 1) / 2) ∂μ ∂μK :=
    fun v m x hL => coneI_levi_pt hKP hC he K μK μ hT hT₁ hΦ' _ v m hL x
  by_cases hex : ∃ (μ₀ : Measure (unip σ G₁.W H₂)) (𝓕₀ : Set (unip σ G₁.W H₂)), μ₀.IsHaarMeasure ∧
      IsFundamentalDomain ((ratU σ G₁.W.J).subgroupOf (unip σ G₁.W H₂)) 𝓕₀ μ₀ ∧ μ₀ 𝓕₀ = 1
  swap
  · refine ⟨0, fun g μ' 𝓕 h1 h2 h3 => absurd ⟨μ', 𝓕, h1, h2, h3⟩ hex, ?_, ?_⟩ <;> intros <;> simp
  obtain ⟨μ₀, 𝓕₀, hμ₀, h𝓕₀, h1₀⟩ := hex
  have key : ∀ g v m, IsLevi H' 1 v m → C (m * g) 1 = C g v := by
    intro g v m hL
    rw [hCT (m * g) μ₀ 𝓕₀ hμ₀ h𝓕₀ h1₀ 1, hCT g μ₀ 𝓕₀ hμ₀ h𝓕₀ h1₀ v]
    refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
    have A := hLv (u.1 * 1) (emb (u.1 * 1)) (m * g) (hemb _)
    have hv : u.1 * 1 * v = u.1 * v := by rw [mul_one]
    have B' := hLv (u.1 * v) (emb (u.1 * 1) * m) g (by rw [← hv]; exact isLevi_mul (hemb _) hL)
    rw [mul_assoc] at B'
    exact A.symm.trans B'
  refine ⟨fun x => C x 1, fun g μ' 𝓕 h1 h2 h3 h => ?_, fun t t' m m' hm hm' g => ?_, fun t t' m m' hm hm' g => ?_⟩
  · show C (emb h * g) 1 = _
    rw [key g h (emb h) (hemb h), hCT g μ' 𝓕 h1 h2 h3 h]
    refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
    exact (hLv _ _ g (hemb (u.1 * h))).symm
  · have e1 := key g (m' * m) (emb m' * emb m) (isLevi_mul (hemb m') (hemb m))
    have e2 := key g m (emb m) (hemb m)
    have e3 := key g m' (emb m') (hemb m')
    have hj := hJ1 g t t' m m' hm hm' 1
    simp only [mul_one] at hj
    show C (emb m' * (emb m * g)) 1 - _ * C (emb m * g) 1 - _ * C (emb m' * g) 1 + _ * C g 1 = 0
    rw [← mul_assoc, e1, e2, e3]
    exact hj
  · have e1 := key g (m' * m) (emb m' * emb m) (isLevi_mul (hemb m') (hemb m))
    have e2 := key g m (emb m) (hemb m)
    have e3 := key g m' (emb m') (hemb m')
    have hj := hJ2 g t t' m m' hm hm' 1
    simp only [mul_one] at hj
    show C (emb m' * (emb m * g)) 1 - _ * C (emb m * g) 1 - _ * C (emb m' * g) 1 + _ * C g 1 = 0
    rw [← mul_assoc, e1, e2, e3]
    exact hj

end GlobalTheory.ConeSmallMidJBInner

end
