import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EigenIntertwinerGoodModels
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SkewAdaptedPlanePairConverse
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicStoneVonNeumannLagrangianUniquenessStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CharacterMultiplicativeStabilizerStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSkewComplement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SymplecticIsotropicPlaneVanishesAdelicStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SymplecticIsotropicEmbeddedVanishesAdelicStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SymplecticFormRestrictedPlaneStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LagrangianDimensionBoundStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RationalModelCoordinatesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RationalLagrangianSubspaceExistsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SkewDeterminantNeZeroFirstSpaceStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuadraticInjectivePlaneCoordinates
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HyperbolicPlaneDecompositionOfPair
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PairAdaptedPlaneThetaIntegralStatement

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

noncomputable section

namespace GlobalTheory.NwAvgComp

open GlobalTheory.MixedLagr (IsMixed lagr hat)

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem first_coordinate_admissible {B : Base F E} {n d n₁ d₁ : ℕ} {X : Spc F E n} {W : Spc F E d} {X₁ : Spc F E n₁} {W₁ : Spc F E d₁}
    {M : Model σ X W} {M₁ : Model σ X₁ W₁} {ι : Matrix (Fin n) (Fin n₁) E} {ι' : Matrix (Fin d) (Fin d₁) E}
    {I : Set (Matrix (Fin n) (Fin d) (AE F E))} {e : Fn F n d →ₗ[ℂ] Fn F n₁ d₁} (hM : M.IsGood B.ψ)
    (hE : IsEv B M M₁ ι ι' I e) :
    (LinearMap.proj 0 : Fn F n₁ d₁ →ₗ[ℂ] ℂ) ∘ₗ e ∈ (adeleClass F).adm (Fin n × Fin d) := by
  classical
  intro g hg
  obtain ⟨ei, ev, -, hev, hloc⟩ := hE.loc
  obtain ⟨m, c, φ, hφSB, hφstd, hgeq⟩ := GlobalTheory.EvAdm.exists_sum_finprod hg
  have hφvac : ∀ k, ∀ᶠ v in cofinite, φ k v = M.vac v := fun k =>
    ((hφstd k).and hM.std).mono fun v h => h.1.trans h.2.symm
  let δ : SInf F (Fin n₁ × Fin d₁) →L[ℂ] ℂ :=
    (BoundedContinuousFunction.evalCLM ℂ (fun i => evI F ((0 : Fin n₁ × Fin d₁ → AF F) i))).comp
      (SchwartzMap.toBoundedContinuousFunctionCLM ℂ (Fin n₁ × Fin d₁ → mixedEmbedding.mixedSpace F) ℂ)
  let a : Fin m → ℂ := fun k => ∏ᶠ v, ev v (φ k v) fun i => evFin F v ((0 : Fin n₁ × Fin d₁ → AF F) i)
  refine ⟨∑ k, (c k * a k) • δ.comp ei, fun f => ?_⟩
  have h1 : pureA F (f : (Fin n × Fin d → mixedEmbedding.mixedSpace F) → ℂ) g = ∑ k, c k • GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f (φ k) := by
    rw [hgeq]
    funext x
    simp only [pureA, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp only [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure]
    rw [mul_left_comm]
    rfl
  have h2 : ∀ k, (LinearMap.proj 0 : Fn F n₁ d₁ →ₗ[ℂ] ℂ) (e (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f (φ k))) = a k * δ (ei f) := fun k => by
    rw [hloc f (φ k) (hφSB k) (hφvac k), mul_comm]
    rfl
  simp only [LinearMap.comp_apply, h1, map_sum, map_smul, h2, FunLike.coe_sum, Finset.sum_apply,
    FunLike.coe_smul, Pi.smul_apply, ContinuousLinearMap.coe_comp, Function.comp_apply, smul_eq_mul, mul_assoc]

variable {n d d₁ d₂ : ℕ} {X : Spc F E n} {W : Spc F E d} {W₁ : Spc F E d₁} {V₁ : Spc F E d₂}

theorem rho_add (ψ : AddChar (AF F) ℂ) (M : Model σ X W) (w w' : Matrix (Fin n) (Fin d) (AE F E))
    (h : (M.co.e w).1 ⬝ᵥ (M.co.e w').2 - (M.co.e w').1 ⬝ᵥ (M.co.e w).2 = 0) (φ : Fn F n d) :
    M.co.rho ψ (w + w') φ = M.co.rho ψ w (M.co.rho ψ w' φ) := by
  change schr ψ (M.co.e _) φ = schr ψ (M.co.e _) (schr ψ (M.co.e _) φ)
  rw [GlobalTheory.MixedLagr.schr_comp, h, mul_zero, AddChar.map_zero_eq_one, one_smul, ← map_add]

theorem symp_isMixed {B : Base F E} {H' : Plane E d d₁} {i₀ i₁ : ℕ} (hH : H'.IsAdapted σ B W W₁ i₀ i₁)
    (M₁ : Model σ V₁ W) (M₂ : Model σ V₁ W₁) {z z' : Matrix (Fin d₂) (Fin d) (AE F E)} (h : IsMixed M₂ H' z)
    (h' : IsMixed M₂ H' z') : (M₁.co.e z).1 ⬝ᵥ (M₁.co.e z').2 - (M₁.co.e z').1 ⬝ᵥ (M₁.co.e z).2 = 0 := by
  have hD : ∀ p q, symp (cA σ) (-1) (incM F V₁.J) (incM F W.J) p q =
      (M₁.co.e p).1 ⬝ᵥ (M₁.co.e q).2 - (M₁.co.e q).1 ⬝ᵥ (M₁.co.e p).2 := M₁.co.form
  have hcross := GlobalTheory.T.symplectic_isotropic_embedded_vanishes_adelic F E σ d₂ d d₁ V₁.J W.J H' (fun u => (hH.orth u).1)
  obtain ⟨u, hu, y, hy, rfl⟩ := h
  obtain ⟨u', hu', y', hy', rfl⟩ := h'
  have h1 := GlobalTheory.T.symplectic_isotropic_plane_vanishes_adelic F E σ d₂ d d₁ V₁.J W.J H' hH.xx u hu u' hu'
  have h2 := hcross u' hu' y
  have h3 := hcross u hu y'
  have h4 := GlobalTheory.T.symplectic_form_restricted_plane F E σ d₂ d d₁ V₁.J W.J W₁.J H'.ι hH.gram y y'
  rw [M₂.co.form, hy, hy', zero_dotProduct, zero_dotProduct, sub_zero] at h4
  rw [hD] at h1 h2 h3 h4
  simp only [map_add, Prod.fst_add, Prod.snd_add, add_dotProduct, dotProduct_add]
  linear_combination h1 + h2 - h3 + h4

def Q (M₂ : Model σ V₁ W₁) (H : Plane E n d₂) (H' : Plane E d d₁) (m : Matrix (Fin n) (Fin d) (AE F E)) : Prop :=
  ∃ (a : Fin d → AE F E) (z : Matrix (Fin d₂) (Fin d) (AE F E)), IsMixed M₂ H' z ∧
    m = Matrix.vecMulVec (incV F H.x) a + incM F H.ι * z * (incM F (1 : Matrix (Fin d) (Fin d) E))ᵀ

theorem Q.smul {M₂ : Model σ V₁ W₁} {H : Plane E n d₂} {H' : Plane E d d₁} {m : Matrix (Fin n) (Fin d) (AE F E)}
    (h : Q M₂ H H' m) (t : AF F) : Q M₂ H H' (t • m) := by
  obtain ⟨y, z, hz, rfl⟩ := h
  refine ⟨t • y, t • z, hz.smul t, ?_⟩
  rw [smul_add, Matrix.vecMulVec_smul, Matrix.mul_smul, Matrix.smul_mul]

open GlobalTheory.MixedLagrX in
theorem symp_Q {B : Base F E} {H' : Plane E d d₁} {i₀ i₁ : ℕ} (hH : H'.IsAdapted σ B W W₁ i₀ i₁) {H : Plane E n d₂}
    (hxx : form σ X.J H.x H.x = 0) (horth : ∀ u, form σ X.J (H.ι *ᵥ u) H.x = 0 ∧ form σ X.J (H.ι *ᵥ u) H.y = 0)
    (hgram : V₁.J = H.ιᵀ * X.J * H.ι.map σ) (M : Model σ X W) (M₁ : Model σ V₁ W) (M₂ : Model σ V₁ W₁)
    {m m' : Matrix (Fin n) (Fin d) (AE F E)} (h : Q M₂ H H' m) (h' : Q M₂ H H' m') :
    (M.co.e m).1 ⬝ᵥ (M.co.e m').2 - (M.co.e m').1 ⬝ᵥ (M.co.e m).2 = 0 := by
  obtain ⟨y, z, hz, rfl⟩ := h
  obtain ⟨y', z', hz', rfl⟩ := h'
  have hQ : ∀ a b, (M.co.e a).1 ⬝ᵥ (M.co.e b).2 - (M.co.e b).1 ⬝ᵥ (M.co.e a).2 =
      symp (cA σ) (-1) (incM F X.J) (incM F W.J) a b := fun a b => (M.co.form a b).symm
  have h1 := symp_eq_zero (JB := W.J) _ _ _ (GlobalTheory.MixedLagrXPlain.piece_xx hxx y y')
  have h2 := symp_eq_zero (JB := W.J) _ _ _ (GlobalTheory.MixedLagrXPlain.piece_ix horth z y')
  have h3 := symp_eq_zero (JB := W.J) _ _ _ (GlobalTheory.MixedLagrXPlain.piece_ix horth z' y)
  have h4 : symp (cA σ) (-1) (incM F X.J) (incM F W.J) (incM F H.ι * z * (incM F (1 : Matrix (Fin d) (Fin d) E))ᵀ)
      (incM F H.ι * z' * (incM F (1 : Matrix (Fin d) (Fin d) E))ᵀ) = 0 := by
    have : symp (cA σ) (-1) (incM F X.J) (incM F W.J) (incM F H.ι * z * (incM F (1 : Matrix (Fin d) (Fin d) E))ᵀ)
        (incM F H.ι * z' * (incM F (1 : Matrix (Fin d) (Fin d) E))ᵀ) =
        symp (cA σ) (-1) (incM F V₁.J) (incM F W.J) z z' := by
      simp only [symp, hTens_eq, GlobalTheory.MixedLagrXPlain.piece_ii hgram]
    rw [this, M₁.co.form, symp_isMixed hH M₁ M₂ hz hz']
  rw [← hQ] at h1 h2 h3 h4
  simp only [map_add, Prod.fst_add, Prod.snd_add, add_dotProduct, dotProduct_add]
  linear_combination h1 + h2 - h3 + h4

open GlobalTheory.MixedLagrX in

theorem exists_lagr {B : Base F E} (hB : B.IsGood σ) {H' : Plane E d d₁} {i₀ i₁ : ℕ} (hH : H'.IsAdapted σ B W W₁ i₀ i₁)
    (hdet : W₁.J.det ≠ 0) {H : Plane E n d₂} (hrank : d₂ + 2 = n)
    (hxx : form σ X.J H.x H.x = 0) (hxy : form σ X.J H.x H.y = 1)
    (horth : ∀ u, form σ X.J (H.ι *ᵥ u) H.x = 0 ∧ form σ X.J (H.ι *ᵥ u) H.y = 0) (hinj : Function.Injective H.ι.mulVec)
    (hgram : V₁.J = H.ιᵀ * X.J * H.ι.map σ) (M : Model σ X W) (M₁ : Model σ V₁ W) (M₂ : Model σ V₁ W₁)
    (hM : M.IsGood B.ψ) (hM₁ : M₁.IsGood B.ψ)
    (hrat : ∀ x : Matrix (Fin d₂) (Fin d₁) E, ∃ y z : Fin d₂ × Fin d₁ → F,
        M₂.co.e (incM F x) = (fun i => algebraMap F (AF F) (y i), fun i => algebraMap F (AF F) (z i))) :
    ∃ L : Submodule F ((Fin n × Fin d → F) × (Fin n × Fin d → F)), (∀ a ∈ L, ∀ b ∈ L, a.1 ⬝ᵥ b.2 = b.1 ⬝ᵥ a.2) ∧
      Module.finrank F L = Fintype.card (Fin n × Fin d) ∧ ∀ w ∈ L, ∃ m, Q M₂ H H' m ∧ hat w = M.co.e m := by
  have h2 : Module.finrank F E = 2 := hB.cm.2.2.1
  haveI : Module.Finite F E := Module.finite_of_finrank_pos (by omega)
  obtain ⟨Φ, hΦ⟩ := GlobalTheory.T.quadratic_model_rational_coordinates F E σ n d X W M B.ψ hM h2
  obtain ⟨Φ₁, hΦ₁⟩ := GlobalTheory.T.quadratic_model_rational_coordinates F E σ d₂ d V₁ W M₁ B.ψ hM₁ h2
  obtain ⟨f₂, hf₂, hfe₂⟩ := GlobalTheory.T.rational_model_coordinates F E σ d₂ d₁ V₁ W₁ M₂ hrat
  obtain ⟨K, hK, hKz⟩ := GlobalTheory.T.rational_lagrangian_subspace_exists F E σ d₂ d₁ V₁ W₁ M₂ h2 f₂ hf₂ hfe₂
  have hle := GlobalTheory.MixedLagr.le_finrank_lagr F E σ d₂ d d₁ V₁ W W₁ M₁ M₂ H' h2 hH.rank hH.xy (fun u => (hH.orth u).2)
    (GlobalTheory.MixedLagr.mul_transpose_injective F E σ d₂ d d₁ W.J W₁.J H'.ι hH.gram hdet) Φ₁.toLinearMap Φ₁.injective
    (fun x => (hΦ₁ x).symm) K hK hKz
  let G₀ : (Fin d → E) × Matrix (Fin d₂) (Fin d) E →ₗ[F] Matrix (Fin n) (Fin d) E :=
    { toFun := fun p => Matrix.vecMulVec H.x p.1 + H.ι * p.2
      map_add' := fun p q => by
        simp only [Prod.fst_add, Prod.snd_add, Matrix.vecMulVec_add, Matrix.mul_add]; abel
      map_smul' := fun c p => by
        ext i j
        simp [Matrix.vecMulVec_apply, Matrix.mul_apply, Algebra.smul_def]
        rw [mul_add, Finset.mul_sum]
        ring }
  have hG₀ : Function.Injective G₀ := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    rintro ⟨y, z⟩ h
    change Matrix.vecMulVec H.x y + H.ι * z = 0 at h
    have hy : y = 0 := by
      funext j
      have hcol : (fun i => (Matrix.vecMulVec H.x y + H.ι * z) i j) = y j • H.x + H.ι *ᵥ (fun k => z k j) := by
        funext i; simp [Matrix.vecMulVec_apply, Matrix.mul_apply, Matrix.mulVec, dotProduct, mul_comm]
      have hj := congrArg (fun A : Fin n → E => form σ X.J A H.y) hcol
      simp only [h, Matrix.zero_apply] at hj
      rw [form_add_left, form_smul_left, hxy, (horth _).2, mul_one, add_zero] at hj
      rw [← hj]; simp [form]
    subst hy
    have hιz : H.ι * z = 0 := by
      ext i j
      have := congrFun (congrFun h i) j
      simpa [Matrix.vecMulVec_apply] using this
    have h5 : z = 0 := by
      ext k j
      have hc : H.ι *ᵥ (fun k => z k j) = H.ι *ᵥ 0 := by
        funext i
        have := congrFun (congrFun hιz i) j
        simpa [Matrix.mul_apply, Matrix.mulVec, dotProduct] using this
      have := congrFun (hinj hc) k
      simpa using this
    exact Prod.ext rfl h5
  let T : (Fin d → E) × lagr M₁ M₂ H' →ₗ[F] (Fin n × Fin d → F) × (Fin n × Fin d → F) :=
    Φ.toLinearMap ∘ₗ G₀ ∘ₗ (LinearMap.id.prodMap (Φ₁.symm.toLinearMap ∘ₗ (lagr M₁ M₂ H').subtype))
  have hT : Function.Injective T := by
    intro p q hpq
    have h := hG₀ (Φ.injective hpq)
    have ha := congrArg Prod.fst h
    have hb := congrArg Prod.snd h
    exact Prod.ext ha (Subtype.ext (Φ₁.symm.injective hb))
  have hQ : ∀ w ∈ LinearMap.range T, ∃ m, Q M₂ H H' m ∧ hat w = M.co.e m := by
    rintro _ ⟨p, rfl⟩
    refine ⟨incM F (Matrix.vecMulVec H.x p.1 + H.ι * Φ₁.symm p.2), ⟨incV F p.1, incM F (Φ₁.symm p.2), ?_, ?_⟩, (hΦ _).symm⟩
    · have h : IsMixed M₂ H' (M₁.co.e.symm (hat p.2.1)) := p.2.2
      have e1 : hat p.2.1 = M₁.co.e (incM F (Φ₁.symm p.2)) := by
        rw [hΦ₁, LinearEquiv.apply_symm_apply]; rfl
      rwa [e1, LinearEquiv.symm_apply_apply] at h
    · rw [incM_one, Matrix.transpose_one, Matrix.mul_one, ← incM_mul]
      ext i j
      simp only [incM, incV, Matrix.map_apply, Matrix.add_apply, Matrix.vecMulVec_apply, map_add, map_mul]
  have hiso : ∀ a ∈ LinearMap.range T, ∀ b ∈ LinearMap.range T, a.1 ⬝ᵥ b.2 = b.1 ⬝ᵥ a.2 := by
    intro a ha b hb
    obtain ⟨m, hm, ea⟩ := hQ a ha
    obtain ⟨m', hm', eb⟩ := hQ b hb
    have h := symp_Q hH hxx horth hgram M M₁ M₂ hm hm'
    rw [← ea, ← eb] at h
    simp only [hat] at h
    rw [← sub_eq_zero]
    apply AdeleRing.algebraMap_injective (𝓞 F) F
    rw [map_sub, map_zero, RingHom.map_dotProduct, RingHom.map_dotProduct]
    exact h
  refine ⟨LinearMap.range T, hiso, le_antisymm (GlobalTheory.T.lagrangian_dimension_bound F _ _ hiso) ?_, hQ⟩
  rw [LinearMap.finrank_range_of_inj hT, Module.finrank_prod, Module.finrank_pi_fintype]
  simp only [h2, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, Fintype.card_prod]
  calc n * d = d * 2 + d₂ * d := by rw [← hrank]; ring
    _ ≤ _ := by omega

theorem comp_unip_invariant : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ),
    IsPair B M χX χW om r s r' s' →
    ∀ (d₁ : ℕ) (W₁ : Spc F E d₁) (H' : Plane E d d₁) (i₀ i₁ : ℕ), H'.IsAdapted σ B W W₁ i₀ i₁ →
    ∀ (d₂ : ℕ) (H : Plane E n d₂), (d₂ + 2 = n ∧ form σ X.J H.x H.x = 0 ∧ form σ X.J H.y H.y = 0 ∧ form σ X.J H.x H.y = 1 ∧
        (∀ u, form σ X.J (H.ι *ᵥ u) H.x = 0 ∧ form σ X.J (H.ι *ᵥ u) H.y = 0) ∧ Function.Injective H.ι.mulVec) →
    ∀ (V₁ : Spc F E d₂) (M₁ : Model σ V₁ W) (e : Fn F n d →ₗ[ℂ] Fn F d₂ d),
      V₁.J = H.ιᵀ * X.J * H.ι.map σ → M₁.IsGood B.ψ → IsEv B M M₁ H.ι 1 {u | ∃ z, u = Matrix.vecMulVec (incV F H.x) z} e →
    ∀ (M₂ : Model σ V₁ W₁) (e₂ : Fn F d₂ d →ₗ[ℂ] Fn F d₂ d₁),
      (∀ x : Matrix (Fin d₂) (Fin d₁) E, ∃ y z : Fin d₂ × Fin d₁ → F,
        M₂.co.e (incM F x) = (fun i => algebraMap F (AF F) (y i), fun i => algebraMap F (AF F) (z i))) →
      IsEv B M₁ M₂ 1 H'.ι (iso0 d₂ H') e₂ →
    ∀ u' ∈ unip σ W H', ∀ Φ ∈ schA F (Fin n × Fin d), e₂ (e (om (1, u') Φ)) = e₂ (e Φ) := by
  intro _ F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hP d₁ W₁ H' i₀ i₁ hH' d₂ H hH V₁ M₁ e hgram hM₁ he M₂ e₂ hrat he₂
  classical
  obtain ⟨hrank, hxx, -, hxy, horth, hinj⟩ := hH
  have hstd : IsStd B.ψ := hP.base.std
  have hS := IsUWeilPair.isUSplitting hP.weil
  have hW₁ := KernelZero.isSkew_complement F E σ B hP.base d d₁ W W₁ H' i₀ i₁ r' s' hP.skew hH'
  obtain ⟨L, hLiso, hLrank, hL⟩ := exists_lagr hP.base hH' (GlobalTheory.T.skew_determinant_ne_zero_first_space F E σ B d₁ W₁ _ _ hW₁) hrank hxx hxy horth hinj hgram
    M M₁ M₂ hP.good hM₁ hrat
  have hρ : ∀ u, ∀ Φ ∈ schA F (Fin n × Fin d), M.co.rho B.ψ u Φ ∈ schA F (Fin n × Fin d) :=
    fun u Φ hΦ => GlobalTheory.EvZeroUniq.schr_mem_schA _ hstd _ hΦ
  have hρ₁ : ∀ u, ∀ Φ ∈ schA F (Fin d₂ × Fin d), M₁.co.rho B.ψ u Φ ∈ schA F (Fin d₂ × Fin d) :=
    fun u Φ hΦ => GlobalTheory.EvZeroUniq.schr_mem_schA _ hstd _ hΦ
  have h1d : incM F (1 : Matrix (Fin d) (Fin d) E) = 1 := GlobalTheory.MixedLagrX.incM_one
  have h1v : incM F (1 : Matrix (Fin d₂) (Fin d₂) E) = 1 := GlobalTheory.MixedLagrX.incM_one
  let δ : Fn F d₂ d₁ →ₗ[ℂ] ℂ := LinearMap.proj 0
  have hδe : ∀ (f : Fn F d₂ d₁) x, f x = δ (M₂.co.rho B.ψ (M₂.co.e.symm (x, 0)) f) := fun f x =>
    GlobalTheory.EvZeroUniq.apply_eq_rho _ _ f x
  have hfix : ∀ z, (M₂.co.e z).1 = 0 → ∀ f : Fn F d₂ d₁, δ (M₂.co.rho B.ψ z f) = δ f :=
    fun z hz f => GlobalTheory.EvZeroUniq.rho_apply_zero _ _ f z hz
  let ιX : Matrix (Fin d₂) (Fin d) (AE F E) → Matrix (Fin n) (Fin d) (AE F E) :=
    fun z => incM F H.ι * z * (incM F (1 : Matrix (Fin d) (Fin d) E))ᵀ
  let ιW : Matrix (Fin d₂) (Fin d₁) (AE F E) → Matrix (Fin d₂) (Fin d) (AE F E) :=
    fun z => incM F (1 : Matrix (Fin d₂) (Fin d₂) E) * z * (incM F H'.ι)ᵀ
  have omul : ∀ g h : UA σ W.J, ∀ Φ, om (1, g * h) Φ = om (1, g) (om (1, h) Φ) := fun g h Φ => by
    rw [← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk, mul_one]
  have om1 : ∀ Φ, om (1, 1) Φ = Φ := fun Φ => by
    rw [show ((1 : UA σ X.J), (1 : UA σ W.J)) = 1 from rfl, map_one, Module.End.one_apply]
  have hact : ∀ (h : UA σ W.J) w, actAB (cA σ) ((1, h) : UA σ X.J × UA σ W.J) w = w * (mat h)ᵀ := by
    intro h w; simp [actAB, mat]

  have laws : ∀ h ∈ GlobalTheory.UnipEv.stabilizer₂ σ W H',
      (∀ a, ∀ Φ ∈ schA F (Fin n × Fin d), e₂ (e (om (1, h) (M.co.rho B.ψ (Matrix.vecMulVec (incV F H.x) a) Φ))) =
        e₂ (e (om (1, h) Φ))) ∧
      (∀ y, ∀ Φ ∈ schA F (Fin n × Fin d), e₂ (e (om (1, h) (M.co.rho B.ψ (ιX (Matrix.vecMulVec y (incV F H'.x))) Φ))) =
        e₂ (e (om (1, h) Φ))) ∧
      (∀ z, ∀ Φ ∈ schA F (Fin n × Fin d), e₂ (e (om (1, h) (M.co.rho B.ψ (ιX (ιW z)) Φ))) =
        M₂.co.rho B.ψ z (e₂ (e (om (1, h) Φ)))) := by
    rintro h ⟨⟨t, ht⟩, hι⟩
    have hX : ∀ z, ιX z * (mat h)ᵀ = ιX (z * (mat h)ᵀ) := fun z => by
      simp only [ιX, h1d, Matrix.transpose_one, Matrix.mul_one, Matrix.mul_assoc]
    refine ⟨fun a Φ hΦ => ?_, fun y Φ hΦ => ?_, fun z Φ hΦ => ?_⟩
    · rw [hS.impl (1, h) _ Φ hΦ, hact, Matrix.vecMulVec_mul, he.inv _ ⟨_, rfl⟩ _ (hS.pres _ Φ hΦ)]
    · have hΨ := hS.pres (1, h) Φ hΦ
      rw [hS.impl (1, h) _ Φ hΦ, hact, hX, he.Heisenberg₂ _ _ hΨ, Matrix.vecMulVec_mul, Matrix.vecMul_transpose, ht]
      refine he₂.inv _ ⟨(t : AE F E) • y, ?_⟩ _ (he.maps _ hΨ)
      ext i j
      simp only [Matrix.vecMulVec_apply, Pi.smul_apply, smul_eq_mul]
      ring
    · have hΨ := hS.pres (1, h) Φ hΦ
      choose β hβ using fun j : Fin d₁ => hι (Pi.single j 1)
      have hgι : mat h * incM F H'.ι = incM F H'.ι + Matrix.vecMulVec (incV F H'.x) β := by
        ext i j
        have h := congrFun (hβ j) i
        rw [Matrix.mulVec_mulVec, Matrix.mulVec_single_one, Matrix.mulVec_single_one] at h
        simpa [Matrix.vecMulVec_apply, mul_comm] using h
      have hw : ιW z * (mat h)ᵀ = Matrix.vecMulVec (z *ᵥ β) (incV F H'.x) + ιW z := by
        simp only [ιW, h1v, Matrix.one_mul]
        rw [Matrix.mul_assoc, ← Matrix.transpose_mul, hgι, Matrix.transpose_add, Matrix.mul_add, Matrix.transpose_vecMulVec,
          Matrix.mul_vecMulVec, add_comm]
      have h0 := GlobalTheory.T.symplectic_isotropic_embedded_vanishes_adelic F E σ d₂ d d₁ V₁.J W.J H' (fun u => (hH'.orth u).1) _ ⟨z *ᵥ β, rfl⟩ z
      rw [M₁.co.form] at h0
      rw [hS.impl (1, h) _ Φ hΦ, hact, hX, he.Heisenberg₂ _ _ hΨ, hw, rho_add B.ψ M₁ _ _ (by linear_combination -h0),
        he₂.inv _ ⟨_, rfl⟩ _ (hρ₁ _ _ (he.maps _ hΨ)), he₂.Heisenberg₂ _ _ (he.maps _ hΨ)]
  let l : UA σ W.J → (Fn F n d →ₗ[ℂ] ℂ) := fun h => ((δ ∘ₗ e₂) ∘ₗ e) ∘ₗ om (1, h)
  have hl : ∀ h Φ, l h Φ = δ (e₂ (e (om (1, h) Φ))) := fun _ _ => rfl
  have hadm : ∀ h, l h ∈ (adeleClass F).adm (Fin n × Fin d) := fun h =>
    hS.adm (1, h) _ (GlobalTheory.EvAdm.comp_mem_adm F E σ B n d d₂ d X W V₁ W M M₁ H.ι 1 _ e hP.good hM₁ he _ (first_coordinate_admissible hM₁ he₂))
  have hinvL : ∀ h ∈ GlobalTheory.UnipEv.stabilizer₂ σ W H', ∀ (t : AF F), ∀ w ∈ L, ∀ φ ∈ schA F (Fin n × Fin d),
      l h (schr B.ψ (t • ((fun i => algebraMap F (AF F) (w.1 i)), (fun i => algebraMap F (AF F) (w.2 i)))) φ) = l h φ := by
    intro h hh t w hw φ hφ
    obtain ⟨la, lb, lc⟩ := laws h hh
    obtain ⟨m, hm, hwm⟩ := hL w hw
    have key : schr B.ψ (t • hat w) φ = M.co.rho B.ψ (t • m) φ := by
      rw [hwm, ← LinearEquiv.map_smul]; rfl
    change l h (schr B.ψ (t • hat w) φ) = l h φ
    rw [key]
    obtain ⟨a, _, ⟨_, ⟨y, rfl⟩, z, hz, rfl⟩, hm'⟩ := hm.smul t
    have qa : Q M₂ H H' (Matrix.vecMulVec (incV F H.x) a) :=
      ⟨a, 0, GlobalTheory.MixedLagr.isMixed_zero M₂ H', by simp⟩
    have q0 : ∀ u, IsMixed M₂ H' u → Q M₂ H H' (ιX u) := fun u hu =>
      ⟨0, u, hu, by
        rw [show Matrix.vecMulVec (incV F H.x) (0 : Fin d → AE F E) = 0 by ext i j; simp [Matrix.vecMulVec_apply], zero_add]⟩
    have qb : Q M₂ H H' (ιX (Matrix.vecMulVec y (incV F H'.x))) := q0 _ ⟨_, ⟨y, rfl⟩, 0, by simp, by simp⟩
    have qc : Q M₂ H H' (ιX (ιW z)) := q0 _ ⟨_, ⟨0, rfl⟩, z, hz, by
      rw [show Matrix.vecMulVec (0 : Fin d₂ → AE F E) (incV F H'.x) = 0 by ext i j; simp [Matrix.vecMulVec_apply], zero_add]⟩
    have qbc : Q M₂ H H' (ιX (Matrix.vecMulVec y (incV F H'.x) + ιW z)) := q0 _ ⟨_, ⟨y, rfl⟩, z, hz, rfl⟩
    have e1 : t • m = Matrix.vecMulVec (incV F H.x) a + ιX (Matrix.vecMulVec y (incV F H'.x) + ιW z) := hm'
    have e2 : ιX (Matrix.vecMulVec y (incV F H'.x) + ιW z) = ιX (Matrix.vecMulVec y (incV F H'.x)) + ιX (ιW z) := by
      simp only [ιX, Matrix.mul_add, Matrix.add_mul]
    rw [e1, rho_add B.ψ M _ _ (symp_Q hH' hxx horth hgram M M₁ M₂ qa qbc), hl, la _ _ (hρ _ _ hφ), e2,
      rho_add B.ψ M _ _ (symp_Q hH' hxx horth hgram M M₁ M₂ qb qc), lb _ _ (hρ _ _ hφ), lc _ _ hφ, hfix z hz, hl]
  have hpt : ∀ h ∈ GlobalTheory.UnipEv.stabilizer₂ σ W H', ∀ Φ ∈ schA F (Fin n × Fin d), ∀ x,
      e₂ (e (om (1, h) Φ)) x = l h (M.co.rho B.ψ (ιX (ιW (M₂.co.e.symm (x, 0)))) Φ) := fun h hh Φ hΦ x => by
    rw [hl, (laws h hh).2.2 _ _ hΦ, ← hδe]
  by_cases h0 : ∀ Φ ∈ schA F (Fin n × Fin d), e₂ (e Φ) = 0
  · intro u _ Φ hΦ
    rw [h0 _ (hS.pres _ _ hΦ), h0 _ hΦ]
  push Not at h0
  obtain ⟨Φ₀, hΦ₀, hne⟩ := h0
  have twist : ∀ h ∈ GlobalTheory.UnipEv.stabilizer₂ σ W H', ∃ c : ℂ, ∀ Φ ∈ schA F (Fin n × Fin d), e₂ (e (om (1, h) Φ)) = c • e₂ (e Φ) := by
    intro h hh
    obtain ⟨x₀, hx₀⟩ := Function.ne_iff.1 hne
    have hone := hpt 1 (one_mem _)
    simp only [om1] at hone
    obtain ⟨c, hc⟩ := GlobalTheory.T.adelicStoneVonNeumann_lagrangian_uniqueness F B.ψ hstd (Fin n × Fin d) L hLiso hLrank (l h) (hadm h) (l 1) (hadm 1)
      (hinvL h hh) (hinvL 1 (one_mem _)) ⟨_, hρ _ Φ₀ hΦ₀, by rw [← hone Φ₀ hΦ₀ x₀]; exact hx₀⟩
    refine ⟨c, fun Φ hΦ => funext fun x => ?_⟩
    rw [hpt h hh Φ hΦ x, hc _ (hρ _ Φ hΦ), ← hone Φ hΦ x]
    rfl
  choose! c hc using twist
  have huniq : ∀ a b : ℂ, a • e₂ (e Φ₀) = b • e₂ (e Φ₀) → a = b := fun a b h => smul_left_injective ℂ hne h
  have hc1 := GlobalTheory.T.character_multiplicative_stabilizer F E σ B d W d₁ W₁ H' i₀ i₁ r' s' _ _ hP.base hP.skew hW₁ hH' c
    (fun g hg h hh => huniq _ _ (by
      rw [← hc _ (mul_mem hg hh) Φ₀ hΦ₀, omul, hc g hg _ (hS.pres _ _ hΦ₀), hc h hh _ hΦ₀, smul_smul]))
    (huniq _ _ (by rw [← hc 1 (one_mem _) Φ₀ hΦ₀, om1, one_smul]))
  intro u hu Φ hΦ
  rw [hc u (GlobalTheory.UnipEv.unip_le_stabP W H' hu) Φ hΦ, hc1 u hu, one_smul]

end GlobalTheory.NwAvgComp

namespace GlobalTheory.NwAvgInv

theorem avg_invariant : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ),
    IsPair B M χX χW om r s r' s' →
    ∀ (d₁ : ℕ) (W₁ : Spc F E d₁) (H' : Plane E d d₁) (i₀ i₁ : ℕ), H'.IsAdapted σ B W W₁ i₀ i₁ →
    ∀ (d₂ : ℕ) (H : Plane E n d₂), (d₂ + 2 = n ∧ form σ X.J H.x H.x = 0 ∧ form σ X.J H.y H.y = 0 ∧ form σ X.J H.x H.y = 1 ∧
        (∀ u, form σ X.J (H.ι *ᵥ u) H.x = 0 ∧ form σ X.J (H.ι *ᵥ u) H.y = 0) ∧ Function.Injective H.ι.mulVec) →
    ∀ (V₁ : Spc F E d₂) (M₁ : Model σ V₁ W) (e : Fn F n d →ₗ[ℂ] Fn F d₂ d),
      V₁.J = H.ιᵀ * X.J * H.ι.map σ → M₁.IsGood B.ψ → IsEv B M M₁ H.ι 1 {u | ∃ z, u = Matrix.vecMulVec (incV F H.x) z} e →
    ∀ (μ : Measure (unip σ X H)) (𝓕 : Set (unip σ X H)), μ.IsHaarMeasure →
      IsFundamentalDomain ((ratU σ X.J).subgroupOf (unip σ X H)) 𝓕 μ → μ 𝓕 = 1 →
    ∀ vf : unip σ X H → (Fin d₂ → AE F E), (∀ u, ∃ a : AE F E, mat u.1⁻¹ *ᵥ incV F H.y = incV F H.y + incM F H.ι *ᵥ vf u + a • incV F H.x) →
    ∀ Φ ∈ schA F (Fin n × Fin d), ∀ u' ∈ unip σ W H',
      ∫ u in 𝓕, thetaSum F (M₁.co.rho B.ψ (Matrix.vecMulVec (vf u) (incV F H'.x)) (e (om (1, u') Φ))) ∂μ =
        ∫ u in 𝓕, thetaSum F (M₁.co.rho B.ψ (Matrix.vecMulVec (vf u) (incV F H'.x)) (e Φ)) ∂μ := by
  intro hKP F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hP d₁ W₁ H' i₀ i₁ hH' d₂ H hH V₁ M₁ e hJ hM₁ he μ 𝓕 hμ h𝓕 h1 vf hvf Φ hΦ u' hu'
  obtain ⟨M₂, e₂, C, hrat, he₂, hA⟩ := GlobalTheory.T.pair_adapted_plane_theta_integral hKP F E σ B n d X W M χX χW om r s r' s' hP d₁ W₁ H' i₀ i₁ hH' d₂ H hH V₁ M₁ e hJ hM₁ he μ 𝓕 hμ h𝓕 h1 vf hvf
  have hΨ : om (1, u') Φ ∈ schA F (Fin n × Fin d) := (IsUWeilPair.isUSplitting hP.weil).pres _ Φ hΦ
  rw [hA _ (he.maps _ hΨ), hA _ (he.maps _ hΦ),
    GlobalTheory.NwAvgComp.comp_unip_invariant hKP F E σ B n d X W M χX χW om r s r' s' hP d₁ W₁ H' i₀ i₁ hH' d₂ H hH V₁ M₁ e hJ hM₁ he M₂ e₂ hrat he₂ u' hu' Φ hΦ]

end GlobalTheory.NwAvgInv

end
