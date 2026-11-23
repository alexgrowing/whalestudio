import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConfigATripleMatchedFold
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAdmittedFormEqAdelicThetaDistribution

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)
open scoped Classical

noncomputable section

namespace GlobalTheory.XiArchDecay

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

def oneS (F : Type) [Field F] [NumberField F] : SInf F Empty where
  toFun _ := 1
  smooth' := contDiff_const
  decay' k n := ⟨‖(0 : Empty → mixedEmbedding.mixedSpace F)‖ ^ k *
      ‖iteratedFDeriv ℝ n (fun _ : Empty → mixedEmbedding.mixedSpace F => (1 : ℂ)) 0‖, fun x => by
    rw [Subsingleton.elim x 0]⟩

theorem form_decay {κ ι : Type} [Fintype κ] [Fintype ι] (ψ : AddChar (AF F) ℂ) (hψ : IsStd ψ)
    (S U : ι → (κ → AF F) × (κ → AF F)) (hSU : ∀ i j, (S j).1 ⬝ᵥ (U i).2 - (U i).1 ⬝ᵥ (S j).2 = if i = j then 1 else 0)
    (l : ((κ → AF F) → ℂ) →ₗ[ℂ] ℂ) (hl : l ∈ (adeleClass F).adm κ)
    (hinv : ∀ i (a : AF F), ∀ Φ ∈ schA F κ, l (schr ψ (a • U i) Φ) = l Φ) (N : ℕ) :
    ∀ Φ ∈ schA F κ, ∃ C : ℝ, ∀ x : ι → AF F, (∀ i, (x i).2 = 0) →
      ‖l (schr ψ (∑ i, x i • S i) Φ)‖ * (1 + ‖fun i => evI F (x i)‖) ^ N ≤ C := by
  intro Φ hΦ
  obtain ⟨C, hC⟩ := GlobalTheory.ConeTateDecay.value_decay (κ₁ := Empty) ψ hψ S U hSU (LinearMap.pi fun _ => l)
    (fun g hg => by
      obtain ⟨T, hT⟩ := hl g hg
      refine ⟨T.smulRight (oneS F), fun f => funext fun y => ?_⟩
      change T f * 1 = l _
      rw [hT, mul_one])
    (fun i a Ψ hΨ => funext fun _ => hinv i a Ψ hΨ) (isCompact_singleton (x := 0)) 0 N Φ hΦ
  exact ⟨C, fun x hx => hC x (funext hx)⟩

theorem symp_pair (hcm : IsCMExt F E σ) {n d : ℕ} {JX : Matrix (Fin n) (Fin n) E} {JW : Matrix (Fin d) (Fin d) E}
    (hJ : ∀ i j, σ (JW j i) = -JW i j) (x y : Fin d → E) (hxy : form σ JW x y = 1) (a a' : Fin n → E) (l : AE F E) (c : E) :
    symp (cA σ) (-1) (incM F JX) (incM F JW) (l • Matrix.vecMulVec (incV F a) (incV F y))
      (inclR (F := F) (AF F) (σ c) • Matrix.vecMulVec (incV F a') (incV F x)) =
      Algebra.trace (AF F) (AE F E) (l * inclR (F := F) (AF F) c * inclR (F := F) (AF F) (form σ JX a a')) := by
  have hc : ∀ x : E, cA σ (inclR (F := F) (AF F) x) = inclR (F := F) (AF F) (σ x) := fun x => rfl
  rw [symp, GlobalTheory.XTermSupp.hTens_vv, GlobalTheory.XTermSupp.form_inc, GlobalTheory.XTermSupp.form_inc,
    GlobalTheory.XTermSupp.form_skew hcm hJ, hxy, hc, GlobalTheory.XTermSupp.invol hcm]
  congr 1
  simp

theorem exists_dual (hcm : IsCMExt F E σ) {B : Base F E} {n r s : ℕ} {X : Spc F E n} (hX : X.IsHerm σ B r s) :
    ∃ a : Fin n → Fin n → E, ∀ i j, form σ X.J (Pi.single j 1) (a i) = if i = j then 1 else 0 := by
  obtain ⟨w⟩ : Nonempty (InfinitePlace F) := inferInstance
  have hdet : X.J.det ≠ 0 := by
    intro h0
    have h1 : (X.J.map (B.emb w).1).det = 0 := by
      rw [← RingHom.mapMatrix_apply, ← RingHom.map_det, h0, map_zero]
    obtain ⟨v, hv, hM⟩ := Matrix.exists_mulVec_eq_zero_iff.2 h1
    have := (hX.cartan w).2.2 (star v) (by simpa using hv)
    rw [star_star, hM] at this
    simp at this
  refine ⟨fun i k => σ ((X.J⁻¹ *ᵥ Pi.single i 1) k), fun i j => ?_⟩
  simp only [form, GlobalTheory.XTermSupp.invol hcm]
  change Pi.single j 1 ⬝ᵥ X.J *ᵥ (X.J⁻¹ *ᵥ Pi.single i 1) = _
  rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.2 hdet), Matrix.one_mulVec,
    single_dotProduct, one_mul, Pi.single_apply]
  simp only [eq_comm]

theorem evI_realAd_mul (r : F) : evI F (realAd F 1 * algebraMap F (AF F) r) = mixedEmbedding F r := by
  change GlobalTheory.XTermDecay.qA (realAd F 1 * algebraMap F (AF F) r) = _
  rw [map_mul]
  have h1 : GlobalTheory.XTermDecay.qA (realAd F 1) = 1 := by
    change InfiniteAdeleRing.ringEquiv_mixedSpace F
      ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (algebraMap ℝ (mixedEmbedding.mixedSpace F) 1)) = _
    rw [RingEquiv.apply_symm_apply, map_one]
  rw [h1, one_mul, InfiniteAdeleRing.mixedEmbedding_eq_algebraMap_comp]
  rfl

theorem place_le_norm (w : InfinitePlace F) (r : F) : w r ≤ ‖mixedEmbedding F r‖ := by
  rw [← mixedEmbedding.normAtPlace_apply, mixedEmbedding.norm_eq_sup'_normAtPlace]
  exact Finset.le_sup' (fun w => mixedEmbedding.normAtPlace w (mixedEmbedding F r)) (Finset.mem_univ w)

theorem size_le {n m : ℕ} (b : Module.Basis (Fin m) F E) : ∃ c : ℝ, 1 ≤ c ∧ ∀ ξ : Fin n → E,
    1 + ∑ i, ∑ w : InfinitePlace E, w (ξ i) ≤
      c * (1 + ‖fun p : Fin n × Fin m => mixedEmbedding F (b.repr (ξ p.1) p.2)‖) := by
  set A : ℝ := ∑ _i : Fin n, ∑ w : InfinitePlace E, ∑ k, w (b k) with hA
  have hA0 : 0 ≤ A := by positivity
  refine ⟨1 + A, by linarith, fun ξ => ?_⟩
  set R := ‖fun p : Fin n × Fin m => mixedEmbedding F (b.repr (ξ p.1) p.2)‖ with hR
  have hR0 : 0 ≤ R := norm_nonneg _
  have h : ∑ i, ∑ w : InfinitePlace E, w (ξ i) ≤ A * R := by
    rw [hA, Finset.sum_mul]
    refine Finset.sum_le_sum fun i _ => ?_
    rw [Finset.sum_mul]
    refine Finset.sum_le_sum fun w _ => ?_
    rw [Finset.sum_mul]
    conv_lhs => rw [← b.sum_repr (ξ i)]
    refine (w.1.sum_le _ _).trans (Finset.sum_le_sum fun k _ => ?_)
    rw [Algebra.smul_def, map_mul, mul_comm]
    refine mul_le_mul_of_nonneg_left ?_ (apply_nonneg _ _)
    exact (place_le_norm (w.comap (algebraMap F E)) _).trans
      (norm_le_pi_norm (fun p : Fin n × Fin m => mixedEmbedding F (b.repr (ξ p.1) p.2)) (i, k))
  nlinarith

theorem decay : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (n d d₁ : ℕ) (X : Spc F E n) (W : Spc F E d) (W₁ : Spc F E d₁) (M : Model σ X W) (M₁ : Model σ X W₁) (H' : Plane E d d₁) (i₀ i₁ : ℕ),
    H'.IsAdapted σ B W W₁ i₀ i₁ → M₁.IsGood B.ψ → ∀ (e₀ : Fn F n d →ₗ[ℂ] Fn F n d₁), IsEv B M M₁ 1 H'.ι (iso0 n H') e₀ → B.IsGood σ → M.IsGood B.ψ → (∃ r s r' s' : ℕ, X.IsHerm σ B r s ∧ W.IsSkew σ B r' s') →
    ∀ Φ ∈ schA F (Fin n × Fin d), ∀ K : ℕ, ∃ C : ℝ, ∀ ξ : Fin n → E,
      ‖thetaSum F (e₀ (M.co.rho B.ψ (realAd F 1 • Matrix.vecMulVec (incV F ξ) (incV F H'.y)) Φ))‖ *
        (1 + ∑ i, ∑ w : InfinitePlace E, w (ξ i)) ^ K ≤ C := by
  intro _ F E _ _ _ _ _ σ B n d d₁ X W W₁ M M₁ H' i₀ i₁ hAd hM₁ e₀ he hB hM hXW Φ hΦ K
  obtain ⟨r, s, r', s', hX, hW⟩ := hXW
  haveI : Module.Finite F E := Module.Finite.of_restrictScalars_finite ℚ F E
  let b := Module.finBasis F E
  choose c hc using GlobalTheory.ConeTateSupp.trace_mul_dual (F := F) (E := E) b
  obtain ⟨a, ha⟩ := exists_dual hB.cm hX
  obtain ⟨l, hl, hlθ⟩ := GlobalTheory.ThetaAdmitted.exists_admitted_form_eq_adelicThetaDistribution_alt F (Fin n × Fin d₁)
  let S := fun p : Fin n × Fin (Module.finrank F E) =>
    M.co.e (inclR (F := F) (AF F) (b p.2) • Matrix.vecMulVec (incV F (Pi.single p.1 (1 : E))) (incV F H'.y))
  let U := fun p : Fin n × Fin (Module.finrank F E) =>
    M.co.e (inclR (F := F) (AF F) (σ (c p.2)) • Matrix.vecMulVec (incV F (a p.1)) (incV F H'.x))
  obtain ⟨C, hC⟩ := form_decay B.ψ hB.std S U (fun p q => by
      rw [← M.co.form, symp_pair hB.cm hW.skew _ _ hAd.xy, ha]
      by_cases h1 : p.1 = q.1
      · rw [if_pos h1, map_one, mul_one, hc,
          show inclR (F := F) (AF F) (b q.2) = Algebra.TensorProduct.basis (AF F) b q.2 from
            (Algebra.TensorProduct.basis_apply _ _).symm, Module.Basis.equivFun_self]
        by_cases h2 : p.2 = q.2
        · rw [if_pos h2.symm, if_pos (Prod.ext h1 h2)]
        · rw [if_neg (Ne.symm h2), if_neg fun h => h2 (congrArg Prod.snd h)]
      · rw [if_neg h1, map_zero, mul_zero, map_zero, if_neg fun h => h1 (congrArg Prod.fst h)])
    (l ∘ₗ e₀) (GlobalTheory.EvAdm.comp_mem_adm F E σ B n d n d₁ X W X W₁ M M₁ _ _ _ e₀ hM hM₁ he l hl)
    (fun p t Ψ hΨ => by
      have := he.inv (Matrix.vecMulVec (t • inclR (F := F) (AF F) (σ (c p.2)) • incV F (a p.1)) (incV F H'.x))
        ⟨_, rfl⟩ Ψ hΨ
      rw [Matrix.smul_vecMulVec, Matrix.smul_vecMulVec, Darboux.rho, map_smul] at this
      exact congrArg l this) K Φ hΦ
  obtain ⟨c₀, hc₀, hsz⟩ := size_le (n := n) b
  refine ⟨c₀ ^ K * C, fun ξ => ?_⟩
  have key := hC (fun p => realAd F 1 * algebraMap F (AF F) (b.repr (ξ p.1) p.2)) fun p => zero_mul _
  have hS : ∑ p : Fin n × Fin (Module.finrank F E), (realAd F 1 * algebraMap F (AF F) (b.repr (ξ p.1) p.2)) • S p =
      M.co.e (realAd F 1 • Matrix.vecMulVec (incV F ξ) (incV F H'.y)) := by
    simp only [S, mul_smul, ← map_smul, ← map_sum, ← Finset.smul_sum]
    congr 2
    ext i j
    rw [Matrix.sum_apply, Fintype.sum_prod_type, Finset.sum_eq_single i]
    · simp only [Matrix.smul_apply, Matrix.vecMulVec_apply, incV, Pi.single_eq_same, map_one, one_mul, smul_eq_mul,
        ← smul_mul_assoc, ← Finset.sum_mul]
      congr 1
      conv_rhs => rw [← b.sum_repr (ξ i)]
      rw [map_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      change algebraMap F (AF F) (b.repr (ξ i) k) • ((1 : AF F) ⊗ₜ[F] b k) = (1 : AF F) ⊗ₜ[F] (b.repr (ξ i) k • b k)
      rw [algebraMap_smul, TensorProduct.tmul_smul]
    · intro i' _ hi
      simp [Matrix.vecMulVec_apply, incV, Pi.single_eq_of_ne hi.symm]
    · intro h
      exact absurd (Finset.mem_univ i) h
  simp only [evI_realAd_mul] at key
  rw [hS, LinearMap.comp_apply] at key
  rw [← hlθ _ (he.maps _ (GlobalTheory.HeisSchA.rho_mem_schA M B.ψ hB.std _ _ hΦ))]
  calc _ ≤ ‖l (e₀ (M.co.rho B.ψ (realAd F 1 • Matrix.vecMulVec (incV F ξ) (incV F H'.y)) Φ))‖ *
        (c₀ * (1 + ‖fun p : Fin n × Fin (Module.finrank F E) => mixedEmbedding F (b.repr (ξ p.1) p.2)‖)) ^ K := by
        gcongr
        exact hsz ξ
    _ ≤ c₀ ^ K * C := by
        rw [mul_pow, mul_left_comm]
        exact mul_le_mul_of_nonneg_left key (by positivity)

end GlobalTheory.XiArchDecay

end
