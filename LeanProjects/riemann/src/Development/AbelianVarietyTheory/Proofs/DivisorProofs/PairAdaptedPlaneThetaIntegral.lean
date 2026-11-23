import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PairAdaptedPlaneCompatible
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzFunctionalArchimedeanFactor
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAdmittedFormEqAdelicThetaDistribution
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaTransformRationalTranslateQuasiInvariant
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasConstTermThetaSumSchrLin
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MeanEqMeanConstTerm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnipotentRadicalHomeomorphHeisenberg
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConstantTermUnipotentIntegral
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExtendByZeroMemSchA
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExtendByZeroSchwartzBruhatMap
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilRepresentationPreservesSchwartz

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

noncomputable section

namespace GlobalTheory.UnipThetaMean

section Mean

theorem mean_constTerm {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
    [SecondCountableTopology G] [T2Space G] [MeasurableSpace G] [BorelSpace G] (Γ : Subgroup G) [Countable Γ]
    (μ : Measure G) (𝓕 : Set G) (hμ : μ.IsHaarMeasure) (h𝓕 : IsFundamentalDomain Γ 𝓕 μ) (h1 : μ 𝓕 = 1)
    {Z : Type} [AddCommGroup Z] [TopologicalSpace Z] (Λ : Set Z) (π : G → Z) (f : Z → ℂ) (c₀ : ℂ)
    (hπ : ∀ u v, π (u * v) = π u + π v) (hπc : Continuous π) (hπs : Function.Surjective π) (hΛ : ∀ γ ∈ Γ, π γ ∈ Λ)
    (hf : GlobalTheory.ThK.RankRed.HasConstTerm Λ f c₀) : ∫ u in 𝓕, f (π u) ∂μ = c₀ := by
  haveI := hμ
  haveI : μ.IsMulRightInvariant :=
    GlobalTheory.ThK.RankRed.MeanConst.rightInv Γ μ h𝓕 (by rw [h1]; exact ENNReal.one_ne_top)
  haveI : IsFiniteMeasure (μ.restrict 𝓕) := ⟨by rw [Measure.restrict_apply_univ, h1]; exact ENNReal.one_lt_top⟩
  have hr : μ.real 𝓕 = 1 := by simp [Measure.real, h1]
  have hconst : ∀ c : ℂ, ∫ _ in 𝓕, c ∂μ = c := fun c => by rw [setIntegral_const, hr, one_smul]
  have hconstR : ∀ c : ℝ, ∫ _ in 𝓕, c ∂μ = c := fun c => by rw [setIntegral_const, hr, one_smul]
  obtain ⟨ι, c, χ, hι, hsum, hχ, hrep⟩ := hf
  have hz : ∀ k, ∫ v in 𝓕, χ k (π v) ∂μ = 0 := by
    intro k
    obtain ⟨z, hz⟩ := AddChar.ne_one_iff.1 (hχ k).2.2.2
    obtain ⟨w, rfl⟩ := hπs z
    have hinvk : ∀ γ ∈ Γ, ∀ u, χ k (π (γ * u)) = χ k (π u) := fun γ hγ u => by
      rw [hπ, AddChar.map_add_eq_mul, (hχ k).2.2.1 _ (hΛ γ hγ), one_mul]
    have e := GlobalTheory.ThK.RankRed.MeanConst.setIntegral_mul_right Γ μ h𝓕 (φ := fun u => χ k (π u)) hinvk w
    simp only [hπ, AddChar.map_add_eq_mul] at e
    rw [integral_mul_const] at e
    have : (∫ v in 𝓕, χ k (π v) ∂μ) * (χ k (π w) - 1) = 0 := by rw [mul_sub, e, mul_one, sub_self]
    exact (mul_eq_zero.1 this).resolve_right (sub_ne_zero.2 hz)
  have hnk : ∀ k v, ‖c k * χ k (π v)‖ = ‖c k‖ := fun k v => by rw [norm_mul, (hχ k).2.1, mul_one]
  have hck : ∀ k, Continuous fun v => c k * χ k (π v) := fun k => ((hχ k).1.comp hπc).const_mul (c k)
  have hint : ∀ k, Integrable (fun v => c k * χ k (π v)) (μ.restrict 𝓕) := fun k =>
    Integrable.of_bound (hck k).aestronglyMeasurable ‖c k‖ (Filter.Eventually.of_forall fun v => (hnk k v).le)
  have hts := integral_tsum_of_summable_integral_norm hint (by simpa only [hnk, hconstR] using hsum)
  have hsum' : ∀ v, Summable fun k => ‖c k * χ k (π v)‖ := fun v => by simpa only [hnk] using hsum
  have hSint : Integrable (fun v => ∑' k, c k * χ k (π v)) (μ.restrict 𝓕) := by
    have hcont : Continuous (fun v => ∑' k, c k * χ k (π v)) := continuous_tsum hck hsum fun k v => (hnk k v).le
    refine Integrable.of_bound hcont.aestronglyMeasurable (∑' k, ‖c k‖) (Filter.Eventually.of_forall fun v => ?_)
    calc ‖∑' k, c k * χ k (π v)‖ ≤ ∑' k, ‖c k * χ k (π v)‖ := norm_tsum_le_tsum_norm (hsum' v)
      _ = ∑' k, ‖c k‖ := by simp only [hnk]
  simp_rw [hrep]
  rw [integral_add (integrable_const _) hSint, hconst, ← hts]
  simp [integral_const_mul, hz]

end Mean

section Theta

open GlobalTheory.SympChange GlobalTheory.SympChangeBij

theorem thetaSum_op {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ] [DecidableEq κ] (ψ : AddChar (AF F) ℂ)
    (hψ : IsStd ψ) (G : Matrix (κ ⊕ κ) (κ ⊕ κ) F) (e : ((κ → AF F) → ℂ) →ₗ[ℂ] (κ → AF F) → ℂ)
    (hmaps : ∀ Φ ∈ schA F κ, e Φ ∈ schA F κ) (hheis : ∀ w, ∀ Φ ∈ schA F κ, e (schr ψ w Φ) = schr ψ (spAct G w) (e Φ))
    (hloc : GlobalTheory.DblEval.IsLocOp e) (hsurj : Set.SurjOn e (schA F κ : Set ((κ → AF F) → ℂ)) (schA F κ : Set ((κ → AF F) → ℂ))) :
    ∃ c : ℂ, c ≠ 0 ∧ ∀ Φ ∈ schA F κ, thetaSum F (e Φ) = c * thetaSum F Φ := by
  obtain ⟨lθ, hlθ, hlθ'⟩ := GlobalTheory.ThetaAdmitted.exists_admitted_form_eq_adelicThetaDistribution_alt F κ
  have hcomp := GlobalTheory.MixedVec.admissible_of_local_operator e hloc lθ hlθ
  obtain ⟨c, hc⟩ := GlobalTheory.ThetaFunctionalUnique.main F ψ hψ κ (fun Φ => thetaSum F (e Φ))
    (fun Φ hΦ Ψ hΨ => by
      simp only [map_add]
      exact GlobalTheory.WeilM.thetaSum_add F (hmaps Φ hΦ) (hmaps Ψ hΨ))
    (fun c Φ _ => by simp only [map_smul]; exact GlobalTheory.WeilM.thetaSum_smul F c (e Φ))
    (fun g hg => by
      obtain ⟨T, hT⟩ := hcomp g hg
      refine ⟨T, fun f => ?_⟩
      have hm : pureA F f g ∈ schA F κ := Submodule.subset_span ⟨f, g, hg, rfl⟩
      rw [← hlθ' _ (hmaps _ hm)]
      exact hT f)
    (fun a b Φ hΦ => by
      have h1 : spAct G ((fun i => algebraMap F (AF F) (a i)), (fun i => algebraMap F (AF F) (b i))) =
          ((fun i => algebraMap F (AF F) ((G *ᵥ Sum.elim a b) (Sum.inl i))),
            (fun i => algebraMap F (AF F) ((G *ᵥ Sum.elim a b) (Sum.inr i)))) := by
        have h2 : Sum.elim (fun i => algebraMap F (AF F) (a i)) (fun i => algebraMap F (AF F) (b i)) =
            algebraMap F (AF F) ∘ Sum.elim a b := by
          funext k; cases k <;> rfl
        simp only [spAct, h2, RingHom.map_mulVec]
      show thetaSum F (e (schr ψ _ Φ)) = _
      rw [hheis _ Φ hΦ, h1]
      exact GlobalTheory.ThetaQuasiRat.thetaSum_schr_rat F ψ (fun a => hψ.2.1 a) _ _ (e Φ))
  refine ⟨c, ?_, hc⟩
  rintro rfl
  obtain ⟨φ₀, hφ₀, hne⟩ := GlobalTheory.ThetaSumNe.exists_mem_schA_thetaSum_ne_zero F κ
  obtain ⟨Φ, hΦ, rfl⟩ := hsurj hφ₀
  exact hne (by rw [hc Φ hΦ, zero_mul])

end Theta

section Coords

open GlobalTheory.ThK.PlaneEv GlobalTheory.ThK.PlaneEv.Coords

theorem exists_coords {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E) {n d d₁ r' s' i₀ i₁ : ℕ} (X : Spc F E n) (W : Spc F E d) (W₁ : Spc F E d₁) (H' : Plane E d d₁)
    (hd : d = d₁ + 2) (hB : B.IsGood σ) (hXh : ∀ i j, σ (X.J j i) = X.J i j) (hXdet : X.J.det ≠ 0)
    (hW : W.IsSkew σ B r' s') (hH : H'.IsAdapted σ B W W₁ i₀ i₁) :
    ∃ (co₂ : Darboux (symp (R := AF F) (cA σ) (-1) (incM F X.J) (incM F W₁.J)) (Fin n × Fin d₁))
      (co : Darboux (symp (R := AF F) (cA σ) (-1) (incM F X.J) (incM F W.J)) (Fin n × Fin d)),
      (∀ x : Matrix (Fin n) (Fin d₁) E, ∃ y z : Fin n × Fin d₁ → F,
        co₂.e (incM F x) = (fun i => algebraMap F (AF F) (y i), fun i => algebraMap F (AF F) (z i))) ∧
      (∀ z : Matrix (Fin n) (Fin d₁) (AE F E), co.e (z * (incM F H'.ι)ᵀ) = (ins0 hd (co₂.e z).1, ins0 hd (co₂.e z).2)) ∧
      (∀ a : Fin n → AE F E, (co.e (Matrix.vecMulVec a (incV F H'.x))).1 = 0 ∧
        ∀ p, (co.e (Matrix.vecMulVec a (incV F H'.x))).2 ((idx hd).symm (Sum.inl p)) = 0) ∧
      (∀ b : Fin n → AE F E, (co.e (Matrix.vecMulVec b (incV F H'.y))).2 = 0 ∧
        ∀ p, (co.e (Matrix.vecMulVec b (incV F H'.y))).1 ((idx hd).symm (Sum.inl p)) = 0) ∧
      ∀ x : Matrix (Fin n) (Fin d) E, ∃ y z : Fin n × Fin d → F,
        co.e (incM F x) = (fun i => algebraMap F (AF F) (y i), fun i => algebraMap F (AF F) (z i)) := by
  subst hd
  obtain ⟨w⟩ : Nonempty (InfinitePlace F) := inferInstance
  have hσ : ∀ x, σ (σ x) = x := fun x => by
    apply ((B.emb w).1 : E →+* ℂ).injective
    rw [hB.cm.2.2.2, hB.cm.2.2.2, star_star]
  obtain ⟨p, q, hpq, hpq', hpr, hqr⟩ := GlobalTheory.T.quadratic_trace_form_coordinates σ n X.J hσ hB.cm.2.2.1 hXh hXdet
  let Q : Matrix (Fin (d₁ + 2)) (Fin (d₁ + 2)) E := Matrix.of fun r c =>
    Fin.addCases (motive := fun _ => E) (fun i => H'.ι r i) (fun t => ![H'.x r, H'.y r] t) c
  have hQι : ∀ r i, Q r (Fin.castAdd 2 i) = H'.ι r i := fun r i => by simp [Q]
  have hQx : ∀ r, Q r (Fin.natAdd d₁ 0) = H'.x r := fun r => by simp [Q]
  have hQy : ∀ r, Q r (Fin.natAdd d₁ 1) = H'.y r := fun r => by simp [Q]
  have hQdet := GlobalTheory.T.adapted_plane_basis_change_matrix F E σ B d₁ r' s' i₀ i₁ W W₁ H' Q hW hH hQι hQx hQy
  obtain ⟨hG1, hG2, hG3, hG00, hG11, hG01, hG10⟩ :=
    GlobalTheory.T.hyperbolic_basis_matrix_gram σ d₁ W.J W₁.J H'.x H'.y H'.ι Q hσ hW.skew hH.xx hH.yy hH.xy hH.orth hH.gram hQι hQx hQy
  have hWdet : W.J.det ≠ 0 := fun h0 => by
    apply GlobalTheory.RatDarboux.det_ne_zero_of_isCartan (hW.cartan w)
    have := ((B.emb w).1 : E →+* ℂ).map_det W.J
    rw [h0, map_zero] at this
    rw [Matrix.det_smul]
    exact mul_eq_zero_of_right _ this.symm
  have hGdet : (Qᵀ * W.J * Q.map σ).det ≠ 0 := by
    have hm : (Q.map σ).det = σ Q.det := by rw [AlgHom.map_det]; rfl
    rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, hm]
    exact mul_ne_zero (mul_ne_zero hQdet hWdet) ((map_ne_zero σ).2 hQdet)
  have hW₁det : W₁.J.det ≠ 0 := fun h0 => by
    obtain ⟨v, hv, hv0⟩ := Matrix.exists_vecMul_eq_zero_iff.2 h0
    apply hGdet
    refine Matrix.exists_vecMul_eq_zero_iff.1 ⟨Fin.addCases (motive := fun _ => E) v (fun _ => 0), fun h => hv ?_, ?_⟩
    · funext a
      simpa using congrFun h (Fin.castAdd 2 a)
    · funext c
      refine Fin.addCases (fun a => ?_) (fun t => ?_) c
      · have := congrFun hv0 a
        simp only [Matrix.vecMul, dotProduct, Fin.sum_univ_add, Fin.addCases_left, Fin.addCases_right, zero_mul,
          Finset.sum_const_zero, add_zero, hG1] at this ⊢
        exact this
      · simp only [Matrix.vecMul, dotProduct, Fin.sum_univ_add, Fin.addCases_left, Fin.addCases_right, zero_mul,
          Finset.sum_const_zero, add_zero, hG2, mul_zero, Pi.zero_apply]
  have hW₁s : ∀ i j, σ (W₁.J j i) = -W₁.J i j := fun i j => by
    rw [← hH.gram]
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, map_sum, map_mul, hσ, hW.skew,
      Finset.sum_mul, ← Finset.sum_neg_distrib]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
  obtain ⟨co₁, hrat₁⟩ := GlobalTheory.RatDarboux.exists_darboux (AF F) hB.cm.2.2.1 σ hσ hXh hW₁s hXdet hW₁det
  let co₂ : Darboux (symp (R := AF F) (cA σ) (-1) (incM F X.J) (incM F W₁.J)) (Fin n × Fin d₁) := co₁
  have hrat₂ : ∀ x : Matrix (Fin n) (Fin d₁) E, ∃ y z : Fin n × Fin d₁ → F,
      co₂.e (incM F x) = (fun i => algebraMap F (AF F) (y i), fun i => algebraMap F (AF F) (z i)) := hrat₁
  have hQQ : Q * Q⁻¹ = 1 := Matrix.mul_nonsing_inv Q (Ne.isUnit hQdet)
  have hQQ' : Q⁻¹ * Q = 1 := Matrix.nonsing_inv_mul Q (Ne.isUnit hQdet)
  have hinc : ∀ {a b c : ℕ} (U : Matrix (Fin a) (Fin b) E) (V : Matrix (Fin b) (Fin c) E),
      incM F (U * V) = incM F U * incM F V := fun U V => Matrix.map_mul
  have hinc1 : incM F (1 : Matrix (Fin (d₁ + 2)) (Fin (d₁ + 2)) E) = 1 := Matrix.map_one _ (map_zero _) (map_one _)
  have h1 : (incM F Q)ᵀ * (incM F Q⁻¹)ᵀ = 1 := by
    rw [← Matrix.transpose_mul, ← hinc, hQQ', hinc1, Matrix.transpose_one]
  have h2 : (incM F Q⁻¹)ᵀ * (incM F Q)ᵀ = 1 := by
    rw [← Matrix.transpose_mul, ← hinc, hQQ, hinc1, Matrix.transpose_one]
  let mR : Matrix (Fin n) (Fin (d₁ + 2)) (AE F E) ≃ₗ[AF F] Matrix (Fin n) (Fin (d₁ + 2)) (AE F E) :=
    { toFun := fun u => u * (incM F Q⁻¹)ᵀ
      invFun := fun Y => Y * (incM F Q)ᵀ
      map_add' := fun u u' => Matrix.add_mul u u' _
      map_smul' := fun a u => Matrix.smul_mul a u _
      left_inv := fun u => by
        show u * (incM F Q⁻¹)ᵀ * (incM F Q)ᵀ = u
        rw [Matrix.mul_assoc, h2, Matrix.mul_one]
      right_inv := fun Y => by
        show Y * (incM F Q)ᵀ * (incM F Q⁻¹)ᵀ = Y
        rw [Matrix.mul_assoc, h1, Matrix.mul_one] }
  let e := mR ≪≫ₗ glueC co₂.e p q
  have he : ∀ u, e u = glueC co₂.e p q (u * (incM F Q⁻¹)ᵀ) := fun _ => rfl
  have hback : ∀ Y : Matrix (Fin n) (Fin (d₁ + 2)) (AE F E), Y * (incM F Q)ᵀ * (incM F Q⁻¹)ᵀ = Y := fun Y => by
    rw [Matrix.mul_assoc, h1, Matrix.mul_one]
  have hG : (incM F Q)ᵀ * incM F W.J * (incM F Q).map (cA σ) = incM F (Qᵀ * W.J * Q.map σ) := by
    rw [hinc, hinc]; rfl
  have key : ∀ Y Y' : Matrix (Fin n) (Fin (d₁ + 2)) (AE F E),
      symp (R := AF F) (cA σ) (-1) (incM F X.J) (incM F W.J) (Y * (incM F Q)ᵀ) (Y' * (incM F Q)ᵀ) =
        (e (Y * (incM F Q)ᵀ)).1 ⬝ᵥ (e (Y' * (incM F Q)ᵀ)).2 - (e (Y' * (incM F Q)ᵀ)).1 ⬝ᵥ (e (Y * (incM F Q)ᵀ)).2 := fun Y Y' => by
    rw [he, he, hback, hback, glueC_apply, glueC_apply, dot_idx, dot_idx, GlobalTheory.T.symplectic_form_right_mul_transpose, hG,
      GlobalTheory.T.block_gram_matrix_orthogonal_sum (cA σ) (-1) (incM F X.J) (incM F W₁.J) _ (fun a a' => by simp [incM, hG1]) (fun a t => by simp [incM, hG2])
        (fun t a => by simp [incM, hG3]) (by simp [incM, hG00]) (by simp [incM, hG11]) (by simp [incM, hG01])
        (by simp [incM, hG10]) Y Y',
      co₂.form, hpq (fun i => Y' i (Fin.natAdd d₁ 0)) (fun i => Y i (Fin.natAdd d₁ 1)),
      hpq' (fun i => Y i (Fin.natAdd d₁ 0)) (fun i => Y' i (Fin.natAdd d₁ 1)), neg_one_mul, neg_one_mul, map_neg, map_neg]
    ring
  refine ⟨co₂, ⟨e, fun u u' => ?_⟩, hrat₂, fun z => ?_, fun a => ?_, fun b => ?_, fun x => ?_⟩
  · have := key (u * (incM F Q⁻¹)ᵀ) (u' * (incM F Q⁻¹)ᵀ)
    rwa [Matrix.mul_assoc, h2, Matrix.mul_one, Matrix.mul_assoc, h2, Matrix.mul_one] at this
  · have hz : z * (incM F H'.ι)ᵀ = embC z 0 0 * (incM F Q)ᵀ := by
      ext i j
      simp [Matrix.mul_apply, Fin.sum_univ_add, embC, incM, hQι]
    rw [hz, he, hback, glueC_apply, embC_left, embC_zero, embC_one, map_zero, map_zero]
    rfl
  · have ha : Matrix.vecMulVec a (incV F H'.x) = embC (0 : Matrix (Fin n) (Fin d₁) (AE F E)) a 0 * (incM F Q)ᵀ := by
      ext i j
      simp [Matrix.mul_apply, Fin.sum_univ_add, embC, incM, incV, hQx, Matrix.vecMulVec_apply]
    rw [ha, he, hback, glueC_apply, embC_left, embC_zero, embC_one, map_zero, map_zero]
    refine ⟨funext fun k => ?_, fun k => ?_⟩
    · rcases idx rfl k with k | k <;> simp
    · simp
  · have hb : Matrix.vecMulVec b (incV F H'.y) = embC (0 : Matrix (Fin n) (Fin d₁) (AE F E)) 0 b * (incM F Q)ᵀ := by
      ext i j
      simp [Matrix.mul_apply, Fin.sum_univ_add, embC, incM, incV, hQy, Matrix.vecMulVec_apply]
    rw [hb, he, hback, glueC_apply, embC_left, embC_zero, embC_one, map_zero, map_zero]
    refine ⟨funext fun k => ?_, fun k => ?_⟩
    · rcases idx rfl k with k | k <;> simp
    · simp
  · rw [he, show incM F x * (incM F Q⁻¹)ᵀ = incM F (x * (Q⁻¹)ᵀ) from (hinc _ _).symm, glueC_apply]
    obtain ⟨y₁, z₁, hM⟩ := hrat₂ (Matrix.of fun i a => (x * (Q⁻¹)ᵀ) i (Fin.castAdd 2 a))
    obtain ⟨yb, hyb⟩ := hpr (fun i => (x * (Q⁻¹)ᵀ) i (Fin.natAdd d₁ 1))
    obtain ⟨za, hza⟩ := hqr (fun i => (x * (Q⁻¹)ᵀ) i (Fin.natAdd d₁ 0))
    refine ⟨fun k => Sum.elim y₁ yb (idx rfl k), fun k => Sum.elim z₁ za (idx rfl k), ?_⟩
    have e1 : (Matrix.of fun i a => incM F (x * (Q⁻¹)ᵀ) i (Fin.castAdd 2 a)) =
        incM F (Matrix.of fun i a => (x * (Q⁻¹)ᵀ) i (Fin.castAdd 2 a)) := rfl
    have e2 : ∀ c, (fun i => incM F (x * (Q⁻¹)ᵀ) i c) = incV F (fun i => (x * (Q⁻¹)ᵀ) i c) := fun _ => rfl
    rw [e1, e2, e2, hM, hyb, hza]
    ext k <;> dsimp only <;> rcases idx rfl k with k | k <;> simp

end Coords

section Mixed

open GlobalTheory.ThK.PlaneEv GlobalTheory.SympChange GlobalTheory.SympChangeBij GlobalTheory.ThK.Adapt

theorem ins0_eq_extend {R : Type} [Zero R] {n d d₁ : ℕ} (hd : d = d₁ + 2) (x : Fin n × Fin d₁ → R) :
    ins0 hd x = Function.extend (fun p => (idx hd).symm (Sum.inl p)) x 0 := by
  have hj : Function.Injective (fun p : Fin n × Fin d₁ => (idx hd).symm (Sum.inl p)) :=
    (idx hd).symm.injective.comp Sum.inl_injective
  funext k
  obtain ⟨k, rfl⟩ := (idx hd).symm.surjective k
  rcases k with k | k
  · rw [planeZeroInsertion_apply_inl]; exact (hj.extend_apply x 0 k).symm
  · rw [planeZeroInsertion_apply_inr, Function.extend_apply' _ _ _ (by rintro ⟨a, ha⟩; simpa using ha)]; rfl

theorem exists_mixed {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E) {n d d₁ r' s' i₀ i₁ : ℕ} (X : Spc F E n) (W : Spc F E d) (W₁ : Spc F E d₁) (H' : Plane E d d₁)
    (hB : B.IsGood σ) (hXh : ∀ i j, σ (X.J j i) = X.J i j) (hXdet : X.J.det ≠ 0)
    (hW : W.IsSkew σ B r' s') (hH : H'.IsAdapted σ B W W₁ i₀ i₁) (M : Model σ X W) (hM : M.IsGood B.ψ) :
    ∃ (M₂ : Model σ X W₁) (e₂ : Fn F n d →ₗ[ℂ] Fn F n d₁) (C : ℂ),
      (∀ x : Matrix (Fin n) (Fin d₁) E, ∃ y z : Fin n × Fin d₁ → F,
        M₂.co.e (incM F x) = (fun i => algebraMap F (AF F) (y i), fun i => algebraMap F (AF F) (z i))) ∧
      IsEv B M M₂ 1 H'.ι (iso0 n H') e₂ ∧
      ∀ φ ∈ schA F (Fin n × Fin d), GlobalTheory.ThK.RankRed.HasConstTerm (Set.range (incV F : (Fin n → E) → Fin n → AE F E))
        (fun z => thetaSum F (M.co.rho B.ψ (Matrix.vecMulVec z (incV F H'.x)) φ)) (C * thetaSum F (e₂ φ)) := by
  classical
  have hd : d = d₁ + 2 := hH.rank
  have hψ : IsStd B.ψ := hB.std
  obtain ⟨co₂, co, hrat₂, hlow, hx, hy, hrat⟩ := exists_coords σ B X W W₁ H' hd hB hXh hXdet hW hH
  obtain ⟨G, hGs, hGe⟩ := GlobalTheory.SympChange.darboux_change_rat F E σ n d X.J W.J M.co co hM.rat hrat
  obtain ⟨U, eI, eV, hsurj, hmaps, hheis, hSB, -, -, hind, hpure, hbij⟩ := GlobalTheory.MixedVec.hasOpB_of_isSymp B.ψ hψ G hGs
  have hloc : GlobalTheory.DblEval.IsLocOp U := ⟨eI, eV, fun v φ hφ => hSB v ▸ Submodule.mem_map_of_mem hφ, hind, hpure⟩
  obtain ⟨c₀, hc₀, hth⟩ := thetaSum_op B.ψ hψ G U hmaps hheis hloc hbij.surjOn
  have hU : ∀ u, ∀ Φ ∈ schA F (Fin n × Fin d), U (M.co.rho B.ψ u Φ) = schr B.ψ (co.e u) (U Φ) := fun u Φ hΦ => by
    rw [Darboux.rho, hheis _ Φ hΦ, hGe]
  let j : Fin n × Fin d₁ → Fin n × Fin d := fun p => (idx hd).symm (Sum.inl p)
  have hj : Function.Injective j := (idx hd).symm.injective.comp Sum.inl_injective
  have hevA : ∀ Φ : Fn F n d, evA F hd Φ = fun y => Φ (Function.extend j y 0) := fun Φ => by
    funext y; rw [evA_apply, ins0_eq_extend]
  have hone : ∀ {α : Type} [Fintype α] [DecidableEq α], incM F (1 : Matrix α α E) = 1 :=
    Matrix.map_one _ (map_zero _) (map_one _)
  let L : (Fin n → AE F E) →ₗ[AF F] Matrix (Fin n) (Fin d) (AE F E) :=
    { toFun := fun z => Matrix.vecMulVec z (incV F H'.x)
      map_add' := fun z z' => by ext i k; simp [Matrix.vecMulVec_apply, add_mul]
      map_smul' := fun t z => by ext i k; simp [Matrix.vecMulVec_apply] }
  let q : (Fin n → AE F E) →ₗ[AF F] (Fin n × Fin d → AF F) := LinearMap.snd (AF F) _ _ ∘ₗ co.e.toLinearMap ∘ₗ L
  have hq : ∀ z, q z = (co.e (Matrix.vecMulVec z (incV F H'.x))).2 := fun z => rfl
  have hqe : ∀ z, co.e (Matrix.vecMulVec z (incV F H'.x)) = (0, q z) := fun z => Prod.ext (hx z).1 rfl
  have hqs : ∀ η : Fin n × Fin d → AF F, (∀ k, η (j k) = 0) → ∃ z, q z = η := by
    intro η hη
    obtain ⟨Q, h1, h2, -⟩ := exists_frame_inv hH hW.lat
    let u := co.e.symm (0, η)
    let Y := u * (incM F Q)ᵀ
    have hu : u = Y.submatrix id .inl * (incM F H'.ι)ᵀ + Matrix.vecMulVec (fun i => Y i (.inr 0)) (incV F H'.x) +
        Matrix.vecMulVec (fun i => Y i (.inr 1)) (incV F H'.y) := by
      have : u = Y * (incM F (frame H'))ᵀ := by
        rw [Matrix.mul_assoc, ← Matrix.transpose_mul, ← incM_mul, h1, hone, Matrix.transpose_one, Matrix.mul_one]
      refine this.trans ?_
      ext i j
      simp [Matrix.mul_apply, Fintype.sum_sum_type, Fin.sum_univ_two, frame, incM, incV, Matrix.vecMulVec_apply, add_assoc]
    have h5 := congrArg Prod.snd (congrArg co.e hu)
    rw [map_add, map_add, LinearEquiv.apply_symm_apply] at h5
    simp only [Prod.snd_add, hlow, (hy _).1, add_zero] at h5
    have hz : (co₂.e (Y.submatrix id .inl)).2 = 0 := by
      funext k
      have := congrFun h5 (j k)
      rw [hη k] at this
      simp only [j, Pi.add_apply, planeZeroInsertion_apply_inl, (hx _).2 k, add_zero] at this
      exact this.symm
    refine ⟨fun i => Y i (.inr 0), ?_⟩
    rw [hq, h5, hz, ins0_zero, zero_add]
  have hqr : ∀ z : Fin n → E, ∃ y : Fin n × Fin d → F, q (incV F z) = fun k => algebraMap F (AF F) (y k) := fun z => by
    obtain ⟨y, z', hyz⟩ := hrat (Matrix.vecMulVec z H'.x)
    refine ⟨z', ?_⟩
    have : incM F (Matrix.vecMulVec z H'.x) = Matrix.vecMulVec (incV F z) (incV F H'.x) := by
      ext i k; simp [incM, incV, Matrix.vecMulVec_apply]
    rw [hq, ← this, hyz]
  refine ⟨⟨co₂, fun v => ev hd v (eV v (M.vac v)), 0, ∅⟩, evA F hd ∘ₗ U, c₀⁻¹, hrat₂, ⟨?_, ?_, ?_, ?_⟩, ?_⟩
  · intro Φ hΦ
    rw [LinearMap.comp_apply, hevA]
    exact GlobalTheory.RestrSchA.mem_schA_comp_extend F j hj _ (hmaps Φ hΦ)
  · intro z Φ hΦ
    rw [hone, Matrix.one_mul, LinearMap.comp_apply, hU _ Φ hΦ, hlow]
    funext y
    simp only [evA_apply, Darboux.rho, schr, LinearMap.comp_apply, ins0_dotProduct_ins0, ← ins0_add]
  · rintro u ⟨z, rfl⟩ Φ hΦ
    rw [LinearMap.comp_apply, hU _ Φ hΦ, hqe]
    funext y
    have h0 : ins0 hd y ⬝ᵥ q z = 0 := by
      rw [ins0_dotProduct, show (fun p => q z ((idx hd).symm (Sum.inl p))) = 0 from funext (hx z).2, dotProduct_zero]
    simp only [evA_apply, schr, LinearMap.comp_apply, h0, zero_dotProduct, mul_zero, add_zero,
      AddChar.map_zero_eq_one, one_mul]
  · refine ⟨(ei F hd).comp eI, fun v => ev hd v ∘ₗ eV v, ?_, fun v => ⟨rfl, ?_⟩, fun f φ hφ hφv => ?_⟩
    · intro h
      apply ei_ne_zero (F := F) (n := n) hd
      ext1 g
      obtain ⟨g', rfl⟩ := hsurj g
      exact congrArg (fun T : SInf F (Fin n × Fin d) →L[ℂ] SInf F (Fin n × Fin d₁) => T g') h
    · have he : ev (n := n) hd v = LinearMap.funLeft ℂ ℂ (fun y : Fin n × Fin d₁ → Fv F v => Function.extend j y 0) := by
        unfold ev
        congr 1
        funext y
        exact ins0_eq_extend hd y
      rw [Submodule.map_comp, hSB v, he]
      exact GlobalTheory.SchwartzBruhatRestrict.map_funLeft_extendZero F j hj v
    · rw [LinearMap.comp_apply, hpure f φ hφ (by
        filter_upwards [hφv, hM.std] with v h1 h2
        rw [h1, h2]; rfl), evA_pure]
      rfl
  · intro φ hφ
    have hT : c₀⁻¹ • U φ ∈ schA F (Fin n × Fin d) := Submodule.smul_mem _ _ (hmaps φ hφ)
    have h := GlobalTheory.ThK.RankRed.hasConstTerm_thetaSum_schr_lin F E B.ψ hψ _ _ j hj n q (fun z k => (hx z).2 k) hqs hqr _ hT
    convert h using 1
    · funext z
      have hm := GlobalTheory.HeisSchA.rho_mem_schA M B.ψ hψ (Matrix.vecMulVec z (incV F H'.x)) φ hφ
      have h1 := hth _ hm
      rw [hU _ φ hφ, hqe] at h1
      have h2 : schr B.ψ (0, q z) (c₀⁻¹ • U φ) = c₀⁻¹ • schr B.ψ (0, q z) (U φ) := by
        funext y
        simp only [schr, Pi.smul_apply, smul_eq_mul]
        ring
      rw [h2, GlobalTheory.WeilM.thetaSum_smul, h1, ← mul_assoc, inv_mul_cancel₀ hc₀, one_mul]
    · rw [← GlobalTheory.WeilM.thetaSum_smul, LinearMap.comp_apply, hevA]
      rfl

end Mixed

section Unip

open GlobalTheory.LeviModulus GlobalTheory.UnipMass GlobalTheory.LeviModulus.HCoord

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem det_compl {n d₂ : ℕ} {J : Matrix (Fin n) (Fin n) E} (hσ : ∀ x, σ (σ x) = x) (hJ : ∀ i j, σ (J j i) = J i j)
    (hdet : J.det ≠ 0) (H : Plane E n d₂)
    (hH : d₂ + 2 = n ∧ form σ J H.x H.x = 0 ∧ form σ J H.y H.y = 0 ∧ form σ J H.x H.y = 1 ∧
        (∀ u, form σ J (H.ι *ᵥ u) H.x = 0 ∧ form σ J (H.ι *ᵥ u) H.y = 0) ∧ Function.Injective H.ι.mulVec) :
    (H.ιᵀ * J * H.ι.map σ).det ≠ 0 := by
  intro h0
  obtain ⟨hn, hxx, hyy, hxy, horth, hinj⟩ := hH
  have hadd : ∀ a b w, form σ J (a + b) w = form σ J a w + form σ J b w := fun a b w => by
    simp only [form, add_dotProduct]
  have hsmul : ∀ (c : E) a w, form σ J (c • a) w = c * form σ J a w := fun c a w => by
    simp only [form, smul_dotProduct, smul_eq_mul]
  have hzero : ∀ w, form σ J 0 w = 0 := fun w => by simp only [form, zero_dotProduct]
  have hswap : ∀ a b, form σ J a b = σ (form σ J b a) := fun a b => by
    unfold form
    simp only [dotProduct, Matrix.mulVec, map_sum, map_mul, hσ, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [hJ]; ring
  have hyx : form σ J H.y H.x = 1 := by rw [hswap, hxy, map_one]
  let L : ((E × E) × (Fin d₂ → E)) →ₗ[E] (Fin n → E) :=
    { toFun := fun p => p.1.1 • H.x + H.ι *ᵥ p.2 + p.1.2 • H.y
      map_add' := fun p q => by
        simp only [Prod.fst_add, Prod.snd_add, Matrix.mulVec_add, add_smul]; abel
      map_smul' := fun c p => by
        simp only [Prod.smul_fst, Prod.smul_snd, Matrix.mulVec_smul, smul_eq_mul, mul_smul, RingHom.id_apply,
          smul_add] }
  have hinjL : Function.Injective L := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    rintro ⟨⟨s, t⟩, u⟩ hp
    have hp' : s • H.x + H.ι *ᵥ u + t • H.y = 0 := hp
    have h1 := congrArg (fun v => form σ J v H.y) hp'
    have h2 := congrArg (fun v => form σ J v H.x) hp'
    simp only [hadd, hsmul, hzero, hxy, hyy, (horth u).1, (horth u).2, hxx, hyx] at h1 h2
    have hs : s = 0 := by simpa using h1
    have ht : t = 0 := by simpa using h2
    subst hs ht
    have hu : H.ι *ᵥ u = H.ι *ᵥ 0 := by simpa using hp'
    have := hinj hu
    subst this
    rfl
  have hsurj : Function.Surjective L := by
    refine (LinearMap.injective_iff_surjective_of_finrank_eq_finrank ?_).1 hinjL
    simp only [Module.finrank_prod, Module.finrank_self, Module.finrank_fin_fun]
    omega
  obtain ⟨v, hv, hv0⟩ := Matrix.exists_vecMul_eq_zero_iff.2 h0
  have hιι : ∀ u, form σ J (H.ι *ᵥ v) (H.ι *ᵥ u) = 0 := fun u => by
    have hc : (fun i => σ ((H.ι *ᵥ u) i)) = H.ι.map σ *ᵥ fun i => σ (u i) := by
      funext i; exact RingHom.map_mulVec σ.toRingHom H.ι u i
    rw [form, hc, ← Matrix.vecMul_transpose, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec,
      Matrix.dotProduct_mulVec, hv0, zero_dotProduct]
  have hall : ∀ r, form σ J (H.ι *ᵥ v) r = 0 := fun r => by
    obtain ⟨⟨⟨s, t⟩, u⟩, rfl⟩ := hsurj r
    show form σ J _ (s • H.x + H.ι *ᵥ u + t • H.y) = 0
    rw [hswap, hadd, hadd, hsmul, hsmul, hswap H.x, hswap H.y, hswap (H.ι *ᵥ u), (horth v).1, (horth v).2, hιι]
    simp
  have hz : (H.ι *ᵥ v) ᵥ* J = 0 := by
    funext k
    have := hall (Pi.single k 1)
    have hb : (fun i => σ ((Pi.single k 1 : Fin n → E) i)) = Pi.single k 1 := by
      funext l; by_cases h : l = k
      · subst h; simp
      · simp [h]
    rw [form, hb, Matrix.dotProduct_mulVec, dotProduct_single_one] at this
    exact this
  by_cases hz' : H.ι *ᵥ v = 0
  · exact hv (hinj (by rw [hz', Matrix.mulVec_zero]))
  · exact hdet (Matrix.exists_vecMul_eq_zero_iff.1 ⟨_, hz', hz⟩)

theorem coord_facts {n d₂ : ℕ} (X : Spc F E n) (hσ : ∀ x, σ (σ x) = x) (hJ : ∀ i j, σ (X.J j i) = X.J i j)
    (H : Plane E n d₂) (hxx : form σ X.J H.x H.x = 0) (hxy : form σ X.J H.x H.y = 1)
    (horth : ∀ u, form σ X.J (H.ι *ᵥ u) H.x = 0 ∧ form σ X.J (H.ι *ᵥ u) H.y = 0)
    (J₁ : Matrix (Fin d₂) (Fin d₂) E) (hJ₁ : H.ιᵀ * X.J * H.ι.map σ = J₁) (hd : J₁.det ≠ 0)
    (vf : unip σ X H → (Fin d₂ → AE F E))
    (hvf : ∀ u, ∃ a : AE F E, mat u.1⁻¹ *ᵥ incV F H.y = incV F H.y + incM F H.ι *ᵥ vf u + a • incV F H.x) :
    (∀ u v, vf (u * v) = vf u + vf v) ∧ Continuous vf ∧ Function.Surjective vf ∧
      ∀ γ ∈ (ratU σ X.J).subgroupOf (unip σ X H), vf γ ∈ Set.range (incV F : (Fin d₂ → E) → Fin d₂ → AE F E) := by
  haveI := (topAE F E).1
  have hXX : hA σ X.J (incV F H.x) (incV F H.x) = 0 := by rw [hA_incV', hxx, map_zero]
  have hXY : hA σ X.J (incV F H.x) (incV F H.y) = 1 := by rw [hA_incV', hxy, map_one]
  have hYX : hA σ X.J (incV F H.y) (incV F H.x) = 1 := by rw [hA_herm σ X.J hσ hJ, hXY, map_one]
  have hιX : ∀ z, hA σ X.J (incM F H.ι *ᵥ z) (incV F H.x) = 0 := hA_ι_incV σ X.J H.ι H.x (fun u => (horth u).1)
  have hιY : ∀ z, hA σ X.J (incM F H.ι *ᵥ z) (incV F H.y) = 0 := hA_ι_incV σ X.J H.ι H.y (fun u => (horth u).2)
  have hXι : ∀ z, hA σ X.J (incV F H.x) (incM F H.ι *ᵥ z) = 0 := fun z => by
    rw [hA_herm σ X.J hσ hJ, hιX, map_zero]
  have hYι : ∀ z, hA σ X.J (incV F H.y) (incM F H.ι *ᵥ z) = 0 := fun z => by
    rw [hA_herm σ X.J hσ hJ, hιY, map_zero]
  have hιι : ∀ a w, hA σ X.J (incM F H.ι *ᵥ a) (incM F H.ι *ᵥ w) = hA σ J₁ a w := hA_ιι σ X.J J₁ H.ι hJ₁
  let A : Matrix (Fin n) (Fin n) (AE F E) → Fin d₂ → AE F E := fun M => Matrix.vecMul (rv σ X H M) (incM F J₁⁻¹)
  have hA' : ∀ (M : Matrix (Fin n) (Fin n) (AE F E)) (a : Fin d₂ → AE F E) (c : AE F E),
      M *ᵥ incV F H.y = incV F H.y + incM F H.ι *ᵥ a + c • incV F H.x → A M = a := by
    intro M a c h
    have e : rv σ X H M = Matrix.vecMul a (incM F J₁) := by
      funext j
      simp only [rv]
      rw [h, add_assoc, add_sub_cancel_left, hA_add_l, hA_smul_l, hXι, mul_zero, add_zero, hιι, hA_single]
    simp only [A]; rw [e, Matrix.vecMul_vecMul, incM_mul_inv _ hd, Matrix.vecMul_one]
  have hvA : ∀ u, vf u = A (mat u.1⁻¹) := fun u => by
    obtain ⟨a, ha⟩ := hvf u
    exact (hA' _ _ _ ha).symm
  refine ⟨fun u v => ?_, ?_, fun z => ?_, fun γ hγ => ?_⟩
  · obtain ⟨a, ha⟩ := hvf u
    obtain ⟨b, hb⟩ := hvf v
    obtain ⟨h1, h2⟩ := mem_unip_gen σ X H v.1⁻¹ ((unip σ X H).inv_mem v.2)
    obtain ⟨c, hc⟩ := h2 (vf u)
    rw [hvA]
    refine hA' _ _ (a + b + c) ?_
    have hm : mat (u * v).1⁻¹ = mat v.1⁻¹ * mat u.1⁻¹ := by
      rw [Subgroup.coe_mul, mul_inv_rev]; rfl
    rw [hm, ← Matrix.mulVec_mulVec, ha, Matrix.mulVec_add, Matrix.mulVec_add, Matrix.mulVec_smul, hb, hc, h1,
      Matrix.mulVec_add, add_smul, add_smul]
    abel
  · have hmc : Continuous fun g : unip σ X H => mat (g : UA σ X.J)⁻¹ :=
      Units.continuous_coe_inv.comp (continuous_subtype_val.comp continuous_subtype_val)
    have hAc : Continuous A := continuous_rv.matrix_vecMul continuous_const
    rw [show vf = fun u => A (mat u.1⁻¹) from funext hvA]
    exact hAc.comp hmc
  · have hself : ∀ v, cA σ (hA σ X.J v v) = hA σ X.J v v := fun v => (hA_herm σ X.J hσ hJ v v).symm
    set half : AE F E := inclR (F := F) (AF F) (2⁻¹ : E) with hhalf_def
    have hhalf : (2 : AE F E) * half = 1 := by
      rw [hhalf_def, ← map_ofNat (inclR (F := F) (AF F)) 2, ← map_mul, mul_inv_cancel₀ two_ne_zero, map_one]
    have hσhalf : cA σ half = half := by rw [hhalf_def, cA_inclR', map_inv₀, map_ofNat]
    have hcf : (-(half * hA σ X.J (incM F H.ι *ᵥ z) (incM F H.ι *ᵥ z))) +
        cA σ (-(half * hA σ X.J (incM F H.ι *ᵥ z) (incM F H.ι *ᵥ z))) =
        -hA σ X.J (incM F H.ι *ᵥ z) (incM F H.ι *ᵥ z) := by
      rw [map_neg, map_mul, hσhalf, hself]
      linear_combination (-hA σ X.J (incM F H.ι *ᵥ z) (incM F H.ι *ᵥ z)) * hhalf
    refine ⟨(elt hσ hJ hXX hιX z _ hcf)⁻¹, ?_⟩
    rw [hvA, Subgroup.coe_inv, inv_inv, mat_elt]
    refine hA' _ _ (-(half * hA σ X.J (incM F H.ι *ᵥ z) (incM F H.ι *ᵥ z))) ?_
    rw [hmat_mulVec, hYX, hYι, one_smul, zero_smul, sub_zero, add_assoc]
  · have hγ' : γ.1⁻¹ ∈ ratU σ X.J := (ratU σ X.J).inv_mem (Subgroup.mem_subgroupOf.1 hγ)
    obtain ⟨g, hg⟩ := Subgroup.mem_subgroupOf.1 hγ'
    have hm : mat γ.1⁻¹ = incM F g.1 := by
      unfold mat
      rw [← hg]; rfl
    refine ⟨Matrix.vecMul (fun j => form σ X.J (g.1 *ᵥ H.y - H.y) (H.ι *ᵥ Pi.single j 1)) J₁⁻¹, ?_⟩
    rw [hvA, hm]
    have e : rv σ X H (incM F g.1) = incV F (fun j => form σ X.J (g.1 *ᵥ H.y - H.y) (H.ι *ᵥ Pi.single j 1)) := by
      funext j
      have e1 : (Pi.single j 1 : Fin d₂ → AE F E) = incV F (Pi.single j (1 : E)) := by
        funext k; simp [incV, Pi.single_apply]
      have e2 : incV F (g.1 *ᵥ H.y) - incV F H.y = incV F (g.1 *ᵥ H.y - H.y) := by
        funext k; simp [incV]
      simp only [rv]
      rw [e1, incM_mulVec_incV', incM_mulVec_incV', e2, hA_incV']
      rfl
    simp only [A]
    rw [e]
    funext k
    simp [incV, incM, Matrix.vecMul, dotProduct, map_sum, map_mul]

end Unip

theorem mean_theta_eq : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
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
    ∃ (M₂ : Model σ V₁ W₁) (e₂ : Fn F d₂ d →ₗ[ℂ] Fn F d₂ d₁) (C : ℂ),
      (∀ x : Matrix (Fin d₂) (Fin d₁) E, ∃ y z : Fin d₂ × Fin d₁ → F,
        M₂.co.e (incM F x) = (fun i => algebraMap F (AF F) (y i), fun i => algebraMap F (AF F) (z i))) ∧
      IsEv B M₁ M₂ 1 H'.ι (iso0 d₂ H') e₂ ∧
      ∀ φ ∈ schA F (Fin d₂ × Fin d),
        ∫ u in 𝓕, thetaSum F (M₁.co.rho B.ψ (Matrix.vecMulVec (vf u) (incV F H'.x)) φ) ∂μ = C * thetaSum F (e₂ φ) := by
  intro _ F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hP d₁ W₁ H' i₀ i₁ hH' d₂ H hH V₁ M₁ e hV₁ hM₁ _ μ 𝓕 hμ h𝓕 h1 vf hvf
  have hσ : ∀ z, σ (σ z) = z := fun z => by
    have hcm : IsCMExt F E σ := hP.base.cm
    obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
    exact τ.injective (by rw [hcm.2.2.2, hcm.2.2.2, star_star])
  have hdet : V₁.J.det ≠ 0 := by
    rw [hV₁]
    exact det_compl hσ hP.herm.herm (GlobalTheory.LeviModulus.HCoord.det_ne_of_sig_c B X.J hP.herm.sig) H hH
  have hherm : ∀ i j, σ (V₁.J j i) = V₁.J i j := fun i j => by
    rw [hV₁]
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, map_sum, map_mul, hσ, hP.herm.herm,
      Finset.sum_mul]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
  obtain ⟨M₂, e₂, C, hrat, hev, hC⟩ := exists_mixed σ B V₁ W W₁ H' hP.base hherm hdet hP.skew hH' M₁ hM₁
  obtain ⟨hadd, hcont, hsurj, hΛ⟩ :=
    coord_facts X hσ hP.herm.herm H hH.2.1 hH.2.2.2.1 hH.2.2.2.2.1 V₁.J hV₁.symm hdet vf hvf
  refine ⟨M₂, e₂, C, hrat, hev, fun φ hφ => ?_⟩
  obtain ⟨i1, i2, i3, i4⟩ := GlobalTheory.UnipCT.topFacts (F := F) σ X.J
  haveI : BorelSpace (UA σ X.J) := ⟨rfl⟩
  haveI : LocallyCompactSpace (unip σ X H) :=
    (GlobalTheory.UnipCT.isClosed_unip σ X H).isClosedEmbedding_subtypeVal.locallyCompactSpace
  haveI := GlobalTheory.UnipCT.countable_ratU (σ := σ) X.J
  haveI : Countable ((ratU σ X.J).subgroupOf (unip σ X H)) :=
    Function.Injective.countable (f := fun g : (ratU σ X.J).subgroupOf (unip σ X H) => (⟨g.1.1, g.2⟩ : ratU σ X.J))
      fun g h hgh => by
        apply Subtype.ext; apply Subtype.ext
        simpa using congrArg Subtype.val hgh
  exact mean_constTerm _ μ 𝓕 hμ h𝓕 h1 _ vf _ _ hadd hcont hsurj hΛ (hC φ hφ)

end GlobalTheory.UnipThetaMean
