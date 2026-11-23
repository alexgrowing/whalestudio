import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AveragedIntegralFunctional
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianAdaptedPlaneSeesaw

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

noncomputable section
namespace GlobalTheory.DblSiegelInv

section Alg

variable {R S : Type} [CommRing R] [CommRing S] [Algebra R S] {c : S →ₐ[R] S}
  {α β : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]

theorem mul_diagCols_transpose_eq_fromCols (A : Matrix α β S) :
    A * (diagCols β : Matrix (β ⊕ β) β S)ᵀ = Matrix.fromCols A A := by
  rw [diagCols, Matrix.transpose_fromRows, Matrix.mul_fromCols, Matrix.transpose_one, Matrix.mul_one]

theorem vmv_diag {n : Type} (v : n → S) (a : β → S) :
    Matrix.vecMulVec v a * (diagCols β : Matrix (β ⊕ β) β S)ᵀ = Matrix.vecMulVec v ((diagCols β : Matrix (β ⊕ β) β S) *ᵥ a) := by
  ext i j
  simp only [Matrix.mul_apply, Matrix.vecMulVec_apply, Matrix.transpose_apply, Matrix.mulVec, dotProduct, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  ring

variable {ξ : S} {JA : Matrix α α S} {JB : Matrix β β S} {κ : Type} [Fintype κ]

theorem iso_diag {d : Darboux (symp (R := R) c ξ JA JB) κ} {dd : Darboux (symp (R := R) c ξ JA (dbl JB)) (κ ⊕ κ)}
    (hdd : IsDblCoord c ξ JA JB d dd) (A A' : Matrix α β S) :
    (dd.e (A * (diagCols β : Matrix (β ⊕ β) β S)ᵀ)).1 ⬝ᵥ (dd.e (A' * (diagCols β : Matrix (β ⊕ β) β S)ᵀ)).2 =
      (dd.e (A' * (diagCols β : Matrix (β ⊕ β) β S)ᵀ)).1 ⬝ᵥ (dd.e (A * (diagCols β : Matrix (β ⊕ β) β S)ᵀ)).2 := by
  rw [mul_diagCols_transpose_eq_fromCols, mul_diagCols_transpose_eq_fromCols, hdd, hdd]
  simp [dotProduct, Fintype.sum_sum_type]

theorem rho_add_diag [Invertible (2 : R)] {d : Darboux (symp (R := R) c ξ JA JB) κ}
    {dd : Darboux (symp (R := R) c ξ JA (dbl JB)) (κ ⊕ κ)}
    (hdd : IsDblCoord c ξ JA JB d dd) (ψ : AddChar R ℂ) (A A' : Matrix α β S) (φ : (κ ⊕ κ → R) → ℂ) :
    dd.rho ψ (A * (diagCols β : Matrix (β ⊕ β) β S)ᵀ + A' * (diagCols β : Matrix (β ⊕ β) β S)ᵀ) φ =
      dd.rho ψ (A * (diagCols β : Matrix (β ⊕ β) β S)ᵀ) (dd.rho ψ (A' * (diagCols β : Matrix (β ⊕ β) β S)ᵀ) φ) := by
  simp only [Darboux.rho, map_add]
  exact GlobalTheory.MixXEvUniq.schr_add ψ _ _ (iso_diag hdd A A') φ

end Alg

section Plane

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

def pm {n n₁ : ℕ} (H : Plane E n n₁) : Matrix (Fin n) (Unit ⊕ (Fin n₁ ⊕ Unit)) E :=
  Matrix.of fun i k => Sum.elim (fun _ => H.x i) (Sum.elim (fun j => H.ι i j) (fun _ => H.y i)) k

theorem pm_mulVec {n n₁ : ℕ} (H : Plane E n n₁) (c : Unit ⊕ (Fin n₁ ⊕ Unit) → E) :
    pm H *ᵥ c = c (Sum.inl ()) • H.x + H.ι *ᵥ (fun j => c (Sum.inr (Sum.inl j))) + c (Sum.inr (Sum.inr ())) • H.y := by
  funext i
  simp [pm, Matrix.mulVec, dotProduct, Fintype.sum_sum_type, mul_comm] <;> ring

theorem sigma_sigma (hcm : IsCMExt F E σ) (a : E) : σ (σ a) = a := by
  obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
  apply τ.injective
  rw [hcm.2.2.2, hcm.2.2.2, star_star]

theorem form_swap {n : ℕ} (hcm : IsCMExt F E σ) {J : Matrix (Fin n) (Fin n) E} (hJ : ∀ i j, σ (J j i) = J i j)
    (x y : Fin n → E) : form σ J y x = σ (form σ J x y) := by
  simp only [form, dotProduct, Matrix.mulVec, map_sum, map_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [sigma_sigma hcm, hJ j i]
  ring

theorem pm_inj (B : Base F E) (hcm : IsCMExt F E σ) {n n₁ d : ℕ} {X : Spc F E n} {X₁ : Spc F E n₁} {W : Spc F E d}
    (hJ : ∀ i j, σ (X.J j i) = X.J i j) (M : Model σ X W) (M₁ : Model σ X₁ W) (H : Plane E n n₁) {j₀ j₁ : ℕ}
    (hH : H.IsAdapted σ B X X₁ j₀ j₁) (hd : 0 < d) : Function.Injective (pm H).mulVecLin := by
  rw [injective_iff_map_eq_zero]
  intro c hc
  rw [Matrix.mulVecLin_apply, pm_mulVec] at hc
  have hb : c (Sum.inr (Sum.inr ())) = 0 := by
    have h1 := congrArg (fun v => form σ X.J v H.x) hc
    simp only [form, add_dotProduct, smul_dotProduct, zero_dotProduct] at h1
    have hxx : H.x ⬝ᵥ X.J *ᵥ (fun i => σ (H.x i)) = 0 := hH.xx
    have hix : (H.ι *ᵥ (fun j => c (Sum.inr (Sum.inl j)))) ⬝ᵥ X.J *ᵥ (fun i => σ (H.x i)) = 0 :=
      (hH.orth _).1
    have hyx : H.y ⬝ᵥ X.J *ᵥ (fun i => σ (H.x i)) = 1 := by
      have := form_swap hcm hJ H.x H.y
      rw [hH.xy, map_one] at this
      exact this
    rw [hxx, hix, hyx] at h1
    simpa using h1
  have h2 : Matrix.vecMulVec H.x (fun _ : Fin d => c (Sum.inl ())) +
      H.ι * Matrix.vecMulVec (fun j => c (Sum.inr (Sum.inl j))) (fun _ : Fin d => (1 : E)) = 0 := by
    ext i l
    have := congrFun hc i
    simp only [hb, zero_smul, add_zero, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at this
    simp only [Matrix.add_apply, Matrix.vecMulVec_apply, Matrix.mul_apply, mul_one, Matrix.zero_apply]
    rw [← this]
    simp [Matrix.mulVec, dotProduct, mul_comm]
  obtain ⟨h3, h4⟩ := GlobalTheory.MixXEvUniq.direct B M M₁ H hH _ _ h2
  funext k
  rcases k with ⟨⟩ | ⟨j⟩ | ⟨⟩
  · simpa using congrFun h3 ⟨0, hd⟩
  · simpa [Matrix.vecMulVec_apply] using congrFun (congrFun h4 j) ⟨0, hd⟩
  · exact hb

theorem decomp {n n₁ d : ℕ} (H : Plane E n n₁) (hinj : Function.Injective (pm H).mulVecLin) (hrank : n = n₁ + 2)
    (z : Matrix (Fin n) (Fin d) (AE F E)) :
    ∃ (a b : Fin d → AE F E) (m : Matrix (Fin n₁) (Fin d) (AE F E)),
      z = Matrix.vecMulVec (incV F H.x) a + incM F H.ι * m + Matrix.vecMulVec (incV F H.y) b := by
  have hsurj : Function.Surjective (pm H).mulVecLin := by
    refine (LinearMap.injective_iff_surjective_of_finrank_eq_finrank ?_).1 hinj
    simp only [Module.finrank_fintype_fun_eq_card, Fintype.card_sum, Fintype.card_unit, Fintype.card_fin, hrank]
    ring
  choose q hq using fun i : Fin n => hsurj (Pi.single i 1)
  have hPQ : pm H * Matrix.of (fun k i => q i k) = 1 := by
    ext i i'
    have := congrFun (hq i') i
    simp only [Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct] at this
    rw [Matrix.mul_apply, Matrix.one_apply]
    simp only [Matrix.of_apply]
    rw [this, Pi.single_apply]
  have hz : z = incM F (pm H) * (incM F (Matrix.of (fun k i => q i k)) * z) := by
    rw [← Matrix.mul_assoc, ← GlobalTheory.MixXEvUniq.incM_mul, hPQ, incM, Matrix.map_one _ (map_zero _) (map_one _), Matrix.one_mul]
  refine ⟨(incM F (Matrix.of (fun k i => q i k)) * z) (Sum.inl ()),
    (incM F (Matrix.of (fun k i => q i k)) * z) (Sum.inr (Sum.inr ())),
    Matrix.of fun j l => (incM F (Matrix.of (fun k i => q i k)) * z) (Sum.inr (Sum.inl j)) l, ?_⟩
  conv_lhs => rw [hz]
  ext i l
  simp [pm, incM, incV, Matrix.mul_apply, Fintype.sum_sum_type, Matrix.vecMulVec_apply, mul_comm] <;> ring

end Plane

theorem main : GlobalTheory.FunPr.Hypotheses₂ → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d)
    (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ), IsPair B M χX χW om r s r' s' →
    ∀ (n₁ : ℕ) (X₁ : Spc F E n₁) (H : Plane E n n₁) (j₀ j₁ : ℕ) (M₁ : Model σ X₁ W) (om₁ : Rep σ X₁ W) (r₁ s₁ : ℕ),
      H.IsAdapted σ B X X₁ j₀ j₁ → IsPair B M₁ χX χW om₁ r₁ s₁ r' s' →
      ∀ e, IsEv B M M₁ H.ι 1 {u | ∃ z, u = Matrix.vecMulVec (incV F H.x) z} e →
      (∃ Φ ∈ schA F (Fin n × Fin d), e Φ ≠ 0) →
      ∀ (dd : Darboux (symp (cA σ) (-1) (incM F X.J) (dbl (incM F W.J))) (Fin n × Fin d ⊕ Fin n × Fin d))
        (dd₁ : Darboux (symp (cA σ) (-1) (incM F X₁.J) (dbl (incM F W.J))) (Fin n₁ × Fin d ⊕ Fin n₁ × Fin d)),
      IsDblCoord (cA σ) (-1) (incM F X.J) (incM F W.J) M.co dd → IsDblCoord (cA σ) (-1) (incM F X₁.J) (incM F W.J) M₁.co dd₁ →
      ∀ ed : ((Fin n × Fin d ⊕ Fin n × Fin d → AF F) → ℂ) →ₗ[ℂ] ((Fin n₁ × Fin d ⊕ Fin n₁ × Fin d → AF F) → ℂ),
        (∀ Φ ∈ schA F (Fin n × Fin d ⊕ Fin n × Fin d), ed Φ ∈ schA F (Fin n₁ × Fin d ⊕ Fin n₁ × Fin d)) →
        (∀ (z : Matrix (Fin n₁) (Fin d ⊕ Fin d) (AE F E)), ∀ Φ ∈ schA F (Fin n × Fin d ⊕ Fin n × Fin d), ed (dd.rho B.ψ (incM F H.ι * z) Φ) = dd₁.rho B.ψ z (ed Φ)) →
        (∀ z : Fin d ⊕ Fin d → AE F E, ∀ Φ ∈ schA F (Fin n × Fin d ⊕ Fin n × Fin d), ed (dd.rho B.ψ (Matrix.vecMulVec (incV F H.x) z) Φ) = ed Φ) →
        (∀ l ∈ (adeleClass F).adm (Fin n₁ × Fin d ⊕ Fin n₁ × Fin d), l ∘ₗ ed ∈ (adeleClass F).adm (Fin n × Fin d ⊕ Fin n × Fin d)) →
        (∃ Φ ∈ schA F (Fin n × Fin d ⊕ Fin n × Fin d), ed Φ ≠ 0) →
      ∀ l₁ : ((Fin n₁ × Fin d ⊕ Fin n₁ × Fin d → AF F) → ℂ) →ₗ[ℂ] ℂ,
        (∀ (z : Matrix (Fin n₁) (Fin d) (AE F E)), ∀ φ ∈ schA F (Fin n₁ × Fin d ⊕ Fin n₁ × Fin d), l₁ (dd₁.rho B.ψ (z * (diagCols (Fin d))ᵀ) φ) = l₁ φ) →
      ∀ μ : @Measure (Fin d → AE F E) (borel _), @Measure.IsAddHaarMeasure _ _ _ (borel _) μ →
        (∀ Φ ∈ schA F (Fin n × Fin d ⊕ Fin n × Fin d), Integrable (GlobalTheory.DblSiegelX.avgFun dd B.ψ (GlobalTheory.DblSiegelX.zs H) (l₁ ∘ₗ ed) Φ) μ) →
        ∀ (z : Matrix (Fin n) (Fin d) (AE F E)), ∀ Φ ∈ schA F (Fin n × Fin d ⊕ Fin n × Fin d),
          GlobalTheory.DblSiegelX.avgL dd B.ψ (GlobalTheory.DblSiegelX.zs H) (l₁ ∘ₗ ed) μ (dd.rho B.ψ (z * (diagCols (Fin d))ᵀ) Φ) =
            GlobalTheory.DblSiegelX.avgL dd B.ψ (GlobalTheory.DblSiegelX.zs H) (l₁ ∘ₗ ed) μ Φ := by
  intro _ F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hP n₁ X₁ H j₀ j₁ M₁ om₁ r₁ s₁ hH hP₁ e he he0 dd dd₁ hdd hdd₁
    ed hedS hedH hedI hedA hed0 l₁ hl₁ μ hμ hint z Φ hΦ
  have hψ : IsStd B.ψ := hP.base.std
  have hS : ∀ w, ∀ Ψ ∈ schA F (Fin n × Fin d ⊕ Fin n × Fin d), dd.rho B.ψ w Ψ ∈ schA F (Fin n × Fin d ⊕ Fin n × Fin d) :=
    fun w Ψ h => GlobalTheory.HeisSchA.schr_mem_schA B.ψ hψ (dd.e w) Ψ h
  rcases Nat.eq_zero_or_pos d with hd | hd
  · subst hd
    have h0 : z * (diagCols (Fin 0) : Matrix (Fin 0 ⊕ Fin 0) (Fin 0) (AE F E))ᵀ = 0 := by
      ext i j; rcases j with j | j <;> exact j.elim0
    have h1 : dd.rho B.ψ (z * (diagCols (Fin 0) : Matrix (Fin 0 ⊕ Fin 0) (Fin 0) (AE F E))ᵀ) Φ = Φ := by
      rw [h0]; funext x; simp [Darboux.rho, schr]
    exact congrArg (GlobalTheory.DblSiegelX.avgL dd B.ψ (GlobalTheory.DblSiegelX.zs H) (l₁ ∘ₗ ed) μ) h1
  · obtain ⟨a, b, m, rfl⟩ := decomp H (pm_inj B hP.base.cm hP.herm.herm M M₁ H hH hd) hH.rank z
    have key : ∀ u, GlobalTheory.DblSiegelX.avgFun dd B.ψ (GlobalTheory.DblSiegelX.zs H) (l₁ ∘ₗ ed)
        (dd.rho B.ψ ((Matrix.vecMulVec (incV F H.x) a + incM F H.ι * m + Matrix.vecMulVec (incV F H.y) b) *
          (diagCols (Fin d) : Matrix (Fin d ⊕ Fin d) (Fin d) (AE F E))ᵀ) Φ) u =
        GlobalTheory.DblSiegelX.avgFun dd B.ψ (GlobalTheory.DblSiegelX.zs H) (l₁ ∘ₗ ed) Φ (b + u) := by
      intro u
      simp only [GlobalTheory.DblSiegelX.avgFun, LinearMap.comp_apply, GlobalTheory.DblSiegelX.zs, ← vmv_diag]
      have hv : Matrix.vecMulVec (incV F H.y) (b + u) =
          Matrix.vecMulVec (incV F H.y) b + Matrix.vecMulVec (incV F H.y) u := by
        ext i j; simp [Matrix.vecMulVec_apply, mul_add]
      have hsum : Matrix.vecMulVec (incV F H.y) u * (diagCols (Fin d) : Matrix (Fin d ⊕ Fin d) (Fin d) (AE F E))ᵀ +
          (Matrix.vecMulVec (incV F H.x) a + incM F H.ι * m + Matrix.vecMulVec (incV F H.y) b) *
            (diagCols (Fin d) : Matrix (Fin d ⊕ Fin d) (Fin d) (AE F E))ᵀ =
          Matrix.vecMulVec (incV F H.x) a * (diagCols (Fin d) : Matrix (Fin d ⊕ Fin d) (Fin d) (AE F E))ᵀ +
          (incM F H.ι * m + Matrix.vecMulVec (incV F H.y) (b + u)) *
            (diagCols (Fin d) : Matrix (Fin d ⊕ Fin d) (Fin d) (AE F E))ᵀ := by
        rw [hv]; simp only [Matrix.add_mul]; abel
      rw [← rho_add_diag hdd, hsum, rho_add_diag hdd, Matrix.add_mul, rho_add_diag hdd, vmv_diag (incV F H.x) a,
        hedI _ _ (hS _ _ (hS _ _ hΦ)), Matrix.mul_assoc, hedH _ _ (hS _ _ hΦ)]
      exact hl₁ m _ (hedS _ (hS _ _ hΦ))
    letI : MeasurableSpace (Fin d → AE F E) := borel _
    haveI : BorelSpace (Fin d → AE F E) := ⟨rfl⟩
    haveI := hμ
    rw [GlobalTheory.DblSiegelX.avgL_apply _ _ _ _ _ _ (hint _ (hS _ _ hΦ)), GlobalTheory.DblSiegelX.avgL_apply _ _ _ _ _ _ (hint _ hΦ)]
    refine (integral_congr_ae (Filter.Eventually.of_forall key)).trans ?_
    exact integral_add_left_eq_self _ b

end GlobalTheory.DblSiegelInv
