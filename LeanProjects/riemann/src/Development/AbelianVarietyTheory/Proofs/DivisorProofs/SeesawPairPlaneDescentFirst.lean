import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilRepresentationPreservesSchwartz
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SkewAdaptedPlanePairConverse
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EigenIntertwinerGoodModelsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EigenIntertwinerExtensionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicStoneVonNeumannLagrangianUniquenessStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianAdaptedPairConverse
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnitaryScalingVector
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HyperbolicPlaneDecompositionOfPairStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HyperbolicPlaneConditionsHermitianStatement

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

noncomputable section

namespace GlobalTheory.MixXUnipPlain

theorem twist_plain : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d)
    (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ), IsPair B M χX χW om r s r' s' →
    ∀ (d₂ : ℕ) (H : Plane E n d₂), (∀ u, form σ X.J (H.ι *ᵥ u) H.x = 0 ∧ form σ X.J (H.ι *ᵥ u) H.y = 0) →
    ∀ (V₁ : Spc F E d₂) (M₁ : Model σ V₁ W) (e : Fn F n d →ₗ[ℂ] Fn F d₂ d), IsEv B M M₁ H.ι 1 {u | ∃ z, u = Matrix.vecMulVec (incV F H.x) z} e →
      ∀ (g : UA σ X.J) (a : AE F E), mat g *ᵥ incV F H.x = a • incV F H.x →
      (∀ z : Fin d₂ → AE F E, ∃ b : AE F E, mat g *ᵥ (incM F H.ι *ᵥ z) = incM F H.ι *ᵥ z + b • incV F H.x) →
      (∀ z, ∀ Φ ∈ schA F (Fin n × Fin d), e (om (g, 1) (M.co.rho B.ψ (incM F H.ι * z * (incM F (1 : Matrix (Fin d) (Fin d) E))ᵀ) Φ)) =
        M₁.co.rho B.ψ z (e (om (g, 1) Φ))) ∧
      ∀ u ∈ {u | ∃ z, u = Matrix.vecMulVec (incV F H.x) z}, ∀ Φ ∈ schA F (Fin n × Fin d), e (om (g, 1) (M.co.rho B.ψ u Φ)) = e (om (g, 1) Φ) := by
  intro F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hP n₁ H horth X₁ M₁ e he g a hx hι
  have hs := IsUWeilPair.isUSplitting hP.weil
  have hstd : IsStd B.ψ := hP.base.std
  have hc : ∀ t : E, cA σ (inclR (F := F) (AF F) t) = inclR (F := F) (AF F) (σ t) := fun t => rfl
  have h1 : incM F (1 : Matrix (Fin d) (Fin d) E) = 1 := by simp [incM]
  have hact : ∀ w, actAB (cA σ) ((g, 1) : UA σ X.J × UA σ W.J) w = mat g * w := by
    intro w; simp [actAB, mat]
  have hcomp : ∀ w w' Φ, symp (cA σ) (-1) (incM F X.J) (incM F W.J) w w' = 0 →
      M.co.rho B.ψ w (M.co.rho B.ψ w' Φ) = M.co.rho B.ψ (w + w') Φ := by
    intro w w' Φ h0
    simp only [Darboux.rho]
    have hlaw : ∀ (v v' : (Fin n × Fin d → AF F) × (Fin n × Fin d → AF F)) (φ : (Fin n × Fin d → AF F) → ℂ),
        schr B.ψ v (schr B.ψ v' φ) = B.ψ (⅟(2 : AF F) * (v.1 ⬝ᵥ v'.2 - v'.1 ⬝ᵥ v.2)) • schr B.ψ (v + v') φ := by
      intro v v' φ
      funext x
      simp only [schr, Pi.smul_apply, smul_eq_mul, ← mul_assoc, ← AddChar.map_add_eq_mul, Prod.fst_add, Prod.snd_add,
        add_assoc, add_dotProduct, dotProduct_add]
      congr 2
      linear_combination (-(v.1 ⬝ᵥ v'.2)) * invOf_mul_self (2 : AF F)
    rw [hlaw, ← M.co.form, h0, mul_zero, AddChar.map_zero_eq_one, one_smul, ← map_add]
  have hcol : ∀ m, ∑ i, ∑ k, H.ι i m * (X.J i k * σ (H.x k)) = 0 := by
    intro m
    have h := (horth (Pi.single m 1)).1
    simp only [form, Matrix.mulVec_single_one, dotProduct, Matrix.mulVec] at h
    simpa [Finset.mul_sum, Pi.single_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.sum_mul] using h
  have hperp : ∀ (z : Matrix (Fin n₁) (Fin d) (AE F E)) (q : Fin d → AE F E),
      symp (cA σ) (-1) (incM F X.J) (incM F W.J) (incM F H.ι * z) (Matrix.vecMulVec (incV F H.x) q) = 0 := by
    intro z q
    have hinner : ∀ j, ∑ i, ∑ k, (incM F H.ι * z) i j * incM F X.J i k * cA σ (incV F H.x k) = 0 := by
      intro j
      have e1 : ∀ i k, (incM F H.ι * z) i j * incM F X.J i k * cA σ (incV F H.x k) =
          ∑ m, z m j * inclR (F := F) (AF F) (H.ι i m * (X.J i k * σ (H.x k))) := by
        intro i k
        rw [Matrix.mul_apply, Finset.sum_mul, Finset.sum_mul]
        refine Finset.sum_congr rfl fun m _ => ?_
        simp only [incM, incV, Matrix.map_apply, hc, map_mul]
        ring
      simp_rw [e1]
      calc _ = ∑ i, ∑ m, ∑ k, z m j * inclR (F := F) (AF F) (H.ι i m * (X.J i k * σ (H.x k))) :=
            Finset.sum_congr rfl fun i _ => Finset.sum_comm
        _ = ∑ m, ∑ i, ∑ k, z m j * inclR (F := F) (AF F) (H.ι i m * (X.J i k * σ (H.x k))) := Finset.sum_comm
        _ = ∑ m, z m j * inclR (F := F) (AF F) (∑ i, ∑ k, H.ι i m * (X.J i k * σ (H.x k))) := by
            simp [map_sum, Finset.mul_sum]
        _ = 0 := Finset.sum_eq_zero fun m _ => by rw [hcol m, map_zero, mul_zero]
    have hT : hTens (cA σ) (incM F X.J) (incM F W.J) (incM F H.ι * z) (Matrix.vecMulVec (incV F H.x) q) = 0 := by
      unfold hTens
      rw [Finset.sum_comm]
      refine Finset.sum_eq_zero fun j _ => ?_
      have e2 : ∀ i k, ∑ l, (incM F H.ι * z) i j * incM F X.J i k * incM F W.J j l *
          cA σ (Matrix.vecMulVec (incV F H.x) q k l) =
          ((incM F H.ι * z) i j * incM F X.J i k * cA σ (incV F H.x k)) * ∑ l, incM F W.J j l * cA σ (q l) := by
        intro i k
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun l _ => ?_
        simp only [Matrix.vecMulVec_apply, map_mul]
        ring
      simp_rw [e2, ← Finset.sum_mul, hinner j, zero_mul]
    simp [symp, hT]
  choose β hβ using fun j : Fin n₁ => hι (Pi.single j 1)
  have hgι : mat g * incM F H.ι = incM F H.ι + Matrix.vecMulVec (incV F H.x) β := by
    ext i j
    have h := congrFun (hβ j) i
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_single_one, Matrix.mulVec_single_one] at h
    simpa [Matrix.vecMulVec_apply, mul_comm] using h
  refine ⟨fun z Φ hΦ => ?_, fun u hu Φ hΦ => ?_⟩
  · have hΨ := hs.pres (g, 1) Φ hΦ
    rw [hs.impl (g, 1) _ Φ hΦ, hact]
    have hw : mat g * (incM F H.ι * z * (incM F (1 : Matrix (Fin d) (Fin d) E))ᵀ) =
        incM F H.ι * z + Matrix.vecMulVec (incV F H.x) (β ᵥ* z) := by
      rw [h1, Matrix.transpose_one, Matrix.mul_one, ← Matrix.mul_assoc, hgι, Matrix.add_mul]
      congr 1
      ext i j
      simp [Matrix.vecMulVec_apply, Matrix.mul_apply, Matrix.vecMul, dotProduct, Finset.mul_sum, mul_assoc]
    have hh := he.Heisenberg₂ z _ (GlobalTheory.HeisSchA.rho_mem_schA M B.ψ hstd (Matrix.vecMulVec (incV F H.x) (β ᵥ* z)) _ hΨ)
    rw [h1, Matrix.transpose_one, Matrix.mul_one] at hh
    rw [hw, ← hcomp _ _ _ (hperp z _), hh, he.inv _ ⟨_, rfl⟩ _ hΨ]
  · obtain ⟨q, rfl⟩ := hu
    have hΨ := hs.pres (g, 1) Φ hΦ
    rw [hs.impl (g, 1) _ Φ hΦ, hact, Matrix.mul_vecMulVec, hx]
    refine he.inv _ ⟨a • q, ?_⟩ _ hΨ
    ext i j
    simp [Matrix.vecMulVec_apply]
    ring

theorem uniq_plain : GlobalTheory.FunPr.Hypotheses₂ → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d)
    (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ), IsPair B M χX χW om r s r' s' →
    ∀ (d₂ : ℕ) (H : Plane E n d₂), (d₂ + 2 = n ∧ form σ X.J H.x H.x = 0 ∧ form σ X.J H.y H.y = 0 ∧ form σ X.J H.x H.y = 1 ∧
        (∀ u, form σ X.J (H.ι *ᵥ u) H.x = 0 ∧ form σ X.J (H.ι *ᵥ u) H.y = 0) ∧ Function.Injective H.ι.mulVec) →
    ∀ (V₁ : Spc F E d₂) (M₁ : Model σ V₁ W) (e : Fn F n d →ₗ[ℂ] Fn F d₂ d),
      V₁.J = H.ιᵀ * X.J * H.ι.map σ → M₁.IsGood B.ψ → IsEv B M M₁ H.ι 1 {u | ∃ z, u = Matrix.vecMulVec (incV F H.x) z} e →
      ∀ e' : Fn F n d →ₗ[ℂ] Fn F d₂ d,
      (∀ z, ∀ Φ ∈ schA F (Fin n × Fin d), e' (M.co.rho B.ψ (incM F H.ι * z * (incM F (1 : Matrix (Fin d) (Fin d) E))ᵀ) Φ) = M₁.co.rho B.ψ z (e' Φ)) →
      (∀ u ∈ {u | ∃ z, u = Matrix.vecMulVec (incV F H.x) z}, ∀ Φ ∈ schA F (Fin n × Fin d), e' (M.co.rho B.ψ u Φ) = e' Φ) →
      (∀ y : Fin d₂ × Fin d → AF F, (LinearMap.proj y : Fn F d₂ d →ₗ[ℂ] ℂ) ∘ₗ e' ∈ (adeleClass F).adm (Fin n × Fin d)) →
      ∃ c : ℂ, ∀ Φ ∈ schA F (Fin n × Fin d), e' Φ = c • e Φ := by
  intro _ F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hP n₁ H hHyp X₁ M₁ e hgram hM₁ he e' hheis hinv hpt
  have hstd : IsStd B.ψ := hP.base.std
  let δ : Fn F n₁ d →ₗ[ℂ] ℂ := LinearMap.proj 0
  have hδ : δ ∈ (adeleClass F).adm (Fin n₁ × Fin d) := GlobalTheory.EvZeroUniq.proj_zero_mem_adm F _
  have hρ : ∀ u, ∀ Φ ∈ schA F (Fin n × Fin d), M.co.rho B.ψ u Φ ∈ schA F (Fin n × Fin d) :=
    fun u Φ hΦ => GlobalTheory.EvZeroUniq.schr_mem_schA _ hstd _ hΦ
  have hδe : ∀ (f : Fn F n₁ d) x, f x = δ (M₁.co.rho B.ψ (M₁.co.e.symm (x, 0)) f) := fun f x =>
    GlobalTheory.EvZeroUniq.apply_eq_rho _ _ f x
  have hfix : ∀ z, (M₁.co.e z).1 = 0 → ∀ f : Fn F n₁ d, δ (M₁.co.rho B.ψ z f) = δ f :=
    fun z hz f => GlobalTheory.EvZeroUniq.rho_apply_zero _ _ f z hz
  obtain ⟨Φ₀, hΦ₀, hne⟩ := GlobalTheory.T.eigen_intertwiner_extension F E σ B n d n₁ d X W X₁ W M M₁ H.ι 1 _ e hP.good hM₁ he
  obtain ⟨x₀, hx₀⟩ : ∃ x, e Φ₀ x ≠ 0 := by
    by_contra h
    push_neg at h
    exact hne (funext h)
  obtain ⟨L, hLiso, hLrank, hL⟩ := GlobalTheory.T.hyperbolic_plane_decomposition_of_pair F E σ B n d X W M χX χW om r s r' s' hP n₁ H hHyp X₁ M₁ hgram hM₁
  have hinvL : ∀ l : Fn F n d →ₗ[ℂ] ℂ, (∀ u ∈ {u : Matrix (Fin n) (Fin d) (AE F E) | ∃ z, u = Matrix.vecMulVec (incV F H.x) z},
      ∀ Φ ∈ schA F (Fin n × Fin d), l (M.co.rho B.ψ u Φ) = l Φ) →
      (∀ z : Matrix (Fin n₁) (Fin d) (AE F E), (M₁.co.e z).1 = 0 → ∀ Φ ∈ schA F (Fin n × Fin d),
        l (M.co.rho B.ψ (incM F H.ι * z * (incM F (1 : Matrix (Fin d) (Fin d) E))ᵀ) Φ) = l Φ) →
      ∀ (t : AF F), ∀ w ∈ L, ∀ φ ∈ schA F (Fin n × Fin d),
        l (schr B.ψ (t • ((fun i => algebraMap F (AF F) (w.1 i)), (fun i => algebraMap F (AF F) (w.2 i)))) φ) = l φ := by
    intro l h1 h2 t w hw φ hφ
    obtain ⟨u, hu, z, hz, heq⟩ := hL t w hw
    rw [heq φ, h1 u hu _ (hρ _ φ hφ), h2 z hz φ hφ]
  obtain ⟨c, hc⟩ := GlobalTheory.T.adelicStoneVonNeumann_lagrangian_uniqueness F B.ψ hstd (Fin n × Fin d) L hLiso hLrank (δ ∘ₗ e') (hpt 0) (δ ∘ₗ e)
    (GlobalTheory.T.eigen_intertwiner_good_models F E σ B n d n₁ d X W X₁ W M M₁ H.ι 1 _ e hP.good hM₁ he δ hδ)
    (hinvL _ (fun u hu Φ hΦ => by simp only [LinearMap.comp_apply]; rw [hinv u hu Φ hΦ])
      (fun z hz Φ hΦ => by simp only [LinearMap.comp_apply]; rw [hheis z Φ hΦ, hfix z hz]))
    (hinvL _ (fun u hu Φ hΦ => by simp only [LinearMap.comp_apply]; rw [he.inv u hu Φ hΦ])
      (fun z hz Φ hΦ => by simp only [LinearMap.comp_apply]; rw [he.Heisenberg₂ z Φ hΦ, hfix z hz]))
    ⟨_, hρ (incM F H.ι * M₁.co.e.symm (x₀, 0) * (incM F (1 : Matrix (Fin d) (Fin d) E))ᵀ) Φ₀ hΦ₀, by
      simp only [LinearMap.comp_apply]
      rw [he.Heisenberg₂ _ Φ₀ hΦ₀, ← hδe]
      exact hx₀⟩
  refine ⟨c, fun Φ hΦ => funext fun x => ?_⟩
  have h1 := hc _ (hρ (incM F H.ι * M₁.co.e.symm (x, 0) * (incM F (1 : Matrix (Fin d) (Fin d) E))ᵀ) Φ hΦ)
  simp only [LinearMap.comp_apply] at h1
  rw [hheis _ Φ hΦ, he.Heisenberg₂ _ Φ hΦ, ← hδe, ← hδe] at h1
  simpa using h1

open GlobalTheory.PlaneLevi in

theorem levi_plain : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n d₂ : ℕ) (X : Spc F E n)
    (H : Plane E n d₂), (∀ i j, σ (X.J j i) = X.J i j) → (∀ e : E, σ (σ e) = e) →
      form σ X.J H.x H.x = 0 → form σ X.J H.y H.y = 0 → form σ X.J H.x H.y = 1 →
      (∀ u, form σ X.J (H.ι *ᵥ u) H.x = 0 ∧ form σ X.J (H.ι *ᵥ u) H.y = 0) →
      ∀ t : ℕ, t ≠ 0 → ∃ m : UA σ X.J, mat m *ᵥ incV F H.x = (t : AE F E) • incV F H.x ∧
        (t : AE F E) • (mat m *ᵥ incV F H.y) = incV F H.y ∧ ∀ z : Fin d₂ → AE F E, mat m *ᵥ (incM F H.ι *ᵥ z) = incM F H.ι *ᵥ z := by
  intro F E _ _ _ _ _ σ n n₁ X H hXh hσ hxx hyy hxy horth t ht
  have hyp : Hyp (σ := σ) (J := X.J) H.x H.y :=
    ⟨hxx, hyy, hxy, by rw [← form_swap hσ hXh, hxy, map_one]⟩
  have hs : (t : E) ≠ 0 := Nat.cast_ne_zero.2 ht
  have hσs : σ (t : E) = t := map_natCast σ t
  have hinv : levi σ X.J H.x H.y (t : E)⁻¹ * levi σ X.J H.x H.y (t : E) = 1 := by
    have := levi_mul_levi hyp (inv_ne_zero hs); rwa [inv_inv] at this
  let g : GL (Fin n) E := ⟨levi σ X.J H.x H.y t, levi σ X.J H.x H.y (t : E)⁻¹, levi_mul_levi hyp hs, hinv⟩
  refine ⟨toUA σ g (levi_unitary hσ hXh hyp hs hσs), ?_, ?_, ?_⟩
  · rw [mat_toUA]
    ext i
    change ((levi σ X.J H.x H.y t).map (inclR (F := F) (AF F)) *ᵥ ((inclR (F := F) (AF F)) ∘ H.x)) i = _
    rw [← RingHom.map_mulVec, levi_mulVec_of_hyp hyp]
    simp [incV, map_natCast]
  · rw [mat_toUA]
    ext i
    change (t : AE F E) * ((levi σ X.J H.x H.y t).map (inclR (F := F) (AF F)) *ᵥ ((inclR (F := F) (AF F)) ∘ H.y)) i = _
    rw [← RingHom.map_mulVec, levi_mulVec_y hyp, ← map_natCast (inclR (F := F) (AF F)) t, ← map_mul]
    simp only [incV, Pi.smul_apply, smul_eq_mul, ← mul_assoc, mul_inv_cancel₀ hs, one_mul]
  · intro z
    rw [mat_toUA, Matrix.mulVec_mulVec]
    congr 1
    change (levi σ X.J H.x H.y t).map (inclR (F := F) (AF F)) * H.ι.map (inclR (F := F) (AF F)) =
      H.ι.map (inclR (F := F) (AF F))
    rw [← Matrix.map_mul, levi_mul_of_orth _ horth]

end GlobalTheory.MixXUnipPlain

namespace GlobalTheory.MixXUnipPlain

theorem evalX_unip_invariant : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ),
    IsPair B M χX χW om r s r' s' →
    ∀ (d₁ : ℕ) (W₁ : Spc F E d₁) (H' : Plane E d d₁) (i₀ i₁ : ℕ), H'.IsAdapted σ B W W₁ i₀ i₁ →
    ∀ (d₂ : ℕ) (H : Plane E n d₂), (d₂ + 2 = n ∧ form σ X.J H.x H.x = 0 ∧ form σ X.J H.y H.y = 0 ∧ form σ X.J H.x H.y = 1 ∧
        (∀ u, form σ X.J (H.ι *ᵥ u) H.x = 0 ∧ form σ X.J (H.ι *ᵥ u) H.y = 0) ∧ Function.Injective H.ι.mulVec) →
    ∀ (V₁ : Spc F E d₂) (M₁ : Model σ V₁ W) (e : Fn F n d →ₗ[ℂ] Fn F d₂ d),
      V₁.J = H.ιᵀ * X.J * H.ι.map σ → M₁.IsGood B.ψ → IsEv B M M₁ H.ι 1 {u | ∃ z, u = Matrix.vecMulVec (incV F H.x) z} e →
    ∀ u ∈ unip σ X H, ∀ Ψ ∈ schA F (Fin n × Fin d), e (om (u, 1) Ψ) = e Ψ := by
  intro hK F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hP d₁ W₁ H' i₀ i₁ hH' d₂ H hHyp V₁ M₁ e hgram hM₁ he u hu
  obtain ⟨hrk, hxx, hyy, hxy, horth, hinj⟩ := hHyp
  have hS := IsUWeilPair.isUSplitting hP.weil
  have hσ : ∀ e : E, σ (σ e) = e := GlobalTheory.PlaneLevi.invol_of_good hP.base
  have pres : ∀ g Φ, Φ ∈ schA F (Fin n × Fin d) → om g Φ ∈ schA F (Fin n × Fin d) := fun g Φ h => hS.pres g Φ h
  have omul : ∀ g h : UA σ X.J, ∀ Φ, om (g * h, 1) Φ = om (g, 1) (om (h, 1) Φ) := fun g h Φ => by
    rw [← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk, mul_one]
  have om1 : ∀ Φ, om (1, 1) Φ = Φ := fun Φ => by
    rw [show ((1 : UA σ X.J), (1 : UA σ W.J)) = 1 from rfl, map_one, Module.End.one_apply]
  have twist : ∀ (g : UA σ X.J) (a : AE F E), mat g *ᵥ incV F H.x = a • incV F H.x →
      (∀ z : Fin d₂ → AE F E, ∃ b : AE F E, mat g *ᵥ (incM F H.ι *ᵥ z) = incM F H.ι *ᵥ z + b • incV F H.x) →
      ∃ c : ℂ, ∀ Φ ∈ schA F (Fin n × Fin d), e (om (g, 1) Φ) = c • e Φ := by
    intro g a ha hb
    obtain ⟨h1, h2⟩ := twist_plain F E σ B n d X W M χX χW om r s r' s' hP d₂ H horth V₁ M₁ e he g a ha hb
    refine uniq_plain hK.base F E σ B n d X W M χX χW om r s r' s' hP d₂ H ⟨hrk, hxx, hyy, hxy, horth, hinj⟩ V₁ M₁ e hgram hM₁ he
      (e ∘ₗ om (g, 1)) h1 h2 fun y => ?_
    have hy : (LinearMap.proj y : Fn F d₂ d →ₗ[ℂ] ℂ) ∘ₗ e ∈ (adeleClass F).adm (Fin n × Fin d) :=
      GlobalTheory.T.eigen_intertwiner_good_models F E σ B n d d₂ d X W V₁ W M M₁ H.ι 1 _ e hP.good hM₁ he _ (GlobalTheory.EvPoint.proj_mem_adm F _ y)
    have := hS.adm (g, 1) _ hy
    rwa [LinearMap.comp_assoc] at this
  by_cases h0 : ∀ Φ ∈ schA F (Fin n × Fin d), e Φ = 0
  · intro Φ hΦ
    rw [h0 _ (pres _ _ hΦ), h0 _ hΦ]
  push_neg at h0
  obtain ⟨Φ₀, hΦ₀, hne⟩ := h0
  let Q : UA σ X.J → ℂ → Prop := fun g c => ∀ Φ ∈ schA F (Fin n × Fin d), e (om (g, 1) Φ) = c • e Φ
  have Quniq : ∀ g c c', Q g c → Q g c' → c = c' := fun g c c' h h' =>
    smul_left_injective ℂ hne ((h Φ₀ hΦ₀).symm.trans (h' Φ₀ hΦ₀))
  have Qmul : ∀ g h c c', Q g c → Q h c' → Q (g * h) (c * c') := fun g h c c' hg hh Φ hΦ => by
    rw [omul, hg _ (pres _ _ hΦ), hh _ hΦ, smul_smul]
  have Qone : Q 1 1 := fun Φ _ => by rw [om1, one_smul]
  have Qinv : ∀ g c, Q g c → c ≠ 0 ∧ Q g⁻¹ c⁻¹ := by
    intro g c hg
    have key : ∀ Φ ∈ schA F (Fin n × Fin d), e Φ = c • e (om (g⁻¹, 1) Φ) := fun Φ hΦ => by
      rw [← hg _ (pres _ _ hΦ), ← omul, mul_inv_cancel, om1]
    have hc : c ≠ 0 := fun h => hne (by rw [key _ hΦ₀, h, zero_smul])
    exact ⟨hc, fun Φ hΦ => by rw [key Φ hΦ, smul_smul, inv_mul_cancel₀ hc, one_smul]⟩
  have Qpow : ∀ g c, Q g c → ∀ k : ℕ, Q (g ^ k) (c ^ k) := by
    intro g c hg k
    induction k with
    | zero => simpa using Qone
    | succ k ih => rw [pow_succ, pow_succ]; exact Qmul _ _ _ _ ih hg
  have gen : ∀ g : UA σ X.J, mat g *ᵥ incV F H.x = incV F H.x →
      (∀ z : Fin d₂ → AE F E, ∃ a : AE F E, mat g *ᵥ (incM F H.ι *ᵥ z) = incM F H.ι *ᵥ z + a • incV F H.x) → Q g 1 := by
    intro g hgx hgz
    obtain ⟨cu, hcu⟩ := twist g 1 (by rw [one_smul]; exact hgx) hgz
    have scl : ∀ t : ℕ, t ≠ 0 → ∃ m : UA σ X.J, (mat m *ᵥ incV F H.x = (t : AE F E) • incV F H.x ∧
        (t : AE F E) • (mat m *ᵥ incV F H.y) = incV F H.y ∧ ∀ z : Fin d₂ → AE F E, mat m *ᵥ (incM F H.ι *ᵥ z) = incM F H.ι *ᵥ z) ∧
        ∃ c, Q m c := by
      intro t ht
      obtain ⟨m, h1, h2, h3⟩ := levi_plain F E σ n d₂ X H hP.herm.herm hσ hxx hyy hxy horth t ht
      exact ⟨m, ⟨h1, h2, h3⟩, twist m _ h1 fun z => ⟨0, by rw [zero_smul, add_zero, h3]⟩⟩
    obtain ⟨m, ⟨hm1, hm2, hm3⟩, cm, hcm⟩ := scl 2 two_ne_zero
    have hm1' : mat m *ᵥ incV F H.x = (2 : AE F E) • incV F H.x := by exact_mod_cast hm1
    have hm2' : (2 : AE F E) • (mat m *ᵥ incV F H.y) = incV F H.y := by exact_mod_cast hm2
    obtain ⟨hcm0, hcmi⟩ := Qinv _ _ hcm
    obtain ⟨hcu0, hcui⟩ := Qinv _ _ hcu
    set v := g⁻¹ * g⁻¹ * (m * g * m⁻¹) with hv
    have hQv : Q v (cu⁻¹ * cu⁻¹ * (cm * cu * cm⁻¹)) :=
      Qmul _ _ _ _ (Qmul _ _ _ _ hcui hcui) (Qmul _ _ _ _ (Qmul _ _ _ _ hcm hcu) hcmi)
    set cv := cu⁻¹ * cu⁻¹ * (cm * cu * cm⁻¹) with hcv
    have hcv' : cv = cu⁻¹ := by rw [hcv]; field_simp
    have step : ∀ t : ℕ, t ≠ 0 → cv ^ (t ^ 2) = cv := by
      intro t ht
      obtain ⟨m', ⟨h1, h2, h3⟩, cm', hcm'⟩ := scl t ht
      obtain ⟨hcm0', hcmi'⟩ := Qinv _ _ hcm'
      have e1 := Qmul _ _ _ _ (Qmul _ _ _ _ hcm' hQv) hcmi'
      rw [GlobalTheory.T.hyperbolic_plane_conditions_hermitian F E σ n d₂ X H hP.herm.herm hσ ⟨hrk, hxx, hyy, hxy, horth, hinj⟩ g hgx hgz m m' t hm1' hm2' hm3 h1 h2 h3] at e1
      have := Quniq _ _ _ (Qpow _ _ hQv (t ^ 2)) e1
      rw [this]; field_simp
    have hcv0 : cv ≠ 0 := by rw [hcv']; exact inv_ne_zero hcu0
    have s2 := step 2 two_ne_zero
    have s3 := step 3 three_ne_zero
    norm_num at s2 s3
    have c3 : cv ^ 3 = 1 := by
      have : cv * (cv ^ 3 - 1) = 0 := by linear_combination s2
      exact sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_left hcv0)
    have c1 : cv = 1 := by rw [← s3, show 9 = 3 * 3 from rfl, pow_mul, c3, one_pow]
    have : cu = 1 := by rw [hcv', inv_eq_one] at c1; exact c1
    rw [← this]; exact hcu
  have hcl : ∀ g ∈ unip σ X H, Q g 1 := by
    intro g hg
    induction hg using Subgroup.closure_induction with
    | mem g hg => exact gen g hg.1 hg.2
    | one => exact Qone
    | mul g h _ _ ihg ihh => simpa using Qmul _ _ _ _ ihg ihh
    | inv g _ ih => simpa using (Qinv _ _ ih).2
  intro Φ hΦ
  simpa using hcl u hu Φ hΦ

end GlobalTheory.MixXUnipPlain

end
