import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsDblOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilRepresentationPreservesSchwartz
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianAdaptedPlaneFactor
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicStoneVonNeumannLagrangianUniquenessStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PairDescendsAlongAdaptedPlaneStatement

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.MixXChar
open GlobalTheory.Doubling (absE)

noncomputable section

namespace GlobalTheory.MixXDblInt

theorem dbl_decomp {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n n₁ d : ℕ} (H : Plane E n n₁)
    (a₁ a₂ : Fin d → AE F E) (z₁ z₂ : Matrix (Fin n₁) (Fin d) (AE F E)) : Matrix.fromCols z₁ᵀ z₂ᵀ * (dblEmb (F := F) H.ι)ᵀ +
      (Matrix.vecMulVec a₁ (Sum.elim (incV F H.x) 0) + Matrix.vecMulVec a₂ (Sum.elim 0 (incV F H.x))) =
      Matrix.fromCols (Matrix.vecMulVec (incV F H.x) a₁ + incM F H.ι * z₁)ᵀ
        (Matrix.vecMulVec (incV F H.x) a₂ + incM F H.ι * z₂)ᵀ := by
  ext i j
  rcases j with j | j
  · simp [dblEmb, Matrix.fromBlocks_transpose, Matrix.fromCols_mul_fromBlocks, Matrix.vecMulVec_apply, Matrix.mul_apply]
    ring
  · simp [dblEmb, Matrix.fromBlocks_transpose, Matrix.fromCols_mul_fromBlocks, Matrix.vecMulVec_apply, Matrix.mul_apply]
    ring

def dblV {F : Type} [Field F] {κ : Type} (L : Submodule F ((κ → F) × (κ → F))) :
    (L × L) →ₗ[F] ((κ ⊕ κ → F) × (κ ⊕ κ → F)) where
  toFun p := (Sum.elim (p.1 : (κ → F) × (κ → F)).1 (p.2 : (κ → F) × (κ → F)).1,
    Sum.elim (p.1 : (κ → F) × (κ → F)).2 (-(p.2 : (κ → F) × (κ → F)).2))
  map_add' p q := by
    ext i <;> cases i <;> simp [add_comm]
  map_smul' c p := by
    ext i <;> cases i <;> simp

theorem dblV_injective {F : Type} [Field F] {κ : Type} (L : Submodule F ((κ → F) × (κ → F))) :
    Function.Injective (dblV L) := by
  intro p q h
  simp only [dblV, LinearMap.coe_mk, AddHom.coe_mk, Prod.mk.injEq] at h
  obtain ⟨h1, h2⟩ := h
  have a1 := congrArg (fun f => f ∘ Sum.inl) h1
  have a2 := congrArg (fun f => f ∘ Sum.inr) h1
  have b1 := congrArg (fun f => f ∘ Sum.inl) h2
  have b2 := congrArg (fun f => f ∘ Sum.inr) h2
  simp only [Sum.elim_comp_inl, Sum.elim_comp_inr, neg_inj] at a1 a2 b1 b2
  exact Prod.ext (Subtype.ext (Prod.ext a1 b1)) (Subtype.ext (Prod.ext a2 b2))

theorem dblLagr : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d)
    (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ), IsPair B M χX χW om r s r' s' →
    ∀ (n₁ : ℕ) (X₁ : Spc F E n₁) (H : Plane E n n₁) (j₀ j₁ : ℕ) (M₁ : Model σ X₁ W) (om₁ : Rep σ X₁ W) (r₁ s₁ : ℕ),
      H.IsAdapted σ B X X₁ j₀ j₁ → IsPair B M₁ χX χW om₁ r₁ s₁ r' s' →
      ∀ dd omd dd₁ omd₁, IsDblOf B.ψ M χW om dd omd → IsDblOf B.ψ M₁ χW om₁ dd₁ omd₁ →
      ∃ L : Submodule F (((Fin n × Fin d) ⊕ (Fin n × Fin d) → F) × ((Fin n × Fin d) ⊕ (Fin n × Fin d) → F)),
        (∀ a ∈ L, ∀ b ∈ L, a.1 ⬝ᵥ b.2 = b.1 ⬝ᵥ a.2) ∧
        Module.finrank F L = Fintype.card ((Fin n × Fin d) ⊕ (Fin n × Fin d)) ∧
        ∀ (t : AF F), ∀ w ∈ L, ∃ u ∈ isoD d H, ∃ z : Matrix (Fin d) (Fin n₁ ⊕ Fin n₁) (AE F E), (dd₁.e z).1 = 0 ∧
          dd.e (z * (dblEmb H.ι)ᵀ + u) =
            t • ((fun i => algebraMap F (AF F) (w.1 i)), (fun i => algebraMap F (AF F) (w.2 i))) := by
  intro F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hP n₁ X₁ H j₀ j₁ M₁ om₁ r₁ s₁ hH hP₁ dd omd dd₁ omd₁ hD hD₁
  obtain ⟨L₀, hiso, hrk, hre⟩ := GlobalTheory.T.pair_descends_along_adapted_plane F E σ B n d X W M χX χW om r s r' s' hP n₁ X₁ H j₀ j₁ M₁ om₁ r₁ s₁ hH hP₁
  obtain ⟨d', hd', hdc, -⟩ := hD
  obtain ⟨d₁', hd₁', hdc₁, -⟩ := hD₁
  refine ⟨LinearMap.range (dblV L₀), ?_, ?_, ?_⟩
  · rintro _ ⟨⟨p, q⟩, rfl⟩ _ ⟨⟨p', q'⟩, rfl⟩
    simp only [dblV, LinearMap.coe_mk, AddHom.coe_mk, sumElim_dotProduct_sumElim, dotProduct_neg]
    rw [hiso _ p.2 _ p'.2, hiso _ q.2 _ q'.2]
  · rw [LinearMap.finrank_range_of_inj (dblV_injective L₀), Module.finrank_prod, hrk, Fintype.card_sum]
  · rintro t _ ⟨⟨p, q⟩, rfl⟩
    obtain ⟨a₁, z₁, hz₁, he₁⟩ := hre t p.1 p.2
    obtain ⟨a₂, z₂, hz₂, he₂⟩ := hre t q.1 q.2
    refine ⟨Matrix.vecMulVec a₁ (Sum.elim (incV F H.x) 0) + Matrix.vecMulVec a₂ (Sum.elim 0 (incV F H.x)),
      ⟨a₁, a₂, rfl⟩, Matrix.fromCols z₁ᵀ z₂ᵀ, ?_, ?_⟩
    · rw [hdc₁, hd₁', hd₁', hz₁, hz₂]
      funext i; cases i <;> rfl
    · refine (congrArg dd.e (dbl_decomp (F := F) H a₁ a₂ z₁ z₂)).trans ?_
      rw [hdc, hd', hd', he₁, he₂]
      ext i <;> cases i <;> simp [dblV]

theorem vecMulVec_mul_transpose {α β γ R : Type} [Fintype β] [CommSemiring R] (z : α → R) (v : β → R)
    (A : Matrix γ β R) : Matrix.vecMulVec z v * Aᵀ = Matrix.vecMulVec z (A *ᵥ v) := by
  ext i j
  simp [Matrix.mul_apply, Matrix.vecMulVec_apply, Matrix.mulVec, dotProduct, Finset.mul_sum, mul_comm, mul_left_comm]

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem twist {B : Base F E} {n d : ℕ} {X : Spc F E n} {W : Spc F E d} {M : Model σ X W} {χW : Chr F E}
    {om : Rep σ X W} {n₁ : ℕ} {X₁ : Spc F E n₁} {H : Plane E n n₁} {M₁ : Model σ X₁ W} {om₁ : Rep σ X₁ W}
    {dd omd dd₁ omd₁} (hD : IsDblOf B.ψ M χW om dd omd) (hD₁ : IsDblOf B.ψ M₁ χW om₁ dd₁ omd₁)
    (et : ((((Fin n × Fin d) ⊕ (Fin n × Fin d)) → AF F) → ℂ) →ₗ[ℂ] ((((Fin n₁ × Fin d) ⊕ (Fin n₁ × Fin d)) → AF F) → ℂ))
    (hm : ∀ Φ ∈ schA F ((Fin n × Fin d) ⊕ (Fin n × Fin d)), et Φ ∈ schA F ((Fin n₁ × Fin d) ⊕ (Fin n₁ × Fin d)))
    (hl : ∀ w : Matrix (Fin d) (Fin n₁ ⊕ Fin n₁) (AE F E), ∀ u ∈ isoD d H, ∀ Φ ∈ schA F ((Fin n × Fin d) ⊕ (Fin n × Fin d)),
      et (dd.rho B.ψ (w * (dblEmb H.ι)ᵀ + u) Φ) = dd₁.rho B.ψ w (et Φ))
    (ha : ∀ l ∈ (adeleClass F).adm ((Fin n₁ × Fin d) ⊕ (Fin n₁ × Fin d)), l ∘ₗ et ∈ (adeleClass F).adm ((Fin n × Fin d) ⊕ (Fin n × Fin d)))
    (gd₁ md) (hL : IsDLevi H gd₁ md) :
    (∀ Φ ∈ schA F ((Fin n × Fin d) ⊕ (Fin n × Fin d)),
      (omd₁ gd₁⁻¹ ∘ₗ et ∘ₗ omd md) Φ ∈ schA F ((Fin n₁ × Fin d) ⊕ (Fin n₁ × Fin d))) ∧
    (∀ w : Matrix (Fin d) (Fin n₁ ⊕ Fin n₁) (AE F E), ∀ u ∈ isoD d H, ∀ Φ ∈ schA F ((Fin n × Fin d) ⊕ (Fin n × Fin d)),
      (omd₁ gd₁⁻¹ ∘ₗ et ∘ₗ omd md) (dd.rho B.ψ (w * (dblEmb H.ι)ᵀ + u) Φ) =
        dd₁.rho B.ψ w ((omd₁ gd₁⁻¹ ∘ₗ et ∘ₗ omd md) Φ)) ∧
    (∀ l ∈ (adeleClass F).adm ((Fin n₁ × Fin d) ⊕ (Fin n₁ × Fin d)),
      l ∘ₗ (omd₁ gd₁⁻¹ ∘ₗ et ∘ₗ omd md) ∈ (adeleClass F).adm ((Fin n × Fin d) ⊕ (Fin n × Fin d))) := by
  obtain ⟨-, -, -, hW, -⟩ := hD
  obtain ⟨-, -, -, hW₁, -⟩ := hD₁
  have hs := hW.2.1
  have hs₁ := hW₁.2.1
  refine ⟨fun Φ hΦ => ?_, fun w u hu Φ hΦ => ?_, fun l hl' => ?_⟩
  · simp only [LinearMap.comp_apply]
    exact hs₁.pres _ _ (hm _ (hs.pres _ _ hΦ))
  · simp only [LinearMap.comp_apply]
    rw [hs.impl md _ Φ hΦ]
    have ea : actB (cA σ) md (w * (dblEmb H.ι)ᵀ + u) =
        (w * (gd₁.1.1 : Matrix (Fin n₁ ⊕ Fin n₁) (Fin n₁ ⊕ Fin n₁) (AE F E))ᵀ) * (dblEmb H.ι)ᵀ + u := by
      obtain ⟨z₁, z₂, rfl⟩ := hu
      have h3 : (md.1.1 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (AE F E)) * dblEmb H.ι = dblEmb H.ι * gd₁.1.1 := hL.2.2
      show (w * (dblEmb H.ι)ᵀ + _) * (md.1.1 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (AE F E))ᵀ = _
      rw [Matrix.add_mul, Matrix.add_mul, vecMulVec_mul_transpose, vecMulVec_mul_transpose, hL.1, hL.2.1]
      congr 1
      have h4 : (dblEmb H.ι)ᵀ * (md.1.1 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (AE F E))ᵀ =
          (gd₁.1.1 : Matrix (Fin n₁ ⊕ Fin n₁) (Fin n₁ ⊕ Fin n₁) (AE F E))ᵀ * (dblEmb H.ι)ᵀ :=
        (Matrix.transpose_mul _ _).symm.trans ((congrArg Matrix.transpose h3).trans (Matrix.transpose_mul _ _))
      calc w * (dblEmb H.ι)ᵀ * (md.1.1 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (AE F E))ᵀ
          = w * ((dblEmb H.ι)ᵀ * (md.1.1 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (AE F E))ᵀ) := Matrix.mul_assoc _ _ _
        _ = w * ((gd₁.1.1 : Matrix (Fin n₁ ⊕ Fin n₁) (Fin n₁ ⊕ Fin n₁) (AE F E))ᵀ * (dblEmb H.ι)ᵀ) := congrArg _ h4
        _ = _ := (Matrix.mul_assoc _ _ _).symm
    rw [ea, hl _ u hu _ (hs.pres _ _ hΦ), hs₁.impl gd₁⁻¹ _ _ (hm _ (hs.pres _ _ hΦ))]
    congr 1
    show w * (gd₁.1.1 : Matrix (Fin n₁ ⊕ Fin n₁) (Fin n₁ ⊕ Fin n₁) (AE F E))ᵀ *
      (((gd₁⁻¹ : UG (cA σ) (dbl (incM F X₁.J))) : GL (Fin n₁ ⊕ Fin n₁) (AE F E)) : Matrix (Fin n₁ ⊕ Fin n₁) (Fin n₁ ⊕ Fin n₁) (AE F E))ᵀ = w
    have hi : (((gd₁⁻¹ : UG (cA σ) (dbl (incM F X₁.J))) : GL (Fin n₁ ⊕ Fin n₁) (AE F E)) :
        Matrix (Fin n₁ ⊕ Fin n₁) (Fin n₁ ⊕ Fin n₁) (AE F E)) * gd₁.1.1 = 1 := by
      rw [Subgroup.coe_inv]; exact Units.inv_mul _
    rw [Matrix.mul_assoc, ← Matrix.transpose_mul, hi, Matrix.transpose_one, Matrix.mul_one]
  · exact hs.adm md _ (ha _ (hs₁.adm gd₁⁻¹ l hl'))

theorem uniq {B : Base F E} {n d : ℕ} {X : Spc F E n} {W : Spc F E d} {M : Model σ X W} {χX χW : Chr F E}
    {om : Rep σ X W} {r s r' s' : ℕ} (hP : IsPair B M χX χW om r s r' s') {n₁ : ℕ} {X₁ : Spc F E n₁} {H : Plane E n n₁}
    {j₀ j₁ : ℕ} {M₁ : Model σ X₁ W} {om₁ : Rep σ X₁ W} {r₁ s₁ : ℕ} (hH : H.IsAdapted σ B X X₁ j₀ j₁)
    (hP₁ : IsPair B M₁ χX χW om₁ r₁ s₁ r' s') {dd omd dd₁ omd₁} (hD : IsDblOf B.ψ M χW om dd omd)
    (hD₁ : IsDblOf B.ψ M₁ χW om₁ dd₁ omd₁)
    (S T : ((((Fin n × Fin d) ⊕ (Fin n × Fin d)) → AF F) → ℂ) →ₗ[ℂ] ((((Fin n₁ × Fin d) ⊕ (Fin n₁ × Fin d)) → AF F) → ℂ))
    (hSl : ∀ w : Matrix (Fin d) (Fin n₁ ⊕ Fin n₁) (AE F E), ∀ u ∈ isoD d H, ∀ Φ ∈ schA F ((Fin n × Fin d) ⊕ (Fin n × Fin d)),
      S (dd.rho B.ψ (w * (dblEmb H.ι)ᵀ + u) Φ) = dd₁.rho B.ψ w (S Φ))
    (hTl : ∀ w : Matrix (Fin d) (Fin n₁ ⊕ Fin n₁) (AE F E), ∀ u ∈ isoD d H, ∀ Φ ∈ schA F ((Fin n × Fin d) ⊕ (Fin n × Fin d)),
      T (dd.rho B.ψ (w * (dblEmb H.ι)ᵀ + u) Φ) = dd₁.rho B.ψ w (T Φ))
    (hSa : ∀ l ∈ (adeleClass F).adm ((Fin n₁ × Fin d) ⊕ (Fin n₁ × Fin d)), l ∘ₗ S ∈ (adeleClass F).adm ((Fin n × Fin d) ⊕ (Fin n × Fin d)))
    (hTa : ∀ l ∈ (adeleClass F).adm ((Fin n₁ × Fin d) ⊕ (Fin n₁ × Fin d)), l ∘ₗ T ∈ (adeleClass F).adm ((Fin n × Fin d) ⊕ (Fin n × Fin d)))
    (hT0 : ∃ Φ ∈ schA F ((Fin n × Fin d) ⊕ (Fin n × Fin d)), T Φ ≠ 0) :
    ∃ c : ℂ, ∀ Φ ∈ schA F ((Fin n × Fin d) ⊕ (Fin n × Fin d)), S Φ = c • T Φ := by
  obtain ⟨L, hiso, hrk, hre⟩ := dblLagr F E σ B n d X W M χX χW om r s r' s' hP n₁ X₁ H j₀ j₁ M₁ om₁ r₁ s₁ hH hP₁
    dd omd dd₁ omd₁ hD hD₁
  have hψ := hP.base.std
  have hδ := GlobalTheory.LagrUniq.proj_zero_mem_adm (F := F) ((Fin n₁ × Fin d) ⊕ (Fin n₁ × Fin d))
  have h0 : (0 : Matrix (Fin d) (Fin n ⊕ Fin n) (AE F E)) ∈ isoD d H := ⟨0, 0, by simp⟩
  have key : ∀ R : ((((Fin n × Fin d) ⊕ (Fin n × Fin d)) → AF F) → ℂ) →ₗ[ℂ] ((((Fin n₁ × Fin d) ⊕ (Fin n₁ × Fin d)) → AF F) → ℂ),
      (∀ w : Matrix (Fin d) (Fin n₁ ⊕ Fin n₁) (AE F E), ∀ u ∈ isoD d H, ∀ Φ ∈ schA F ((Fin n × Fin d) ⊕ (Fin n × Fin d)),
        R (dd.rho B.ψ (w * (dblEmb H.ι)ᵀ + u) Φ) = dd₁.rho B.ψ w (R Φ)) →
      ∀ (t : AF F), ∀ w ∈ L, ∀ φ ∈ schA F ((Fin n × Fin d) ⊕ (Fin n × Fin d)),
        (LinearMap.proj 0 ∘ₗ R) (schr B.ψ (t • ((fun i => algebraMap F (AF F) (w.1 i)), (fun i => algebraMap F (AF F) (w.2 i)))) φ) =
          (LinearMap.proj 0 ∘ₗ R) φ := by
    intro R hR t w hw φ hφ
    obtain ⟨u, hu, z, hz, he⟩ := hre t w hw
    have e1 : schr B.ψ (t • ((fun i => algebraMap F (AF F) (w.1 i)), (fun i => algebraMap F (AF F) (w.2 i)))) φ =
        dd.rho B.ψ (z * (dblEmb H.ι)ᵀ + u) φ := by rw [Darboux.rho, he]
    simp only [LinearMap.comp_apply, LinearMap.proj_apply]
    rw [e1, hR z u hu φ hφ]
    simp [Darboux.rho, schr, hz]
  have hval : ∀ R : ((((Fin n × Fin d) ⊕ (Fin n × Fin d)) → AF F) → ℂ) →ₗ[ℂ] ((((Fin n₁ × Fin d) ⊕ (Fin n₁ × Fin d)) → AF F) → ℂ),
      (∀ w : Matrix (Fin d) (Fin n₁ ⊕ Fin n₁) (AE F E), ∀ u ∈ isoD d H, ∀ Φ ∈ schA F ((Fin n × Fin d) ⊕ (Fin n × Fin d)),
        R (dd.rho B.ψ (w * (dblEmb H.ι)ᵀ + u) Φ) = dd₁.rho B.ψ w (R Φ)) →
      ∀ x, ∀ Φ ∈ schA F ((Fin n × Fin d) ⊕ (Fin n × Fin d)),
        R Φ x = R (dd.rho B.ψ (dd₁.e.symm (x, 0) * (dblEmb H.ι)ᵀ + 0) Φ) 0 := by
    intro R hR x Φ hΦ
    rw [hR _ 0 h0 Φ hΦ]
    simp [Darboux.rho, schr]
  have hmem : ∀ x, ∀ Φ ∈ schA F ((Fin n × Fin d) ⊕ (Fin n × Fin d)),
      dd.rho B.ψ (dd₁.e.symm (x, 0) * (dblEmb H.ι)ᵀ + 0) Φ ∈ schA F ((Fin n × Fin d) ⊕ (Fin n × Fin d)) :=
    fun x Φ hΦ => GlobalTheory.HeisSchA.schr_mem_schA B.ψ hψ _ Φ hΦ
  obtain ⟨c, hc⟩ := GlobalTheory.T.adelicStoneVonNeumann_lagrangian_uniqueness F B.ψ hψ _ L hiso hrk _ (hSa _ hδ) _ (hTa _ hδ) (key S hSl) (key T hTl) (by
    obtain ⟨Φ, hΦ, h⟩ := hT0
    obtain ⟨x, hx⟩ := Function.ne_iff.1 h
    refine ⟨_, hmem x Φ hΦ, ?_⟩
    rw [hval T hTl x Φ hΦ] at hx
    simpa using hx)
  refine ⟨c, fun Φ hΦ => funext fun x => ?_⟩
  rw [Pi.smul_apply, hval S hSl x Φ hΦ, hval T hTl x Φ hΦ, smul_eq_mul]
  simpa using hc _ (hmem x Φ hΦ)

theorem intertwine : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d)
    (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ), IsPair B M χX χW om r s r' s' →
    ∀ (n₁ : ℕ) (X₁ : Spc F E n₁) (H : Plane E n n₁) (j₀ j₁ : ℕ) (M₁ : Model σ X₁ W) (om₁ : Rep σ X₁ W) (r₁ s₁ : ℕ),
      H.IsAdapted σ B X X₁ j₀ j₁ → IsPair B M₁ χX χW om₁ r₁ s₁ r' s' →
      ∀ e, IsEv B M M₁ H.ι 1 {u | ∃ z, u = Matrix.vecMulVec (incV F H.x) z} e →
      ∀ dd omd dd₁ omd₁, IsDblOf B.ψ M χW om dd omd → IsDblOf B.ψ M₁ χW om₁ dd₁ omd₁ →
      ∀ et : ((((Fin n × Fin d) ⊕ (Fin n × Fin d)) → AF F) → ℂ) →ₗ[ℂ] ((((Fin n₁ × Fin d) ⊕ (Fin n₁ × Fin d)) → AF F) → ℂ),
        (∀ Φ ∈ schA F ((Fin n × Fin d) ⊕ (Fin n × Fin d)), et Φ ∈ schA F ((Fin n₁ × Fin d) ⊕ (Fin n₁ × Fin d))) →
        (∀ w : Matrix (Fin d) (Fin n₁ ⊕ Fin n₁) (AE F E), ∀ u ∈ isoD d H, ∀ Φ ∈ schA F ((Fin n × Fin d) ⊕ (Fin n × Fin d)),
          et (dd.rho B.ψ (w * (dblEmb H.ι)ᵀ + u) Φ) = dd₁.rho B.ψ w (et Φ)) →
        (∀ l ∈ (adeleClass F).adm ((Fin n₁ × Fin d) ⊕ (Fin n₁ × Fin d)), l ∘ₗ et ∈ (adeleClass F).adm ((Fin n × Fin d) ⊕ (Fin n × Fin d))) →
        ∀ gd₁ md, IsDLevi H gd₁ md → ∃ c : ℂ, ∀ Φ ∈ schA F ((Fin n × Fin d) ⊕ (Fin n × Fin d)), et (omd md Φ) = c • omd₁ gd₁ (et Φ) := by
  intro F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hP n₁ X₁ H j₀ j₁ M₁ om₁ r₁ s₁ hH hP₁ e _ dd omd dd₁ omd₁ hD hD₁
    et hm hl ha gd₁ md hL
  by_cases h0 : ∃ Φ ∈ schA F ((Fin n × Fin d) ⊕ (Fin n × Fin d)), et Φ ≠ 0
  · obtain ⟨-, h2, h3⟩ := twist hD hD₁ et hm hl ha gd₁ md hL
    obtain ⟨c, hc⟩ := uniq hP hH hP₁ hD hD₁ _ et h2 hl h3 ha h0
    refine ⟨c, fun Φ hΦ => ?_⟩
    have hinv : ∀ y, omd₁ gd₁ (omd₁ gd₁⁻¹ y) = y := fun y => by
      rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
    calc et (omd md Φ) = omd₁ gd₁ (omd₁ gd₁⁻¹ (et (omd md Φ))) := (hinv _).symm
      _ = omd₁ gd₁ (c • et Φ) := by rw [← hc Φ hΦ]; rfl
      _ = c • omd₁ gd₁ (et Φ) := map_smul _ _ _
  · push_neg at h0
    obtain ⟨-, -, -, hW, -⟩ := hD
    exact ⟨0, fun Φ hΦ => by rw [h0 _ (hW.2.1.pres md Φ hΦ), zero_smul]⟩

end GlobalTheory.MixXDblInt
end
