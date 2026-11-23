import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToGAdMat
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.LanglandsSquareIntegrable
import Development.AbelianVarietyTheory.Definitions.Divisors.IsSquareIntegrableIffMemL2
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPurelyImaginaryElement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsHermNDSmulSkewForm
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.ThK.SquareIntegrability

noncomputable section

namespace GlobalTheory.CuspScale

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n : ℕ}

theorem hr_smul (R : Type) [CommRing R] [Algebra F R] (J : Matrix (Fin n) (Fin n) E) {k : E} (hk : k ≠ 0) :
    HR R σ (k • J) = HR R σ J := by
  have hu : IsUnit (inclR (F := F) R k) := (IsUnit.mk0 k hk).map _
  have e : JR (F := F) R (k • J) = inclR (F := F) R k • JR (F := F) R J :=
    Matrix.ext fun i j => map_mul (inclR (F := F) R) k (J i j)
  ext g
  change Formalism.UG.cT _ g.1 * JR (F := F) R _ * g.1 = JR (F := F) R _ ↔ Formalism.UG.cT _ g.1 * JR (F := F) R _ * g.1 = JR (F := F) R _
  rw [e, Matrix.mul_smul, Matrix.smul_mul, hu.smul_left_cancel]

theorem hfin_smul (R : Type) [CommRing R] [Algebra F R] (J : Matrix (Fin n) (Fin n) E) {k : E} (hk : k ≠ 0) :
    HFin R σ (k • J) = HFin R σ J := by
  have hU : Formalism.UG.UJ (σ : E →+* E) (k • J) = Formalism.UG.UJ (σ : E →+* E) J := by
    have hu : IsUnit k := IsUnit.mk0 k hk
    ext g
    change Formalism.UG.cT _ g.1 * (k • J) * g.1 = k • J ↔ Formalism.UG.cT _ g.1 * J * g.1 = J
    rw [Matrix.mul_smul, Matrix.smul_mul, hu.smul_left_cancel]
  unfold HFin
  rw [hU]

def toJ (J : Matrix (Fin n) (Fin n) E) {k : E} (hk : k ≠ 0) : GAd σ (k • J) ≃* GAd σ J :=
  MulEquiv.subgroupCongr (hr_smul (AF F) J hk)

theorem toJ_val (J : Matrix (Fin n) (Fin n) E) {k : E} (hk : k ≠ 0) (g : GAd σ (k • J)) :
    (toJ J hk g).1 = g.1 := rfl

end GlobalTheory.CuspScale

namespace GlobalTheory.CuspScale

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n : ℕ}

theorem ratPts_iff (J : Matrix (Fin n) (Fin n) E) {k : E} (hk : k ≠ 0) (g : GAd σ (k • J)) :
    g ∈ ratPts σ (k • J) ↔ toJ J hk g ∈ ratPts σ J := by
  change g.1 ∈ HFin (AF F) σ (k • J) ↔ (toJ J hk g).1 ∈ HFin (AF F) σ J
  rw [hfin_smul (AF F) J hk, toJ_val]

end GlobalTheory.CuspScale

namespace GlobalTheory.CuspScale

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n : ℕ}

theorem unipRad_map (J : Matrix (Fin n) (Fin n) E) {k : E} (hk : k ≠ 0) {r : ℕ} (C : Matrix (Fin n) (Fin r) E) :
    (unipRad σ (k • J) C).map (toJ J hk).toMonoidHom = unipRad σ J C := by
  unfold unipRad
  rw [MonoidHom.map_closure]
  congr 1
  ext x
  obtain ⟨y, rfl⟩ := (toJ (σ := σ) J hk).surjective x
  rw [Set.mem_image_iff_of_inverse (f := (toJ J hk).toMonoidHom) (g := (toJ J hk).symm) (fun a => by simp) (fun a => by simp)]
  simp only [Set.mem_setOf_eq, MulEquiv.coe_toMonoidHom, MulEquiv.symm_apply_apply]
  have hm : matHom (AF F) σ J (toJ J hk y) = matHom (AF F) σ (k • J) y := rfl
  have hu : IsUnit (inclR (F := F) (AF F) k) := (IsUnit.mk0 k hk).map _
  have ha : adMat F (Formalism.UG.cT (σ : E →+* E) C * k • J) = inclR (F := F) (AF F) k • adMat F (Formalism.UG.cT (σ : E →+* E) C * J) := by
    rw [Matrix.mul_smul]
    exact Matrix.ext fun i j => map_mul (inclR (F := F) (AF F)) k _
  have hv : ∀ x : Fin n → E, (Formalism.UG.cT (σ : E →+* E) C * k • J) *ᵥ x = 0 ↔ (Formalism.UG.cT (σ : E →+* E) C * J) *ᵥ x = 0 := by
    intro x
    rw [Matrix.mul_smul, Matrix.smul_mulVec, smul_eq_zero, or_iff_right hk]
  rw [hm, ha, Matrix.smul_mul]
  have hz : ∀ M : Matrix (Fin r) (Fin n) (AF F ⊗[F] E), inclR (F := F) (AF F) k • M = 0 ↔ M = 0 := fun M => by
    exact ⟨fun h => hu.smul_left_cancel.1 (h.trans (smul_zero _).symm), fun h => by rw [h, smul_zero]⟩
  simp only [hz, hv]
end GlobalTheory.CuspScale

namespace GlobalTheory.CuspScale

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n : ℕ}

theorem fd_map {G H : Type} [Group G] [Group H] [MeasurableSpace G] [MeasurableSpace H]
    (φ : G ≃* H) (hc : Measurable φ) (hc' : Measurable φ.symm) (Γ : Subgroup G) (Γ' : Subgroup H)
    (hQ : ∀ g, g ∈ Γ ↔ φ g ∈ Γ') (μ : Measure G) (𝓕 : Set G) (h : IsFundamentalDomain Γ 𝓕 μ) :
    IsFundamentalDomain Γ' (φ '' 𝓕) (μ.map φ) := by
  let ψ : G ≃ᵐ H := ⟨φ.toEquiv, hc, hc'⟩
  have hψ : MeasurePreserving ψ μ (μ.map φ) := ⟨ψ.measurable, rfl⟩
  have e : φ '' 𝓕 = φ.symm ⁻¹' 𝓕 := φ.toEquiv.image_eq_preimage_symm 𝓕
  rw [e]
  exact h.preimage_of_equiv (f := φ.symm) (MeasurePreserving.symm ψ hψ).quasiMeasurePreserving
    (e := fun γ => ⟨φ γ, (hQ γ).1 γ.2⟩)
    ⟨fun a b hab => Subtype.ext (φ.injective (congrArg Subtype.val hab)),
      fun b => ⟨⟨φ.symm b, (hQ _).2 (by simp)⟩, Subtype.ext (by simp)⟩⟩
    fun γ y => by
      show φ.symm (φ γ * y) = γ * φ.symm y
      rw [map_mul, φ.symm_apply_apply]

theorem toJ_continuous (J : Matrix (Fin n) (Fin n) E) {k : E} (hk : k ≠ 0) : Continuous (toJ (σ := σ) J hk) :=
  continuous_subtype_val.subtype_mk _

theorem toJ_symm_continuous (J : Matrix (Fin n) (Fin n) E) {k : E} (hk : k ≠ 0) : Continuous (toJ (σ := σ) J hk).symm :=
  continuous_subtype_val.subtype_mk _

def unipJ (J : Matrix (Fin n) (Fin n) E) {k : E} (hk : k ≠ 0) {r : ℕ} (C : Matrix (Fin n) (Fin r) E) :
    unipRad σ (k • J) C ≃ₜ* unipRad σ J C where
  toMulEquiv := ((toJ J hk).subgroupMap _).trans (MulEquiv.subgroupCongr (unipRad_map J hk C))
  continuous_toFun := ((toJ_continuous J hk).comp continuous_subtype_val).subtype_mk _
  continuous_invFun := ((toJ_symm_continuous J hk).comp continuous_subtype_val).subtype_mk _

theorem unipJ_val (J : Matrix (Fin n) (Fin n) E) {k : E} (hk : k ≠ 0) {r : ℕ} (C : Matrix (Fin n) (Fin r) E)
    (u : unipRad σ (k • J) C) : ((unipJ J hk C u : unipRad σ J C) : GAd σ J) = toJ J hk u := rfl

end GlobalTheory.CuspScale

namespace GlobalTheory.CuspScale

theorem isCuspidal_smul : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ)
    (J₀ J₁ : Matrix (Fin n) (Fin n) E) (k : E), k ≠ 0 → J₁ = k • J₀ →
    ∀ (φ₀ : GAd σ J₀ → ℂ) (φ₁ : GAd σ J₁ → ℂ), (∀ (g : GAd σ J₀) (g' : GAd σ J₁), g.1 = g'.1 → φ₁ g' = φ₀ g) →
      IsCuspidal σ J₀ φ₀ → IsCuspidal σ J₁ φ₁ := by
  intro F E _ _ _ _ _ σ n J₀ J₁ k hk hJ φ₀ φ₁ hφ hc
  subst hJ
  rintro r C ⟨hr, hli, hiso⟩ μ 𝓕 hμ hF g
  have hiso₀ : Formalism.UG.cT (σ : E →+* E) C * J₀ * C = 0 := by
    rw [Matrix.mul_smul, Matrix.smul_mul, smul_eq_zero] at hiso
    exact hiso.resolve_left hk
  let e' := unipJ (σ := σ) J₀ hk C
  have hQ : ∀ u, u ∈ (ratPts σ (k • J₀)).subgroupOf (unipRad σ (k • J₀) C) ↔
      e' u ∈ (ratPts σ J₀).subgroupOf (unipRad σ J₀ C) := by
    intro u
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf, unipJ_val]
    exact ratPts_iff J₀ hk (u : GAd σ (k • J₀))
  have hF' := fd_map e'.toMulEquiv e'.continuous.measurable e'.symm.continuous.measurable _ _ hQ μ 𝓕 hF
  have hH : (μ.map e').IsHaarMeasure := ContinuousMulEquiv.isHaarMeasure_map μ e'
  have h0 := hc r C ⟨hr, hli, hiso₀⟩ (μ.map e') (e' '' 𝓕) hH hF' (toJ J₀ hk g)
  let ψ : unipRad σ (k • J₀) C ≃ᵐ unipRad σ J₀ C := ⟨e'.toEquiv, e'.continuous.measurable, e'.symm.continuous.measurable⟩
  have hψ : MeasurePreserving ψ μ (μ.map e') := ⟨ψ.measurable, rfl⟩
  have himg := hψ.setIntegral_image_emb ψ.measurableEmbedding (fun v => φ₀ ((v : GAd σ J₀) * toJ J₀ hk g)) 𝓕
  rw [← h0]
  refine Eq.trans ?_ himg.symm
  congr 1
  funext u
  refine hφ _ _ ?_
  show ((toJ J₀ hk) (↑u) * (toJ J₀ hk) g).1 = (↑u * g).1
  rw [← map_mul]
  rfl

end GlobalTheory.CuspScale
