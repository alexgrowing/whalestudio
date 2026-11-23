import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EisAtMinusRho
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoreConcl
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTransv
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRationalPointSwappingFirstColumnsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeightInvariantUnderStabilizerStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BruhatCellRationalDecompositionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnipotentStabilizerTrivialStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnipotentStabilizerDoubleCosetStatement
open scoped TensorProduct NNReal Matrix
open NumberField MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.EisRes
open GlobalTheory.Doubling (absE)

noncomputable section
namespace GlobalTheory.EisBig
open GlobalTheory.EisCT

theorem unfold_fd {N : Type} [Group N] [TopologicalSpace N] [IsTopologicalGroup N] [MeasurableSpace N] [BorelSpace N]
    [SecondCountableTopology N] (Γ : Subgroup N) [Countable Γ] (μ : Measure N) [μ.IsHaarMeasure] (𝓕 : Set N)
    (h𝓕 : IsFundamentalDomain Γ 𝓕 μ) (Φ : N → ℂ) (hΦ : Integrable Φ μ) :
    IntegrableOn (fun u => ∑' γ : Γ, Φ (γ.1 * u)) 𝓕 μ ∧ ∫ u in 𝓕, ∑' γ : Γ, Φ (γ.1 * u) ∂μ = ∫ u, Φ u ∂μ := by
  have hmp : ∀ γ : Γ, MeasurePreserving (fun u : N => γ.1 * u) μ μ := fun γ => measurePreserving_smul γ μ
  have hi : ∀ γ : Γ, Integrable (fun u => Φ (γ.1 * u)) μ := fun γ =>
    (hmp γ).integrable_comp_of_integrable hΦ
  have hl : ∑' γ : Γ, ∫⁻ u in 𝓕, ‖Φ (γ.1 * u)‖ₑ ∂μ = ∫⁻ u, ‖Φ u‖ₑ ∂μ :=
    (h𝓕.lintegral_eq_tsum'' (fun u => ‖Φ u‖ₑ)).symm
  have hfin : ∑' γ : Γ, ∫⁻ u in 𝓕, ‖Φ (γ.1 * u)‖ₑ ∂μ ≠ ⊤ := by
    rw [hl]; exact hΦ.2.ne
  refine ⟨⟨(AEMeasurable.tsum fun γ => (hi γ).aemeasurable.restrict).aestronglyMeasurable, ?_⟩, ?_⟩
  · refine lt_of_le_of_lt (lintegral_mono fun u => enorm_tsum_le_tsum_enorm) ?_
    rw [lintegral_tsum fun γ => (hi γ).aemeasurable.restrict.enorm]
    exact lt_top_iff_ne_top.2 hfin
  · rw [integral_tsum (fun γ => (hi γ).aestronglyMeasurable.restrict) hfin, h𝓕.integral_eq_tsum'' Φ hΦ]
    rfl

theorem stabL_mul {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (x : Matrix (Fin n) (Fin 1) E) {p q : GAd σ J}
    (hp : StabL σ J x p) (hq : StabL σ J x q) : StabL σ J x (p * q) := by
  obtain ⟨l, hl⟩ := hp
  obtain ⟨m, hm⟩ := hq
  refine ⟨l * m, ?_⟩
  rw [map_mul, Units.val_mul, Matrix.mul_assoc, hm, Matrix.mul_smul, hl, smul_smul, Units.val_mul, mul_comm]

theorem stabL_inv {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (x : Matrix (Fin n) (Fin 1) E) {p : GAd σ J}
    (hp : StabL σ J x p) : StabL σ J x p⁻¹ := by
  obtain ⟨l, hl⟩ := hp
  refine ⟨l⁻¹, ?_⟩
  have h1 : (matHom _ σ J p⁻¹).1 * (matHom _ σ J p).1 = 1 := by
    rw [← Units.val_mul, ← map_mul, inv_mul_cancel, map_one, Units.val_one]
  calc (matHom _ σ J p⁻¹).1 * adMat F x
      = (l⁻¹ : (AF F ⊗[F] E)ˣ).1 • ((matHom _ σ J p⁻¹).1 * (l.1 • adMat F x)) := by
        rw [Matrix.mul_smul, smul_smul, Units.inv_mul, one_smul]
    _ = (l⁻¹ : (AF F ⊗[F] E)ˣ).1 • adMat F x := by
        rw [← hl, ← Matrix.mul_assoc, h1, Matrix.one_mul]

theorem bigCell_constTerm : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ)
    (J : Matrix (Fin n) (Fin n) E) (r : ℕ) (X Y : Matrix (Fin n) (Fin (r + 1)) E) (L : Submodule (𝓞 E) (Fin n → E))
    (a : GL (Fin n) (AF F ⊗[F] E)) (h : GAd σ J → ℝ) (Eis : ℂ → GAd σ J → ℂ) (c : ℂ → ℂ), HidaSetting σ J X Y L a h → EisensteinHyp σ J (col0 X) (col0 Y) h Eis c →
    ∀ T, GlobalTheory.EisCT.IsTransv σ J (col0 X) T → ∀ (μ : Measure (unipRad σ J (col0 X))) (𝓕 : Set (unipRad σ J (col0 X))), μ.IsHaarMeasure →
      IsFundamentalDomain ((ratPts σ J).subgroupOf (unipRad σ J (col0 X))) 𝓕 μ → μ 𝓕 = 1 →
    ∀ s : ℂ, ((n : ℝ) - 1) / 2 < s.re → ∀ g : GAd σ J,
    IntegrableOn (fun u : unipRad σ J (col0 X) => GlobalTheory.EisCT.bigSum σ J (col0 X) T h s (u.1 * g)) 𝓕 μ ∧
    ∫ u in 𝓕, GlobalTheory.EisCT.bigSum σ J (col0 X) T h s (u.1 * g) ∂μ = c s * (h g : ℂ) ^ (-s + (((n : ℂ) - 1) / 2)) := by
  intro F E _ _ _ _ _ σ n J r X Y L a h Eis c hS hP T hT μ 𝓕 hμ h𝓕 h1 s hs g
  obtain ⟨hCM, hS2, hJ, hS4, hW, hS6, hS7⟩ := hS
  obtain ⟨w, hw, hwy⟩ := GlobalTheory.T.exists_rational_point_swapping_first_columns F E σ n J r X Y hCM hJ hW
  have huq : ∀ (γ : GAd σ J) (ν ν' : (ratPts σ J).subgroupOf (unipRad σ J (col0 X))),
      StabL σ J (col0 X) (w * ν.1.1 * γ⁻¹) → StabL σ J (col0 X) (w * ν'.1.1 * γ⁻¹) → ν = ν' := by
    intro γ ν ν' h1 h2
    have h3 := stabL_mul σ J (col0 X) h1 (stabL_inv σ J (col0 X) h2)
    have h4 : w * ν.1.1 * γ⁻¹ * (w * ν'.1.1 * γ⁻¹)⁻¹ = w * (ν.1.1 * ν'.1.1⁻¹) * w⁻¹ := by group
    rw [h4] at h3
    have := GlobalTheory.T.unipotent_stabilizer_trivial F E σ n J r X Y hCM hJ hW w hw hwy _ (mul_mem ν.1.2 (inv_mem ν'.1.2)) h3
    exact Subtype.ext (Subtype.ext (mul_inv_eq_one.1 this))
  have hex : ∀ t : bigSet σ J (col0 X) T, ∃ ν : (ratPts σ J).subgroupOf (unipRad σ J (col0 X)),
      StabL σ J (col0 X) (w * ν.1.1 * t.1.1⁻¹) :=
    fun t => GlobalTheory.T.bruhat_cell_rational_decomposition F E σ n J r X Y hCM hJ hW w hw hwy t.1.1 t.1.2 t.2.2
  have hwν : ∀ ν : (ratPts σ J).subgroupOf (unipRad σ J (col0 X)), w * ν.1.1 ∈ ratPts σ J := fun ν =>
    mul_mem hw (Subgroup.mem_subgroupOf.1 ν.2)
  have hrep : ∀ ν : (ratPts σ J).subgroupOf (unipRad σ J (col0 X)),
      ∃ t : ratPts σ J, t ∈ T ∧ StabL σ J (col0 X) (w * ν.1.1 * t.1⁻¹) := fun ν =>
    (hT ⟨_, hwν ν⟩).exists
  let e : bigSet σ J (col0 X) T ≃ (ratPts σ J).subgroupOf (unipRad σ J (col0 X)) :=
    { toFun := fun t => (hex t).choose
      invFun := fun ν => ⟨(hrep ν).choose, (hrep ν).choose_spec.1,
        GlobalTheory.T.unipotent_stabilizer_double_coset F E σ n J r X Y hCM hJ hW w hw hwy _ ν.1.2 _ (hrep ν).choose_spec.2⟩
      left_inv := fun t => by
        apply Subtype.ext
        exact (hT ⟨_, hwν _⟩).unique (hrep _).choose_spec ⟨t.2.1, (hex t).choose_spec⟩
      right_inv := fun ν => huq _ _ _ (hex _).choose_spec (hrep ν).choose_spec.2 }
  have he : ∀ (t : bigSet σ J (col0 X) T) (v : GAd σ J), h (t.1.1 * v) = h (w * (e t).1.1 * v) := by
    intro t v
    have hp : w * (e t).1.1 * t.1.1⁻¹ ∈ ratPts σ J := mul_mem (hwν _) (inv_mem t.1.2)
    have := GlobalTheory.T.height_invariant_under_stabilizer F E σ n J r X Y L a h ⟨hCM, hS2, hJ, hS4, hW, hS6, hS7⟩ _ hp (hex t).choose_spec (t.1.1 * v)
    rw [← this]
    congr 1
    group
  obtain ⟨hint, heq⟩ := hP.2.1 w hw hwy μ 𝓕 hμ h𝓕 h1 s hs g
  set Φ : unipRad σ J (col0 X) → ℂ := fun u => (h (w * u.1 * g) : ℂ) ^ (s + ((n : ℂ) - 1) / 2) with hΦ
  have key : ∀ u : unipRad σ J (col0 X), bigSum σ J (col0 X) T h s (u.1 * g) =
      ∑' ν : (ratPts σ J).subgroupOf (unipRad σ J (col0 X)), Φ (ν.1 * u) := by
    intro u
    unfold bigSum
    rw [← e.symm.tsum_eq]
    refine tsum_congr fun ν => ?_
    unfold fs
    rw [hΦ, he (e.symm ν) (u.1 * g), e.apply_symm_apply]
    show (h (w * ν.1.1 * (u.1 * g)) : ℂ) ^ _ = (h (w * (ν.1.1 * u.1) * g) : ℂ) ^ _
    rw [mul_assoc, mul_assoc, mul_assoc]
  have hkey : (fun u : unipRad σ J (col0 X) => bigSum σ J (col0 X) T h s (u.1 * g)) =
      fun u => ∑' ν : (ratPts σ J).subgroupOf (unipRad σ J (col0 X)), Φ (ν.1 * u) := funext key
  obtain ⟨i1, i2⟩ := unfold_fd _ μ 𝓕 h𝓕 Φ hint
  rw [hkey]
  exact ⟨i1, i2.trans heq⟩

end GlobalTheory.EisBig

end
