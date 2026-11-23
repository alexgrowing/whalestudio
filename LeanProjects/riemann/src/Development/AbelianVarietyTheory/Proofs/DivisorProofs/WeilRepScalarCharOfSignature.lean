import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocPt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EvFinMkPt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalVacuumEigenLatticeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.VacuumEigenAtAllPlacesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzAdelicSliceSmoothStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilRepSliceFiniteOpStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.VacuumUniqueProductEigenStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.VacuumProductExistsNonzeroStatement

noncomputable section

open scoped TensorProduct
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.FinComm GlobalTheory.VacLine

namespace GlobalTheory.VacLine

theorem vac_line : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    (B : Base F E) {n d : ℕ} (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (r s r' s' : ℕ),
    B.IsGood σ → X.IsHerm σ B r s → W.IsSkew σ B r' s' → M.IsGood B.ψ →
    ∀ c : Pl F → Matrix (Fin n) (Fin d) (AE F E) → ℂ,
      (∀ v, ∀ γ ∈ latAtV X W v, ∀ f : SInf F (Fin n × Fin d), M.co.rho B.ψ γ (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f M.vac) = c v γ • GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f M.vac) →
      ∀ Ψ ∈ schA F (Fin n × Fin d), (∀ v, ∀ γ ∈ latAtV X W v, M.co.rho B.ψ γ Ψ = c v γ • Ψ) →
        ∃ f₁ : SInf F (Fin n × Fin d), Ψ = GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f₁ M.vac := by
  intro F E _ _ _ _ _ σ B n d X W M r s r' s' hB hX hW hM c hc Ψ hΨ hΨc
  have hstd : ∀ᶠ v in cofinite, M.vac v = indO v := by
    filter_upwards [hM.std] with u hu
    rw [hu]
    rfl
  have hveig := GlobalTheory.T.vacuum_eigen_at_all_places M B.ψ hM c hc
  let Q : ∀ v : Pl F, Set (((Fin n × Fin d → Fv F v) × (Fin n × Fin d → Fv F v)) × ℂ) :=
    fun v => {q | ∃ γ ∈ latAtV X W v, q = (locPt v (M.co.e γ), c v γ)}
  have hline : ∀ v, ∀ φ ∈ SB (Fin n × Fin d → Fv F v), (∀ q ∈ Q v, locOp B.ψ v q.1 φ = q.2 • φ) →
      ∃ a : ℂ, φ = a • M.vac v := by
    intro v φ hφ hq
    refine GlobalTheory.T.local_vacuum_eigen_lattice B X W M r s r' s' hB hX hW hM v (c v) (hveig v) φ hφ fun γ hγ => ?_
    exact hq (locPt v (M.co.e γ), c v γ) ⟨γ, hγ, rfl⟩
  obtain ⟨y₀, hy₀⟩ := GlobalTheory.T.vacuum_product_exists_nonzero M.vac (fun v => (hM.vac v).2.1) hstd
  obtain ⟨hF, hSB⟩ := GlobalTheory.T.schwartz_adelic_slice_smooth Ψ hΨ
  obtain ⟨f₀, hf₀⟩ := hF y₀
  have heig : ∀ x, ∀ v, ∀ q ∈ Q v, finOp B.ψ v q.1 (slice Ψ x) = q.2 • slice Ψ x := by
    intro x v q hq
    obtain ⟨γ, hγ, rfl⟩ := hq
    rw [← GlobalTheory.T.weil_rep_slice_finite_op M B.ψ v γ (at_latAtV hγ) Ψ x, hΨc v γ hγ]
    rfl
  have hfac : ∀ x, ∃ a : ℂ, slice Ψ x = a • vacProd M.vac := fun x =>
    GlobalTheory.T.vacuum_unique_product_eigen B.ψ M.vac Q (fun v => (hM.vac v).1) (fun v => (hM.vac v).2.1) hstd hline (slice Ψ x) (hSB x) (heig x)
  choose a ha using hfac
  refine ⟨(vacProd M.vac y₀)⁻¹ • f₀, ?_⟩
  funext z
  have hz := mkPt_eq z
  have h1 : Ψ (mkPt (fun i => evI F (z i)) (fun i => (z i).2)) =
      a (fun i => evI F (z i)) * vacProd M.vac (fun i => (z i).2) := congrFun (ha _) _
  have h2 : f₀ (fun i => evI F (z i)) = a (fun i => evI F (z i)) * vacProd M.vac y₀ := by
    rw [← hf₀]; exact congrFun (ha _) y₀
  rw [← hz, pure_mkPt, h1, SchwartzMap.smul_apply, h2, smul_eq_mul]
  field_simp

end GlobalTheory.VacLine
