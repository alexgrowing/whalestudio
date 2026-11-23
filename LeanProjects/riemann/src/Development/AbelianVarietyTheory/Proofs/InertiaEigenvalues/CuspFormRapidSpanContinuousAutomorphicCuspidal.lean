import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WtOfLastRowOfDetPow
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsEqColGenMulBlkU
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ContinuousOfMemSmoothSpan
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsPsiLocNeOne
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CuspFormRapidKernelSmoothSpanSmoothCuspidalBound
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsEquivariantProj
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsMirabolicWhittakerStageOfIsCuspForm
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsUnitaryOfCharIff
open NumberField IsDedekindDomain MeasureTheory GlobalTheory.CuspRep GlobalTheory.RSJ GlobalTheory.MirTower GlobalTheory.CuspGeneric Formalism.L2.Host
open scoped ENNReal NNReal ComplexConjugate

noncomputable section

namespace GlobalTheory.JSW.SpanProps

theorem avg_eq_zero {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ} {F : GA E a → ℂ}
    (hcont : Continuous F) (hleft : ∀ γ g, F (ratGL E a γ * g) = F g) (hc : IsCuspidal F)
    (r : ℕ) (hr : 0 < r) (hra : r ≤ a - 1) (g : GA E a) :
    avg (ratV E (UnipotentBlockColumnIndex a r (a - 1))) (fun x => F (blkU x * g)) = 0 := by
  have hra' : r < a := by omega
  have hper := per_blk (E := E) (r := r) (m := a - 1) hcont (fun c g => hleft _ g) g
  have hper2 : Per (ratN E a r) (fun x => F (blkU (blkIxHomeo r x) * g)) :=
    ⟨hper.1.comp (blkIxHomeo r).continuous, fun γ hγ x => by
      simp only [map_add]
      exact hper.2 _ ((blkIxHomeo_mem r γ).2 hγ) _⟩
  have key := GlobalTheory.T.quotientAverage_map_lattice_equiv _ _ (ratN E a r) (ratV E _) (isCoLat_ratV E (BlockIx a r))
    (isCoLat_ratV E _) (blkIxHomeo r) (blkIxHomeo_mem r) _ hper
  rw [← key]
  have hfun : (fun x => F (blkU (blkIxHomeo r x) * g)) = fun x => F (unip x * g) :=
    funext fun x => by rw [← blkU_comp_equiv]; rfl
  rw [hfun] at hper2 ⊢
  letI : MeasurableSpace (BlockIx a r → Ad E) := borel _
  haveI : BorelSpace (BlockIx a r → Ad E) := ⟨rfl⟩
  obtain ⟨μ, 𝓕, hμ, hF, h1⟩ := GlobalTheory.T.exists_fundamentalDomain_mass_one_cocompactLattice _ (ratN E a r) (isCoLat_ratV E (BlockIx a r))
  obtain ⟨-, -, -, hint⟩ := GlobalTheory.T.setIntegral_fundamentalDomain_eq_mass_mul_average _ _ (isCoLat_ratV E (BlockIx a r)) μ 𝓕 hμ hF _ hper2
  have hc' := hc r hr hra' μ 𝓕 hμ hF g
  rw [hint, h1] at hc'
  simp only [ENNReal.toReal_one, Complex.ofReal_one, one_mul] at hc'
  exact hc'

end GlobalTheory.JSW.SpanProps

theorem GlobalTheory.JSW.mspanR_cont_left_avg : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (m : ℕ) (π : CuspSub E (m + 1))
    (ω : HChar E), ω.IsUnitary → π.HasCentChar ω → ∀ φ ∈ GlobalTheory.JSW.mspanR π, Continuous φ ∧
    (∀ γ g, φ (ratGL E (m + 1) γ * g) = φ g) ∧
    ∀ r, 0 < r → r ≤ m → ∀ g, avg (ratV E (UnipotentBlockColumnIndex (m + 1) r m)) (fun x => φ (blkU x * g)) = 0 := by
  intro E _ _ _ m π ω hω hc F hF
  have hπ : π.IsUnitary := ⟨ω, hω, CuspSub.hasCentral_iff.2 hc⟩
  obtain ⟨ψ, rfl, h⟩ := GlobalTheory.JSW.mspanR_words GlobalTheory.CuspOrth.cuspFormsBounded hπ F hF
  have h0 := (h []).2
  rw [GlobalTheory.JSW.word_nil] at h0
  refine ⟨h0.cont, h0.left, fun r hr hrm g => ?_⟩
  exact GlobalTheory.JSW.SpanProps.avg_eq_zero (a := m + 1) h0.cont h0.left h0.cusp r hr hrm g
