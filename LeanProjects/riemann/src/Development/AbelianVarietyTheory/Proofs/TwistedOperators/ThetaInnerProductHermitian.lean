import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RestrictedTensorBasePointNormSq
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsIntOv
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaSquareIntegrable
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.AeZeroOfSmall

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting GlobalTheory.PlaceTensor
open scoped TensorProduct ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ThetaPairingLaws

theorem ipO_self {D : D7} {m n : ℕ} (μ : Measure (Mx D m n)) (𝓕 : Set (Mx D m n)) (f : Mx D m n → ℂ) :
    ipO μ 𝓕 f f = (nrm2 μ 𝓕 f : ℂ) := by
  unfold ipO nrm2
  rw [← integral_complex_ofReal]
  congr 1
  funext w
  rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]

private theorem countable_ratL' {D : D7} (S T : HSp D) : Countable ↥(ratL T S) := by
  haveI : Countable D.host.E := Finsupp.Countable.of_moduleFinite (R := ℚ) (M := D.host.E)
  haveI : Countable (Matrix (Fin T.rank) (Fin S.rank) D.host.E) :=
    inferInstanceAs (Countable (Fin T.rank → Fin S.rank → D.host.E))
  have h : (ratL T S : Set (WO S T)).Countable := by
    rw [ratL, AddMonoidHom.coe_range]
    exact Set.countable_range _
  exact h.to_subtype

theorem ipO_laws : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (μ : Measure (WO S T)) (𝓕 : Set (WO S T)), IsStdChar D ψ (-1) → IsCovolOne (ratL T S) μ 𝓕 → ∀ f g : WO S T → ℂ, IsThetaFunO ψ S T f → IsThetaFunO ψ S T g → IntegrableOn (fun w => f w * (starRingEnd ℂ) (g w)) 𝓕 μ ∧ ipO μ 𝓕 g f = (starRingEnd ℂ) (ipO μ 𝓕 f g) ∧ (∀ c : ℂ, ipO μ 𝓕 (c • f) g = c * ipO μ 𝓕 f g ∧ ipO μ 𝓕 f (c • g) = (starRingEnd ℂ) c * ipO μ 𝓕 f g) ∧ (∀ f', IsThetaFunO ψ S T f' → ipO μ 𝓕 (f + f') g = ipO μ 𝓕 f g + ipO μ 𝓕 f' g ∧ ipO μ 𝓕 g (f + f') = ipO μ 𝓕 g f + ipO μ 𝓕 g f') ∧ ipO μ 𝓕 f f = (nrm2 μ 𝓕 f : ℂ) ∧ (nrm2 μ 𝓕 f = 0 → f = 0) ∧ (∀ w, ipO μ 𝓕 (heisO ψ S T w f) (heisO ψ S T w g) = ipO μ 𝓕 f g ∧ ipO μ 𝓕 (heisO ψ S T w f) g = ipO μ 𝓕 f (heisO ψ S T (-w) g)) ∧ ∀ μ' 𝓕', IsCovolOne (ratL T S) μ' 𝓕' → ipO μ' 𝓕' f g = ipO μ 𝓕 f g := by
  intro D ψ S T μ 𝓕 hψ hμ f g hf hg
  have hμ₀ := hμ
  unfold IsCovolOne at hμ₀
  obtain ⟨hHaar, hFD, -⟩ := hμ₀
  haveI := hHaar
  obtain ⟨-, hL2⟩ := GlobalTheory.ThetaSquare.theta_square_integrable D S T
  obtain ⟨hSq, hHeis, -⟩ := hL2 ψ hψ
  obtain ⟨-, hInvol, hPres, hUnit, -⟩ := hHeis
  obtain ⟨-, -, ⟨-, hHL⟩, -⟩ := (GlobalTheory.ThetaAllChar.thetaFacts D).std hψ S T

  have hInt : ∀ a b : WO S T → ℂ, IsThetaFunO ψ S T a → IsThetaFunO ψ S T b →
      IntegrableOn (fun w => a w * (starRingEnd ℂ) (b w)) 𝓕 μ :=
    fun a b ha hb => (hHL μ μ 𝓕 𝓕 hμ hμ a b ha hb).2.1
  refine ⟨hInt f g hf hg, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  ·
    unfold ipO
    rw [← integral_conj]
    congr 1
    funext w
    rw [map_mul, Complex.conj_conj, mul_comm]
  · intro c
    constructor
    · unfold ipO
      rw [← integral_const_mul]
      congr 1
      funext w
      simp only [Pi.smul_apply, smul_eq_mul]
      ring
    · unfold ipO
      rw [← integral_const_mul]
      congr 1
      funext w
      simp only [Pi.smul_apply, smul_eq_mul, map_mul]
      ring
  · intro f' hf'
    constructor
    · unfold ipO
      rw [← integral_add (hInt f g hf hg) (hInt f' g hf' hg)]
      congr 1
      funext w
      simp only [Pi.add_apply]
      ring
    · unfold ipO
      rw [← integral_add (hInt g f hg hf) (hInt g f' hg hf')]
      congr 1
      funext w
      simp only [Pi.add_apply, map_add]
      ring
  · exact ipO_self μ 𝓕 f
  ·

    intro h0
    haveI := countable_ratL' S T
    haveI : BorelSpace (WO S T) := ⟨rfl⟩
    haveI : MeasurableConstVAdd ↥(ratL T S) (WO S T) := ⟨fun γ => measurable_const_add (γ : WO S T)⟩
    haveI : VAddInvariantMeasure ↥(ratL T S) (WO S T) μ :=
      ⟨fun γ s _ => measure_preimage_add μ (γ : WO S T) s⟩
    unfold nrm2 at h0
    have hI : IntegrableOn (fun w => ‖f w‖ ^ 2) 𝓕 μ := by
      refine (hInt f f hf hf).norm.congr (Filter.Eventually.of_forall fun w => ?_)
      simp only [norm_mul, Complex.norm_conj, sq]
    have hae : (fun w => ‖f w‖ ^ 2) =ᵐ[μ.restrict 𝓕] 0 :=
      (integral_eq_zero_iff_of_nonneg (fun w => sq_nonneg ‖f w‖) hI).1 h0
    have hae' : ∀ᵐ w ∂μ.restrict 𝓕, f w = 0 :=
      hae.mono fun w hw => by simpa using hw
    have htopen : IsOpen {x : WO S T | f x ≠ 0} := isOpen_ne_fun hf.cont continuous_const
    have hts : μ ({x : WO S T | f x ≠ 0} ∩ 𝓕) = 0 := by
      rw [← Measure.restrict_apply₀' hFD.nullMeasurableSet]
      exact ae_iff.1 hae'
    have hzero : μ {x : WO S T | f x ≠ 0} = 0 := by
      refine hFD.measure_zero_of_invariant _ (fun γ => ?_) hts
      ext y
      rw [Set.mem_vadd_set_iff_neg_vadd_mem]
      change f ((↑(-γ) : WO S T) + y) ≠ 0 ↔ f y ≠ 0
      rw [← norm_ne_zero_iff, (hSq f hf).1 (↑(-γ)) (-γ).2 y, norm_ne_zero_iff]
    have hempty := (htopen.measure_eq_zero_iff μ).1 hzero
    funext x
    by_contra hx
    have hmem : x ∈ {x : WO S T | f x ≠ 0} := hx
    rw [hempty] at hmem
    exact hmem
  · intro w
    refine ⟨hUnit μ 𝓕 hHaar hFD w f g hf hg, ?_⟩
    have hg' : IsThetaFunO ψ S T (heisO ψ S T (-w) g) := hPres (-w) g hg
    have e := hInvol (-w) g
    rw [neg_neg] at e
    calc ipO μ 𝓕 (heisO ψ S T w f) g
        = ipO μ 𝓕 (heisO ψ S T w f) (heisO ψ S T w (heisO ψ S T (-w) g)) := by rw [e]
      _ = ipO μ 𝓕 f (heisO ψ S T (-w) g) := hUnit μ 𝓕 hHaar hFD w f _ hf hg'
  ·
    intro μ' 𝓕' h'
    have a := (hHL μ' μ 𝓕' 𝓕 h' hμ f g hf hg).2.2
    have b := (hHL μ μ 𝓕 𝓕 hμ hμ f g hf hg).2.2
    simp only [GlobalTheory.IndefiniteRowSideFullHecke.RealDirectionThetaNonzero.heisO_apply_zero] at a b
    unfold ipO
    rw [a, b]

end GlobalTheory.ThetaPairingLaws
