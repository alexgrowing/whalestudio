import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ValLast
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.PureTensorLIntertwine
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.OmPureTensorOOfFinite
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousOnAtTau
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HeisenbergCombinationCommFockPolynomialVectorsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilDatumRealPlacesFockVacuumCharacter
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIdeleAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsEtaTildeUnramified
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Classical

open scoped ComplexOrder

namespace GlobalTheory.CenterVac

variable {D : D7}

theorem lintegral_enorm_sq_eq_one {α : Type} [MeasurableSpace α] {μ : Measure α} {s : Set α} {f : α → ℂ}
    (h : ∫ w in s, ‖f w‖ ^ 2 ∂μ = 1) : ∫⁻ w in s, ‖f w‖ₑ ^ 2 ∂μ = 1 := by
  have hint : Integrable (fun w => ‖f w‖ ^ 2) (μ.restrict s) :=
    Integrable.of_integral_ne_zero (by rw [h]; exact one_ne_zero)
  have e := ofReal_integral_eq_lintegral_ofReal hint (ae_of_all _ fun w => by positivity)
  rw [h, ENNReal.ofReal_one] at e
  rw [e]
  refine lintegral_congr fun w => ?_
  rw [← ofReal_norm_eq_enorm, ENNReal.ofReal_pow (norm_nonneg _)]

theorem om_vac_eq_smul {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} (hθ : IsInfFam θ) {S T : HSp D} {x : DefSp S}
    {y : DefSp T} (hx : x.Is) (hy : y.Is) {k : KerDat S T} (hk : k.Is ψ θ x y) {z : GA D S} (hz : z ∈ GinfC S) :
    ∃ c : ℂ, ‖c‖ = 1 ∧ k.om (z, 1) k.vac = c • k.vac := by
  obtain ⟨χS, χT, hom⟩ := hk.weil
  obtain ⟨hψ, hv⟩ := hk.vac
  obtain ⟨η, hη⟩ := GlobalTheory.WeilParts.exists_isEtaTilde_unramified D
  have hdet : ∀ τ, (gramAt D S τ).det ≠ 0 := fun τ h0 => by
    have := (hx.cart τ).2.2.det_pos.ne'
    rw [Matrix.det_mul, h0, zero_mul] at this
    exact this rfl
  obtain ⟨r, hr, -⟩ := GlobalTheory.VacuumCharacter.exists_root hθ S hdet z hz
  have hy1 : IsDetRoot T 1 1 := by
    show _ = _
    rw [Units.val_one, RingHom.map_one, mul_one]
    exact (Matrix.det_one).symm
  have one : ∀ τ, compAt θ τ (Formalism.L2.Theta.mt T 1) = 1 := fun τ => GlobalTheory.PointAtPlaceHom.infMat_one T _
  obtain ⟨a, ha⟩ : ∃ a : ℂ, k.om (z, 1) k.vac = a • k.vac :=
    ⟨_, GlobalTheory.WeilVacChar.vacuum_character D ψ hψ S T θ hθ χS χT k.om η hη hom x.s y.s hx.cart hy.cart z hz 1 (one_mem _)
      (fun τ => by rcases hx.pm τ with h | h <;> rw [h] <;> simp) (fun τ => by rw [one, one_mul, mul_one]) r 1 hr hy1
      k.vac hv.theta hv.fock⟩
  refine ⟨a, ?_, ha⟩
  obtain ⟨⟨p, hp⟩, hn⟩ := hv.norm
  have n1 : nrm2 p.1 p.2 k.vac = 1 := hn p hp
  obtain ⟨hH, hF, -⟩ := hp
  have hu := hom.om_unit p.1 p.2 hH hF (z, 1) k.vac hv.theta
  have hL := lintegral_enorm_sq_eq_one (μ := p.1) (s := p.2) (f := k.vac) n1
  rw [ha] at hu
  simp only [Pi.smul_apply, smul_eq_mul, enorm_mul, mul_pow] at hu
  rw [lintegral_const_mul' _ _ (by simp), hL, mul_one] at hu
  rw [← ofReal_norm_eq_enorm, ← ENNReal.ofReal_pow (norm_nonneg _), ENNReal.ofReal_eq_one] at hu
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg a) two_ne_zero).1 hu

theorem exists_center_char : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D), IsInfFam θ → ∀ (S T : HSp D) (x : DefSp S) (y : DefSp T), x.Is → y.Is → ∀ k : KerDat S T, k.Is ψ θ x y → ∃ c : GA D S → ℂ, ∀ z ∈ GinfC S, z ∈ Subgroup.center (GA D S) → ‖c z‖ = 1 ∧ k.om (z, 1) k.vac = c z • k.vac := by
  intro D ψ θ hθ S T x y hx hy k hk
  have h : ∀ z : GA D S, ∃ c : ℂ, z ∈ GinfC S → ‖c‖ = 1 ∧ k.om (z, 1) k.vac = c • k.vac := fun z => by
    by_cases hz : z ∈ GinfC S
    · obtain ⟨c, hc⟩ := om_vac_eq_smul hθ hx hy hk hz
      exact ⟨c, fun _ => hc⟩
    · exact ⟨1, fun h' => absurd h' hz⟩
  choose c hc using h
  exact ⟨c, fun z hz _ => hc z hz⟩

end GlobalTheory.CenterVac
