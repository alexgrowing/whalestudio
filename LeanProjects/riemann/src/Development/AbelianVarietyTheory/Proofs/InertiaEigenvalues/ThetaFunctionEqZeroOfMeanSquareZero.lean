import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LengthPosOfPosDef
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AdjFormula
import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchurLemmaThetaFunctionsOrientedPair
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsDescendPeriodicTrig

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RawLift

open scoped ContDiff

namespace GlobalTheory.ThetaSchurBdd

variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D}

theorem psi_ne_zero (hψ : IsStdChar D ψ (-1)) (a : AF D.host.F) : ψ a ≠ 0 := fun h => by
  have := hψ.1.2.1 a
  rw [h, norm_zero] at this
  exact zero_ne_one this

theorem isTheta_star_mul_mul (hψ : IsStdChar D ψ (-1)) {g h f : WO S T → ℂ} (hg : IsThetaFunO ψ S T g)
    (hh : IsThetaFunO ψ S T h) (hf : IsThetaFunO ψ S T f) :
    IsThetaFunO ψ S T (fun x => star (g x) * h x * f x) where
  quasi γ w := by
    rw [hg.quasi, hh.quasi, hf.quasi, star_mul']
    linear_combination (star (g w) * h w * f w * ψ (-(symplOH S T (ratW T S γ) w))) *
      GlobalTheory.ThetaSchur.mul_star_psi hψ (-(symplOH S T (ratW T S γ) w))
  level := by
    obtain ⟨U1, o1, h1⟩ := hg.level
    obtain ⟨U2, o2, h2⟩ := hh.level
    obtain ⟨U3, o3, h3⟩ := hf.level
    refine ⟨U1 ⊓ U2 ⊓ U3, (o1.inter o2).inter o3, fun u hu hfin => ?_⟩
    funext x
    have e1 := congrFun (h1 u hu.1.1 hfin) x
    have e2 := congrFun (h2 u hu.1.2 hfin) x
    have e3 := congrFun (h3 u hu.2 hfin) x
    simp only [heisO] at e1 e2 e3 ⊢
    have hs := GlobalTheory.ThetaSchur.mul_star_psi hψ (symplOH S T x u)
    rw [← e1, ← e2, ← e3, star_mul']
    linear_combination (-(ψ (symplOH S T x u) * (star (g (x + u)) * h (x + u) * f (x + u)))) * hs
  cont := (hg.cont.star.mul hh.cont).mul hf.cont
  smooth k L hL hL0 w := by
    have hs : ContDiff ℝ ∞ (fun t => star (g (w + L t))) :=
      Complex.conjCLE.contDiff.comp (hg.smooth k L hL hL0 w)
    exact ContDiff.mul (ContDiff.mul hs (hh.smooth k L hL hL0 w)) (hf.smooth k L hL hL0 w)

theorem exists_bound (hψ : IsStdChar D ψ (-1)) {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f) :
    ∃ C : ℝ, ∀ x, ‖f x‖ ≤ C := by
  obtain ⟨i1, i2, i3, i4, i5, K, hK, hKc⟩ := GlobalTheory.AdelicMatrixLattice.lattice D T S
  have hp : ∀ γ ∈ ratL T S, ∀ w, ‖f (γ + w)‖ = ‖f w‖ := by
    rintro _ ⟨γ, rfl⟩ w
    exact (congrArg norm (hf.quasi γ w)).trans (by rw [norm_mul, hψ.1.2.1, one_mul])
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hf.cont.continuousOn
  refine ⟨C, fun w => ?_⟩
  obtain ⟨γ, hγ, h⟩ := hKc w
  rw [← hp γ hγ w]
  exact hC _ h

theorem integrable_sq (hψ : IsStdChar D ψ (-1)) {μ : Measure (WO S T)} {𝓕 : Set (WO S T)} (h1 : μ 𝓕 = 1)
    {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f) : Integrable (fun w => ‖f w‖ ^ 2) (μ.restrict 𝓕) := by
  haveI : BorelSpace (WO S T) := ⟨rfl⟩
  haveI : IsFiniteMeasure (μ.restrict 𝓕) := ⟨by rw [Measure.restrict_apply_univ, h1]; exact ENNReal.one_lt_top⟩
  obtain ⟨C, hC⟩ := exists_bound hψ hf
  refine Integrable.of_bound (hf.cont.norm.pow 2).aestronglyMeasurable (C ^ 2)
    (Filter.Eventually.of_forall fun w => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  exact pow_le_pow_left₀ (norm_nonneg _) (hC w) 2

theorem thetaFunction_eq_zero_of_meanSquare_zero (hψ : IsStdChar D ψ (-1)) {μ : Measure (WO S T)} {𝓕 : Set (WO S T)}
    (hcv : IsCovolOne (ratL T S) μ 𝓕) {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f) (h0 : nrm2 μ 𝓕 f = 0) :
    f = 0 := by
  obtain ⟨hμ, h𝓕, h1⟩ := hcv
  obtain ⟨i1, i2, i3, i4, i5, -⟩ := GlobalTheory.AdelicMatrixLattice.lattice D T S
  haveI : BorelSpace (WO S T) := ⟨rfl⟩
  haveI : Countable (ratL T S) := TopologicalSpace.separableSpace_iff_countable.1 inferInstance
  have hae : ∀ᵐ w ∂(μ.restrict 𝓕), ‖f w‖ ^ 2 = 0 :=
    (integral_eq_zero_iff_of_nonneg (fun w => by positivity) (integrable_sq hψ h1 hf)).1 h0
  have ho : IsOpen {x | f x ≠ 0} := isOpen_ne_fun hf.cont continuous_const
  have hper : ∀ γ ∈ ratL T S, ∀ x, (f (γ + x) ≠ 0 ↔ f x ≠ 0) := by
    rintro _ ⟨γ, rfl⟩ x
    show f (ratW T S γ + x) ≠ 0 ↔ _
    rw [hf.quasi, ne_eq, mul_eq_zero, not_or]
    exact ⟨fun h => h.2, fun h => ⟨psi_ne_zero hψ _, h⟩⟩
  have h2 : μ {x | f x ≠ 0} = 0 := by
    refine h𝓕.measure_zero_of_invariant _ (fun g => ?_) ?_
    · ext x
      rw [Set.mem_vadd_set_iff_neg_vadd_mem]
      show f (((-g : ratL T S) : WO S T) + x) ≠ 0 ↔ f x ≠ 0
      exact hper _ (-g).2 x
    · rw [← Measure.restrict_apply ho.measurableSet]
      rw [ae_iff] at hae
      simpa using hae
  funext x
  by_contra hx
  exact (ho.measure_pos μ ⟨x, hx⟩).ne' h2

end GlobalTheory.ThetaSchurBdd

namespace GlobalTheory.ThetaSchurBdd

variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D}

theorem trig_approx (hψ : IsStdChar D ψ (-1)) {q : WO S T → ℂ} (hq : Continuous q)
    (hqp : ∀ γ ∈ ratL T S, ∀ x, q (γ + x) = q x) {δ : ℝ} (hδ : 0 < δ) :
    ∃ (s : Finset (ratL T S)) (c : ratL T S → ℂ), ∀ x, ‖q x - ∑ a ∈ s, c a * ψ (symplO S T x a)‖ ≤ δ := by
  obtain ⟨i1, i2, i3, i4, i5, K, hK, hKc⟩ := GlobalTheory.AdelicMatrixLattice.lattice D T S
  haveI : BorelSpace (WO S T) := ⟨rfl⟩
  obtain ⟨l1, l2, -, l4, -⟩ := GlobalTheory.OrientedFormLaws.symplOH_laws D S T
  exact GlobalTheory.trigPoly_dense_periodic (WO S T) (ratL T S) K hK hKc (ratL T S)
    (fun γ x => ψ (symplO S T x γ))
    (fun γ => by
      have : Continuous fun x : WO S T => symplOH S T x (γ : WO S T) :=
        GlobalTheory.WeilVacMove.continuous_symplOH S T continuous_id' continuous_const
      simp only [← l4]
      exact hψ.1.1.comp (this.add this))
    (fun γ x y => by
      simp only [← l4, l1, AddChar.map_add_eq_mul]
      ring)
    (fun γ γ' x => by
      simp only [← l4, AddSubgroup.coe_add, l2, AddChar.map_add_eq_mul]
      ring)
    (fun x => by
      simp only [← l4, AddSubgroup.coe_zero, GlobalTheory.WeilVacMove.symplOH_zero_right, add_zero, AddChar.map_zero_eq_one])
    (fun γ x => hψ.1.2.1 _)
    (fun x => by
      rw [← GlobalTheory.RatAnnih.ratL_annihilator D ψ hψ S T x]
      exact ⟨fun h γ hγ => h ⟨γ, hγ⟩, fun h γ => h γ γ.2⟩)
    q hq hqp δ hδ

def thetaSub (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) : Submodule ℂ (WO S T → ℂ) where
  carrier := {f | IsThetaFunO ψ S T f}
  add_mem' := GlobalTheory.WeilVacMove.isTheta_add
  zero_mem' := GlobalTheory.WeilVacMove.isTheta_zero
  smul_mem' := fun c _ h => GlobalTheory.WeilVacMove.isTheta_smul c h

theorem trig_mul_eq (s : Finset (ratL T S)) (c : ratL T S → ℂ) {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f) :
    (fun x => (∑ a ∈ s, c a * ψ (symplO S T x a)) * f x) = ∑ a ∈ s, c a • heisO ψ S T a f := by
  funext x
  rw [Finset.sum_apply, Finset.sum_mul]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Pi.smul_apply, smul_eq_mul, GlobalTheory.ThetaSchur.heisO_rat hf a.2, mul_assoc]

end GlobalTheory.ThetaSchurBdd
