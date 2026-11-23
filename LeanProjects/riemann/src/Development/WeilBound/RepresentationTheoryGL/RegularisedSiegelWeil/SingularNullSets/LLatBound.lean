import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.LLatBoundB
import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.LLatBoundC
import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.LLatBoundD
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsGrowthSobNeTopOfIsAutFunSm

noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open IsDedekindDomain NumberField
open GlobalTheory.RegSch (ikS projS Lvl)

namespace PositivityTheory.Rg.Rsw.L.LLatBound

variable {D : D7}

theorem gen_all {θ : InfFam D} (hθ : IsInfFam θ) (V : HSp D) (n : ℕ)
    (f : SchwartzMap (D.what₂.Tau → Fin V.rank → Fin n → ℂ) ℂ)
    (g : (Fin V.rank → Fin n → Af D.host.F ⊗[D.host.F] D.host.E) → ℂ)
    (hg : g ∈ GlobalTheory.WeilM.SB (Fin V.rank → Fin n → Af D.host.F ⊗[D.host.F] D.host.E)) :
    ∃ C : ℝ≥0∞, C < ⊤ ∧ ∀ h : GA D V,
      ∑' x : {x : Matrix (Fin V.rank) (Fin n) D.host.E // x.rank = V.rank},
        ‖(fun X : Mx D V.rank n => f (fun τ i j => compAt θ τ X i j) * g (fun i j => finPart D (X i j)))
          (mm (mt V h⁻¹) (rat x.1))‖ₑ ≤ C := by
  obtain ⟨U, hUo, hU⟩ := exists_intOpen V
  obtain ⟨S, -, hS⟩ := GlobalTheory.Size.exists_finset_doubleCosets V U hUo
  choose C hC hb using fun x₀ : GA D V => gen_bound_col hθ V n x₀⁻¹ f g hg
  refine ⟨∑ x₀ ∈ S, C x₀, ENNReal.sum_lt_top.2 fun x _ => hC x, fun h => ?_⟩
  obtain ⟨γ, hγ, x₀, hx₀, a, ha, k, hk, hkf, rfl⟩ := hS h
  have e : (γ * x₀ * a * k)⁻¹ = (k⁻¹ * a⁻¹ * x₀⁻¹) * γ⁻¹ := by group
  have e2 : ∀ X : Mx D V.rank n, mm (mt V (γ * x₀ * a * k)⁻¹) X = mm (mt V (k⁻¹ * a⁻¹ * x₀⁻¹)) (mm (mt V γ⁻¹) X) := by
    intro X
    rw [e, mtL_mul]
    exact Matrix.mul_assoc _ _ _
  simp_rw [e2]
  rw [tsum_GQ V n γ⁻¹ (inv_mem hγ) (fun X => ‖f (fun τ i j => compAt θ τ (mm (mt V (k⁻¹ * a⁻¹ * x₀⁻¹)) X) i j) *
    g (fun i j => finPart D ((mm (mt V (k⁻¹ * a⁻¹ * x₀⁻¹)) X) i j))‖ₑ)]
  refine (hb x₀ a⁻¹ (inv_mem ha) k⁻¹ (inv_mem hkf) ?_).trans
    (Finset.single_le_sum (f := C) (fun _ _ => zero_le) hx₀)
  simpa using hU k hk

end PositivityTheory.Rg.Rsw.L.LLatBound

namespace PositivityTheory.Rg.Rsw.L

theorem latBound : LatBound := by
  intro D θ hθ V n M hM
  suffices h : ∃ C : ℝ≥0∞, C < ⊤ ∧ ∀ h : GA D V,
      ∑' x : {x : Matrix (Fin V.rank) (Fin n) D.host.E // x.rank = V.rank}, ‖M (mm (mt V h⁻¹) (rat x.1))‖ₑ ≤ C by
    obtain ⟨C, hC, h⟩ := h
    exact ⟨C.toNNReal, fun g => (h g).trans (by rw [ENNReal.coe_toNNReal hC.ne])⟩
  induction hM using Submodule.span_induction with
  | mem Φ hΦ =>
    obtain ⟨f, g, hg, rfl⟩ := hΦ
    exact LLatBound.gen_all hθ V n f g hg
  | zero => exact ⟨0, by simp, fun _ => by simp⟩
  | add f g _ _ hf hg =>
    obtain ⟨C₁, h₁, hf⟩ := hf
    obtain ⟨C₂, h₂, hg⟩ := hg
    refine ⟨C₁ + C₂, ENNReal.add_lt_top.2 ⟨h₁, h₂⟩, fun h => ?_⟩
    calc _ ≤ ∑' x : {x : Matrix (Fin V.rank) (Fin n) D.host.E // x.rank = V.rank},
          (‖f (mm (mt V h⁻¹) (rat x.1))‖ₑ + ‖g (mm (mt V h⁻¹) (rat x.1))‖ₑ) :=
          ENNReal.tsum_le_tsum fun x => enorm_add_le _ _
      _ = _ := ENNReal.tsum_add
      _ ≤ _ := add_le_add (hf h) (hg h)
  | smul c f _ hf =>
    obtain ⟨C₁, h₁, hf⟩ := hf
    refine ⟨‖c‖ₑ * C₁, ENNReal.mul_lt_top enorm_lt_top h₁, fun h => ?_⟩
    calc _ = ∑' x : {x : Matrix (Fin V.rank) (Fin n) D.host.E // x.rank = V.rank}, ‖c‖ₑ * ‖f (mm (mt V h⁻¹) (rat x.1))‖ₑ :=
          tsum_congr fun x => by simp [enorm_mul]
      _ = _ := ENNReal.tsum_mul_left
      _ ≤ _ := by gcongr; exact hf h

end PositivityTheory.Rg.Rsw.L

end
