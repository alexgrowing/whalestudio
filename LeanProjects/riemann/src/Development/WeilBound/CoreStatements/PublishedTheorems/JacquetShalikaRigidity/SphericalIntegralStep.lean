import Development.WeilBound.CoreStatements.PublishedTheorems.JacquetShalikaRigidity.ColumnConjugationMeasure
import Development.WeilBound.CoreStatements.PublishedTheorems.SmoothVectorEstimates.GeneralLinearEntryConvergence

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open GlobalTheory.CuspGeneric GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DiscSpec PositivityTheory.jumpWindows PositivityTheory.RgJS
open GroundTheory.Automorphic GroundTheory.Automorphic.FourierWhittaker GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.Spherical
open scoped ENNReal ComplexConjugate

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PositivityTheory.AdelicQuotientData

namespace SphericalFunctionIntegral

open Formalism.UG GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.AutomorphicL2Unitary GlobalTheory.LFun Formalism.L2.Host

variable {E : Type} [Field E] [NumberField E] {k : ℕ}

theorem le_one (w : Pl E) (x : w.adicCompletion E) :
    ValuativeRel.valuation (w.adicCompletion E) x ≤ 1 ↔ Valued.v x ≤ 1 := by
  have : (Valued.v : Valuation (w.adicCompletion E) (WithZero (Multiplicative ℤ))).Compatible :=
    Valuation.Compatible.ofValuation _
  exact (ValuativeRel.isEquiv (ValuativeRel.valuation _) Valued.v).le_one_iff_le_one

theorem mem_Ov (w : Pl E) {x : w.adicCompletion E} (h : x ∈ (ValuativeRel.valuation (w.adicCompletion E)).integer) :
    x ∈ Ov E w :=
  (le_one w x).1 ((Valuation.mem_integer_iff _ _).1 h)

theorem int_KGL (w : Pl E) {x : GL (Fin k) (w.adicCompletion E)}
    (hx : x ∈ GLnLocal.integralGL (w.adicCompletion E) k) : x ∈ KGL w k := by
  obtain ⟨h1, h2⟩ := (GLnLocal.mem_integralGL_iff _ _).1 hx
  have hi : Function.Injective fun A : Matrix (Fin k) (Fin k) (Ov E w) => A.map (Ov E w).subtype :=
    Matrix.map_injective Subtype.val_injective
  refine ⟨⟨Matrix.of fun i j => ⟨_, mem_Ov w (h1 i j)⟩, Matrix.of fun i j => ⟨(x⁻¹ : GL (Fin k) (w.adicCompletion E)).1 i j, mem_Ov w (h2 i j)⟩, hi ?_, hi ?_⟩, Units.ext rfl⟩
  · simp only [Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _)]
    exact x.mul_inv
  · simp only [Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _)]
    exact x.inv_mul

theorem fix {w : Pl E} {B : Multiset ℂˣ} {φ : XB E k} (h : SatFn w B φ) {x : GL (Fin k) (w.adicCompletion E)}
    (hx : x ∈ GLnLocal.integralGL (w.adicCompletion E) k) : Rt E k (fl k w x) φ = φ := by
  rcases h with rfl | h
  · exact map_zero _
  · exact GlobalTheory.LGrp.mem_fixed.1 h.2.1 x (int_KGL w hx)

variable [IsTotallyComplex E]

theorem step (hG : jumpWindows.G0) (S : Finset (Pl E)) (φ : XB E k) (g κ : GA E k)
    (hfix : ∀ w, w ∉ S → ∀ x ∈ GLnLocal.integralGL (w.adicCompletion E) k, Rt E k (fl k w x) φ = φ)
    (hinf : cInf κ = 1) (hS : ∀ w ∈ S, cLoc w κ = 1)
    (hint : ∀ w, cLoc w κ ∈ GLnLocal.integralGL (w.adicCompletion E) k) (T : Finset (Pl E)) :
    ∃ h : GA E k, φ (g * h) = φ g ∧ cInf h = cInf κ ∧ (∀ w, (w ∈ S ∨ w ∈ T) → cLoc w h = cLoc w κ) ∧
      (∀ w, w ∉ S → w ∉ T → cLoc w h = 1) := by
  classical
  obtain ⟨-, -, h3, h4, h5, -⟩ := hG E k
  induction T using Finset.induction_on with
  | empty =>
    refine ⟨1, by rw [mul_one], by rw [map_one, hinf], fun w hw => ?_, fun w _ _ => map_one _⟩
    rcases hw with hw | hw
    · rw [map_one, hS w hw]
    · simp at hw
  | insert w T hwT ih =>
    obtain ⟨h, hf0, hi, hl, ho⟩ := ih
    by_cases hwS : w ∈ S
    · refine ⟨h, hf0, hi, fun v hv => ?_, fun v hv hv' => ho v hv fun h' => hv' (Finset.mem_insert_of_mem h')⟩
      rcases hv with hv | hv
      · exact hl v (Or.inl hv)
      · rcases Finset.mem_insert.1 hv with rfl | hv
        · exact hl v (Or.inl hwS)
        · exact hl v (Or.inr hv)
    · refine ⟨h * fl k w (cLoc w κ), ?_, ?_, fun v hv => ?_, fun v hv hv' => ?_⟩
      · have e := congrArg (fun ψ : XB E k => ψ (g * h)) (hfix w hwS _ (hint w))
        simp only [Rt_apply] at e
        rw [← mul_assoc, e, hf0]
      · rw [map_mul, h3, mul_one, hi]
      · rw [map_mul]
        by_cases hvw : v = w
        · subst hvw
          rw [h4, ho v hwS hwT, one_mul]
        · rw [h5 _ _ _ hvw, mul_one]
          rcases hv with hv | hv
          · exact hl v (Or.inl hv)
          · exact hl v (Or.inr ((Finset.mem_insert.1 hv).resolve_left hvw))
      · have hvw : v ≠ w := fun e => hv' (e ▸ Finset.mem_insert_self w T)
        rw [map_mul, h5 _ _ _ hvw, mul_one]
        exact ho v hv fun h' => hv' (Finset.mem_insert_of_mem h')

open jumpWindows.GeneralLinearEntryConvergence in

theorem sph (hG : jumpWindows.G0) (S : Finset (Pl E)) (φ : XB E k)
    (hfix : ∀ w, w ∉ S → ∀ x ∈ GLnLocal.integralGL (w.adicCompletion E) k, Rt E k (fl k w x) φ = φ) :
    SphOff S (φ : GA E k → ℂ) := by
  intro g κ hinf hS hint
  choose H hH using step hG S φ g κ hfix hinf hS hint
  have hT : Tendsto H atTop (𝓝 κ) := by
    refine tendsto_gl κ H (tendsto_entry S κ H (fun T => (hH T).2.1) (fun T => (hH T).2.2.1)
      (fun T => (hH T).2.2.2)) (tendsto_entry S κ⁻¹ (fun T => (H T)⁻¹) (fun T => ?_) (fun T w hw => ?_)
      (fun T w hw hw' => ?_))
    · rw [map_inv, map_inv, (hH T).2.1]
    · rw [map_inv, map_inv, (hH T).2.2.1 w hw]
    · rw [map_inv, (hH T).2.2.2 w hw hw', inv_one]
  have hc : Continuous fun x : GA E k => φ (g * x) := φ.continuous.comp (continuous_const.mul continuous_id)
  have h1 := (hc.tendsto κ).comp hT
  have h2 : Tendsto ((fun x : GA E k => φ (g * x)) ∘ H) atTop (𝓝 (φ g)) := by
    have e : (fun x : GA E k => φ (g * x)) ∘ H = fun _ => φ g := funext fun T => (hH T).1
    rw [e]
    exact tendsto_const_nhds
  exact tendsto_nhds_unique h1 h2

end SphericalFunctionIntegral

theorem spherical_function_of : jumpWindows.G0 → jumpWindows.G5 → C0 → K7 → K8 := by
  intro hG0 hG5 hC0 hK7 E _ _ _ k ψ hψ S hcond α φ hgood hsat
  obtain ⟨-, hrt, -, hreg⟩ := hG5 E k ψ hψ
  have hfix : ∀ w, w ∉ S → ∀ x ∈ GLnLocal.integralGL (w.adicCompletion E) k, Rt E k (fl k w x) φ = φ :=
    fun w hw x hx => SphericalFunctionIntegral.fix (hsat ⟨w, hw⟩) hx
  have hφ := SphericalFunctionIntegral.sph hG0 S φ hfix
  have hcont := (hreg φ hgood).1
  refine ⟨hφ, fun g κ hinf hS hint => ?_, fun g hg => ⟨fun g₀ hi hS hIn h0 => ?_, fun w hw => ?_⟩⟩
  · have e : Rt E k κ φ = φ := by
      ext x
      simp only [Rt_apply]
      exact hφ x κ hinf hS hint
    rw [← hrt, e]
  · refine hg (jumpWindows.convergence_entries_general_linear hG0 E k S (Wh ψ φ) hcont (fun w hw h hh h0 u => ?_) g g₀ hi hS hIn h0)
    obtain ⟨χ, -, -, hK⟩ := hK7 E k ψ hψ w (hcond w hw)
    rw [hK (α ⟨w, hw⟩) φ hgood (hsat ⟨w, hw⟩) h hh u, h0, zero_mul]
  · obtain ⟨χ, -, -, hK⟩ := hK7 E k ψ hψ w (hcond w hw)
    obtain ⟨g', hg', e, -, -⟩ := (hC0 E k S).2.2.2.2.2.2 w g
    have h1 := hK (α ⟨w, hw⟩) φ hgood (hsat ⟨w, hw⟩) g' hg' (cLoc w g)
    rw [← e] at h1
    rw [h1] at hg
    have h2 := right_ne_zero_of_mul hg
    by_contra hA
    apply h2
    rw [sphericalWhittaker, if_neg hA]

end PositivityTheory.AdelicQuotientData

end
