import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.EigenvalueSeparation.StableEigenspaces.InterpolationL2Bound
import Development.WeilBound.RepresentationTheoryGL.ConstantTermFiniteness.LieInvariants.InvariantOfLieOneLEqZero

noncomputable section

open NumberField GlobalTheory.CuspRep GlobalTheory.UnitaryBC

namespace PositivityTheory.Rg.BcB.E.E3

namespace fintype

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {N : ℕ}

def Wl (W : Submodule ℂ (Kinf E N → ℂ)) : Submodule ℂ (Kinf E N → ℂ) where
  carrier := {w | Continuous w ∧ ∀ k₀, (fun k => w (k₀ * k)) ∈ W}
  add_mem' := fun {_ _} hv hw => ⟨hv.1.add hw.1, fun k₀ => W.add_mem (hv.2 k₀) (hw.2 k₀)⟩
  zero_mem' := ⟨continuous_const, fun _ => W.zero_mem⟩
  smul_mem' := fun c _ hw => ⟨hw.1.const_smul c, fun k₀ => W.smul_mem c (hw.2 k₀)⟩

omit [NumberField E] [IsCMField E] in
theorem wl_le (W : Submodule ℂ (Kinf E N → ℂ)) : Wl W ≤ W := fun w hw => by
  simpa only [one_mul] using hw.2 1

theorem wl_fin (W : Submodule ℂ (Kinf E N → ℂ)) [FiniteDimensional ℂ W] : FiniteDimensional ℂ (Wl W) :=
  Submodule.finiteDimensional_of_le (wl_le W)

def lt (W : Submodule ℂ (Kinf E N → ℂ)) (k : Kinf E N) : Wl W →ₗ[ℂ] Wl W where
  toFun w := ⟨fun k' => w.1 (k * k'), w.2.1.comp (continuous_const.mul continuous_id), fun k₀ => by
    simpa only [mul_assoc] using w.2.2 (k * k₀)⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def sig (W : Submodule ℂ (Kinf E N → ℂ)) : Representation ℂ (Kinf E N) (Module.Dual ℂ (Wl W)) where
  toFun k := (lt W k).dualMap
  map_one' := by
    refine LinearMap.ext fun v => LinearMap.ext fun w => ?_
    change v (lt W 1 w) = v w
    congr 1
    exact Subtype.ext (funext fun k' => show w.1 (1 * k') = w.1 k' by rw [one_mul])
  map_mul' k₁ k₂ := by
    refine LinearMap.ext fun v => LinearMap.ext fun w => ?_
    change v (lt W (k₁ * k₂) w) = v (lt W k₂ (lt W k₁ w))
    congr 1
    exact Subtype.ext (funext fun k' => show w.1 (k₁ * k₂ * k') = w.1 (k₁ * (k₂ * k')) by rw [mul_assoc])

theorem sig_cont (W : Submodule ℂ (Kinf E N → ℂ)) [FiniteDimensional ℂ W] : GlobalTheory.Published.AutFin.IsContRep (sig W) := by
  have := wl_fin W
  intro ℓ v
  set w := (Module.evalEquiv ℂ (Wl W)).symm ℓ
  have hℓ : ∀ x, ℓ x = x w := fun x => by
    rw [← (Module.evalEquiv ℂ (Wl W)).apply_symm_apply ℓ]
    rfl
  simp_rw [hℓ]
  have hc : Continuous fun k : Kinf E N => lt W k w :=
    continuous_induced_rng.2 (continuous_pi fun k' => w.2.1.comp (continuous_id.mul continuous_const))
  exact (LinearMap.continuous_of_finiteDimensional v).comp hc

theorem cont_ev (y : Sm E N) (g : GA E N) : Continuous fun k : Kinf E N => y.1 (g * infGL E N (Unitary.toUnits k)) := by
  have h1 : (fun k : Kinf E N => y.1 (g * infGL E N (Unitary.toUnits k))) = fun k => chart y.1 g (toL k.1) :=
    funext fun k => (chart_val y.1 g (Unitary.toUnits k)).symm
  rw [h1]
  exact (y.2 g).continuousOn.comp_continuous continuous_subtype_val fun k => val_mem_invSet (Unitary.toUnits k)

theorem coeff_mem (W : Submodule ℂ (Kinf E N → ℂ)) (φ : Sm E N)
    (hφ : ∀ x, (fun k : Kinf E N => φ.1 (x * infGL E N (Unitary.toUnits k))) ∈ W) (g : GA E N) :
    (fun k : Kinf E N => (cptRep E N k φ).1 g) ∈ GlobalTheory.Published.AutFin.coeffSpan (sig W) := by
  let f : Wl W := ⟨fun k => φ.1 (g * infGL E N (Unitary.toUnits k)), cont_ev φ g, fun k₀ => by
    simpa only [map_mul, mul_assoc] using hφ (g * infGL E N (Unitary.toUnits k₀))⟩
  refine Submodule.subset_span ⟨Module.Dual.eval ℂ (Wl W) f, (LinearMap.proj 1).comp (Wl W).subtype, funext fun k => ?_⟩
  show φ.1 (g * infGL E N (Unitary.toUnits k)) = φ.1 (g * infGL E N (Unitary.toUnits (k * 1)))
  rw [mul_one]

end fintype

open fintype in
theorem fintype_holds : FinType := by
  intro E _ _ _ N K W m S hK hW hS hm
  have := wl_fin W
  have hF := PositivityTheory.Rg.HF.GL.automorphicFormsFiniteGL E N K hK (Module.Dual ℂ (Wl W)) (sig W) (sig_cont W)
    (fun τ u => ((m τ).map (u + ·)).prod)
  have hsub : S ⊆ GlobalTheory.Published.AutFinGL.forms K (sig W) (fun τ u => ((m τ).map (u + ·)).prod) := by
    intro φ hφ
    obtain ⟨h1, h2, h3⟩ := hS φ hφ
    exact ⟨h1, fun u hu => Subtype.ext (funext fun x => h2 u hu x), coeff_mem W φ h3,
      fun τ u => (hm τ).2 u φ (Submodule.subset_span hφ)⟩
  exact Submodule.finiteDimensional_of_le (Submodule.span_mono hsub)

end PositivityTheory.Rg.BcB.E.E3

end
