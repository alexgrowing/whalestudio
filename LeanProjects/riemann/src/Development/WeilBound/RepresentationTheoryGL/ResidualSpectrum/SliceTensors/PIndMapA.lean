import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.TwistedSlicesSquareIntegrable
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EqOfIsLocCompGL

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Formalism.L2.Host
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec GlobalTheory.CompanionTheory.CTFin
open scoped ContDiff

namespace PositivityTheory.Rg.Rs.InducedTensorMap

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {r s : ℕ}

def cf (a : ℕ) (k : Kinf E a) (g : GL (Fin a) (Af E)) : GA E a := infGL E a (Unitary.toUnits k) * finGL E a g

theorem A.act_cf {a : ℕ} (k : Kinf E a) (g : GL (Fin a) (Af E)) (ψ : Sm E a) (x : GA E a) :
    (act (.cpt k) (act (.fin g) ψ)).1 x = ψ.1 (x * cf a k g) := congrArg ψ.1 (mul_assoc _ _ _)

theorem A.sum_mem {U₁ : Submodule ℂ (Sm E r)} {U₂ : Submodule ℂ (Sm E s)} {n : ℕ} {ψ₁ : Fin n → Sm E r}
    {ψ₂ : Fin n → Sm E s} (h₁ : ∀ i, ψ₁ i ∈ U₁) (h₂ : ∀ i, ψ₂ i ∈ U₂) :
    (fun m : GA E r × GA E s => ∑ i, (ψ₁ i).1 m.1 * (ψ₂ i).1 m.2) ∈ tens2 U₁ U₂ := by
  have := Submodule.sum_mem (tens2 U₁ U₂) (t := Finset.univ)
    (f := fun i (m : GA E r × GA E s) => (ψ₁ i).1 m.1 * (ψ₂ i).1 m.2)
    fun i _ => Submodule.subset_span ⟨_, h₁ i, _, h₂ i, rfl⟩
  convert this using 1
  funext m
  simp

theorem exists_extOp {a : ℕ} (f : Sm E a →ₗ[ℂ] Sm E a) :
    ∃ T : Module.End ℂ (GA E a → ℂ), ∀ ψ : Sm E a, T ψ.1 = (f ψ).1 := by
  obtain ⟨T, hT⟩ := LinearMap.exists_extend ((Sm E a).subtype ∘ₗ f)
  exact ⟨T, fun ψ => LinearMap.congr_fun hT ψ⟩

def extOp {a : ℕ} (f : Sm E a →ₗ[ℂ] Sm E a) : Module.End ℂ (GA E a → ℂ) := (exists_extOp f).choose

theorem extOp_apply {a : ℕ} (f : Sm E a →ₗ[ℂ] Sm E a) (ψ : Sm E a) : extOp f ψ.1 = (f ψ).1 :=
  (exists_extOp f).choose_spec ψ

def tensOp (f₁ : Sm E r →ₗ[ℂ] Sm E r) (f₂ : Sm E s →ₗ[ℂ] Sm E s) : Module.End ℂ (GA E r × GA E s → ℂ) where
  toFun F m := extOp f₂ (fun b => extOp f₁ (fun a => F (a, b)) m.1) m.2
  map_add' F G := by
    funext m
    have e : (fun b => extOp f₁ (fun a => (F + G) (a, b)) m.1) =
        (fun b => extOp f₁ (fun a => F (a, b)) m.1) + fun b => extOp f₁ (fun a => G (a, b)) m.1 :=
      funext fun b => congrFun (map_add (extOp f₁) (fun a => F (a, b)) fun a => G (a, b)) m.1
    rw [e, map_add]
    rfl
  map_smul' c F := by
    funext m
    have e : (fun b => extOp f₁ (fun a => (c • F) (a, b)) m.1) = c • fun b => extOp f₁ (fun a => F (a, b)) m.1 :=
      funext fun b => congrFun (map_smul (extOp f₁) c fun a => F (a, b)) m.1
    rw [e, map_smul]
    rfl

theorem tensOp_sum (f₁ : Sm E r →ₗ[ℂ] Sm E r) (f₂ : Sm E s →ₗ[ℂ] Sm E s) {n : ℕ} (ψ₁ : Fin n → Sm E r)
    (ψ₂ : Fin n → Sm E s) :
    tensOp f₁ f₂ (fun m => ∑ i, (ψ₁ i).1 m.1 * (ψ₂ i).1 m.2) = fun m => ∑ i, (f₁ (ψ₁ i)).1 m.1 * (f₂ (ψ₂ i)).1 m.2 := by
  funext m
  have e1 : ∀ b, (fun a => ∑ i, (ψ₁ i).1 a * (ψ₂ i).1 b) = ∑ i, (ψ₂ i).1 b • (ψ₁ i).1 := fun b => by
    funext a; simp [mul_comm]
  have e2 : (fun b => extOp f₁ (fun a => ∑ i, (ψ₁ i).1 a * (ψ₂ i).1 b) m.1) = ∑ i, (f₁ (ψ₁ i)).1 m.1 • (ψ₂ i).1 := by
    funext b
    rw [e1, map_sum]
    simp [extOp_apply, mul_comm]
  change extOp f₂ (fun b => extOp f₁ (fun a => ∑ i, (ψ₁ i).1 a * (ψ₂ i).1 b) m.1) m.2 = _
  rw [e2, map_sum]
  simp [extOp_apply]

theorem tensor_pair_finite_sum {U₁ : Submodule ℂ (Sm E r)} {U₂ : Submodule ℂ (Sm E s)} {F : GA E r × GA E s → ℂ}
    (hF : F ∈ tens2 U₁ U₂) : ∃ (n : ℕ) (ψ₁ : Fin n → Sm E r) (ψ₂ : Fin n → Sm E s), (∀ i, ψ₁ i ∈ U₁) ∧ (∀ i, ψ₂ i ∈ U₂) ∧
      F = fun m => ∑ i, (ψ₁ i).1 m.1 * (ψ₂ i).1 m.2 := by
  obtain ⟨n, c, g, rfl⟩ := Submodule.mem_span_set'.1 hF
  choose φ₁ h₁ φ₂ h₂ e using fun i => (g i).2
  refine ⟨n, fun i => c i • φ₁ i, φ₂, fun i => U₁.smul_mem _ (h₁ i), h₂, funext fun m => ?_⟩
  simp [e, mul_assoc]

theorem tensOp_id {U₁ : Submodule ℂ (Sm E r)} {U₂ : Submodule ℂ (Sm E s)} {F : GA E r × GA E s → ℂ}
    (hF : F ∈ tens2 U₁ U₂) : tensOp LinearMap.id LinearMap.id F = F := by
  obtain ⟨n, ψ₁, ψ₂, -, -, rfl⟩ := tensor_pair_finite_sum hF
  rw [tensOp_sum]
  rfl

theorem tensOp_mem (f₁ : Sm E r →ₗ[ℂ] Sm E r) (f₂ : Sm E s →ₗ[ℂ] Sm E s) {U₁ : Submodule ℂ (Sm E r)}
    {U₂ : Submodule ℂ (Sm E s)} {F : GA E r × GA E s → ℂ} (hF : F ∈ tens2 U₁ U₂) : tensOp f₁ f₂ F ∈ tens2 ⊤ ⊤ := by
  obtain ⟨n, ψ₁, ψ₂, -, -, rfl⟩ := tensor_pair_finite_sum hF
  rw [tensOp_sum]
  exact A.sum_mem (fun _ => trivial) fun _ => trivial

theorem tensOp_translate {U₁ : Submodule ℂ (Sm E r)} {U₂ : Submodule ℂ (Sm E s)} (hU₁ : IsStable U₁)
    (hU₂ : IsStable U₂) {f₁ : Sm E r →ₗ[ℂ] Sm E r} {f₂ : Sm E s →ₗ[ℂ] Sm E s}
    (hf₁ : ∀ o, ∀ ψ ∈ U₁, f₁ (act o ψ) = act o (f₁ ψ)) (hf₂ : ∀ o, ∀ ψ ∈ U₂, f₂ (act o ψ) = act o (f₂ ψ))
    {F : GA E r × GA E s → ℂ} (hF : F ∈ tens2 U₁ U₂) (k₁ : Kinf E r) (g₁ : GL (Fin r) (Af E)) (k₂ : Kinf E s)
    (g₂ : GL (Fin s) (Af E)) :
    tensOp f₁ f₂ (fun m => F (m.1 * cf r k₁ g₁, m.2 * cf s k₂ g₂)) =
      fun m => tensOp f₁ f₂ F (m.1 * cf r k₁ g₁, m.2 * cf s k₂ g₂) := by
  obtain ⟨n, ψ₁, ψ₂, h₁, h₂, rfl⟩ := tensor_pair_finite_sum hF
  have e := tensOp_sum f₁ f₂ (fun i => act (.cpt k₁) (act (.fin g₁) (ψ₁ i))) fun i => act (.cpt k₂) (act (.fin g₂) (ψ₂ i))
  simp only [A.act_cf] at e
  rw [e, tensOp_sum]
  funext m
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [hf₁ _ _ (hU₁ _ _ (h₁ i)), hf₁ _ _ (h₁ i), hf₂ _ _ (hU₂ _ _ (h₂ i)), hf₂ _ _ (h₂ i), A.act_cf, A.act_cf]

theorem tensOp_deriv {U₁ : Submodule ℂ (Sm E r)} {U₂ : Submodule ℂ (Sm E s)} {f₁ : Sm E r →ₗ[ℂ] Sm E r}
    {f₂ : Sm E s →ₗ[ℂ] Sm E s} (hf₁ : ∀ o, ∀ ψ ∈ U₁, f₁ (act o ψ) = act o (f₁ ψ))
    (hf₂ : ∀ o, ∀ ψ ∈ U₂, f₂ (act o ψ) = act o (f₂ ψ)) (γ₁ : ℝ → GL (Fin r) (Cinf E)) (γ₂ : ℝ → GL (Fin s) (Cinf E))
    (Z₁ : Lie E r) (Z₂ : Lie E s) (h₁ : γ₁ 0 = 1) (h₂ : γ₂ 0 = 1) (hγ₁ : HasDerivAt (fun t => toL (γ₁ t).val) Z₁ 0)
    (hγ₂ : HasDerivAt (fun t => toL (γ₂ t).val) Z₂ 0) {F : GA E r × GA E s → ℂ} (hF : F ∈ tens2 U₁ U₂) :
    ∃ G : GA E r × GA E s → ℂ,
      (∀ m, HasDerivAt (fun t => F (m.1 * infGL E r (γ₁ t), m.2 * infGL E s (γ₂ t))) (G m) 0) ∧
      ∀ m, HasDerivAt (fun t => tensOp f₁ f₂ F (m.1 * infGL E r (γ₁ t), m.2 * infGL E s (γ₂ t))) (tensOp f₁ f₂ G m) 0 := by
  obtain ⟨n, ψ₁, ψ₂, u₁, u₂, rfl⟩ := tensor_pair_finite_sum hF
  have key : ∀ (χ₁ : Fin n → Sm E r) (χ₂ : Fin n → Sm E s) (m : GA E r × GA E s),
      HasDerivAt (fun t => ∑ i, (χ₁ i).1 (m.1 * infGL E r (γ₁ t)) * (χ₂ i).1 (m.2 * infGL E s (γ₂ t)))
        (∑ i, (lie E r Z₁ (χ₁ i)).1 m.1 * (χ₂ i).1 m.2 + ∑ i, (χ₁ i).1 m.1 * (lie E s Z₂ (χ₂ i)).1 m.2) 0 := by
    intro χ₁ χ₂ m
    rw [← Finset.sum_add_distrib]
    refine HasDerivAt.fun_sum fun i _ => ?_
    have := (hasDerivAt_curve (χ₁ i) m.1 γ₁ Z₁ h₁ hγ₁).mul (hasDerivAt_curve (χ₂ i) m.2 γ₂ Z₂ h₂ hγ₂)
    simp only [h₁, h₂, map_one, mul_one] at this
    exact this
  refine ⟨(fun m => ∑ i, (lie E r Z₁ (ψ₁ i)).1 m.1 * (ψ₂ i).1 m.2) + fun m => ∑ i, (ψ₁ i).1 m.1 * (lie E s Z₂ (ψ₂ i)).1 m.2,
    key ψ₁ ψ₂, fun m => ?_⟩
  rw [map_add, tensOp_sum, tensOp_sum, tensOp_sum]
  have e₁ : ∀ i, f₁ (lie E r Z₁ (ψ₁ i)) = lie E r Z₁ (f₁ (ψ₁ i)) := fun i => hf₁ (.lie Z₁) _ (u₁ i)
  have e₂ : ∀ i, f₂ (lie E s Z₂ (ψ₂ i)) = lie E s Z₂ (f₂ (ψ₂ i)) := fun i => hf₂ (.lie Z₂) _ (u₂ i)
  simp only [e₁, e₂]
  exact key (fun i => f₁ (ψ₁ i)) (fun i => f₂ (ψ₂ i)) m

theorem contDiffAt_tens {U₁ : Submodule ℂ (Sm E r)} {U₂ : Submodule ℂ (Sm E s)} {P : Type} [NormedAddCommGroup P]
    [NormedSpace ℝ P] {y₀ : P} (b₁ : P → GL (Fin r) (Cinf E)) (b₂ : P → GL (Fin s) (Cinf E))
    (hb₁ : ContDiffAt ℝ ∞ (fun y => toL (b₁ y).val) y₀) (hb₂ : ContDiffAt ℝ ∞ (fun y => toL (b₂ y).val) y₀)
    {F : GA E r × GA E s → ℂ} (hF : F ∈ tens2 U₁ U₂) (m : GA E r × GA E s) :
    ContDiffAt ℝ ∞ (fun y => F (m.1 * infGL E r (b₁ y), m.2 * infGL E s (b₂ y))) y₀ := by
  obtain ⟨n, ψ₁, ψ₂, -, -, rfl⟩ := tensor_pair_finite_sum hF
  refine ContDiffAt.sum fun i _ => ContDiffAt.mul ?_ ?_
  · have := (contDiffAt_chart (ψ₁ i).2 m.1 (val_mem_invSet (b₁ y₀))).comp y₀ hb₁
    simpa only [Function.comp_def, chart_val] using this
  · have := (contDiffAt_chart (ψ₂ i).2 m.2 (val_mem_invSet (b₂ y₀))).comp y₀ hb₂
    simpa only [Function.comp_def, chart_val] using this

end PositivityTheory.Rg.Rs.InducedTensorMap

end
