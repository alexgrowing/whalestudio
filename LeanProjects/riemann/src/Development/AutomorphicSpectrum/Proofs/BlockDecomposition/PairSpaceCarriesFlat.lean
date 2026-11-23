import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FinStable
open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec GlobalTheory.CompanionTheory.CTFin PositivityTheory.Rg.Rs PositivityTheory.Rg.Rs.InducedTensorMap
open PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.SpectralAccumulation GlobalTheory.CompanionTheory.LimV
open scoped ContDiff

noncomputable section

namespace GlobalTheory.CompanionTheory.LimV

section PairCarry

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {a b : ℕ}

theorem FlatFn.fin_inv {N : ℕ} {e : GA E N → ℂ} (he : FlatFn e) (x : GA E N) {u : GL (Fin N) (Af E)}
    (hu : u ∈ KO E N) : e (x * finGL E N u) = e x := by
  have h := he.rinv x 1 u hu
  simpa [cf] using h

theorem FlatFn.inf_inv {N : ℕ} {e : GA E N → ℂ} (he : FlatFn e) (x : GA E N) (k : Kinf E N) :
    e (x * infGL E N (Unitary.toUnits k)) = e x := by
  have h := he.rinv x k 1 (one_mem _)
  simpa [cf] using h

theorem mul_mem_pairSpace (e₁ : GA E a → ℂ) (e₂ : GA E b → ℂ) (U₁ U₁' : Submodule ℂ (Sm E a))
    (U₂ U₂' : Submodule ℂ (Sm E b)) (F : H E a b → ℂ) (c₁ : Carries e₁ U₁ U₁') (c₂ : Carries e₂ U₂ U₂')
    (hF : F ∈ pairSpace U₁ U₂) : (fun x => e₁ x.1 * e₂ x.2 * F x) ∈ pairSpace U₁' U₂' := by
  induction hF using Submodule.span_induction with
  | mem G hG =>
    obtain ⟨φ₁, h₁, φ₂, h₂, rfl⟩ := hG
    obtain ⟨ψ₁, k₁, i₁⟩ := c₁ φ₁ h₁
    obtain ⟨ψ₂, k₂, i₂⟩ := c₂ φ₂ h₂
    refine Submodule.subset_span ⟨ψ₁, k₁, ψ₂, k₂, funext fun x => ?_⟩
    simp only [i₁, i₂]
    ring
  | zero =>
    have : (fun x : H E a b => e₁ x.1 * e₂ x.2 * (0 : H E a b → ℂ) x) = 0 := by
      funext x; simp
    rw [this]
    exact Submodule.zero_mem _
  | add G G' _ _ h h' =>
    have : (fun x : H E a b => e₁ x.1 * e₂ x.2 * (G + G') x) =
        (fun x => e₁ x.1 * e₂ x.2 * G x) + fun x => e₁ x.1 * e₂ x.2 * G' x := by
      funext x; simp only [Pi.add_apply]; ring
    rw [this]
    exact Submodule.add_mem _ h h'
  | smul c G _ h =>
    have : (fun x : H E a b => e₁ x.1 * e₂ x.2 * (c • G) x) = c • fun x => e₁ x.1 * e₂ x.2 * G x := by
      funext x; simp only [Pi.smul_apply, smul_eq_mul]; ring
    rw [this]
    exact Submodule.smul_mem _ c h

theorem pair_carry (e₁ : GA E a → ℂ) (e₂ : GA E b → ℂ) (U₁ U₁' : Submodule ℂ (Sm E a))
    (U₂ U₂' : Submodule ℂ (Sm E b)) (K₁ : Subgroup (GL (Fin a) (Af E))) (K₂ : Subgroup (GL (Fin b) (Af E)))
    (W₁ : Submodule ℂ (Kinf E a → ℂ)) (W₂ : Submodule ℂ (Kinf E b → ℂ)) (F : H E a b → ℂ)
    (f₁ : FlatFn e₁) (f₂ : FlatFn e₂) (c₁ : Carries e₁ U₁ U₁') (c₂ : Carries e₂ U₂ U₂')
    (hF : F ∈ pairSpace U₁ U₂) (hT : TypeH K₁ K₂ W₁ W₂ F) :
    (fun x => e₁ x.1 * e₂ x.2 * F x) ∈
      (pairSpace U₁' U₂' ⊓ typeHF (K₁ ⊓ KO E a) (K₂ ⊓ KO E b) W₁ W₂ : Submodule ℂ (H E a b → ℂ)) := by
  refine Submodule.mem_inf.2 ⟨mul_mem_pairSpace e₁ e₂ U₁ U₁' U₂ U₂' F c₁ c₂ hF, ?_, fun x => ?_⟩
  · intro u₁ hu₁ u₂ hu₂ x
    have h₁ : e₁ (x * (finGL E a u₁, finGL E b u₂)).1 = e₁ x.1 := f₁.fin_inv x.1 hu₁.2
    have h₂ : e₂ (x * (finGL E a u₁, finGL E b u₂)).2 = e₂ x.2 := f₂.fin_inv x.2 hu₂.2
    show e₁ (x * (finGL E a u₁, finGL E b u₂)).1 * e₂ (x * (finGL E a u₁, finGL E b u₂)).2 *
      F (x * (finGL E a u₁, finGL E b u₂)) = e₁ x.1 * e₂ x.2 * F x
    rw [h₁, h₂, hT.1 u₁ hu₁.1 u₂ hu₂.1 x]
  · have h : (fun k : Kinf E a × Kinf E b =>
        (fun y : H E a b => e₁ y.1 * e₂ y.2 * F y)
          (x * (infGL E a (Unitary.toUnits k.1), infGL E b (Unitary.toUnits k.2)))) =
        (e₁ x.1 * e₂ x.2) • fun k : Kinf E a × Kinf E b =>
          F (x * (infGL E a (Unitary.toUnits k.1), infGL E b (Unitary.toUnits k.2))) := by
      funext k
      have h₁ : e₁ (x * (infGL E a (Unitary.toUnits k.1), infGL E b (Unitary.toUnits k.2))).1 = e₁ x.1 :=
        f₁.inf_inv x.1 k.1
      have h₂ : e₂ (x * (infGL E a (Unitary.toUnits k.1), infGL E b (Unitary.toUnits k.2))).2 = e₂ x.2 :=
        f₂.inf_inv x.2 k.2
      simp only [Pi.smul_apply, smul_eq_mul, h₁, h₂]
    rw [h]
    exact Submodule.smul_mem _ _ (hT.2 x)

end PairCarry

end GlobalTheory.CompanionTheory.LimV

end
