import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ValLastX
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BesselPeriodRightTranslateSobolevSepContinuousStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TprodEqZeroOfKFinOff
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BesselPeriodLinearAndTranslationCombinationStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.SeeSaw.DenseRel

variable {D : D7}

theorem sobCont_zero {n : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (Lie : Set (Matrix (Fin n) (Fin n) ℂ)) (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) : Sobolev₂ Lie σ 0 :=
  ⟨[], 0, by simp, by simp⟩

theorem sobCont_smul {n : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {Lie : Set (Matrix (Fin n) (Fin n) ℂ)} {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {ℓ : H →ₗ[ℂ] ℂ} (c : ℂ)
    (h : Sobolev₂ Lie σ ℓ) : Sobolev₂ Lie σ (c • ℓ) := by
  obtain ⟨S, C, h1, h2⟩ := h
  refine ⟨S, ‖c‖ * C, h1, fun w hw => ?_⟩
  rw [LinearMap.smul_apply, norm_smul, mul_assoc]
  exact mul_le_mul_of_nonneg_left (h2 w hw) (norm_nonneg c)

theorem sobCont_add {n : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {Lie : Set (Matrix (Fin n) (Fin n) ℂ)} {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {ℓ ℓ' : H →ₗ[ℂ] ℂ}
    (h : Sobolev₂ Lie σ ℓ) (h' : Sobolev₂ Lie σ ℓ') : Sobolev₂ Lie σ (ℓ + ℓ') := by
  obtain ⟨S, C, h1, h2⟩ := h
  obtain ⟨S', C', h1', h2'⟩ := h'
  refine ⟨S ++ S', max C C', fun l hl => (List.mem_append.1 hl).elim (h1 l) (h1' l), fun w hw => ?_⟩
  have p : ∀ S : List (List (Matrix (Fin n) (Fin n) ℂ)), 0 ≤ (S.map fun l => ‖l.foldr (dRep σ) w‖).sum := by
    intro S
    refine List.sum_nonneg fun x hx => ?_
    obtain ⟨l, -, rfl⟩ := List.mem_map.1 hx
    exact norm_nonneg _
  rw [LinearMap.add_apply, List.map_append, List.sum_append, mul_add]
  refine (norm_add_le _ _).trans (add_le_add ((h2 w hw).trans ?_) ((h2' w hw).trans ?_))
  · exact mul_le_mul_of_nonneg_right (le_max_left _ _) (p S)
  · exact mul_le_mul_of_nonneg_right (le_max_right _ _) (p S')

section Sep

variable {V : HSp D} {S : D.what₂.Tau → SPar} (M : DSModel V S)

theorem sepCont_zero : GlobalTheory.Core.Mi.SepCont M 0 := fun τ _ => ⟨0, sobCont_zero _ _, fun _ => by simp⟩

theorem sepCont_add {Λ Λ' : SmT M →ₗ[ℂ] ℂ} (h : GlobalTheory.Core.Mi.SepCont M Λ) (h' : GlobalTheory.Core.Mi.SepCont M Λ') :
    GlobalTheory.Core.Mi.SepCont M (Λ + Λ') := fun τ v => by
  obtain ⟨ℓ, hℓ, e⟩ := h τ v
  obtain ⟨ℓ', hℓ', e'⟩ := h' τ v
  exact ⟨ℓ + ℓ', sobCont_add hℓ hℓ', fun w => by simp [e, e']⟩

theorem sepCont_smul (a : ℂ) {Λ : SmT M →ₗ[ℂ] ℂ} (h : GlobalTheory.Core.Mi.SepCont M Λ) : GlobalTheory.Core.Mi.SepCont M (a • Λ) :=
  fun τ v => by
    obtain ⟨ℓ, hℓ, e⟩ := h τ v
    exact ⟨a • ℓ, sobCont_smul a hℓ, fun w => by simp [e]⟩

theorem sepCont_sum {ι : Type} (s : Finset ι) (Λ : ι → SmT M →ₗ[ℂ] ℂ) (h : ∀ i ∈ s, GlobalTheory.Core.Mi.SepCont M (Λ i)) :
    GlobalTheory.Core.Mi.SepCont M (∑ i ∈ s, Λ i) :=
  Finset.sum_induction Λ (GlobalTheory.Core.Mi.SepCont M) (fun _ _ => sepCont_add M) (sepCont_zero M) h

theorem kill_of_itSpans {W : HSp D} {S' : D.what₂.Tau → SPar} (M' : DSModel W S')
    (It : PolF D W.rank V.rank →ₗ[ℂ] SmT M' →ₗ[ℂ] SmT M) (hS : GlobalTheory.Core.Mi.ItSpans M M' It) (Λ : SmT M →ₗ[ℂ] ℂ)
    (h : ∀ P (y : M'.Vec), GlobalTheory.Core.Mi.KVecP M' y → Λ (It P (PiTensorProduct.tprod ℂ y)) = 0) :
    ∀ v : M.Vec, GlobalTheory.Core.Mi.KVecP M v → Λ (PiTensorProduct.tprod ℂ v) = 0 := by
  intro v hv
  have hle : Submodule.span ℂ {x | ∃ (P : PolF D W.rank V.rank) (y : M'.Vec), GlobalTheory.Core.Mi.KVecP M' y ∧
      x = It P (PiTensorProduct.tprod ℂ y)} ≤ LinearMap.ker Λ := by
    rw [Submodule.span_le]
    rintro x ⟨P, y, hy, rfl⟩
    exact h P y hy
  exact hle (hS v hv)

end Sep

theorem isContAut_zero (V : HSp D) : IsContAut V (0 : GA D V → ℂ) :=
  ⟨fun _ _ _ => rfl, continuous_const⟩

theorem isContAut_add {V : HSp D} {f g : GA D V → ℂ} (hf : IsContAut V f) (hg : IsContAut V g) :
    IsContAut V (f + g) :=
  ⟨fun γ hγ x => by simp only [Pi.add_apply, hf.1 γ hγ x, hg.1 γ hγ x], hf.2.add hg.2⟩

theorem isContAut_smul {V : HSp D} {f : GA D V → ℂ} (hf : IsContAut V f) (c : ℂ) : IsContAut V (c • f) :=
  ⟨fun γ hγ x => by simp only [Pi.smul_apply, hf.1 γ hγ x], hf.2.const_smul c⟩

theorem isContAut_multT {V : HSp D} {S : D.what₂.Tau → SPar} {θ : InfFam D} {M : DSModel V S} {J : Set (GA D V)}
    {χ : GA D V → ℂ} {G : SmT M →ₗ[ℂ] (GA D V → ℂ)} (hG : G ∈ MultT θ M J χ) (x : SmT M) : IsContAut V (G x) := by
  obtain ⟨T, hT, rfl⟩ := hG
  induction hT using Submodule.span_induction generalizing x with
  | mem T hT =>
    induction x using PiTensorProduct.induction_on with
    | smul_tprod r v =>
      rw [map_smul, LinearEquiv.coe_coe, PiTensorProduct.lift.tprod]
      exact isContAut_smul ⟨(hT.aut v).left, (hT.aut v).cont⟩ r
    | add x y hx hy => rw [map_add]; exact isContAut_add hx hy
  | zero => simpa using isContAut_zero V
  | add T₁ T₂ _ _ h₁ h₂ => rw [map_add, LinearMap.add_apply]; exact isContAut_add (h₁ x) (h₂ x)
  | smul c T _ h => rw [map_smul, LinearMap.smul_apply]; exact isContAut_smul (h x) c

end GlobalTheory.SeeSaw.DenseRel

open GlobalTheory.SeeSaw.DenseRel in

theorem GlobalTheory.SeeSaw.perF_rel_of_steps : GlobalTheory.Published.HarishChandraModules → ∀ (D : D7) (c : Comm D) (𝒯 : Type) (t : 𝒯 → Tup c), c.Is → ∀ j ρ (h : j + 2 * ρ + 2 = D.R.m) (I : Type) [Fintype I] (s : I → 𝒯) (α : I → ℂ) (φ : ∀ i, (t (s i)).Ch j → GA D (c.X j) → ℂ) (G : ∀ i, (t (s i)).CC j), (∀ s, (t s).Is) → (∀ i a, IsContAut (c.X j) (φ i a)) → ∀ (W W' : HSp D) (S' : D.what₂.Tau → SPar) (M' : DSModel W' S') (It' : PolF D W'.rank (c.V (j + 1)).rank →ₗ[ℂ] SmT M' →ₗ[ℂ] SmT (c.M (j + 1))), GlobalTheory.Core.Mi.ItSpans (c.M (j + 1)) M' It' → (∀ P₁ P₂ v, ∑ i, α i * (t (s i)).perF j ρ h (φ i) ((G i).1 (c.It j P₁ (It' P₂ v))) = 0) → ∀ v, ∑ i, α i * (t (s i)).perF j ρ h (φ i) ((G i).1 v) = 0 := by
  intro hHC D c 𝒯 t hc j ρ h I _ s α φ G ht hφ _W W' S' M' It' hS' hrel
  have hj : j < D.R.m := by omega
  have hj1 : j + 1 < D.R.m := by omega

  have hmult : ∀ i, ∃ J χ, (G i).1 ∈ MultT c.θ (c.M j) J χ := fun i => by
    obtain ⟨J, χ, hle⟩ := (ht (s i)).CC j hj
    exact ⟨J, χ, hle (G i).2⟩
  choose J χ hG using hmult
  have hcont : ∀ i x, IsContAut (c.V j) ((G i).1 x) := fun i x => isContAut_multT (hG i) x

  have hL : ∀ (i : I) (a : (t (s i)).Ch j) (g : GA D (c.V j)), ∃ Λ : SmT (c.M j) →ₗ[ℂ] ℂ, GlobalTheory.Core.Mi.SepCont (c.M j) Λ ∧
      ∀ x, Λ x = (c.B j ρ h).per c.ψ (φ i a) (rTrans g ((G i).1 x)) := fun i a g =>
    GlobalTheory.T.besselPeriod_rightTranslate_sobolevSepContinuous D c.θ c.ψ ρ (c.B j ρ h) (c.par j) (c.M j) (J i) (χ i) g (φ i a) hc.inf hc.std (hφ i a) (G i).1 (hG i)
  choose L hLs hLe using hL
  let Λ : SmT (c.M j) →ₗ[ℂ] ℂ :=
    ∑ i, α i • ∑ a, ∑ g ∈ ((t (s i)).e j a).support, ((t (s i)).e j a g) • L i a g
  have hΛ : ∀ x, Λ x = ∑ i, α i * (t (s i)).perF j ρ h (φ i) ((G i).1 x) := by
    intro x
    simp only [Λ, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul, hLe]
    refine Finset.sum_congr rfl fun i _ => ?_
    congr 1
    unfold Tup.perF
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [((GlobalTheory.T.besselPeriod_linear_and_translationCombination D c.ψ hc.std ρ (c.B j ρ h) (φ i a) (hφ i a)).2 _ _ (hcont i x)).2]
  have hΛs : GlobalTheory.Core.Mi.SepCont (c.M j) Λ :=
    sepCont_sum _ _ _ fun i _ => sepCont_smul _ _ (sepCont_sum _ _ _ fun a _ =>
      sepCont_sum _ _ _ fun g _ => sepCont_smul _ _ (hLs i a g))
  have hK : ∀ v : (c.M j).Vec, GlobalTheory.Core.Mi.KVecP (c.M j) v → Λ (PiTensorProduct.tprod ℂ v) = 0 := by
    refine kill_of_itSpans (c.M j) (c.M (j + 1)) (c.It j) (hc.span j hj1) Λ fun P y hy => ?_
    exact kill_of_itSpans (c.M (j + 1)) M' It' hS' (Λ ∘ₗ c.It j P)
      (fun P₂ z _ => by simp only [LinearMap.comp_apply, hΛ]; exact hrel P P₂ _) y hy
  have h0 := GlobalTheory.Core.Mi.eq_zero_of_sepCont hHC D (c.V j) (c.par j) (c.M j) Λ hΛs hK
  intro v
  rw [← hΛ v, h0, LinearMap.zero_apply]

end
