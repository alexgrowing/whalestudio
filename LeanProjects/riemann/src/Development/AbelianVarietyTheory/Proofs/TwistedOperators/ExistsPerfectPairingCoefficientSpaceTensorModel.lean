import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MeasurePreservingMulRight
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.StepUnfold
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsDefiniteOfAllPlus
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open GlobalTheory.ChiGrid GlobalTheory.RowReal GlobalTheory.IndefiniteRowSideFullHecke.MinorOrderedEntries
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.CoefPairTens

open GlobalTheory.DefLift GlobalTheory.DefiniteMult Formalism.IndefR.Mult

variable {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar} {M : DSModel V S}

theorem sigma_one (M : DSModel V S) (τ : D.what₂.Tau) : M.σ τ 1 = 1 := (M.ds τ).2.2.1.1.1

theorem sigma_mul (hp : AllPlus M) (τ : D.what₂.Tau) (a b : Matrix.unitaryGroup (Fin V.rank) ℂ) :
    M.σ τ ((a : Matrix (Fin V.rank) (Fin V.rank) ℂ) * b) = (M.σ τ a).comp (M.σ τ b) := by
  have hm : ∀ x : Matrix.unitaryGroup (Fin V.rank) ℂ,
      (x : Matrix (Fin V.rank) (Fin V.rank) ℂ)ᴴ * Formalism.REAL.Jm (M.ε τ) * x = Formalism.REAL.Jm (M.ε τ) := fun x => by
    rw [hp.jm τ, Matrix.mul_one]
    exact Matrix.mem_unitaryGroup_iff'.1 x.2
  exact (M.ds τ).2.2.1.1.2 _ (hm a) _ (hm b)

theorem sigma_comp_inv (hp : AllPlus M) (τ : D.what₂.Tau) (v : Matrix.unitaryGroup (Fin V.rank) ℂ) :
    ((M.σ τ v : M.H τ →L[ℂ] M.H τ) : M.H τ →ₗ[ℂ] M.H τ) ∘ₗ
      ((M.σ τ (v⁻¹ : Matrix.unitaryGroup (Fin V.rank) ℂ) : M.H τ →L[ℂ] M.H τ) : M.H τ →ₗ[ℂ] M.H τ) = LinearMap.id := by
  refine LinearMap.ext fun x => ?_
  show M.σ τ v (M.σ τ (v⁻¹ : Matrix.unitaryGroup (Fin V.rank) ℂ) x) = x
  rw [← ContinuousLinearMap.comp_apply, ← sigma_mul hp, ← Submonoid.coe_mul, mul_inv_cancel, OneMemClass.coe_one,
    sigma_one]
  rfl

theorem unfr_one (M : DSModel V S) (τ : D.what₂.Tau) : unfr M τ 1 = 1 := by
  unfold unfr
  rw [Matrix.mul_one, Matrix.nonsing_inv_mul _ (fr_det M τ)]

theorem pairEquiv_realAll : ∀ (D : D7) (V : HSp D) (S : D.what₂.Tau → SPar) (M : Formalism.IndefR.Mult.DSModel V S) (θ : InfFam D) (c : CoefA V) (pr : c.W →ₗ[ℂ] SmT M →ₗ[ℂ] ℂ), IsInfFam θ → GlobalTheory.DefLift.AllPlus M → c.Is → IsDualPair θ M c pr → ∃ E : c.W ≃ₗ[ℂ] Module.Dual ℂ (⨂[ℂ] τ, M.H τ), ∀ (u : UG D.what₂.Tau V.rank) (w : c.W), E (c.ρ (realAll θ V (fun τ => GlobalTheory.DefLift.unfr M τ (u τ))) w) = E w ∘ₗ PiTensorProduct.map (fun τ => ((M.σ τ ((u τ)⁻¹ : Matrix.unitaryGroup (Fin V.rank) ℂ) : M.H τ →L[ℂ] M.H τ) : M.H τ →ₗ[ℂ] M.H τ)) := by
  intro D V S M θ c pr hθ hp hc hpr
  classical
  have m := AllPlus.finite_smooth_irreducible D V S M hp
  obtain ⟨-, inj, π, hπ, -⟩ := tensor_irreducible D V S M m hp
  have key := pair_tens hp (fun τ => (m τ).2.1) inj hπ hpr
  have hb := pair_bijective hθ hp hc hpr
  let e : SmT M ≃ₗ[ℂ] ⨂[ℂ] τ, M.H τ := PiTensorProduct.congr fun τ => LinearEquiv.ofTop (M.sm τ) (m τ).2.1
  have he : ∀ x, e x = inclT M x := fun x => rfl
  let E : c.W ≃ₗ[ℂ] Module.Dual ℂ (⨂[ℂ] τ, M.H τ) := (LinearEquiv.ofBijective pr hb).trans e.symm.dualMap
  have hE : ∀ w y, E w y = pr w (e.symm y) := fun w y => rfl
  let F : ∀ τ, Matrix.unitaryGroup (Fin V.rank) ℂ → (M.H τ →ₗ[ℂ] M.H τ) := fun τ v =>
    ((M.σ τ v : M.H τ →L[ℂ] M.H τ) : M.H τ →ₗ[ℂ] M.H τ)
  have hact : ∀ τ (v : Matrix.unitaryGroup (Fin V.rank) ℂ), actT M τ (unfr M τ v) =
      PiTensorProduct.map (Function.update (fun ρ => (LinearMap.id : M.H ρ →ₗ[ℂ] M.H ρ)) τ (F τ v)) := by
    intro τ v
    unfold actT
    rw [rep_unfr]
  have hπe : ∀ τ v x, π τ v x = e.symm (actT M τ (unfr M τ v) (e x)) := fun τ v x => by
    apply e.injective
    rw [LinearEquiv.apply_symm_apply, he, he, hπ]
  have hinv : ∀ τ (v : Matrix.unitaryGroup (Fin V.rank) ℂ) x, π τ v (π τ v⁻¹ x) = x := by
    intro τ v x
    rw [hπe, hπe, LinearEquiv.apply_symm_apply, hact, hact, ← LinearMap.comp_apply (PiTensorProduct.map _),
      ← PiTensorProduct.map_comp]
    have : (fun ρ => Function.update (fun ρ => (LinearMap.id : M.H ρ →ₗ[ℂ] M.H ρ)) τ (F τ v) ρ ∘ₗ
        Function.update (fun ρ => (LinearMap.id : M.H ρ →ₗ[ℂ] M.H ρ)) τ (F τ v⁻¹) ρ) = fun ρ => LinearMap.id := by
      funext ρ
      by_cases h : ρ = τ
      · subst h
        simp only [Function.update_self]
        exact GlobalTheory.CoefPairTens.sigma_comp_inv hp ρ v
      · simp only [Function.update_of_ne h, LinearMap.id_comp]
    rw [this, PiTensorProduct.map_id, LinearMap.id_apply, LinearEquiv.symm_apply_apply]
  have one : ∀ τ (v : Matrix.unitaryGroup (Fin V.rank) ℂ) w,
      E (c.ρ (atTau θ V τ (unfr M τ v)) w) =
        E w ∘ₗ PiTensorProduct.map (Function.update (fun ρ => (LinearMap.id : M.H ρ →ₗ[ℂ] M.H ρ)) τ (F τ v⁻¹)) := by
    intro τ v w
    refine LinearMap.ext fun y => ?_
    obtain ⟨x, rfl⟩ := e.surjective y
    rw [LinearMap.comp_apply, hE, hE, ← hact, ← hπe, LinearEquiv.symm_apply_apply]
    have h1 := key τ v (c.ρ (atTau θ V τ (unfr M τ v)) w) (π τ v⁻¹ x)
    rw [hinv, ← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply] at h1
    exact h1
  refine ⟨E, fun u w => ?_⟩
  let us : Finset D.what₂.Tau → UG D.what₂.Tau V.rank := fun s ρ => if ρ ∈ s then u ρ else 1
  have hM : ∀ (s : Finset D.what₂.Tau) ρ, unfr M ρ (us s ρ) ∈ Formalism.QuantumDeterminants.UH (gramAt D V ρ) := fun s ρ =>
    hp.unfr_mem ρ _
  have ind : ∀ s : Finset D.what₂.Tau, ∀ w, E (c.ρ (realAll θ V (fun ρ => unfr M ρ (us s ρ))) w) =
      E w ∘ₗ PiTensorProduct.map (fun ρ => F ρ (us s ρ)⁻¹) := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      intro w
      have h0 : (fun ρ => unfr M ρ (us ∅ ρ)) = 1 := by
        funext ρ
        have : us ∅ ρ = 1 := if_neg (Finset.notMem_empty ρ)
        rw [this, OneMemClass.coe_one, Pi.one_apply]
        exact GlobalTheory.CoefPairTens.unfr_one M ρ
      have h1 : (fun ρ => F ρ (us ∅ ρ)⁻¹) = fun ρ => LinearMap.id := by
        funext ρ
        have : us ∅ ρ = 1 := if_neg (Finset.notMem_empty ρ)
        show ((M.σ ρ ((us ∅ ρ)⁻¹ : Matrix.unitaryGroup (Fin V.rank) ℂ) : M.H ρ →L[ℂ] M.H ρ) : M.H ρ →ₗ[ℂ] M.H ρ) = _
        rw [this, inv_one, OneMemClass.coe_one, GlobalTheory.CoefPairTens.sigma_one]
        rfl
      rw [h0, realAll_one hθ, map_one, Module.End.one_apply, h1, PiTensorProduct.map_id, LinearMap.comp_id]
    | insert τ s hτ ih =>
      intro w
      have hs : us s τ = 1 := if_neg hτ
      have h3 : us (insert τ s) τ = u τ := if_pos (Finset.mem_insert_self τ s)
      have h4 : ∀ ρ, ρ ≠ τ → us (insert τ s) ρ = us s ρ := fun ρ h => by
        simp only [us, Finset.mem_insert, h, false_or]
      rw [realAll_eq_atTau_mul hθ (hM (insert τ s)) τ]
      have h2 : Function.update (fun ρ => unfr M ρ (us (insert τ s) ρ)) τ 1 = fun ρ => unfr M ρ (us s ρ) := by
        funext ρ
        by_cases h : ρ = τ
        · rw [h, Function.update_self, hs, OneMemClass.coe_one, GlobalTheory.CoefPairTens.unfr_one]
        · rw [Function.update_of_ne h, h4 ρ h]
      rw [h2, map_mul, Module.End.mul_apply, h3, one, ih, LinearMap.comp_assoc, ← PiTensorProduct.map_comp]
      congr 2
      funext ρ
      by_cases h : ρ = τ
      · subst h
        rw [Function.update_self, hs, h3]
        show ((M.σ ρ ((1 : Matrix.unitaryGroup (Fin V.rank) ℂ)⁻¹ : Matrix.unitaryGroup (Fin V.rank) ℂ) :
          M.H ρ →L[ℂ] M.H ρ) : M.H ρ →ₗ[ℂ] M.H ρ) ∘ₗ F ρ (u ρ)⁻¹ = F ρ (u ρ)⁻¹
        rw [inv_one, OneMemClass.coe_one, GlobalTheory.CoefPairTens.sigma_one]
        rfl
      · rw [Function.update_of_ne h, h4 ρ h, LinearMap.comp_id]
  have huniv : us Finset.univ = u := funext fun ρ => if_pos (Finset.mem_univ ρ)
  have := ind Finset.univ w
  rw [huniv] at this
  exact this

end GlobalTheory.CoefPairTens

end
