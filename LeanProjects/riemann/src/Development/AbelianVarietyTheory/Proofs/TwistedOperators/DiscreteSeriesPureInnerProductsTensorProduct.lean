import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ChosenSeries

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Matrix GlobalTheory.Chain GlobalTheory.Chain.RealIt
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Chain.RealIt

variable {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar}

theorem exists_finite_support {ι : Type} {E : ι → Type} [∀ i, AddCommGroup (E i)] [∀ i, Module ℂ (E i)]
    (x : ⨂[ℂ] i, E i) : ∃ F : ∀ i, Submodule ℂ (E i), (∀ i, FiniteDimensional ℂ (F i)) ∧
      ∀ G : ∀ i, Submodule ℂ (E i), (∀ i, F i ≤ G i) →
        x ∈ LinearMap.range (PiTensorProduct.map fun i => (G i).subtype) := by
  induction x using PiTensorProduct.induction_on with
  | smul_tprod r f =>
    refine ⟨fun i => ℂ ∙ f i, fun i => inferInstance, fun G hG => ?_⟩
    refine LinearMap.mem_range.mpr
      ⟨r • PiTensorProduct.tprod ℂ (fun i => (⟨f i, hG i (Submodule.mem_span_singleton_self (f i))⟩ : G i)), ?_⟩
    rw [map_smul, PiTensorProduct.map_tprod]
    rfl
  | add x y hx hy =>
    obtain ⟨F₁, h₁, k₁⟩ := hx
    obtain ⟨F₂, h₂, k₂⟩ := hy
    refine ⟨fun i => F₁ i ⊔ F₂ i, fun i => ?_, fun G hG => ?_⟩
    · haveI := h₁ i
      haveI := h₂ i
      infer_instance
    · exact add_mem (k₁ G fun i => le_trans le_sup_left (hG i)) (k₂ G fun i => le_trans le_sup_right (hG i))

theorem ellT_pure (M : DSModel V S) (w v : ∀ τ, M.H τ) :
    ellT M w (PiTensorProduct.tprod ℂ v) = ∏ τ, ⟪w τ, v τ⟫_ℂ := by
  unfold ellT
  rw [PiTensorProduct.lift.tprod]
  simp

private lemma eq_zero_of_ellT_map_eq_zero (M : DSModel V S) {K : D.what₂.Tau → Type} [∀ τ, NormedAddCommGroup (K τ)]
    [∀ τ, InnerProductSpace ℂ (K τ)] [hK : ∀ τ, FiniteDimensional ℂ (K τ)] (j : ∀ τ, K τ →ₗ[ℂ] M.H τ)
    (hj : ∀ τ a b, ⟪j τ a, j τ b⟫_ℂ = ⟪a, b⟫_ℂ) (z : ⨂[ℂ] τ, K τ)
    (hz : ∀ w, ellT M w (PiTensorProduct.map j z) = 0) : z = 0 := by
  classical
  let b := fun τ => stdOrthonormalBasis ℂ (K τ)
  let B := Basis.piTensorProduct (fun τ => (b τ).toBasis)
  have key : ∀ p, B.coord p = ellT M (fun τ => j τ (b τ (p τ))) ∘ₗ PiTensorProduct.map j := by
    intro p
    apply PiTensorProduct.ext
    apply MultilinearMap.ext
    intro x
    simp only [LinearMap.compMultilinearMap_apply, LinearMap.comp_apply, Module.Basis.coord_apply, B,
      Basis.piTensorProduct_repr_tprod_apply, PiTensorProduct.map_tprod, ellT_pure, hj,
      OrthonormalBasis.coe_toBasis_repr_apply, OrthonormalBasis.repr_apply_apply]
  refine B.forall_coord_eq_zero_iff.mp fun p => ?_
  rw [key, LinearMap.comp_apply]
  exact hz _

theorem ellT_separates (M : DSModel V S) (x : ⨂[ℂ] τ, M.H τ) (hx : ∀ w, ellT M w x = 0) : x = 0 := by
  obtain ⟨F, hF, hx'⟩ := exists_finite_support x
  obtain ⟨y, rfl⟩ := LinearMap.mem_range.mp (hx' F fun _ => le_rfl)
  have hy : y = 0 := eq_zero_of_ellT_map_eq_zero M (K := fun τ => F τ) (hK := hF) (fun τ => (F τ).subtype)
    (fun τ a b => rfl) y hx
  rw [hy, map_zero]

theorem inclT_injective (M : DSModel V S) : Function.Injective (inclT M) := by
  unfold inclT
  rw [injective_iff_map_eq_zero]
  intro y hy
  obtain ⟨F, hF, hy'⟩ := exists_finite_support y
  obtain ⟨z, rfl⟩ := LinearMap.mem_range.mp (hy' F fun _ => le_rfl)
  have hz : z = 0 := eq_zero_of_ellT_map_eq_zero M (K := fun τ => F τ) (hK := hF)
    (fun τ => (M.sm τ).subtype ∘ₗ (F τ).subtype) (fun τ a b => rfl) z (by
      intro w
      rw [PiTensorProduct.map_comp, LinearMap.comp_apply, hy, map_zero])
  rw [hz, map_zero]

theorem fr_conj_mem (M : DSModel V S) (τ : D.what₂.Tau) {g : Matrix (Fin V.rank) (Fin V.rank) ℂ}
    (hg : g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ)) : M.fr τ * g * (M.fr τ)⁻¹ ∈ Formalism.MainNotions.S.UJset (M.ε τ) := by
  have hd : IsUnit (M.fr τ).det := (Matrix.isUnit_iff_isUnit_det _).mp (M.fr_unit τ)
  have hPQ : M.fr τ * (M.fr τ)⁻¹ = 1 := Matrix.mul_nonsing_inv _ hd
  have hg' : gᴴ * gramAt D V τ * g = gramAt D V τ := hg
  rw [← M.fr_gram τ] at hg'
  show Formalism.REAL.inUJ (M.ε τ) _
  unfold Formalism.REAL.inUJ
  calc (M.fr τ * g * (M.fr τ)⁻¹)ᴴ * Formalism.REAL.Jm (M.ε τ) * (M.fr τ * g * (M.fr τ)⁻¹)
      = ((M.fr τ)⁻¹)ᴴ * (gᴴ * ((M.fr τ)ᴴ * Formalism.REAL.Jm (M.ε τ) * M.fr τ) * g) * (M.fr τ)⁻¹ := by
        simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
    _ = ((M.fr τ)⁻¹)ᴴ * ((M.fr τ)ᴴ * Formalism.REAL.Jm (M.ε τ) * M.fr τ) * (M.fr τ)⁻¹ := by rw [hg']
    _ = (M.fr τ * (M.fr τ)⁻¹)ᴴ * Formalism.REAL.Jm (M.ε τ) * (M.fr τ * (M.fr τ)⁻¹) := by
        simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
    _ = Formalism.REAL.Jm (M.ε τ) := by rw [hPQ]; simp

open Classical in
theorem actT_pure (M : DSModel V S) (τ : D.what₂.Tau) (g : Matrix (Fin V.rank) (Fin V.rank) ℂ) (v : ∀ ρ, M.H ρ) :
    actT M τ g (PiTensorProduct.tprod ℂ v) = PiTensorProduct.tprod ℂ (Function.update v τ (M.rep τ g (v τ))) := by
  unfold actT
  rw [PiTensorProduct.map_tprod]
  congr 1
  funext ρ
  by_cases h : ρ = τ
  · subst h
    simp
  · simp [Function.update_of_ne h]

theorem tensorLaw : ∀ (D : D7) (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S), TensorLaw M := by
  intro D V S M
  classical
  refine ⟨fun x hx => ellT_separates M x hx, inclT_injective M, ?_, ?_, ?_⟩
  · intro τ
    obtain ⟨-, -, ⟨⟨h1, -⟩, -⟩, -⟩ := M.ds τ
    have hd : IsUnit (M.fr τ).det := (Matrix.isUnit_iff_isUnit_det _).mp (M.fr_unit τ)
    have hr : M.rep τ 1 = 1 := by
      show M.σ τ (M.fr τ * 1 * (M.fr τ)⁻¹) = 1
      rw [Matrix.mul_one, Matrix.mul_nonsing_inv _ hd, h1]
    apply PiTensorProduct.ext
    apply MultilinearMap.ext
    intro v
    simp only [LinearMap.compMultilinearMap_apply, LinearMap.id_apply]
    rw [actT_pure]
    simp [hr]
  · intro τ g hg g' hg'
    obtain ⟨-, -, ⟨⟨-, hmul⟩, -⟩, -⟩ := M.ds τ
    have hd : IsUnit (M.fr τ).det := (Matrix.isUnit_iff_isUnit_det _).mp (M.fr_unit τ)
    have hQP : (M.fr τ)⁻¹ * M.fr τ = 1 := Matrix.nonsing_inv_mul _ hd
    have hsplit : M.fr τ * (g * g') * (M.fr τ)⁻¹ =
        (M.fr τ * g * (M.fr τ)⁻¹) * (M.fr τ * g' * (M.fr τ)⁻¹) := by
      calc M.fr τ * (g * g') * (M.fr τ)⁻¹ = M.fr τ * g * ((M.fr τ)⁻¹ * M.fr τ) * g' * (M.fr τ)⁻¹ := by
            rw [hQP, Matrix.mul_one, Matrix.mul_assoc (M.fr τ) g g']
        _ = _ := by simp only [Matrix.mul_assoc]
    have hr : M.rep τ (g * g') = (M.rep τ g).comp (M.rep τ g') := by
      show M.σ τ (M.fr τ * (g * g') * (M.fr τ)⁻¹) = (M.σ τ (M.fr τ * g * (M.fr τ)⁻¹)).comp (M.σ τ (M.fr τ * g' * (M.fr τ)⁻¹))
      rw [hsplit]
      exact hmul _ (fr_conj_mem M τ hg) _ (fr_conj_mem M τ hg')
    apply PiTensorProduct.ext
    apply MultilinearMap.ext
    intro v
    simp only [LinearMap.compMultilinearMap_apply, LinearMap.comp_apply]
    rw [actT_pure, actT_pure, actT_pure, hr]
    congr 1
    simp [Function.update_idem]
  · intro τ g _ w
    obtain ⟨hc, -⟩ := M.ds τ
    haveI : CompleteSpace (M.H τ) := hc
    refine ⟨Function.update w τ (ContinuousLinearMap.adjoint (M.rep τ g) (w τ)), ?_⟩
    apply PiTensorProduct.ext
    apply MultilinearMap.ext
    intro v
    simp only [LinearMap.compMultilinearMap_apply, LinearMap.comp_apply]
    rw [actT_pure, ellT_pure, ellT_pure]
    refine Finset.prod_congr rfl fun ρ _ => ?_
    by_cases h : ρ = τ
    · subst h
      simp [ContinuousLinearMap.adjoint_inner_left]
    · simp [Function.update_of_ne h]

end GlobalTheory.Chain.RealIt

end
