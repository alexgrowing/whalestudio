import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.DiscreteSpectrumResidualClassification
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LieWordExpansionUniform
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.BernsteinUnitaryProductIrreducible
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LieWordExpansionUniformStatement

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.Grow GlobalTheory.Size
open Formalism.REAL Formalism.MainNotions.S GlobalTheory.SmoothGlob GlobalTheory.LowTypeDetermined GlobalTheory.TypeSum GlobalTheory.SeriesToClosure GlobalTheory.PlaceDecomp GlobalTheory.KFinDecomp Matrix
open scoped InnerProductSpace
namespace GlobalTheory.PlaceDecomp
theorem placeDecomposition_gkMap_rankOne_values : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (N : GlobalTheory.Grid.Node D) (τ : D.what₂.Tau) (φ : GA D N.V → ℂ) (S : GA D N.V → List (List (Mx N.V.rank))) (v : GA D N.V → ℕ → N.M.H τ) (ℓ : GA D N.V → ℕ → (N.M.H τ →ₗ[ℂ] ℂ)) (C : GA D N.V → ℕ → ℝ), (∀ x, Words (lieSet (N.M.ε τ)) (S x)) → (∀ x, Ctrl (lieSet (N.M.ε τ)) (UJset (N.M.ε τ)) (N.M.σ τ) (S x)) → (∀ x, Expn (N.M.ε τ) (N.M.σ τ) (S x) (v x) (ℓ x) (C x) (res θ N.V τ (N.M.fr τ) φ x)) → ∀ (c : N.M.H τ) (ψ : GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.kFin N.M τ → GA D N.V → ℂ), (∀ u : GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.kFin N.M τ, Moves θ N.V τ (N.M.ε τ) (N.M.σ τ) (N.M.fr τ) (fun w => ⟪c, w⟫_ℂ • (u : N.M.H τ)) φ (ψ u)) → (∀ u x, ψ u x = ∑' i, ⟪c, v x i⟫_ℂ * ℓ x i u) ∧ (∀ u u', ψ (u + u') = ψ u + ψ u') ∧ (∀ (z : ℂ) u, ψ (z • u) = z • ψ u) ∧ (∀ k ∈ GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.maxCpt N.M τ, ∀ u w : GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.kFin N.M τ, (w : N.M.H τ) = N.M.rep τ k u → ψ w = rTr N.V (atTau θ N.V τ k) (ψ u)) ∧ (∀ X ∈ lieAt N.V τ, ∀ u w : GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.kFin N.M τ, (w : N.M.H τ) = dRep (N.M.rep τ) X u → ψ w = Rder θ N.V τ X (ψ u)) := by
  intro D θ hθ hp N τ φ S v ℓ C hS hc h c ψ hψ
  have hσ : Std (N.M.ε τ) (N.M.σ τ) := std_of_isDS hp.harishChandraModules (N.M.ds τ)
  have hP := N.M.fr_unit τ
  haveI : CompleteSpace (N.M.H τ) := (N.M.ds τ).1
  have hJ := N.M.fr_gram τ
  have hb := fun x => (h x).sobFun (hS x) c
  have hsm : ∀ u : GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.kFin N.M τ, Sm (N.M.ε τ) (N.M.σ τ) u := fun u => hσ.2.2.1 _ u.2
  have key : ∀ u x, ∀ y ∈ UJset (N.M.ε τ),
      res θ N.V τ (N.M.fr τ) (ψ u) x y = ∑' i, ⟪c, v x i⟫_ℂ * ℓ x i (N.M.σ τ y u) := by
    intro u x y hy
    have := (hψ u x _ _ _ _ (hS x) (hc x) (h x)).1.2.2.2.2 y hy
    simp only [map_smul, smul_eq_mul] at this
    exact this.tsum_eq.symm
  have hval : ∀ u x, ψ u x = ∑' i, ⟪c, v x i⟫_ℂ * ℓ x i u := by
    intro u x
    have := key u x 1 (one_mem_UJ _)
    rwa [res_one hθ hP, sigma_one hσ.1] at this
  refine ⟨hval, fun u u' => funext fun x => ?_, fun z u => funext fun x => ?_, ?_, ?_⟩
  · rw [Pi.add_apply, hval, hval, hval, Submodule.coe_add]
    exact (hb x).1 _ _ (hsm u) (hsm u')
  · rw [Pi.smul_apply, hval, hval, Submodule.coe_smul, smul_eq_mul]
    exact (hb x).2.1 z _ (hsm u)
  · intro k hk u w hw
    funext x
    rw [rTr, ← res_conj hP (ψ u) x k, key u x _ (K_le_UJ hk), hval, hw]
    rfl
  · intro X hX u w hw
    funext x
    have hd := (isUnit_iff_isUnit_det _).1 hP
    have hY : N.M.fr τ * X * (N.M.fr τ)⁻¹ ∈ lieSet (N.M.ε τ) := by
      refine Transport.conj_lie (G := gramAt D N.V τ) (Matrix.nonsing_inv_mul _ hd) ?_ hX
      rw [← hJ]
      calc _ = (N.M.fr τ * (N.M.fr τ)⁻¹)ᴴ * Jm (N.M.ε τ) * (N.M.fr τ * (N.M.fr τ)⁻¹) := by
            simp only [conjTranspose_mul, Matrix.mul_assoc]
        _ = _ := by rw [Matrix.mul_nonsing_inv _ hd]; simp
    have e : (w : N.M.H τ) = dRep (N.M.σ τ) (N.M.fr τ * X * (N.M.fr τ)⁻¹) u := by
      rw [hw]
      unfold dRep
      congr 1
      funext t
      rw [Transport.exp_smul_conj hP]
      rfl
    have h1 := (hσ.hasDerivAt_sobFun (hb x) (hsm u) hY).deriv
    rw [← e] at h1
    rw [hval]
    refine h1.symm.trans ?_
    unfold Rder oneP
    congr 1
    funext t
    rw [← res_conj hP (ψ u) x, ← Transport.exp_smul_conj hP, key u x _ (exp_mem_UJ hY t)]
end GlobalTheory.PlaceDecomp
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.Grow GlobalTheory.Size
open Formalism.REAL Formalism.MainNotions.S GlobalTheory.SmoothGlob GlobalTheory.LowTypeDetermined GlobalTheory.TypeSum GlobalTheory.SeriesToClosure GlobalTheory.PlaceDecomp GlobalTheory.KFinDecomp Matrix
open scoped InnerProductSpace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twist_gkMap_rankOne_values : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (N : GlobalTheory.Grid.Node D) (τ : D.what₂.Tau) (φ : GA D N.V → ℂ) (S : GA D N.V → List (List (Mx N.V.rank))) (v : GA D N.V → ℕ → N.M.H τ) (ℓ : GA D N.V → ℕ → (N.M.H τ →ₗ[ℂ] ℂ)) (C : GA D N.V → ℕ → ℝ), (∀ x, Words (lieSet (N.M.ε τ)) (S x)) → (∀ x, Ctrl (lieSet (N.M.ε τ)) (UJset (N.M.ε τ)) (N.M.σ τ) (S x)) → (∀ x, Expn (N.M.ε τ) (N.M.σ τ) (S x) (v x) (ℓ x) (C x) (res θ N.V τ (N.M.fr τ) φ x)) → ∀ (c : N.M.H τ) (ψ : GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.kFin N.M τ → GA D N.V → ℂ), (∀ u : GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.kFin N.M τ, Moves θ N.V τ (N.M.ε τ) (N.M.σ τ) (N.M.fr τ) (fun w => ⟪c, w⟫_ℂ • (u : N.M.H τ)) φ (ψ u)) → (∀ u x, ψ u x = ∑' i, ⟪c, v x i⟫_ℂ * ℓ x i u) ∧ (∀ u u', ψ (u + u') = ψ u + ψ u') ∧ (∀ (z : ℂ) u, ψ (z • u) = z • ψ u) ∧ (∀ k ∈ GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.maxCpt N.M τ, ∀ u w : GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.kFin N.M τ, (w : N.M.H τ) = N.M.rep τ k u → ψ w = rTr N.V (atTau θ N.V τ k) (ψ u)) ∧ (∀ X ∈ lieAt N.V τ, ∀ u w : GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.kFin N.M τ, (w : N.M.H τ) = dRep (N.M.rep τ) X u → ψ w = Rder θ N.V τ X (ψ u)) := by
  first | exact @_root_.GlobalTheory.PlaceDecomp.placeDecomposition_gkMap_rankOne_values | exact _root_.GlobalTheory.PlaceDecomp.placeDecomposition_gkMap_rankOne_values | (intros; apply _root_.GlobalTheory.PlaceDecomp.placeDecomposition_gkMap_rankOne_values <;> assumption)
end
