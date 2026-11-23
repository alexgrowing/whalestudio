import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DatVtEq
import Formalism.LocalToGlobal.Columns.MtAdWtIrr
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.HwFixEx
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.HwFixLine
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsPolynomialModelCoefficientSpaceRealPoints
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsotypicFactorOfIsIrreduciblePiFiniteGroups
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.StdCharFinitePartRationalEqExpTrace
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsCoefDualPair
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Formalism.L2 Formalism.L2.Host Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.MtIn
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.MtIn

open Formalism.L2.Col

theorem map_inv_mat {E K : Type} [Field E] [Field K] (f : E →+* K) {n : ℕ} (γE : GL (Fin n) E) :
    ((γE : Matrix (Fin n) (Fin n) E).map f)⁻¹ = ((γE : Matrix (Fin n) (Fin n) E)⁻¹).map f := by
  have h := congrArg (fun g : GL (Fin n) K => (g : Matrix (Fin n) (Fin n) K)) (map_inv (Matrix.GeneralLinearGroup.map f) γE)
  have h1 : ((Matrix.GeneralLinearGroup.map f γE : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = (γE : Matrix (Fin n) (Fin n) E).map f := rfl
  have h2 : ((Matrix.GeneralLinearGroup.map f γE⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = ((γE⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E).map f := rfl
  simp only [Matrix.coe_units_inv] at h h2
  rw [h1] at h
  rw [h2] at h
  exact h.symm

theorem isAlgWeight_of_equiv {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ} {W W' : Type}
    [AddCommGroup W] [Module ℂ W] [AddCommGroup W'] [Module ℂ W']
    (ρ : Representation ℂ (ReciprocityTheory.Aut.GQ L n) W) (ρ' : Representation ℂ (ReciprocityTheory.Aut.GQ L n) W')
    (T : W ≃ₗ[ℂ] W') (hT : ∀ γ x, T (ρ γ x) = ρ' γ (T x)) (h : Formalism.AUTREP.IsAlgWeight L n ρ) :
    Formalism.AUTREP.IsAlgWeight L n ρ' := by
  obtain ⟨hf, κ, hfi, hd, bs, P, hP⟩ := h
  refine ⟨LinearEquiv.finiteDimensional T, κ, hfi, hd, bs.map T, P, fun γ γ₀ hm => ?_⟩
  rw [← hP γ γ₀ hm]
  ext i j
  rw [LinearMap.toMatrix_apply, LinearMap.toMatrix_apply, Module.Basis.map_apply, ← hT, Module.Basis.map_repr,
    LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply]

theorem exists_weight_of_coefMap {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ} {ι : Type} [Fintype ι]
    {K : Type} [Field K] (φ : K →+* ℂ) (lab : ι → L →+* K) (emb : ι → L →+* ℂ) (hlab : ∀ τ x, φ (lab τ x) = emb τ x)
    (hinj : Function.Injective emb) (hcm : ∀ τ τ', emb τ ≠ ComplexEmbedding.conjugate (emb τ'))
    (lam : ι → DomWeight n) {W : Type} [AddCommGroup W] [Module ℂ W] (ρ : Representation ℂ (ReciprocityTheory.Aut.GQ L n) W)
    (c0 : VV K lam →ₛₗ[φ] W) (h0 : ∀ γ v, c0 (rhoVr lab lam (mtwRat γ) v) = ρ γ (c0 v))
    (h1 : LinearIndependent ℂ fun i => c0 (bVV K lam i))
    (h2 : Submodule.span ℂ (Set.range fun i => c0 (bVV K lam i)) = ⊤) :
    ∃ (alg : Formalism.AUTREP.IsAlgWeight L n ρ) (irr : ρ.IsIrreducible), ∀ (a : NG.AlgWt L n) (τ : ι) (lam0 : Fin n → ℤ),
      NG.AlgWt.IsDual { W := W, ρ := ρ, alg := alg, irr := irr } a → a.HWAt (emb τ) lam0 → lam0 = (lam τ).w := by
  obtain ⟨T, hT⟩ := GlobalTheory.CoefReal.exists_scalarExt φ lam c0 h1 h2
  have hint : ∀ (γ : ReciprocityTheory.Aut.GQ L n) (x : VV ℂ lam), T (mtRep emb lam γ x) = ρ γ (T x) := by
    intro γ x
    have hfam : (fun τ => Formalism.UG.bc φ (invTrK (embGL lab (mtwRat γ)) τ)) = mtwInvTr (mtwEmb emb (mtwRat γ)) := by
      funext τ
      apply Units.ext
      ext a b
      simp [mtwInvTr, mtwEmb, inside₂, invTrK_coe, bc_coe, embGL_coe, ← map_inv, hlab, map_inv_mat]
    have hL : T.toLinearMap ∘ₗ mtRep emb lam γ = ρ γ ∘ₗ T.toLinearMap := by
      refine LinearMap.ext_on_range (GlobalTheory.CoefModel.span_mapVV φ lam) fun i => ?_
      show T (rhoK lam (mtwInvTr (mtwEmb emb (mtwRat γ))) (GlobalTheory.CoefModel.mapVV φ lam _)) = ρ γ (T _)
      rw [← hfam, ← GlobalTheory.CoefModel.mapVV_rhoK, hT, hT]
      exact h0 γ _
    exact LinearMap.congr_fun hL x
  have hi : TenIrr emb lam := tenIrr_of' highest_weight_fixed_exists highest_weight_fixed_line emb hinj hcm lam
  have alg : Formalism.AUTREP.IsAlgWeight L n ρ := isAlgWeight_of_equiv (mtRep emb lam) ρ T hint (mtRep_alg emb lam)
  have irr : ρ.IsIrreducible :=
    GlobalTheory.PiIsotypic.isIrreducible_of_linearEquiv (mtRep emb lam) ρ T (fun g v => (hint g v).symm) hi
  refine ⟨alg, irr, fun a τ lam0 hd hw => ?_⟩
  obtain ⟨B, hB0, hB⟩ : ∃ B : W →ₗ[ℂ] a.W →ₗ[ℂ] ℂ, B ≠ 0 ∧ ∀ γ x y, B (ρ γ x) (a.ρ γ y) = B x y := hd
  have hd' : ∃ B : VV ℂ lam →ₗ[ℂ] a.W →ₗ[ℂ] ℂ, B ≠ 0 ∧ ∀ γ x y, B (mtRep emb lam γ x) (a.ρ γ y) = B x y := by
    refine ⟨B ∘ₗ T.toLinearMap, fun h => hB0 (LinearMap.ext fun w => ?_), fun γ x y => ?_⟩
    · obtain ⟨x, rfl⟩ := T.surjective w
      exact LinearMap.congr_fun h x
    · show B (T (mtRep emb lam γ x)) (a.ρ γ y) = B (T x) y
      rw [hint]
      exact hB γ (T x) y
  exact mtWtOf_hw_dual highest_weight_fixed_exists highest_weight_fixed_line emb hinj hcm lam τ a lam0 hd' hw

theorem wt_main : ∀ (D : D7) (V : HSp D) (P : principalLevelFrame.RowPsi V V.rank) (e : ReciprocityTheory.Aut.GQ D.host.E V.rank ≃* Formalism.L2.Theta.GQ V), RatIso P e → ∀ (c : CoefA V) (lam : D.what₂.Tau → DomWeight V.rank) (c0 : VV D.what₂.LL lam →ₛₗ[D.what₂.embLL] c.W), Bridge.CoefMapTie V c.coef c0 (rhoVr (labLL D) lam) → ∃ (alg : Formalism.AUTREP.IsAlgWeight D.host.E V.rank (wtRep c e)) (irr : (wtRep c e).IsIrreducible), ∀ (a : NG.AlgWt D.host.E V.rank) (τ : D.what₂.Tau) (lam0 : Fin V.rank → ℤ), NG.AlgWt.IsDual { W := c.W, ρ := wtRep c e, alg := alg, irr := irr } a → a.HWAt (Formalism.L2.embT D τ) lam0 → lam0 = (lam τ).w := by
  intro D V P e hR c lam c0 ht
  exact exists_weight_of_coefMap D.what₂.embLL (labLL D) (tauE D) GlobalTheory.CoefSpace.embLL_labLL (GlobalTheory.StdRat.tauE_injective D)
    (fun τ τ' h => (GlobalTheory.StdRat.tauE_cm D (tauE D τ')).1 ⟨τ', rfl⟩ ⟨τ, h⟩) lam (wtRep c e) c0
    (fun γ v => ht.1 (e γ) (mtwRat γ) ((hR γ).2 _ (congrArg Units.val (mtwInc_mtwRatFun γ)).symm) v) ht.2.1 ht.2.2

end GlobalTheory.MtIn

end
