import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.RankOneUnitary
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.WeightRegularOfExt

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial NumberField IsDedekindDomain
open GlobalTheory.WeilDeligne
open scoped TensorProduct

namespace GlobalTheory.RowTie.EigTwist

theorem roots_charpoly_smul_matrix {ι : Type*} [Fintype ι] [DecidableEq ι] (M : Matrix ι ι ℂ) (u : ℂ) :
    (u • M).charpoly.roots = M.charpoly.roots.map (· * u) := by
  have hM := (IsAlgClosed.splits M.charpoly).eq_prod_roots_of_monic (Matrix.charpoly_monic M)
  have hc : Multiset.card M.charpoly.roots = Fintype.card ι := by
    rw [← (IsAlgClosed.splits M.charpoly).natDegree_eq_card_roots, Matrix.charpoly_natDegree_eq_dim]
  suffices (u • M).charpoly = ((M.charpoly.roots.map (· * u)).map fun α => X - C α).prod by
    rw [this, roots_multiset_prod_X_sub_C]
  rcases eq_or_ne u 0 with rfl | hu
  · simp [hc]
  · refine Polynomial.funext fun x => ?_
    have h1 := congrArg (eval (x / u)) hM
    rw [Matrix.eval_charpoly, eval_multiset_prod, Multiset.map_map] at h1
    have e : Matrix.scalar ι x - u • M = u • (Matrix.scalar ι (x / u) - M) := by
      ext a b
      by_cases hab : a = b
      · subst hab
        simp
        field_simp
      · simp [Matrix.diagonal_apply_ne _ hab]
    rw [Matrix.eval_charpoly, e, Matrix.det_smul, h1, eval_multiset_prod, Multiset.map_map,
      Multiset.map_map, ← hc, ← Multiset.prod_replicate, ← Multiset.map_const, ← Multiset.prod_map_mul]
    refine congrArg _ (Multiset.map_congr rfl fun α _ => ?_)
    simp
    field_simp

theorem roots_charpoly_smul {V : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (f : Module.End ℂ V) (u : ℂ) : (u • f).charpoly.roots = f.charpoly.roots.map (· * u) := by
  rw [← LinearMap.charpoly_toMatrix (u • f) (Module.finBasis ℂ V),
    ← LinearMap.charpoly_toMatrix f (Module.finBasis ℂ V), map_smul, roots_charpoly_smul_matrix]

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {B : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver B w}

theorem eig_lpTw (x : WD h) {φ : Weil h} (hφ : deg φ = 1) (s : ℝ) :
    (x.lpTw s).eig φ = (x.eig φ).map (· * ((normV w : ℕ) : ℂ) ^ ((s : ℝ) : ℂ)) := by
  induction x using WD.ind with
  | hP n a =>
    rw [WD.lpTw_mk, WD.eig_mk, WD.eig_mk, WDRep.tw_ρ, hφ, zpow_one, roots_charpoly_smul]

theorem eig_lpChar (x y : WD h) (φ : Weil h) (hy : y.lpDim = 1) (c : ℂ) (hc : y.eig φ = {c}) :
    (x.lpChar y).eig φ = (x.eig φ).map (· * c) := by
  induction x using WD.ind with
  | hP n a =>
  induction y using WD.ind with
  | hP m b =>
    rw [WD.lpDim_mk, Module.finrank_fin_fun] at hy
    subst hy
    rw [WD.eig_mk] at hc
    have hb : b.ρ φ = c • 1 := by
      have hp : (b.ρ φ).charpoly = X - C c := by
        rw [(IsAlgClosed.splits _).eq_prod_roots_of_monic (LinearMap.charpoly_monic _), hc]
        simp
      have h3 := LinearMap.aeval_self_charpoly (b.ρ φ)
      rw [hp, map_sub, aeval_X, aeval_C, sub_eq_zero, Algebra.algebraMap_eq_smul_one] at h3
      exact h3
    rw [WD.lpChar_mk, WD.eig_mk, WD.eig_mk, WDRep.tensor_ρ, hb]
    let e : (Fin n → ℂ) ⊗[ℂ] (Fin 1 → ℂ) ≃ₗ[ℂ] (Fin n → ℂ) :=
      (TensorProduct.congr (LinearEquiv.refl ℂ _) (LinearEquiv.funUnique (Fin 1) ℂ ℂ)).trans
        (TensorProduct.rid ℂ _)
    have he : e.conj (TensorProduct.map (a.ρ φ) (c • 1)) = c • a.ρ φ := by
      refine LinearMap.ext fun v => ?_
      obtain ⟨t, rfl⟩ := e.surjective v
      rw [LinearEquiv.conj_apply, LinearMap.comp_apply, LinearMap.comp_apply, LinearEquiv.coe_coe]
      erw [LinearEquiv.symm_apply_apply]
      induction t using TensorProduct.induction_on with
      | zero => simp
      | tmul x y => simp [e, smul_smul, mul_comm]
      | add x y hx hy => simp only [map_add, hx, hy]
    rw [← LinearEquiv.charpoly_conj e, he, roots_charpoly_smul]

end GlobalTheory.RowTie.EigTwist

open GlobalTheory.RowTie.EigTwist in

theorem GlobalTheory.RowTie.eigLaws_of_wdTie : ∀ (R : Ranks) (H : Host R) (what₂ : Rows.Data R) (N : NData R H what₂)
    (A : NAut N) (T : GlobalTheory.RowTie.WDTie N A), GlobalTheory.LocalInv.EigLaws N A T.eig := by
  intro R H what₂ N A T w σ hσ
  have hW : σ ∈ Weil (N.plOm.2 w) := mem_Weil_of_isFrob _ hσ
  let φ : Weil (N.plOm.2 w) := ⟨σ, hW⟩
  have hφ : deg φ = 1 := deg_eq_one_iff.mpr hσ
  have key : ∀ a, T.eig w a σ = (T.e w a).eig φ := fun a => by
    rw [WDTie.eig, WD.inePol_of_mem _ hW]
    rfl
  refine ⟨fun a => ?_, fun a s => ?_, fun a χ c hχ hc => ?_⟩
  · rw [key, WD.card_eig, T.dim]
  · rw [key, key, T.tw, eig_lpTw _ hφ]
  · rw [key] at hc
    rw [key, key, T.char _ _ _ hχ, eig_lpChar _ _ _ (by rw [T.dim, hχ]) c hc]
