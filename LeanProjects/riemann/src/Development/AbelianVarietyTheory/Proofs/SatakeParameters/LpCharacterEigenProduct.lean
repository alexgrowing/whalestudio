import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.LocalLanglandsGL
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Mono0OfLpDimEqOne
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.WeilDeligne.DetSp

open Polynomial TensorProduct Module

theorem prod_roots_charpoly {V : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (f : Module.End ℂ V) : f.charpoly.roots.prod = LinearMap.det f := by
  rw [← LinearMap.charpoly_toMatrix f (Module.finBasis ℂ V), ← Matrix.det_eq_prod_roots_charpoly,
    LinearMap.det_toMatrix]

theorem det_map {n m : ℕ} (f : Module.End ℂ (Fin n → ℂ)) (g : Module.End ℂ (Fin m → ℂ)) :
    LinearMap.det (TensorProduct.map f g) = LinearMap.det f ^ m * LinearMap.det g ^ n := by
  classical
  set b := Pi.basisFun ℂ (Fin n)
  set c := Pi.basisFun ℂ (Fin m)
  rw [← LinearMap.det_toMatrix (b.tensorProduct c), TensorProduct.toMatrix_map, Matrix.det_kronecker,
    LinearMap.det_toMatrix, LinearMap.det_toMatrix, Fintype.card_fin, Fintype.card_fin]

theorem det_diagEnd {m : ℕ} (c : Fin m → ℂ) : LinearMap.det (diagEnd c) = ∏ i, c i := by
  classical
  have e : diagEnd c = Matrix.toLin' (Matrix.diagonal c) := by
    refine LinearMap.ext fun v => funext fun i => ?_
    simp [Matrix.mulVec_diagonal]
  rw [e, LinearMap.det_toLin', Matrix.det_diagonal]

theorem sum_centred (m : ℕ) : ∑ i : Fin m, (((i : ℕ) : ℝ) - ((m : ℝ) - 1) / 2) = 0 := by
  rw [Fin.sum_univ_eq_sum_range (fun i => ((i : ℝ) - ((m : ℝ) - 1) / 2)), Finset.sum_sub_distrib,
    Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have : ∀ k : ℕ, ∑ i ∈ Finset.range k, (i : ℝ) = (k : ℝ) * ((k : ℝ) - 1) / 2 := by
    intro k
    induction k with
    | zero => simp
    | succ k ih => rw [Finset.sum_range_succ, ih]; push_cast; ring
  rw [this]; ring

variable {E : Type*} [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E))

theorem prod_qPow {ι : Type*} (s : Finset ι) (f : ι → ℝ) :
    ∏ i ∈ s, qPow w (f i) = qPow w (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [Finset.prod_insert ha, Finset.sum_insert ha, ih, qPow_add]

theorem prod_spEig (m : ℕ) : ∏ i, WDRep.spEig w m i = 1 := by
  simp only [WDRep.spEig]
  rw [prod_qPow, sum_centred, qPow_zero]

end GlobalTheory.WeilDeligne.DetSp

namespace GlobalTheory.WeilDeligne

theorem prod_eig_lpChar_lpSp : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w) (x : WD h) (l : ℕ) (σ : Weil h), ((x.lpChar (WD.lpSp h l)).eig σ).prod = ((x.eig σ).prod) ^ l := by
  intro E Ω _ _ _ _ _ A w h x l σ
  induction x using WD.ind with
  | hP n a =>
    rw [WD.lpSp, WD.lpChar_mk, WD.eig_mk, WD.eig_mk, WDRep.tensor_ρ, WDRep.sp_ρ,
      DetSp.prod_roots_charpoly, DetSp.prod_roots_charpoly, DetSp.det_map, DetSp.det_diagEnd,
      Finset.prod_zpow, ← Units.coe_prod, DetSp.prod_spEig, Units.val_one, one_zpow, one_pow, mul_one]

end GlobalTheory.WeilDeligne
