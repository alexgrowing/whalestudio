import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.WeakApproximationFinitePlace
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ThetaCoefficientOfConvergence
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RallisConvIffInnerProduct

noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open IsDedekindDomain NumberField
open GlobalTheory.RegSch (ikS projS Lvl)

namespace PositivityTheory.Rg.Rsw.L.LThCoef

theorem rinv_of_rank {K : Type*} [Field K] {m n : ℕ} (x : Matrix (Fin m) (Fin n) K) (h : x.rank = m) :
    ∃ x' : Matrix (Fin n) (Fin m) K, x * x' = 1 := by
  have hr : LinearMap.range x.mulVecLin = ⊤ := by
    apply Submodule.eq_top_of_finrank_eq
    rw [← Matrix.rank, h]
    simp
  obtain ⟨g, hg⟩ := x.mulVecLin.exists_rightInverse_of_surjective hr
  refine ⟨LinearMap.toMatrix' g, ?_⟩
  have e : LinearMap.toMatrix' (x.mulVecLin ∘ₗ g) = x * LinearMap.toMatrix' g := by
    show LinearMap.toMatrix' (Matrix.toLin' x ∘ₗ g) = _
    rw [LinearMap.toMatrix'_comp, LinearMap.toMatrix'_toLin']
  rw [← e, hg, LinearMap.toMatrix'_id]

theorem orbit_mat {K : Type*} [Field K] [StarRing K] {m n : ℕ} (J : Matrix (Fin m) (Fin m) K) (hJ : IsUnit J.det)
    (x y : Matrix (Fin m) (Fin n) K) (x' y' : Matrix (Fin n) (Fin m) K) (hx : x * x' = 1) (hy : y * y' = 1)
    (h : xᴴ * (J * x) = yᴴ * (J * y)) : ∃ g : Matrix (Fin m) (Fin m) K, g * x = y ∧ gᴴ * (J * g) = J := by
  have hL : y'ᴴ * yᴴ = 1 := by rw [← Matrix.conjTranspose_mul, hy, Matrix.conjTranspose_one]
  have h0 : J * (y * (1 - x' * x)) = 0 := by
    calc J * (y * (1 - x' * x)) = (y'ᴴ * yᴴ) * (J * y) * (1 - x' * x) := by
          rw [hL, Matrix.one_mul, Matrix.mul_assoc]
      _ = y'ᴴ * (yᴴ * (J * y)) * (1 - x' * x) := by rw [Matrix.mul_assoc y'ᴴ]
      _ = y'ᴴ * (xᴴ * (J * x)) * (1 - x' * x) := by rw [h]
      _ = y'ᴴ * xᴴ * J * (x - x * x' * x) := by
          simp only [Matrix.mul_sub, Matrix.mul_one, Matrix.mul_assoc]
      _ = 0 := by rw [hx, Matrix.one_mul, sub_self, Matrix.mul_zero]
  have h1 : y * (1 - x' * x) = 0 := by
    have := congrArg (fun M => J⁻¹ * M) h0
    simp only [Matrix.mul_zero] at this
    rwa [← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hJ, Matrix.one_mul] at this
  refine ⟨y * x', ?_, ?_⟩
  · have : y - y * (x' * x) = 0 := by rw [← h1, Matrix.mul_sub, Matrix.mul_one]
    rw [Matrix.mul_assoc]
    exact (sub_eq_zero.1 this).symm
  · calc (y * x')ᴴ * (J * (y * x')) = x'ᴴ * (yᴴ * (J * y)) * x' := by
          rw [Matrix.conjTranspose_mul]; simp only [Matrix.mul_assoc]
      _ = x'ᴴ * (xᴴ * (J * x)) * x' := by rw [h]
      _ = (x * x')ᴴ * (J * (x * x')) := by
          rw [Matrix.conjTranspose_mul]; simp only [Matrix.mul_assoc]
      _ = J := by rw [hx, Matrix.conjTranspose_one, Matrix.one_mul, Matrix.mul_one]

variable {D : D7}

theorem gramQ_eq' (W : HSp D) {n : ℕ} (x : Matrix (Fin W.rank) (Fin n) D.host.E) : gramQ W x = xᴴ * (HSpace.gram W * x) := rfl

theorem exists_rat (W : HSp D) (γ : GQ W) : ∃ δ : Matrix (Fin W.rank) (Fin W.rank) D.host.E, rat δ = mt W γ := by
  obtain ⟨δ, hδ⟩ := (mem_GQ_iff W γ.1).1 γ.2
  exact ⟨δ, hδ⟩

def dl (W : HSp D) (γ : GQ W) : Matrix (Fin W.rank) (Fin W.rank) D.host.E := Classical.choose (exists_rat W γ)

theorem rat_dl (W : HSp D) (γ : GQ W) : rat (dl W γ) = mt W γ := Classical.choose_spec (exists_rat W γ)

theorem dl_unitary (W : HSp D) (γ : GQ W) : (dl W γ)ᴴ * (HSpace.gram W * dl W γ) = HSpace.gram W := by
  apply rat_injective
  rw [rat_mul, rat_mul, rat_conjTranspose, rat_dl]
  exact mt_unitary W γ.1

theorem dl_inv_mul (W : HSp D) (γ : GQ W) : dl W γ⁻¹ * dl W γ = 1 := by
  apply rat_injective
  rw [rat_mul, rat_dl, rat_dl, rat_one]
  exact mt_inv_mul W γ.1

theorem orbit_equiv (W : HSp D) {n : ℕ} (x₀ : Matrix (Fin W.rank) (Fin n) D.host.E) (hx₀ : x₀.rank = W.rank) :
    ∃ e : GQ W ≃ {y : Matrix (Fin W.rank) (Fin n) D.host.E // y.rank = W.rank ∧ gramQ W y = gramQ W x₀},
      ∀ γ, rat (e γ).1 = mm (mt W γ) (rat x₀) := by
  obtain ⟨x', hx'⟩ := rinv_of_rank x₀ hx₀
  have hrk : ∀ γ : GQ W, (dl W γ * x₀).rank = W.rank := fun γ => by
    refine le_antisymm (Matrix.rank_le_height _) ?_
    calc W.rank = x₀.rank := hx₀.symm
      _ = (dl W γ⁻¹ * (dl W γ * x₀)).rank := by rw [← Matrix.mul_assoc, dl_inv_mul, Matrix.one_mul]
      _ ≤ _ := Matrix.rank_mul_le_right _ _
  have hgr : ∀ γ : GQ W, gramQ W (dl W γ * x₀) = gramQ W x₀ := fun γ => by
    rw [gramQ_eq', gramQ_eq', Matrix.conjTranspose_mul]
    calc x₀ᴴ * (dl W γ)ᴴ * (HSpace.gram W * (dl W γ * x₀))
        = x₀ᴴ * ((dl W γ)ᴴ * (HSpace.gram W * dl W γ) * x₀) := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [dl_unitary]
  let f : GQ W → {y : Matrix (Fin W.rank) (Fin n) D.host.E // y.rank = W.rank ∧ gramQ W y = gramQ W x₀} :=
    fun γ => ⟨dl W γ * x₀, hrk γ, hgr γ⟩
  have hinj : Function.Injective f := by
    intro γ γ' hγ
    have h1 : dl W γ * x₀ = dl W γ' * x₀ := congrArg Subtype.val hγ
    have h2 : dl W γ = dl W γ' := by
      have := congrArg (· * x') h1
      simpa only [Matrix.mul_assoc, hx', Matrix.mul_one] using this
    have h3 : mt W γ = mt W γ' := by rw [← rat_dl, ← rat_dl, h2]
    exact Subtype.ext (mt_injective W h3)
  have hsurj : Function.Surjective f := by
    rintro ⟨y, hyr, hyg⟩
    obtain ⟨y', hy'⟩ := rinv_of_rank y hyr
    obtain ⟨g, hgx, hgu⟩ := orbit_mat (HSpace.gram W) (gram_isUnit_det W) x₀ y x' y' hx' hy'
      (by rw [← gramQ_eq', ← gramQ_eq', hyg])
    have hM : adj (rat g) * (gA W * rat g) = gA W := by
      rw [← rat_conjTranspose, gA, ← rat_mul, ← rat_mul, hgu]
    let γ : GA D W := ofMat W (rat g) hM
    have hγ : γ ∈ GQ W := (mem_GQ_iff W γ).2 (by rw [mt_ofMat]; exact ⟨g, rfl⟩)
    refine ⟨⟨γ, hγ⟩, Subtype.ext ?_⟩
    have : dl W ⟨γ, hγ⟩ = g := rat_injective (by rw [rat_dl]; exact mt_ofMat W _ hM)
    show dl W ⟨γ, hγ⟩ * x₀ = y
    rw [this, hgx]
  refine ⟨Equiv.ofBijective f ⟨hinj, hsurj⟩, fun γ => ?_⟩
  show rat (dl W γ * x₀) = _
  rw [rat_mul, rat_dl]

end PositivityTheory.Rg.Rsw.L.LThCoef

end
