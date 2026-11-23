import Mathlib
import Development.AbelianVarietyTheory.Definitions.CMLattices.LamLetters
import Development.AbelianVarietyTheory.Definitions.CMLattices.ExistsIsThetaDegOfIsLocalModel
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.LinearIndependentOfIsLieBasis
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.LieCombBaseChange

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.LamCM
open scoped CategoryTheory.Obj ComplexOrder
open GlobalTheory GlobalTheory.CM GlobalTheory.LamF

noncomputable section
namespace GlobalTheory.CM.LieMetric

theorem form_eq_sum_sum {K : Type} [Field K] {g : ℕ} (h : HermFam K (Fin g → K)) (s : K →+* ℂ) (x y : Fin g → K) :
    h.form s x y = ∑ j, ∑ i, s (y j) * star (s (x i)) * h.form s (Pi.single i 1) (Pi.single j 1) := by
  rw [form_sum_right]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← h.conj_symm, form_sum_right, map_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_mul, h.conj_symm, _root_.mul_assoc]
  rfl

theorem hermForm_sum_sum {g n : ℕ} (Hm : Matrix (Fin g) (Fin g) ℂ) (a b : Fin n → ℂ) (X : Fin n → Fin g → ℂ) :
    hermForm Hm (∑ j, a j • X j) (∑ i, b i • X i) = ∑ j, ∑ i, a j * star (b i) * hermForm Hm (X j) (X i) := by
  simp only [hermForm, star_sum, star_smul, Matrix.mulVec_sum, Matrix.mulVec_smul, sum_dotProduct, dotProduct_sum,
    smul_dotProduct, dotProduct_smul, smul_eq_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_
  ring

theorem form_eq_pi_mul_hermForm : ThetaUnifAV → Out.Laws → ∀ (K : Type) [Field K] [NumberField K] (P : Out.PolAV (Sp (𝓞 K))) (F : GenFib P) (h : HermFam K (Fin F.P₀.g → K)), F.IsHerm h → ∀ (s : K →+* ℂ) (Q : Out.PolAV (Sp ℂ)) (ψ : Q.A.left ⟶ F.P₀.A.left) (u : HolUnif Q.A Q.L Q.g) (Hm : Matrix (Fin Q.g) (Fin Q.g) ℂ) (χ : u.Λ → ℂ), IsPolFibre s F.P₀ Q ψ → u.IsAH Hm χ → ∀ (c c' : Fin F.P₀.g → K) (w w' : epsR K ⟶ F.P₀.A) (v v' : epsR ℂ ⟶ Q.A) (W W' : Fin Q.g → ℂ), IsLieComb c F.v w → IsLieComb c' F.v w' → IsVecOver s ψ w v → IsVecOver s ψ w' v' → u.IsDiff W v → u.IsDiff W' v' → h.form s c c' = Real.pi * hermForm Hm W' W := by
  intro hU _ K _ _ P F h H s Q ψ u Hm χ hQ hA c c' w w' v v' W W' hw hw' hv hv' hW hW'
  obtain ⟨Q₀, ψ₀, v₀, u₀, Hm₀, χ₀, W₀, a₀, b₀, c₀, d₀⟩ := H s
  obtain ⟨-, -, -, -, t1, -, -⟩ := AHWeil.tangent_and_weil_of_isAH hU Q _ u Hm χ hA
  choose x hx using fun i => (existsUnique_isVecOver hQ.2.1.1 (F.v i)).exists
  have hxt : ∀ i, IsTangent (x i) := fun i => (hx i).isTangent hQ.2.1 (F.basis.1 i)
  choose X hX using fun i => (t1 _ (hxt i)).exists
  have key : ∀ (c : Fin F.P₀.g → K) (w : epsR K ⟶ F.P₀.A) (v : epsR ℂ ⟶ Q.A) (W : Fin Q.g → ℂ), IsLieComb c F.v w →
      IsVecOver s ψ w v → u.IsDiff W v → W = ∑ i, s (c i) • X i := fun c w v W hw hv hW => by
    have h1 := (lieComb_baseChange K ℂ s _ _ ψ hQ.2.1 _ F.v w c x v hx hw).1 hv
    have h2 := UnifDifferential.isDiff_prod u (fun i => s (c i) • X i) _
      (fun i => Chart.isTan_scale (s (c i)) ((Chart.isTan_iff _).2 (hxt i)))
      (fun i => UnifDifferential.isDiff_scale u (hX i) (s (c i)))
    have h3 : IsTangent v := by
      rw [(Chart.isLieComb_iff _ x v).1 h1]
      exact (Chart.isTan_iff _).1 h2.1
    exact (t1 v h3).unique hW (UnifDifferential.isDiff_of_isLieComb _ _ _ _ u X x _ v hxt hX h1)
  rw [key c w v W hw hv hW, key c' w' v' W' hw' hv' hW', hermForm_sum_sum, form_eq_sum_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [d₀, hermForm_eq hU a₀ hQ b₀ hA F.basis.1 c₀ (fun i => ⟨hx i, hX i⟩)]
  ring

end GlobalTheory.CM.LieMetric
end
