import Development.WeilBound.ThetaLifts.LatticeBasics.BadFactor
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.SplitStab
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.IsLatRepL
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.ThetaBasicK

set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
namespace GlobalTheory.ThK.Dbl.Bad
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.Doubling (absE)
open PositivityTheory.ThKG.Loc (idem)
open PositivityTheory.ThKG.Loc.Cone
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n d : ℕ}
variable {X : Spc F E n} {W : Spc F E d} {B : Base F E} {M : Model σ X W} {χX χW : Chr F E} {om : Rep σ X W} {r s r' s' : ℕ}
theorem orth_k (P : _root_.GlobalTheory.ThK.IsPair_k B M χX χW om r s r' s') {ν} (hν : @Measure.IsAddHaarMeasure _ _ _ (borel _) ν) {Φ} (h : Φ ∈ schA F _)
    (h0 : Φ ≠ 0) {g u} {c c' : ℂ} (hc : c ≠ c') (h1 : M.co.rho B.ψ u Φ = c • Φ) (h2 : M.co.rho B.ψ (mat g * u) Φ = c' • Φ) :
    coef om ν Φ g = 0 := by
  by_contra hn
  have i := P.weil.isUSplitting.impl (g, 1) u Φ h
  rw [h1, map_smul, show actAB (cA σ) (g, 1) u = mat g * u from (congrArg _ Matrix.transpose_one).trans (Matrix.mul_one _)] at i
  have a1 := schr_unit P.base.std ν hν (M.co.e (mat g * u)) (om (g, 1) Φ) Φ
  have a2 := schr_unit P.base.std ν hν (M.co.e (mat g * u)) Φ Φ
  have k : ∀ (A : Fn F n d) (t : ℂ), ∫ x, (t • A) x * star ((c' • Φ) x) ∂ν = t * star c' * ∫ x, A x * star (Φ x) ∂ν := fun A t => by
    rw [← integral_const_mul]
    exact integral_congr_ae (.of_forall fun x => by simp only [Pi.smul_apply, smul_eq_mul, star_mul']; ring)
  rw [show schr B.ψ (M.co.e (mat g * u)) Φ = _ from h2] at a1 a2
  rw [show schr B.ψ (M.co.e (mat g * u)) (om (g, 1) Φ) = _ from i.symm, k] at a1
  rw [k] at a2
  have b1 := (mul_eq_right₀ hn).1 a1
  have b2 := (mul_eq_right₀ (sq_ne ν hν h h0)).1 a2
  exact hc (mul_right_cancel₀ (right_ne_zero_of_mul_eq_one b1) (b1.trans b2.symm))
theorem law_k {dd om₂ S l} (hB : _root_.UpperTheory.TP.W.GoodK σ B) (h : IsDbl (σ := σ) (A := W) (Y := X) (κ := (Fin n × Fin d) ⊕ (Fin n × Fin d)) B.ψ dd χW om₂ S l)
    {Ψ} (hΨ : Ψ ∈ schA F _) : Law χW (d / 2) fun x => l (om₂ x Ψ) := fun p t x hp => by
  have := hB.cm.1
  beta_reduce
  rw [map_mul, Module.End.mul_apply, h.weil.2.2 l h.adm h.kill p t hp _ (h.weil.2.1.pres x Ψ hΨ), PositivityTheory.ThKF0.Chr.absE_eq,
    Complex.ofReal_cpow (NNReal.coe_nonneg _), Fintype.card_fin]
  push_cast
  rfl
end GlobalTheory.ThK.Dbl.Bad
end
end
