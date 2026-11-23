import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.SplitStab
import Development.WeilBound.ThetaLifts.Reductions.WeilPairs.AutEtaB
import Development.WeilBound.ThetaLifts.Reductions.WeilPairs.LatRepBI
import GroundTheory.HeightsAndTheta.Heights.LatticeLemmas.PLocalLatticeIndex

open scoped TensorProduct Matrix Topology Kronecker ComplexOrder Classical
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Matrix
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF MeasureTheory GlobalTheory.FinWeil GlobalTheory.FinLatF GlobalTheory.RealWeilF GlobalTheory.WeilPartsF
open PositivityTheory.ThKW PositivityTheory.ThKW.AutEtaA
open UpperTheory.TP.W

theorem UpperTheory.eq_zero_of_splitIdempotent_eval_place_eq_zero :
    ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E),
        IsCMExt F E σ → ∀ e, IsSplitIdemF σ e → ∀ P : HeightOneSpectrum (𝓞 E), (∀ Q, Q ≠ P → ev F E Q e = 0) →
        ∀ a : AEF F E, e * a = a → ev F E P a = 0 → a = 0 := by
  intro F E _ _ _ _ _ σ hσ e he P hP a hea haP
  obtain ⟨hee, hec, v, ε, hε, hsum⟩ := he
  obtain ⟨α, rfl, -, -⟩ := hε
  have h1 : e * algebraMap (AF F) (AEF F E) (pairA F 0 α) = e := by
    rw [← hsum, mul_add, hee, hec, add_zero]
  have h2 : a = algebraMap (AF F) (AEF F E) (pairA F 0 α) * a := by
    calc a = e * a := hea.symm
      _ = (e * algebraMap (AF F) (AEF F E) (pairA F 0 α)) * a := by rw [h1]
      _ = _ := by rw [mul_comm e, mul_assoc, hea]
  have h3 : ∀ Q, ev F E Q a = 0 := by
    intro Q
    by_cases hQ : Q = P
    · subst hQ
      exact haP
    · rw [← hea, map_mul, hP Q hQ, zero_mul]
  have h4 : finPartF F E a = 0 := by
    apply (finAdEquiv F E).injective
    rw [map_zero]
    apply RestrictedProduct.ext
    intro Q
    exact h3 Q
  let g : Af F →ₗ[F] AF F := (LinearMap.inr F (Ainf F) (Af F) : Af F →ₗ[F] AF F) ∘ₗ LinearMap.mulLeft F α
  have h5 : ∀ b : AEF F E, algebraMap (AF F) (AEF F E) (pairA F 0 α) * b =
      TensorProduct.map g LinearMap.id (finPartF F E b) := by
    intro b
    induction b using TensorProduct.induction_on with
    | zero => simp
    | tmul x y =>
      rw [Algebra.TensorProduct.algebraMap_apply, Algebra.TensorProduct.tmul_mul_tmul, one_mul]
      show _ = TensorProduct.map g LinearMap.id ((sndA F x) ⊗ₜ[F] y)
      rw [TensorProduct.map_tmul]
      congr 1
      exact Prod.ext (zero_mul x.1) rfl
    | add x y hx hy => rw [mul_add, hx, hy, map_add, map_add]
  rw [h2, h5, h4, map_zero]
