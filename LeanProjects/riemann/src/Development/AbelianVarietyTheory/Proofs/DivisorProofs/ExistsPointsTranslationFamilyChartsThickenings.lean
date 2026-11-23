import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsTaylorExpansionOrderOne
import Development.AbelianVarietyTheory.Definitions.Divisors.FstTszeSec
import Development.AbelianVarietyTheory.Definitions.Divisors.IsPeriodHom
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CloseTensorStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTensorLiftOfAnalyticThickeningStatement

open CategoryTheory TopologicalSpace TensorProduct
open GlobalTheory.AnPer

namespace GlobalTheory.AnPer

set_option maxHeartbeats 1000000 in

theorem exists_points_on_DObj : ∀ {I : Type} [Fintype I] {g : ℕ} {Λ : Type} [AddCommGroup Λ] {F : Fam I g Λ} {F₀ : Fam Empty g Λ} (K : Charts F) (K₀ : Charts F₀) {R : Type} [CommRing R] [Algebra ℂ R] (et : Hol F₀.V →ₐ[ℂ] R) (M : Ideal R) (θ : Hol F.V →+* R) (ka : K₀.K → K.K) (hka : ∀ {l k' k}, K₀.le l k' k → K.le l (ka k') (ka k)) (ρ : ∀ k, Hol (K.W (ka k)) →+* R ⊗[ℂ] Hol (K₀.W k)), (∀ k f, ρ k (K.cst (ka k) f) = θ f ⊗ₜ[ℂ] 1) → (∀ k a h, ρ k (dw a h) = LinearMap.lTensor R (dw a).toLinearMap (ρ k h)) → (∀ l k' k (h : K₀.le l k' k), Close (M.map (Algebra.TensorProduct.includeLeft : R →ₐ[ℂ] R ⊗[ℂ] Hol (K₀.W k'))) ((ρ k').comp (Charts.sh (hka h))) ((Algebra.TensorProduct.map (AlgHom.id ℂ R) (Charts.shA h)).toRingHom.comp (ρ k))) → ∀ (res : ∀ k, Hol (K.W (ka k)) →+* Hol (K₀.W k)), (∀ k h, ρ k h - 1 ⊗ₜ[ℂ] res k h ∈ M.map (Algebra.TensorProduct.includeLeft : R →ₐ[ℂ] R ⊗[ℂ] Hol (K₀.W k))) → ∃ ρ' : ∀ S : K₀.DObj (et : Hol F₀.V →+* R) M, Hol (K.W (ka S.T.k)) →+* S.T.C, (∀ S f, ρ' S (K.cst _ f) = algebraMap R S.T.C (θ f)) ∧ (∀ S h, ρ' S h - S.T.ρ (res _ h) ∈ S.T.J) ∧ ∀ (S S' : K₀.DObj (et : Hol F₀.V →+* R) M) (f : S ⟶ S'), Close S'.T.J ((ρ' S').comp (Charts.sh (hka (Charts.Hom.le f.1)))) ((f.1.φ : S.T.C →+* S'.T.C).comp (ρ' S)) := by
  intro I _ g Λ _ F F₀ K K₀ R _ _ et M θ ka hka ρ hc hd hs res hr
  choose ψ hψ using GlobalTheory.T.exists_tensorLift_of_analyticThickening K₀ et M
  have h1 : ∀ (S : K₀.DObj (et : Hol F₀.V →+* R) M) (d : R), ψ S (d ⊗ₜ[ℂ] 1) = algebraMap R S.T.C d :=
    fun S d ↦ (hψ S d 1).trans (by rw [S.T.ρ.map_one, mul_one])
  have h2 : ∀ (S : K₀.DObj (et : Hol F₀.V →+* R) M) (h : Hol (K₀.W S.T.k)), ψ S (1 ⊗ₜ[ℂ] h) = S.T.ρ h :=
    fun S h ↦ (hψ S 1 h).trans (by rw [(algebraMap R S.T.C).map_one, one_mul])
  have hJ : ∀ (S : K₀.DObj (et : Hol F₀.V →+* R) M),
      ∀ c ∈ M.map (Algebra.TensorProduct.includeLeft : R →ₐ[ℂ] R ⊗[ℂ] Hol (K₀.W S.T.k)), ψ S c ∈ S.T.J := by
    intro S c hc
    have : M.map (Algebra.TensorProduct.includeLeft : R →ₐ[ℂ] R ⊗[ℂ] Hol (K₀.W S.T.k)) ≤ S.T.J.comap (ψ S) := by
      refine Ideal.map_le_iff_le_comap.2 fun d hd ↦ ?_
      change ψ S (d ⊗ₜ[ℂ] 1) ∈ S.T.J
      rw [h1]
      exact S.mem d hd
    exact this hc
  refine ⟨fun S ↦ (ψ S).comp (ρ S.T.k), fun S f ↦ ?_, fun S h ↦ ?_, fun S S' f ↦ ?_⟩
  · exact (congrArg (ψ S) (hc _ f)).trans (h1 S _)
  · have := hJ S _ (hr S.T.k h)
    rw [(ψ S).map_sub, h2] at this
    exact this
  · have c1 := (hs _ _ _ (Charts.Hom.le f.1)).map (ψ S') (hJ S')
    have c2 := GlobalTheory.T.close_comp_of_close_includeRight S'.T.J (ρ S.T.k) (hd S.T.k)
      ((ψ S').comp (Algebra.TensorProduct.map (AlgHom.id ℂ R) (Charts.shA (Charts.Hom.le f.1))).toRingHom)
      ((f.1.φ : S.T.C →+* S'.T.C).comp (ψ S))
      (fun d ↦ by
        have e : Algebra.TensorProduct.map (AlgHom.id ℂ R) (Charts.shA (Charts.Hom.le f.1)) (d ⊗ₜ[ℂ] 1) = d ⊗ₜ[ℂ] 1 :=
          (Algebra.TensorProduct.map_tmul _ _ _ _).trans
            (congrArg (fun x ↦ d ⊗ₜ[ℂ] x) (Charts.shA (Charts.Hom.le f.1)).map_one)
        exact (congrArg (ψ S') e).trans ((h1 S' d).trans ((f.2 d).symm.trans (congrArg f.1.φ (h1 S d).symm))))
      (by
        have e1 : ((ψ S').comp (Algebra.TensorProduct.map (AlgHom.id ℂ R)
            (Charts.shA (Charts.Hom.le f.1))).toRingHom).comp
            (Algebra.TensorProduct.includeRight : Hol (K₀.W S.T.k) →ₐ[ℂ] R ⊗[ℂ] Hol (K₀.W S.T.k)).toRingHom =
            S'.T.ρ.comp (Charts.sh (Charts.Hom.le f.1)) :=
          RingHom.ext fun h ↦ (congrArg (ψ S') (Algebra.TensorProduct.map_tmul (AlgHom.id ℂ R)
            (Charts.shA (Charts.Hom.le f.1)) 1 h)).trans (h2 S' _)
        have e2 : ((f.1.φ : S.T.C →+* S'.T.C).comp (ψ S)).comp
            (Algebra.TensorProduct.includeRight : Hol (K₀.W S.T.k) →ₐ[ℂ] R ⊗[ℂ] Hol (K₀.W S.T.k)).toRingHom =
            (f.1.φ : S.T.C →+* S'.T.C).comp S.T.ρ :=
          RingHom.ext fun h ↦ congrArg f.1.φ (h2 S h)
        rw [e1, e2]
        exact f.1.close)
    exact Relation.ReflTransGen.trans c1 c2

end GlobalTheory.AnPer
