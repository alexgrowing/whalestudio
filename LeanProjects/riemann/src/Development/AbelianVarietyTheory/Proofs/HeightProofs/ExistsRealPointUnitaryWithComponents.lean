import Mathlib
import Development.AbelianVarietyTheory.Proofs.HeightProofs.IsTopologicalRingAE
import Development.AbelianVarietyTheory.Counterexamples.HeightSurvey.StarPurelyImaginaryEqNeg

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Matrix GlobalTheory.FockCompare GlobalTheory.IndefiniteRowSideFullHecke.FockOrthogonalDecomposition
open scoped TensorProduct ContDiff ComplexOrder

namespace GlobalTheory.FockCompare.LiftUnitary

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Abstract

variable {A B T : Type} [CommRing A] [CommRing B] {n : Type} [Fintype n] [DecidableEq n]

theorem lift_abstract (φ : A →+* B) (p : T → A →+* ℂ) (s : (T → ℂ) → A) (c : A →+* A) (cB : B →+* B)
    (hfin : ∀ z, φ (s z) = 0) (hcomp : ∀ z τ, p τ (s z) = z τ)
    (hext : ∀ a, φ a = 0 → (∀ τ, p τ a = 0) → a = 0)
    (hc : ∀ a, φ (c a) = cB (φ a)) (hp : ∀ τ a, p τ (c a) = starRingEnd ℂ (p τ a))
    (J : Matrix n n A) (hJ : ∀ τ, (J.map (p τ)).det ≠ 0) (g : T → Matrix n n ℂ)
    (hg : ∀ τ, (g τ)ᴴ * J.map (p τ) * g τ = J.map (p τ)) :
    ∃ k : GL n A, k ∈ Formalism.UG.UJ c J ∧ Formalism.UG.bc φ k = 1 ∧ ∀ τ, (k : Matrix n n A).map (p τ) = g τ := by
  let m : (T → Matrix n n ℂ) → Matrix n n A := fun g => 1 + Matrix.of fun i j => s fun τ => (g τ - 1) i j
  have m1 : ∀ g, (m g).map φ = 1 := by
    intro g; ext i j
    simp only [m, Matrix.map_apply, Matrix.add_apply, Matrix.of_apply, map_add, hfin, add_zero, Matrix.one_apply]
    split_ifs <;> simp
  have m2 : ∀ g τ, (m g).map (p τ) = g τ := by
    intro g τ; ext i j
    simp only [m, Matrix.map_apply, Matrix.add_apply, Matrix.of_apply, map_add, hcomp, Matrix.sub_apply,
      Matrix.one_apply]
    split_ifs <;> simp
  have mext : ∀ x y : Matrix n n A, x.map φ = y.map φ → (∀ τ, x.map (p τ) = y.map (p τ)) → x = y := by
    intro x y h1 h2
    ext i j
    rw [← sub_eq_zero]
    refine hext _ ?_ fun τ => ?_
    · rw [map_sub, sub_eq_zero]; exact congrFun (congrFun h1 i) j
    · rw [map_sub, sub_eq_zero]; exact congrFun (congrFun (h2 τ) i) j
  have hdet : ∀ τ, IsUnit (g τ).det := by
    intro τ
    rw [isUnit_iff_ne_zero]
    intro h0
    have := congrArg Matrix.det (hg τ)
    rw [Matrix.det_mul, h0, mul_zero] at this
    exact hJ τ this.symm
  have o1 : (1 : Matrix n n A).map φ = 1 := Matrix.map_one _ (map_zero φ) (map_one φ)
  have o2 : ∀ τ, (1 : Matrix n n A).map (p τ) = 1 := fun τ => Matrix.map_one _ (map_zero _) (map_one _)
  refine ⟨⟨m g, m fun τ => (g τ)⁻¹, ?_, ?_⟩, ?_, ?_, m2 g⟩
  · refine mext _ _ ?_ fun τ => ?_
    · rw [Matrix.map_mul, m1, m1, o1, Matrix.one_mul]
    · rw [Matrix.map_mul, m2, m2, o2, Matrix.mul_nonsing_inv _ (hdet τ)]
  · refine mext _ _ ?_ fun τ => ?_
    · rw [Matrix.map_mul, m1, m1, o1, Matrix.one_mul]
    · rw [Matrix.map_mul, m2, m2, o2, Matrix.nonsing_inv_mul _ (hdet τ)]
  · show Formalism.UG.cT c (m g) * J * m g = J
    refine mext _ _ ?_ fun τ => ?_
    · have e : (Formalism.UG.cT c (m g)).map φ = Formalism.UG.cT cB ((m g).map φ) := by
        ext i j; exact hc _
      rw [Matrix.map_mul, Matrix.map_mul, e, m1, Formalism.UG.cT_one, Matrix.one_mul, Matrix.mul_one]
    · have e : (Formalism.UG.cT c (m g)).map (p τ) = ((m g).map (p τ))ᴴ := by
        ext i j; exact hp τ _
      rw [Matrix.map_mul, Matrix.map_mul, e, m2, hg]
  · apply Units.ext
    exact m1 g

end Abstract

theorem snd_sigR {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] (σ : E →ₐ[F] E) (z : AF F ⊗[F] E) :
    (Algebra.TensorProduct.map (sndA F) (AlgHom.id F E)).toRingHom (sigR (AF F) σ z) =
      sigR (Af F) σ ((Algebra.TensorProduct.map (sndA F) (AlgHom.id F E)).toRingHom z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp only [RingHom.map_zero]
  | add a b ha hb => simp only [RingHom.map_add, ha, hb]
  | tmul a x => rfl

theorem lift_unitary (D : D7) (θ : InfFam D) (σ : (D.what₂.Tau → ℂ) →+ AE D) (h : Chart θ σ) (V : HSp D)
    (g : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ) (hg : ∀ τ, g τ ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ)) :
    ∃ k ∈ GinfC V, ∀ τ, infMat D.sp.cm.sig V.gram (θ τ) k = g τ := by
  have hJ : ∀ τ, (V.gram.map (incA D)).map ((θ τ).comp (infPart D)) = gramAt D V τ := by
    intro τ; ext i j; exact comp_incA h.inf τ _
  obtain ⟨k, hk, hf, hi⟩ := lift_abstract (finPart D) (fun τ => (θ τ).comp (infPart D)) σ (cA D)
    (sigR (Af D.host.F) D.sp.cm.sig) h.fin h.comp h.ext (snd_sigR D.sp.cm.sig) (comp_cA h.inf)
    (V.gram.map (incA D))
    (fun τ => by
      rw [hJ]
      have e : (gramAt D V τ).det = tauE D τ V.gram.det := (RingHom.map_det (tauE D τ) V.gram).symm
      rw [e]
      exact (map_ne_zero _).2 (Formalism.L2.Theta.gram_det_ne V))
    g (fun τ => by rw [hJ]; exact hg τ)
  exact ⟨⟨k, hk⟩, hf, hi⟩

end GlobalTheory.FockCompare.LiftUnitary

end
