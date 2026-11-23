import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LnStepFalse
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SumLogEmbeddingAddFinsumLogAdicAbvEqZero
open AlgebraicGeometry CategoryTheory NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj
open GlobalTheory.TrueGeo GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.Toroidal GlobalTheory.LocM.Frm GlobalTheory.HeightParts
open GlobalTheory.GradedNorm GlobalTheory.LieHt
open Formalism.MainNotions.DIV.Cons (intO)
open GlobalTheory.LieSmooth

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.LieSmooth

theorem sum_log_norm_embeddings_eq_log_norm {L : Type} [Field L] [NumberField L] (x : L) (hx : x ≠ 0) :
    ∑ σ : L →+* ℂ, Real.log ‖σ x‖ = Real.log ‖algebraMap ℚ ℂ (Algebra.norm ℚ x)‖ := by
  rw [Algebra.norm_eq_prod_embeddings ℚ ℂ x, norm_prod, Real.log_prod (fun τ _ => norm_ne_zero_iff.2
    ((map_ne_zero_iff _ τ.injective).2 hx))]
  exact Fintype.sum_equiv (RingHom.equivRatAlgHom L ℂ) _ _ fun _ => rfl

theorem finsum_sum_log_embOver_eq : ∀ {F : Type} [Field F] [NumberField F] {K : Type} [Field K] [NumberField K] (φ : F →+* K) (a : K), a ≠ 0 → (Function.support fun v : HeightOneSpectrum (𝓞 F) => ∑ θ : EmbOver φ, Real.log ((extOf v).w (θ.1 a))).Finite ∧ ∑ᶠ v : HeightOneSpectrum (𝓞 F), ∑ θ : EmbOver φ, Real.log ((extOf v).w (θ.1 a)) = -∑ σ : K →+* ℂ, Real.log ‖σ a‖ := by
  intro F _ _ K _ _ φ a ha
  letI : Algebra F K := φ.toAlgebra
  haveI : IsScalarTower ℚ F K := IsScalarTower.of_algebraMap_eq fun x => (map_ratCast φ x).symm
  haveI : FiniteDimensional F K := Module.Finite.of_restrictScalars_finite ℚ F K
  let e : EmbOver φ ≃ (K →ₐ[F] AlgebraicClosure F) :=
    { toFun := fun θ => { θ.1 with commutes' := fun r => RingHom.congr_fun θ.2 r }
      invFun := fun f => ⟨f.toRingHom, RingHom.ext fun r => f.commutes r⟩
      left_inv := fun θ => rfl
      right_inv := fun f => AlgHom.ext fun _ => rfl }
  set N : F := Algebra.norm F a with hNdef
  have hN : N ≠ 0 := Algebra.norm_ne_zero_iff.2 ha
  have hprod : ∏ θ : EmbOver φ, θ.1 a = algebraMap F (AlgebraicClosure F) N := by
    rw [hNdef, Algebra.norm_eq_prod_embeddings F (AlgebraicClosure F) a]
    exact Fintype.prod_equiv e _ _ fun _ => rfl
  have hv : ∀ v : HeightOneSpectrum (𝓞 F), ∑ θ : EmbOver φ, Real.log ((extOf v).w (θ.1 a)) =
      Real.log (NumberField.HeightOneSpectrum.adicAbv F v N) := by
    intro v
    rw [← Real.log_prod (fun θ _ => ((extOf v).w.pos ((map_ne_zero_iff _ θ.1.injective).2 ha)).ne'), ← map_prod,
      hprod, (extOf v).w_alg]
  have hfun : (fun v : HeightOneSpectrum (𝓞 F) => ∑ θ : EmbOver φ, Real.log ((extOf v).w (θ.1 a))) =
      fun v => Real.log (NumberField.HeightOneSpectrum.adicAbv F v N) := funext hv
  obtain ⟨h₁, h₂⟩ := GlobalTheory.sum_log_embedding_add_finsum_log_adicAbv_eq_zero F N hN
  refine ⟨hfun ▸ h₁, ?_⟩
  rw [hfun, eq_neg_iff_add_eq_zero, add_comm, ← h₂, sum_log_norm_embeddings_eq_log_norm a ha,
    sum_log_norm_embeddings_eq_log_norm N hN, hNdef, Algebra.norm_norm]

end GlobalTheory.LieSmooth

end
