import Mathlib
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.CoefS
import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.IsEulerProd
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.NcSIntWittOEv

open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.Published.SiegelOneVector GlobalTheory.CompanionTheory.Hypotheses₂.OneV
open scoped TensorProduct ENNReal

noncomputable section

namespace GlobalTheory.CompanionTheory.Hypotheses₂.OneV.Coef

open Formalism.L2.SG.LocVol Formalism.L2.SG.Pf.NcS.KfOrbPf Formalism.L2.SG.Pf.NcS.IntWittPf

theorem trace_one_tmul_len {F E : Type} [Field F] [Field E] [Algebra F E] [FiniteDimensional F E]
    (R : Type) [CommRing R] [Algebra F R] (e : E) :
    Algebra.trace R (R ⊗[F] E) ((1 : R) ⊗ₜ[F] e) = algebraMap F R (Algebra.trace F E e) := by
  rw [Algebra.trace_apply, Algebra.trace_apply, ← Algebra.baseChange_lmul, LinearMap.trace_baseChange]

theorem sub_qR_mem_integers : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J →
    ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (t : F),
    ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite,
      ∀ X ∈ (latV b v : Set (Fin 1 → Fin M → Fv F v ⊗[F] E)),
        algebraMap F (Fv F v) t - qR (Fv F v) σ J (X 0) ∈ v.adicCompletionIntegers F := by
  intro F E _ _ _ _ _ σ _ M J _ d b t
  haveI : FiniteDimensional F E := Module.Finite.of_basis b
  have hb : ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite,
      ∀ k, inclR (F := F) (Fv F v) (b k) ∈ OEv (E := E) v :=
    Filter.eventually_all.2 fun k => ev_oev (b k)
  have hJ : ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite,
      ∀ i j, inclR (F := F) (Fv F v) (J i j) ∈ OEv (E := E) v :=
    Filter.eventually_all.2 fun i => Filter.eventually_all.2 fun j => ev_oev (J i j)
  have htr : ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite,
      ∀ k, algebraMap F (Fv F v) (Algebra.trace F E (b k)) ∈ v.adicCompletionIntegers F :=
    Filter.eventually_all.2 fun k => ev_int (Algebra.trace F E (b k))
  filter_upwards [ev_int (F := F) t, ev_int (F := F) (1 / 2), hb, hJ, htr, ev_crd_oev (E := E) b]
    with v ht hh hbv hJv htrv hc X hX
  have hrepr : ∀ z : Fv F v ⊗[F] E,
      z = ∑ k, (Algebra.TensorProduct.basis (Fv F v) b).repr z k • ((1 : Fv F v) ⊗ₜ[F] b k) := by
    intro z
    conv_lhs => rw [← (Algebra.TensorProduct.basis (Fv F v) b).sum_repr z]
    simp only [Algebra.TensorProduct.basis_apply]
  have hx : ∀ i, X 0 i ∈ oevRing (E := E) v := by
    intro i
    rw [hrepr (X 0 i)]
    refine Subring.sum_mem _ fun k _ => ?_
    exact oev_smul' v (hX 0 i k) (hbv k)
  have hh' : hR (Fv F v) σ J (X 0) (X 0) ∈ oevRing (E := E) v := by
    show ∑ i, ∑ j, sigR (Fv F v) σ (X 0 i) * JR (Fv F v) J i j * X 0 j ∈ oevRing (E := E) v
    refine sum_mem fun i _ => sum_mem fun j _ => ?_
    exact mul_mem (mul_mem (oev_sigR v σ (hx i)) (hJv i j)) (hx j)
  have htrace : Algebra.trace (Fv F v) (Fv F v ⊗[F] E) (hR (Fv F v) σ J (X 0) (X 0)) ∈
      v.adicCompletionIntegers F := by
    rw [hrepr (hR (Fv F v) σ J (X 0) (X 0)), map_sum]
    refine sum_mem fun k _ => ?_
    rw [map_smul, trace_one_tmul_len, smul_eq_mul]
    exact mul_mem (hc _ hh' k) (htrv k)
  exact sub_mem ht (mul_mem hh htrace)

end GlobalTheory.CompanionTheory.Hypotheses₂.OneV.Coef
