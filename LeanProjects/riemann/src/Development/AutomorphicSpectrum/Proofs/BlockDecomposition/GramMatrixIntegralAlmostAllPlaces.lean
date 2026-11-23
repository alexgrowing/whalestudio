import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsUnitHermOfDet
import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.IsEulerProd
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.SubQRMemIntegers

open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.Published.SiegelOneVector GlobalTheory.CompanionTheory.SiegelND GlobalTheory.CompanionTheory.SiegelND.Coef
open scoped TensorProduct ENNReal

noncomputable section

namespace GlobalTheory.CompanionTheory.SiegelND.Coef

open Formalism.L2.SG.LocVol Formalism.L2.SG.Pf.NcS.KfOrbPf Formalism.L2.SG.Pf.NcS.IntWittPf

private theorem tensorBasis_repr_tmul {F E R : Type} [Field F] [Field E] [Algebra F E] [CommRing R] [Algebra F R]
    {d : ℕ} (b : Module.Basis (Fin d) F E) (c : R) (e : E) (m : Fin d) :
    (Algebra.TensorProduct.basis R b).repr (c ⊗ₜ[F] e) m = c * algebraMap F R (b.repr e m) := by
  rw [Algebra.TensorProduct.basis_repr_tmul]
  simp [Algebra.smul_def]

private theorem eq_sum_repr_tmul_basis {F E R : Type} [Field F] [Field E] [Algebra F E] [CommRing R] [Algebra F R]
    {d : ℕ} (b : Module.Basis (Fin d) F E) (z : R ⊗[F] E) :
    z = ∑ k, ((Algebra.TensorProduct.basis R b).repr z k) ⊗ₜ[F] b k := by
  conv_lhs => rw [← (Algebra.TensorProduct.basis R b).sum_repr z]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Algebra.TensorProduct.basis_apply, TensorProduct.smul_tmul', smul_eq_mul, mul_one]

private theorem tensorBasis_repr_sum_mem_of_repr_mem {F E R : Type} [Field F] [Field E] [Algebra F E] [CommRing R] [Algebra F R]
    {d : ℕ} (b : Module.Basis (Fin d) F E) (O : Subring R) {ι : Type} (s : Finset ι)
    (f : ι → R ⊗[F] E) (h : ∀ x ∈ s, ∀ m, (Algebra.TensorProduct.basis R b).repr (f x) m ∈ O) (m : Fin d) :
    (Algebra.TensorProduct.basis R b).repr (∑ x ∈ s, f x) m ∈ O := by
  rw [map_sum, Finsupp.finsetSum_apply]
  exact O.sum_mem fun x hx => h x hx m

private theorem tensorBasis_repr_tmul_mem_of_mem {F E R : Type} [Field F] [Field E] [Algebra F E] [CommRing R] [Algebra F R]
    {d : ℕ} (b : Module.Basis (Fin d) F E) (O : Subring R) (c : R) (e : E) (hc : c ∈ O)
    (he : ∀ m, algebraMap F R (b.repr e m) ∈ O) (m : Fin d) :
    (Algebra.TensorProduct.basis R b).repr (c ⊗ₜ[F] e) m ∈ O := by
  rw [tensorBasis_repr_tmul]
  exact O.mul_mem hc (he m)

private theorem tensorBasis_repr_mul_mem_of_repr_mem {F E R : Type} [Field F] [Field E] [Algebra F E] [CommRing R] [Algebra F R]
    {d : ℕ} (b : Module.Basis (Fin d) F E) (O : Subring R)
    (hb : ∀ k l m, algebraMap F R (b.repr (b k * b l) m) ∈ O) (z w : R ⊗[F] E)
    (hz : ∀ m, (Algebra.TensorProduct.basis R b).repr z m ∈ O)
    (hw : ∀ m, (Algebra.TensorProduct.basis R b).repr w m ∈ O) (m : Fin d) :
    (Algebra.TensorProduct.basis R b).repr (z * w) m ∈ O := by
  rw [eq_sum_repr_tmul_basis b z, eq_sum_repr_tmul_basis b w, Finset.sum_mul_sum]
  refine tensorBasis_repr_sum_mem_of_repr_mem b O _ _ (fun k _ m' => tensorBasis_repr_sum_mem_of_repr_mem b O _ _ (fun l _ m'' => ?_) m') m
  rw [Algebra.TensorProduct.tmul_mul_tmul]
  exact tensorBasis_repr_tmul_mem_of_mem b O _ _ (O.mul_mem (hz k) (hw l)) (hb k l) m''

private theorem tensorBasis_repr_sigR_mem_of_repr_mem {F E R : Type} [Field F] [Field E] [Algebra F E] [CommRing R] [Algebra F R]
    {d : ℕ} (b : Module.Basis (Fin d) F E) (O : Subring R) (σ : E →ₐ[F] E)
    (hs : ∀ k m, algebraMap F R (b.repr (σ (b k)) m) ∈ O) (z : R ⊗[F] E)
    (hz : ∀ m, (Algebra.TensorProduct.basis R b).repr z m ∈ O) (m : Fin d) :
    (Algebra.TensorProduct.basis R b).repr (sigR R σ z) m ∈ O := by
  rw [eq_sum_repr_tmul_basis b z, map_sum]
  refine tensorBasis_repr_sum_mem_of_repr_mem b O _ _ (fun k _ m' => ?_) m
  simp only [sigR, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, Algebra.TensorProduct.map_tmul, AlgHom.id_apply]
  exact tensorBasis_repr_tmul_mem_of_mem b O _ _ (hz k) (hs k) m'

theorem hermOf_sub_gramH_mem_latH : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (hCM : IsCMExt F E σ) (M : ℕ) (J : Matrix (Fin M) (Fin M) E) (hJ : IsHermND σ J) (n : ℕ),
    2 * n < M → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (T : Matrix (Fin n) (Fin n) E)
    (hT : ∀ a c, σ (T c a) = T a c),
    ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite,
      ∀ X ∈ (latV b v : Set (Fin n → Fin M → Fv F v ⊗[F] E)),
        hermOf (Fv F v) σ T hT - gramH hCM hJ (Fv F v) X ∈ latH σ b v n := by
  intro F E _ _ _ _ _ σ hCM M J hJ n hn d b T hT
  have intF : ∀ t : F, ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite,
      algebraMap F (Fv F v) t ∈ HeightOneSpectrum.adicCompletionIntegers F v := by
    intro t
    filter_upwards [GlobalTheory.CompanionTheory.Hypotheses₂.OneV.Coef.sub_qR_mem_integers F E σ hCM M J hJ d b t] with v hv
    have h0 := hv 0 (fun a i k => by simp)
    simpa [qR, hR, Formalism.UG.hform] using h0
  have hdiag := Filter.eventually_all.2 fun i : Fin n =>
    GlobalTheory.CompanionTheory.Hypotheses₂.OneV.Coef.sub_qR_mem_integers F E σ hCM M J hJ d b ((1 / 2) * Algebra.trace F E (T i i))
  have h1 : ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite, ∀ k l m,
      algebraMap F (Fv F v) (b.repr (b k * b l) m) ∈ HeightOneSpectrum.adicCompletionIntegers F v :=
    Filter.eventually_all.2 fun k => Filter.eventually_all.2 fun l => Filter.eventually_all.2 fun m => intF _
  have h2 : ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite, ∀ k m,
      algebraMap F (Fv F v) (b.repr (σ (b k)) m) ∈ HeightOneSpectrum.adicCompletionIntegers F v :=
    Filter.eventually_all.2 fun k => Filter.eventually_all.2 fun m => intF _
  have h3 : ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite, ∀ p q m,
      algebraMap F (Fv F v) (b.repr (J p q) m) ∈ HeightOneSpectrum.adicCompletionIntegers F v :=
    Filter.eventually_all.2 fun p => Filter.eventually_all.2 fun q => Filter.eventually_all.2 fun m => intF _
  have h4 : ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite, ∀ i j m,
      algebraMap F (Fv F v) (b.repr (T i j) m) ∈ HeightOneSpectrum.adicCompletionIntegers F v :=
    Filter.eventually_all.2 fun i => Filter.eventually_all.2 fun j => Filter.eventually_all.2 fun m => intF _
  filter_upwards [hdiag, h1, h2, h3, h4] with v hd hb hs hJv hTv
  intro X hX
  clear intF hdiag h1 h2 h3 h4
  haveI : FiniteDimensional F E := Module.Finite.of_basis b
  unfold latH gramH
  refine ⟨fun i => ?_, fun i j _ k => ?_⟩
  · have hX' := hd i (fun _ => X i) (fun _ a k => hX i a k)
    convert hX' using 1
    simp only [AddSubgroup.coe_sub, Matrix.sub_apply, hermOf, gramR, qR, Matrix.map_apply, map_sub, mul_sub]
    congr 1
    simp only [inclR, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, Algebra.TensorProduct.includeRight_apply]
    rw [GlobalTheory.CompanionTheory.Hypotheses₂.OneV.Coef.trace_one_tmul_len, map_mul]
  · let O : Subring (Fv F v) := (HeightOneSpectrum.adicCompletionIntegers F v).toSubring
    have gX : ∀ a p m, (Algebra.TensorProduct.basis (Fv F v) b).repr (X a p) m ∈ O := fun a p m => hX a p m
    have gI : ∀ e : E, (∀ m, algebraMap F (Fv F v) (b.repr e m) ∈ O) →
        ∀ m, (Algebra.TensorProduct.basis (Fv F v) b).repr (inclR (Fv F v) e) m ∈ O := by
      intro e he m
      simp only [inclR, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, Algebra.TensorProduct.includeRight_apply]
      rw [tensorBasis_repr_tmul, one_mul]
      exact he m
    have gH : ∀ m, (Algebra.TensorProduct.basis (Fv F v) b).repr (hR (Fv F v) σ J (X i) (X j)) m ∈ O := by
      intro m
      simp only [hR, Formalism.UG.hform, JR, Matrix.map_apply]
      exact tensorBasis_repr_sum_mem_of_repr_mem b O _ _ (fun p _ m' => tensorBasis_repr_sum_mem_of_repr_mem b O _ _ (fun q _ m'' =>
        tensorBasis_repr_mul_mem_of_repr_mem b O hb _ _ (fun m3 => tensorBasis_repr_mul_mem_of_repr_mem b O hb _ _ (tensorBasis_repr_sigR_mem_of_repr_mem b O σ hs _ (gX i p))
          (gI _ (hJv p q)) m3) (gX j q) m'') m') m
    have gT := gI (T i j) (hTv i j)
    simp only [AddSubgroup.coe_sub, Matrix.sub_apply, hermOf, gramR, Matrix.map_apply, map_sub,
      Finsupp.coe_sub, Pi.sub_apply]
    exact O.sub_mem (gT k) (gH k)

end GlobalTheory.CompanionTheory.SiegelND.Coef
