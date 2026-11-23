import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.WhittakerGlobalFactors.MeasurableSetUH
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicTraceSupportedAtSplitPlace

noncomputable section

namespace PositivityTheory.SiegelWeilFormula.GFac

open HeckeCharacterZeroLocus.SiegelWeilU NumberField IsDedekindDomain MeasureTheory GlobalTheory.Cont PositivityTheory.PfSWUS.Loc PositivityTheory.Rg.Sw Filter
open PositivityTheory.SiegelWeilFormula.Gen
open GlobalTheory.CompanionTheory.SiegelND.Coef (hermInf hermFin hermV latH intH)
open scoped TensorProduct Matrix

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

def intE {d : ℕ} (bs : Module.Basis (Fin d) F E) (v : HeightOneSpectrum (𝓞 F)) : Set (Fv F v ⊗[F] E) :=
  {e | ∀ k, (Algebra.TensorProduct.basis (Fv F v) bs).repr e k ∈ v.adicCompletionIntegers F}

structure Good (σ : E →ₐ[F] E) {d M n : ℕ} (bs : Module.Basis (Fin d) F E) (J : Matrix (Fin M) (Fin M) E)
    (T : Matrix (Fin n) (Fin n) E) (v : HeightOneSpectrum (𝓞 F)) : Prop where
  one : (1 : Fv F v ⊗[F] E) ∈ intE bs v
  mul : ∀ e e', e ∈ intE bs v → e' ∈ intE bs v → e * e' ∈ intE bs v
  sig : ∀ e, e ∈ intE bs v → sigR (Fv F v) σ e ∈ intE bs v
  tr : ∀ e, e ∈ intE bs v → Algebra.trace (Fv F v) (Fv F v ⊗[F] E) e ∈ v.adicCompletionIntegers F
  half : algebraMap F (Fv F v) (1 / 2) ∈ v.adicCompletionIntegers F
  hJ : ∀ i j, inclR (Fv F v) (J i j) ∈ intE bs v
  hT : ∀ i j, inclR (Fv F v) (T i j) ∈ intE bs v

theorem add_mem_intE {d : ℕ} (bs : Module.Basis (Fin d) F E) (v : HeightOneSpectrum (𝓞 F)) {e e' : Fv F v ⊗[F] E}
    (he : e ∈ intE bs v) (he' : e' ∈ intE bs v) : e + e' ∈ intE bs v := by
  intro k
  simp only [map_add, Finsupp.add_apply]
  exact add_mem (he k) (he' k)

theorem zero_mem_intE {d : ℕ} (bs : Module.Basis (Fin d) F E) (v : HeightOneSpectrum (𝓞 F)) :
    (0 : Fv F v ⊗[F] E) ∈ intE bs v := by
  intro k
  simp only [map_zero, Finsupp.zero_apply]
  exact zero_mem _

theorem sum_mem_intE {d : ℕ} (bs : Module.Basis (Fin d) F E) (v : HeightOneSpectrum (𝓞 F)) {ι : Type} (s : Finset ι)
    (f : ι → Fv F v ⊗[F] E) (hf : ∀ i ∈ s, f i ∈ intE bs v) : ∑ i ∈ s, f i ∈ intE bs v := by
  classical
  exact Finset.sum_induction f (· ∈ intE bs v) (fun _ _ ha hb => add_mem_intE bs v ha hb) (zero_mem_intE bs v) hf

theorem algebraMap_mem_intE {d : ℕ} (bs : Module.Basis (Fin d) F E) (v : HeightOneSpectrum (𝓞 F))
    (h1 : (1 : Fv F v ⊗[F] E) ∈ intE bs v) {r : Fv F v} (hr : r ∈ v.adicCompletionIntegers F) :
    algebraMap (Fv F v) (Fv F v ⊗[F] E) r ∈ intE bs v := by
  intro k
  rw [Algebra.algebraMap_eq_smul_one, map_smul, Finsupp.smul_apply, smul_eq_mul]
  exact mul_mem hr (h1 k)

theorem repr_tmul_apply {d : ℕ} (bs : Module.Basis (Fin d) F E) (R : Type) [CommRing R] [Algebra F R] (c : R) (x : E)
    (k : Fin d) : (Algebra.TensorProduct.basis R bs).repr (c ⊗ₜ[F] x) k = c * algebraMap F R (bs.repr x k) := by
  simp [Algebra.TensorProduct.basis_repr_tmul, Algebra.smul_def, mul_comm]

theorem eq_sum_tmul {d : ℕ} (bs : Module.Basis (Fin d) F E) (R : Type) [CommRing R] [Algebra F R] (e : R ⊗[F] E) :
    e = ∑ k, (Algebra.TensorProduct.basis R bs).repr e k ⊗ₜ[F] bs k := by
  conv_lhs => rw [← (Algebra.TensorProduct.basis R bs).sum_repr e]
  simp [Algebra.TensorProduct.basis_apply, TensorProduct.smul_tmul']

def OkE {d : ℕ} (bs : Module.Basis (Fin d) F E) (v : HeightOneSpectrum (𝓞 F)) (x : E) : Prop :=
  ∀ m, algebraMap F (Fv F v) (bs.repr x m) ∈ v.adicCompletionIntegers F

theorem ev_okE {d : ℕ} (bs : Module.Basis (Fin d) F E) (x : E) : ∀ᶠ v in cofinite, OkE bs v x :=
  Filter.eventually_all.2 fun m => GlobalTheory.CompanionTheory.SiegelND.Coef.Lim.ev_rat _

theorem tmul_mem_intE {d : ℕ} (bs : Module.Basis (Fin d) F E) (v : HeightOneSpectrum (𝓞 F)) {c : Fv F v} {x : E}
    (hc : c ∈ v.adicCompletionIntegers F) (hx : OkE bs v x) : c ⊗ₜ[F] x ∈ intE bs v := fun m => by
  rw [repr_tmul_apply]
  exact mul_mem hc (hx m)

theorem eventually_good (σ : E →ₐ[F] E) (hCM : IsCMExt F E σ) {d M n : ℕ} (bs : Module.Basis (Fin d) F E)
    (J : Matrix (Fin M) (Fin M) E) (T : Matrix (Fin n) (Fin n) E) :
    ∀ᶠ v in cofinite, Good σ bs J T v := by
  haveI : FiniteDimensional F E := Module.Finite.of_basis bs
  have h2 : ∀ᶠ v in cofinite, ∀ k l, OkE bs v (bs k * bs l) :=
    Filter.eventually_all.2 fun k => Filter.eventually_all.2 fun l => ev_okE bs _
  have h3 : ∀ᶠ v in cofinite, ∀ k, OkE bs v (σ (bs k)) := Filter.eventually_all.2 fun k => ev_okE bs _
  have h4 : ∀ᶠ v in cofinite, ∀ k, algebraMap F (Fv F v) (Algebra.trace F E (bs k)) ∈ v.adicCompletionIntegers F :=
    Filter.eventually_all.2 fun k => GlobalTheory.CompanionTheory.SiegelND.Coef.Lim.ev_rat _
  have h6 : ∀ᶠ v in cofinite, ∀ i j, OkE bs v (J i j) :=
    Filter.eventually_all.2 fun i => Filter.eventually_all.2 fun j => ev_okE bs _
  have h7 : ∀ᶠ v in cofinite, ∀ i j, OkE bs v (T i j) :=
    Filter.eventually_all.2 fun i => Filter.eventually_all.2 fun j => ev_okE bs _
  filter_upwards [ev_okE bs (1 : E), h2, h3, h4, GlobalTheory.CompanionTheory.SiegelND.Coef.Lim.ev_rat (1 / 2 : F), h6, h7]
    with v h1 h2 h3 h4 h5 h6 h7
  have hone : (1 : Fv F v ⊗[F] E) ∈ intE bs v := by
    rw [Algebra.TensorProduct.one_def]
    exact tmul_mem_intE bs v (one_mem _) h1
  refine ⟨hone, fun e e' he he' => ?_, fun e he => ?_, fun e he => ?_, h5, fun i j => ?_, fun i j => ?_⟩
  · rw [eq_sum_tmul bs (Fv F v) e, eq_sum_tmul bs (Fv F v) e', Finset.sum_mul_sum]
    refine sum_mem_intE bs v _ _ fun k _ => sum_mem_intE bs v _ _ fun l _ => ?_
    rw [Algebra.TensorProduct.tmul_mul_tmul]
    exact tmul_mem_intE bs v (mul_mem (he k) (he' l)) (h2 k l)
  · rw [eq_sum_tmul bs (Fv F v) e, map_sum]
    refine sum_mem_intE bs v _ _ fun k _ => ?_
    have : sigR (Fv F v) σ ((Algebra.TensorProduct.basis (Fv F v) bs).repr e k ⊗ₜ[F] bs k) =
        (Algebra.TensorProduct.basis (Fv F v) bs).repr e k ⊗ₜ[F] σ (bs k) := by
      simp [sigR]
    rw [this]
    exact tmul_mem_intE bs v (he k) (h3 k)
  · rw [eq_sum_tmul bs (Fv F v) e, map_sum]
    refine sum_mem fun k _ => ?_
    rw [GlobalTheory.CompanionTheory.SW.HermSd.trace_tmul]
    exact mul_mem (he k) (h4 k)
  · simp only [inclR, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, Algebra.TensorProduct.includeRight_apply]
    exact tmul_mem_intE bs v (one_mem _) (h6 i j)
  · simp only [inclR, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, Algebra.TensorProduct.includeRight_apply]
    exact tmul_mem_intE bs v (one_mem _) (h7 i j)

theorem diag_eq_halfTrace (σ : E →ₐ[F] E) (hCM : IsCMExt F E σ) (v : HeightOneSpectrum (𝓞 F)) (e : Fv F v ⊗[F] E)
    (he : sigR (Fv F v) σ e = e) :
    e = algebraMap (Fv F v) (Fv F v ⊗[F] E) (algebraMap F (Fv F v) (1 / 2) *
      Algebra.trace (Fv F v) (Fv F v ⊗[F] E) e) := by
  haveI : FiniteDimensional F E := Module.finite_of_finrank_pos (by rw [hCM.2.2.1]; omega)
  obtain ⟨bs⟩ : Nonempty (Module.Basis (Fin (Module.finrank F E)) F E) := ⟨Module.finBasis F E⟩
  have h2 : e + e = algebraMap (Fv F v) (Fv F v ⊗[F] E) (Algebra.trace (Fv F v) (Fv F v ⊗[F] E) e) := by
    conv_lhs => rw [show e + e = e + sigR (Fv F v) σ e by rw [he]]
    rw [eq_sum_tmul bs (Fv F v) e]
    simp only [map_sum]
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    have hs : sigR (Fv F v) σ ((Algebra.TensorProduct.basis (Fv F v) bs).repr e k ⊗ₜ[F] bs k) =
        (Algebra.TensorProduct.basis (Fv F v) bs).repr e k ⊗ₜ[F] σ (bs k) := by
      simp [sigR]
    rw [hs, ← TensorProduct.tmul_add, GlobalTheory.SplitAdeleTrace.add_conj_eq_trace hCM, GlobalTheory.CompanionTheory.SW.HermSd.trace_tmul,
      Algebra.algebraMap_eq_smul_one (Algebra.trace F E (bs k)), ← TensorProduct.smul_tmul]
    simp [Algebra.TensorProduct.algebraMap_apply, Algebra.smul_def, mul_comm]
  have hh : algebraMap F (Fv F v ⊗[F] E) (1 / 2) * 2 = 1 := by
    rw [← map_ofNat (algebraMap F (Fv F v ⊗[F] E)) 2, ← map_mul]
    norm_num
    rfl
  rw [map_mul, ← IsScalarTower.algebraMap_apply, ← h2]
  calc e = (algebraMap F (Fv F v ⊗[F] E) (1 / 2) * 2) * e := by rw [hh, one_mul]
    _ = _ := by ring

theorem herm_entries (σ : E →ₐ[F] E) (hCM : IsCMExt F E σ) {d M n : ℕ} (bs : Module.Basis (Fin d) F E)
    (J : Matrix (Fin M) (Fin M) E) (T : Matrix (Fin n) (Fin n) E) (v : HeightOneSpectrum (𝓞 F)) (hv : Good σ bs J T v)
    {m : ℕ} (b : HermR (Fv F v) σ m) (hb : b ∈ latH σ bs v m) (i j : Fin m) :
    (b : Matrix (Fin m) (Fin m) (Fv F v ⊗[F] E)) i j ∈ intE bs v := by
  have hsym : ∀ a c, sigR (Fv F v) σ ((b : Matrix (Fin m) (Fin m) (Fv F v ⊗[F] E)) c a) =
      (b : Matrix (Fin m) (Fin m) (Fv F v ⊗[F] E)) a c := b.2
  rcases lt_trichotomy i j with h | h | h
  · exact hb.2 i j h
  · subst h
    rw [diag_eq_halfTrace σ hCM v _ (hsym i i)]
    exact algebraMap_mem_intE bs v hv.one (hb.1 i)
  · rw [← hsym i j]
    exact hv.sig _ (hb.2 j i h)

theorem gram_entries (σ : E →ₐ[F] E) {d M n : ℕ} (bs : Module.Basis (Fin d) F E)
    (J : Matrix (Fin M) (Fin M) E) (T : Matrix (Fin n) (Fin n) E) (v : HeightOneSpectrum (𝓞 F)) (hv : Good σ bs J T v)
    {m : ℕ} (Y : Fin m → Fin M → Fv F v ⊗[F] E) (hY : Y ∈ latV bs v) (a c : Fin m) :
    gramR (Fv F v) σ J Y a c ∈ intE bs v := by
  simp only [gramR, hR, hform, JR, Matrix.map_apply]
  refine sum_mem_intE bs v _ _ fun i _ => sum_mem_intE bs v _ _ fun j _ => ?_
  exact hv.mul _ _ (hv.mul _ _ (hv.sig _ (hY a i)) (hv.hJ i j)) (hY c j)

theorem trPair_int (σ : E →ₐ[F] E) {d M n : ℕ} (bs : Module.Basis (Fin d) F E)
    (J : Matrix (Fin M) (Fin M) E) (T : Matrix (Fin n) (Fin n) E) (v : HeightOneSpectrum (𝓞 F)) (hv : Good σ bs J T v)
    {m : ℕ} (A B : Matrix (Fin m) (Fin m) (Fv F v ⊗[F] E)) (hA : ∀ i j, A i j ∈ intE bs v)
    (hB : ∀ i j, B i j ∈ intE bs v) : trPair (Fv F v) A B ∈ v.adicCompletionIntegers F := by
  unfold trPair
  refine mul_mem hv.half (hv.tr _ ?_)
  exact sum_mem_intE bs v _ _ fun i _ => sum_mem_intE bs v _ _ fun j _ => hv.mul _ _ (hA i j) (hB j i)

theorem mulVec_latO (σ : E →ₐ[F] E) {d M n : ℕ} (bs : Module.Basis (Fin d) F E)
    (J : Matrix (Fin M) (Fin M) E) (T : Matrix (Fin n) (Fin n) E) (v : HeightOneSpectrum (𝓞 F)) (hv : Good σ bs J T v)
    {m : ℕ} (B : Matrix (Fin m) (Fin m) (Fv F v ⊗[F] E)) (hB : ∀ i j, B i j ∈ intE bs v)
    (y : Fin m → Fv F v ⊗[F] E) (hy : y ∈ latO bs v) : B.mulVec y ∈ latO bs v := by
  intro a
  show (B.mulVec y) a ∈ intE bs v
  simp only [Matrix.mulVec, dotProduct]
  exact sum_mem_intE bs v _ _ fun j _ => hv.mul _ _ (hB a j) (hy j)

end PositivityTheory.SiegelWeilFormula.GFac

end
