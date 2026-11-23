import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.T2SpaceNumberFieldInfiniteAdeles

noncomputable section

namespace GlobalTheory.GaugeEx

open NumberField IsDedekindDomain MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open scoped TensorProduct NNReal ENNReal

section BaseMap

variable {F E : Type} [Field F] [Field E] [Algebra F E]
  {R R' : Type} [CommRing R] [Algebra F R] [CommRing R'] [Algebra F R']

theorem qloc_trace_tmul [FiniteDimensional F E] (r : R) (e : E) :
    Algebra.trace R (R ⊗[F] E) (r ⊗ₜ[F] e) = r * algebraMap F R (Algebra.trace F E e) := by
  have h1 : (r ⊗ₜ[F] e : R ⊗[F] E) = r • ((1 : R) ⊗ₜ[F] e) := by
    rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
  rw [h1, map_smul, Algebra.trace_apply, Algebra.trace_apply, ← Algebra.baseChange_lmul,
    LinearMap.trace_baseChange, smul_eq_mul]

variable (φ : R →ₐ[F] R') (π : R ⊗[F] E →+* R' ⊗[F] E)
  (hπ : ∀ r e, π (r ⊗ₜ[F] e) = φ r ⊗ₜ[F] e)
include hπ

theorem qloc_trace [FiniteDimensional F E] (z : R ⊗[F] E) :
    Algebra.trace R' (R' ⊗[F] E) (π z) = φ (Algebra.trace R (R ⊗[F] E) z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul r e => rw [hπ, qloc_trace_tmul, qloc_trace_tmul, map_mul, AlgHom.commutes]
  | add x y hx hy => simp only [map_add, hx, hy]

theorem qloc_sig (σ : E →ₐ[F] E) (z : R ⊗[F] E) : sigR R' σ (π z) = π (sigR R σ z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul r e => simp [sigR, hπ]
  | add x y hx hy => simp only [map_add, hx, hy]

theorem qloc_incl (e : E) : π (inclR R e) = inclR R' e := by
  simp [inclR, hπ]

theorem qloc_q [FiniteDimensional F E] (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E)
    (z : Fin M → R ⊗[F] E) : qR R' σ J (fun i => π (z i)) = φ (qR R σ J z) := by
  have h : hR R' σ J (fun i => π (z i)) (fun i => π (z i)) = π (hR R σ J z z) := by
    simp only [hR, Formalism.UG.hform, JR, Matrix.map_apply, map_sum, map_mul, qloc_sig φ π hπ,
      qloc_incl φ π hπ]
  rw [qR, qR, h, qloc_trace φ π hπ, map_mul, AlgHom.commutes]

theorem qloc_group (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) (g : HA R σ J) :
    ∃ g' : HA R' σ J, (HA.mat R' σ J g').val = (HA.mat R σ J g).val.map π := by
  have hg : Formalism.UG.cT (sigR R σ) (HA.mat R σ J g).val * JR R J * (HA.mat R σ J g).val = JR R J :=
    Subtype.property (p := fun x => x ∈ HR R σ J) g
  have hJ : (JR R J).map π = JR R' J := by
    ext i j
    exact qloc_incl φ π hπ _
  have hc : Formalism.UG.cT (sigR R' σ) ((HA.mat R σ J g).val.map π) =
      (Formalism.UG.cT (sigR R σ) (HA.mat R σ J g).val).map π := by
    ext i j
    exact qloc_sig φ π hπ σ _
  have hm : Formalism.UG.bc π (HA.mat R σ J g) ∈ HR R' σ J := by
    change Formalism.UG.cT (sigR R' σ) ((HA.mat R σ J g).val.map π) * JR R' J *
      ((HA.mat R σ J g).val.map π) = JR R' J
    rw [hc, ← hJ, ← Matrix.map_mul, ← Matrix.map_mul, hg]
  exact ⟨(⟨_, hm⟩ : HR R' σ J), rfl⟩

end BaseMap

theorem qloc_adele_ext {F : Type} [Field F] [NumberField F] (a b : AF F)
    (h1 : fstA F a = fstA F b) (h2 : ∀ v, evalV F v (sndA F a) = evalV F v (sndA F b)) : a = b := by
  refine Prod.ext h1 ?_
  exact FiniteAdeleRing.ext F fun v => h2 v

theorem q_and_unitary_local_components : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (M : ℕ) (J : Matrix (Fin M) (Fin M) E), (∀ (z : Fin M → AF F ⊗[F] E) (β : F), qR (AF F) σ J z = algebraMap F (AF F) β ↔ qR (Ainf F) σ J (fun i => prInf (z i)) = algebraMap F (Ainf F) β ∧ ∀ v : HeightOneSpectrum (𝓞 F), qR (Fv F v) σ J (fun i => prV v (z i)) = algebraMap F (Fv F v) β) ∧ ∀ g : HA (AF F) σ J, (∃ gi : HA (Ainf F) σ J, (HA.mat (Ainf F) σ J gi).val = (HA.mat (AF F) σ J g).val.map prInf) ∧ ∀ v : HeightOneSpectrum (𝓞 F), ∃ gv : HA (Fv F v) σ J, (HA.mat (Fv F v) σ J gv).val = (HA.mat (AF F) σ J g).val.map (prV v) := by
  intro F E _ _ _ _ _ σ M J
  have hI : ∀ (r : AF F) (e : E), prInf (r ⊗ₜ[F] e) = fstA F r ⊗ₜ[F] e := fun r e => rfl
  have hV : ∀ v (r : AF F) (e : E),
      prV v (r ⊗ₜ[F] e) = ((evalV F v).comp (sndA F)) r ⊗ₜ[F] e := fun v r e => rfl
  refine ⟨fun z β => ?_, fun g => ⟨qloc_group _ _ hI σ J g, fun v => qloc_group _ _ (hV v) σ J g⟩⟩
  simp only [qloc_q _ _ hI, qloc_q _ _ (hV _)]
  constructor
  · intro h
    rw [h]
    exact ⟨AlgHom.commutes _ _, fun v => AlgHom.commutes _ _⟩
  · rintro ⟨h1, h2⟩
    refine qloc_adele_ext _ _ (by rw [h1, AlgHom.commutes]) fun v => ?_
    rw [AlgHom.commutes, AlgHom.commutes]
    exact h2 v

end GlobalTheory.GaugeEx
