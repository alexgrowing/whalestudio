import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.T2SpaceNumberFieldInfiniteAdeles
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IntegralPointsFinitePlaceTensorProperties

noncomputable section

namespace GlobalTheory.GaugeEx.PairLat

open NumberField IsDedekindDomain MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.GaugeEx
open scoped TensorProduct NNReal ENNReal

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]
  {d : ℕ} (b : Module.Basis (Fin d) F E)

theorem ev_incl (e : E) : ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite,
    inclR (Fv F v) e ∈ intV b v := by
  filter_upwards [IntBasis.ev_int_coord b e] with v hv
  exact IntBasis.tmul_mem b v (one_mem _) hv

theorem ev_map {m n : ℕ} (A : Matrix (Fin m) (Fin n) E) :
    ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite,
      ∀ i j, A.map (inclR (Fv F v)) i j ∈ intV b v :=
  Filter.eventually_all.2 fun i => Filter.eventually_all.2 fun j => ev_incl b (A i j)

theorem mulVec_mem (v : HeightOneSpectrum (𝓞 F))
    (hm : ∀ y ∈ intV b v, ∀ z ∈ intV b v, y * z ∈ intV b v) {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) (Fv F v ⊗[F] E)) (hA : ∀ i j, A i j ∈ intV b v)
    (w : Fin n → Fv F v ⊗[F] E) (hw : ∀ j, w j ∈ intV b v) (i : Fin m) :
    A.mulVec w i ∈ intV b v := by
  have h : A.mulVec w i = ∑ j, A i j * w j := rfl
  rw [h]
  exact IntBasis.sum_mem' b v Finset.univ (fun j => A i j * w j) fun j _ => hm _ (hA i j) _ (hw j)

theorem main : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (d : ℕ) (b : Module.Basis (Fin d) F E) (M : ℕ) (J : Matrix (Fin (M + 1)) (Fin (M + 1)) E) (x : Fin 1 → Fin (M + 1) → E) (a : F) (B : Matrix (Fin (M + 1)) (Fin M) E) (J' : Matrix (Fin M) (Fin M) E), StepData σ J x a B J' → ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite, ∀ k : HA (Fv F v) σ J, (∀ i j, (HA.mat (Fv F v) σ J k).val i j ∈ intV b v ∧ (HA.mat (Fv F v) σ J (k)⁻¹).val i j ∈ intV b v) → ∀ (y : Fin 1 → Fin (M + 1) → Fv F v ⊗[F] E) (y' : Fin 1 → Fin M → Fv F v ⊗[F] E), pairOf (Fv F v) σ J B y k y' ∈ latV b v ↔ y ∈ latV b v ∧ y' ∈ latV b v := by
  intro F E _ _ _ _ _ σ d b M J x a B J' hS
  obtain ⟨-, -, -, -, hJ', hH⟩ := hS
  have hdet : J'.det ≠ 0 := hH.2
  set C : Matrix (Fin M) (Fin (M + 1)) E := J'⁻¹ * (Formalism.UG.cT (σ : E →+* E) B * J) with hC
  have hCB : C * B = 1 := by
    rw [hC, Matrix.mul_assoc, ← hJ']
    exact Matrix.nonsing_inv_mul _ (Ne.isUnit hdet)
  filter_upwards [(IntBasis.main F E σ d b).2.1, ev_map b B, ev_map b C] with v hv hB hCv k hk y y'
  have hm := hv.2.1
  simp only [mem_latV_iff, Fin.forall_fin_two, Fin.forall_fin_one]
  refine and_congr Iff.rfl ⟨fun h => ?_, fun h => ?_⟩
  · have h1 := mulVec_mem b v hm _ hCv _ (mulVec_mem b v hm _ (fun i j => (hk i j).2) _ h)
    have h2 : (C.map (inclR (Fv F v))).mulVec (((HA.mat (Fv F v) σ J k)⁻¹).val.mulVec
        (pairOf (Fv F v) σ J B y k y' 1)) = y' 0 := by
      change (C.map (inclR (Fv F v))).mulVec (((HA.mat (Fv F v) σ J k)⁻¹).val.mulVec
        ((HA.mat (Fv F v) σ J k).val.mulVec ((B.map (inclR (Fv F v))).mulVec (y' 0)))) = y' 0
      rw [Matrix.mulVec_mulVec _ _ (HA.mat (Fv F v) σ J k).val, Units.inv_mul, Matrix.one_mulVec,
        Matrix.mulVec_mulVec, ← Matrix.map_mul, hCB, Matrix.map_one _ (map_zero _) (map_one _),
        Matrix.one_mulVec]
    intro i
    rw [← h2]
    exact h1 i
  · exact mulVec_mem b v hm _ (fun i j => (hk i j).1) _ (mulVec_mem b v hm _ hB _ h)

end GlobalTheory.GaugeEx.PairLat
