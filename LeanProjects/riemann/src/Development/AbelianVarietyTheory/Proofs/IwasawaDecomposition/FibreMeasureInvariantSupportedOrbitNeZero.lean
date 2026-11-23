import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.T2SpaceNumberFieldInfiniteAdeles
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FibreFamilyHermitianQuadraticFormAtUnitPropsStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FibreMeasuresTransportUnitarySimilitudeStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HaarModulusTensorEqModulusNormStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousDistribHaarCharUnits
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CmExtensionLocalFieldProductRingExistsSmulEqStatement

open NumberField IsDedekindDomain MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.GaugeEx
open scoped TensorProduct NNReal ENNReal

namespace GlobalTheory.GaugeEx.FibProp

section Alg

variable {A : Type} [CommRing A] {n : ℕ} (s : A →+* A) (J : Matrix (Fin n) (Fin n) A)

theorem form_eq (x y : Fin n → A) :
    Formalism.UG.hform s J x y = dotProduct (fun i => s (x i)) (J.mulVec y) := by
  simp only [Formalism.UG.hform, dotProduct, Matrix.mulVec, Finset.mul_sum, mul_assoc]

theorem form_mulVec {g : Matrix (Fin n) (Fin n) A} (hg : Formalism.UG.cT s g * J * g = J) (x y : Fin n → A) :
    Formalism.UG.hform s J (g.mulVec x) (g.mulVec y) = Formalism.UG.hform s J x y := by
  have e : (fun i => s (g.mulVec x i)) = Matrix.vecMul (fun i => s (x i)) (Formalism.UG.cT s g) := by
    funext i
    simp only [Matrix.mulVec, Matrix.vecMul, dotProduct, map_sum, map_mul, Formalism.UG.cT, Matrix.transpose_apply,
      Matrix.map_apply, mul_comm]
  rw [form_eq, form_eq, e, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hg]

theorem form_smul (a : A) (x : Fin n → A) :
    Formalism.UG.hform s J (a • x) (a • x) = s a * a * Formalism.UG.hform s J x x := by
  simp only [Formalism.UG.hform, Pi.smul_apply, smul_eq_mul, map_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

theorem det_norm {g : Matrix (Fin n) (Fin n) A} (hJ : IsUnit J.det) (hg : Formalism.UG.cT s g * J * g = J) :
    g.det * s g.det = 1 := by
  have h := congrArg Matrix.det hg
  rw [Matrix.det_mul, Matrix.det_mul, Formalism.UG.cT, Matrix.det_transpose, ← RingHom.mapMatrix_apply,
    ← RingHom.map_det] at h
  apply hJ.mul_left_cancel
  linear_combination h

theorem lrAct_one (g : Matrix (Fin n) (Fin n) A) {k : ℕ} (X : Fin k → Fin n → A) :
    lrAct g 1 X = fun a => g.mulVec (X a) := by
  funext a
  simp [lrAct, Matrix.one_apply]

end Alg

section Q

variable {F E : Type} [Field F] [Field E] [Algebra F E]
  (R : Type) [CommRing R] [Algebra F R] (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E)

theorem sig_alg (r : R) : sigR R σ (algebraMap R (R ⊗[F] E) r) = algebraMap R (R ⊗[F] E) r := by
  simp [sigR, Algebra.TensorProduct.algebraMap_apply]

theorem sig_incl (e : E) : sigR R σ (inclR R e) = inclR R (σ e) := by
  simp [sigR, inclR]

theorem q_scale (r : R) (z : Fin M → R ⊗[F] E) :
    qR R σ J (algebraMap R (R ⊗[F] E) r • z) = r * r * qR R σ J z := by
  unfold qR hR
  rw [form_smul, sig_alg, ← map_mul, ← Algebra.smul_def (r * r), map_smul, smul_eq_mul]
  ring

theorem q_rat [CharZero F] (h2 : Module.finrank F E = 2) (x : Fin M → E) (β : F)
    (hx : hE σ J x x = algebraMap F E β) :
    qR R σ J (fun i => inclR R (x i)) = algebraMap F R β := by
  haveI : FiniteDimensional F E := Module.finite_of_finrank_eq_succ h2
  have e : hR R σ J (fun i => inclR R (x i)) (fun i => inclR R (x i)) = inclR R (hE σ J x x) := by
    simp only [hR, hE, Formalism.UG.hform, JR, Matrix.map_apply, sig_incl, map_sum, map_mul]
    rfl
  have e2 : inclR R (algebraMap F E β) = algebraMap R (R ⊗[F] E) (algebraMap F R β) := by
    rw [← IsScalarTower.algebraMap_apply]
    exact (Algebra.TensorProduct.includeRight : E →ₐ[F] R ⊗[F] E).commutes β
  unfold qR
  rw [e, hx, e2, Algebra.trace_algebraMap_of_basis
    (Algebra.TensorProduct.basis R (Module.finBasisOfFinrankEq F E h2))]
  simp only [Fintype.card_fin, nsmul_eq_mul]
  rw [← mul_assoc, ← map_natCast (algebraMap F R), ← map_mul]
  norm_num

theorem q_cont [TopologicalSpace R] [FiniteDimensional F E] [IsTopologicalRing R] :
    Continuous (qR R σ J) := by
  have hs : Continuous (sigR R σ) :=
    IsModuleTopology.continuous_of_linearMap
      (Algebra.TensorProduct.map (AlgHom.id R R) σ).toLinearMap
  have ht : Continuous (Algebra.trace R (R ⊗[F] E)) := IsModuleTopology.continuous_of_linearMap _
  unfold qR hR Formalism.UG.hform
  fun_prop

end Q

theorem fibre_invariant_orbit_ne_zero : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [IsTopologicalRing R] [T2Space R] [LocallyCompactSpace R] [SecondCountableTopology R] [MeasurableSpace R] [BorelSpace R], Nice R → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E) (x : Fin 1 → Fin M → E) (β : F) (lam : Measure (R ⊗[F] E)) (ν : Measure R) (m : Measure (Fin 1 → Fin M → R ⊗[F] E)), IsHermND σ J → β ≠ 0 → hE σ J (x 0) (x 0) = algebraMap F E β → lam.IsAddHaarMeasure → ν.IsAddHaarMeasure → FibAt R σ J (tupMeas lam 1 M) ν (algebraMap F R β) m → IsInvTup R σ J m ∧ OnOrbit R σ J x m ∧ m ≠ 0 := by
  intro F E _ _ _ _ _ σ hCM R _ _ _ _ _ _ _ _ _ hN M J x β lam ν m hJ hβ hx hlam hν hm
  have hu : IsUnit (algebraMap F R β) := (IsUnit.mk0 β hβ).map _
  have hq : qR R σ J (ratTup (F := F) R x 0) = algebraMap F R β := q_rat R σ J hCM.2.2.1 (x 0) β hx
  obtain ⟨hsupp, -, huniq⟩ := GlobalTheory.T.fibreFamily_hermitian_quadratic_form_at_unit_props F E σ R hN M J _ ν _ m hν hu hm
  have h1 : modu R 1 = 1 := (GlobalTheory.GaugeEx.modu_basic R).2.2.1
  refine ⟨fun g => ?_, ?_, ?_⟩
  · set G : Matrix (Fin M) (Fin M) (R ⊗[F] E) := (HA.mat R σ J g).val with hG
    have hg : Formalism.UG.cT (sigR R σ) G * JR R J * G = JR R J := g.2
    have hd : IsUnit G.det := (Matrix.isUnit_iff_isUnit_det _).1 (HA.mat R σ J g).isUnit
    have hJu : IsUnit (JR (F := F) R J).det := by
      unfold JR
      rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]
      exact (IsUnit.mk0 _ hJ.2).map _
    have hm1 : modu (R ⊗[F] E) G.det = 1 := by
      rw [(GlobalTheory.T.haarModulus_tensor_eq_modulus_norm F E σ hCM R G.det 1 hd (by rw [map_one, det_norm _ _ hJu hg])).2, h1]
    have := GlobalTheory.T.fibreMeasures_transport_unitary_similitude F E σ R hN M J J lam ν _ 1 m G hlam hν hd isUnit_one
      (fun z => by rw [one_mul]; unfold qR hR; rw [form_mulVec _ _ hg]) hm
    rw [one_mul, hm1, h1, inv_one, mul_one, one_smul] at this
    have e : lrAct G 1 = fun X : Fin 1 → Fin M → R ⊗[F] E => g • X := by
      funext X; rw [lrAct_one]; rfl
    rw [e] at this
    exact huniq _ this
  · refine measure_mono_null (fun y hy => ?_) hsupp
    exact fun h => hy (GlobalTheory.T.cmExtension_localFieldProductRing_exists_smul_eq F E σ hCM R hN M J hJ _ _ y hu hq h)
  · rintro rfl
    obtain ⟨-, -, hO, U, hU, h1U, s, -, -, hs⟩ := id hN
    obtain ⟨fib, hfib, -⟩ := id hm
    obtain ⟨w, hw⟩ := hu
    let T : Set R := {b | IsUnit b} ∩ (fun b => b * (↑w⁻¹ : R)) ⁻¹' U
    have hT : IsOpen T := by
      refine IsOpen.inter ?_ (hU.preimage (by fun_prop))
      exact hO.isOpenEmbedding_unitsVal.isOpen_range
    have hz : ∀ b ∈ T, fib b = 0 := by
      rintro b ⟨hb, hbU⟩
      set r := s (b * (↑w⁻¹ : R))
      have hr : r * r = b * (↑w⁻¹ : R) := hs _ hbU
      have hrr : IsUnit (r * r) := hr ▸ IsUnit.mul hb (Units.isUnit _)
      have hru : IsUnit r := isUnit_of_mul_isUnit_left hrr
      have := GlobalTheory.T.fibreMeasures_transport_unitary_similitude F E σ R hN M J J lam ν _ (r * r) 0
        (algebraMap R (R ⊗[F] E) r • (1 : Matrix (Fin M) (Fin M) (R ⊗[F] E))) hlam hν
        (by rw [Matrix.det_smul, Matrix.det_one, mul_one]; exact (hru.map _).pow _) hrr
        (fun z => by rw [Matrix.smul_mulVec, Matrix.one_mulVec, q_scale]) hm
      rw [Measure.map_zero, smul_zero, hr, ← hw, Units.inv_mul_cancel_right] at this
      exact (GlobalTheory.T.fibreFamily_hermitian_quadratic_form_at_unit_props F E σ R hN M J _ ν _ 0 hν hb this).2.2 _ ⟨fib, hfib, rfl⟩
    let O : Set (Fin 1 → Fin M → R ⊗[F] E) := (fun X => qR R σ J (X 0)) ⁻¹' T
    have hOo : IsOpen O := hT.preimage ((q_cont R σ J).comp (continuous_apply 0))
    have hne : O.Nonempty := ⟨ratTup (F := F) R x, by
      show qR R σ J (ratTup (F := F) R x 0) ∈ T
      rw [hq, ← hw]
      exact ⟨w.isUnit, by simpa using h1U⟩⟩
    have key := hfib.2.1 (O.indicator 1) (measurable_one.indicator hOo.measurableSet)
    have hz' : ∀ b, fib b O = 0 := by
      intro b
      by_cases hb : b ∈ T
      · rw [hz b hb]; rfl
      · refine measure_mono_null (fun y hy => ?_) (hfib.1 b)
        intro h
        apply hb
        have : qR R σ J (y 0) = b := h.1
        rw [← this]; exact hy
    simp only [Measure.restrict_univ, lintegral_indicator_one hOo.measurableSet, hz',
      lintegral_zero] at key
    haveI : (tupMeas lam 1 M).IsOpenPosMeasure := by
      unfold tupMeas
      haveI : (Measure.pi fun _ : Fin M => lam).IsOpenPosMeasure :=
        Measure.pi.isOpenPosMeasure (fun _ : Fin M => lam)
      exact Measure.pi.isOpenPosMeasure (fun _ : Fin 1 => Measure.pi fun _ : Fin M => lam)
    exact (hOo.measure_pos _ hne).ne' key

end GlobalTheory.GaugeEx.FibProp
