import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LinearDescent
import Development.AbelianVarietyTheory.Definitions.Divisors.GaloisRepOfPolarizedCuspidal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MulMat
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MulMatInjective
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIntegralOfIsCompactClosureZpowers
open NumberField GlobalTheory.UnitaryBC IsDedekindDomain Matrix Polynomial GlobalTheory.CuspRep Formalism.UG GlobalTheory.BCT
open scoped Classical

namespace GlobalTheory.TwLat

variable {E : Type} [Field E] [NumberField E] {w : Pl E} {K : GlobalTheory.UnitLemma.UQ}
  (e : K.E ≃+* w.adicCompletion E) {B : GlobalTheory.UnitLemma.InvAlg K} {m : ℕ} (b : Module.Basis (Fin m) K.E B.A)

noncomputable def mulMatHom : B.A →+* Matrix (Fin m) (Fin m) (w.adicCompletion E) :=
  (e : K.E →+* w.adicCompletion E).mapMatrix.comp
    ((LinearMap.toMatrixAlgEquiv b).toRingHom.comp (Algebra.lmul K.E B.A).toRingHom)

theorem mulMatHom_apply (a : B.A) : mulMatHom e b a = mulMat e b a := by
  rw [mulMat_eq_map]
  simp only [mulMatHom, RingHom.comp_apply]
  congr 1

theorem mulMatHom_algebraMap (x : K.E) :
    mulMatHom e b (algebraMap K.E B.A x) = algebraMap (w.adicCompletion E) _ (e x) := by
  simp only [mulMatHom, RingHom.comp_apply, AlgHom.toRingHom_eq_coe, AlgEquiv.toRingEquiv_eq_coe,
    RingEquiv.toRingHom_eq_coe, AlgHom.coe_toRingHom, AlgHom.commutes, RingEquiv.coe_toRingHom,
    AlgEquiv.coe_ringEquiv, AlgEquiv.commutes]
  rw [Matrix.algebraMap_eq_diagonal, Matrix.algebraMap_eq_diagonal]
  simp [Pi.algebraMap_def]

theorem mulMatHom_injective : Function.Injective (mulMatHom e b) := by
  intro a a' h
  rw [mulMatHom_apply, mulMatHom_apply] at h
  exact mulMat_injective e b h

theorem isIntegral_of_isIntegral_mulMat
    (hint : ∀ x, x ∈ (algebraMap K.O K.E).range ↔ Valued.v (e x) ≤ 1) (a : B.A)
    (h : IsIntegral (w.adicCompletionIntegers E) (mulMat e b a)) : IsIntegral K.O a := by
  obtain ⟨p, hpm, hp⟩ := h
  set Q : (w.adicCompletion E)[X] := p.map (algebraMap (w.adicCompletionIntegers E) (w.adicCompletion E)) with hQdef
  have hQ : aeval (mulMat e b a) Q = 0 := by
    rw [hQdef, aeval_map_algebraMap]; exact hp
  set Q' : K.E[X] := Q.map e.symm.toRingHom with hQ'def
  have hQQ : Q'.map (e : K.E →+* w.adicCompletion E) = Q := by
    rw [hQ'def, Polynomial.map_map]
    convert Polynomial.map_id
    ext x; simp
  have hu : aeval a Q' = 0 := by
    apply mulMatHom_injective e b
    rw [map_zero, aeval_def, Polynomial.hom_eval₂]
    have hc : (mulMatHom e b).comp (algebraMap K.E B.A) =
        (algebraMap (w.adicCompletion E) (Matrix (Fin m) (Fin m) (w.adicCompletion E))).comp
          (e : K.E →+* w.adicCompletion E) := by
      ext x; simp [mulMatHom_algebraMap]
    rw [hc, ← Polynomial.eval₂_map, hQQ, mulMatHom_apply, ← aeval_def]
    exact hQ
  have hlift : Q' ∈ Polynomial.lifts (algebraMap K.O K.E) := by
    rw [Polynomial.lifts_iff_coeff_lifts]
    intro i
    rw [hQ'def, Polynomial.coeff_map, hQdef, Polynomial.coeff_map]
    have hv : Valued.v (algebraMap (w.adicCompletionIntegers E) (w.adicCompletion E) (p.coeff i)) ≤ 1 :=
      (IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).1 (p.coeff i).2
    have := (hint (e.symm (algebraMap _ _ (p.coeff i)))).2 (by simpa using hv)
    simpa using this
  obtain ⟨P, hPm, -, hPmon⟩ := Polynomial.lifts_and_degree_eq_and_monic hlift (by rw [hQ'def]; exact (hpm.map _).map _)
  refine ⟨P, hPmon, ?_⟩
  rw [← Polynomial.aeval_def, ← Polynomial.aeval_map_algebraMap K.E, hPm]
  exact hu

theorem mem_intUnits_of_isCompact_closure_zpowers : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ (w : Pl E), ¬ IsSplitAt w → ∀ (K : GlobalTheory.UnitLemma.UQ) (e : K.E ≃+* w.adicCompletion E), (∀ x, e (K.c x) = cj w (e x)) → (∀ x, x ∈ (algebraMap K.O K.E).range ↔ Valued.v (e x) ≤ 1) → (∀ x, GlobalTheory.UnitLemma.val K.O x = ordL (e x)) → ∀ (B : GlobalTheory.UnitLemma.InvAlg K) (m : ℕ) (b : Module.Basis (Fin m) K.E B.A) (a : B.Aˣ), IsCompact (closure (Subgroup.zpowers (GlobalTheory.TwLat.mulU e b a) : Set (GLw m w))) → a ∈ GlobalTheory.UnitLemma.intUnits K.O B.A := by
  intro E _ _ _ _ w _ K e _ hint _ B m b a hc
  have h1 : IsIntegral (w.adicCompletionIntegers E) (mulMat e b (a : B.A)) := by
    rw [← mulU_val]
    exact GlobalTheory.isIntegral_of_isCompact_closure_zpowers E w m _ hc
  have hc' : IsCompact (closure (Subgroup.zpowers (mulU e b a⁻¹) : Set (GLw m w))) := by
    rw [map_inv, Subgroup.zpowers_inv]; exact hc
  have h2 : IsIntegral (w.adicCompletionIntegers E) (mulMat e b ((a⁻¹ : B.Aˣ) : B.A)) := by
    rw [← mulU_val]
    exact GlobalTheory.isIntegral_of_isCompact_closure_zpowers E w m _ hc'
  exact ⟨isIntegral_of_isIntegral_mulMat e b hint _ h1, isIntegral_of_isIntegral_mulMat e b hint _ h2⟩

end GlobalTheory.TwLat
