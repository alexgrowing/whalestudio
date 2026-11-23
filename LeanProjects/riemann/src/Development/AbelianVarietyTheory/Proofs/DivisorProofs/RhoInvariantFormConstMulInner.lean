import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsUSplittingTrRep
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.RealMetaplecticRepresentation
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPairingCoordinatesSchrodingerFolland
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MulRealAdEqZero
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.WeilTr MeasureTheory
open scoped Matrix ENNReal

noncomputable section

namespace GlobalTheory.ArchUniq.FormTransport

open GlobalTheory.RealWeil GlobalTheory.ArchUniq
open scoped SchwartzMap ComplexConjugate

theorem rhoFun_mul_conj {n : ℕ} (w : Fin n ⊕ Fin n → ℝ) (G G' : EuclideanSpace ℝ (Fin n) → ℂ)
    (x : EuclideanSpace ℝ (Fin n)) :
    rhoFun w G x * conj (rhoFun w G' x) = G (x + pPart w) * conj (G' (x + pPart w)) := by
  have h : phase w x * conj (phase w x) = 1 := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, norm_phase]; simp
  simp only [rhoFun, map_mul]
  calc _ = (phase w x * conj (phase w x)) * (G (x + pPart w) * conj (G' (x + pPart w))) := by ring
    _ = _ := by rw [h, one_mul]

theorem integral_rhoFun_mul_conj {n : ℕ} (w : Fin n ⊕ Fin n → ℝ) (G G' : EuclideanSpace ℝ (Fin n) → ℂ) :
    ∫ x, rhoFun w G x * conj (rhoFun w G' x) = ∫ x, G x * conj (G' x) := by
  simp_rw [rhoFun_mul_conj]
  exact integral_add_right_eq_self (fun x => G x * conj (G' x)) (pPart w)

open scoped Classical in

theorem schr_eq_schrF {F : Type} [Field F] [NumberField F] [Invertible (2 : mixedEmbedding.mixedSpace F)]
    {κ : Type} [Fintype κ] (ψ : AddChar (mixedEmbedding.mixedSpace F) ℂ)
    (hψ : ∀ a, ψ a = Complex.exp (-(2 * Real.pi * Complex.I) *
      (Algebra.trace ℝ (mixedEmbedding.mixedSpace F) a : ℝ)))
    (w : (κ → mixedEmbedding.mixedSpace F) × (κ → mixedEmbedding.mixedSpace F))
    (u : (κ → mixedEmbedding.mixedSpace F) → ℂ) :
    schr ψ w u = schrF (trP F κ) w u := by
  funext x
  have h2 : (⅟(2 : mixedEmbedding.mixedSpace F)) = algebraMap ℝ (mixedEmbedding.mixedSpace F) (1 / 2) := by
    refine invOf_eq_right_inv ?_
    rw [← map_ofNat (algebraMap ℝ (mixedEmbedding.mixedSpace F)) 2, ← map_mul]
    norm_num
  have ht : Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (x ⬝ᵥ w.2 + ⅟(2 : mixedEmbedding.mixedSpace F) * (w.1 ⬝ᵥ w.2)) =
      trP F κ x w.2 + trP F κ w.1 w.2 / 2 := by
    rw [map_add, h2, ← Algebra.smul_def, map_smul, smul_eq_mul]
    simp only [trP, dotProduct]
    ring
  simp only [schr, schrF, hψ, ht]

theorem haar_coords_cplx {n : ℕ} {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [MeasurableSpace V]
    [BorelSpace V] [FiniteDimensional ℝ V] (μ : Measure V) [μ.IsAddHaarMeasure]
    (C : V ≃L[ℝ] EuclideanSpace ℝ (Fin n)) :
    ∃ k : ℝ, ∀ G : V → ℂ, ∫ y, G y ∂μ = (k : ℂ) * ∫ x, G (C.symm x) := by
  let e : V ≃ᵐ EuclideanSpace ℝ (Fin n) := C.toHomeomorph.toMeasurableEquiv
  have he : ∀ y, e y = C y := fun y => rfl
  haveI : (μ.map e).IsAddHaarMeasure := C.isAddHaarMeasure_map μ
  have hk := Measure.isAddLeftInvariant_eq_smul (μ.map e) (volume : Measure (EuclideanSpace ℝ (Fin n)))
  refine ⟨(Measure.addHaarScalarFactor (μ.map e) volume : ℝ), fun G => ?_⟩
  have h1 : ∫ y, G y ∂μ = ∫ x, G (C.symm x) ∂(μ.map e) := by
    rw [integral_map_equiv]
    simp [he]
  rw [h1, congrArg (fun m => ∫ x, G (C.symm x) ∂m) hk]
  simp only [integral_smul_nnreal_measure, NNReal.smul_def, Complex.real_smul]

open scoped Classical in

theorem const_of_euclidean : (∀ (n : ℕ) (B : GlobalTheory.RealWeil.Sch (Fin n) → GlobalTheory.RealWeil.Sch (Fin n) → ℂ),
    (∀ h', ∃ L : GlobalTheory.RealWeil.Sch (Fin n) →L[ℂ] ℂ, ∀ h, B h h' = L h) →
    (∀ h h', B h' h = starRingEnd ℂ (B h h')) → (∀ h, 0 ≤ (B h h).re) →
    (∀ (w : Fin n ⊕ Fin n → ℝ) (h h' g g' : GlobalTheory.RealWeil.Sch (Fin n)), ⇑g = GlobalTheory.RealWeil.rhoFun w ⇑h →
      ⇑g' = GlobalTheory.RealWeil.rhoFun w ⇑h' → B g g' = B h h') →
    ∃ c : ℝ, 0 ≤ c ∧ ∀ h h', B h h' = c * ∫ x, h x * starRingEnd ℂ (h' x)) → ∀ (F : Type) [Field F] [NumberField F] [Invertible (2 : mixedEmbedding.mixedSpace F)] (κ : Type) [Fintype κ]
    (ψ : AddChar (mixedEmbedding.mixedSpace F) ℂ),
    (∀ a, ψ a = Complex.exp (-(2 * Real.pi * Complex.I) * (Algebra.trace ℝ (mixedEmbedding.mixedSpace F) a : ℝ))) →
    ∀ (T : SInf F κ →L[ℂ] SInf F κ)
      (A : (κ → mixedEmbedding.mixedSpace F) × (κ → mixedEmbedding.mixedSpace F) →
        (κ → mixedEmbedding.mixedSpace F) × (κ → mixedEmbedding.mixedSpace F)),
      (∀ w (f g : SInf F κ), (g : (κ → mixedEmbedding.mixedSpace F) → ℂ) = schr ψ w f →
        (T g : (κ → mixedEmbedding.mixedSpace F) → ℂ) = schr ψ (A w) (T f)) →
      ∃ c : ℝ, 0 ≤ c ∧ ∀ μ : @Measure (κ → mixedEmbedding.mixedSpace F) (borel _),
        @Measure.IsAddHaarMeasure _ _ _ (borel _) μ → ∀ f f' : SInf F κ,
          @integral _ ℂ _ _ (borel _) μ (fun x => T f x * starRingEnd ℂ (T f' x)) =
            (c : ℂ) * @integral _ ℂ _ _ (borel _) μ (fun x => f x * starRingEnd ℂ (f' x)) := by
  intro H F _ _ _ κ _ ψ hψ T A hT
  letI : MeasurableSpace (κ → mixedEmbedding.mixedSpace F) := borel _
  haveI : BorelSpace (κ → mixedEmbedding.mixedSpace F) := ⟨rfl⟩
  have hP : IsPairing (trP F κ) := Coord.isPairing_trP κ
  obtain ⟨C, φ, -, hS⟩ := exists_pairing_coords (κ → mixedEmbedding.mixedSpace F) (trP F κ) hP _ rfl
  generalize Module.finrank ℝ (κ → mixedEmbedding.mixedSpace F) = n at C φ hS
  let toE : SInf F κ →L[ℂ] Sch (Fin n) := SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (F := ℂ) C.symm
  let toV : Sch (Fin n) →L[ℂ] SInf F κ := SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (F := ℂ) C
  have htoE : ∀ g, ⇑(toE g) = ⇑g ∘ ⇑C.symm := fun g => rfl
  have htoV : ∀ h, ⇑(toV h) = ⇑h ∘ ⇑C := fun h => rfl
  have hVE : ∀ g, toV (toE g) = g := fun g => by ext x; simp [htoE, htoV]
  let T' : Sch (Fin n) →L[ℂ] Sch (Fin n) := toE.comp (T.comp toV)
  have hT' : ∀ h, T' h = toE (T (toV h)) := fun h => rfl
  have hI : ∀ w (h g : Sch (Fin n)), ⇑g = rhoFun w ⇑h → ⇑(T' g) = rhoFun (φ (A (φ.symm w))) ⇑(T' h) := by
    intro w h g hg
    have e1 : ⇑(toV g) = schr ψ (φ.symm w) ⇑(toV h) := by
      rw [schr_eq_schrF ψ hψ]
      funext x
      have := congrFun (hS (φ.symm w) ⇑h) x
      simp only [Function.comp_apply, LinearEquiv.apply_symm_apply] at this
      simp only [htoV, Function.comp_apply, hg]
      exact this.symm
    have e2 := hT _ _ _ e1
    rw [schr_eq_schrF ψ hψ] at e2
    rw [hT', hT', htoE, htoE, e2]
    obtain ⟨G, hG⟩ : ∃ G : EuclideanSpace ℝ (Fin n) → ℂ, ⇑(T (toV h)) = G ∘ ⇑C :=
      ⟨⇑(T (toV h)) ∘ ⇑C.symm, by ext x; simp⟩
    have hGC : (G ∘ ⇑C) ∘ ⇑C.symm = G := by funext x; simp
    rw [hG, hS, hGC]
    funext x
    simp
  let B : Sch (Fin n) → Sch (Fin n) → ℂ := fun h h' => ∫ x, T' h x * conj (T' h' x)
  have hcont : ∀ h', ∃ L : Sch (Fin n) →L[ℂ] ℂ, ∀ h, B h h' = L h := by
    intro h'
    refine ⟨(innerSL ℂ ((T' h').toLp 2)).comp
      ((SchwartzMap.toLpCLM ℂ ℂ 2 (volume : Measure (EuclideanSpace ℝ (Fin n)))).comp T'), fun h => ?_⟩
    simp only [ContinuousLinearMap.comp_apply, innerSL_apply_apply, SchwartzMap.toLpCLM_apply]
    rw [SchwartzMap.inner_toL2_toL2_eq (T' h') (T' h) volume]
    simp only [B, RCLike.inner_apply]
  have hherm : ∀ h h', B h' h = conj (B h h') := by
    intro h h'
    simp only [B]
    rw [← integral_conj]
    congr 1
    funext x
    simp [mul_comm]
  have hpos : ∀ h, 0 ≤ (B h h).re := by
    intro h
    have e : B h h = ((∫ x, Complex.normSq (T' h x) : ℝ) : ℂ) := by
      have e0 : B h h = ∫ x, ((Complex.normSq (T' h x) : ℝ) : ℂ) := by simp only [B, Complex.mul_conj]
      rw [e0]
      first
        | exact integral_complex_ofReal
        | exact integral_ofReal
    rw [e, Complex.ofReal_re]
    exact integral_nonneg fun x => Complex.normSq_nonneg _
  have hinv : ∀ (w : Fin n ⊕ Fin n → ℝ) (h h' g g' : Sch (Fin n)), ⇑g = rhoFun w ⇑h →
      ⇑g' = rhoFun w ⇑h' → B g g' = B h h' := by
    intro w h h' g g' hg hg'
    simp only [B]
    rw [hI w h g hg, hI w h' g' hg']
    exact integral_rhoFun_mul_conj _ _ _
  obtain ⟨c, hc0, hc⟩ := H n B hcont hherm hpos hinv
  have hB : ∀ f f' : SInf F κ, ∫ x, T f (C.symm x) * conj (T f' (C.symm x)) =
      (c : ℂ) * ∫ x, f (C.symm x) * conj (f' (C.symm x)) := by
    intro f f'
    have := hc (toE f) (toE f')
    simpa only [B, hT', hVE, htoE, Function.comp_apply] using this
  refine ⟨c, hc0, fun μ hμ f f' => ?_⟩
  haveI := hμ
  obtain ⟨k, hk⟩ := haar_coords_cplx μ C
  rw [hk, hk, hB]
  ring

end GlobalTheory.ArchUniq.FormTransport

end
