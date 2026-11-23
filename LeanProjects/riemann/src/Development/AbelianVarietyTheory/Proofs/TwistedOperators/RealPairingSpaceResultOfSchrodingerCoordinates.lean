import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsPairingStdP
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.RealMetaplecticRepresentation
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPairingCoordinatesSchrodingerFolland

open GlobalTheory.ArchUniq GlobalTheory.RealWeil MeasureTheory
open scoped SchwartzMap RealInnerProductSpace

noncomputable section

namespace GlobalTheory.ArchUniq.SchrTransport

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]

theorem coords (P : V → V → ℝ) (hP : IsPairing P) [FiniteDimensional ℝ V] (n : ℕ) (hn : Module.finrank ℝ V = n) :
    ∃ (C : V ≃L[ℝ] EuclideanSpace ℝ (Fin n)) (φ : (V × V) ≃ₗ[ℝ] (Fin n ⊕ Fin n → ℝ)),
      (∀ v, pPart (φ v) = C v.1) ∧ ∀ v y, ⟪qPart (φ v), C y⟫ = -P y v.2 := by
  let C : V ≃L[ℝ] EuclideanSpace ℝ (Fin n) :=
    ContinuousLinearEquiv.ofFinrankEq (hn.trans (finrank_euclideanSpace_fin).symm)
  have hdim : Module.finrank ℝ (V × V) = Module.finrank ℝ (Fin n ⊕ Fin n → ℝ) := by
    simp [Module.finrank_prod, hn]
  let φ : (V × V) ≃ₗ[ℝ] (Fin n ⊕ Fin n → ℝ) :=
    LinearMap.linearEquivOfInjective (pairCoordsL C hP) (pairCoordsL_injective C hP) hdim
  have hφ : ∀ v, φ v = pairCoordsL C hP v := fun v => rfl
  refine ⟨C, φ, fun v => ?_, fun v y => ?_⟩
  · ext i; simp [hφ, pPart, pairCoordsL]
  · rw [pair_expand C hP y v.2]
    simp [hφ, qPart, pairCoordsL, PiLp.inner_apply, mul_comm]

theorem schr_coords {n : ℕ} (P : V → V → ℝ) (C : V ≃L[ℝ] EuclideanSpace ℝ (Fin n))
    (φ : (V × V) ≃ₗ[ℝ] (Fin n ⊕ Fin n → ℝ)) (hp : ∀ v, pPart (φ v) = C v.1)
    (hq : ∀ v y, ⟪qPart (φ v), C y⟫ = -P y v.2) (v : V × V) (f : EuclideanSpace ℝ (Fin n) → ℂ) :
    schrF P v (f ∘ C) = rhoFun (φ v) f ∘ C := by
  funext y
  have h2 : ⟪pPart (φ v), qPart (φ v)⟫ = -P v.1 v.2 := by rw [hp, real_inner_comm, hq]
  have h3 : ⟪C v.1, qPart (φ v)⟫ = -P v.1 v.2 := by rw [real_inner_comm, hq]
  simp only [schrF, rhoFun, phase, Function.comp_apply, map_add, hp, hq, h3]
  congr 2
  push_cast
  ring

theorem dRho_coords {n : ℕ} (P : V → V → ℝ) (C : V ≃L[ℝ] EuclideanSpace ℝ (Fin n))
    (φ : (V × V) ≃ₗ[ℝ] (Fin n ⊕ Fin n → ℝ)) (hp : ∀ v, pPart (φ v) = C v.1)
    (hq : ∀ v y, ⟪qPart (φ v), C y⟫ = -P y v.2) (u : V × V) (g : 𝓢(V, ℂ)) (h : Sch (Fin n))
    (hg : ⇑g = ⇑h ∘ ⇑C) (y : V) :
    fderiv ℝ (⇑g) y u.1 - 2 * Real.pi * Complex.I * (P y u.2 : ℂ) * g y = dRho (φ u) h (C y) := by
  have hd : HasFDerivAt (⇑h ∘ ⇑C) ((fderiv ℝ (⇑h) (C y)).comp (C : V →L[ℝ] EuclideanSpace ℝ (Fin n))) y :=
    (h.hasFDerivAt (C y)).comp y C.hasFDerivAt
  rw [dRho_apply, hg, hd.fderiv, hp, hq]
  simp
  ring

theorem quad_eq_sum {l : Type} [Fintype l] [DecidableEq l] (X : Matrix (l ⊕ l) (l ⊕ l) ℝ) :
    quad X = ∑ p : (l ⊕ l) × (l ⊕ l), ((4 * Real.pi * Complex.I : ℂ)⁻¹ *
      ((((X * Matrix.J l ℝ) p.1 p.2 + (X * Matrix.J l ℝ) p.2 p.1) / 2 : ℝ) : ℂ)) •
        (dRho (Pi.single p.1 1) * dRho (Pi.single p.2 1)) := by
  rw [quad, Fintype.sum_prod_type, Finset.smul_sum]
  simp only [smul_add, Finset.sum_add_distrib, Finset.smul_sum]
  rw [Finset.sum_comm (f := fun a b => (4 * Real.pi * Complex.I : ℂ)⁻¹ • (((X * Matrix.J l ℝ) a b / 2 : ℝ) : ℂ) •
    (dRho (Pi.single b 1) * dRho (Pi.single a 1))), ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun b _ => ?_
  simp only [smul_smul]
  rw [← add_smul]
  congr 1
  push_cast
  ring

theorem haar_coords {n : ℕ} [MeasurableSpace V] [BorelSpace V] [FiniteDimensional ℝ V] (μ : Measure V) [μ.IsAddHaarMeasure]
    (C : V ≃L[ℝ] EuclideanSpace ℝ (Fin n)) :
    ∃ k : ℝ, 0 < k ∧ ∀ F : V → ℝ, ∫ y, F y ∂μ = k * ∫ x, F (C.symm x) := by
  let e : V ≃ᵐ EuclideanSpace ℝ (Fin n) := C.toHomeomorph.toMeasurableEquiv
  have he : ∀ y, e y = C y := fun y => rfl
  haveI : (μ.map e).IsAddHaarMeasure := C.isAddHaarMeasure_map μ
  have hk := Measure.isAddLeftInvariant_eq_smul (μ.map e) (volume : Measure (EuclideanSpace ℝ (Fin n)))
  refine ⟨(Measure.addHaarScalarFactor (μ.map e) volume : ℝ),
    NNReal.coe_pos.2 (Measure.addHaarScalarFactor_pos_of_isAddHaarMeasure _ _), fun F => ?_⟩
  have h1 : ∫ y, F y ∂μ = ∫ x, F (C.symm x) ∂(μ.map e) := by
    rw [integral_map_equiv]
    simp [he]
  rw [h1, congrArg (fun m => ∫ x, F (C.symm x) ∂m) hk]
  simp only [integral_smul_nnreal_measure, NNReal.smul_def, smul_eq_mul]

theorem transport : ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] (μ : Measure V), μ.IsAddHaarMeasure → ∀ (P : V → V → ℝ), IsPairing P → ∀ n : ℕ, Module.finrank ℝ V = n →
    (∀ (A' : ℝ → (Fin n ⊕ Fin n → ℝ) →ₗ[ℝ] (Fin n ⊕ Fin n → ℝ)) (T' : ℝ → Sch (Fin n) →ₗ[ℂ] Sch (Fin n)),
      (∀ w, Continuous fun t => A' t w) → (∀ s t f, T' (s + t) f = T' s (T' t f)) → (∀ f, T' 0 f = f) →
      (∀ t w (f f₁ : Sch (Fin n)), ⇑f₁ = rhoFun w ⇑f → ⇑(T' t f₁) = rhoFun (A' t w) ⇑(T' t f)) →
      (∀ t f, ∫ x, ‖T' t f x‖ ^ 2 = ∫ x, ‖f x‖ ^ 2) → (∀ f y, Continuous fun t => T' t f y) →
      ∃ (X : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ) (c : ℂ),
        ∀ f y, HasDerivAt (fun t => T' t f y) (quad X f y + c * f y) 0) →
    ∀ (A : ℝ → (V × V) →ₗ[ℝ] (V × V)) (T : ℝ → 𝓢(V, ℂ) →ₗ[ℂ] 𝓢(V, ℂ)),
    (∀ v, Continuous fun t => A t v) →
    (∀ s t f, T (s + t) f = T s (T t f)) → (∀ f, T 0 f = f) →
    (∀ t v (f f₁ : 𝓢(V, ℂ)), ⇑f₁ = schrF P v ⇑f → ⇑(T t f₁) = schrF P (A t v) ⇑(T t f)) →
    (∀ t f, ∫ x, ‖T t f x‖ ^ 2 ∂μ = ∫ x, ‖f x‖ ^ 2 ∂μ) →
    (∀ f y, Continuous fun t => T t f y) →
    ∃ (m : ℕ) (a b : Fin m → V × V) (c : Fin m → ℂ) (c₀ : ℂ), ∀ (f : 𝓢(V, ℂ)) (g₁ g₂ : Fin m → 𝓢(V, ℂ)),
      (∀ i y, g₁ i y = fderiv ℝ (⇑f) y (b i).1 - 2 * Real.pi * Complex.I * (P y (b i).2 : ℂ) * f y) →
      (∀ i y, g₂ i y = fderiv ℝ (⇑(g₁ i)) y (a i).1 - 2 * Real.pi * Complex.I * (P y (a i).2 : ℂ) * g₁ i y) →
      ∀ y, HasDerivAt (fun t => T t f y) (∑ i, c i * g₂ i y + c₀ * f y) 0 := by
  intro V _ _ _ _ _ μ hμ P hP n hn H A T hAc hTadd hT0 hTi hTl2 hTc
  obtain ⟨C, φ, hp, hq⟩ := coords P hP n hn
  have hS := schr_coords P C φ hp hq
  let toE : 𝓢(V, ℂ) →L[ℂ] Sch (Fin n) := SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (F := ℂ) C.symm
  let toV : Sch (Fin n) →L[ℂ] 𝓢(V, ℂ) := SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (F := ℂ) C
  have htoE : ∀ g, ⇑(toE g) = ⇑g ∘ ⇑C.symm := fun g => rfl
  have htoV : ∀ h, ⇑(toV h) = ⇑h ∘ ⇑C := fun h => rfl
  have hVE : ∀ g, toV (toE g) = g := fun g => by ext x; simp [htoE, htoV]
  have hEV : ∀ h, toE (toV h) = h := fun h => by ext x; simp [htoE, htoV]
  let T' : ℝ → Sch (Fin n) →ₗ[ℂ] Sch (Fin n) := fun t => toE.toLinearMap ∘ₗ T t ∘ₗ toV.toLinearMap
  let A' : ℝ → (Fin n ⊕ Fin n → ℝ) →ₗ[ℝ] (Fin n ⊕ Fin n → ℝ) :=
    fun t => φ.toLinearMap ∘ₗ A t ∘ₗ φ.symm.toLinearMap
  have hT' : ∀ t h, T' t h = toE (T t (toV h)) := fun t h => rfl
  obtain ⟨k, hk, hint⟩ := haar_coords μ C
  have c1 : ∀ w, Continuous fun t => A' t w := by
    intro w
    exact (φ.toLinearMap.continuous_of_finiteDimensional).comp (hAc (φ.symm w))
  have c2 : ∀ s t f, T' (s + t) f = T' s (T' t f) := by
    intro s t h
    simp only [hT', hVE, hTadd]
  have c3 : ∀ f, T' 0 f = f := by
    intro h
    simp [hT', hT0, hEV]
  have c4 : ∀ t w (f f₁ : Sch (Fin n)), ⇑f₁ = rhoFun w ⇑f → ⇑(T' t f₁) = rhoFun (A' t w) ⇑(T' t f) := by
    intro t w f f₁ hf
    have e1 : ⇑(toV f₁) = schrF P (φ.symm w) ⇑(toV f) := by
      funext x
      have := congrFun (hS (φ.symm w) ⇑f) x
      simp only [Function.comp_apply, LinearEquiv.apply_symm_apply] at this
      simp only [htoV, Function.comp_apply, hf]
      exact this.symm
    have e2 := hTi t _ _ _ e1
    rw [hT' t f₁, hT' t f, htoE, htoE, e2]
    obtain ⟨G, hG⟩ : ∃ G : EuclideanSpace ℝ (Fin n) → ℂ, ⇑(T t (toV f)) = G ∘ ⇑C :=
      ⟨⇑(T t (toV f)) ∘ ⇑C.symm, by ext x; simp⟩
    have hGC : (G ∘ ⇑C) ∘ ⇑C.symm = G := by funext x; simp
    rw [hG, hS, hGC]
    funext x
    simp [A']
  have c5 : ∀ t f, ∫ x, ‖T' t f x‖ ^ 2 = ∫ x, ‖f x‖ ^ 2 := by
    intro t h
    have e := hTl2 t (toV h)
    rw [hint, hint] at e
    simp only [htoV, Function.comp_apply, ContinuousLinearEquiv.apply_symm_apply] at e
    exact mul_left_cancel₀ hk.ne' e
  have c6 : ∀ f y, Continuous fun t => T' t f y := by
    intro h y
    exact hTc (toV h) (C.symm y)
  obtain ⟨X, c, hX⟩ := H A' T' c1 c2 c3 c4 c5 c6
  let eq := (Fintype.equivFin ((Fin n ⊕ Fin n) × (Fin n ⊕ Fin n))).symm
  let S := X * Matrix.J (Fin n) ℝ
  refine ⟨Fintype.card ((Fin n ⊕ Fin n) × (Fin n ⊕ Fin n)), fun i => φ.symm (Pi.single (eq i).1 1),
    fun i => φ.symm (Pi.single (eq i).2 1),
    fun i => (4 * Real.pi * Complex.I : ℂ)⁻¹ * (((S (eq i).1 (eq i).2 + S (eq i).2 (eq i).1) / 2 : ℝ) : ℂ), c, ?_⟩
  intro f g₁ g₂ hg₁ hg₂ y
  have hf : ⇑f = ⇑(toE f) ∘ ⇑C := by ext x; simp [htoE]
  have h1 : ∀ i, ⇑(g₁ i) = ⇑(dRho (Pi.single (eq i).2 1) (toE f)) ∘ ⇑C := fun i => by
    ext x
    rw [hg₁, dRho_coords P C φ hp hq _ f (toE f) hf, LinearEquiv.apply_symm_apply]
    rfl
  have h2 : ∀ i, g₂ i y = dRho (Pi.single (eq i).1 1) (dRho (Pi.single (eq i).2 1) (toE f)) (C y) := fun i => by
    rw [hg₂, dRho_coords P C φ hp hq _ (g₁ i) _ (h1 i), LinearEquiv.apply_symm_apply]
  have hd := hX (toE f) (C y)
  have e1 : (fun t => T' t (toE f) (C y)) = fun t => T t f y := by
    funext t
    simp [hT', htoE, hVE]
  rw [e1] at hd
  convert hd using 1
  have e2 : toE f (C y) = f y := by simp [htoE]
  rw [e2, quad_eq_sum]
  congr 1
  simp only [h2, ContinuousLinearMap.coe_sum', Finset.sum_apply, SchwartzMap.sum_apply,
    ContinuousLinearMap.coe_smul', Pi.smul_apply, SchwartzMap.smul_apply, ContinuousLinearMap.mul_apply, smul_eq_mul]
  exact Equiv.sum_comp eq (fun p => (4 * Real.pi * Complex.I : ℂ)⁻¹ * (((S p.1 p.2 + S p.2 p.1) / 2 : ℝ) : ℂ) *
    dRho (Pi.single p.1 1) (dRho (Pi.single p.2 1) (toE f)) (C y))

end GlobalTheory.ArchUniq.SchrTransport
