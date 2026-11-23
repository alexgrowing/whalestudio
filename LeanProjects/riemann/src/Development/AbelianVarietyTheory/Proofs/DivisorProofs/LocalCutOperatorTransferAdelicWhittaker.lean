import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KerInfMemLocSpan
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
import GroundTheory.AutomorphicForms.MultiplicityOne.Injective
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SelfMemCell
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemSupportComp
open NumberField IsDedekindDomain GlobalTheory.CuspRep Formalism.UG GlobalTheory.LFun Matrix MeasureTheory

noncomputable section

namespace GlobalTheory.JSW.CutTransfer

variable {E : Type} [Field E] [NumberField E] {n : ℕ}

theorem proj_finGL_locGL (w : HeightOneSpectrum (𝓞 E)) (g : GL (Fin n) (w.adicCompletion E)) :
    GeneralLinearGroup.map ((pLoc E w).comp (pFin E)) (finGL E n (locGL E n w g)) = g := by
  refine Units.ext (Matrix.ext fun i j => ?_)
  have h1 := congrArg (fun z => (GeneralLinearGroup.map (pLoc E w) z).val i j) (pFin_finGL (E := E) (locGL E n w g))
  simp only [pLoc_locGL] at h1
  exact h1

theorem gl_ext_pLoc {x y : GL (Fin n) (Af E)}
    (h : ∀ v, GeneralLinearGroup.map (pLoc E v) x = GeneralLinearGroup.map (pLoc E v) y) : x = y :=
  Units.ext (Matrix.ext fun i k => IsDedekindDomain.FiniteAdeleRing.ext _ fun v =>
    congrArg (fun x : GL (Fin n) (v.adicCompletion E) => x.val i k) (h v))

variable [IsTotallyComplex E]

theorem comm_of_proj_eq_one (w : HeightOneSpectrum (𝓞 E)) {x : GA E n}
    (hx : GeneralLinearGroup.map ((pLoc E w).comp (pFin E)) x = 1) (g : GL (Fin n) (w.adicCompletion E)) :
    x * finGL E n (locGL E n w g) = finGL E n (locGL E n w g) * x := by
  have hxw : GeneralLinearGroup.map (pLoc E w) (GeneralLinearGroup.map (pFin E) x) = 1 := by
    refine Units.ext (Matrix.ext fun i j => ?_)
    exact congrArg (fun z : GL (Fin n) (w.adicCompletion E) => z.val i j) hx
  refine ga_ext ?_ ?_
  · simp only [map_mul, pInf_finGL, mul_one, one_mul]
  · simp only [map_mul, pFin_finGL]
    refine gl_ext_pLoc fun v => ?_
    simp only [map_mul]
    by_cases hv : v = w
    · subst hv
      rw [hxw, one_mul, mul_one]
    · rw [pLoc_locGL_of_ne hv, one_mul, mul_one]

theorem superDiag_finGL_locGL (w : HeightOneSpectrum (𝓞 E)) (u : GL (Fin n) (w.adicCompletion E)) :
    GlobalTheory.Whittaker.superDiag (finGL E n (locGL E n w u)) = sFin E (sLoc E w (GlobalTheory.Whittaker.superDiag u)) := by
  unfold GlobalTheory.Whittaker.superDiag
  rw [map_sum, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_sum, map_sum]
  refine Finset.sum_congr rfl fun j hj => ?_
  have hij : i ≠ j := by
    intro h
    subst h
    simp at hj
  change (1 : Matrix (Fin n) (Fin n) (Ad E)) i j - sFin E ((1 : Matrix (Fin n) (Fin n) (Af E)) i j) +
    sFin E ((1 : Matrix (Fin n) (Fin n) (Af E)) i j - sLoc E w ((1 : Matrix (Fin n) (Fin n) (w.adicCompletion E)) i j) +
      sLoc E w ((u : Matrix (Fin n) (Fin n) (w.adicCompletion E)) i j)) = _
  simp [Matrix.one_apply_ne hij]

theorem psiN_finGL_locGL (w : HeightOneSpectrum (𝓞 E)) (u : GL (Fin n) (w.adicCompletion E)) :
    psiN (finGL E n (locGL E n w u)) = psiLoc w (GlobalTheory.Whittaker.superDiag u) := by
  unfold psiN psiLoc
  rw [superDiag_finGL_locGL]

theorem finGL_locGL_mem_NA' (w : HeightOneSpectrum (𝓞 E)) {u : GL (Fin n) (w.adicCompletion E)}
    (hu : u ∈ GlobalTheory.SmGL.unipB (w.adicCompletion E) (Fin n)) : finGL E n (locGL E n w u) ∈ NA E n := by
  obtain ⟨h1, h2⟩ := (GlobalTheory.SmGL.mem_unipB _).1 hu
  refine ⟨fun i j hij => ?_, fun i => ?_⟩
  · change (1 : Matrix (Fin n) (Fin n) (Ad E)) i j - sFin E ((1 : Matrix (Fin n) (Fin n) (Af E)) i j) +
      sFin E ((1 : Matrix (Fin n) (Fin n) (Af E)) i j - sLoc E w ((1 : Matrix (Fin n) (Fin n) (w.adicCompletion E)) i j) +
        sLoc E w ((u : Matrix (Fin n) (Fin n) (w.adicCompletion E)) i j)) = 0
    simp [Matrix.one_apply_ne hij.ne', h1 i j hij]
  · change (1 : Matrix (Fin n) (Fin n) (Ad E)) i i - sFin E ((1 : Matrix (Fin n) (Fin n) (Af E)) i i) +
      sFin E ((1 : Matrix (Fin n) (Fin n) (Af E)) i i - sLoc E w ((1 : Matrix (Fin n) (Fin n) (w.adicCompletion E)) i i) +
        sLoc E w ((u : Matrix (Fin n) (Fin n) (w.adicCompletion E)) i i)) = 1
    simp [h2 i]

end GlobalTheory.JSW.CutTransfer

namespace GlobalTheory.JSW.CutTransfer

theorem transfer : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (m : ℕ) (w : HeightOneSpectrum (𝓞 E)) (ψ : AddChar (w.adicCompletion E) ℂ), (∀ x, ψ x = GlobalTheory.JSW.psiLoc w x) → ∀ (K : Subgroup (GL (Fin (m + 1)) (Af E))) (U : Subgroup (GL (Fin (m + 1)) (w.adicCompletion E))), (∀ u ∈ U, locGL E (m + 1) w u ∈ K) → ∀ X A : Set (GL (Fin (m + 1)) (w.adicCompletion E)), GlobalTheory.JSW.Cut.Cuts ψ (U : Set (GL (Fin (m + 1)) (w.adicCompletion E))) X A → ∃ T : GA E (m + 1) →₀ ℂ, (∀ k ∈ T.support, ∃ g, k = finGL E (m + 1) (locGL E (m + 1) w g)) ∧ ∀ W : GA E (m + 1) → ℂ, (∀ u ∈ GlobalTheory.JSW.NA E (m + 1), ∀ g, W (u * g) = GlobalTheory.JSW.psiN u * W g) → (∀ u ∈ K, ∀ g, W (g * finGL E (m + 1) u) = W g) → ∀ y : GA E (m + 1), GeneralLinearGroup.map ((pLoc E w).comp (pFin E)) y ∈ A → GlobalTheory.JSW.Cut.act T W y = {x : GA E (m + 1) | GeneralLinearGroup.map ((pLoc E w).comp (pFin E)) x ∈ X}.indicator W y := by
  intro E _ _ _ m w ψ hψ K U hU X A hcut
  classical
  obtain ⟨T₀, hT₀⟩ := hcut
  let Φ : GL (Fin (m + 1)) (w.adicCompletion E) →* GA E (m + 1) := (finGL E (m + 1)).comp (locGL E (m + 1) w)
  have hΦ : ∀ g, Φ g = finGL E (m + 1) (locGL E (m + 1) w g) := fun _ => rfl
  refine ⟨T₀.mapDomain Φ, ?_, ?_⟩
  · intro k hk
    obtain ⟨g, -, rfl⟩ := Finset.mem_image.1 (Finsupp.mapDomain_support hk)
    exact ⟨g, rfl⟩
  · intro W hN hK y hy
    set yw := GeneralLinearGroup.map ((pLoc E w).comp (pFin E)) y with hyw
    set x := y * (Φ yw)⁻¹ with hxdef
    have hx : GeneralLinearGroup.map ((pLoc E w).comp (pFin E)) x = 1 := by
      rw [hxdef, map_mul, map_inv, hΦ, proj_finGL_locGL, ← hyw, mul_inv_cancel]
    have hcomm : ∀ g, x * Φ g = Φ g * x := fun g => comm_of_proj_eq_one w hx g
    have hxy : ∀ g, x * Φ (yw * g) = y * Φ g := by
      intro g
      rw [map_mul, hxdef, mul_assoc, ← mul_assoc (Φ yw)⁻¹, inv_mul_cancel, one_mul]
    let f : GL (Fin (m + 1)) (w.adicCompletion E) → ℂ := fun g => W (x * Φ g)
    have hf1 : GlobalTheory.JSW.KirFin.Eqv ψ f := by
      intro u hu g
      show W (x * Φ (u * g)) = ψ (GlobalTheory.Whittaker.superDiag u) * W (x * Φ g)
      rw [map_mul, ← mul_assoc, hcomm u, mul_assoc, hΦ u, hN _ (finGL_locGL_mem_NA' w hu), psiN_finGL_locGL, hψ]
    have hf2 : ∀ u ∈ (U : Set (GL (Fin (m + 1)) (w.adicCompletion E))), ∀ g, f (g * u) = f g := by
      intro u hu g
      show W (x * Φ (g * u)) = W (x * Φ g)
      rw [map_mul, ← mul_assoc, hΦ u, hK _ (hU u hu)]
    have key := hT₀ f hf1 hf2 yw hy
    have hact : GlobalTheory.JSW.Cut.act (T₀.mapDomain Φ) W y = GlobalTheory.JSW.Cut.act T₀ f yw := by
      unfold GlobalTheory.JSW.Cut.act
      rw [Finsupp.sum_mapDomain_index (fun _ => zero_mul _) (fun _ _ _ => add_mul _ _ _)]
      refine Finset.sum_congr rfl fun k _ => ?_
      show _ * W (y * Φ k) = _ * W (x * Φ (yw * k))
      rw [hxy]
    rw [hact, key]
    by_cases h : yw ∈ X
    · have h' : y ∈ {z : GA E (m + 1) | GeneralLinearGroup.map ((pLoc E w).comp (pFin E)) z ∈ X} := h
      rw [Set.indicator_of_mem h, Set.indicator_of_mem h']
      show W (x * Φ yw) = W y
      rw [hxdef, mul_assoc, inv_mul_cancel, mul_one]
    · have h' : y ∉ {z : GA E (m + 1) | GeneralLinearGroup.map ((pLoc E w).comp (pFin E)) z ∈ X} := h
      rw [Set.indicator_of_notMem h, Set.indicator_of_notMem h']

end GlobalTheory.JSW.CutTransfer
