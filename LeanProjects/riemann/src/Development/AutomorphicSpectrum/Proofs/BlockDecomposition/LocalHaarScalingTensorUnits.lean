import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OfE
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.FactorConjugationCancel

noncomputable section

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology Filter PositivityTheory.Rg.Base1 GroundTheory.Global GlobalTheory.CompanionTheory.SW.RankOneSiegelWeil
open scoped TensorProduct ENNReal NNReal Matrix Classical

namespace GlobalTheory.CompanionTheory.SW.RankOneSiegelWeil.UnitScale

open GlobalTheory.CompanionTheory.SW.WBox (cK eW)

theorem map_eq_of_conj {G : Type} [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G]
    [LocallyCompactSpace G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
    (m s : G ≃ₜ+ G) (ν : Measure G) [ν.IsAddHaarMeasure] (c : ℝ≥0) (hs : ∀ x, s (s x) = x)
    (h : ν.map (fun x => s (m (s (m x)))) = (c * c) • ν) : ν.map m = c • ν :=
  _root_.UpperTheory.Reformulated.B.FactorConjugationCancel.map_eq_of_conj m s ν c hs h

section Coord

variable {F E : Type} [Field F] [Field E] [Algebra F E] {R : Type} [CommRing R] [Algebra F R] {d : ℕ}
  (b : Module.Basis (Fin d) F E)

theorem cK_tmul_mul' (r : R) (y : R ⊗[F] E) (k : Fin d) :
    cK R b ((r ⊗ₜ[F] (1 : E)) * y) k = r * cK R b y k := by
  have e : (r ⊗ₜ[F] (1 : E)) * y = r • y := by
    rw [Algebra.smul_def]
    rfl
  simp [cK, e]

end Coord

theorem pi_map_mul {R ι : Type} [Fintype ι] [CommRing R] [MeasurableSpace R] (lam : Measure R) [SigmaFinite lam]
    (f : R → R) (hf : Measurable f) (c : ℝ≥0) (h : lam.map f = c • lam) :
    (Measure.pi fun _ : ι => lam).map (fun t i => f (t i)) =
      (c ^ Fintype.card ι) • Measure.pi fun _ : ι => lam := by
  haveI : SigmaFinite (lam.map f) := by rw [h]; infer_instance
  rw [Measure.pi_map_pi (fun _ => hf.aemeasurable)]
  refine Measure.pi_eq fun s hs => ?_
  simp only [h, Measure.smul_apply, Measure.pi_pi, ENNReal.smul_def, smul_eq_mul,
    Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, ENNReal.coe_pow]

theorem sigR_sigR {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R]
    (σ : E →ₐ[F] E) (hσ : ∀ x, σ (σ x) = x) (z : R ⊗[F] E) : sigR R σ (sigR R σ z) = z := by
  induction z with
  | zero => simp
  | add x y hx hy => simp [hx, hy]
  | tmul r e => simp [sigR, hσ]

theorem conj_conj {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (hcm : IsCMExt F E σ) (x : E) : σ (σ x) = x := by
  obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
  apply τ.injective
  rw [hcm.2.2.2, hcm.2.2.2]
  simp

def mulT {S : Type} [CommRing S] [TopologicalSpace S] [IsTopologicalRing S] (u : Sˣ) :
    (Fin 1 → Fin 1 → S) ≃ₜ+ (Fin 1 → Fin 1 → S) where
  toFun X a i := (u : S) * X a i
  invFun X a i := ((u⁻¹ : Sˣ) : S) * X a i
  left_inv X := by
    funext a i
    exact Units.inv_mul_cancel_left u _
  right_inv X := by
    funext a i
    exact Units.mul_inv_cancel_left u _
  map_add' X Y := by
    funext a i
    exact mul_add _ _ _
  continuous_toFun := continuous_pi fun a => continuous_pi fun i =>
    continuous_const.mul (continuous_apply_apply a i)
  continuous_invFun := continuous_pi fun a => continuous_pi fun i =>
    continuous_const.mul (continuous_apply_apply a i)

def sigT {S : Type} [CommRing S] [TopologicalSpace S] [IsTopologicalRing S] (f : S →+* S) (hf : Continuous f)
    (hff : ∀ x, f (f x) = x) : (Fin 1 → Fin 1 → S) ≃ₜ+ (Fin 1 → Fin 1 → S) where
  toFun X a i := f (X a i)
  invFun X a i := f (X a i)
  left_inv X := by
    funext a i
    exact hff _
  right_inv X := by
    funext a i
    exact hff _
  map_add' X Y := by
    funext a i
    exact map_add f _ _
  continuous_toFun := continuous_pi fun a => continuous_pi fun i =>
    hf.comp (continuous_apply_apply a i)
  continuous_invFun := continuous_pi fun a => continuous_pi fun i =>
    hf.comp (continuous_apply_apply a i)

theorem map_coordW_unit : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [IsTopologicalRing R] [LocallyCompactSpace R] [SecondCountableTopology R] [T2Space R] [MeasurableSpace R] [BorelSpace R], IsLocR R → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (lam : Measure R), lam.IsAddHaarMeasure → ∀ (y : (R ⊗[F] E)ˣ) (n : Rˣ) (c : ℝ≥0), (n : R) ⊗ₜ[F] (1 : E) = sigR R σ y * y → lam.map (fun t => (n : R) * t) = c • lam → (coordW R b lam 1 1).map (fun (X : Fin 1 → Fin 1 → R ⊗[F] E) a i => (y : R ⊗[F] E) * X a i) = c • coordW R b lam 1 1 := by
  intro F E _ _ _ _ _ σ hcm R _ _ _ _ _ _ _ _ _ hR d b lam hlam y n c hn hc
  have hd : d = 2 := by
    have := Module.finrank_eq_card_basis b
    rw [hcm.2.2.1] at this
    simpa using this.symm
  subst hd
  obtain ⟨iTR, iLC, iSC, iT2, hsc, -, hK', hB, -⟩ := GlobalTheory.T.tensor_locally_compact_ring F E σ hcm R
  haveI := iTR
  haveI := iLC
  haveI := iSC
  haveI := iT2
  haveI := hB 1 1
  haveI := hlam
  have hK : IsHomeomorph (cK (F := F) (E := E) R b) := hK' 2 b
  haveI hν : (coordW R b lam 1 1).IsAddHaarMeasure :=
    (GlobalTheory.T.coordinate_haar_measure F E σ hcm R 2 b lam hlam).2.1 1 1
  have hinv := sigR_sigR R σ (conj_conj σ hcm)
  set π : Measure (Fin 1 × Fin 1 × Fin 2 → R) := Measure.pi fun _ => lam with hπ
  have hmp := GlobalTheory.CompanionTheory.SW.WBox.map_coordW R hK lam 1 1
  have hf : Measurable (fun t : R => (n : R) * t) := (continuous_const.mul continuous_id).measurable
  have hTm : Measurable (fun (t : Fin 1 × Fin 1 × Fin 2 → R) i => (n : R) * t i) :=
    measurable_pi_lambda _ fun i => hf.comp (measurable_pi_apply i)
  have hT : π.map (fun t i => (n : R) * t i) = (c * c) • π := by
    have h1 := pi_map_mul (ι := Fin 1 × Fin 1 × Fin 2) lam _ hf c hc
    have e : c ^ Fintype.card (Fin 1 × Fin 1 × Fin 2) = c * c := by
      simp [pow_two]
    rw [e] at h1
    exact h1
  have hνπ : coordW R b lam 1 1 = π.map (eW R hK 1 1).symm := by
    rw [hπ, ← hmp.map_eq, Measure.map_map (eW R hK 1 1).symm.measurable (eW R hK 1 1).measurable,
      MeasurableEquiv.symm_comp_self, Measure.map_id]
  have hNc : Continuous (fun (X : Fin 1 → Fin 1 → R ⊗[F] E) a i => ((n : R) ⊗ₜ[F] (1 : E)) * X a i) :=
    continuous_pi fun a => continuous_pi fun i => continuous_const.mul (continuous_apply_apply a i)
  have hNm := hNc.measurable
  have hcomm : (fun (X : Fin 1 → Fin 1 → R ⊗[F] E) a i => ((n : R) ⊗ₜ[F] (1 : E)) * X a i) ∘ (eW R hK 1 1).symm =
      (eW R hK 1 1).symm ∘ (fun t i => (n : R) * t i) := by
    funext t
    apply (eW R hK 1 1).injective
    simp only [Function.comp_apply, MeasurableEquiv.apply_symm_apply]
    funext p
    have h1 := congrFun ((eW R hK 1 1).apply_symm_apply t) p
    rw [GlobalTheory.CompanionTheory.SW.WBox.eW_apply] at h1
    rw [GlobalTheory.CompanionTheory.SW.WBox.eW_apply, cK_tmul_mul', h1]
  have hN : (coordW R b lam 1 1).map
      (fun (X : Fin 1 → Fin 1 → R ⊗[F] E) a i => ((n : R) ⊗ₜ[F] (1 : E)) * X a i) =
      (c * c) • coordW R b lam 1 1 := by
    calc _ = (π.map (eW R hK 1 1).symm).map
            (fun (X : Fin 1 → Fin 1 → R ⊗[F] E) a i => ((n : R) ⊗ₜ[F] (1 : E)) * X a i) := by rw [← hνπ]
      _ = π.map ((eW R hK 1 1).symm ∘ (fun t i => (n : R) * t i)) := by
          rw [Measure.map_map hNm (eW R hK 1 1).symm.measurable, hcomm]
      _ = (π.map (fun t i => (n : R) * t i)).map (eW R hK 1 1).symm := by
          rw [Measure.map_map (eW R hK 1 1).symm.measurable hTm]
      _ = _ := by rw [hT, Measure.map_smul, ← hνπ]
  refine map_eq_of_conj (mulT y) (sigT (sigR R σ) hsc hinv) _ c (fun X => ?_) ?_
  · funext a i
    exact hinv _
  · have e : (fun X => sigT (sigR R σ) hsc hinv (mulT y (sigT (sigR R σ) hsc hinv (mulT y X)))) =
        (fun (X : Fin 1 → Fin 1 → R ⊗[F] E) a i => ((n : R) ⊗ₜ[F] (1 : E)) * X a i) := by
      funext X a i
      change sigR R σ ((y : R ⊗[F] E) * sigR R σ ((y : R ⊗[F] E) * X a i)) = _
      rw [map_mul, hinv, hn, mul_assoc]
    rw [e, hN]

end GlobalTheory.CompanionTheory.SW.RankOneSiegelWeil.UnitScale
