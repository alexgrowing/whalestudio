import Mathlib
import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.IsEulerProd
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.FiniteAdeleHaarPiRestrictedProduct
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.CompletionIsLocalRing
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.TensorLocallyCompactRing
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.AdelesLocallyCompactSecondCountable
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

noncomputable section

namespace GlobalTheory.CompanionTheory.SW.WBox

section Gen

variable {F E : Type} [Field F] [Field E] [Algebra F E]

def cK (R : Type) [CommRing R] [Algebra F R] {d : ℕ} (b : Module.Basis (Fin d) F E) (y : R ⊗[F] E)
    (k : Fin d) : R :=
  (Algebra.TensorProduct.basis R b).repr y k

theorem cK_map {R R' : Type} [CommRing R] [Algebra F R] [CommRing R'] [Algebra F R'] {d : ℕ}
    (b : Module.Basis (Fin d) F E) (f : R →ₐ[F] R') (y : R ⊗[F] E) (k : Fin d) :
    cK R' b (Algebra.TensorProduct.map f (AlgHom.id F E) y) k = f (cK R b y k) := by
  induction y with
  | zero => simp [cK]
  | add x y hx hy =>
    simp only [cK] at hx hy ⊢
    simp [map_add, hx, hy]
  | tmul r e =>
    simp [cK, Algebra.TensorProduct.basis_repr_tmul, Algebra.smul_def]

variable (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [SecondCountableTopology R]
  [MeasurableSpace R] [BorelSpace R] {d : ℕ} {b : Module.Basis (Fin d) F E}

def eK (hK : IsHomeomorph (cK (F := F) (E := E) R b)) : (R ⊗[F] E) ≃ᵐ (Fin d → R) :=
  haveI : BorelSpace (R ⊗[F] E) := ⟨rfl⟩
  (hK.homeomorph _).toMeasurableEquiv

def eW (hK : IsHomeomorph (cK (F := F) (E := E) R b)) (n M : ℕ) :
    (Fin n → Fin M → R ⊗[F] E) ≃ᵐ (Fin n × Fin M × Fin d → R) where
  toFun X p := eK R hK (X p.1 p.2.1) p.2.2
  invFun Y a i := (eK R hK).symm fun k => Y (a, i, k)
  left_inv X := by
    funext a i
    simp
  right_inv Y := by
    funext p
    simp
  measurable_toFun := measurable_pi_lambda _ fun p =>
    (measurable_pi_apply p.2.2).comp ((eK R hK).measurable.comp
      ((measurable_pi_apply p.2.1).comp (measurable_pi_apply p.1)))
  measurable_invFun := measurable_pi_lambda _ fun a => measurable_pi_lambda _ fun i =>
    (eK R hK).symm.measurable.comp (measurable_pi_lambda _ fun k => measurable_pi_apply (a, i, k))

theorem eW_apply (hK : IsHomeomorph (cK (F := F) (E := E) R b)) (n M : ℕ)
    (X : Fin n → Fin M → R ⊗[F] E) (p : Fin n × Fin M × Fin d) :
    eW R hK n M X p = cK R b (X p.1 p.2.1) p.2.2 := rfl

theorem coordK_eq (hK : IsHomeomorph (cK (F := F) (E := E) R b)) (lam : Measure R) :
    coordK R b lam = (Measure.pi fun _ : Fin d => lam).map (eK R hK).symm := by
  rw [MeasurableEquiv.map_symm]
  rfl

theorem sigmaFinite_coordK (hK : IsHomeomorph (cK (F := F) (E := E) R b)) (lam : Measure R)
    [SigmaFinite lam] : SigmaFinite (coordK R b lam) := by
  rw [coordK_eq R hK lam]
  exact (eK R hK).symm.measurableEmbedding.sigmaFinite_map

theorem map_coordW (hK : IsHomeomorph (cK (F := F) (E := E) R b)) (lam : Measure R) [SigmaFinite lam]
    (n M : ℕ) :
    MeasurePreserving (eW R hK n M) (coordW R b lam n M)
      (Measure.pi fun _ : Fin n × Fin M × Fin d => lam) := by
  haveI := sigmaFinite_coordK R hK lam
  refine ⟨(eW R hK n M).measurable, ?_⟩
  symm
  refine Measure.pi_eq fun s hs => ?_
  rw [Measure.map_apply (eW R hK n M).measurable (MeasurableSet.univ_pi hs)]
  have hset : (eW R hK n M) ⁻¹' Set.pi Set.univ s =
      Set.pi Set.univ fun a => Set.pi Set.univ fun i =>
        (eK R hK) ⁻¹' Set.pi Set.univ fun k => s (a, i, k) := by
    ext X
    simp only [Set.mem_preimage, Set.mem_pi, Set.mem_univ, forall_true_left]
    exact ⟨fun h a i k => h (a, i, k), fun h p => h p.1 p.2.1 p.2.2⟩
  have hK1 : ∀ t : Fin d → Set R, (∀ k, MeasurableSet (t k)) →
      coordK R b lam ((eK R hK) ⁻¹' Set.pi Set.univ t) = ∏ k, lam (t k) := by
    intro t ht
    rw [coordK_eq R hK lam, Measure.map_apply (eK R hK).symm.measurable
      ((eK R hK).measurable (MeasurableSet.univ_pi ht))]
    have : (eK R hK).symm ⁻¹' ((eK R hK) ⁻¹' Set.pi Set.univ t) = Set.pi Set.univ t := by
      ext x
      simp
    rw [this, Measure.pi_pi]
  rw [hset, coordW, Measure.pi_pi]
  simp_rw [Measure.pi_pi]
  simp_rw [hK1 _ (fun k => hs _)]
  rw [Fintype.prod_prod_type]
  refine Finset.prod_congr rfl fun a _ => ?_
  rw [Fintype.prod_prod_type]

end Gen

theorem coordW_box : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (lam : ∀ v : HeightOneSpectrum (𝓞 F), Measure (Fv F v)), (∀ v, IsStdV v (lam v)) → ∀ (lf : Measure (Af F)), lf.IsAddHaarMeasure → lf {x | ∀ v, x v ∈ v.adicCompletionIntegers F} = 1 → ∀ (n M : ℕ) (S : Finset (HeightOneSpectrum (𝓞 F))) (A : ∀ v : HeightOneSpectrum (𝓞 F), Set (Fin n → Fin M → Fv F v ⊗[F] E)), (∀ v, MeasurableSet (A v)) → coordW (Af F) b lf n M {X | (∀ v ∈ S, projV v X ∈ A v) ∧ ∀ v, v ∉ S → projV v X ∈ latV b v} = ∏ v ∈ S, coordW (Fv F v) b (lam v) n M (A v) := by
  intro F E _ _ _ _ _ σ hσ d b lam hlam lf hlf h1 n M S A hA
  obtain ⟨-, hAfLC, hAfSC, hAfT2⟩ := GlobalTheory.CompanionTheory.AdeleTop.adele_top F
  have hloc := fun v => GlobalTheory.CompanionTheory.SW.LocFv.isLocR_Fv F v
  haveI : ∀ v, IsTopologicalRing (Fv F v) := fun v => (hloc v).1
  haveI : ∀ v, LocallyCompactSpace (Fv F v) := fun v => (hloc v).2.1
  haveI : ∀ v, SecondCountableTopology (Fv F v) := fun v => (hloc v).2.2.1
  haveI : ∀ v, T2Space (Fv F v) := fun v => (hloc v).2.2.2.1
  haveI : ∀ v, BorelSpace (Fv F v) := fun v => ⟨rfl⟩
  haveI : ∀ v, (lam v).IsAddHaarMeasure := fun v => (hlam v).1
  haveI : BorelSpace (Af F) := ⟨rfl⟩
  have hKf : IsHomeomorph (cK (F := F) (E := E) (Af F) b) :=
    (GlobalTheory.CompanionTheory.SW.TopK.topTens_props F E σ hσ (Af F)).2.2.2.2.2.2.1 d b
  have hKv : ∀ v, IsHomeomorph (cK (F := F) (E := E) (Fv F v) b) := fun v =>
    (GlobalTheory.CompanionTheory.SW.TopK.topTens_props F E σ hσ (Fv F v)).2.2.2.2.2.2.1 d b
  have mf := map_coordW (Af F) hKf lf n M
  have mv := fun v => map_coordW (Fv F v) (hKv v) (lam v) n M
  let A' : ∀ v : HeightOneSpectrum (𝓞 F), Set (Fin n × Fin M × Fin d → Fv F v) := fun v =>
    (eW (Fv F v) (hKv v) n M).symm ⁻¹' A v
  have hA' : ∀ v, MeasurableSet (A' v) := fun v => (eW (Fv F v) (hKv v) n M).symm.measurable (hA v)
  have hcomm : ∀ (v : HeightOneSpectrum (𝓞 F)) (X : Fin n → Fin M → Af F ⊗[F] E)
      (p : Fin n × Fin M × Fin d),
      evalV F v (eW (Af F) hKf n M X p) = eW (Fv F v) (hKv v) n M (projV v X) p := by
    intro v X p
    rw [eW_apply, eW_apply, projV, cK_map]
  have hset : {X : Fin n → Fin M → Af F ⊗[F] E | (∀ v ∈ S, projV v X ∈ A v) ∧
      ∀ v, v ∉ S → projV v X ∈ latV b v} =
      (eW (Af F) hKf n M) ⁻¹' {x | (∀ v ∈ S, (fun i => evalV F v (x i)) ∈ A' v) ∧
        ∀ v, v ∉ S → ∀ i, evalV F v (x i) ∈ v.adicCompletionIntegers F} := by
    ext X
    simp only [Set.mem_setOf_eq, Set.mem_preimage, hcomm]
    refine and_congr (forall₂_congr fun v _ => ?_) (forall₂_congr fun v _ => ?_)
    · simp [A']
    · exact ⟨fun h p => h p.1 p.2.1 p.2.2, fun h a i k => h (a, i, k)⟩
  rw [hset, mf.measure_preimage_equiv,
    GlobalTheory.CompanionTheory.SW.AfBox.pi_box F lam hlam lf hlf h1 (Fin n × Fin M × Fin d) S A' hA']
  exact Finset.prod_congr rfl fun v _ => (mv v).symm.measure_preimage_equiv (A v)

end GlobalTheory.CompanionTheory.SW.WBox
