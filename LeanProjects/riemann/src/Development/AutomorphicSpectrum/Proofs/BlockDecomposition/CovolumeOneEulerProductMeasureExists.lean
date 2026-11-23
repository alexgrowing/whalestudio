import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsCovolOne
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AdelicMeasureEulerProductDecomposition
import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.IsEulerProd
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.ExistsLocalApproximateIdentity
import GroundTheory.GlobalFields.TateThesis.AdeleMeasure

noncomputable section

namespace GlobalTheory.CompanionTheory.WeilSiegel.HypStep.CovolA

open NumberField IsDedekindDomain MeasureTheory HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.BB
open GlobalTheory.CompanionTheory.SiegelND.DxN GlobalTheory.CompanionTheory.Hypotheses₂.OneV.DxEuler
open scoped TensorProduct ENNReal NNReal

theorem cvN_ratTup {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R]
    {d M n : ℕ} (b : Module.Basis (Fin d) F E) (r : Fin n → Fin M → E) (p : Fin n × (Fin M × Fin d)) :
    cvN R b (ratTup R r : Fin n → Fin M → R ⊗[F] E) p = algebraMap F R (b.repr (r p.1 p.2.1) p.2.2) := by
  simp only [cvN, cv, ratTup, inclR]
  change (Algebra.TensorProduct.basis R b).repr ((1 : R) ⊗ₜ[F] (r p.1 p.2.1)) p.2.2 = _
  rw [Algebra.TensorProduct.basis_repr_tmul, Finsupp.smul_apply, Finsupp.mapRange_apply, one_smul]

section Meas
open GroundTheory.Global
attribute [local instance 100000] GroundTheory.Global.measurableSpace_adeleRing GroundTheory.Global.measurableSpace_infiniteAdeleRing

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem exists_covolOne (σ : E →ₐ[F] E) (hCM : IsCMExt F E σ) (n : ℕ) {d : ℕ} (b : Module.Basis (Fin d) F E) :
    ∃ (dA : Measure (Fin 1 → Fin n → AF F ⊗[F] E)) (e : (Fin 1 → Fin n → AF F ⊗[F] E) ≃ₜ (Fin 1 × (Fin n × Fin d) → AF F)),
      (∀ X, e X = cvN (AF F) b X) ∧ BorelSpace (Fin 1 → Fin n → AF F ⊗[F] E) ∧
      dA.map e = GroundTheory.Automorphic.GJMatrix.adeleMeasurePi F ∧ IsCovolOne dA := by
  obtain ⟨e, he, hB⟩ := exists_coordHomeoN σ hCM 1 n b
  obtain ⟨t1, -, -, -, -, -, -, -, -, -⟩ := GlobalTheory.CompanionTheory.SW.TopK.topTens_props F E σ hCM (AF F)
  haveI : IsTopologicalAddGroup (Fin 1 → Fin n → AF F ⊗[F] E) := inferInstance
  let eA := e.toMeasurableEquiv
  let μ := GroundTheory.Automorphic.GJMatrix.adeleMeasurePi F (ι := Fin 1 × (Fin n × Fin d))
  have hadd : ∀ x y, e (x + y) = e x + e y := by
    intro x y
    rw [he, he, he]
    funext p
    simp [cvN, cv]
  let φ : (Fin 1 → Fin n → AF F ⊗[F] E) ≃+ (Fin 1 × (Fin n × Fin d) → AF F) :=
    { e.toEquiv with map_add' := hadd }
  have hr : ∀ (r : Fin 1 → Fin n → E) p,
      e (ratTup (AF F) r) p = algebraMap F (AF F) (b.repr (r p.1 p.2.1) p.2.2) := by
    intro r p
    rw [he, cvN_ratTup]
  refine ⟨μ.map eA.symm, e, he, hB, ?_, ?_, e ⁻¹' Set.univ.pi fun _ => fundamentalSet F, ?_, ?_⟩
  · exact MeasurableEquiv.map_map_symm eA
  · exact φ.symm.isAddHaarMeasure_map μ e.symm.continuous e.continuous
  · refine IsAddFundamentalDomain.mk' (eA.measurable (MeasurableSet.univ_pi fun _ =>
      measurableSet_fundamentalSet F)).nullMeasurableSet fun x => ?_
    choose k hk huniq using fun p => existsUnique_sub_mem_fundamentalSet F (e x p)
    let r : Fin 1 → Fin n → E := fun a i => ∑ j, (-k (a, (i, j))) • b j
    have hrk : ∀ p, b.repr (r p.1 p.2.1) p.2.2 = -k p := by
      intro p
      simp only [r]
      rw [Module.Basis.repr_sum_self]
    refine ⟨⟨ratTup (AF F) r, r, rfl⟩, ?_, ?_⟩
    · change e (ratTup (AF F) r + x) ∈ Set.univ.pi fun _ => fundamentalSet F
      rw [hadd]
      intro p _
      have := hk p
      rw [Pi.add_apply, hr, hrk, map_neg, neg_add_eq_sub]
      exact this
    · rintro ⟨_, r', rfl⟩ h
      change e (ratTup (AF F) r' + x) ∈ Set.univ.pi fun _ => fundamentalSet F at h
      rw [hadd] at h
      refine Subtype.ext (e.injective (funext fun p => ?_))
      change e (ratTup (AF F) r') p = e (ratTup (AF F) r) p
      have hp := h p (Set.mem_univ p)
      rw [Pi.add_apply, hr] at hp
      have hk' : -(b.repr (r' p.1 p.2.1) p.2.2) = k p := huniq p _ (by
        change e x p - algebraMap F (AF F) (-(b.repr (r' p.1 p.2.1) p.2.2)) ∈ fundamentalSet F
        rw [map_neg, sub_neg_eq_add, add_comm]
        exact hp)
      rw [hr, hr, hrk, ← hk', neg_neg]
  · rw [MeasurableEquiv.map_apply]
    have : eA.symm ⁻¹' (e ⁻¹' Set.univ.pi fun _ => fundamentalSet F) = Set.univ.pi fun _ => fundamentalSet F := by
      ext u
      simp [eA]
    rw [this]
    change Measure.pi (fun _ => adeleMeasure F) _ = 1
    rw [Measure.pi_pi]
    simp [adeleMeasure_fundamentalSet]

theorem split_coord' (σ : E →ₐ[F] E) (hCM : IsCMExt F E σ) (M n : ℕ) (dx : Measure (Fin n → Fin M → AF F ⊗[F] E))
    {d : ℕ} (b : Module.Basis (Fin d) F E)
    (e : (Fin n → Fin M → AF F ⊗[F] E) ≃ₜ (Fin n × (Fin M × Fin d) → AF F))
    (he : ∀ X, e X = cvN (AF F) b X) (hB : BorelSpace (Fin n → Fin M → AF F ⊗[F] E))
    (hdxc : dx.map e = GroundTheory.Automorphic.GJMatrix.adeleMeasurePi F)
    (l : Measure (InfiniteAdeleRing F)) (hH : l.IsAddHaarMeasure)
    (D : Set (Ainf F)) (hD : IsAddFundamentalDomain (intInf F) D l) (hD1 : l D = 1)
    (lf : Measure (Af F)) (hlf : lf.IsAddHaarMeasure) (h1 : lf {x | ∀ v, x v ∈ v.adicCompletionIntegers F} = 1) :
    MeasurePreserving (fun X : Fin n → Fin M → AF F ⊗[F] E => (projInf X, projFin X)) dx
      ((coordW (Ainf F) b l n M).prod (coordW (Af F) b lf n M)) := by
  obtain ⟨-, hAfLC, hAfSC, hAfT2⟩ := GlobalTheory.CompanionTheory.AdeleTop.adele_top F
  haveI : BorelSpace (Af F) := ⟨rfl⟩
  have hEq := adele_eq l hH D hD hD1 lf hlf h1
  obtain ⟨i1, i3⟩ := coordMapN σ hCM (Ainf F) b l hH n M
  obtain ⟨f1, f3⟩ := coordMapN σ hCM (Af F) b lf hlf n M
  haveI hBi := (GlobalTheory.CompanionTheory.SW.TopK.topTens_props F E σ hCM (Ainf F)).2.2.2.2.2.2.2.1 n M
  haveI hBf := (GlobalTheory.CompanionTheory.SW.TopK.topTens_props F E σ hCM (Af F)).2.2.2.2.2.2.2.1 n M
  haveI : SigmaFinite l := by
    exact Measure.IsAddHaarMeasure.sigmaFinite l
  haveI : SigmaFinite lf := Measure.IsAddHaarMeasure.sigmaFinite lf
  let eI := (i1.homeomorph).toMeasurableEquiv
  let eF := (f1.homeomorph).toMeasurableEquiv
  let eA := e.toMeasurableEquiv
  have hI : MeasurePreserving eI (coordW (Ainf F) b l n M) (Measure.pi fun _ : Fin n × (Fin M × Fin d) => l) :=
    ⟨eI.measurable, i3⟩
  have hF : MeasurePreserving eF (coordW (Af F) b lf n M) (Measure.pi fun _ : Fin n × (Fin M × Fin d) => lf) :=
    ⟨eF.measurable, f3⟩
  have hΘ := measurePreserving_arrowProdEquivProdArrow (InfiniteAdeleRing F) (FiniteAdeleRing (𝓞 F) F)
    (Fin n × (Fin M × Fin d)) (fun _ => l) (fun _ => lf)
  have hA' : MeasurePreserving eA dx (Measure.pi fun _ : Fin n × (Fin M × Fin d) => l.prod lf) := by
    have e1 : GroundTheory.Automorphic.GJMatrix.adeleMeasurePi F (ι := Fin n × (Fin M × Fin d)) =
        Measure.pi fun _ : Fin n × (Fin M × Fin d) => l.prod lf := by
      rw [GroundTheory.Automorphic.GJMatrix.adeleMeasurePi, hEq]
      rfl
    exact ⟨eA.measurable, hdxc.trans e1⟩
  let eP := eI.prodCongr eF
  haveI : SFinite (coordW (Af F) b lf n M) := sfinite_coordW σ hCM b lf hlf n M
  haveI : SFinite (coordW (Ainf F) b l n M) := by
    have hK : IsHomeomorph (GlobalTheory.CompanionTheory.SW.WBox.cK (F := F) (E := E) (Ainf F) b) :=
      (GlobalTheory.CompanionTheory.SW.TopK.topTens_props F E σ hCM (Ainf F)).2.2.2.2.2.2.1 d b
    haveI := GlobalTheory.CompanionTheory.SW.WBox.sigmaFinite_coordK (Ainf F) hK l
    unfold coordW
    infer_instance
  have hP : MeasurePreserving eP ((coordW (Ainf F) b l n M).prod (coordW (Af F) b lf n M))
      ((Measure.pi fun _ : Fin n × (Fin M × Fin d) => l).prod (Measure.pi fun _ : Fin n × (Fin M × Fin d) => lf)) :=
    hI.prod hF
  refine (hP.comp_left_iff).1 ?_
  have hc := hΘ.comp hA'
  convert hc using 1
  funext X
  have hX : ∀ p, e X p = cvN (AF F) b X p := fun p => by rw [he]
  refine Prod.ext (funext fun p => ?_) (funext fun p => ?_)
  · change cvN (Ainf F) b (projInf X) p = (e X p).1
    rw [hX]
    exact GlobalTheory.CompanionTheory.SW.WBox.cK_map b (fstA F) (X p.1 p.2.1) p.2.2
  · change cvN (Af F) b (projFin X) p = (e X p).2
    rw [hX]
    exact GlobalTheory.CompanionTheory.SW.WBox.cK_map b (sndA F) (X p.1 p.2.1) p.2.2

end Meas

section Euler

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem split_coord (σ : E →ₐ[F] E) (hCM : IsCMExt F E σ) (M n : ℕ) (dx : Measure (Fin n → Fin M → AF F ⊗[F] E))
    {d : ℕ} (b : Module.Basis (Fin d) F E)
    (e : (Fin n → Fin M → AF F ⊗[F] E) ≃ₜ (Fin n × (Fin M × Fin d) → AF F))
    (he : ∀ X, e X = cvN (AF F) b X) (hB : BorelSpace (Fin n → Fin M → AF F ⊗[F] E))
    (hdxc : @Measure.map _ _ _ (@MeasurableSpace.pi _ _ fun _ => GroundTheory.Global.measurableSpace_adeleRing F) e dx =
      @GroundTheory.Automorphic.GJMatrix.adeleMeasurePi F _ _ (Fin n × (Fin M × Fin d)) _)
    (laminf : Measure (Ainf F)) (hinf : IsStdInf laminf)
    (lf : Measure (Af F)) (hlf : lf.IsAddHaarMeasure) (h1 : lf {x | ∀ v, x v ∈ v.adicCompletionIntegers F} = 1) :
    MeasurePreserving (fun X : Fin n → Fin M → AF F ⊗[F] E => (projInf X, projFin X)) dx
      ((coordW (Ainf F) b laminf n M).prod (coordW (Af F) b lf n M)) := by
  have hm : GroundTheory.Global.measurableSpace_infiniteAdeleRing F = (measAinf : MeasurableSpace (Ainf F)) :=
    (GroundTheory.Global.borelSpace_infiniteAdeleRing F).measurable_eq
  obtain ⟨l, hl, hH, D, hD, hD1⟩ := @std_transfer F _ _ laminf hinf (GroundTheory.Global.measurableSpace_infiniteAdeleRing F) hm
  have h := split_coord' σ hCM M n dx b e he hB hdxc l hH D hD hD1 lf hlf h1
  rw [coordW_congr hm l laminf hl b n M] at h
  exact h

theorem euler_coord (σ : E →ₐ[F] E) (hCM : IsCMExt F E σ) (M n : ℕ) (dx : Measure (Fin n → Fin M → AF F ⊗[F] E))
    {d : ℕ} (b : Module.Basis (Fin d) F E)
    (e : (Fin n → Fin M → AF F ⊗[F] E) ≃ₜ (Fin n × (Fin M × Fin d) → AF F))
    (he : ∀ X, e X = cvN (AF F) b X) (hB : BorelSpace (Fin n → Fin M → AF F ⊗[F] E))
    (hdxc : @Measure.map _ _ _ (@MeasurableSpace.pi _ _ fun _ => GroundTheory.Global.measurableSpace_adeleRing F) e dx =
      @GroundTheory.Automorphic.GJMatrix.adeleMeasurePi F _ _ (Fin n × (Fin M × Fin d)) _)
    (laminf : Measure (Ainf F)) (lam : ∀ v : HeightOneSpectrum (𝓞 F), Measure (Fv F v))
    (hinf : IsStdInf laminf) (hlam : ∀ v, IsStdV v (lam v)) :
    IsEulerProd b dx 1 (coordW (Ainf F) b laminf n M) (fun v => coordW (Fv F v) b (lam v) n M) := by
  obtain ⟨lf, hlf, h1⟩ := GlobalTheory.CompanionTheory.AdeleHaar.exists_haar_integral_one F
  have hmass := fun v => coordW_latV σ hCM b lam hlam n M v
  refine ⟨fun v => ?_, ?_, ∅, fun S _ φinf φ hφi hφ => ?_⟩
  · simp only [hmass v]; exact ENNReal.one_lt_top
  · simp only [hmass]; simp [summable_zero]
  · have hT := split_coord σ hCM M n dx b e he hB hdxc laminf hinf lf hlf h1
    obtain ⟨hg, hI⟩ := lint_fin σ hCM b lam hlam lf hlf h1 n M S φ hφ
    haveI := sfinite_coordW σ hCM b lf hlf n M
    set g := ({Y | ∀ v, v ∉ S → projV v Y ∈ latV b v} : Set (Fin n → Fin M → Af F ⊗[F] E)).indicator
      fun Y => ∏ v ∈ S, φ v (projV v Y) with hgdef
    have e' : ∀ X, pureL b S φinf φ X =
        (fun p : _ × _ => φinf p.1 * g p.2) (projInf X, projFin X) := by
      intro X
      by_cases hX : X ∈ intOff b S
      · have hX' : projFin X ∈ ({Y | ∀ v, v ∉ S → projV v Y ∈ latV b v} : Set (Fin n → Fin M → Af F ⊗[F] E)) := hX
        simp only [pureL, Set.indicator_of_mem hX, hgdef, Set.indicator_of_mem hX']
      · have hX' : projFin X ∉ ({Y | ∀ v, v ∉ S → projV v Y ∈ latV b v} : Set (Fin n → Fin M → Af F ⊗[F] E)) := hX
        simp only [pureL, Set.indicator_of_notMem hX, hgdef, Set.indicator_of_notMem hX', mul_zero]
    have hm : Measurable (fun p : (Fin n → Fin M → Ainf F ⊗[F] E) × (Fin n → Fin M → Af F ⊗[F] E) => φinf p.1 * g p.2) :=
      (hφi.comp measurable_fst).mul (hg.comp measurable_snd)
    rw [lintegral_congr e', hT.lintegral_comp hm, lintegral_prod_mul hφi.aemeasurable hg.aemeasurable, hI]
    simp [hmass]

end Euler

end GlobalTheory.CompanionTheory.WeilSiegel.HypStep.CovolA

end

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
open GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WeilSiegel.Free GlobalTheory.CompanionTheory.WeilSiegel.HypStep

theorem GlobalTheory.CompanionTheory.WeilSiegel.HypStep.CovolA.exists_dA : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n d : ℕ) (b : Module.Basis (Fin d) F E) (laminf : Measure (Ainf F)) (lam : ∀ v : HeightOneSpectrum (𝓞 F), Measure (Fv F v)), IsStdInf laminf → (∀ v, IsStdV v (lam v)) → ∃ dA : Measure (Fin 1 → Fin n → AF F ⊗[F] E), IsCovolOne dA ∧ IsEulerProd b dA 1 (coordW (Ainf F) b laminf 1 n) (fun v => coordW (Fv F v) b (lam v) 1 n) := by
  intro F E _ _ _ _ _ σ hCM n d b laminf lam hinf hlam
  obtain ⟨dA, e, he, hB, hm, hc⟩ := GlobalTheory.CompanionTheory.WeilSiegel.HypStep.CovolA.exists_covolOne σ hCM n b
  exact ⟨dA, hc, GlobalTheory.CompanionTheory.WeilSiegel.HypStep.CovolA.euler_coord σ hCM n 1 dA b e he hB hm laminf lam hinf hlam⟩
