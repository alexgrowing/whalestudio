import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.WhittakerGlobalFactors.MeasurableSetUH
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.ExistsStandardLocalMeasuresStatement

noncomputable section

namespace PositivityTheory.SiegelWeilFormula.GFac.HS

open HeckeCharacterZeroLocus.SiegelWeilU NumberField IsDedekindDomain MeasureTheory
open GlobalTheory.CompanionTheory.SiegelND.Coef (hermInf hermFin hermV latH intH hermMap)
open GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.HermSd
open scoped TensorProduct ENNReal NNReal Matrix

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem hermVec_map {R R' : Type} [CommRing R] [Algebra F R] [CommRing R'] [Algebra F R'] (f : R →ₐ[F] R')
    (σ : E →ₐ[F] E) {d : ℕ} (b : Module.Basis (Fin d) F E) (n : ℕ) (S : HermR R σ n) (i : Idx n d) :
    hermVec R' σ b n (hermMap f σ S) i = f (hermVec R σ b n S i) := by
  haveI : FiniteDimensional F E := Module.Finite.of_basis b
  cases i with
  | inl i =>
    simp only [hermVec, toVec, GlobalTheory.CompanionTheory.SW.HaarCoord.hermCoord, Sum.elim_inl, hermMap, Matrix.map_apply]
    rw [GlobalTheory.CompanionTheory.SiegelND.Coef.Lim.trace_map f b, map_mul, AlgHom.commutes]
    congr 1
    have h := GlobalTheory.CompanionTheory.SiegelND.Coef.Lim.trace_map (AlgHom.id F R) b ((S : Matrix (Fin n) (Fin n) (R ⊗[F] E)) i i)
    rw [Algebra.TensorProduct.map_id, AlgHom.id_apply] at h
    rw [h, map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_mul, AlgHom.commutes]
    rfl
  | inr q =>
    simp only [hermVec, toVec, GlobalTheory.CompanionTheory.SW.HaarCoord.hermCoord, Sum.elim_inr, hermMap, Matrix.map_apply]
    exact GlobalTheory.CompanionTheory.SiegelND.Coef.Lim.repr_map f b _ q.2

def hInfR (σ : E →ₐ[F] E) {n : ℕ} (S : HermR (AF F) σ n) : HermR (Ainf F) σ n := hermInf σ S

def hFinR (σ : E →ₐ[F] E) {n : ℕ} (S : HermR (AF F) σ n) : HermR (Af F) σ n := hermFin σ S

theorem sigmaFinite_of_mp {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y] (e : X ≃ᵐ Y) {μ : Measure X}
    {ν : Measure Y} [SigmaFinite ν] (h : MeasurePreserving e μ ν) : SigmaFinite μ := by
  have h2 : μ = ν.map e.symm := by
    rw [← h.map_eq, MeasurableEquiv.map_symm_map]
  rw [h2]
  exact e.symm.measurableEmbedding.sigmaFinite_map

omit [NumberField E] in

theorem coordHerm_congr {R : Type} [CommRing R] [Algebra F R] [TopologicalSpace R]
    {m₁ m₂ : MeasurableSpace R} (h : m₁ = m₂) (l₁ : @Measure R m₁) (l₂ : @Measure R m₂) (hl : ∀ s, l₁ s = l₂ s)
    (σ : E →ₐ[F] E) {d : ℕ} (b : Module.Basis (Fin d) F E) (n : ℕ) :
    @coordHerm F E _ _ _ R _ _ _ m₁ σ d b l₁ n = @coordHerm F E _ _ _ R _ _ _ m₂ σ d b l₂ n := by
  subst h
  obtain rfl : l₁ = l₂ := Measure.ext fun s _ => hl s
  rfl

section Meas
open GroundTheory.Global GroundTheory.Automorphic.GJMatrix GroundTheory.Heights₂.Theta GlobalTheory.CompanionTheory.Hypotheses₂.OneV.Fth
attribute [local instance 100000] GroundTheory.Global.measurableSpace_adeleRing GroundTheory.Global.measurableSpace_infiniteAdeleRing

theorem db_split' (σ : E →ₐ[F] E) (hCM : IsCMExt F E σ) (ψ : AddChar (AF F) ℂ) (hψ : IsCharAF F ψ) (n : ℕ)
    (db : Measure (HermR (AF F) σ n)) (hdb : SdHerm F E σ (AF F) ψ n db)
    {d : ℕ} (b : Module.Basis (Fin d) F E) (l : Measure (InfiniteAdeleRing F)) (hH : l.IsAddHaarMeasure)
    (D : Set (Ainf F)) (hD : IsAddFundamentalDomain (GlobalTheory.CompanionTheory.Hypotheses₂.OneV.DxEuler.intInf F) D l) (hD1 : l D = 1)
    (lf : Measure (Af F)) (hlf : lf.IsAddHaarMeasure) (h1 : lf {x | ∀ v, x v ∈ v.adicCompletionIntegers F} = 1) :
    MeasurePreserving (fun S : HermR (AF F) σ n => (hInfR σ S, hFinR σ S)) db
      ((coordHerm (Ainf F) σ b l n).prod (coordHerm (Af F) σ b lf n)) := by
  obtain ⟨⟨hALC, hASC, hAT2⟩, hAfLC, hAfSC, hAfT2⟩ := GlobalTheory.CompanionTheory.AdeleTop.adele_top F
  haveI : BorelSpace (Af F) := ⟨rfl⟩
  haveI : BorelSpace (HermR (AF F) σ n) := ⟨rfl⟩
  haveI : BorelSpace (HermR (Ainf F) σ n) := ⟨rfl⟩
  haveI : BorelSpace (HermR (Af F) σ n) := ⟨rfl⟩
  haveI : FiniteDimensional F E := Module.Finite.of_basis b
  obtain ⟨hinv, δ, hδ, hσδ⟩ := GlobalTheory.CompanionTheory.SW.HaarCoord.conj_facts hCM
  obtain ⟨ξ, hξ⟩ := GlobalTheory.CompanionTheory.AdeleDual.exists_eq_adelicChar_mul ψ hψ.1 hψ.2.2.1
  have hξ0 : ξ ≠ 0 := by
    rintro rfl
    obtain ⟨x, hx⟩ := hψ.2.2.2
    apply hx
    rw [hξ x]
    simp

  let e : HermR (AF F) σ n ≃ₜ (Idx n d → AF F) := (hermVec_isHomeomorph hCM (AF F) b n).homeomorph _
  have he : ∀ S, e S = hermVec (AF F) σ b n S := fun _ => rfl
  have hs : (ξ • formB σ b n).IsSymm := (formB_isSymm hinv b n).smul ξ
  have hdet : (ξ • formB σ b n).det ≠ 0 := by
    rw [Matrix.det_smul]
    exact mul_ne_zero (pow_ne_zero _ hξ0) (formB_det hinv b n)
  have hpair : ∀ S T : HermR (AF F) σ n, chiG (ξ • formB σ b n) (e S) (e T) = ψ (pairHerm (AF F) σ n S T) := by
    intro S T
    rw [he, he, pair_eq (AF F) hinv hCM.2.2.1 hδ hσδ b n S T, hξ, chiG]
    congr 2
    have h2 : (ξ • formB σ b n).map (algebraMap F (AF F)) =
        algebraMap F (AF F) ξ • (formB σ b n).map (algebraMap F (AF F)) := by
      ext p q
      exact map_mul (algebraMap F (AF F)) ξ (formB σ b n p q)
    rw [h2, Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul]
  have hsd : db.map e = adeleMeasurePi F :=
    selfDual_eq _ hs hdet _ (selfDual_transport e (fun S T => by rw [he, he, he, hermVec_add]) _ _ hpair db hdb)
  have hEq := GlobalTheory.CompanionTheory.Hypotheses₂.OneV.DxEuler.adele_eq l hH D hD hD1 lf hlf h1
  haveI : SigmaFinite l := Measure.IsAddHaarMeasure.sigmaFinite l
  haveI : SigmaFinite lf := Measure.IsAddHaarMeasure.sigmaFinite lf
  have hΘ := measurePreserving_arrowProdEquivProdArrow (InfiniteAdeleRing F) (FiniteAdeleRing (𝓞 F) F)
    (Idx n d) (fun _ => l) (fun _ => lf)
  have hA' : MeasurePreserving e.toMeasurableEquiv db (Measure.pi fun _ : Idx n d => l.prod lf) := by
    refine ⟨e.toMeasurableEquiv.measurable, ?_⟩
    change db.map e = _
    rw [hsd, adeleMeasurePi, hEq]
  let eI := ((hermVec_isHomeomorph hCM (Ainf F) b n).homeomorph _).toMeasurableEquiv
  let eF := ((hermVec_isHomeomorph hCM (Af F) b n).homeomorph _).toMeasurableEquiv
  have hI : MeasurePreserving eI (coordHerm (Ainf F) σ b l n) (Measure.pi fun _ : Idx n d => l) :=
    mp_hermVec hCM (Ainf F) b n l
  have hF : MeasurePreserving eF (coordHerm (Af F) σ b lf n) (Measure.pi fun _ : Idx n d => lf) :=
    mp_hermVec hCM (Af F) b n lf
  haveI : SigmaFinite (coordHerm (Ainf F) σ b l n) := sigmaFinite_of_mp eI hI
  haveI : SigmaFinite (coordHerm (Af F) σ b lf n) := sigmaFinite_of_mp eF hF
  let eP := eI.prodCongr eF
  have hP : MeasurePreserving eP ((coordHerm (Ainf F) σ b l n).prod (coordHerm (Af F) σ b lf n))
      ((Measure.pi fun _ : Idx n d => l).prod (Measure.pi fun _ : Idx n d => lf)) :=
    hI.prod hF
  refine (hP.comp_left_iff).1 ?_
  have hc := hΘ.comp hA'
  convert hc using 1
  funext S
  refine Prod.ext (funext fun i => ?_) (funext fun i => ?_)
  · show hermVec (Ainf F) σ b n (hermMap (fstA F) σ S) i = (hermVec (AF F) σ b n S i).1
    rw [hermVec_map]
    rfl
  · show hermVec (Af F) σ b n (hermMap (sndA F) σ S) i = (hermVec (AF F) σ b n S i).2
    rw [hermVec_map]
    rfl

end Meas

theorem db_split (σ : E →ₐ[F] E) (hCM : IsCMExt F E σ) (ψ : AddChar (AF F) ℂ) (hψ : IsCharAF F ψ) (n : ℕ)
    (db : Measure (HermR (AF F) σ n)) (hdb : SdHerm F E σ (AF F) ψ n db)
    {d : ℕ} (b : Module.Basis (Fin d) F E) (laminf : Measure (Ainf F)) (hinf : IsStdInf laminf)
    (lf : Measure (Af F)) (hlf : lf.IsAddHaarMeasure) (h1 : lf {x | ∀ v, x v ∈ v.adicCompletionIntegers F} = 1) :
    MeasurePreserving (fun S : HermR (AF F) σ n => (hInfR σ S, hFinR σ S)) db
      ((coordHerm (Ainf F) σ b laminf n).prod (coordHerm (Af F) σ b lf n)) := by
  have hm : GroundTheory.Global.measurableSpace_infiniteAdeleRing F = (measAinf : MeasurableSpace (Ainf F)) :=
    (GroundTheory.Global.borelSpace_infiniteAdeleRing F).measurable_eq
  obtain ⟨l, hl, hH, D, hD, hD1⟩ :=
    @GlobalTheory.CompanionTheory.Hypotheses₂.OneV.DxEuler.std_transfer F _ _ laminf hinf (GroundTheory.Global.measurableSpace_infiniteAdeleRing F) hm
  have h := db_split' σ hCM ψ hψ n db hdb b l hH D hD hD1 lf hlf h1
  rw [coordHerm_congr hm l laminf hl σ b n] at h
  exact h

end PositivityTheory.SiegelWeilFormula.GFac.HS

end
