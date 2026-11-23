import Development.AutomorphicArithmetic.Foundations.Convolution.GeneralizedMeasures.HeckeFinAlt
import GroundTheory.AutomorphicForms.CompactFormulaCountable

open MeasureTheory NumberField IsDedekindDomain MvPolynomial Filter
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum UpperTheory.ConvolutionTheory.C PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Geo
open GroundTheory.Global GroundTheory.Global.SemiLocal GroundTheory.Automorphic.Spherical
open UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.GM

private theorem haar_ex {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
    [MeasurableSpace G] [BorelSpace G] {K : Set G} (hc : IsCompact K) (ho : IsOpen K) (h1 : (1 : G) ∈ K) :
    ∃ m : Measure G, m.IsHaarMeasure ∧ m K = 1 := by
  let K₀ : TopologicalSpace.PositiveCompacts G := ⟨⟨K, hc⟩, by
    show (interior K).Nonempty
    rw [ho.interior_eq]; exact ⟨1, h1⟩⟩
  exact ⟨Measure.haarMeasure K₀, inferInstance, Measure.haarMeasure_self (K₀ := K₀)⟩

private theorem haar_uniq {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
    [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] {K : Set G} {m m' : Measure G}
    (hm : m.IsHaarMeasure) (hm' : m'.IsHaarMeasure) (h : m K = 1) (h' : m' K = 1) : m = m' := by
  have e := Measure.isMulLeftInvariant_eq_smul m m'
  have e2 : m K = (Measure.haarScalarFactor m m' • m') K := by rw [← e]
  rw [h, Measure.smul_apply, h', ENNReal.smul_def, smul_eq_mul, mul_one] at e2
  have e3 : Measure.haarScalarFactor m m' = 1 := by exact_mod_cast e2.symm
  rw [e3, one_smul] at e
  exact e

private theorem gl_top (R : Type*) [CommRing R] [TopologicalSpace R] [IsTopologicalRing R] [T2Space R]
    [LocallyCompactSpace R] [SecondCountableTopology R] (n : ℕ) :
    LocallyCompactSpace (GL (Fin n) R) ∧ SecondCountableTopology (GL (Fin n) R) := by
  haveI : LocallyCompactSpace (Matrix (Fin n) (Fin n) R) := inferInstanceAs (LocallyCompactSpace (Fin n → Fin n → R))
  haveI : SecondCountableTopology (Matrix (Fin n) (Fin n) R) :=
    inferInstanceAs (SecondCountableTopology (Fin n → Fin n → R))
  haveI : SecondCountableTopology (Matrix (Fin n) (Fin n) R)ᵐᵒᵖ :=
    MulOpposite.opHomeomorph.symm.isEmbedding.secondCountableTopology
  exact ⟨inferInstance, Units.isEmbedding_embedProduct.secondCountableTopology⟩

private theorem gl_int {R : Type*} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R] [T2Space R] (n : ℕ)
    (O : Subring R) (hc : IsCompact (O : Set R)) (ho : IsOpen (O : Set R)) :
    IsCompact {g : GL (Fin n) R | (∀ i j, g i j ∈ O) ∧ ∀ i j, (g⁻¹ : GL (Fin n) R) i j ∈ O} ∧
    IsOpen {g : GL (Fin n) R | (∀ i j, g i j ∈ O) ∧ ∀ i j, (g⁻¹ : GL (Fin n) R) i j ∈ O} := by
  let S : Subring (Matrix (Fin n) (Fin n) R) := (RingHom.mapMatrix O.subtype).range
  have hS : ∀ A : Matrix (Fin n) (Fin n) R, A ∈ S ↔ ∀ i j, A i j ∈ O := by
    intro A
    constructor
    · rintro ⟨B, rfl⟩ i j
      exact (B i j).2
    · intro h
      exact ⟨Matrix.of fun i j => ⟨A i j, h i j⟩, rfl⟩
  constructor
  · have e : {g : GL (Fin n) R | (∀ i j, g i j ∈ O) ∧ ∀ i j, (g⁻¹ : GL (Fin n) R) i j ∈ O} =
        (S.toSubmonoid.units : Set (GL (Fin n) R)) := by
      ext g
      rw [SetLike.mem_coe, Submonoid.mem_units_iff, Subring.mem_toSubmonoid, Subring.mem_toSubmonoid, hS, hS]
      rfl
    rw [e]
    apply Submonoid.units_isCompact
    have : (S.toSubmonoid : Set (Matrix (Fin n) (Fin n) R)) =
        Set.pi Set.univ fun _ => Set.pi Set.univ fun _ => (O : Set R) := by
      ext A
      change A ∈ S ↔ ∀ i ∈ Set.univ, ∀ j ∈ Set.univ, A i j ∈ (O : Set R)
      rw [hS]
      simp
    rw [this]
    exact isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => hc
  · simp only [Set.setOf_and, Set.setOf_forall]
    refine IsOpen.inter ?_ ?_
    · exact isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j =>
        ho.preimage (Units.continuous_val.matrix_elem i j)
    · exact isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j =>
        ho.preimage ((Units.continuous_val.matrix_elem i j).comp continuous_inv)

open ValuativeRel in
private theorem unitSet_top {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (n : ℕ) (v : Pl F) :
    IsCompact (unitSet E n v) ∧ IsOpen (unitSet E n v) ∧ (1 : GL (Fin n) (CompletionsOver E v)) ∈ unitSet E n v := by
  let O : Subring (CompletionsOver E v) :=
    ⨅ w : PlacesOver E v, (𝒪[w.1.adicCompletion E]).comap
      (Pi.evalRingHom (fun w : PlacesOver E v => w.1.adicCompletion E) w)
  have hO : (O : Set (CompletionsOver E v)) =
      Set.pi Set.univ fun w : PlacesOver E v => (𝒪[w.1.adicCompletion E] : Set (w.1.adicCompletion E)) := by
    ext x
    simp [O, Subring.mem_iInf]
  have hc : IsCompact (O : Set (CompletionsOver E v)) := by
    rw [hO]
    exact isCompact_univ_pi fun w => isCompact_iff_compactSpace.mpr (inferInstanceAs (CompactSpace 𝒪[w.1.adicCompletion E]))
  have ho : IsOpen (O : Set (CompletionsOver E v)) := by
    rw [hO]
    exact isOpen_set_pi Set.finite_univ fun w _ => Valuation.isOpen_integer
  have e : unitSet E n v = {g : GL (Fin n) (CompletionsOver E v) | (∀ i j, g i j ∈ O) ∧
      ∀ i j, (g⁻¹ : GL (Fin n) (CompletionsOver E v)) i j ∈ O} := by
    ext g
    simp only [unitSet, Set.mem_setOf_eq, GLnLocal.mem_integralGL_iff, ← map_inv, O, Subring.mem_iInf, Subring.mem_comap]
    exact ⟨fun h => ⟨fun i j w => (h w).1 i j, fun i j w => (h w).2 i j⟩,
      fun h w => ⟨fun i j => h.1 i j w, fun i j => h.2 i j w⟩⟩
  refine ⟨e ▸ (gl_int n O hc ho).1, e ▸ (gl_int n O hc ho).2, fun w => ?_⟩
  rw [map_one]
  exact one_mem _

theorem UpperTheory.ConvolutionTheory.GM.matchOne :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E ≃ₐ[F] E) (n : ℕ) (v : Pl F),
    (∃ (_ : MeasurableSpace (GL (Fin n) (CompletionsOver E v))) (_ : BorelSpace (GL (Fin n) (CompletionsOver E v)))
      (_ : MeasurableSpace (GL (Fin n) (v.adicCompletion F))) (_ : BorelSpace (GL (Fin n) (v.adicCompletion F)))
      (mE : Measure (GL (Fin n) (CompletionsOver E v))) (mF : Measure (GL (Fin n) (v.adicCompletion F))),
      mE.IsHaarMeasure ∧ mF.IsHaarMeasure ∧ mE (unitSet E n v) = 1 ∧ mF (GLnLocal.integralGL (v.adicCompletion F) n) = 1) ∧
    ∀ [MeasurableSpace (GL (Fin n) (CompletionsOver E v))] [BorelSpace (GL (Fin n) (CompletionsOver E v))]
      [MeasurableSpace (GL (Fin n) (v.adicCompletion F))] [BorelSpace (GL (Fin n) (v.adicCompletion F))]
      (mE : Measure (GL (Fin n) (CompletionsOver E v))) (mF : Measure (GL (Fin n) (v.adicCompletion F))),
      mE.IsHaarMeasure → mF.IsHaarMeasure → mE (unitSet E n v) = 1 → mF (GLnLocal.integralGL (v.adicCompletion F) n) = 1 →
      ∀ (c : ℂ) (φ : GL (Fin n) (CompletionsOver E v) → ℂ) (f : GL (Fin n) (v.adicCompletion F) → ℂ),
      Match (incFin E v) (galFin σ v) (Module.finrank F E) mE mF c φ f → MatchAt σ v c φ f := by
  intro F E _ _ _ _ _ σ n v
  obtain ⟨lE, sE⟩ := gl_top (CompletionsOver E v) n
  obtain ⟨lF, sF⟩ := gl_top (v.adicCompletion F) n
  obtain ⟨hc, ho, h1⟩ := unitSet_top (E := E) n v
  constructor
  · borelize (GL (Fin n) (CompletionsOver E v))
    borelize (GL (Fin n) (v.adicCompletion F))
    obtain ⟨mE, hE, hE1⟩ := haar_ex hc ho h1
    obtain ⟨mF, hF, hF1⟩ := haar_ex (GLnLocal.isCompact_integralGL (v.adicCompletion F) n)
      (GLnLocal.isOpen_integralGL (v.adicCompletion F) n) (one_mem _)
    exact ⟨inferInstance, inferInstance, inferInstance, inferInstance, mE, mF, hE, hF, hE1, hF1⟩
  · intro aE bE aF bF mE mF hE hF hE1 hF1 c φ f hM aE' bE' aF' bF' mE' mF' hE' hF' hE1' hF1'
    obtain rfl : aE = aE' := bE.measurable_eq.trans bE'.measurable_eq.symm
    obtain rfl : aF = aF' := bF.measurable_eq.trans bF'.measurable_eq.symm
    obtain rfl : mE = mE' := haar_uniq hE hE' hE1 hE1'
    obtain rfl : mF = mF' := haar_uniq hF hF' hF1 hF1'
    exact hM
