import Development.AutomorphicArithmetic.Foundations.Convolution.SphericalHeckeOperators.SymSum
import Development.AutomorphicArithmetic.Foundations.Convolution.GeneralizedMeasures.LocHeckeInert
import Development.AutomorphicArithmetic.Foundations.Convolution.SphericalHeckeOperators.DeepHecke
import Development.AutomorphicArithmetic.Foundations.Convolution.SphericalHeckeOperators.PolyAlg
import Development.AutomorphicArithmetic.Foundations.Convolution.SphericalHeckeOperators.SphIndep
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.OrbitalIntegrals.BrMain

open MeasureTheory NumberField GroundTheory.Automorphic GroundTheory.Automorphic.Spherical UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.H

private theorem haar_eq {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
    [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] (m m' : Measure G) [m.IsHaarMeasure] [m'.IsHaarMeasure]
    {A : Set G} (hm : m A = 1) (hm' : m' A = 1) : m' = m := by
  have h1 := Measure.isMulLeftInvariant_eq_smul m' m
  have h2 := congrArg (fun μ : Measure G => μ A) h1
  simp only [Measure.smul_apply, hm, hm'] at h2
  have h3 : Measure.haarScalarFactor m' m = 1 := by
    simpa [ENNReal.smul_def] using h2.symm
  rw [h1, h3, one_smul]

private theorem haar_ex {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [MeasurableSpace G] [BorelSpace G] (K : Subgroup G) (hc : IsCompact (K : Set G)) (ho : IsOpen (K : Set G)) :
    ∃ m : Measure G, m.IsHaarMeasure ∧ m K = 1 := by
  let K₀ : TopologicalSpace.PositiveCompacts G := ⟨⟨K, hc⟩, by
    simpa [ho.interior_eq] using (⟨1, K.one_mem⟩ : (K : Set G).Nonempty)⟩
  exact ⟨Measure.haarMeasure K₀, inferInstance, Measure.haarMeasure_self⟩

private theorem exists_point {n : ℕ} (t : Multiset ℂ) (ht : t.card = n) (h0 : 0 ∉ t) :
    ∃ z : Fin n → ℂˣ, (Finset.univ.val.map fun j => (z j : ℂ)) = t := by
  induction t using Quotient.inductionOn with
  | h l =>
    have hl : l.length = n := ht
    subst hl
    refine ⟨fun j => Units.mk0 (l.get j) fun e => h0 (e ▸ List.get_mem l j), ?_⟩
    simp only [Units.val_mk0, Fin.univ_val_map, List.ofFn_get]
    rfl

open GroundTheory.Global GroundTheory.Global.SemiLocal UpperTheory.V.Z.Tf.Orb in
open PositivityTheory.Rg.Tf.Geo (mapGL incFin galFin) in
theorem UpperTheory.ConvolutionTheory.H.locHeckeInert :
    UpperTheory.ConvolutionTheory.GM.LocHeckeInert := by
  intro F E _ _ _ _ _ _ σ hσ hp n _ v hu hsp w t ht h0 D
  obtain ⟨w', hw'⟩ := placeUniq_holds F E hp v hsp
  have hw : ∀ x : PlacesOver E v, x = w := fun x => (hw' x).trans (hw' w).symm
  obtain ⟨i1, i2, i3, i4, s, hs, hr, h1, h2, h3⟩ := placeData_holds F E σ hσ v w hw
  letI : MeasurableSpace (GL (Fin n) (w.1.adicCompletion E)) := borel _
  haveI : BorelSpace (GL (Fin n) (w.1.adicCompletion E)) := ⟨rfl⟩
  letI mv : MeasurableSpace (GL (Fin n) (v.adicCompletion F)) := borel _
  haveI bv : BorelSpace (GL (Fin n) (v.adicCompletion F)) := ⟨rfl⟩
  haveI : CharZero (v.adicCompletion F) := algebraRat.charZero _
  obtain ⟨μE, hμE, vE⟩ := haar_ex _ (unitSB_holds (w.1.adicCompletion E) n).2.1 (unitSB_holds (w.1.adicCompletion E) n).1
  obtain ⟨μF, hμF, vF⟩ := haar_ex _ (unitSB_holds (v.adicCompletion F) n).2.1 (unitSB_holds (v.adicCompletion F) n).1
  obtain ⟨z, hz⟩ := exists_point t ht h0
  obtain ⟨a1, a2, a3, a4⟩ := polyAlg n
  obtain ⟨P, hP, hPD⟩ := a4 D
  obtain ⟨g, hg, hg', hgz, H⟩ := @deepHecke _ _ _ _ _ _ _ _ _ _ _ i1 i2 i3 i4 (h3 (hu w)) s hs n _ _ _ _ μE μF hμE hμF
    vE vF P hP z
  obtain ⟨γ, rfl⟩ := a1 g hg hg'
  refine ⟨γ, by rwa [a2, hz] at hgz, fun p hpD h f hh hf => ?_⟩
  intro _ _ mv' bv' mE mF hE hF wE wF
  have e : mv' = mv := @BorelSpace.measurable_eq _ _ mv' bv'
  subst e
  obtain ⟨hH, hPl⟩ := @placeOfLocal_holds F E _ _ _ _ _ _ σ hσ v w hw i1 i2 i3 i4 s hs hr h1 h2 n _ _ _ _ mE mF hE hF _ _
  have hc : Continuous (mapGL n (Pi.evalRingHom (fun w : PlacesOver E v => w.1.adicCompletion E) w)) :=
    Continuous.units_map _ (continuous_id.matrix_map (continuous_apply w))
  have eE := haar_eq μE (mE.map (mapGL n (Pi.evalRingHom (fun w : PlacesOver E v => w.1.adicCompletion E) w))) vE
    (by rw [Measure.map_apply hc.measurable (unitSB_holds _ n).1.measurableSet, ← placeInt_holds.2 F E v w hw n, wE])
  have eF := haar_eq μF mF vF (by rw [placeInt_holds.1 F v n, wF])
  obtain ⟨HE, hE1, hE2⟩ := sphIndep E n w.1 _ h hh μE (by rw [← placeInt_holds.1 E w.1 n, vE])
  obtain ⟨HF, hF1, hF2⟩ := sphIndep F n v _ f hf μF (by rw [← placeInt_holds.1 F v n, vF])
  have hm := H _ (hPD p hpD) HE HF (by rw [hE2, map_mul, map_mul]) (by rw [hF2, hr, ← a3, map_mul, map_mul])
  have e1 : (fun x => (HE : HeckeAlgebra μE) x) = h := funext hE1
  have e2 : (fun x => (HF : HeckeAlgebra μF) x) = f := funext hF1
  have m1 := (HE : HeckeAlgebra μE).mem
  have m2 := (HF : HeckeAlgebra μF).mem
  rw [e1, e2, ← eE, ← eF] at hm
  rw [show ((HE : HeckeAlgebra μE) : _ → ℂ) = h from e1] at m1
  rw [show ((HF : HeckeAlgebra μF) : _ → ℂ) = f from e2] at m2
  exact hPl h m1 f m2 hm
