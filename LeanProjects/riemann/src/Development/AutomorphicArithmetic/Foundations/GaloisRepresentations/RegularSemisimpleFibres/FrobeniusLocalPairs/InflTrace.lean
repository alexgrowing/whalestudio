import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.FrobeniusLocalPairs.FrobFactsAlt
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.FrobeniusLocalPairs.MatchOfSum
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.FrobeniusLocalPairs.TraceRangeEq
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.FrobeniusLocalPairs.TwScale
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.FrobeniusLocalPairs.InflFacts
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.FrobeniusLocalPairs.FrobFacts
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.FrobeniusLocalPairs.GlobOf
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.OrbitalIntegrals.BrMain
import Development.AutomorphicArithmetic.Foundations.Convolution.GeneralizedMeasures.MatchOne
import Development.AutomorphicArithmetic.Foundations.Convolution.TraceSplitting.CoreDescOf
import Development.WeilBound.CoreStatements.AutomorphicKernels.LanglandsExhaustion.IrreducibleAdmissibleGL
import Development.WeilBound.CuspidalAdmissibility.OccursIff
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FixedEqFixedVectors

open MeasureTheory NumberField IsDedekindDomain ValuativeRel Matrix GroundTheory.Global GroundTheory.Global.SemiLocal
open PositivityTheory.Rg.Tf.Geo (incFin galFin mapGL)
open UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C Formalism.BasicNotions GlobalTheory.PRep GlobalTheory.CuspRep GlobalTheory.SmGL GlobalTheory.DZA UpperTheory.V.Published UpperTheory.CBC
open scoped Classical

namespace UpperTheory.Gal.InertialTypesAlt.L.InflationTrace

private theorem exists_trace {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : ℕ}
    [MeasurableSpace (GL (Fin n) k)] [BorelSpace (GL (Fin n) k)] (m : Measure (GL (Fin n) k)) [m.IsHaarMeasure]
    (τ : SmIrr (GL (Fin n) k)) (φ : GL (Fin n) k → ℂ) (hφ : Test φ) : ∃ z, GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets.HasTrace m τ.ρ φ z := by
  obtain ⟨l1, -, t1, -⟩ := UpperTheory.V.Z.Tf.Orb.gLTop_of k n
  have hA := (GlobalTheory.CompanionTheory.AdmDict.isAdmissible_iff τ.ρ).1 (PositivityTheory.Exh.irreducibleAdmissibleGL k n τ.V τ.ρ τ.smooth τ.irred)
  obtain ⟨A, hA1, hA2⟩ := PositivityTheory.TfC.OccursIff.exists_integralOp_of_admissible m τ.ρ hA φ hφ.1 hφ.2
  exact ⟨_, A, hA1, hA2, rfl⟩

private theorem fin_fixed {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : ℕ}
    (τ : SmIrr (GL (Fin n) k)) (U : Subgroup (GL (Fin n) k)) (ho : IsOpen (U : Set (GL (Fin n) k)))
    (hc : IsCompact (U : Set (GL (Fin n) k))) : FiniteDimensional ℂ (fixed τ.ρ U) :=
  (PositivityTheory.Exh.irreducibleAdmissibleGL k n τ.V τ.ρ τ.smooth τ.irred).2 U ho hc

private theorem twKer_keep {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V) (U : Subgroup G)
    (θ : G → G) (hθ : ∀ u ∈ U, θ u ∈ U) (I : V →ₗ[ℂ] V) (hI : ∀ g x, I (ρ g x) = ρ (θ g) (I x)) :
    ∀ x ∈ twKer ρ U 1, I x ∈ twKer ρ U 1 := by
  have h : twKer ρ U 1 ≤ (twKer ρ U 1).comap I := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨u, x, rfl⟩
    refine Submodule.subset_span ⟨⟨θ u, hθ u u.2⟩, I x, ?_⟩
    simp [hI]
  exact fun x hx => h hx

private theorem cmp_onto {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ} {v : Pl F}
    (w : PlacesOver E v) (hw : ∀ w' : PlacesOver E v, w' = w) (g : Gw n w.1) :
    ∃ y : GL (Fin n) (CompletionsOver E v), GM.cmp w y = g := by
  letI : Unique (PlacesOver E v) := ⟨⟨w⟩, hw⟩
  let e := RingEquiv.piUnique (fun w : PlacesOver E v => w.1.adicCompletion E)
  refine ⟨mapGL n (e.symm : _ →+* _) g, ?_⟩
  refine Units.ext (Matrix.ext fun i j => ?_)
  exact e.apply_symm_apply (g i j)

end UpperTheory.Gal.InertialTypesAlt.L.InflationTrace

open UpperTheory.Gal.InertialTypesAlt.L.InflationTrace

theorem UpperTheory.Gal.InertialTypesAlt.L.inflTrace :
    GlobalTheory.DZA.InflMatching → UpperTheory.Gal.InertialTypesAlt.G.VarEx → UpperTheory.Gal.InertialTypesAlt.G.VarTrace → UpperTheory.Gal.InertialTypesAlt.G.NormInt → UpperTheory.Gal.InertialTypesAlt.L.InflTrace := by
  intro hIM hVE hVT hNI F E _ _ _ _ _ _ _ _ hp n hn π P hconj hweak v w hw hunr _ _ _ _ hcm F₀ F₁ _ _ _ _ _ rk rK s sb hres τ τ' hτ hτ'
  haveI : CharZero (v.adicCompletion F) := charZero_of_injective_algebraMap (algebraMap F (v.adicCompletion F)).injective
  obtain ⟨hgen, hfr⟩ := UpperTheory.Gal.InertialTypesAlt.L.frobFacts _ _ F₀ F₁ rk rK s sb hres
  obtain ⟨hns, hdeg, hglob⟩ := UpperTheory.Gal.InertialTypesAlt.L.globOf F E hp v w hw hcm
  obtain ⟨σ, hσg, hσs⟩ := hglob s hgen
  obtain ⟨s', hs', hI⟩ := hVE F E σ hσg hp n hn P hconj v w hns
  obtain ⟨I₀, hI₀⟩ := hI τ' hτ'

  have hsg : ∀ g : Gw n w.1, s' g = GlobalTheory.LBC.galAct s n g := by
    intro g
    obtain ⟨y, rfl⟩ := cmp_onto w hw g
    have e := hs' y
    change (s' : Gw n w.1 →* Gw n w.1) (GM.cmp w y) = _
    rw [← e]
    refine Units.ext (Matrix.ext fun i j => ?_)
    exact hσs (y i j)

  obtain ⟨a, ha, hTw⟩ := UpperTheory.Gal.InertialTypesAlt.L.twScale _ _ s hgen n τ'.V τ'.ρ τ'.smooth τ'.irred I₀
    (fun g x => by rw [hI₀, hsg])
  let I₂ : τ'.V ≃ₗ[ℂ] τ'.V := I₀.trans (LinearEquiv.smulOfNeZero ℂ τ'.V a ha)
  have hI₂c : (I₂ : τ'.V →ₗ[ℂ] τ'.V) = a • (I₀ : τ'.V →ₗ[ℂ] τ'.V) := rfl
  have hI₂ : ∀ g x, I₂ (τ'.ρ g x) = τ'.ρ (s' g) (I₂ x) := fun g x => by
    change a • I₀ (τ'.ρ g x) = τ'.ρ (s' g) (a • I₀ x)
    rw [hI₀, map_smul]

  obtain ⟨i1, i2, i3, i4, mE, mF, hE, hF, h1, h2⟩ := (UpperTheory.ConvolutionTheory.GM.matchOne F E σ n v).1
  letI : MeasurableSpace (GL (Fin n) (w.1.adicCompletion E)) := borel _
  haveI : BorelSpace (GL (Fin n) (w.1.adicCompletion E)) := ⟨rfl⟩
  obtain ⟨hH, hP⟩ := @UpperTheory.V.Z.Tf.Orb.placeOfLocal_holds F E _ _ _ _ _ _ σ hσg v w hw _ _ _ _ s hgen hdeg hcm hσs n _ _ _ _ mE mF hE hF _ _
  have hUS := UpperTheory.V.Z.Tf.Orb.unitSB_holds
  have hPI := UpperTheory.V.Z.Tf.Orb.placeInt_holds
  have hcmp : Continuous (mapGL n (Pi.evalRingHom (fun w : PlacesOver E v => w.1.adicCompletion E) w)) :=
    Continuous.units_map _ (continuous_id.matrix_map (continuous_apply w))
  have hE1 : (mE.map (mapGL n (Pi.evalRingHom (fun w : PlacesOver E v => w.1.adicCompletion E) w)))
      (PositivityTheory.Rg.Tf.Loc.unitGL (n := Fin n) (w.1.adicCompletion E) : Set (GL (Fin n) (w.1.adicCompletion E))) = 1 := by
    rw [Measure.map_apply hcmp.measurable (hUS _ n).1.measurableSet, ← hPI.2 F E v w hw n, h1]
  have hF1 : mF (PositivityTheory.Rg.Tf.Loc.unitGL (n := Fin n) (v.adicCompletion F) : Set (GL (Fin n) (v.adicCompletion F))) = 1 := by
    rw [hPI.1 F v n, h2]
  obtain ⟨c, hc, hcT⟩ := hVT F E σ hσg hp n hn π P hconj hweak v w hns mF _ hF hH τ τ' hτ hτ' (s' : Gw n w.1 →* Gw n w.1) I₂ hs' hI₂
  refine ⟨(I₂ : τ'.V →ₗ[ℂ] τ'.V), c, by rw [hI₂c]; exact hTw, hc, fun fb hfb => ?_⟩
  obtain ⟨hKk, hUko, hUkc, hUkle, -, hfk⟩ := UpperTheory.Gal.InertialTypesAlt.L.inflFacts _ F₀ rk hres.onto₀ n
  obtain ⟨hKK, hUKo, hUKc, hUKle, -, hfK⟩ := UpperTheory.Gal.InertialTypesAlt.L.inflFacts _ F₁ rK hres.onto₁ n
  obtain ⟨hHk, hTk, hSk⟩ := hfk fb
  obtain ⟨hHK, hTK, -⟩ := hfK (normLift sb fb)
  obtain ⟨hst1, -, -⟩ := hfr n
  have hstab : ∀ u ∈ K1 rK n, GlobalTheory.LBC.galAct s n u ∈ K1 rK n := fun u hu => by
    have : GlobalTheory.LBC.galAct s n u ∈ (K1 rK n).map (GlobalTheory.LBC.galAct s n) := Subgroup.mem_map_of_mem _ hu
    rwa [hst1] at this
  obtain ⟨hm1, hm2⟩ := hIM _ _ (UpperTheory.V.Z.Tf.Orb.extCont_of _ _).1 inferInstance F₀ F₁ hres.deg rk rK hres.onto₀ hres.onto₁
    hres.inc s sb hres.gal hres.frob n fb hfb
  rw [hKk, hKK] at hm1
  rw [hKk] at hm2
  have hM := UpperTheory.Gal.InertialTypesAlt.L.matchOfSum _ _ s hgen n _ mF hH hF hE1 hF1 (K1 rK n) (K1 rk n) _ _
    ⟨hUKo, hKK ▸ hUKle, hstab⟩ ⟨hUko, hKk ▸ hUkle, fun _ h => h⟩ hHK hHk hm1 hm2
  have hMA : GM.MatchAt σ v 1 (fun g => infl rK (normLift sb fb) (GM.cmp w g)) (infl rk fb) :=
    @(UpperTheory.ConvolutionTheory.GM.matchOne F E σ n v).2 i1 i2 i3 i4 mE mF hE hF h1 h2 _ _ _ (hP _ hTK _ hTk hM)
  have hsupp : ∀ g, infl rk fb g ≠ 0 → g ∈ UpperTheory.Gal.InertialTypesAlt.G.normSet E n v := fun g hg =>
    hNI F E σ hσg hp n hn v hunr g (by
      have h3 : g ∈ (PositivityTheory.Rg.Tf.Loc.unitGL (n := Fin n) (v.adicCompletion F) : Set (GL (Fin n) (v.adicCompletion F))) := by
        have := hSk g hg
        rwa [hKk] at this
      rw [hPI.1 F v n] at h3
      exact h3)
  obtain ⟨z, hz⟩ := exists_trace mF τ _ hTk
  obtain ⟨B, hB, hBt⟩ := hcT _ _ 1 z hTK hTk hMA hsupp hz
  obtain ⟨A, hA, hAt⟩ := hz
  obtain ⟨l1, s1, t1, -⟩ := UpperTheory.V.Z.Tf.Orb.gLTop_of (v.adicCompletion F) n
  obtain ⟨l2, s2, t2, -⟩ := UpperTheory.V.Z.Tf.Orb.gLTop_of (w.1.adicCompletion E) n
  have e1 := UpperTheory.Gal.InertialTypesAlt.L.trSum _ _ hH (KO _ n) (by rw [hKK]; exact (hUS _ n).1) (by rw [hKK]; exact (hUS _ n).2.1)
    (by rw [hKK]; exact hE1) _ τ'.ρ τ'.smooth (K1 rK n) hUKo hUKle _ hHK (I₂ : τ'.V →ₗ[ℂ] τ'.V)
    (fun x hx => by rw [hI₂c]; exact hTw.mem_fixed hst1 hx)
    (twKer_keep _ _ (GlobalTheory.LBC.galAct s n) hstab _ (fun g x => (hI₂ g x).trans (congrArg (fun h => τ'.ρ h (I₂ x)) (hsg g))))
    B _ hB hBt (fin_fixed τ' _ hUKo hUKc)
  have e2 := UpperTheory.Gal.InertialTypesAlt.L.trSum _ _ hF (KO _ n) (by rw [hKk]; exact (hUS _ n).1) (by rw [hKk]; exact (hUS _ n).2.1)
    (by rw [hKk]; exact hF1) _ τ.ρ τ.smooth (K1 rk n) hUko hUkle _ hHk LinearMap.id (fun _ h => h) (fun _ h => h)
    A z hA hAt (fin_fixed τ _ hUko hUkc)
  rw [← e1, ← e2, mul_one]
