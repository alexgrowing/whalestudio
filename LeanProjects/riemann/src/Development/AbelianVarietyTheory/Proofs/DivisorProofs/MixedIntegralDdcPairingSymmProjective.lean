import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.DensConst
import Development.AbelianVarietyTheory.Definitions.Divisors.ContinuousBcPt
import Development.AbelianVarietyTheory.Definitions.Divisors.IsAmbOfIsArithVar
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GeometricallyConnectedOfIsIsoRestrict
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RationalSectionDivisorPullbackGeneric
import ReciprocityTheory.AnalyticForms.PotentialTheory.ProjectiveLineFubiniStudyFacts
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothWeightedLineBundleIsometryCalculusStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MixedChernFormSignedPartMeasureEqOfIsometricProjStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MixedChernIntegralEqMongeAmpereIntegralCompactStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MixedIntegralPullbackGenericallyFiniteStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLogResolutionProjectiveOfPrincipalisationStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ChartGlue GlobalTheory.Mix

namespace GlobalTheory.Mix

theorem mInt_half {e : ℕ} {X : Type} [TopologicalSpace X] [CompactSpace X] [T2Space X] (A : FinHolAtlas e X)
    (Φ : Fin e → LocPot X) (hΦ : ∀ i, IsPotential A (Φ i)) (g : X → ℝ) (hg : Continuous g) :
    mInt A Φ (fun x => g x / 2) = mInt A Φ g / 2 := by
  have h0 := mIntegrableCont A Φ hΦ (fun _ => 0) continuous_const
  have h1 := mIntLinear A Φ hΦ 1 (fun _ => 0) (fun _ => 0) h0 h0
  have h2 := mIntLinear A Φ hΦ (1 / 2) g (fun _ => 0) (mIntegrableCont A Φ hΦ g hg) h0
  have e1 : (fun x => 1 / 2 * g x + 0) = fun x => g x / 2 := funext fun x => by ring
  simp only [mul_zero, add_zero] at h1
  rw [e1] at h2
  linarith

theorem mInt_cons_ofFun_symm {k : Type} [CommRing k] {X : Scheme.{0}} {p : X ⟶ Sp k} {σ : k →+* ℂ} {e : ℕ}
    [CompactSpace (CxPts p σ)] [T2Space (CxPts p σ)] {A : FinHolAtlas (e + 1) (CxPts p σ)} (hA : IsAlgAtlas A)
    (L : Fin e → MLine p σ) (u v : CxPts p σ → ℝ) (hu : ∀ y, CInfAt u y) (hv : ∀ y, CInfAt v y) :
    mInt A (fun i => ((Fin.cons (MLine.ofFun u hu) L : Fin (e + 1) → MLine p σ) i).φ.locPot) v =
      mInt A (fun i => ((Fin.cons (MLine.ofFun v hv) L : Fin (e + 1) → MLine p σ) i).φ.locPot) u := by
  have hpot (N : MLine p σ) : IsPotential A N.φ.locPot :=
    ((Weight.isCInf_iff_isSmooth hA.anRead).1 N.cInf).isPotential hA
  have hsm (a : CxPts p σ → ℝ) (ha : ∀ y, CInfAt a y) : A.Smooth fun y => a y / 2 := fun j =>
    ((hA.smooth_iff hA.anRead).2 ((cInfAt_iff_smoothOn hA.anRead isOpen_univ).1 fun y _ => ha y) j).div_const 2
  have key (a b : CxPts p σ → ℝ) (ha : ∀ y, CInfAt a y) (hb : ∀ y, CInfAt b y) :
      mInt A (Fin.cons (LocPot.ofFun fun y => a y / 2) fun i => (L i).φ.locPot) (fun y => b y / 2) =
      mInt A (fun i => ((Fin.cons (MLine.ofFun a ha) L : Fin (e + 1) → MLine p σ) i).φ.locPot) b / 2 := by
    rw [← mInt_half A _ (fun i => hpot _) b (continuous_iff_continuousAt.2 fun y => (hb y).continuousAt)]
    refine SameForm.mInt_eq (fun i => ?_) _
    refine Fin.cases ?_ (fun j => ?_) i
    · exact fun _ _ _ => rfl
    · exact fun _ _ _ => rfl
  have h := byPartsSymm A _ _ (hsm v hv) (hsm u hu) (fun i => (L i).φ.locPot) fun i => hpot _
  rw [key u v hu hv, key v u hv hu] at h
  linarith

theorem int_cons_ofFun_symm : GlobalTheory.Published.Principalisation → ∀ (F : Type) [Field F] (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] (p : X ⟶ Sp F) (σ : F →+* ℂ) (e : ℕ), IsProjOver p → topologicalKrullDim X = (e + 1 : ℕ) → ∀ (L : Fin e → MLine p σ) (u v : CxPts p σ → ℝ) (hu : ∀ y, CInfAt u y) (hv : ∀ y, CInfAt v y), Mix.int (Fin.cons (MLine.ofFun u hu) L : Fin (e + 1) → MLine p σ) v = Mix.int (Fin.cons (MLine.ofFun v hv) L : Fin (e + 1) → MLine p σ) u := by
  intro hP F _ X _ _ p σ e hproj hdim L u v hu hv
  haveI : CharZero F := RingHom.charZero σ
  obtain ⟨Y, hY, π, hsm, hprojY, -, hgen, hdeg, -⟩ :=
    GlobalTheory.T.exists_logResolution_projective_of_principalisation hP F X p (e + 1) hproj hdim ⊥
      (by rw [← SetLike.mem_coe, TopologicalSpace.Closeds.coe_bot]; exact Set.notMem_empty _)
  haveI := hsm
  haveI : CompactSpace (CxPts (π ≫ p) σ) := CxPts.compactSpace σ hprojY
  haveI : T2Space (CxPts (π ≫ p) σ) := CxPts.t2Space_cxPts_of_isProjOver σ hprojY
  haveI : SecondCountableTopology (CxPts (π ≫ p) σ) := CxPts.secondCountableTopology_of_isProjOver σ hprojY
  have hA : IsAlgAtlas (AnRead.all (π ≫ p) σ (e + 1)).finAtlas := AnRead.isAlgAtlas_finAtlas _
  have hiso := GlobalTheory.T.smoothWeightedLineBundle_isometry_calculus F X Y p (π ≫ p) σ π rfl
  have hisoY := GlobalTheory.T.smoothWeightedLineBundle_isometry_calculus F Y Y (π ≫ p) (π ≫ p) σ (𝟙 Y) (Category.id_comp _)
  have key (a b : CxPts p σ → ℝ) (ha : ∀ y, CInfAt a y) (hb : ∀ y, CInfAt b y) :
      Mix.int (Fin.cons (MLine.ofFun a ha) L : Fin (e + 1) → MLine p σ) b =
      mInt (AnRead.all (π ≫ p) σ (e + 1)).finAtlas (fun i => ((Fin.cons (MLine.ofFun (fun z => a (ptMap π rfl σ z))
        fun z => (ha _).pull π rfl) fun i => (L i).pull π rfl : Fin (e + 1) → MLine (π ≫ p) σ) i).φ.locPot)
        (fun z => b (ptMap π rfl σ z)) := by
    have hbc : Continuous b := continuous_iff_continuousAt.2 fun y => (hb y).continuousAt
    have hbc' : Continuous fun z : CxPts (π ≫ p) σ => b (ptMap π rfl σ z) :=
      continuous_iff_continuousAt.2 fun z => ((hb _).pull π rfl).continuousAt
    have h1 := (GlobalTheory.T.mixedIntegral_pullback_genericallyFinite F X Y p (π ≫ p) σ (e + 1) hproj hdim hprojY π rfl hgen
      (by rw [hdeg]; exact one_ne_zero) (Fin.cons (MLine.ofFun a ha) L) b hbc.measurable).2
    rw [hdeg, Nat.cast_one, one_mul] at h1
    have h2 := GlobalTheory.T.mixedChernFormSignedPartMeasure_eq_of_isometric_projOver F Y (π ≫ p) σ hprojY (e + 1)
      (fun i => ((Fin.cons (MLine.ofFun a ha) L : Fin (e + 1) → MLine p σ) i).pull π rfl)
      (Fin.cons (MLine.ofFun (fun z => a (ptMap π rfl σ z)) fun z => (ha _).pull π rfl) fun i => (L i).pull π rfl)
      (fun i => Fin.cases (hiso.2.2.2.1 a ha) (fun j => hisoY.1 _) i)
    have h3 := GlobalTheory.T.mixedChernIntegral_eq_mongeAmpereIntegral_compact F Y (π ≫ p) σ (e + 1) _ hA
      (Fin.cons (MLine.ofFun (fun z => a (ptMap π rfl σ z)) fun z => (ha _).pull π rfl) fun i => (L i).pull π rfl)
      _ hbc'.measurable
    rw [← h1, ← h3.2 (h3.1.2 (mIntegrableCont _ _
      (fun i => ((Weight.isCInf_iff_isSmooth hA.anRead).1 (MLine.cInf _)).isPotential hA) _ hbc'))]
    simp only [Mix.int, h2]
  rw [key u v hu hv, key v u hv hu]
  exact mInt_cons_ofFun_symm hA _ _ _ _ _

end GlobalTheory.Mix
