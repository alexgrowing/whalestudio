import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GrothendieckDeformation
import Development.AbelianVarietyTheory.Definitions.Divisors.NormNegCmConstantEqAtAllEmbeddings
import Formalism.LocalRingCardinality.DataParamsT
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Definitions.Divisors.CuspIso
import Development.AbelianVarietyTheory.Definitions.Divisors.WellChosen
import Development.AbelianVarietyTheory.Definitions.Divisors.MeanLogLeOfBounds
import Development.AbelianVarietyTheory.Definitions.Divisors.WedgeNrmLeOfWedgeNormLe
import Development.AbelianVarietyTheory.Definitions.Divisors.IsHomWeightHomWeight
import Development.AbelianVarietyTheory.Definitions.Divisors.MemLevEigenIffTransl
import Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.RealCubicMeans.LogMeanShares.LogMeanStatements.HSClaim
import Development.AbelianVarietyTheory.Definitions.Divisors.GenRatios
import Development.AbelianVarietyTheory.Definitions.Divisors.BadElt
import Development.AbelianVarietyTheory.Definitions.Divisors.P22
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsLogCanonicalMultipleCanonical
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GeometricallyConnectedOfIsIsoRestrict
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DenseInterior
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrysToDRBijective
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FgIntOfForallIsIntegral
import Development.AbelianVarietyTheory.Definitions.CMLattices.IntegralOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSmulNonnegOfPow
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsScalarCuspFormIntegralStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSemilinearL2Independent
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSmulMemOfMemSpan
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCmPointGoodSectionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFrameDenominatorDominantWeightCmStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPowerCuspMultiplierGapStatement
open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Theta
open GlobalTheory GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.DegVal GlobalTheory.DegCmp
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW latOn latW normOn petOn GoodOn GoodW rankOn degOn rankW)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR latN levDet secRing transl pull KeepsCusp)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.BadCount
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.GeometryOfNumbersTheory TopologicalSpace Limits
open GlobalTheory.HSApp
set_option synthInstance.maxHeartbeats 400000
open GlobalTheory.LamT (CMPt)

noncomputable section

namespace GlobalTheory.CovTop.GoodDom

set_option maxHeartbeats 1000000 in

theorem latW_fg_dom : GlobalTheory.CovTop.Hypotheses2 → ∀ (D : D7) (T : Core D) (j : ℕ) (Y : Deep T j) (e : ℕ) (o : ℝ), Y.Good e o →
    2 < Module.finrank ℚ D.host.E / 2 → 1 ≤ (T.Q.Dw j).p → 1 ≤ (T.Q.Dw j).q → ∀ la : GlobalTheory.AllWt.Weight (T.Q.Dw j), (∀ τ, Antitone (la τ)) → (∀ τ, 1 ≤ gap (la τ) ((T.Q.Dw j).p - 1)) →
    FiniteDimensional Y.d.c₂.F (Y.V (wtOf _ la 0)) → (GlobalTheory.AllWt.latW Y.U (wtOf _ la 0)).FG := by
  intro hP D T j Y e o hG hE hp hq la hA hb hfd
  letI := T.Q.H.starRing
  refine GlobalTheory.fg_of_integral_functionals Y.d.c₂.F (Y.V (wtOf _ la 0)) _ fun x hx => ?_
  obtain ⟨z, La, y, hz, hyx, hne⟩ := GlobalTheory.T.exists_cm_point_good_section hP D T j Y e o hG hE hp hq la hA hb (fun _ => rfl) x.1 x.2
    (fun h => hx (Subtype.ext h))
  obtain ⟨N, hN, hint⟩ := GlobalTheory.T.exists_frame_denominator_dominant_weight_cm _ _ _ _ _ _ z _ La hz y hyx hp hq la hA hb
  refine ⟨z.K, inferInstance, inferInstance, inferInstance,
    { toFun := fun F => N * evR Y.d.Xo₂ Y.d.c₂ F.1 y
      map_add' := fun F G => ?_
      map_smul' := fun s F => ?_ }, mul_ne_zero hN hne, fun F hF => hint F.1 (GlobalTheory.AllWt.cuspW_le_secZ _ F.2) hF⟩
  · rw [← mul_add]
    exact congrArg _ (evalAt_add _ _ F.1 G.1 y)
  · have e1 : evR Y.d.Xo₂ Y.d.c₂ (s • F).1 y = algebraMap Y.d.c₂.F z.K s * evR Y.d.Xo₂ Y.d.c₂ F.1 y :=
      evalAt_smul _ _ s F.1 y
    rw [e1, RingHom.id_apply, Algebra.smul_def, mul_left_comm]

set_option maxHeartbeats 800000 in

theorem span_latW_dom : GlobalTheory.CovTop.Hypotheses2 → ∀ (D : D7) (T : Core D) (j : ℕ) (Y : Deep T j) (e : ℕ) (o : ℝ),
    Y.Good e o → 2 < Module.finrank ℚ D.host.E / 2 → 1 ≤ (T.Q.Dw j).p → 1 ≤ (T.Q.Dw j).q → ∀ la : GlobalTheory.AllWt.Weight (T.Q.Dw j), (∀ τ, Antitone (la τ)) → (∀ τ, 1 ≤ gap (la τ) ((T.Q.Dw j).p - 1)) →
    Submodule.span Y.d.c₂.F (GlobalTheory.AllWt.latW Y.U (wtOf _ la 0) : Set (Y.V (wtOf _ la 0))) = ⊤ := by
  intro hP D T j Y e o hY hE hp hq la hA hb
  refine eq_top_iff.2 fun f _ => ?_
  obtain ⟨k, a, n, g, h, t, hdom, hn, hmem, ht, hgh, hh⟩ := GlobalTheory.T.exists_power_cusp_multiplier_gap hP D T j Y e o hY hE hp hq la hA hb f.1 f.2
  obtain ⟨s, hs, hsv⟩ := GlobalTheory.T.exists_scalar_cusp_form_integral hP D T j Y e o hY hE a n hdom hn _ hmem
  have key : ∀ la', ∀ v ∈ valSet Y.d.Xo₂ Y.d.c₂ (algCls Y.d.Xo₂ Y.d.c₂) la',
      0 ≤ v ((s * t) • ((f : Rul Y.d.Xo₂ Y.d.c₂) ^ (k + 1))) := by
    intro la' v hv
    have hV := isVal_valSet la' v hv
    have e1 : (s • ((f : Rul Y.d.Xo₂ Y.d.c₂) ^ (k + 1) * g)) * h = (s * t) • ((f : Rul Y.d.Xo₂ Y.d.c₂) ^ (k + 1)) := by
      rw [smul_mul_assoc, mul_assoc, hgh, mul_smul_comm, mul_one, smul_smul]
    rw [← e1, hV.mul]
    exact add_nonneg (hsv la' v hv) (hh la' v hv)
  obtain ⟨s', hs', h'⟩ := GlobalTheory.SupFull.exists_smul_nonneg_of_pow (valSet Y.d.Xo₂ Y.d.c₂ (algCls Y.d.Xo₂ Y.d.c₂))
    (fun la => isVal_valSet la) {(f : Rul Y.d.Xo₂ Y.d.c₂) ^ (k + 1)}
    (by rintro g' rfl; exact ⟨s * t, mul_ne_zero hs ht, key⟩) (f : Rul Y.d.Xo₂ Y.d.c₂) k
    (Submodule.subset_span rfl)
  have hmem' : s' • f ∈ GlobalTheory.AllWt.latW Y.U (wtOf _ la 0) :=
    GlobalTheory.AllWt.mem_supLat.2 fun la v hv => h' la v hv
  rw [← inv_smul_smul₀ hs' f]
  exact Submodule.smul_mem _ _ (Submodule.subset_span hmem')

set_option maxHeartbeats 1000000 in

theorem goodAt_dom : Hypotheses2 → ∀ (D : D7) (T : CoreJ D), LawsJ T → ∀ j : ℕ, 1 ≤ (T.Q.Dw j).p → 1 ≤ (T.Q.Dw j).q → 2 < Module.finrank ℚ D.host.E / 2 → InR D j → ∀ (Y : Deep T.toCore j) (e : ℕ) (o : ℝ), Y.Good e o → ∀ la : AllWt.Weight (T.Q.Dw j), (∀ τ, Antitone (la τ)) → (∀ τ, 1 ≤ gap (la τ) ((T.Q.Dw j).p - 1)) → Y.GoodAt (wtOf _ la 0) ∧ ∀ Z, GoodOn Y.U (xiR D) (fun _ => D.sp.W j) Y.dict Z (wtOf _ la 0) := by
  intro hP D T hL j hp hq hE _ Y e o hY la hA hb
  have hfd := GlobalTheory.Deep.finiteDimensional_V_of_good D T.toCore j Y e o hY (wtOf _ la 0)
  have hG : Y.GoodAt (wtOf _ la 0) :=
    ⟨hasGram_nrm_of_good D T.toCore j Y e o hY _, latW_fg_dom hP D T.toCore j Y e o hY hE hp hq la hA hb hfd,
      span_latW_dom hP D T.toCore j Y e o hY hE hp hq la hA hb⟩
  exact ⟨hG, fun Z => goodOn_of_goodAt D T.toCore j Y e o hY hE Z _ hG⟩

end GlobalTheory.CovTop.GoodDom
