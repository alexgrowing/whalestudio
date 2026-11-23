import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevelAutomorphismRepresentation
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BadPartDimLeSumLocalSharesWhittakerStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalShareSumBoundStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoveringRepresentationTypeFrameStatement
import Development.AbelianVarietyTheory.Definitions.Divisors.HypothesesX
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.GreenCuspidalIff
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.SiegelToroidalIntegral
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ToroidalCompactificationBis
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.InterNumDetNonposSplitTorus
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GrothendieckDeformation
import Development.AbelianVarietyTheory.Definitions.Divisors.CovolXOfCovol
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
open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Theta
open GlobalTheory GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.HSApp GlobalTheory.DegVal GlobalTheory.DegCmp
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW latOn latW normOn petOn GoodOn GoodW rankOn degOn rankW)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR latN levDet secRing transl pull KeepsCusp)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.BadCount
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.BadIndef

theorem finiteDimensional_of_lat {K V : Type} [Field K] [NumberField K] [AddCommGroup V] [Module K V]
    [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (L : Submodule (𝓞 K) V) (hL : L.FG)
    (hs : Submodule.span K (L : Set V) = ⊤) : FiniteDimensional K V := by
  obtain ⟨s, rfl⟩ := hL
  refine Module.finite_def.2 ⟨s, ?_⟩
  rw [← Submodule.span_span_of_tower (𝓞 K) K (s : Set V)]
  exact hs

set_option maxHeartbeats 1000000 in

theorem bad_rows_indef : GlobalTheory.CovTop.HypothesesX → Hypotheses2 → GlobalTheory.Published.GrothendieckDeformation → GlobalTheory.HSCore.Quoted → GlobalTheory.Published.SiegelToroidalIntegral → GlobalTheory.Published.ToroidalForFanKS → GlobalTheory.Published.SemiAbelianLieSeminegative → GlobalTheory.Published.GreenCuspidal → Gram → DeepGood → Size → FlatDeg → Deg → Share → Covers fun _ _ _ _ p i _ _ _ => BadAt p i := by
  intro hX hP hGD hQ hS hT hSA hGr hG hDG hSz hFD hDg hSh
  have hB := GlobalTheory.T.level_automorphism_representation hP hG hDG
  have hW := GlobalTheory.T.local_share_sum_bound hP hGr
  have hE := GlobalTheory.T.covering_representation_type_frame hX hP hGD hQ hS hT hSA hG hDG hSz hFD hDg hSh
  refine Formalism.MainNotions.Closed.imp (((hB.and hW).and hE).and hDG) ?_
  rintro eps Fm CH - ⟨⟨⟨⟨C1, -, x1, h1⟩, ⟨C2, -, x2, h2⟩⟩, ⟨C3, -, x3, h3⟩⟩, ⟨C4, -, x4, h4⟩⟩
  refine ⟨0, le_rfl, max (max x1 x4) (max x2 x3), fun x hx hle ι p hp i hi Y hY => ?_⟩
  have l1 : x1 ≤ x := ((le_max_left _ _).trans (le_max_left _ _)).trans hle
  have l4 : x4 ≤ x := ((le_max_right _ _).trans (le_max_left _ _)).trans hle
  have l2 : x2 ≤ x := ((le_max_left _ _).trans (le_max_right _ _)).trans hle
  have l3 : x3 ≤ x := ((le_max_right _ _).trans (le_max_right _ _)).trans hle
  obtain ⟨ψ₀, hψ₀, hsh⟩ := h2 x hx l2 ι p hp i
  obtain ⟨fr, π, s, ρ, χ, Pb, lam, ψ, lamb, H, hsp, hwh, hlb, hhalf, hPb, hH, hρ, hrkT, hrkB⟩ :=
    h1 x hx l1 ι p hp i hi Y hY
  have hemb := fun k => h3 x hx l3 ι p hp i hi Y hY fr π ρ χ Pb lamb H hPb hH hρ k
  choose n hn1 hn2 using hemb
  have hgd := (h4 x hx l4 ι p hp i hi Y hY).1
  haveI : FiniteDimensional Y.d.c₂.F (Y.V (Gk p i)) := finiteDimensional_of_lat _ hgd.2.1 hgd.2.2
  obtain ⟨S, hSg, hbd⟩ := GlobalTheory.T.bad_part_dim_le_sum_local_shares_whittaker (Fm.D x ι) _ _ π s hsp ρ Pb lam ψ hwh lamb hlb H hhalf n (3 / 2) hn1 hn2 ψ₀ hψ₀
  have hs := hsh S hSg
  have e0 : (0 : ℝ) ≤ Module.finrank ℂ (eig ρ (Pb.comap π) lamb) := Nat.cast_nonneg _
  have e1 : 0 ≤ Real.exp (-((Fm.L x ι).sc.x ^ ((Fm.L x ι).sc.ez / 7))) := (Real.exp_pos _).le
  have k1 := mul_le_mul_of_nonneg_right hs e0
  have k2 := mul_nonneg e1 e0
  have key : (Formalism.HN.rkK (CovTop.latBad p.R.toRealDat p.F.lv2 i) : ℝ) ≤
      3 * Real.exp (-((Fm.L x ι).sc.x ^ ((Fm.L x ι).sc.ez / 7))) * Formalism.HN.rkK (latType p.R.toRealDat p.F.lv2 i) := by
    rw [hrkT, hrkB]
    refine hbd.trans ?_
    linarith
  exact key

end GlobalTheory.BadIndef
