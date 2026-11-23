import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.CuspIso
import Development.AbelianVarietyTheory.Definitions.Divisors.WellChosen
import Development.AbelianVarietyTheory.Definitions.Divisors.P22
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsLogCanonicalMultipleCanonical
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GeometricallyConnectedOfIsIsoRestrict
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DenseInterior
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrysToDRBijective
import Formalism.LocalToGlobal.ProjectiveLattices.ReadQuot
import Formalism.LocalToGlobal.ProjectiveLattices.ReadLeaves
import Development.AbelianVarietyTheory.Proofs.HeightProofs.VolPairExAndFinVol
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsCoreGoodMatch
import Development.AbelianVarietyTheory.Counterexamples.LevelGroupExamples.LocClauseOfUnifPlaces
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsPrincipalLevelSubgroupOpen
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsIdempotentComponentOfGroupElement
import Formalism.LocalToGlobal.BesselHermitianTheta.TiedWeil
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop
open GlobalTheory.AllWt (Psi wtOf cuspOn latOn normOn petOn GoodOn GoodW bergOn framesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp
set_option synthInstance.maxHeartbeats 400000
open MeasureTheory Formalism.L2.Theta Formalism.BasicNotions.TH ReciprocityTheory.ChartRestriction.G.FD Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open scoped Topology TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.LevelNbhd

open GlobalTheory.GfCut

variable {D : D7}

def finIdem (D : D7) : AE D := algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 1)

theorem finIdem_mul : finIdem D * finIdem D = finIdem D := by
  unfold finIdem
  rw [← map_mul]
  congr 1
  show ((0 : Ainf D.host.F) * 0, (1 : Af D.host.F) * 1) = (0, 1)
  simp

theorem cA_finIdem : cA D (finIdem D) = finIdem D := by
  unfold finIdem
  simp [cA, sigR, Algebra.TensorProduct.algebraMap_apply]

theorem fst_finIdem :
    (Algebra.TensorProduct.map (fstA D.host.F) (AlgHom.id D.host.F D.host.E)).toRingHom (finIdem D) = 0 := by
  show fstA D.host.F (pairA D.host.F 0 1) ⊗ₜ[D.host.F] (AlgHom.id D.host.F D.host.E) 1 = 0
  rw [show fstA D.host.F (pairA D.host.F 0 1) = 0 from rfl, TensorProduct.zero_tmul]

theorem snd_finIdem :
    (Algebra.TensorProduct.map (sndA D.host.F) (AlgHom.id D.host.F D.host.E)).toRingHom (finIdem D) = 1 := by
  show sndA D.host.F (pairA D.host.F 0 1) ⊗ₜ[D.host.F] (AlgHom.id D.host.F D.host.E) 1 = 1
  rw [show sndA D.host.F (pairA D.host.F 0 1) = 1 from rfl]
  rfl

def finPartGL (V : HSp D) (g : GA D V) : GL (Fin V.rank) (AE D) :=
  ⟨finIdem D • Formalism.L2.Theta.mt V g + (1 - finIdem D) • 1,
    finIdem D • ((matHom V g)⁻¹).1 + (1 - finIdem D) • 1,
    idem_mul _ finIdem_mul _ _ (matHom V g).mul_inv, idem_mul _ finIdem_mul _ _ (matHom V g).inv_mul⟩

theorem finPartGL_mem (V : HSp D) (g : GA D V) : finPartGL V g ∈ HR (AF D.host.F) D.sp.cm.sig V.gram := by
  have hgU : Formalism.UG.cT (cA D) (Formalism.L2.Theta.mt V g) * V.gram.map (incA D) * Formalism.L2.Theta.mt V g =
      V.gram.map (incA D) :=
    (show HR (AF D.host.F) D.sp.cm.sig V.gram from g).2
  have hKU := idem_unitary (cA D) _ cA_finIdem finIdem_mul _ _ hgU
  exact hKU

def finPartG (V : HSp D) (g : GA D V) : GA D V :=
  (⟨finPartGL V g, finPartGL_mem V g⟩ : HR (AF D.host.F) D.sp.cm.sig V.gram)

theorem finPartG_mem_GfC (V : HSp D) (g : GA D V) : finPartG V g ∈ GfC V := by
  show infHom V (finPartG V g) = 1
  apply Units.ext
  change (finIdem D • Formalism.L2.Theta.mt V g + (1 - finIdem D) • (1 : Matrix (Fin V.rank) (Fin V.rank) (AE D))).map _ = 1
  rw [map_idem, fst_finIdem, zero_smul, zero_add, sub_zero, one_smul]

theorem finHom_finPartG (V : HSp D) (g : GA D V) : finHom V (finPartG V g) = finHom V g := by
  apply Units.ext
  change (finIdem D • Formalism.L2.Theta.mt V g + (1 - finIdem D) • (1 : Matrix (Fin V.rank) (Fin V.rank) (AE D))).map _ = _
  rw [map_idem, snd_finIdem, one_smul, sub_self, zero_smul, add_zero]
  rfl

theorem inv_finPartG_mul_mem_GinfC (V : HSp D) (g : GA D V) : (finPartG V g)⁻¹ * g ∈ GinfC V := by
  show finHom V ((finPartG V g)⁻¹ * g) = 1
  rw [map_mul, map_inv, finHom_finPartG, inv_mul_cancel]

theorem finCong_finPartG_iff {V : HSp D} {N : ℕ} (g : GA D V) :
    GlobalTheory.Member.FinCong V N (finPartG V g) ↔ GlobalTheory.Member.FinCong V N g := by
  unfold GlobalTheory.Member.FinCong
  rw [finHom_finPartG]

theorem level_mul_inf_mem_nhds : ∀ (D : D7) (V : HSp D) (N : ℕ) (Kf : Subgroup (GA D V)), 0 < N →
    IsLevelK V N Kf → ∀ g₀ : GA D V,
      {g : GA D V | ∃ k ∈ Kf, ∃ h ∈ GinfC V, g = g₀ * k * h} ∈ 𝓝 g₀ := by
  intro D V N Kf hN hK g₀
  haveI : IsTopologicalGroup (GA D V) := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.topGroupHA _ _
  have hU := GlobalTheory.Member.PrincLevel.finCong_mem_nhds V hN
  have ht : Filter.Tendsto (fun x : GA D V => g₀⁻¹ * x) (𝓝 g₀) (𝓝 1) := by
    have := (continuous_mul_left g₀⁻¹).tendsto g₀
    rwa [inv_mul_cancel] at this
  refine Filter.mem_of_superset (ht hU) fun x hx => ?_
  have hx' : GlobalTheory.Member.FinCong V N (g₀⁻¹ * x) := hx
  refine ⟨finPartG V (g₀⁻¹ * x), (hK _).2 ⟨finPartG_mem_GfC V _, (finCong_finPartG_iff _).2 hx'⟩,
    (finPartG V (g₀⁻¹ * x))⁻¹ * (g₀⁻¹ * x), inv_finPartG_mul_mem_GinfC V _, ?_⟩
  group

end GlobalTheory.LevelNbhd
