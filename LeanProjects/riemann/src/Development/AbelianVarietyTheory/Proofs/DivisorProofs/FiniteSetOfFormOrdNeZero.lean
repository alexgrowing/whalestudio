import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsLogMult
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsNeZeroIsStandardSmoothOfRelativeDimension
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TopologicalKrullDimEqOfIsIsoRestrict
import Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.FiniteCodimOnePointsClosed
import Development.AbelianVarietyTheory.Definitions.Divisors.IsEtCoord
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumOrdSubOneLeOrdWedgeDifferentials
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntersectionNumberPullbackProportionalOfProporti
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.LogPair

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FormOrdFinite

theorem exists_isFrame_genericPoint {k : Type} [Field k] [PerfectField k] {X : Scheme.{0}}
    [IsIntegral X] (p : X ⟶ Sp k) [LocallyOfFiniteType p] (n : ℕ)
    (hn : topologicalKrullDim X = n) :
    ∃ (U : X.Opens) (ω : FormsOn p n U), genericPoint X ∈ U ∧ IsFrame ω := by
  obtain ⟨V, hV, hgV, -⟩ := exists_isAffineOpen_mem_and_subset (x := genericPoint X) (U := ⊤) trivial
  haveI : Nonempty V := ⟨⟨_, hgV⟩⟩
  letI := (ReciprocityTheory.ChartRestriction.G.DVR.FlatBC.algX p V).toAlgebra
  have h1 : (ReciprocityTheory.ChartRestriction.G.DVR.FlatBC.algX p V).FiniteType :=
    (p.finiteType_appLE (isAffineOpen_top _) hV _).comp
      (.of_surjective _ (ConcreteCategory.bijective_of_isIso _).2)
  haveI : Algebra.FiniteType k Γ(X, V) := h1
  have hd : ringKrullDim Γ(X, V) = n := by
    have h2 := GlobalTheory.OpenDim.topologicalKrullDim_open k p V ⟨_, hgV⟩
    rw [hn] at h2
    rw [← PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim, ← h2]
    exact (topologicalKrullDim_eq_of_isEmbedding hV.fromSpec.isOpenEmbedding.isEmbedding
      hV.range_fromSpec).symm
  obtain ⟨s, hs, hsm⟩ := GlobalTheory.AffinePoints.exists_ne_zero_isStandardSmoothOfRelativeDimension
    (K := k) (A := Γ(X, V)) hd
  have hloc := hV.isLocalization_basicOpen s
  have h₁ : (algebraMap k (Localization.Away s)).IsStandardSmoothOfRelativeDimension n :=
    (RingHom.isStandardSmoothOfRelativeDimension_algebraMap n).2 hsm
  have h₂ := RingHom.isStandardSmoothOfRelativeDimension_respectsIso.1 _
    (IsLocalization.algEquiv (Submonoid.powers s) (Localization.Away s)
      Γ(X, X.basicOpen s)).toRingEquiv h₁
  have e : ((IsLocalization.algEquiv (Submonoid.powers s) (Localization.Away s)
      Γ(X, X.basicOpen s)).toRingEquiv.toRingHom.comp (algebraMap k (Localization.Away s))) =
      ReciprocityTheory.ChartRestriction.G.DVR.FlatBC.algX p (X.basicOpen s) := by
    rw [← resG_comp_algX p (X.basicOpen_le s)]
    ext a
    simp [IsScalarTower.algebraMap_apply k Γ(X, V) (Localization.Away s)]
    rfl
  rw [e] at h₂
  obtain ⟨ω, hω⟩ := GlobalTheory.TopForm.exists_isFreeGen h₂
  have hne : X.basicOpen s ≠ ⊥ := fun h => hs ((AlgebraicGeometry.basicOpen_eq_bot_iff s).1 h)
  obtain ⟨x, hx⟩ := (TopologicalSpace.Opens.ne_bot_iff_nonempty _).1 hne
  exact ⟨X.basicOpen s, ω, gen_mem hx, hV.basicOpen s, hω⟩

theorem finite_setOf_formOrd_ne_zero : ∀ (k : Type) [Field k] [CharZero k] (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] [GlobalTheory.IsNormalScheme X] (p : X ⟶ Sp k) (n : ℕ), IsProjOver p → topologicalKrullDim X = n → ∀ η : RatForms p n, η ≠ 0 → {z : X | ∃ E : DivOver p, E.IsAt z ∧ E.formOrd η ≠ 0}.Finite := by
  intro k _ _ X _ _ _ p n hp hn η hη
  haveI : IsProper p := ((isProjOver_iff_isProper_and_exists_isAmpleLB _).1 hp).1
  haveI : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace p
  haveI : IsNoetherian X := {}
  obtain ⟨U, ω, hU, hω⟩ := exists_isFrame_genericPoint p n hn
  have hgen := isFreeGen_formOf hU hω
  have h0 : formOf U hU ω ≠ 0 := fun h =>
    one_ne_zero (hgen.1 (a₁ := 1) (a₂ := 0) (by simp [h]))
  obtain ⟨c, hc⟩ := hgen.2 η
  replace hc : c • formOf U hU ω = η := hc
  have hc0 : c ≠ 0 := fun h => hη (by rw [← hc, h, zero_smul])
  obtain ⟨W, hW, hWu⟩ := (unitAt_genericPoint hc0).exists_nhds
  let B : Closeds X := ⟨((U ⊓ W : X.Opens) : Set X)ᶜ, (U ⊓ W).isOpen.isClosed_compl⟩
  have hB : B ≠ ⊤ := fun h => by
    have hm : genericPoint X ∈ (B : Set X) := by rw [h]; trivial
    exact hm ⟨hU, hW⟩
  refine (GlobalTheory.T.finite_codim_one_points_closed X B hB).subset ?_
  rintro z ⟨E, hE, hne⟩
  refine ⟨hE.coheight_eq_one, fun hz => hne ?_⟩
  obtain ⟨hzU, hzW⟩ := hz
  obtain ⟨a, ha, e⟩ := hWu z hzW
  have hord : E.ord (Units.mk0 c hc0) = 0 :=
    E.ord_eq_zero (u := hE.equiv a) (ha.map hE.equiv) e
  have h1 := E.formOrd_smul hn h0 (Units.mk0 c hc0)
  rw [Units.val_mk0, hc, hord, DivOver.formOrd_formOf_eq_zero hzU hE hω] at h1
  simpa using h1

end GlobalTheory.FormOrdFinite
