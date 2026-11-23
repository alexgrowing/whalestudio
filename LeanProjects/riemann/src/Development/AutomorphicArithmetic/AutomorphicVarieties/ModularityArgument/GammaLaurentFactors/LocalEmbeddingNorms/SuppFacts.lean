import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.GammaLaurentFactors.MatchIndOf
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.BernsteinZelevinskyFiniteness
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.GeometricLemma
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.HasSupportOfIsSubquotientProdIrr
import Development.WeilBound.CoreStatements.PublishedTheorems.FiniteGLInvariants.AffineLieInvariants.Imports
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsLocCompAndIsLocLoc
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EquivOfISupRange
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsFixedOfMemISup
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsFixedIff
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.HeckeCharLocalComponentExistsUniqueUnitary
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsEquivProdIrrTw
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SupercuspidalSupportOfPrincipalSeriesSubquotient
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SphericalRepGLExistsSatakeParameters

noncomputable section

open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.HenQ UpperTheory.V.Z.Bc UpperTheory.V.Published
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL UpperTheory.Zero.LLC UpperTheory.V.Z.Inf
open scoped Classical

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
attribute [-instance] Formalism.DoubleCosetMeasures.instMeasGL

namespace UpperTheory.V.Z.Gam

section Loc

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {V : Type} [AddCommGroup V] [Module ℂ V] {n : ℕ}

private theorem supp_unique {π : Representation ℂ (GL (Fin n) k) V} {s t : Multiset (IrrGL k)}
    (hs : HasSupport π s) (ht : HasSupport π t) : s = t :=
  GlobalTheory.CompanionTheory.Hypotheses₂.TD.hasSupport_unique GlobalTheory.CompanionTheory.GeoLink.geometricLemma GlobalTheory.CompanionTheory.Published.bernsteinZelevinskyFiniteness hs ht

private theorem supp_exists {π : Representation ℂ (GL (Fin n) k) V} (h1 : IsSmooth π) (h2 : π.IsIrreducible) :
    ∃ s, HasSupport π s := by
  obtain ⟨s, hs⟩ := GlobalTheory.CompanionTheory.Hypotheses₂.TD.exists_hasSupport GlobalTheory.CompanionTheory.Published.bernsteinZelevinskyFiniteness
    GlobalTheory.CompanionTheory.GeoLink.geometricLemma (IrrGL.of π h1 h2)
  exact ⟨s, hs.of_equiv (IrrGL.equivOf π h1 h2).symm⟩

private theorem unram_of_fixed [CharZero k] {π : Representation ℂ (GL (Fin n) k) V} {s : Multiset (IrrGL k)}
    (hs : HasSupport π s) {v : V} (h0 : v ≠ 0) (hv : ∀ g ∈ KO k (Fin n), π g v = v) : ∀ y ∈ s, y.IsUnramChar := by
  obtain ⟨α, hα⟩ := GlobalTheory.SatakeExists.exists_isSubquotient_prinSeries
    ((GlobalTheory.CompanionTheory.Published.bernsteinZelevinskyFiniteness k).1 (Fin n) V π hs.isSmooth hs.isIrreducible) hs.isIrreducible
    ((Submodule.ne_bot_iff _).2 ⟨v, fun g => by simpa using hv g.1 (iwahori_le_KO k _ g.2), h0⟩)
  have h := GlobalTheory.LocLanglands.hasSupport_of_isSubquotient_prinSeries k n (fun i => unrChar k (α i))
    (fun i => isSmoothChar_of_isUnram (isUnram_unrChar k (α i))) ⟨V, π, hs.isSmooth, hs.isIrreducible⟩ hα
  rw [supp_unique hs h]
  intro y hy
  obtain ⟨i, -, rfl⟩ := Multiset.mem_map.1 hy
  exact ⟨_, isUnram_unrChar k (α i), rfl⟩

private theorem tw_iff (y : IrrGL k) (χ θ : kˣ →* ℂˣ) (hχ : IsSmoothChar χ) :
    (∃ ξ hξ, y.tw χ hχ = IrrGL.ofChar ξ hξ ∧ IsUnram (ξ * θ)) ↔
      ∃ ξ hξ, y = IrrGL.ofChar ξ hξ ∧ IsUnram (ξ * (χ * θ)) := by
  constructor
  · rintro ⟨ξ, hξ, e, hu⟩
    refine ⟨ξ * χ⁻¹, hξ.mul hχ.inv, ?_, ?_⟩
    · rw [← IrrGL.tw_ofChar ξ χ⁻¹ hξ hχ.inv, ← e, IrrGL.tw_tw_inv]
    · rwa [mul_assoc, inv_mul_cancel_left]
  · rintro ⟨ξ, hξ, rfl, hu⟩
    exact ⟨ξ * χ, hξ.mul hχ, IrrGL.tw_ofChar _ _ _ _, by rwa [mul_assoc]⟩

end Loc

section Glob

variable {K : Type} [Field K] [NumberField K] [IsTotallyComplex K] {n : ℕ}

omit [IsTotallyComplex K] in
private theorem smooth_loc (χ : HChar K) (v : HeightOneSpectrum (𝓞 K)) : IsSmoothChar (χ.loc v) :=
  GlobalTheory.HeckeComp.smooth_loc χ v

private theorem exists_fixed {π : CuspSub K n} {v : HeightOneSpectrum (𝓞 K)} {σ : SmIrr (GL (Fin n) (v.adicCompletion K))}
    (hσ : π.IsLocComp v σ) {B : Multiset ℂˣ} (hB : (CG.mk π).HasSat v B) :
    ∃ y : σ.V, y ≠ 0 ∧ ∀ g ∈ KO (v.adicCompletion K) (Fin n), σ.ρ g y = y := by
  obtain ⟨x, hx, hx0⟩ := (Submodule.ne_bot_iff _).1 ((CG.hasSat_mk π v B).1 hB).1
  rw [show KO (v.adicCompletion K) (Fin n) = GlobalTheory.LFun.KGL v n from SphCompletion.KO_completion v n]
  exact LocSph.exists_fixed_of_mem_iSup ((finRep K n).comp (locGL K n v)) σ.ρ σ.irred
    (fun f : LocSph.Maps π v σ => f.1) (fun f => f.2.2) (GlobalTheory.LFun.KGL v n : Set _) x.1 (fun e => hx0 (Subtype.ext e))
    (fun g hg => congrArg Subtype.val (GlobalTheory.LGrp.mem_fixed.1 hx g hg))
    ((LocSph.iSup_range_eq π v σ hσ).symm ▸ x.2)

private theorem supp_twist {v : HeightOneSpectrum (𝓞 K)} {σ : SmIrr (GL (Fin n) (v.adicCompletion K))} (χ : HChar K)
    {s : Multiset (IrrGL (v.adicCompletion K))} (h : HasSupport σ.ρ s) :
    HasSupport (σ.twist (CuspSub.locDet n χ v) (CuspSub.isOpen_ker_locDet χ v)).ρ
      (s.map (·.tw (χ.loc v) (smooth_loc χ v))) :=
  h.tw (χ.loc v) (smooth_loc χ v)

end Glob

end UpperTheory.V.Z.Gam

open UpperTheory.V.Z.Gam in
theorem UpperTheory.V.Z.Gam.suppFacts :
    UpperTheory.V.Z.Gam.SuppFacts := by
  intro K _ _ _ n _ π v
  have uniq : ∀ {σ σ' s}, π.IsLocComp v σ → π.IsLocComp v σ' → HasSupport σ.ρ s → HasSupport σ'.ρ s :=
    fun h h' hs => hs.of_equiv (LocUniq.isLocComp_unique π v _ _ h h').some
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · obtain ⟨σ, hσ, -⟩ := LocEx.exists_isLocComp CuspFormAutomorphicBounds.automorphicFormsFiniteGL K n π v
    obtain ⟨s, hs⟩ := supp_exists σ.smooth σ.irred
    exact ⟨s, σ, hσ, hs⟩
  · rintro s s' ⟨σ, hσ, hs⟩ ⟨σ', hσ', hs'⟩
    exact supp_unique (uniq hσ hσ' hs) hs'
  · rintro s ⟨σ, hσ, hs⟩
    refine ⟨⟨fun h => ?_, fun h σ' hσ' => ?_⟩, by simpa using hs.sum_fst, fun y hy => (hs.isCusp hy).1⟩
    · obtain ⟨t, ht, h1⟩ := h σ hσ
      rwa [supp_unique hs (ht.of_equiv (IrrGL.equivOf σ.ρ σ.smooth σ.irred).symm)]
    · exact ⟨s, (uniq hσ hσ' hs).of_equiv (IrrGL.equivOf σ'.ρ σ'.smooth σ'.irred), h⟩
  · rintro s B ⟨σ, hσ, hs⟩ hB
    obtain ⟨y, h0, hy⟩ := exists_fixed hσ hB
    haveI : CharZero (v.adicCompletion K) := charZero_of_injective_algebraMap (algebraMap K _).injective
    exact unram_of_fixed hs h0 hy
  · rintro χ s ⟨σ, hσ, hs⟩
    refine ⟨_, ⟨_, hσ.twist χ, supp_twist χ hs⟩, fun θ => ?_, ?_⟩
    · unfold cnt
      rw [Multiset.filter_map, Multiset.card_map]
      exact congrArg Multiset.card (Multiset.filter_congr fun y _ => tw_iff y (χ.loc v) θ _)
    · rw [Multiset.map_map]
      rfl
