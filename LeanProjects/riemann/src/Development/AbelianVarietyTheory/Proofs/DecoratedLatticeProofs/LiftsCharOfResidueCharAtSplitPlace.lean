import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsLevMeas
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.TransferOn
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CartFrSgn
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HarishChandraFinite
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnrOffOne
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SplitProjAdeleComponentChartProperties
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SplitIdempotentPrimeProjectionCorrespondence
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemIdSOfResSEqZero
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.StrongApproximationDecomposition
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FinPartIdemMulMemIff
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.ChainTw
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (SplitProj IsProjAt IsIdemOf LiftsChar rdA grpCo frCo gAt)
open GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection (Blocks parahoric datum)
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.Chain GlobalTheory.ChainFr GlobalTheory.PairLift GlobalTheory.Chain.RealIt

noncomputable section

namespace GlobalTheory.ResLift

open GlobalTheory.AdelicU

variable {D : D7} {v : HeightOneSpectrum (𝓞 D.host.F)}

def swapProj (φ : SplitProj D v) : D.host.E ⊗[D.host.F] Fv D.host.F v →+* Fv D.host.F v :=
  φ.toRingHom.comp (Algebra.TensorProduct.comm D.host.F D.host.E (Fv D.host.F v)).toAlgHom.toRingHom

theorem swapProj_one_tmul (φ : SplitProj D v) (a : Fv D.host.F v) : swapProj φ ((1 : D.host.E) ⊗ₜ[D.host.F] a) = a := by
  change φ (a ⊗ₜ[D.host.F] (1 : D.host.E)) = a
  exact φ.commutes a

theorem swapProj_prV (φ : SplitProj D v) (z : EAf D) : swapProj φ (Formalism.UG.prV v z) = GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.rdE φ z := by
  induction z using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul b y => rfl

theorem swapProj_prV_oToS (φ : SplitProj D v) (x : 𝓞 D.host.E) :
    swapProj φ (Formalism.UG.prV v (Formalism.L2.DIV.oToS D.host.F D.host.E x).1) = GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.rdQ φ (x : D.host.E) := by
  rw [swapProj_prV, Formalism.L2.DIV.oToS_coe]
  change φ ((Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV D.host.F v 1) ⊗ₜ[D.host.F] (x : D.host.E)) = _
  rw [map_one]
  rfl

theorem isIdemOf_idem (φ : SplitProj D v) : IsIdemOf φ (GlobalTheory.EmbChart.idem (GlobalTheory.SplitProjChart.emb φ)) := by
  refine ⟨GlobalTheory.EmbChart.isSplitIdem_idem _, ?_, GlobalTheory.SplitProjChart.rdA_idem φ⟩
  rw [GlobalTheory.EmbChart.cA_idem, GlobalTheory.EmbChart.idem, ← LinearMap.map_add, add_sub_cancel]
  rfl

theorem eq_splitPrime {φ : SplitProj D v} {PP : Pl D.host.E} (hφ : IsProjAt φ PP) :
    PP = splitPrime (GlobalTheory.SplitProjChart.emb φ) :=
  HeightOneSpectrum.ext (Ideal.ext fun x => (hφ x).trans (mem_splitPrime (GlobalTheory.SplitProjChart.emb φ) x).symm)

theorem exists_mem_only (τ : D.host.E →ₐ[D.host.F] Fv D.host.F v) : ∃ p ∈ (splitPrime τ).asIdeal,
    ∀ P : HeightOneSpectrum (𝓞 D.host.E), P.under (𝓞 D.host.F) = v → p ∈ P.asIdeal → P = splitPrime τ := by
  obtain ⟨p, hp, hp'⟩ : ∃ p ∈ (splitPrime τ).asIdeal, p ∉ (splitPrime (τ.comp D.sp.cm.sig)).asIdeal := by
    by_contra hc
    push Not at hc
    have h := (splitPrime τ).isMaximal.eq_of_le (splitPrime (τ.comp D.sp.cm.sig)).isPrime.ne_top hc
    exact splitPrime_comp_ne (isCMExt_host D) τ (HeightOneSpectrum.ext h.symm)
  refine ⟨p, hp, fun P hP hpP => ?_⟩
  have hm : P.asIdeal ∈ v.asIdeal.primesOver (𝓞 D.host.E) := ⟨P.isPrime, ⟨hP ▸ rfl⟩⟩
  rw [primesOver_eq_split (isCMExt_host D) τ] at hm
  rcases hm with h | h
  · exact HeightOneSpectrum.ext h
  · exact absurd (h ▸ hpP) hp'

theorem resS_eq {φ : SplitProj D v} {PP : Pl D.host.E} (hφ : IsProjAt φ PP)
    (s : Formalism.L2.Herm.intAf D.host.F D.host.E) (x : 𝓞 D.host.E)
    (h : Valued.v (GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.rdE φ s.1 - GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.rdQ φ (x : D.host.E)) < 1) :
    resS D.host.F PP s = Ideal.Quotient.mk PP.asIdeal x := by
  obtain ⟨p, hp, hp'⟩ := exists_mem_only (GlobalTheory.SplitProjChart.emb φ)
  rw [← eq_splitPrime hφ] at hp hp'
  obtain ⟨ρ, ι, hρ, hρr⟩ := GlobalTheory.SplitResidue.exists_residue_equiv D.host.F D.host.E v PP
    (swapProj φ) p (swapProj_one_tmul φ) ((hφ p).1 hp) hp'
  have h0 : IsLocalRing.residue _ (ρ s) = IsLocalRing.residue _ (ρ (oToS D.host.F D.host.E x)) := by
    refine Ideal.Quotient.eq.2 ((GlobalTheory.SplitResidue.mem_maximalIdeal_iff v _).2 ?_)
    rw [AddSubgroupClass.coe_sub, hρ, hρ, swapProj_prV_oToS, swapProj_prV]
    exact h
  rw [hρr, hρr, resS_oToS] at h0
  exact ι.injective h0

theorem exists_unit_lift {A K : Type} [CommRing A] [CommRing K] (π : A →+* K) {e : A} (hee : e * e = e)
    (hs : Function.Surjective π) (hk : ∀ a, π a = 0 ↔ e * a = 0) (u : Kˣ) :
    ∃ x : Aˣ, (1 - e) * (x : A) = 1 - e ∧ e * ((x : A) - 1) = (x : A) - 1 ∧ π x = u := by
  obtain ⟨U, hU⟩ := hs (u : K)
  obtain ⟨U', hU'⟩ := hs ((u⁻¹ : Kˣ) : K)
  have h1 : e * (U * U' - 1) = 0 := (hk _).1 (by rw [map_sub, map_mul, hU, hU', map_one, Units.mul_inv, sub_self])
  have h2 : π (1 - e) = 0 := (hk _).2 (by linear_combination -hee)
  have h3 : π e = 1 := by
    rw [map_sub, map_one, sub_eq_zero] at h2
    exact h2.symm
  refine ⟨⟨e * U + (1 - e), e * U' + (1 - e), by linear_combination h1 + (U * U' - U - U' + 1) * hee,
    by linear_combination h1 + (U * U' - U - U' + 1) * hee⟩, ?_, ?_, ?_⟩
  · change (1 - e) * (e * U + (1 - e)) = 1 - e
    linear_combination (1 - U) * hee
  · change e * (e * U + (1 - e) - 1) = e * U + (1 - e) - 1
    linear_combination (U - 1) * hee
  · change π (e * U + (1 - e)) = u
    rw [map_add, map_mul, h2, h3, hU, one_mul, add_zero]

theorem liftsChar_of_resAt : ∀ (D : D7) (χ : (AE D)ˣ →* Circle) (PP : Pl D.host.E) (a : (kP PP)ˣ →* ℂˣ), GlobalTheory.StepLaw.ResAt χ PP a → ∀ (v : HeightOneSpectrum (𝓞 D.host.F)) (φ : SplitProj D v), IsProjAt φ PP → ∀ μ : (Fv D.host.F v)ˣ →* ℂˣ, (∀ (x : (AE D)ˣ) (y : (Fv D.host.F v)ˣ), (∃ e, IsIdemOf φ e ∧ (1 - e) * (x : AE D) = 1 - e ∧ rdA φ (x : AE D) = y) → μ y = Circle.toUnits (χ x)) → LiftsChar φ PP μ a := by
  intro D χ PP a hres v φ hφ μ hμ u k ⟨x0, hx0k, hx0⟩
  have he := isIdemOf_idem φ
  generalize GlobalTheory.EmbChart.idem (GlobalTheory.SplitProjChart.emb φ) = e at he
  have hch := (GlobalTheory.SplitProjChart.chart_rdA D v φ e he).1
  have hAt : Formalism.L2.NTheta.IsIdemAt e PP := (((GlobalTheory.SplitIdemDict.idem_dictionary D).2 v φ PP hφ).2.2 e he).1
  obtain ⟨x, h1, h2, h3⟩ := exists_unit_lift (rdA φ) he.1.1 hch.1 hch.2.1 u
  have hu : (u : Fv D.host.F v) ∈ v.adicCompletionIntegers D.host.F := by
    have h4 : (u : Fv D.host.F v) - GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.rdQ φ (x0 : D.host.E) ∈ v.adicCompletionIntegers D.host.F := hx0.le
    have h5 : GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.rdQ φ (x0 : D.host.E) ∈ v.adicCompletionIntegers D.host.F :=
      apply_coe_mem (GlobalTheory.SplitProjChart.emb φ) x0
    have h6 := add_mem h4 h5
    rwa [sub_add_cancel] at h6
  have hint : toEAf D (x : AE D) ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := by
    have h4 : finPart D (e * ((x : AE D) - 1)) ∈ intAE D := by
      refine (hch.2.2.2 _).2 (GlobalTheory.SplitHecke.isInt_Ov.2 ?_)
      rw [RingHom.map_sub, h3, RingHom.map_one]
      exact sub_mem hu (one_mem _)
    have h5 := (GlobalTheory.SplitDec.int_iff _).1 h4
    rw [h2, RingHom.map_sub, RingHom.map_one] at h5
    have h6 := add_mem h5 (one_mem _)
    rwa [sub_add_cancel] at h6
  have hk : resS D.host.F PP ⟨_, hint⟩ = Ideal.Quotient.mk PP.asIdeal x0 := by
    refine resS_eq hφ _ x0 ?_
    change Valued.v (GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.rdE φ (toEAf D (x : AE D)) - _) < 1
    rw [GlobalTheory.SplitProjChart.rdE_toEAf, h3]
    exact hx0
  rw [hμ x u ⟨e, he, h1, h3⟩]
  exact Units.ext (hres e hAt x h2 hint k (hk.trans hx0k).symm)

end GlobalTheory.ResLift

end
