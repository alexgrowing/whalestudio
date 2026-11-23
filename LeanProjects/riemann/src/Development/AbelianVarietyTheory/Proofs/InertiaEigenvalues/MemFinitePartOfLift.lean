import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LiftQMk
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CrystallineCocycleTransportConjugation
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.LocalCoefficientChangeCompare
import Formalism.LocalRingCardinality.SpanPowerMembership.NDLocE
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsIntegralRetractionLocalIntegersStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsFieldExtensionOfIntegralRetractionStatement

noncomputable section
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pass GlobalTheory.Cut GlobalTheory.UseLoc Module

namespace GlobalTheory.UseLoc.DescHf

theorem exists_retraction {l : ℕ} [Fact l.Prime] {LL LL' : FinExt l} (h : LL.1 ≤ LL'.1) :
    ∃ p : ↥LL'.1 →ₗ[ℚ_[l]] ↥LL.1, (∀ (a : ↥LL.1) (x : ↥LL'.1), p (IntermediateField.inclusion h a * x) = a * p x) ∧
      (∀ a : ↥LL.1, p (IntermediateField.inclusion h a) = a) ∧ (∀ x : ↥LL'.1, x ∈ OL LL' → p x ∈ OL LL) := by
  obtain ⟨r, hr, hr1⟩ := GlobalTheory.T.exists_integral_retraction_localIntegers h
  obtain ⟨p, hp, hpr⟩ := GlobalTheory.T.exists_fieldExtension_of_integral_retraction h r hr hr1
  have h1 : p 1 = 1 := by
    have := hpr 1
    rw [hr1] at this
    exact this
  refine ⟨p, hp, fun a => ?_, fun x hx => ?_⟩
  · have := hp a 1
    rw [mul_one, h1, mul_one] at this
    exact this
  · have := hpr ⟨x, hx⟩
    rw [show p x = _ from this]
    exact (r ⟨x, hx⟩).2

set_option maxHeartbeats 1000000 in
set_option synthInstance.maxHeartbeats 400000 in

theorem descHf : ∀ (D : D7) (i : D.nd.Loc) (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i))
    (C : TruncatedSeriesCountingIdentities.CoefExt D i w hw) (k : ℕ) (M : GE D.nd →* Matrix (Fin k) (Fin k) (D.nd.O i))
    (z : Br.G D.nbr i w hw → (Fin k → Br.LL D.nbr i w hw) ⧸ (Br.locLat D.nbr i w hw M).T),
    (fun g => liftQ C.le k (z g)) ∈ HfD (Br.PD D.loc D.nbr i w hw) (latC C (locOC C M)) →
    z ∈ HfD (Br.PD D.loc D.nbr i w hw) (Br.locLat D.nbr i w hw M) := by
  intro D i w hw C k M z hz
  obtain ⟨p, hpm, hp1, hpO⟩ := exists_retraction C.le
  obtain ⟨c, hc, m, hcm⟩ := (GlobalTheory.BlochKatoBaseChangeLe.mem_HfD_gen _ _ _).1 hz
  have hent : ∀ g a b, (mapM (algebraMap ↥(OL C.LL) ↥C.LL.1) (locOC C M) g) a b =
      IntermediateField.inclusion C.le (Br.loc D.nbr i w hw M g a b) := fun g a b => rfl
  have hp : ∀ g (v : Fin k → ↥C.LL.1),
      (fun j => p ((mapM (algebraMap ↥(OL C.LL) ↥C.LL.1) (locOC C M) g).mulVec v j)) =
        (Br.loc D.nbr i w hw M g).mulVec fun j => p (v j) := by
    intro g v
    funext a
    simp only [Matrix.mulVec, dotProduct, map_sum, hent, hpm]
  have hc' := GlobalTheory.TwistedSelmerCompare.crystallineCocycle_transport_conjugation (D.loc (D.nd.l i)) (D.nbr i w hw).Kw (D.nbr i w hw).Kw C.LL
    (D.nbr i w hw).LL (MonoidHom.id _) continuous_id 1 (fun g => by simp) _ (Br.loc D.nbr i w hw M) p hp c hc
  refine (GlobalTheory.BlochKatoBaseChangeLe.mem_HfD_gen _ _ _).2 ⟨_, hc', fun j => p (m j), fun g => ?_⟩
  obtain ⟨u, hu⟩ := Submodule.Quotient.mk_surjective _ (z g)
  have h1 : (Submodule.Quotient.mk (p := stdG ↥(OL C.LL) ↥C.LL.1 k) (incV C.le k u)) =
      Submodule.Quotient.mk (c g + ((mapM (algebraMap ↥(OL C.LL) ↥C.LL.1) (locOC C M) g).mulVec m - m)) := by
    refine (liftQ_mk C.le k u).symm.trans ?_
    refine Eq.trans ?_ (hcm g)
    exact congrArg (liftQ C.le k) hu
  obtain ⟨n, hn⟩ := (Submodule.Quotient.eq (stdG ↥(OL C.LL) ↥C.LL.1 k)).1 h1
  refine hu.symm.trans ((Submodule.Quotient.eq (stdG (Br.OLL D.nbr i w hw) (Br.LL D.nbr i w hw) k)).2 ?_)
  refine ⟨fun j => ⟨p (n j), hpO _ (n j).2⟩, ?_⟩
  funext j
  have h2 := congrArg p (congrFun hn j)
  have h3 := congrFun (hp g m) j
  change p ((n j : ↥C.LL.1)) = p (IntermediateField.inclusion C.le (u j) - (c g j + ((mapM (algebraMap ↥(OL C.LL) ↥C.LL.1) (locOC C M) g).mulVec m j - m j))) at h2
  change (p (n j) : Br.LL D.nbr i w hw) = u j - (p (c g j) + ((Br.loc D.nbr i w hw M g).mulVec (fun j => p (m j)) j - p (m j)))
  rw [h2, map_sub, map_add, map_sub, hp1, ← h3]

end GlobalTheory.UseLoc.DescHf
