import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PeriodComparison
import Development.AbelianVarietyTheory.Definitions.Divisors.JetAnalytic
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TateUnramifiedOfTorsionUnramified
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrysToDRBijective
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsCrystalPairing
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.PolarisationModuleIndex
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ConjugateOrderData
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsPlaceRing
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolarizationFormsCommensurableStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CmTypePeriodIntegralFirst
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CmTypePeriodIntegralSecond
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CmTypePeriodConjugateIntegral
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CmAuxiliarySetReductionGood
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WedgeOrdVpBaseChangeOfNeBot
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsProjectiveModel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsChernExistsUniqueAndIso
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CmTypePeriodProductIntegral
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CmTypePeriodIntegralThird
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.CMVal GlobalTheory.LatVal GlobalTheory.LatJet GlobalTheory.LatModel
open GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds (IsClassZetaVals c_vp cE_vp a0)
open TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.EigLineSumCM

open Classical in

theorem eigK_isInternal_of_cmType : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (c : Ideal (OF E)), c ≠ ⊥ →
    ∀ (R : Type) [CommRing R] [IsDomain R] (K : Type) [Field K] [Algebra R K] [IsFractionRing R K] [DecidableEq (E →+* K)] (H : Type)
    [AddCommGroup H] [Module R H] (I : Type) [Fintype I] (φ : I → E →+* K) (ρ : orderC c →+* Module.End R H)
    (Fil : Submodule R H) (B : LinearMap.BilinForm R H), GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.IsCMLattice φ ρ Fil B →
    GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.IsCMTypeIn φ → 2 * Fintype.card I = Module.finrank ℚ E →
    DirectSum.IsInternal (fun σ : E →+* K ↦ GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.eigK ρ σ) := by
  intro E _ _ _ c hc R _ _ K _ _ _ _ H _ _ I _ φ ρ Fil B hL hT hI
  obtain ⟨hfree, hfin, hrank, hline, -⟩ := hL

  let g : I × Bool → (E →+* K) := fun p => if p.2 then φ p.1 else GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.bar (φ p.1)
  have hg_or : ∀ p : I × Bool, g p = φ p.1 ∨ g p = GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.bar (φ p.1) := by
    rintro ⟨i, b⟩; cases b <;> simp [g]
  have hgbij : Function.Bijective g := by
    constructor
    · rintro ⟨i, b⟩ ⟨j, b'⟩ h
      have hij : i = j := by
        obtain ⟨k, -, hk⟩ := hT (g (i, b))
        have h1 := hk i (hg_or (i, b))
        have h2 := hk j (by rw [h]; exact hg_or (j, b'))
        rw [h1, h2]
      subst hij
      have hne := GlobalTheory.LowerOps.bar_ne_self (φ i)
      cases b <;> cases b'
      · rfl
      · have h' : GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.bar (φ i) = φ i := by simpa [g] using h
        exact absurd h' hne
      · have h' : φ i = GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.bar (φ i) := by simpa [g] using h
        exact absurd h'.symm hne
      · rfl
    · intro σ
      obtain ⟨i, hi, -⟩ := hT σ
      rcases hi with h | h
      · exact ⟨(i, true), by simp [g, h]⟩
      · exact ⟨(i, false), by simp [g, h]⟩
  have hcard : Nat.card (E →+* K) = Module.finrank ℚ E := by
    rw [← Nat.card_eq_of_bijective g hgbij, Nat.card_prod, Nat.card_eq_fintype_card, Nat.card_eq_fintype_card,
      Fintype.card_bool, ← hI, mul_comm]
  let f : orderC c → Module.End K (K ⊗[R] H) := fun a => (ρ a).baseChange K
  have hcomm : ∀ a b, Commute (f a) (f b) := fun a b => by
    show (ρ a).baseChange K * (ρ b).baseChange K = (ρ b).baseChange K * (ρ a).baseChange K
    rw [← LinearMap.baseChange_mul, ← LinearMap.baseChange_mul, ← map_mul, ← map_mul, mul_comm]
  have hind0 := Module.End.independent_iInf_maxGenEigenspace_of_forall_mapsTo f
    (fun i j φ => Module.End.mapsTo_maxGenEigenspace_of_comm (hcomm j i) φ)
  have hinj : Function.Injective (fun σ : E →+* K => fun a : orderC c => σ a) := fun σ σ' h =>
    GlobalTheory.EigLineSum.ringHom_eq_of_eq_on_orderC hc (fun a => congrFun h a)
  have hind : iSupIndep (fun σ : E →+* K => GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.eigK ρ σ) :=
    (hind0.comp hinj).mono fun σ => iInf_mono fun a => Module.End.eigenspace_le_maxGenEigenspace
  haveI : Finite (E →+* K) := Finite.of_surjective g hgbij.2
  haveI := Fintype.ofFinite (E →+* K)
  have htot : Module.finrank K (K ⊗[R] H) = Module.finrank ℚ E := by
    rw [Module.finrank_baseChange, hrank]
  have hinjD : Function.Injective (DirectSum.coeLinearMap (fun σ : E →+* K => GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.eigK ρ σ)) :=
    hind.dfinsupp_lsum_injective
  have hdim : Module.finrank K (DirectSum (E →+* K) fun σ => GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.eigK ρ σ) =
      Module.finrank K (K ⊗[R] H) := by
    rw [Module.finrank_directSum, htot, ← hcard, Nat.card_eq_fintype_card]
    simp [hline]
  exact ⟨hinjD, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).1 hinjD⟩

end GlobalTheory.EigLineSumCM
