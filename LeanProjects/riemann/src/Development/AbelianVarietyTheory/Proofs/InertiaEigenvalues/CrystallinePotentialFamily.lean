import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsSummandTw
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PotentialFamilySummandRestrictionStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsComplementedSubrepLocalMatrixRepTwistedSumStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TateDualTwistedSumSummandIsDeRhamStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsDualLatticeIsOpenPerfectPairingStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.InvariantsStableLatticeModIrreducibleEqBot
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EqZeroOfTmulOne
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocChiEpsUEqCycLL
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GoodORingOfIntegers

open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module GlobalTheory.Pass Formalism.MainNotions.PairedCharacterCondition GlobalTheory.Pass.LocDual

noncomputable section

namespace GlobalTheory.Pass.LocDualU

theorem dualLatLe_of {G : Type} [Group G] [TopologicalSpace G] [CompactSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR) {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] [IsDomain O] [IsFractionRing O LL]
    (U U' : GRep G Qp LL O) (LT : Lattice (O := O) U.ρ) (P : U.V →ₗ[LL] U'.V →ₗ[LL] LL)
    (LT' : Lattice (O := O) U'.ρ) (hLT' : IsDualLat1 PD LT LT' P) (hopen : IsOpen (LT'.T : Set U'.V)) (b : ℕ)
    (h : finrank LL (FiniteCohomology PD U'.ρ) + finrank O ↥LT.T ≤ b) : DualLatLe PD U U' LT P b :=
  ⟨LT', hLT', by rw [GlobalTheory.TopSteps.FinSummand.finrank_h1fT PD LT' hopen]; exact h⟩

set_option maxHeartbeats 1000000 in
set_option synthInstance.maxHeartbeats 400000 in

theorem main : ∀ (D : D7), FontaineAtPlacesOverL (D := D) → PotDRL D.loc → admBK (D := D) → ∀ (i : D.nd.Loc)
    (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))), GoodR D.nd i r →
    ∀ (Xs : Set (D.nd.X i)) (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i)),
      finrank ℚ_[D.nd.l i] (Br.Kw D.nbr i w hw) = 1 → ∀ n : ℕ,
      PotFam i w hw (fun x : ↥Xs => rTwO D.nd i r x) n →
    ∀ (k : ℕ) (M : GE D.nd →* Matrix (Fin k) (Fin k) (D.nd.O i)) (hSub : SubTw i r Xs M),
      IsDR (Br.PD D.loc D.nbr i w hw) (locU i w hw M hSub.1).ρ ∧
      ∃ (U' : GRep (Br.G D.nbr i w hw) ℚ_[D.nd.l i] (Br.LL D.nbr i w hw) (Br.OLL D.nbr i w hw))
        (PU : (locU i w hw M hSub.1).V →ₗ[Br.LL D.nbr i w hw] U'.V →ₗ[Br.LL D.nbr i w hw] Br.LL D.nbr i w hw),
        IsSubFam (fun x : ↥Xs => Br.loc D.nbr i w hw (rDuO D.nd i r x)) U' ∧
        DualLatLe (Br.PD D.loc D.nbr i w hw) (locU i w hw M hSub.1) U' (Br.locLat D.nbr i w hw M) PU (2 * k) := by
  intro D hF hDR hBK i r hR Xs w hw hK n hPot k M hSub
  have hSum := GlobalTheory.T.isComplementedSubrep_localMatrixRep_twistedSum D i r hR Xs w hw k M hSub
  obtain ⟨hU, X', PX, hD1, hSF⟩ := GlobalTheory.T.potential_family_summand_restriction D hF hDR i r hR Xs w hw n hPot _ hSum
  have hX' := GlobalTheory.T.tateDual_twistedSumSummand_isDeRham D hF hDR i r hR Xs w hw n hPot _ hSum X' PX hD1
  have hGood := goodO_ringOfIntegers (D.nd.l i) (D.nbr i w hw).LL
  have hcyc : ∀ g, ∃ u : (Br.OLL D.nbr i w hw)ˣ, ((cycLL (Br.PD D.loc D.nbr i w hw) (Br.LL D.nbr i w hw) g :
      (Br.LL D.nbr i w hw)ˣ) : Br.LL D.nbr i w hw) = algebraMap (Br.OLL D.nbr i w hw) (Br.LL D.nbr i w hw) (u : Br.OLL D.nbr i w hw) := by
    intro g
    rw [← GlobalTheory.CycBridge.locChi_epsU_eq_cycLL D i w hw]
    exact ⟨Units.map (D.nbr i w hw).eO.toRingHom.toMonoidHom (epsU D.nd i ((decS D.nd w) (Br.iota D.nbr i w hw g))), rfl⟩
  obtain ⟨LT', hLT', hopen⟩ := GlobalTheory.T.exists_dualLattice_isOpen_perfectPairing (Br.PD D.loc D.nbr i w hw) hGood hcyc _ X' PX hD1
    (Br.locLat D.nbr i w hw M)
  refine ⟨hU, X', PX, hSF, ?_⟩
  obtain ⟨⟨hdom, -, hfr⟩, -⟩ := hGood
  haveI := hdom
  haveI := hfr
  haveI : CompactSpace (Br.G D.nbr i w hw) := GlobalTheory.BlochKatoIntegralScalars.compactSpace_GK _
  refine dualLatLe_of _ _ X' _ PX LT' hLT' hopen _ ?_
  have h2 := GlobalTheory.Pass.RankDeRham.finrank_H1f_le (D.nd.l i) (D.loc (D.nd.l i)) (D.nbr i w hw).Kw (D.nbr i w hw).LL hK
    (hBK (D.nd.l i) (D.nbr i w hw).Kw) X' hX'
  have h3 : finrank (Br.LL D.nbr i w hw) X'.V = k := by
    rw [← hD1.2.2.2]
    exact Module.finrank_fin_fun _
  have h4 : finrank (Br.OLL D.nbr i w hw) ↥(Br.locLat D.nbr i w hw M).T = k := by
    have e := LinearEquiv.ofInjective _ (stdG_inj (O := Br.OLL D.nbr i w hw) (LL := Br.LL D.nbr i w hw) Subtype.val_injective k)
    exact (LinearEquiv.finrank_eq e).symm.trans (Module.finrank_fin_fun _)
  have h5 : finrank (Br.LL D.nbr i w hw) (FiniteCohomology (Br.PD D.loc D.nbr i w hw) X'.ρ) ≤ k := h3 ▸ h2
  exact le_trans (Nat.add_le_add h5 h4.le) (by omega)

end GlobalTheory.Pass.LocDualU

end
