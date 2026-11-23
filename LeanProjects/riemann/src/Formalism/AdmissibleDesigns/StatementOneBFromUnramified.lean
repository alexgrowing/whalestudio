import Formalism.AdmissibleDesigns.StatementOneBChangedOfOpen
import Formalism.AdmissibleDesigns.HRhoFull
import Formalism.AdmissibleDesigns.FirstCharacterIndexNeZero
import Formalism.AdmissibleDesigns.PhiWRhoT
import Formalism.AdmissibleDesigns.RowTieInOf
import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.BaseLin
import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.BlochKatoAnnihilatorAboveL
import Development.AutomorphicArithmetic.ResidueCharacters.LenLeTorsion
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WachHypothesisCrystallineLattices
import Formalism.AdmissibleDesigns.AdmG5OfAdm51AdmG5
import Formalism.SharpRestriction.LevelLetterCocycles.QpowOfTw
import Formalism.SharpRestriction.LevelLetterCocycles.WildPro

variable [hT2Core : Fact ReciprocityTheory.ChartRestriction.T2.Core] [hH0Fin : Fact Formalism.MainNotions.N.K.H0.FinCore]

noncomputable section

open Finset Classical Formalism.BasicNotions

namespace Formalism.MainNotions.N.K.Closed

open Formalism.NG Formalism.RepresentationBoundsCohomology.BR Formalism.RepresentationBoundsCohomology.TorsionBoundCyclotomic Formalism.RepresentationBoundsCohomology.JL Formalism.RepresentationBoundsCohomology.JT Formalism.RepresentationBoundsCohomology.JS Formalism.RepresentationBoundsCohomology.SplitClassesAll Formalism.RepresentationBoundsCohomology.LocallyConstantCohomology Formalism.RepresentationBoundsCohomology.FIN
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.RepresentationBoundsCohomology.LOC
open ReciprocityTheory.ChartRestriction.T2 (PadicCoeff FracTop IsFGTop cupFG)
open Formalism.RepresentationBoundsCohomology.ringDataObjects (RingData RingDef)
open Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.N.K Formalism.RepresentationBoundsCohomology.SF Formalism.MainNotions.N.K.St

attribute [local instance 2000] Topo.fracTopology Topo.rTopology

section Plug

variable {D : D7} (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i)))
  (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i)
  (dc : TruncatedSeriesCountingIdentities.Decl D i) (g0 : GE D.nd) (eB e₁ s : D.nd.X i → MatN D.nd i)
  (Dd : RingData (D.nd.O i) (D.nd.X i) (Fin D.R.nV) (GE D.nd) D.R.t (RepresentationBoundsCohomology.blk D.R))
  [∀ k, SMulCommClass Dd.R' (D.nd.O i) (blockRestrictedRepresentationType (RepresentationBoundsCohomology.blk D.R) Dd.ρk k)]
  [∀ k, IsScalarTower Dd.T' Dd.R' (blockRestrictedRepresentationType (RepresentationBoundsCohomology.blk D.R) Dd.ρk k)]
  (hD : RingDef (D.nd.O i) (D.nd.T i) (RepresentationBoundsCohomology.repX D.nd r) π (chiU D.nd i 1) (epsU D.nd i) g0 eB e₁ s Dd)
  (hc : TruncatedSeriesCountingIdentities.FamilyContinuous (D := D) i r) (cB : ℕ)

include hD hc in
set_option maxHeartbeats 4000000 in
set_option synthInstance.maxHeartbeats 400000 in

theorem tbTarget_row (hN : RepresentationBoundsCohomology.NormAt D.nd r ρ π) (hTB : EmbeddingTypes.admTB i r π dc cB) (hG : K.SelfGood i)
    (hTie : TruncatedSeriesCountingIdentities.LocalCoefficientCompatibility i) (hF : TruncatedSeriesCountingIdentities.FontaineAtPlacesOverL i) (hG2 : TruncatedSeriesCountingIdentities.admG2 i r ρ π) (hdec : TruncatedSeriesCountingIdentities.SemisimpleDecomposition i r ρ π) :
    TB.TBTarget i dc Dd cB :=
  haveI := Topo.finite_RD i r π g0 eB e₁ s Dd hD
  TBb.trivial_bound_target_of_psi i dc r ρ π g0 eB e₁ s Dd cB hD hN hc (TB.trivialBoundAtRows_of_admTB i dc r π cB hG hTB) hTie
    (fun _w hw _ c _ Cd => TBa.ytTarget_of π ρ (Topo.finite_RD i r π g0 eB e₁ s Dd hD) hF hG2 hw
      (TBa.ytEmbW_of i dc r Dd hw (StC.embRW_of i dc r Dd hD hw) (TBa.lineW_of i r ρ π hdec hw))
      (KOrb.msContW i r hc hw) c Cd)

end Plug

section PlugN

variable {D : D7} (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i)))
  (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i)
  (dc : TruncatedSeriesCountingIdentities.Decl D i) (g0 : GE D.nd) (eB e₁ s : D.nd.X i → MatN D.nd i)
  (Dd : RingData (D.nd.O i) (D.nd.X i) (Fin D.R.nV) (GE D.nd) D.R.t (RepresentationBoundsCohomology.blk D.R))
  [∀ k, SMulCommClass Dd.R' (D.nd.O i) (blockRestrictedRepresentationType (RepresentationBoundsCohomology.blk D.R) Dd.ρk k)]
  [∀ k, IsScalarTower Dd.T' Dd.R' (blockRestrictedRepresentationType (RepresentationBoundsCohomology.blk D.R) Dd.ρk k)]
  (hD : RingDef (D.nd.O i) (D.nd.T i) (RepresentationBoundsCohomology.repX D.nd (Norm.rN i r ρ π)) π (chiU D.nd i 1) (epsU D.nd i)
    g0 eB e₁ s Dd)
  (hc : TruncatedSeriesCountingIdentities.FamilyContinuous (D := D) i (Norm.rN i r ρ π))
  (hT : Dd.Top (D.nd.T i) (RepresentationBoundsCohomology.one_le_letterBlockLength D.R))
  (hrk : ((Dd.ρk 0 Dd.e₁).map (algebraMap (D.nd.O i) (FractionRing (D.nd.O i)))).rank = 1)
  (lenRow : HeightOneSpectrum (𝓞 D.host.E) → ℚ) (cB : ℕ)

set_option maxHeartbeats 4000000 in
set_option synthInstance.maxHeartbeats 400000 in

theorem open_inputs_at_normalized (g2 : TruncatedSeriesCountingIdentities.admG2 i r ρ π) (g4 : TruncatedSeriesCountingIdentities.admG4 i r) (g5 : TruncatedSeriesCountingIdentities.admG5 i r) (g5x : TruncatedSeriesCountingIdentities.TameGeneratorConditions i)
    (dcm : TruncatedSeriesCountingIdentities.SemisimpleDecomposition i r ρ π) (font : TruncatedSeriesCountingIdentities.FontaineAtPlacesOverL i) (fin : LargeLevelLemmas.tateH1FinitenessAtPlacesOver i) (tie : TruncatedSeriesCountingIdentities.LocalCoefficientCompatibility i)
    (hG : K.SelfGood i) (hQP : QS.QPow i) (hTB : EmbeddingTypes.admTB i (Norm.rN i r ρ π) π dc cB) :
    Final.RhoOpenA i (Norm.rN i r ρ π) ρ π dc g0 eB e₁ s Dd hD hc hT hrk ∧
    Final.TBOpen i (Norm.rN i r ρ π) π dc g0 eB e₁ s Dd hD hc cB ∧
    Final.ChiOpen i (Norm.rN i r ρ π) π dc g0 eB e₁ s Dd hD hc ∧
    Final.FirstLocalConditionOpen i (Norm.rN i r ρ π) π dc g0 eB e₁ s Dd hD hc ∧
    StD.RowTieIn i (Norm.rN i r ρ π) ρ π dc g0 eB e₁ s Dd hD hc := by
  have hN := Norm.normAt_rN i r ρ π
  have g4' := Norm.admG4_rN i r ρ π dcm g4
  have g5' := Norm.admG5_rN i r ρ π dcm g5
  have g2' := Norm.admG2_rN i r ρ π dcm g2
  have dcm' := Norm.decomposes_normalized i r ρ π
  refine ⟨StB.hRho_rN i r ρ π dc g0 eB e₁ s Dd hD hc hT hrk g4 dcm fin, ?_, ?_, ?_, ?_⟩
  · exact StC.tb_of_target i (Norm.rN i r ρ π) π dc g0 eB e₁ s Dd hD hc cB
      (tbTarget_row i (Norm.rN i r ρ π) ρ π dc g0 eB e₁ s Dd hD hc cB hN hTB hG tie font g2' dcm')
  · exact StC.chi_of i (Norm.rN i r ρ π) ρ π dc g0 eB e₁ s Dd hD hc hN g4' dcm' g5' g5x hQP
  · exact StC.first_local_clause_of i (Norm.rN i r ρ π) ρ π dc g0 eB e₁ s Dd hD hc hN g4' dcm' g5' g5x hQP
  · exact KRowA.rowTieIn_of i (Norm.rN i r ρ π) ρ π dc g0 eB e₁ s Dd hD hc
      (RowB.rowMat_SN i r ρ π dc g0 eB e₁ s Dd hD hc) (RowB.orbC_S i (Norm.rN i r ρ π) π dc g0 eB e₁ s Dd hD hc)

end PlugN

section Inputs

theorem wildTriv_holds : Formalism.MainNotions.N.WildTriv := by
  intro E Ω _ _ _ _ _ l hl v A hA hv M _ φ hker htors σ hσ
  unfold IsPlaceOver at hA
  haveI := v.isPrime
  haveI : Finite (𝓞 E ⧸ v.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot v.asIdeal v.ne_bot
  obtain ⟨p, hp⟩ : ∃ p, CharP (𝓞 E ⧸ v.asIdeal) p := ⟨ringChar _, ringChar.charP _⟩
  have hpp : p.Prime := CharP.char_is_prime (𝓞 E ⧸ v.asIdeal) p
  have hpv : ((p : ℕ) : 𝓞 E) ∈ v.asIdeal := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_natCast]
    exact CharP.cast_eq_zero _ p
  have hpl : p ≠ l := by
    rintro rfl
    exact hv hpv
  have hval : A.valuation ((p : ℕ) : Ω) < 1 := by
    have h := (hA (p : 𝓞 E)).mpr hpv
    simpa [map_natCast] using h
  obtain ⟨k, hk⟩ := Formalism.MainNotions.N.KillingConditions.WildPf.wildProP E Ω A p hpp hval σ hσ φ.ker hker
  obtain ⟨n, hn⟩ := htors σ
  have h1 : φ σ ^ (p ^ k) = 1 := by
    rw [← map_pow]
    exact MonoidHom.mem_ker.mp hk
  have hcop : Nat.Coprime (p ^ k) (l ^ n) := Nat.Coprime.pow k n ((Nat.coprime_primes hpp hl).mpr hpl)
  have hc2 : Nat.Coprime (orderOf (φ σ)) (l ^ n) :=
    Nat.Coprime.coprime_dvd_left (orderOf_dvd_of_pow_eq_one h1) hcop
  exact orderOf_eq_one_iff.mp (Nat.Coprime.eq_one_of_dvd hc2 (orderOf_dvd_of_pow_eq_one hn))

theorem selfGood_rec {D : D7} (i : D.nd.Loc) : K.SelfGood i :=
  fun w hw => D.self_good i w hw

theorem qPow_rec {D : D7} (i : D.nd.Loc) : QS.QPow i :=
  Formalism.MainNotions.N.qpow_of_tw wildTriv_holds D i

end Inputs

section Closed

variable {D : D7} (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i)))
  (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i) (dc : TruncatedSeriesCountingIdentities.Decl D i)
  (lenRow : HeightOneSpectrum (𝓞 D.host.E) → ℚ) (e' : HeightOneSpectrum (𝓞 D.host.E) → ℕ) (cB : ℕ)

set_option maxHeartbeats 4000000 in
set_option synthInstance.maxHeartbeats 400000 in

theorem theorem_n5_from_inputs (g1 : TruncatedSeriesCountingIdentities.admG1 i r) (g2 : TruncatedSeriesCountingIdentities.admG2 i r ρ π) (g3 : TruncatedSeriesCountingIdentities.admG3 i r ρ π) (g4 : TruncatedSeriesCountingIdentities.admG4 i r)
    (g5 : TruncatedSeriesCountingIdentities.admG5 i r) (g5x : TruncatedSeriesCountingIdentities.TameGeneratorConditions i) (g6 : TruncatedSeriesCountingIdentities.admG6 i r) (bk : TruncatedSeriesCountingIdentities.admBK i) (bka : LargeLevelLemmas.BlochKatoAnnihilators i)
    (ct : TruncatedSeriesCountingIdentities.FamilyContinuous i r) (dcm : TruncatedSeriesCountingIdentities.SemisimpleDecomposition i r ρ π) (font : TruncatedSeriesCountingIdentities.FontaineAtPlacesOverL i) (fin : LargeLevelLemmas.tateH1FinitenessAtPlacesOver i)
    (tie : TruncatedSeriesCountingIdentities.LocalCoefficientCompatibility i) (a51 : LargeLevelLemmas.adm51 i r ρ π) (unr : StD.UnrIn i dc) :
    TruncatedSeriesCountingIdentities.LengthBoundAtPlaces i r ρ π dc lenRow → TruncatedSeriesCountingIdentities.LiftExponentAtPlaces i r dc e' → EmbeddingTypes.admTB i r π dc cB →
      TruncatedSeriesCountingIdentities.GlobalLatticeIndexTheorem i ρ π dc lenRow e' cB := by
  intro hROW hLIFT hTB
  refine Final.theorem_n5_of_open_b (i := i) (r := r) (ρ := ρ) (π := π) (dc := dc) (lenRow := lenRow) (e' := e') (cB := cB)
    g1 g2 g3 g5x g6 bk bka ct dcm font fin a51 unr (selfGood_rec i) ?_ hROW hLIFT hTB
  intro _ _ hTB' _ g0 eB e₁ s Dd _ hD hc hT hrk
  haveI : ∀ k, IsScalarTower Dd.T' Dd.R' (blockRestrictedRepresentationType (RepresentationBoundsCohomology.blk D.R) Dd.ρk k) := by
    intro k
    refine ⟨fun f a m => ?_⟩
    have hD' := hD
    dsimp only [RingDef] at hD'
    obtain ⟨-, -, -, -, -, -, -, -, h9, -, h11, -, -, -, -, -, h17, h18, -, -, -, -⟩ := hD'
    have hπ : Dd.ρπ (f • a) = ((f : Dd.X' → D.nd.O i) Dd.π') • Dd.ρπ a := by
      apply Matrix.map_injective (IsFractionRing.injective (D.nd.O i) (FractionRing (D.nd.O i)))
      dsimp only
      rw [h17, h9, ← h17 a]
      ext u v
      simp [map_mul]
    have hk : Dd.ρk k (f • a) = ((f : Dd.X' → D.nd.O i) Dd.π') • Dd.ρk k a := by
      rw [← h18, ← h18, hπ]
      ext u v
      rfl
    rw [h11 f k (a • m)]
    refine funext fun j => ?_
    show (∑ x, (Dd.ρk k (f • a)) j x • m x) = ((f : Dd.X' → D.nd.O i) Dd.π') • ∑ x, (Dd.ρk k a) j x • m x
    rw [hk]
    simp only [Matrix.smul_apply, smul_eq_mul, mul_smul, Finset.smul_sum]
  exact open_inputs_at_normalized (i := i) (r := r) (ρ := ρ) (π := π) (dc := dc) (g0 := g0) (eB := eB) (e₁ := e₁) (s := s)
    (Dd := Dd) (hD := hD) (hc := hc) (hT := hT) (hrk := hrk) (cB := cB)
    g2 g4 g5 g5x dcm font fin tie (selfGood_rec i) (qPow_rec i) hTB'

end Closed

section Stmts

end Stmts

end Formalism.MainNotions.N.K.Closed

end
