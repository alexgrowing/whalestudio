import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.AAcrossOf
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.PolarizedLinkage.CompatTOf
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.QuadraticCharpolySplitting.ThruLoc
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.QuadraticCharpolySplitting.RcChars
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.PlainTorExistsChars
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SupercuspidalSupportTwistNuCharacters
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CardFiberEqOfSumEq
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalArtinExistsHolds
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.WeilDeligneParamMonodromyEqZeroIff
import Development.AutomorphicArithmetic.Foundations.LocalLanglands.LocalCentralUnits.RecTExists
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.GammaLaurentFactors.LocalEmbeddingNorms.SuppFacts

noncomputable section

open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N Polynomial GlobalTheory.CuspRep GlobalTheory.WeilDeligne
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.LocLanglands GlobalTheory.GalOfCusp UpperTheory.Zero.LLC UpperTheory.V.Af UpperTheory.V.Z.Gam
open UpperTheory.GalN.V GroundTheory.Global.SemiLocal UpperTheory.V.Published UpperTheory.V.Z.ImaginaryQuadraticEtaCharacter

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.V.Z.Win

private theorem exists_eq_of_prod {M : Type} [Monoid M] {n : ℕ} (f g : Fin n → (M →* ℂ))
    (h : ∀ x, ∏ j, (X - C (f j x)) = ∏ j, (X - C (g j x))) (j : Fin n) : ∃ i, g i = f j := by
  have hc := GlobalTheory.CharDeg.card_fiber_eq_of_sum_eq f g (fun x => GlobalTheory.CharDeg.sum_eq_of_prod_eq _ _ (h x)) (f j)
  haveI : Nonempty {i // f i = f j} := ⟨⟨j, rfl⟩⟩
  haveI : Finite {i // g i = f j} := inferInstance
  have hpos : 0 < Nat.card {i // g i = f j} := hc ▸ Nat.card_pos
  obtain ⟨⟨i, hi⟩⟩ := (Nat.card_pos_iff.1 hpos).1
  exact ⟨i, hi⟩

private theorem isPlaceOver_of_over {K L Ω : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Field Ω] [Algebra K L]
    [Algebra K Ω] [Algebra L Ω] [IsScalarTower K L Ω] {A : ValuationSubring Ω} {v : HeightOneSpectrum (𝓞 K)}
    (w : PlacesOver L v) (h : IsPlaceOver A w.1) : IsPlaceOver A v := by
  have e : w.1.under (𝓞 K) = v := by
    ext1
    exact (Ideal.over_def w.1.asIdeal v.asIdeal).symm
  exact e ▸ GlobalTheory.AboveL.SatBC.isPlaceOver_under h

theorem _root_.UpperTheory.V.Z.Win.thruAway : ThruAway := by
  intro hPR hRow K L Ω _ _ _ _ _ _ _ _ _ _ _ _ l _ ι n hn r hc hIne P hreg hpol hatt v hv _ w t hwin s hs ζ hζ hmem
  obtain ⟨σ, hσ, hsup⟩ := hs
  haveI : FiniteDimensional K L := Module.Finite.of_restrictScalars_finite ℚ K L
  haveI : Algebra.IsAlgebraic L Ω := Algebra.IsAlgebraic.tower_top (K := K) L
  haveI : IsAlgClosure L Ω := ⟨IsAlgClosure.isAlgClosed K, inferInstance⟩
  haveI : CharZero (w.1.adicCompletion L) := charZero_of_injective_algebraMap (algebraMap L _).injective
  obtain ⟨A, hA⟩ := exists_isPlaceOver Ω w.1
  have hAv : IsPlaceOver A v := isPlaceOver_of_over w hA
  have hlv : ((l : ℕ) : 𝓞 K) ∉ v.asIdeal := fun k => by simpa using hv.1 k
  have hlw : ((l : ℕ) : 𝓞 L) ∉ w.1.asIdeal := fun k => hlv (by
    rw [Ideal.over_def w.1.asIdeal v.asIdeal, Ideal.under, Ideal.mem_comap]
    simpa using k)
  set rL : G L Ω →* GL (Fin n) (Qbar l) := r.comp (AlgEquiv.restrictScalarsHom K : G L Ω →* G K Ω) with hrL
  have hcL : Continuous rL := hc.comp (UpperTheory.V.Af.continuous_restrictScalarsHom K L Ω)
  obtain ⟨rc, hrc⟩ := UpperTheory.Zero.LLC.recTExists L Ω A w.1 hA
  obtain ⟨HT, -, hC⟩ := UpperTheory.V.Z.Win.compatTOf hRow hPR L Ω l ι n (by omega) rL P hcL hreg hpol hatt
  obtain ⟨hPT, hTor, hMono⟩ := hPR L Ω A w.1 hA rc hrc n P t hwin σ hσ
  have hwd : IsWDOf ι rL (rc (algNorm σ)) := (((hC w.1 σ hσ).1 A hA rc hrc).1 hlw).isWDOf ⟨hTor, hMono⟩
  have hpolW : ∀ g : Weil hA, (rc (algNorm σ)).charPol g = ((rL g : Matrix (Fin n) (Fin n) (Qbar l)).charpoly).map ι.toRingHom := fun g => by
    rw [← hwd.wdOf_eq hlw]
    exact charPol_wdOf hlw ι (Units.continuous_val.comp hcL) g
  obtain ⟨a, ha, hLaws⟩ := hrc
  obtain ⟨aK, haK⟩ := GlobalTheory.localArtinExists_holds K Ω A v hAv
  obtain ⟨ξ, hξ, hsupx, -⟩ := GlobalTheory.RoadU.plainTor_exists_chars (w.1.adicCompletion L) (IrrGL.of σ.ρ σ.smooth σ.irred) hPT
  let c : ℂ := (((1 - (n : ℝ)) / 2 : ℝ) : ℂ)
  let ξ' : Fin n → ((w.1.adicCompletion L)ˣ →* ℂˣ) := fun j => ξ j * absPow _ c
  have hξ' : ∀ j, IsSmoothChar (ξ' j) := fun j => (hξ j).mul (GlobalTheory.LocGL.isSmoothChar_absPow _)
  have hsup' : HasSupport (algNorm σ).rep (GlobalTheory.RoadU.chars ξ' hξ') :=
    (GlobalTheory.RoadU.TwistSupp.supp_nu_chars (w.1.adicCompletion L) (IrrGL.of σ.ρ σ.smooth σ.irred) n ξ ξ' hξ hξ' c fun _ => rfl).1.1 hsupx
  have hpolC : ∀ g : Weil hA, (rc (algNorm σ)).charPol g = ∏ j, (X - C ((ξ' j (a g) : ℂˣ) : ℂ)) := fun g =>
    charPol_of_chars hLaws _ ξ' hξ' hsup' g
  obtain ⟨hG, hZ⟩ := GlobalTheory.geometricLemma_and_zelevinskyPolynomialRing
  have hse : s = GlobalTheory.RoadU.chars ξ hξ := GlobalTheory.LocGL.SupportUnique.hasSupport_unique hG GlobalTheory.Laid.bzfin_holds hZ _
    (IrrGL.of σ.ρ σ.smooth σ.irred) _ _ (hsup.of_equiv (IrrGL.equivOf σ.ρ σ.smooth σ.irred)) hsupx
  obtain ⟨j, -, hj⟩ := Multiset.mem_map.1 (hse ▸ hmem)
  have hζj : ξ j = ζ := IrrGL.ofChar_inj.1 hj
  obtain ⟨κ, -, hκ⟩ := hIne v hlv A hAv
  let θ : Fin n → (Weil hAv →* ℂˣ) := fun i =>
    (Units.map (ι.toRingHom : Qbar l →* ℂ)).comp ((κ i).comp (Subgroup.inclusion (Weil_le_Dec hAv)))
  let f : Fin n → (Ine (F := L) A →* ℂ) := fun j => (Units.coeHom ℂ).comp ((ξ' j).comp (a.comp (ineIncl hA)))
  let g : Fin n → (Ine (F := L) A →* ℂ) := fun i =>
    (Units.coeHom ℂ).comp ((θ i).comp ((ineIncl hAv).comp (ineRes (K := K))))
  have hfg : ∀ x, ∏ j, (X - C (f j x)) = ∏ i, (X - C (g i x)) := by
    intro x
    have e1 := hpolC (ineIncl hA x)
    rw [hpolW] at e1
    have e3 : ((rL (ineIncl hA x : G L Ω) : GL (Fin n) (Qbar l)) : Matrix (Fin n) (Fin n) (Qbar l)).charpoly =
        ∏ i, (X - C ((κ i ⟨_, Weil_le_Dec hAv (Ine_le_Weil hAv (ineRes (K := K) x).2)⟩ : (Qbar l)ˣ) : Qbar l)) :=
      hκ ⟨_, Weil_le_Dec hAv (Ine_le_Weil hAv (ineRes (K := K) x).2)⟩ (ineRes (K := K) x).2
    rw [e3, Polynomial.map_prod] at e1
    refine e1.symm.trans (Finset.prod_congr rfl fun i _ => ?_)
    simp [g, θ]
    rfl
  obtain ⟨i, hi⟩ := exists_eq_of_prod f g hfg j
  have hθ : ∀ x : Ine (F := L) A, θ i (ineIncl hAv (ineRes (K := K) x)) = ξ' j (a (ineIncl hA x)) := fun x =>
    Units.ext (DFunLike.congr_fun hi x)
  obtain ⟨χ, hχ, hx⟩ := exists_char_of_ine haK ha (hξ' j) (θ i) hθ
  refine ⟨χ⁻¹, hχ.inv, fun x hx1 => ?_⟩
  have e := hx x (ord_eq_zero_iff.2 hx1)
  have e' : ξ' j x = ξ j x := by
    simp only [ξ', MonoidHom.mul_apply, isUnram_absPow _ c x hx1, mul_one]
  have e2 : nm w x = GlobalTheory.BCChar.normU v w.1 x := rfl
  rw [MonoidHom.mul_apply, MonoidHom.comp_apply, MonoidHom.inv_apply, ← hζj, ← e', e, e2, mul_inv_cancel]

end UpperTheory.V.Z.Win
