import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.FrobeniusLocalPairs.LiftFactorization
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.FrobeniusLocalPairs.OrbSum
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.FrobeniusLocalPairs.CptCpt
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.FrobeniusLocalPairs.CptConj
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.FrobeniusLocalPairs.MemTwCentConj
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.OrbitalIntegrals.QuotFubiniHolds
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.OrbitalIntegrals.BrMain
import Development.AutomorphicArithmetic.Foundations.Convolution.TwistedLocalOrbits.OrbProper

open MeasureTheory ValuativeRel Matrix GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets
open scoped Classical ENNReal

namespace UpperTheory.Gal.InertialTypesAlt.L

open PositivityTheory.Rg.Tf.Loc UpperTheory.V.Z.Tf.Orb

private theorem kSide (k : Type) [Field k] [CharZero k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (n : ℕ) [MeasurableSpace (GL (Fin n) k)] [BorelSpace (GL (Fin n) k)]
    (μk : Measure (GL (Fin n) k)) (hμ : μk.IsHaarMeasure)
    (hk1 : μk (unitGL (n := Fin n) k : Set (GL (Fin n) k)) = 1)
    (U : Subgroup (GL (Fin n) k)) (f : GL (Fin n) k → ℂ)
    (hL : GlobalTheory.BCT.IsLevel (MonoidHom.id _) (unitGL k) U) (hH : GlobalTheory.BCT.IsHecke U f)
    (γ : GL (Fin n) k) (hγ : IsRegSemisimple γ) (μγ : Measure (Subgroup.centralizer {γ}))
    (hh : μγ.IsHaarMeasure) :
    IsCompact (GlobalTheory.BCT.cptPart (Subgroup.centralizer {γ}) : Set (GL (Fin n) k)) ∧
    ((μγ.real {t : Subgroup.centralizer {γ} |
        (t : GL (Fin n) k) ∈ GlobalTheory.BCT.cptPart (Subgroup.centralizer {γ})} : ℝ) ≠ 0) ∧
    orbIntegralC μk γ μγ f =
      ((μγ.real {t : Subgroup.centralizer {γ} |
        (t : GL (Fin n) k) ∈ GlobalTheory.BCT.cptPart (Subgroup.centralizer {γ})} : ℝ) : ℂ)⁻¹ *
        GlobalTheory.BCT.twOrb (MonoidHom.id _) (unitGL k) γ f := by
  obtain ⟨hLC, hSC, hT2, -, -⟩ := gLTop_holds k n
  haveI := hLC
  haveI := hSC
  haveI := hT2
  obtain ⟨hKo, hKc, -⟩ := unitSB_holds k n
  haveI : ValuativeExtension k k := ⟨fun _ _ => Iff.rfl⟩
  obtain ⟨hgen, hσ1, hTw, -⟩ := untwist_holds k n μk γ
  have hT : Subgroup.centralizer {γ} = GlobalTheory.BCT.twCent (MonoidHom.id (GL (Fin n) k)) γ := by
    ext g
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact Iff.rfl
  have hTcl : IsClosed (Subgroup.centralizer {γ} : Set (GL (Fin n) k)) := by
    rw [hT]
    show IsClosed {g : GL (Fin n) k | g * γ = γ * (MonoidHom.id (GL (Fin n) k)) g}
    exact isClosed_eq (continuous_id.mul continuous_const) (continuous_const.mul continuous_id)
  have hcommA : ∀ t ∈ Subgroup.centralizer {γ}, Commute t γ :=
    fun t ht => Subgroup.mem_centralizer_singleton_iff.1 ht
  have hcomm : ∀ a ∈ Subgroup.centralizer {γ}, ∀ b ∈ Subgroup.centralizer {γ}, Commute a b := by
    intro a ha b hb
    have hm : ∀ t ∈ Subgroup.centralizer {γ},
        Commute (t : Matrix (Fin n) (Fin n) k) (γ : Matrix (Fin n) (Fin n) k) := by
      intro t ht
      have h := Subgroup.mem_centralizer_singleton_iff.1 ht
      show (t : Matrix (Fin n) (Fin n) k) * γ = γ * t
      rw [← Units.val_mul, ← Units.val_mul, h]
    have h := centComm_holds k n (γ : Matrix (Fin n) (Fin n) k) a b hγ (hm a ha) (hm b hb)
    show a * b = b * a
    exact Units.ext (by rw [Units.val_mul, Units.val_mul]; exact h.eq)
  have hC := cptCpt k n γ _ hγ hTcl hcommA
  have hcm : CptMod (Subgroup.centralizer {γ})
      (fun x => f (x⁻¹ * γ * (MonoidHom.id (GL (Fin n) k)) x)) := by
    obtain ⟨D, hD, hDp⟩ := orbProper_holds k k 1 hgen n γ (hTw hγ) (tsupport f) hH.1
    refine ⟨D, hD, fun g hg => ?_⟩
    have hg' : twConj (sigmaGL (1 : Gal(k/k))) g γ ∈ tsupport f := by
      have he : twConj (sigmaGL (1 : Gal(k/k))) g γ = g⁻¹ * γ * g := by
        show g⁻¹ * γ * (sigmaGL (1 : Gal(k/k))) g = g⁻¹ * γ * g
        rw [hσ1 g]
      rw [he]
      exact subset_tsupport f hg
    obtain ⟨t, ht, d, hd, rfl⟩ := hDp g hg'
    refine ⟨t, ?_, d, hd, rfl⟩
    have h1 := (mem_twCent _ _ _).1 ht
    rw [hσ1 t] at h1
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc t * γ = t * (t⁻¹ * γ * t) := by rw [h1]
      _ = γ * t := by group
  obtain ⟨hne, heq⟩ := orbSum (GL (Fin n) k) μk hμ (unitGL k) hKo hKc hk1 (MonoidHom.id _)
    continuous_id γ (Subgroup.centralizer {γ}) hT hcomm hC μγ hh U f hL hH hcm
  exact ⟨hC, hne, heq⟩

theorem matchOfSum : MatchOfSum := by
  unfold MatchOfSum
  intro k E _ _ _ _ _ _ _ _ _ _ _ _ _ σ hgen n _ _ _ _ μE μk hμE hμk hE1 hk1 UE Uk φ f hLE hLk hHE hHk
    hmatch hsurj
  obtain ⟨hgal, hnorm, htw, -, hpair, hnormOf⟩ := dict k E σ hgen n
  obtain ⟨hLCE, hSCE, hT2E, -, -⟩ := gLTop_holds E n
  haveI := hLCE
  haveI := hSCE
  haveI := hT2E
  obtain ⟨hLCk, hSCk, hT2k, -, -⟩ := gLTop_holds k n
  haveI := hLCk
  haveI := hSCk
  haveI := hT2k
  obtain ⟨hKo, hKc, -⟩ := unitSB_holds E n
  obtain ⟨-, -, hcontE⟩ := extCont_holds k E
  have hgalg : ∀ g : GL (Fin n) E, (GlobalTheory.LBC.galAct σ n) g = (sigmaGL σ) g :=
    fun g => DFunLike.congr_fun hgal g
  have hθc : Continuous (GlobalTheory.LBC.galAct σ n) := by
    have h := (hcontE n).2 σ
    have he : (⇑(GlobalTheory.LBC.galAct σ n)) = ⇑(sigmaGL (n := Fin n) σ) := funext hgalg
    rw [he]
    exact h
  have hpow : (sigmaGL (n := Fin n) σ) ^ Module.finrank k E = 1 := by
    rw [← sigmaGL_pow, ← IsGalois.card_aut_eq_finrank, pow_card_eq_one', sigmaGL_one]
  refine ⟨?_, ?_⟩
  · intro δ γ h μδ μγ hTw hnh hδ hγh hmap
    obtain ⟨hγ, hchar, hmem⟩ := hpair δ h γ hTw hnh
    obtain ⟨hCk, -, heqk⟩ := kSide k n μk hμk hk1 Uk f hLk hHk γ hγ μγ hγh
    obtain ⟨hTcl, hcomm⟩ := twCent_holds k E σ hgen n δ hTw
    have hT : PositivityTheory.Rg.Tf.Loc.twCent (sigmaGL σ) δ = GlobalTheory.BCT.twCent (GlobalTheory.LBC.galAct σ n) δ := by
      rw [hgal]
      exact htw δ
    have hCE : IsCompact (GlobalTheory.BCT.cptPart (PositivityTheory.Rg.Tf.Loc.twCent (sigmaGL σ) δ) : Set (GL (Fin n) E)) :=
      cptCpt E n (normGL σ δ) _ hTw hTcl (fun t ht => twCent_commute_twNorm (sigmaGL σ) hpow δ ht)
    have hcm : CptMod (PositivityTheory.Rg.Tf.Loc.twCent (sigmaGL σ) δ)
        (fun x => φ (x⁻¹ * δ * (GlobalTheory.LBC.galAct σ n) x)) := by
      obtain ⟨D, hD, hDp⟩ := orbProper_holds k E σ hgen n δ hTw (tsupport φ) hHE.1
      refine ⟨D, hD, fun g hg => ?_⟩
      have hg2 : φ (g⁻¹ * δ * (sigmaGL σ) g) ≠ 0 := by
        rw [← hgalg]
        exact hg
      exact hDp g (subset_tsupport φ hg2)
    obtain ⟨-, heqE⟩ := orbSum (GL (Fin n) E) μE hμE (unitGL E) hKo hKc hE1 (GlobalTheory.LBC.galAct σ n) hθc δ _
      hT hcomm hCE μδ hδ UE φ hLE hHE hcm
    have hvol := cptConj (GL (Fin n) E) (GL (Fin n) k) incl (inclClosed_holds k E n)
      (PositivityTheory.Rg.Tf.Loc.twCent (sigmaGL σ) δ) (Subgroup.centralizer {γ}) h hmem hCk μδ μγ hmap
    have hO : GlobalTheory.BCT.twOrb (GlobalTheory.LBC.galAct σ n) (unitGL E) δ φ =
        GlobalTheory.BCT.twOrb (MonoidHom.id (GL (Fin n) k)) (unitGL k) γ f :=
      hmatch δ (by rw [hnorm]; exact hTw) γ (by rw [hnorm]; exact hchar)
    have hL : twOrbIntegralC (sigmaGL σ) μE δ μδ φ = quotIntegral μE _ μδ
        (fun x => φ (x⁻¹ * δ * (GlobalTheory.LBC.galAct σ n) x)) := by
      refine congrArg (quotIntegral μE _ μδ) (funext fun x => ?_)
      show φ (x⁻¹ * δ * (sigmaGL σ) x) = φ (x⁻¹ * δ * (GlobalTheory.LBC.galAct σ n) x)
      rw [hgalg]
    rw [heqk, hL, heqE, hO, hvol]
  · intro γ μγ hγ hno hγh
    obtain ⟨-, -, heqk⟩ := kSide k n μk hμk hk1 Uk f hLk hHk γ hγ μγ hγh
    rw [heqk]
    have h0 : GlobalTheory.BCT.twOrb (MonoidHom.id (GL (Fin n) k)) (unitGL k) γ f = 0 := by
      by_contra hne
      obtain ⟨δ, hδ⟩ := hsurj γ hγ hne
      exact hno ⟨δ, hnormOf δ γ hγ (by rw [← hnorm]; exact hδ)⟩
    rw [h0, mul_zero]

end UpperTheory.Gal.InertialTypesAlt.L
