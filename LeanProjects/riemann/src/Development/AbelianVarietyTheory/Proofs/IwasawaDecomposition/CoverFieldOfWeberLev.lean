import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HoldsUIff
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.TupPrimeEmpty
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.GeometricallyIrreducibleComponentsWeberValues
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.CmHostRootComplexEqPmSqrt
import Development.AbelianVarietyTheory.Proofs.HeightProofs.CmCurveTorsionDefinedOverOfWeberValues
import Development.AbelianVarietyTheory.Proofs.HeightProofs.InvariantIsAlgebraic
import Development.AbelianVarietyTheory.Proofs.HeightProofs.WeberValuesFiniteAlgebraicPermuted
import Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsRichSmall
import Development.AbelianVarietyTheory.Proofs.HeightProofs.CardKPNeZero
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ResCharConj

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Host GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting NumberField IsDedekindDomain
open Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.L2.Pj GlobalTheory.FieldSize GlobalTheory.FinalJoin
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.Top.Bl.CoverAt

theorem exists_finset_weberIn (r : ℂ) (M : ℕ) (hM : M ≠ 0) : ∃ S : Finset ℂ, (∀ z ∈ S, IsAlgebraic ℚ z) ∧
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E), H.rt0 = r →
      ∀ F : IntermediateField ℚ ℂ, (∀ z ∈ S, z ∈ F) → WeberIn H F M := by
  by_cases h : ∃ (E : Type) (_ : Field E) (_ : NumberField E) (_ : IsCMField E) (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E), H.rt0 = r
  · obtain ⟨E₀, _, _, _, H₀, h₀⟩ := h
    obtain ⟨L₀, hL₀⟩ := GlobalTheory.FinalJoin.CurveField.exists_periodPair H₀
    obtain ⟨hfin, halg, -⟩ := weberSet_finite_algebraic_permuted L₀ M (Nat.pos_of_ne_zero hM)
      (GlobalTheory.CompRat.Weber.g₂_ne_zero H₀ L₀ hL₀) (GlobalTheory.CompRat.Weber.g₃_ne_zero H₀ L₀ hL₀)
    refine ⟨hfin.toFinset, fun z hz => halg (GlobalTheory.WeberField.invariant_isAlgebraic H₀ L₀ hL₀) z (hfin.mem_toFinset.1 hz), ?_⟩
    intro E _ _ _ H hH F hF L hL
    have hw : ∀ s, GlobalTheory.CompRat.wC H s = GlobalTheory.CompRat.wC H₀ s := fun s => by
      unfold GlobalTheory.CompRat.wC
      rw [hH, h₀]
    have e : weberSet L M = weberSet L₀ M :=
      GlobalTheory.FieldSize.SmallField.weberSet_congr (Submodule.ext fun z => by
        rw [hL z, hL₀ z]
        simp only [hw]) M
    have hs : ∀ z ∈ weberSet L M, z ∈ F := fun z hz => hF z (hfin.mem_toFinset.2 (e ▸ hz))
    exact ⟨hs _ (Set.mem_insert _ _), fun s hs' => hs _ (Set.mem_insert_of_mem _ ⟨_, (hL _).2 ⟨s, rfl⟩, hs', rfl⟩)⟩
  · exact ⟨∅, by simp, fun E _ _ _ H hH => absurd ⟨E, _, _, _, H, hH⟩ h⟩

open Classical in

def WeberLev (B : Base) (f : Fr B.toPre) (T : TwDat B) : Prop :=
  ∀ S : Finset (HeightOneSpectrum (𝓞 B.host.E)), (∀ Q ∈ S, ∃ χ ∈ T.set f, ¬ χ.UnrAt Q) →
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E),
      H.rt0 = B.host.φ₀ B.host.sqrtMinusD →
      WeberIn H B.LLC (B.host.g 0 * B.host.g 1 * ∏ q ∈ S.image (fun Q => Nat.card (kP Q)), q)

open Classical in

theorem lg_weberLev (K : Ctx) : large₂ K WeberLev := by
  have h : ∀ (P : Pre) (Ξ : Set (HChar P.host.E)), ∃ Z : Finset ℂ, (∀ z ∈ Z, IsAlgebraic ℚ z) ∧
      ({Q : HeightOneSpectrum (𝓞 P.host.E) | ∃ χ ∈ Ξ, ¬ χ.UnrAt Q}.Finite →
        ∀ S : Finset (HeightOneSpectrum (𝓞 P.host.E)), (∀ Q ∈ S, ∃ χ ∈ Ξ, ¬ χ.UnrAt Q) →
        ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E),
          H.rt0 = P.host.φ₀ P.host.sqrtMinusD → ∀ F : IntermediateField ℚ ℂ, (∀ z ∈ Z, z ∈ F) →
          WeberIn H F (P.host.g 0 * P.host.g 1 * ∏ q ∈ S.image (fun Q => Nat.card (kP Q)), q)) := by
    intro P Ξ
    have hne : ∀ S : Finset (HeightOneSpectrum (𝓞 P.host.E)),
        P.host.g 0 * P.host.g 1 * ∏ q ∈ S.image (fun Q => Nat.card (kP Q)), q ≠ 0 := fun S => by
      refine mul_ne_zero (mul_ne_zero (P.host.g_prime 0).ne_zero (P.host.g_prime 1).ne_zero) ?_
      rw [Finset.prod_ne_zero_iff]
      intro q hq
      obtain ⟨Q, -, rfl⟩ := Finset.mem_image.1 hq
      exact GlobalTheory.Plug.TwistLevels.card_residueField_ne_zero Q
    choose Z hZ hZ' using fun S => exists_finset_weberIn (P.host.φ₀ P.host.sqrtMinusD) _ (hne S)
    by_cases hA : {Q : HeightOneSpectrum (𝓞 P.host.E) | ∃ χ ∈ Ξ, ¬ χ.UnrAt Q}.Finite
    · refine ⟨hA.toFinset.powerset.biUnion Z, fun z hz => ?_, fun _ S hS E _ _ _ H hH F hF => ?_⟩
      · obtain ⟨S, -, hz⟩ := Finset.mem_biUnion.1 hz
        exact hZ S z hz
      · exact hZ' S E H hH F fun z hz => hF z (Finset.mem_biUnion.2
          ⟨S, Finset.mem_powerset.2 fun Q hQ => hA.mem_toFinset.2 (hS Q hQ), hz⟩)
    · exact ⟨∅, by simp, fun h => absurd h hA⟩
  choose Z hZ hZ' using h
  refine ⟨fun _ _ _ => ∅, fun _ _ _ _ => ∅, fun _ _ _ _ _ => ∅, fun P _ _ _ Ξ => Z P Ξ, by simp,
    fun P _ _ _ Ξ => hZ P Ξ, fun B f T _ hH _ _ S hS E _ _ _ H hr => ?_⟩
  refine hZ' B.toPre (T.set f) ?_ S hS E H hr _ hH.2
  refine ((GlobalTheory.Mem.Top.TwFin.tw_fin B f T).1.biUnion fun χ hχ => GlobalTheory.Plug.TwistLevels.ram_finite B f T χ hχ).subset ?_
  rintro Q ⟨χ, hχ, hr⟩
  exact Set.mem_biUnion (x := χ) hχ hr

set_option maxHeartbeats 1000000 in

theorem coverField_of_weberLev {B : Base} {f : Fr B.toPre} {T : TwDat B} (hW : WeberLev B f T) (w : ColW B f T) (Z : w.Lt)
    (hX : B.fields.Ok) (Wt : Set B.places.Pl) (z : R3.Dat (w.st Z) w.I hX T Wt) :
    GlobalTheory.TwistField.CoverField z.core z.R.toRealDat := by
  intro i t l₂ _ hM hA Xo₂ c₂ hc
  have hP : z.core.Q.Pins := z.geo.fw.laws.pins
  have hS : ∀ Q ∈ z.R.Q t, ∃ χ ∈ T.set f, ¬ χ.UnrAt Q := fun Q hQ =>
    ⟨z.R.xiH t, by
      rw [z.lev.xiH t, ← w.xi_range]
      exact ⟨_, rfl⟩, (z.lev.is.Q_ram t Q).2 (Or.inl hQ)⟩
  have hw := hW (z.R.Q t) hS _ z.core.Q.H hP.1.2.2.1
  have hlev : l₂.M = B.host.g 0 * B.host.g 1 * GlobalTheory.TwistField.tupPrime z.R.toRealDat t := by
    rw [hM, show z.core.Q.l.M = _ from hP.2.1.1]
    rfl
  have hw' : WeberIn z.core.Q.H c₂.F l₂.M := by
    rw [hlev, hc]
    exact hw
  refine GlobalTheory.FinalJoin.FieldAlg.fnAlgClosed_of_weberIn _ z.core.Q hP ((i : ℕ) + 1) ⟨Nat.succ_le_succ (Nat.zero_le _), i.2⟩ l₂ Xo₂ c₂
    l₂.M (lt_of_lt_of_le (by norm_num) l₂.three_le) ?_ (Or.inl hw')
  rw [ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level.M', hA, Nat.lcm_one_right]

end GlobalTheory.Mem.Top.Bl.CoverAt

end
