import Mathlib
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.NormSmall
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RatInOfUnit
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NegIdxOfIsStd
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SquareNuHeckeCharacterNotUnramifiedAtChosenPlace
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FinPartIdemMulMemIff
import Development.AbelianVarietyTheory.Definitions.Foundations.OfInfProjInfMulOfFinProjFin
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HeckeCharUnramifiedAbovePlaceOfTrivialUnits
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsUnramifiedAtPlaceIdempotentOfHeckeCharUnramifiStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RamificationIdxEqOneOfIsSquare
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AuxiliaryPlaceNotDvdDifferentBaseField
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LargePlaceNotDvdDifferent
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SplitPrimeAdditiveCharacterUnramified
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GridLocalTensorPlacesOverSplitPlaces
import Formalism.LocalToGlobal.UnitaryNorms.CharUniq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistCharacterOfArtin
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LevelCharactersUnramifiedOffLevelPlaces

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset
open Formalism.DivisionValues (vw)
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.CMVal (IsHeckeL)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.SqTop
open GlobalTheory.ConstRatio (NegIdx Factor)

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.StageRam

private theorem pow_apply' {E : Type} [Field E] [NumberField E] (χ : HChar E) (a : ℕ) (x) : (χ ^ a).1 x = χ.1 x ^ a := by
  rw [SubgroupClass.coe_pow, MonoidHom.pow_apply]

private theorem loc_pow {E : Type} [Field E] [NumberField E] (χ : HChar E) (a : ℕ) (v x) :
    (χ ^ a).loc v x = χ.loc v x ^ a :=
  pow_apply' χ a _

private theorem locK_pow {E : Type} [Field E] [NumberField E] (χ : HChar E) (a : ℕ) (v x) :
    (χ ^ a).locK v x = χ.locK v x ^ a :=
  pow_apply' χ a _

private theorem unrAt_pow {E : Type} [Field E] [NumberField E] {χ : HChar E} {v} (h : χ.UnrAt v) (a : ℕ) :
    (χ ^ a).UnrAt v :=
  fun x hx => by rw [loc_pow, h x hx, one_pow]

private theorem chrEq_pow {D : D7} {c : (AE D)ˣ →* Circle} {χ : HChar D.host.E} (h : ChrEq c χ) (a : ℕ) :
    ChrEq (c ^ a) (χ ^ a) := by
  refine ⟨⟨?_, fun x => ?_⟩, fun P e he k x hx => ?_⟩
  · have : ((c ^ a : (AE D)ˣ →* Circle) : (AE D)ˣ → Circle) = fun x => c x ^ a := by
      funext x; simp
    rw [this]
    exact h.1.1.pow a
  · have h1 := h.1.2 x
    simp only [MonoidHom.pow_apply, h1, one_pow]
  · rw [MonoidHom.pow_apply, locK_pow, Units.val_pow_eq_pow_val, ← h.2 P e he k x hx]
    exact map_pow Circle.coeHom _ _

private theorem not_nonSplitAt_of_emb {D : D7} {v : HeightOneSpectrum (𝓞 D.host.F)} {ε : AF D.host.F}
    (hε : IsPlaceIdem D v ε) (τ : D.host.E →ₐ[D.host.F] Fv D.host.F v) : ¬ GlobalTheory.WeilParts.NonSplitAt D v ε := by
  intro h
  refine h.2 ⟨GlobalTheory.EmbChart.idem τ, GlobalTheory.EmbChart.isSplitIdem_idem τ, ?_⟩
  have he : ε = GlobalTheory.EmbChart.atPlace v 1 := by
    obtain ⟨α, rfl, h1, h0⟩ := hε
    rw [GlobalTheory.EmbChart.atPlace_apply]
    congr 1
    refine FiniteAdeleRing.ext _ fun u => ?_
    change evalV D.host.F u α = evalV D.host.F u (GlobalTheory.AdelicU.singleFin v 1)
    by_cases e : u = v
    · subst e; rw [GlobalTheory.AdelicU.evalV_singleFin_self, h1]
    · rw [GlobalTheory.AdelicU.evalV_singleFin_ne e, h0 u e]
  rw [he, GlobalTheory.EmbChart.cA_idem, GlobalTheory.EmbChart.idem, ← LinearMap.map_add, add_sub_cancel]; rfl

private theorem levelLe_one_of_unrAt {L : Type} [Field L] [NumberField L] {χ : HChar L} {w : HeightOneSpectrum (𝓞 L)}
    (h : χ.UnrAt w) : χ.LevelLe w 1 :=
  fun x hx _ => h x hx

private theorem natCast_mem_of_card {E : Type} [Field E] [NumberField E] {P : HeightOneSpectrum (𝓞 E)} {ℓ : ℕ}
    (hℓ : ℓ.Prime) (h : Nat.card (𝓞 E ⧸ P.asIdeal) = ℓ) : (ℓ : 𝓞 E) ∈ P.asIdeal := by
  have : Finite (𝓞 E ⧸ P.asIdeal) := Nat.finite_of_card_ne_zero (h ▸ hℓ.ne_zero)
  letI := Fintype.ofFinite (𝓞 E ⧸ P.asIdeal)
  have h0 : ((Fintype.card (𝓞 E ⧸ P.asIdeal) : ℕ) : 𝓞 E ⧸ P.asIdeal) = 0 := Nat.cast_card_eq_zero _
  rw [← Nat.card_eq_fintype_card, h] at h0
  rw [← Ideal.Quotient.eq_zero_iff_mem, map_natCast]
  exact h0

open Classical in

theorem _root_.GlobalTheory.T.towerStage_finitePlaces_unramified_or_split : GBig fun {D} {T} {Lc} {sc} G _ _ _ _ => ∀ (W : G.Weil) (i j : Fin D.R.m) (p q : ℕ) (A A' WW : HSp D) (X : Tri T A A' WW), GlobalTheory.SqTower.IsStageC W i j p q X → ∀ (t : T) (v : HeightOneSpectrum (𝓞 D.host.F)) (e : AF D.host.F), IsPlaceIdem D v e → (GlobalTheory.WeilParts.UnramAt e (Lc.mu t (j + 1) * Lc.eta ^ (rankV D i j % 2)) ∧ GlobalTheory.WeilParts.UnramAt e (G.ch.chi (D.R.m - i) * Lc.eta ^ (rankV D i j % 2))) ∨ (¬ GlobalTheory.WeilParts.NonSplitAt D v e ∧ ¬ GlobalTheory.WeilParts.UnramAt e (Lc.mu t (j + 1) * Lc.eta ^ (rankV D i j % 2) / (G.ch.chi (D.R.m - i) * Lc.eta ^ (rankV D i j % 2))) ∧ ¬ v.asIdeal ∣ differentIdeal ℤ (𝓞 D.host.F)) := by
  refine ⟨0, fun _ _ _ => ⟨0, 0, fun _ _ D large₂ _ _ hR T Lc μ₀ hL G => ?_⟩⟩
  intro W i j p q A A' WW X _ t v e he
  have hm1 : 1 ≤ D.R.m - (i : ℕ) := by omega
  have hm2 : D.R.m - (i : ℕ) ≤ D.R.m := by omega
  have hα : ChrEq (Lc.mu t (j + 1) * Lc.eta ^ (rankV D i j % 2)) (alphaH Lc t i j) :=
    GlobalTheory.TwistChr.chrEq_mul (GlobalTheory.TwistChr.chrEq_mul (hL.mu0 j) (hL.xi t)) (chrEq_pow hL.eta _)
  have hβ : ChrEq (G.ch.chi (D.R.m - i) * Lc.eta ^ (rankV D i j % 2)) (betaH G i j) :=
    GlobalTheory.TwistChr.chrEq_mul (G.ch.chi_eq _ hm1 hm2) (chrEq_pow hL.eta _)
  have hν : ChrEq (Lc.mu t (j + 1) * Lc.eta ^ (rankV D i j % 2) / (G.ch.chi (D.R.m - i) * Lc.eta ^ (rankV D i j % 2)))
      (nuH G t i j) := by
    rw [mul_div_mul_right_eq_div]
    exact chrEq_nu G t i j hL
  have hmu : ∀ P : HeightOneSpectrum (𝓞 D.host.E), P.under (𝓞 D.host.F) ∉ S1 D → (Lc.C.mu0 j).UnrAt P :=
    fun P hP => (Lc.C.isMu0 j).unr _ fun k hk => hP (by
      have h : ((D.host.g k : ℕ) : 𝓞 D.host.F) ∈ (P.under (𝓞 D.host.F)).asIdeal := by
        show algebraMap _ (𝓞 D.host.E) _ ∈ P.asIdeal
        rw [map_natCast]; exact hk
      refine (S1_mem_OmF D).2 ?_
      fin_cases k
      · exact Or.inl h
      · exact Or.inr (Or.inl h))
  have hxi : ∀ P : HeightOneSpectrum (𝓞 D.host.E),
      (∀ PP ∈ Lc.Q t, PP.under (𝓞 D.host.F) ≠ P.under (𝓞 D.host.F)) → (Lc.xiH t).UnrAt P := fun P hP => by
    by_contra hc
    rcases (hL.Q_ram t P).1 hc with h | ⟨PP', h, hc'⟩
    · exact hP P h rfl
    · exact hP PP' h (GlobalTheory.LevelPlaces.under_eq_of_isConjPl hc')
  have hchi : ∀ P : HeightOneSpectrum (𝓞 D.host.E), P.under (𝓞 D.host.F) ∉ G.pl.S0 →
      (G.ch.chiH (D.R.m - i)).UnrAt P := fun P hP => G.ch.unr _ hm1 hm2 P hP
  have heta : ∀ P : HeightOneSpectrum (𝓞 D.host.E), (Lc.C.eta ^ (rankV D i j % 2)).UnrAt P :=
    fun P => unrAt_pow (Lc.C.isEta.unr P) _
  by_cases hS : v ∈ G.pl.S0 ∨ ∃ PP ∈ Lc.Q t, PP.under (𝓞 D.host.F) = v
  · right
    obtain ⟨w, hw, hwv⟩ : ∃ w ∈ locPl G t, w.under (𝓞 D.host.F) = v := by
      rcases hS with h | ⟨PP, hP, hPv⟩
      · exact ⟨G.pl.w v, Finset.mem_union_left _ (Finset.mem_image_of_mem _ h), G.pl.under_w h⟩
      · exact ⟨PP, Finset.mem_union_right _ hP, hPv⟩
    have hns : ¬ GlobalTheory.WeilParts.NonSplitAt D v e := by
      obtain ⟨τ⟩ := GlobalTheory.LocPlSplit.locPl_split hL t w hw
      rw [hwv] at τ
      exact not_nonSplitAt_of_emb he τ
    refine ⟨hns, fun hu => ?_, ?_⟩
    · have key : ∀ P : HeightOneSpectrum (𝓞 D.host.E), P.under (𝓞 D.host.F) = v → (nuH G t i j).UnrAt P :=
        fun P hP => (GlobalTheory.LFun.unrAt_iff_of_chrEq hν P).1 (GlobalTheory.UnrOverPlace.unrAt_of_unramAt D _ v e he hu P hP)
      by_cases h0 : v = G.pl.v0
      · subst h0
        exact GlobalTheory.RowTest.squareNuHeckeCharacter_not_unramified_at_chosenPlace hL G t i j (key _ (G.pl.under_w (G.pl.mem_S0_of_sum_eq.2 (Or.inl rfl))))
      · by_cases h1 : v ∈ S1 D
        · have hv : v ∈ G.pl.S0 := G.pl.mem_S0_of_sum_eq.2 (Or.inr h1)
          have hwv' := G.pl.under_w hv
          apply (G.ch.lev1 _ hm1 hm2 (G.pl.w v) (by rw [hwv']; exact h1)).2
          have ee : G.ch.chiH (D.R.m - i) = Lc.C.mu0 j * Lc.xiH t / nuH G t i j := by
            rw [nuH, div_div_cancel]
          rw [ee, div_eq_mul_inv]
          exact HChar.LevelLe.mul (HChar.LevelLe.mul ((Lc.C.isMu0 j).tame _) (hL.xi_tame t _))
            (HChar.LevelLe.inv (levelLe_one_of_unrAt (key _ hwv')))
        · obtain ⟨PP, hP, hPv⟩ := hS.resolve_left fun h => (G.pl.mem_S0_of_sum_eq.1 h).elim h0 h1
          apply (hL.Q_ram t PP).2 (Or.inl hP)
          have ee : Lc.xiH t = nuH G t i j * G.ch.chiH (D.R.m - i) / Lc.C.mu0 j := by
            rw [nuH, div_mul_cancel, mul_div_cancel_left]
          rw [ee, div_eq_mul_inv]
          exact ((key PP hPv).mul (hchi PP (by rw [hPv]; exact fun h => (G.pl.mem_S0_of_sum_eq.1 h).elim h0 h1))).mul
            (hmu PP (by rw [hPv]; exact h1)).inv
    · by_cases h0 : v = G.pl.v0
      · subst h0
        exact GlobalTheory.DifferentAtBasePlace.not_dvd_different G
      · by_cases h1 : v ∈ S1 D
        · exact GlobalTheory.DiffSOne.not_dvd_differentIdeal large₂ hR v h1
        · obtain ⟨PP, hP, hPv⟩ := hS.resolve_left fun h => (G.pl.mem_S0_of_sum_eq.1 h).elim h0 h1
          obtain ⟨⟨ℓ, hℓ, hcard, hℓ2, -⟩, -⟩ := hL.Q_pl t PP hP
          have hℓP : ((ℓ : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal := natCast_mem_of_card hℓ hcard
          have hle : v.asIdeal.map (algebraMap (𝓞 D.host.F) (𝓞 D.host.E)) ≤ PP.asIdeal := by
            rw [← hPv]
            exact Ideal.map_comap_le
          refine GlobalTheory.SplitUnram.not_dvd_different hℓ v ?_ ?_
          · rw [← hPv]
            show algebraMap _ (𝓞 D.host.E) _ ∈ PP.asIdeal
            rw [map_natCast]; exact hℓP
          · intro hv2
            have h' := Ideal.mem_map_of_mem (algebraMap (𝓞 D.host.F) (𝓞 D.host.E)) hv2
            rw [Ideal.map_pow, map_natCast] at h'
            exact hℓ2 (Ideal.pow_right_mono hle 2 h')
  · left
    push_neg at hS
    obtain ⟨hS0, hQ⟩ := hS
    have hS1 : v ∉ S1 D := fun h => hS0 (G.pl.mem_S0_of_sum_eq.2 (Or.inr h))
    refine ⟨GlobalTheory.T.isUnramifiedAtPlaceIdempotent_of_heckeChar_unramified_above D _ _ hα v e he fun P hP => ?_, GlobalTheory.T.isUnramifiedAtPlaceIdempotent_of_heckeChar_unramified_above D _ _ hβ v e he fun P hP => ?_⟩
    · exact ((hmu P (by rw [hP]; exact hS1)).mul (hxi P fun PP hPP h => hQ PP hPP (h.trans hP))).mul (heta P)
    · exact (hchi P (by rw [hP]; exact hS0)).mul (heta P)

end GlobalTheory.StageRam

end
