import Mathlib
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.SizeAt
import Development.AbelianVarietyTheory.Definitions.Divisors.TieTest
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.NormSmall
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ToricSymbols
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NuHTwisted
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAutCentre
import CompanionTheory.AutomorphicTheory.PlaceSeparation.IsOpenQuotientMapArt0
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.NormalFormToricRatio
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsCMValueHeckeCharacterAuxiliarySetOfEmpty
import Development.AbelianVarietyTheory.Definitions.Divisors.IsValCharTwist

open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.BigTop GlobalTheory.BigTop.Fun GlobalTheory.SqTop NumberField IsDedekindDomain
open GlobalTheory.FunObj.SqNum (nuH halfRank IsTor)
open GlobalTheory.CMVal GlobalTheory.HeckeGal

noncomputable section

namespace GlobalTheory.ThmAMove

open GlobalTheory.ToricDenom GlobalTheory.IndefiniteRowSideFullHecke.GoodPairSystems

variable {D : D7}

private theorem val_pos_iff (w : D.what₂.places.Pl) (y : D.what₂.LL) :
    0 < D.what₂.places.val w y ↔ (D.plEq w).valuation D.what₂.LL y < 1 := by
  by_cases hy : y = 0
  · simp [hy]
  have h0 : (D.plEq w).valuation D.what₂.LL y ≠ 0 := by simpa using hy
  rw [D.val_eq w y hy, vAdd, ← WithZero.log_lt_log h0 one_ne_zero, WithZero.log_one]
  norm_cast
  omega

private theorem val_zero_iff (w : D.what₂.places.Pl) (y : D.what₂.LL) :
    D.what₂.places.val w y = 0 ↔ (D.plEq w).valuation D.what₂.LL y = 1 := by
  by_cases hy : y = 0
  · simp [hy]
  have h0 : (D.plEq w).valuation D.what₂.LL y ≠ 0 := by simpa using hy
  rw [D.val_eq w y hy, vAdd]
  norm_cast
  rw [neg_eq_zero]
  exact ⟨fun h => by rw [← WithZero.exp_log h0, h, WithZero.exp_zero], fun h => by rw [h, WithZero.log_one]⟩

private theorem val_resChar_lt (w : D.what₂.places.Pl) :
    (D.plEq w).valuation D.what₂.LL ((D.what₂.places.resChar w : ℕ) : D.what₂.LL) < 1 := by
  rw [← val_pos_iff, D.what₂.places.val_resChar w]
  exact_mod_cast D.what₂.places.ramIdx_pos w

private theorem exists_place (C : NChoice D) (w w' : D.what₂.places.Pl) (hw' : LiesUnder D (C.twI w) w')
    (ι : ℂ →+* Kbar D.ntw (C.twI w))
    (hι : ∀ x : D.LL0, ι (D.what₂.embLL (x : D.what₂.LL)) = toBar D.ntw (C.twI w) (D.ntw.emb0 (C.twI w) x))
    (jk : FractionRing (D.ntw.Ok (C.twI w) (C.k' w)) →+* Kbar D.ntw (C.twI w))
    (hjk : jk.comp (BlochKatoReduction.Gen.kMap D.ntw (C.twI w) (C.k' w)) = algebraMap _ (Kbar D.ntw (C.twI w))) :
    ∃ (je : FractionRing (C.Oe w) →+* Kbar D.ntw (C.twI w)) (A : ValuationSubring (Kbar D.ntw (C.twI w))) (g : ℂ ≃+* ℂ),
      (∀ x, je (C.kMapE w x) = jk x) ∧
      (∀ x y, A.valuation (je x) = A.valuation (je y) → ∃ u : (C.Oe w)ˣ, x = algebraMap _ _ (u : C.Oe w) * y) ∧
      (∀ y, (D.plEq w).valuation D.what₂.LL y = 1 → A.valuation (je (C.embW w y)) = 1) ∧
      (∀ x : D.LL0, g (D.what₂.embLL x) = D.what₂.embLL x) ∧
      ∀ y, (D.plEq w').valuation D.what₂.LL y = 1 → A.valuation (ι (g (D.what₂.embLL y))) = 1 := by
  haveI := C.Oe_fin w
  haveI := D.galLL
  obtain ⟨je, hje⟩ := exists_ext (C.Oe_inj w) jk
  obtain ⟨A, hA, hloc⟩ := IsLocalRing.exists_factor_valuationRing (je.comp (algebraMap (C.Oe w) (FractionRing (C.Oe w))))
  have hu : ∀ a : C.Oe w, A.valuation (je (algebraMap _ _ a)) = 1 → IsUnit a := fun a h =>
    hloc.1 a ((A.valuation_eq_one_iff ⟨_, hA a⟩).2 h)
  have hα : ∀ y, (D.plEq w).valuation D.what₂.LL y = 1 → A.valuation (je (C.embW w y)) = 1 := by
    have key : ∀ y, (D.plEq w).valuation D.what₂.LL y = 1 → A.valuation (je (C.embW w y)) ≤ 1 := fun y hy => by
      obtain ⟨a, ha⟩ := (C.embW_w w y).1 ((val_zero_iff w y).2 hy).ge
      rw [← ha, A.valuation_le_one_iff]
      exact hA a
    intro y hy
    refine le_antisymm (key y hy) ?_
    have h1 := key y⁻¹ (by rw [map_inv₀, hy, inv_one])
    have hy0 : y ≠ 0 := by
      rintro rfl
      simp at hy
    rwa [map_inv₀, map_inv₀, map_inv₀, inv_le_one₀ (zero_lt_iff.2 (by simpa using hy0))] at h1
  have hp := D.what₂.places.resChar_prime w
  have hl : A.valuation ((D.what₂.places.resChar w : ℕ) : Kbar D.ntw (C.twI w)) < 1 := by
    refine lt_of_le_of_ne ((A.valuation_le_one_iff _).2 (natCast_mem A _)) fun h => ?_
    obtain ⟨u, hu'⟩ := hu ((D.what₂.places.resChar w : ℕ) : C.Oe w) (by rwa [map_natCast, map_natCast])
    have h1 : 0 ≤ D.what₂.places.val w (((D.what₂.places.resChar w : ℕ) : D.what₂.LL)⁻¹) :=
      (C.embW_w w _).2 ⟨(u⁻¹ : (C.Oe w)ˣ), by rw [map_units_inv, hu', map_inv₀, map_natCast, map_natCast]⟩
    have hne : ((D.what₂.places.resChar w : ℕ) : D.what₂.LL) ≠ 0 := Nat.cast_ne_zero.2 hp.ne_zero
    have h2 := (D.what₂.places.val w).map_mul ((D.what₂.places.resChar w : ℕ) : D.what₂.LL)
      (((D.what₂.places.resChar w : ℕ) : D.what₂.LL)⁻¹)
    rw [mul_inv_cancel₀ hne, AddValuation.map_one] at h2
    exact absurd h2 (add_pos_of_pos_of_nonneg ((val_pos_iff w _).2 (val_resChar_lt w)) h1).ne
  have hl0 : ((D.what₂.places.resChar w : ℕ) : Kbar D.ntw (C.twI w)) ≠ 0 := by
    rw [← map_natCast ι, map_ne_zero]
    exact Nat.cast_ne_zero.2 hp.ne_zero
  let f0 : D.ntw.O0 (C.twI w) →+* Kbar D.ntw (C.twI w) := (toBar D.ntw (C.twI w)).comp (algebraMap _ _)
  have hf0 : ∀ r, f0 r ∈ A := fun r => by
    have e1 := GlobalTheory.ToricRational.toBar_algebraMap (X := D.ntw) (C.twI w) r
    have e2 := DFunLike.congr_fun hjk (algebraMap (D.ntw.O (C.twI w)) _ (algebraMap _ _ r))
    rw [RingHom.comp_apply, BlochKatoReduction.Gen.kMap, IsFractionRing.lift_algebraMap, RingHom.comp_apply, ← hje] at e2
    replace e2 := e2.trans e1.symm
    have e3 := hA (algebraMap (D.ntw.Ok (C.twI w) (C.k' w)) _ (algebraMap (D.ntw.O (C.twI w)) _ (algebraMap _ _ r)))
    show toBar D.ntw (C.twI w) (algebraMap _ _ r) ∈ A
    rw [← e2]
    simpa [IsFractionRing.map] using e3
  obtain ⟨σ, hσ⟩ := exists_aut_centre A D.LL0 (ι.comp D.what₂.embLL) (D.plEq w') fun x => by
    have hi : IsIntegral (D.ntw.O0 (C.twI w)) (D.ntw.emb0 (C.twI w) x) :=
      IsIntegral.map_of_comp_eq (Int.castRingHom _) (D.ntw.emb0 (C.twI w)) (RingHom.ext_int _ _) x.isIntegral_coe
    obtain ⟨a, ha⟩ := IsIntegrallyClosed.isIntegral_iff.1 hi
    have e1 : (ι.comp D.what₂.embLL) ((x : D.LL0) : D.what₂.LL) = f0 a := by
      rw [RingHom.comp_apply, hι, ← ha]; rfl
    rw [e1, ← mem_max_iff A f0 hf0 hl0 hl, ← HeightOneSpectrum.valuation_lt_one_iff_mem (K := D.what₂.LL), ← val_pos_iff]
    refine Iff.trans ⟨fun h => ⟨a, h, ha⟩, fun ⟨y, hy, e⟩ => ?_⟩ (hw' x)
    rwa [← IsFractionRing.injective _ (FractionRing (D.ntw.O0 (C.twI w))) (e.trans ha.symm)]
  haveI : Countable D.what₂.LL := Countable.of_equiv _ (Module.finBasis ℚ D.what₂.LL).equivFun.toEquiv.symm
  obtain ⟨g, hg⟩ := GlobalTheory.GaloisDescent.exists_complex_ringEquiv_comp_eq D.what₂.embLL (D.what₂.embLL.comp σ.toRingEquiv.toRingHom)
  refine ⟨je, A, g, hje, fun x y h => exists_unit A je hA hu h, hα, fun x => ?_, fun y hy => ?_⟩
  · rw [hg]
    exact congrArg D.what₂.embLL (σ.commutes x)
  · rw [hg]
    exact unit_of_centre A (ι.comp (D.what₂.embLL.comp σ.toRingEquiv.toRingHom)) _ hσ y hy

private theorem exists_side (C : NChoice D) (w : D.what₂.places.Pl)
    (hw : LiesUnder D (C.twI w) w ∨ LiesUnder D (C.twI w) (D.what₂.places.conj w)) : ∃ b : Bool,
    ∀ (ι : ℂ →+* Kbar D.ntw (C.twI w))
      (_ : ∀ x : D.LL0, ι (D.what₂.embLL (x : D.what₂.LL)) = toBar D.ntw (C.twI w) (D.ntw.emb0 (C.twI w) x))
      (jk : FractionRing (D.ntw.Ok (C.twI w) (C.k' w)) →+* Kbar D.ntw (C.twI w))
      (_ : jk.comp (BlochKatoReduction.Gen.kMap D.ntw (C.twI w) (C.k' w)) = algebraMap _ (Kbar D.ntw (C.twI w))),
    ∃ (je : FractionRing (C.Oe w) →+* Kbar D.ntw (C.twI w)) (A : ValuationSubring (Kbar D.ntw (C.twI w))) (g : ℂ ≃+* ℂ),
      (∀ x, je (C.kMapE w x) = jk x) ∧
      (∀ x y, A.valuation (je x) = A.valuation (je y) → ∃ u : (C.Oe w)ˣ, x = algebraMap _ _ (u : C.Oe w) * y) ∧
      (∀ t ∈ (Formalism.L2.Host.embLL0 D).fieldRange, starRingEnd ℂ t ∈ (Formalism.L2.Host.embLL0 D).fieldRange → g t = t) ∧
      ∀ z, A.valuation (je (C.embW w z)) = A.valuation (atSide D.ntw b ι (g (D.what₂.embLL z))) := by
  have hp := (D.what₂.places.resChar_prime w).ne_zero
  rcases hw with hw | hw
  · refine ⟨true, fun ι hι jk hjk => ?_⟩
    obtain ⟨je, A, g, h1, h2, h3, h4, h5⟩ := exists_place C w w hw ι hι jk hjk
    refine ⟨je, A, g, h1, h2, ?_, val_eq_of_unit A (je.comp (C.embW w)) (ι.comp (g.toRingHom.comp D.what₂.embLL)) _ hp
      (val_resChar_lt w).ne h3 h5⟩
    rintro _ ⟨x, rfl⟩ -
    exact h4 x
  · refine ⟨false, fun ι hι jk hjk => ?_⟩
    obtain ⟨je, A, g, h1, h2, h3, h4, h5⟩ := exists_place C w _ hw ι hι jk hjk
    let c : ℂ ≃+* ℂ := Complex.conjAe.toRingEquiv
    have hc : ∀ t, c t = starRingEnd ℂ t := fun _ => rfl
    refine ⟨je, A, (c.trans g).trans c, h1, h2, ?_, val_eq_of_unit A (je.comp (C.embW w))
      ((atSide D.ntw false ι).comp (((c.trans g).trans c).toRingHom.comp D.what₂.embLL)) _ hp
      (val_resChar_lt w).ne h3 fun y hy => ?_⟩
    · rintro t - ⟨x, hx⟩
      show c (g (c t)) = t
      rw [hc t, ← hx]
      refine (congrArg c (h4 x)).trans ?_
      show starRingEnd ℂ (Formalism.L2.Host.embLL0 D x) = t
      rw [hx, Complex.conj_conj]
    · letI := D.starLL
      have h6 := h5 (star y) (by rw [← val_zero_iff, D.conj_val, star_star, val_zero_iff, hy])
      rw [D.starLL_cx] at h6
      show A.valuation (ι (starRingEnd ℂ (starRingEnd ℂ (g (starRingEnd ℂ (D.what₂.embLL y)))))) = 1
      rwa [Complex.conj_conj]

private theorem emb_mem (σ : D.host.E →+* ℂ) (x : D.host.E) : σ x ∈ (Formalism.L2.Host.embLL0 D).fieldRange := by
  have : IsGalois ℚ D.host.E := D.host.hostE_isGalois
  let _ : Algebra D.host.E ℂ := D.host.φ₀.toAlgebra
  have : IsScalarTower ℚ D.host.E ℂ := IsScalarTower.of_algebraMap_eq fun q => (map_ratCast D.host.φ₀ q).symm
  have e : D.host.φ₀ (σ.toRatAlgHom.restrictNormal D.host.E x) = σ x := σ.toRatAlgHom.restrictNormal_commutes D.host.E x
  rw [← e, ← D.embE_φ₀]
  exact ⟨⟨_, D.hostField_le_fixedField _⟩, rfl⟩

section Point

variable {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ} {p : PtAt ex Csz} {CF : ℝ} {G : Grid p CF}

private theorem almostIn (h : GridFit p G) (i j : Fin D.R.m) (l : ℕ) :
    GlobalTheory.GalChar.AlmostIn (Formalism.L2.Host.embLL0 D) (nuH G p.P.A3.A.μ0 i j * p.R.C.delAt l) := by
  unfold nuH
  rw [GlobalTheory.ThmAUpper.xiH_base p, mul_one, div_eq_mul_inv]
  refine ((GlobalTheory.GalChar.almostIn_of_valuesIn (h.frame.mu0 j)).mul
    (GlobalTheory.GalChar.almostIn_of_valuesIn (h.field.values _ (by omega) (by omega))).inv).mul ?_
  unfold Formalism.L2.Host.CharFrame.delAt
  split_ifs
  exacts [GlobalTheory.GalChar.almostIn_of_valuesIn h.frame.del', GlobalTheory.GalChar.almostIn_of_valuesIn h.frame.del]

private theorem divisorProofs_isSet_fact (h : GridFit p G) {w : D.what₂.places.Pl} (hw : TwistedAt D w) :
    IsFinSetSplitPlacesCoprimeConductor (GlobalTheory.FunObj.SqNum.condF G.pl) (belowSet (ex.nch.Q w)) := by
  refine (placesBelow_splitCoprimeConductor_of_admissible (h.cond w hw) fun P hP => (h.list _ (h.setting.inW1 hw)).1 P ?_).1
  obtain ⟨v, hv, hd⟩ := (Prime.dvd_finset_prod_iff (below P).prime _).1 hP
  have e : below P = v := HeightOneSpectrum.ext
    ((v.isMaximal.eq_of_le (below P).isPrime.ne_top (Ideal.le_of_dvd ((below P).prime.dvd_of_dvd_pow hd))).symm)
  subst e
  rcases G.pl.mem_S0_of_sum_eq.1 hv with h0 | h1
  · refine Dvd.dvd.mul_left ?_ _
    have : below (G.pl.w G.pl.v0) = G.pl.v0 := G.pl.under_w (G.pl.mem_S0_of_sum_eq.2 (Or.inl rfl))
    show _ ∣ (below (G.pl.w G.pl.v0)).asIdeal
    rw [this, ← h0]
  · refine Dvd.dvd.mul_right (dvd_pow (Ideal.dvd_span_singleton.2 ?_) two_ne_zero) _
    have := (GlobalTheory.ChiGrid.S1_mem_OmF D).1 h1
    simp only [Nat.cast_mul, (below P).isPrime.mul_mem_iff_mem_or_mem, or_assoc]
    exact this

end Point

theorem _root_.GlobalTheory.T.toric_ratio_field_data_cm : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ} (p : PtAt ex Csz) (CF : ℝ) (d : FunIn p CF), p.Rows → Fitted (@Comparison₂) p CF d → GlobalTheory.IndefiniteRowSideFullHecke.ToricSymbols.ToricRatioConjugates → (∃ (_ : IsCMField D.host.E) (_ : IsAbelianGalois ℚ D.host.E), GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds.IsFieldData D.host.d (GlobalTheory.FunObj.SqNum.cmPhi D) ∧
    GlobalTheory.CMVal.IsBaseCond (GlobalTheory.FunObj.SqNum.condF d.G.pl) ∧ ∃ Λ, GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds.IsIntLattice D.host.d Λ) → ∀ w : D.what₂.places.Pl, TwistedAt D w → ∀ (i j : Fin D.R.m) (s : ℕ), 1 ≤ s → s ≤ halfRank D i j →
    ∀ (T₀ : ℂ) (ψc : PicO (condQ (GlobalTheory.FunObj.SqNum.condF d.G.pl) (GlobalTheory.ToricDenom.belowSet (ex.nch.Q w))) →* ℂˣ) (T : (PicO (condQ (GlobalTheory.FunObj.SqNum.condF d.G.pl) (GlobalTheory.ToricDenom.belowSet (ex.nch.Q w))) →* ℂˣ) → ℂ), IsValChar (GlobalTheory.FunObj.SqNum.cmPhi D) s (GlobalTheory.FunObj.SqNum.kap D 1 i j s) (GlobalTheory.FunObj.SqNum.condF d.G.pl) ∅ (nuH d.G p.P.A3.A.μ0 i j * p.R.C.delAt (D.what₂.places.resChar w)) →
      IsToricSum (GlobalTheory.FunObj.SqNum.cmPhi D) s (GlobalTheory.FunObj.SqNum.kap D 1 i j s) (GlobalTheory.FunObj.SqNum.condF d.G.pl) (nuH d.G p.P.A3.A.μ0 i j * p.R.C.delAt (D.what₂.places.resChar w)) T₀ → T₀ ≠ 0 →
      (∀ y, finPart (p.Tp.psi w) y = ψc (QuotientGroup.mk y)) →
      (∀ ψ, GlobalTheory.IndefiniteRowSideFullHecke.ToricSymbols.IsTwistedSum (GlobalTheory.FunObj.SqNum.cmPhi D) s (GlobalTheory.FunObj.SqNum.kap D 1 i j s) (condQ (GlobalTheory.FunObj.SqNum.condF d.G.pl) (GlobalTheory.ToricDenom.belowSet (ex.nch.Q w))) (nuH d.G p.P.A3.A.μ0 i j * p.R.C.delAt (D.what₂.places.resChar w)) ψ (T ψ)) → ∀ z : D.what₂.LL, D.what₂.embLL z * T₀ = T ψc → (∃ ι : ℂ →+* GlobalTheory.ToricDenom.Kbar D.ntw (ex.nch.twI w),
        (∀ x : D.LL0, ι (D.what₂.embLL (x : D.what₂.LL)) = GlobalTheory.ToricDenom.toBar D.ntw (ex.nch.twI w) (D.ntw.emb0 (ex.nch.twI w) x)) ∧
        ∀ b : Bool, ∃ (lam : D.ntw.abelian₂ (ex.nch.twI w)) (jk : FractionRing (D.ntw.Ok (ex.nch.twI w) (ex.nch.k' w)) →+* GlobalTheory.ToricDenom.Kbar D.ntw (ex.nch.twI w)) (c : ℤ),
            D.ntw.sideL (ex.nch.twI w) lam = b ∧ IsCoprime c (D.ntw.l (ex.nch.twI w) : ℤ) ∧
            jk.comp (BlochKatoReduction.Gen.kMap D.ntw (ex.nch.twI w) (ex.nch.k' w)) = algebraMap (FractionRing (D.ntw.O (ex.nch.twI w))) (GlobalTheory.ToricDenom.Kbar D.ntw (ex.nch.twI w)) ∧
            ∀ a : ℤ, jk (BlochKatoReduction.Gen.thEval D.ntw (ex.nch.twI w) (ex.nch.Q w) lam (ex.nch.k' w) (BlochKatoReduction.Gen.psiAt (D.ntw.sideL (ex.nch.twI w) lam) (ex.nch.psi' w ^ a))) *
                GlobalTheory.ToricDenom.atSide D.ntw b ι T₀ =
              jk (BlochKatoReduction.Gen.kMap D.ntw (ex.nch.twI w) (ex.nch.k' w) (∑ δ, D.ntw.th (ex.nch.twI w) ∅ lam δ)) * GlobalTheory.ToricDenom.atSide D.ntw b ι (T (ψc ^ (c * a)))) →
      ∃ (lam : D.ntw.abelian₂ (ex.nch.twI w)) (a : ℤ) (u : (ex.nch.Oe w)ˣ), IsCoprime a (D.ntw.l (ex.nch.twI w) : ℤ) ∧
        ex.nch.embW w z * ex.nch.kMapE w (BlochKatoReduction.Gen.kMap D.ntw (ex.nch.twI w) (ex.nch.k' w) (∑ δ, D.ntw.th (ex.nch.twI w) ∅ lam δ)) =
          algebraMap (ex.nch.Oe w) (FractionRing (ex.nch.Oe w)) (u : ex.nch.Oe w) *
            ex.nch.kMapE w (BlochKatoReduction.Gen.thEval D.ntw (ex.nch.twI w) (ex.nch.Q w) lam (ex.nch.k' w)
              (BlochKatoReduction.Gen.psiAt (D.ntw.sideL (ex.nch.twI w) lam) (ex.nch.psi' w ^ a))) := by
  intro D L hT Gi Gl Kc Y cX ex Csz p CF d hp hfit hG hF w hw i j s hs1 hs2 T₀ ψc T hv h0 h0ne hψ hT' z hz hread
  obtain ⟨hcm, -, hfd, hbc, -⟩ := hF
  obtain ⟨ι, hι, hread⟩ := hread
  obtain ⟨b, hb⟩ := exists_side ex.nch w (hfit.1.setting.1 w hw).2
  obtain ⟨lam, jk, c, -, hc, hjk, hid⟩ := hread b
  obtain ⟨je, A, g, h1, h2, h3, h4⟩ := hb ι hι jk hjk
  have hU : UnramFin D.host.E := hfd.2.2.1
  have hφ : IsCMType (GlobalTheory.FunObj.SqNum.cmPhi D) := hfd.2.2.2.2.2.2.1
  generalize hχ : nuH d.G p.P.A3.A.μ0 i j * p.R.C.delAt (D.what₂.places.resChar w) = χ at hv h0 hT'
  have hal : GlobalTheory.GalChar.AlmostIn (Formalism.L2.Host.embLL0 D) χ := hχ ▸ almostIn hfit.1 i j _
  have hfin : Finite (PicO (condQ (GlobalTheory.FunObj.SqNum.condF d.G.pl) ∅)) := by
    rw [condQ, Finset.prod_empty, mul_one]; exact h0.1
  have hval : ∀ y, (finPart χ y : ℂ) ∈ (Formalism.L2.Host.embLL0 D).fieldRange :=
    GlobalTheory.ToricRational.finPart_mem hv.2.2.1 (GlobalTheory.ToricRational.condQ_ne_bot hbc.1 ∅)
      (OrderUnits.finPart_eq_one _ _ _ hφ s _ _ ∅ χ hU hbc (fun _ h => absurd h (Finset.notMem_empty _)) hv) _ emb_mem
      (Filter.eventually_cofinite.1 hal).toFinset fun P hP => by simpa using hP
  have hlam : ∀ y, g (GlobalTheory.IndefiniteRowSideFullHecke.ToricSymbols.lamF χ s y) = GlobalTheory.IndefiniteRowSideFullHecke.ToricSymbols.lamF χ s y := fun y => by
    have hm : ((modF y ^ s : ℝ) : ℂ) ∈ (Formalism.L2.Host.embLL0 D).fieldRange := by
      rw [Complex.ofReal_pow]
      exact pow_mem (GlobalTheory.ToricRational.modF_mem _ y) s
    refine h3 _ (mul_mem (hval y) hm) ?_
    rw [GlobalTheory.IndefiniteRowSideFullHecke.ToricSymbols.lamF, map_mul, Complex.conj_ofReal, ← Complex.inv_eq_conj (show ‖(finPart χ y : ℂ)‖ = 1 from hv.1 _)]
    exact mul_mem (inv_mem (hval y)) hm
  haveI : Nonempty D.what₂.Tau := Fintype.card_pos_iff.1 (by have := hfd.2.2.2.2.2.1; omega)
  let τ₀ : D.what₂.Tau := Classical.arbitrary _
  let δ : D.host.K := ⟨D.host.sqrtMinusD, GlobalTheory.Mem.Col2.HostK.sqrt_mem D.host⟩
  have hδ : δ ^ 2 = -(D.host.d : D.host.K) := Subtype.ext (by simpa using Formalism.BasicNotions.Host.sqrtMinusD_sq D.host)
  obtain ⟨ζ, hζ, hg⟩ := ratio_conj CompanionTheory.FamInh.globalArtin hG D.host.E D.host.K D.host.d δ _ _ _ s _ _ _ χ hU (Formalism.MainNotions.DIV.Bridge.LogAbsNormDifferent.finrank_K D)
    hfd.1.pos hδ hφ (fun τ => GlobalTheory.RowEx.RatioField.cmPhi_comp_eq hfd τ τ₀) hs1
    (fun τ => (GlobalTheory.FunObj.SqNum.Model.kap_add D 1 i j τ hs2).2) hbc (divisorProofs_isSet_fact hfit.1 hw) hv h0 hT' g
    (fun τ x => h3 _ (emb_mem _ x) (emb_mem ((starRingEnd ℂ).comp _) x)) hlam ψc
  obtain ⟨n, hn⟩ := (p.Tp.psi_is w hw).ord
  rw [ex.nch.twI_l] at hc ⊢
  obtain ⟨a, ha, he⟩ := exists_exponent ψc (n := n) (D.what₂.places.resChar_prime w) (fun q => by
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective q
    rw [← hψ]
    exact congrArg (fun ξ => finPart ξ y) hn) g hc
  have hid' := hid a
  rw [← he] at hid'
  have hz' : T ψc / T₀ = D.what₂.embLL z := by rw [← hz, mul_div_cancel_right₀ _ h0ne]
  have hT : T (GlobalTheory.IndefiniteRowSideFullHecke.ToricSymbols.conjChar g ψc) = ζ * g (D.what₂.embLL z) * T₀ := by
    rw [← hz', hg]
    field_simp
  have hζ1 : A.valuation (atSide D.ntw b ι ζ) = 1 := by
    obtain ⟨m, hm, hm'⟩ := isOfFinOrder_iff_pow_eq_one.1 hζ
    refine (pow_eq_one_iff_of_nonneg zero_le hm.ne').1 ?_
    rw [← map_pow, ← map_pow, ← Units.val_pow_eq_pow_val, hm', Units.val_one, map_one, map_one]
  obtain ⟨u, hu⟩ := h2 (ex.nch.embW w z * ex.nch.kMapE w (BlochKatoReduction.Gen.kMap D.ntw (ex.nch.twI w) (ex.nch.k' w)
      (∑ δ, D.ntw.th (ex.nch.twI w) ∅ lam δ))) (ex.nch.kMapE w (BlochKatoReduction.Gen.thEval D.ntw (ex.nch.twI w) (ex.nch.Q w) lam (ex.nch.k' w)
      (BlochKatoReduction.Gen.psiAt (D.ntw.sideL (ex.nch.twI w) lam) (ex.nch.psi' w ^ a)))) (by
    have e := hid'.trans (congrArg (fun t => _ * atSide D.ntw b ι t) hT)
    rw [map_mul, ← mul_assoc] at e
    have e' := mul_right_cancel₀ ((map_ne_zero _).2 h0ne) e
    rw [map_mul, h1, h1, e', map_mul, map_mul, map_mul, map_mul, hζ1, one_mul, h4, mul_comm])
  exact ⟨lam, a, u, ha, hu⟩

end GlobalTheory.ThmAMove
