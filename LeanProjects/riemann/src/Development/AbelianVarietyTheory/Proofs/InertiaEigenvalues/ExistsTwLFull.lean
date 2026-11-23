import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsAuxiliaryHeckeCharacter
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NotTeichTrivOfIsDelta
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.TwistBaseCoefficientRingResidueFieldFinite
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsValueTiedOfIsToricElt
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsCMValueHeckeCharacterAuxiliarySetOfEmpty
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LambdaDataAtSide
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ToricCharacterIsCMHostValueDatumStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToricSumEqHeckeLValueMulAuxiliaryFactorsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeLNeZeroNat
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsTwoReadings
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LevelLeConjugateSplit
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SplitsInCMFieldPlaceBelowOfCompletelySplit
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ToricLam0UnitaryTrivOnMaxRealSubfield
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ConductorExponentAtPlaces
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsPlaceOverMoveValCc

noncomputable section

namespace GlobalTheory.LamTie.TrueList

open NumberField IsDedekindDomain ReciprocityTheory.Gal Formalism.ConjugateSelfDual Formalism.BasicNotions Formalism.MainNotions Formalism.FrobeniusOrbits Formalism.L2.Host GlobalTheory.CMVal GlobalTheory.ToricDenom GlobalTheory.ToricRational
open GlobalTheory.HeckeGal GlobalTheory.GalChar GlobalTheory.HeightCounting GlobalTheory.ToricDistribution

attribute [local instance 10000] GlobalTheory.GalChar.isTorsionFree_field

theorem exists_twL_full (hA : GlobalTheory.Published.GlobalArtinReciprocity) (hR : RatioConj) (D : D7) (N : NData D.R D.host D.what₂)
    (hE : IsEmpty N.Loc) (T : TwR D.LL0 N) (Z : LamDat D) (hZ : Z.Ok)
    (art : Ideles D.host.E →* Gab D.host.E N.Om) (ha : IsGlobalArtin art)
    (κ : ∀ i, FractionRing (T.O0 i) →+* Qbar (T.l i)) (ι : ∀ i, Qbar (T.l i) ≃+* ℂ)
    (hκ : ∀ i (z : ℤ_[T.l i]), κ i (algebraMap (T.O0 i) _ (algebraMap ℤ_[T.l i] (T.O0 i) z)) =
      algebraMap ℚ_[T.l i] (Qbar (T.l i)) (z : ℚ_[T.l i]))
    (hι : ∀ i (x : D.LL0), ι i (κ i (T.emb0 i x)) = D.what₂.embLL (x : D.what₂.LL))
    (hμ : ∀ i j, (Z.C.mu0 j).ValuesIn 0 ((ι i).toRingHom.comp (κ i)))
    (hχ : ∀ i a, (Z.chi a).ValuesIn 0 ((ι i).toRingHom.comp (κ i)))
    (hδ : ∀ i, IsGal art (κ i) (ι i) (Z.C.delAt (T.l i)) 0 (T.delta i))
    (hS : ∀ i P, (below P).asIdeal ∣ cond0 D.host Z.w0 → P ∈ T.S0 i)
    (hT : ∀ a w, OverP D.host D.host.pde w ∨ OverP D.host D.host.pde' w → ∃ w', below w' = below w ∧ TeichTriv (Z.chi a) w') :
    ∃ (L : TwL T) (e : ∀ i, L.abelian₂ i ≃ Idx D.R),
      (∀ i lam, L.jL i lam = (e i lam).1.1 + 1 ∧ L.sideL i lam = (e i lam).2.2.2 ∧ L.s2 i lam = 2 * ((e i lam).2.2.1.1 : ℤ) ∧
        (∃ n r, IsGal art (κ i) (sideIso (ι i) (e i lam).2.2.2) (Z.lam0 (T.l i) (e i lam).1 (e i lam).2.1) n r ∧
          L.lamG i lam = (Units.map (algebraMap (T.O0 i) (T.O i)).toMonoidHom).comp r) ∧
        ∀ P, L.qs i lam P = ((Ideal.absNorm P.asIdeal : ℕ) : FractionRing (T.O i)) ^ (-((e i lam).2.2.1.1 : ℤ))) ∧
      ∀ F : TwF T, IsLamTieFull (T.ntw hE F L) Z := by
  let C : GlobalTheory.Mem.Chr.HFrame D.host (fun j => eExp D j) :=
    ⟨Z.C.P, Z.C.W, Z.C.mu0, Z.C.eta, Z.C.chiPsi, Z.C.del, Z.C.del', Z.C.isMu0, Z.C.isEta, Z.C.isChi, Z.C.isDel, Z.C.isDel'⟩
  have hcu : ∀ i a P, P ∉ T.S0 i → (Z.chi a).UnrAt P := fun i a P hP => chi_unr hZ a fun h => hP (hS i P h)
  have hpD : ∀ i v, v ∈ T.pD i ↔ OverP D.host (if T.l i = D.host.pde then D.host.pde' else D.host.pde) v := fun i v => by
    rw [← Finset.mem_coe, T.pD_eq]; rfl
  have hlu : ∀ i j a P, P ∉ T.S0 i → (Z.lam0 (T.l i) j a).UnrAt P := fun i j a P hP =>
    (((Z.C.isMu0 j).unr P fun k hk => hP (T.placesOver_subset_exceptional i k hk)).mul
      ((inertialOrderFifteenChar_auxiliaryPrime_spec C (l := T.l i)).2.2.2.2.unr P fun hk => hP (T.primes_subset_exceptional i ((hpD i P).2 hk)))).mul (hcu i a P hP).inv
  choose K f f' hf hf' hK using fun i => exists_two_readings ((ι i).toRingHom.comp (κ i))
  have key := fun (i : T.Tw) (j a : Fin D.R.m) (b : Bool) =>
    hostHeckeFrame_toric_quotient_character C T.cc_cm ha (fun j τ => (D.hc _).e_int j) (T.l i) (T.O0 i) (T.twistBaseCoefficientRing_isAdic i) (κ i) (hκ i) (ι i) (K i)
      (K i).subtype (f i) (f' i) (hf i) (hf' i) (T.pD i) (T.pD_eq i) (T.delta i) (hδ i) (T.O i) (T.O_adic i) (T.O_l i) j b (Z.chi a) (Z.c a) (hZ.aux a).triv
      (by
        obtain ⟨n, hn, h⟩ := (hZ.aux a).inf
        have : n = fun τ => 2 * Z.c a τ := funext fun τ => by have := hn τ; beta_reduce at this; exact_mod_cast this
        exact this ▸ h)
      (fun v hv => by
        have h4 : OverP D.host D.host.pde v ∨ OverP D.host D.host.pde' v := by
          have := (hpD i v).1 hv
          split_ifs at this
          exacts [Or.inr this, Or.inl this]
        obtain ⟨w', e, h⟩ := hT a v h4
        exact chi_teich hZ a h4 e h)
      (valuesIn_of_unitary (hK i) (Z.C.isMu0 j).unitary (hμ i j))
      (valuesIn_of_unitary (hK i) (delAt_unitary_triv Z.C _).1 (valuesIn_of_isGal ha (hδ i)))
      (valuesIn_of_unitary (hK i) (hZ.aux a).unitary (hχ i a)) (T.S0 i) (T.twistExcludedPlaces_contains_residueChar i) (T.placesOver_subset_exceptional i) (T.primes_subset_exceptional i) (hcu i a)
  choose r g Xv h1 h2 h3 h4 h5 h6 h7 using key
  let L : (∀ i Q, Idx D.R → T.RCG i Q → FractionRing (T.O i)) → TwL T := fun th =>
    { abelian₂ := fun _ => Idx D.R
      jL := fun _ x => x.1.1 + 1
      sideL := fun _ x => x.2.2.2
      s2 := fun _ x => 2 * (x.2.2.1.1 : ℤ)
      jL_range := fun _ x => ⟨by omega, x.1.2⟩
      lamG := fun i x => g i x.1 x.2.1 x.2.2.2
      lamG_cont := fun i x => h3 i _ _ _
      lamG_unr := fun i x => h4 i _ _ _
      lamG_pD := fun i x => h5 i _ _ _
      lamG_anti := fun i x => h6 i _ _ _
      Xv := fun i x => Xv i x.1 x.2.1 x.2.2.2
      Xv_def := fun i x P hP => h7 i _ _ _ P hP _ (N.plOm.2 P)
      qs := fun i x P => ((Ideal.absNorm P.asIdeal : ℕ) : FractionRing (T.O i)) ^ (-(x.2.2.1.1 : ℤ))
      qs_sq := fun i x P _ => by rw [← zpow_natCast, ← zpow_mul]; congr 1; push_cast; ring
      qs_conj := fun i x P P' h => by
        rw [show Ideal.absNorm P'.asIdeal = Ideal.absNorm P.asIdeal from GlobalTheory.TwistDet.normV_conj h]
      th := th }
  have hcl : ∀ th i (x : Idx D.R), (L th).jL i x = x.1.1 + 1 ∧ (L th).sideL i x = x.2.2.2 ∧
      (L th).s2 i x = 2 * (x.2.2.1.1 : ℤ) ∧
      (∃ n r, IsGal art (κ i) (sideIso (ι i) x.2.2.2) (Z.lam0 (T.l i) x.1 x.2.1) n r ∧
        (L th).lamG i x = (Units.map (algebraMap (T.O0 i) (T.O i)).toMonoidHom).comp r) ∧
      ∀ P, (L th).qs i x P = ((Ideal.absNorm P.asIdeal : ℕ) : FractionRing (T.O i)) ^ (-(x.2.2.1.1 : ℤ)) := fun th i x => by
    refine ⟨rfl, rfl, rfl, ?_, fun _ => rfl⟩
    obtain ⟨n, hn⟩ := h1 i x.1 x.2.1 x.2.2.2
    exact ⟨n, _, hn, h2 i _ _ _⟩
  rcases isEmpty_or_nonempty (TwF T) with hF | ⟨⟨F₀⟩⟩
  · exact ⟨L fun _ _ _ _ => 0, fun _ => Equiv.refl _, hcl _, fun F => hF.elim F⟩
  let X₀ := T.ntw hE F₀ (L fun _ _ _ _ => 0)
  choose ι₀ hι₀ using fun i => exists_reading X₀ i (κ i) (ι i) (hκ i)
  have m0 : ∀ i, (∀ x : D.LL0, ι₀ i (D.what₂.embLL (x : D.what₂.LL)) = toBar X₀ i (T.emb0 i x)) ∧
      ∀ x : Idx D.R, IsLam X₀ Z i (atSide X₀ x.2.2.2 (ι₀ i)) x x.1 x.2.1 x.2.2.1.1 := fun i => by
    refine ⟨fun x => by rw [← hι i x]; exact hι₀ i true _, fun x => ⟨rfl, ⟨rfl, ?_, ?_⟩, fun P hP => ?_⟩⟩
    · exact_mod_cast x.2.2.1.2.1
    · exact_mod_cast x.2.2.1.2.2
    · obtain ⟨n, hn⟩ := h1 i x.1 x.2.1 x.2.2.2
      exact xv_mul_val X₀ i (hι₀ i x.2.2.2) ha hn (h2 i _ _ _) hP (hlu i _ _ P hP)
  have hL : ToricSumFormula := GlobalTheory.T.toric_sum_eq_hecke_L_value_mul_auxiliary_factors exists_isHeckeL_of_hasInf
  have tkey : ∀ i (x : Idx D.R), ∃ t : ∀ Q, T.RCG i Q → FractionRing (T.O i),
      ∀ th : ∀ i Q, X₀.abelian₂ i → X₀.RCG i Q → FractionRing (X₀.O i), (∀ Q, th i Q x = t Q) →
        IsThOf (setTh X₀ th) i (atSide X₀ x.2.2.2 (ι₀ i)) x (phi D.host) x.2.2.1.1 (Z.kap x.1 x.2.1 x.2.2.1.1)
          (cond0 D.host Z.w0) (Z.lam0 (T.l i) x.1 x.2.1) := fun i x => by
    have hl := (m0 i).2 x
    have hD := GlobalTheory.T.isHostDatum_kap_lam0_of_ok D Z hZ (T.l i) x.1 x.2.1 x.2.2.1.1 (by exact_mod_cast hl.2.1.2.1) hl.2.1.2.2
    exact exists_th_of hA hR hL (atSide_emb_mem (m0 i).1 _) hD (hS i) hl.2.2
  choose t ht using tkey
  let th : ∀ i Q, Idx D.R → T.RCG i Q → FractionRing (T.O i) := fun i Q x => t i x Q
  refine ⟨L th, fun _ => Equiv.refl _, hcl th, fun F => ?_⟩
  refine isLamTieFull_of_labels (fun _ x => x.1) (fun _ x => x.2.1) (fun _ x => x.2.2.1.1) (fun i _ => hS i)
    (fun i _ => ⟨ι₀ i, (m0 i).1, fun x => ⟨(m0 i).2 x, ht i x th fun _ => rfl⟩⟩)
    (fun i _ j a s b hs hs' => ⟨(j, a, ⟨s, hs, hs'⟩, b), rfl, rfl, rfl, rfl⟩)

end GlobalTheory.LamTie.TrueList
