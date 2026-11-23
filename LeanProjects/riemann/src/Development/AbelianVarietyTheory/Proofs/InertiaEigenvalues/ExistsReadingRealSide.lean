import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnivChar
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NoFormsOff
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SubsetTwistExceptionalPlaces
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FrameEquivApply
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GoodBaseDataWeightEqLiftCoeffModuleWeight
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TwistingCharacterAdmissibleGaloisTwistGood
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.StdCharFinitePartRationalEqExpTrace
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ComapRealSubfieldEqIffEqOrIsConjPlace
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdmissibleTwistOfTwistingCharacter
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IrreducibleWeightDescendsToPolynomialModuleStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LiftWeightInfinitesimalCharacterEqDefiniteParamStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ResidueCharacterArtinTameGaloisEqTameValueStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LevelCharactersTypePlacesEqLocalComponentsStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BaseDataTypeCharacterEqLocalComponentStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsStandardFrameKeepsMatricesStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FrameKeepsMatricesMatchesRationalPointsStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsWeightEmbeddingHarmonicPolynomialsLatticesStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AlgebraicFormsLevelGroupEqTwistLevelStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AlgebraicLevelCharacterEqTwistLevelCharacterStatement

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.StandardLattice Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2 Formalism.L2.Host Formalism.L2.DIV Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.TwInputs GlobalTheory.SeriesTie GlobalTheory.ExportSeries NumberField IsDedekindDomain
open Formalism.MainNotions.IntegralHeckeForms (TwOK)
open Formalism.AUTREP (GAf)
open GlobalTheory.FormInner (frameEquiv)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

namespace GlobalTheory.MtRead
variable {D : D7}

theorem half_eq_qpOf {ch : Set (Pl D.host.E)} {Pq : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E)) → PlE D.host}
    (hPq : ∀ v, NG.OverPl (Pq v) v) (hch : ∀ P, IsSplitPl D.host P → (P ∈ ch ↔ P ∈ Set.range Pq)) {s : Finset (PlE D.host)}
    (hs : ∀ P ∈ s, IsSplitPl D.host P) (hc : ∀ P ∈ s, ∀ P', Formalism.BasicNotions.IsConjPl D.host P P' → P' ∈ s) : half ch s = qpOf D Pq s := by
  classical
  ext P
  rw [mem_half, qpOf, Finset.mem_filter]
  refine and_congr_right fun hP => (hch P (hs P hP)).trans ⟨?_, fun h => ?_⟩
  · rintro ⟨v', rfl⟩ v hv
    obtain rfl : v' = v := HeightOneSpectrum.ext ((hPq v').symm.trans hv)
    exact Or.inl rfl
  · let v : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E)) := P.under _
    have hv : NG.OverPl P v := rfl
    rcases h v hv with h | h
    · exact ⟨v, h.symm⟩
    · rcases (GlobalTheory.PlacePair.comap_eq_iff D P (Pq v)).1 (hv.trans (hPq v).symm) with e | e
      · exact ⟨v, e.symm⟩
      · exact absurd (hc P hP _ e) h

theorem delta_tame (i : D.ntw.Tw) {P : PlE D.host} (hP : P ∈ D.ntw.pD i) : ((15 : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal ∧
    ∀ A : ValuationSubring D.nd.Om, IsPlaceOver A P → ∀ σ ∈ Ine (F := D.host.E) A, D.ntw.delta i σ ^ 15 = 1 := by
  refine ⟨fun h => ?_, fun A hA σ hσ => ?_⟩
  · have h1 := D.ntw.delta_tame i P hP
    have h2 : Ideal.absNorm P.asIdeal ∣ 15 ^ Module.finrank ℤ (𝓞 D.host.E) := by
      have := Ideal.absNorm_dvd_absNorm_of_le ((Ideal.span_singleton_le_iff_mem _).2 h)
      rwa [Ideal.absNorm_span_natCast] at this
    have h3 : Nat.Coprime (Ideal.absNorm P.asIdeal) 15 := by
      rw [Nat.Coprime, Nat.gcd_comm, Nat.gcd_rec, h1]
      rfl
    have h4 := Nat.Coprime.eq_one_of_dvd (Nat.Coprime.pow_right _ h3) h2
    exact P.isPrime.ne_top (Ideal.absNorm_eq_one_iff.1 h4)
  · have h1 := pow_card_eq_one' (x := (⟨D.ntw.delta i σ, σ, hσ, rfl⟩ : (Ine (F := D.host.E) A).map (D.ntw.delta i)))
    rw [D.ntw.delta_15 i P hP A hA] at h1
    exact congrArg Subtype.val h1

theorem ek_toKk {ρ : Setup D.ntw} (hρ : ρ.Good) (i : D.ntw.Tw) (b : Bool) (k : ℕ) (x : FractionRing (D.ntw.O i)) :
    ρ.ek i b k (NX.toKk D i k x) = ρ.e i b x := by
  have : (ρ.ek i b k).comp (NX.toKk D i k) = ρ.e i b := by
    refine IsLocalization.ringHom_ext (nonZeroDivisors (D.ntw.O i)) (RingHom.ext fun y => ?_)
    simp only [RingHom.comp_apply, NX.toKk, IsFractionRing.map, IsLocalization.map_eq]
    exact hρ.ek_e i b k y
  exact RingHom.congr_fun this x

section Cell

variable {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL Γ Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks]
  [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat3 D A3 Ks} {cG : G0 R.Pg D.R.r ≃* G0g D.nd}
  {hF : D.host.F = maximalRealSubfield D.host.E} {ρ : Setup D.ntw}

theorem exists_wtMap {cf : CharFrame D} (X : NExpTied D) (cs : CharSide D cf) (hL : R.toLevCh.Is A3.A.μ0) (hρ : ρ.Good)
    (hp : RealPin R cG ρ) (i : D.ntw.Tw) (j : Fin D.R.m) (b : Bool) (k : ℕ) (Q : Finset (PlE D.host))
    (ψ : G D.host.E D.nd.Om →* (D.ntw.Ok i k)ˣ) (P : principalLevelFrame.RowPsi (Vc D j) D.R.nV) (hP : IdFrame hF P)
    (M : NX.MtVReal D i (j.1 + 1) b k Q ψ X.sgnT (X.Wt i (j.1 + 1) b) (X.rhoW i (j.1 + 1) b) (X.tauG i (j.1 + 1) b)) :
    ∃ ω : M.W →ₛₗ[ρ.ek i b k] PolF D (Wc D j).rank (Vc D j).rank,
      WtMap (ρ.B i j b) (frameEquiv P) (D.ntw.Ok i k) (ρ.ek i b k) M.ρ ω := by
  have h1 : 1 ≤ j.1 + 1 := by omega
  have h2 : j.1 + 1 ≤ D.R.m := j.2
  obtain ⟨hn, -⟩ := id hP
  have hemb : ∀ t, NX.kEmb D i b t = (sideEmb D.ntw i b).comp (labLL0 D t) := fun t => rfl
  have he : (fun t => (ρ.e i b).comp (NX.kEmb D i b t)) = tauE D := by
    funext t
    rw [hemb, ← embLL0_labLL0]
    exact RingHom.ext fun x => hρ.e_LL0 i b _
  choose lam0 hlam0 using fun t => X.rhoW_hw i (j.1 + 1) b t h1 h2
  obtain ⟨lam, hlam, T₀, hT₀⟩ := GlobalTheory.T.irreducible_weight_descends_to_polynomial_module D.host.E D.R.nV D.what₂.Tau _ (ρ.e i b) (NX.kEmb D i b)
    (by rw [he]; exact GlobalTheory.StdRat.tauE_injective D)
    (by
      rw [he]
      intro t t' h
      exact (GlobalTheory.StdRat.tauE_cm D _).1 ⟨t', rfl⟩ ⟨t, h⟩)
    (by
      rw [he]
      intro σ
      by_cases h : ∃ t, tauE D t = σ
      · exact h.imp fun _ h => Or.inl h.symm
      · obtain ⟨t, ht⟩ := not_not.1 (mt (GlobalTheory.StdRat.tauE_cm D σ).2 h)
        exact ⟨t, Or.inr (by rw [ht]; ext; simp)⟩)
    (NX.cE D) (fun x => by
      apply D.host.φ₀.injective
      change D.host.φ₀ (D.host.conj x) = _
      rw [IsCMField.complexEmbedding_complexConj, Formalism.HC.HostAx.conjE_apply]) _ (X.rhoW i (j.1 + 1) b) (X.rhoW_irr i _ b h1 h2) lam0 hlam0
  have hB : (ρ.B i j b).w.lam = FWT.lamV D j := GlobalTheory.BaseLiftWeight.lam_eq D T R.toLevCh A3.A.μ0 j _ hL (hρ.base i j b)
    (hp.mu0 i j b) (hp.ap i j b) (hp.am i j b)
  have hw : ∀ t, (lam t).w = fun a : Fin D.R.nV => (FWT.lamV D j t).w (Fin.cast hn.symm a) := fun t => by
    refine eq_of_infOf_eq (lam t).2 (fun a c h => (FWT.lamV D j t).2 h) ?_
    have hi : D.naut.infG D.naut.etaT (embT D t) = {(1 / 2 : ℂ)} := by
      have := (cs.infG D.naut.etaT (fun _ => 1 / 2) (by
        rw [cs.etaT]
        exact ⟨fun _ => 1, fun _ => by norm_num, cf.isEta.inf⟩) (D.eTau t)).1
      rw [show (1 / 2 : ℂ) = ((1 / 2 : ℚ) : ℂ) by norm_num]
      exact this
    rw [hlam, X.rhoW_wt i _ b t h1 h2 _ _ hi (hlam0 t), GlobalTheory.T.lift_weight_infinitesimal_character_eq_definite_param D j hn t]
    rfl
  exact GlobalTheory.T.exists_weightEmbedding_harmonicPolynomials_lattices D _ _ (ρ.B i j b) (hρ.base i j b) _ hF P hP hn _ _ (ρ.ek i b k) (NX.toKk D i k) (sideEmb D.ntw i b)
    (fun x => (ek_toKk hρ i b k _).trans (hρ.e_LL0 i b x)) (hρ.isCoefRing_k i b k) _ (X.rhoW i (j.1 + 1) b) lam
    (fun t a => by rw [hw, hB]; rfl) T₀ hT₀ M.W M.ρ M.bc

end Cell

set_option maxHeartbeats 1600000 in

theorem levMatch (hA : GlobalTheory.Published.GlobalArtinReciprocity) : ∀ (D : D7) (cf : CharFrame D) (Rw : RowSide D) (low : Finset ℕ) (Pq : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E)) → PlE D.host) (S : RatDat D.ntw) (hL : ∀ j, ℕ → PlE D.host → Module.End D.what₂.LL (S.WL j)) (eig : ℕ → D.what₂.FT → ℕ → PlE D.host → ↥D.LL0) (θ : ∀ kk : Fin 2, Multiplicative (ZMod (D.host.g kk)) →* (↥D.LL0)ˣ) (Bs : SideB D cf Rw low Pq S hL eig θ), TauTrue Bs.exp → ValLL0 D cf →
    (∀ v, v ∈ placesOver D.host.E D.host.pde ∨ v ∈ placesOver D.host.E D.host.pde' → IsSplitPl D.host v) →
    (∀ v, NG.OverPl (Pq v) v) →
    ∀ (Γ : Type) [Group Γ] [Fintype Γ] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL Γ Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks]
    [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) (cG : G0 R.Pg D.R.r ≃* G0g D.nd),
    R.toLevCh.Is A3.A.μ0 → R.C = cf → GlobalTheory.Mem.R3.Keep (A3 := A3) R.toRealDat F.lv2 cG →
    ∀ (hF : D.host.F = maximalRealSubfield D.host.E) (PV : ∀ j : Fin D.R.m, principalLevelFrame.RowPsi (Vc D j) D.R.nV),
    (∀ j, IdFrame hF (PV j)) → ∀ (ρ : Setup D.ntw), ρ.Good → RealPin R cG ρ → ρ.LevelOf D.nexp →
    (∀ i P, IsSplitPl D.host P → (P ∈ ρ.ch i ↔ P ∈ Set.range Pq)) →
    ∀ i (j : Fin D.R.m) b k Q ψ (hAd : NX.AdmTw D i k Q ψ), TwOK i k Q ψ →
      LevMatch (ρ.B i j b) (ρ.tw i b k Q ψ) (frameEquiv (PV j)) (ρ.ek i b k)
        (Bs.exp.mtV i (j.1 + 1) b k Q ψ (by omega) (by omega) hAd).J (Bs.exp.mtV i (j.1 + 1) b k Q ψ (by omega) (by omega) hAd).χ := by
  intro D cf Rw low Pq S hL eig θ Bs hτ hV hspl hPq Γ _ _ Pl0 I0 T A3 Ks _ _ _ R F cG hlev hC hK hF PV hPV ρ hρ hp hlv hch
    i j b k Q ψ hAd hT
  have h1 : 1 ≤ j.1 + 1 := by omega
  have h2 : j.1 + 1 ≤ D.R.m := j.2
  obtain ⟨plg, iso, hplg, -, -, hiso⟩ := hK.grp
  obtain ⟨τ, hτ⟩ := hτ
  have hB := hρ.base i j b
  obtain ⟨hg, ha, -⟩ := GlobalTheory.TwistGood.tw_good D D.nd D.ntw ρ hρ i j b k Q ψ hT
  have hβ : (ρ.B i j b).F.βS = 1 := (hp.frS i j b).trans (hK.beta.1 j)
  have hplg' : ∀ kv, ((plg kv : R.Pg) : Pl D.host.E) = NX.pG D kv := hplg
  have hPg : ∀ PP, PP ∈ (ρ.B i j b).G.Pg ↔ ∃ kv, PP = NX.pG D kv := fun PP => by
    rw [hp.Pg]
    exact ⟨fun h => ⟨plg.symm ⟨PP, h⟩, by rw [← hplg', Equiv.apply_symm_apply]⟩, fun ⟨kv, h⟩ => h ▸ hplg' kv ▸ (plg kv).2⟩
  have hinj : Function.Injective (NX.pG D) := fun kv kv' h => plg.injective (Subtype.ext (by rw [hplg', hplg', h]))
  have hQ : (ρ.tw i b k Q ψ).Q = (Bs.exp.mtV i (j.1 + 1) b k Q ψ h1 h2 hAd).QP := by
    rw [(Bs.pq i _ b k Q ψ h1 h2 hAd).1]
    exact half_eq_qpOf hPq (hch i) hT.1 (GlobalTheory.TwistGood.ramExactly_conj D.ntw ψ _ hT.2.2.2.1 hT.2.2.2.2.2.1)
  have hD : (ρ.B i j b).de.Q = (Bs.exp.mtV i (j.1 + 1) b k Q ψ h1 h2 hAd).DP := by
    rw [(Bs.pq i _ b k Q ψ h1 h2 hAd).2, hρ.delta]
    refine half_eq_qpOf hPq (hch i) (fun P hP => hspl P ?_)
      (GlobalTheory.TwistGood.ramExactly_conj D.ntw (D.ntw.delta i) _ (D.ntw.delta_anti i) (D.ntw.delta_ram i))
    have h3 : P ∈ (D.ntw.pD i : Set _) := hP
    rw [D.ntw.pD_eq] at h3
    split_ifs at h3
    exacts [Or.inr h3, Or.inl h3]
  have key : ∀ (kv : Σ k : Fin 2, D.nd.PlG k) (PP : R.Pg) (_ : (PP : Pl D.host.E) = NX.pG D kv)
      (is : ZMod (D.host.g kv.1) ≃+* kP PP.1), (∀ g, R.eG g PP = Formalism.UG.bc (is : ZMod (D.host.g kv.1) →+* kP PP.1)
        ((R.eG.trans cG) g kv)) → ∃ is' : ZMod (D.host.g kv.1) ≃+* kP (NX.pG D kv), ∀ (g : G0g D.nd) (h : NX.pG D kv ∈ R.Pg) a c,
          (cG.symm g ⟨NX.pG D kv, h⟩).val a c = is' ((g kv).val a c) := by
    rintro kv ⟨PP, hPP⟩ rfl is h
    refine ⟨is, fun g _ a c => ?_⟩
    have := h (R.eG.symm (cG.symm g))
    rw [MulEquiv.trans_apply, MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply] at this
    exact congrArg (fun x => x.val a c) this
  choose is his using fun kv => key kv (plg kv) (hplg' kv) (iso kv) fun g => hiso g kv
  have hgrp : ∀ (g : G0g D.nd) kv (h : NX.pG D kv ∈ (ρ.B i j b).G.Pg) (a c : Fin (Wc D j).rank),
      (ρ.eG i j b g ⟨NX.pG D kv, h⟩).val a c = is kv ((g kv).val (Fin.cast (FWT.rank_Wc j) a) (Fin.cast (FWT.rank_Wc j) c)) :=
    fun g kv h a c => (hp.grp i j b g _ h (hp.Pg i j b ▸ h) a c).trans (his kv g _ _ _)
  refine ⟨GlobalTheory.T.algebraicForms_levelGroup_eq_twistLevel D i j b k Q ψ _ _ _ _ _ _ _ hF (PV j) (hPV j) hβ hPg hinj hQ hD is _ hgrp (hlv.U_eq i j b) Bs.exp.U_eq,
    GlobalTheory.T.algebraicLevelCharacter_eq_twistLevelCharacter D i j b k Q ψ _ _ _ _ _ _ _ hF (PV j) (hPV j) hβ hPg hinj hQ hD is _ hgrp (hlv.U_eq i j b) Bs.exp.U_eq ?_
      (ρ.e i b) (ρ.ek i b k) (ek_toKk hρ i b k) (Bs.exp.psiU_gen i b) (hlv.psiU_eq i j b) ?_ ?_ ?_⟩
  · rw [← hQ, ← hD]
    exact ha.2.symm
  · intro kv x z hz
    have hmem := (hPg _).2 ⟨kv, rfl⟩
    have hz' : (z : kP (NX.pG D kv)) = Ideal.Quotient.mk _ (((x : ZMod (D.host.g kv.1)).val : ℕ) : 𝓞 D.host.E) := by
      haveI : NeZero (D.host.g kv.1) := ⟨(D.host.g_prime _).ne_zero⟩
      rw [hz, map_natCast, ← map_natCast (is kv), ZMod.natCast_zmod_val]
    have hu : ((((x : ZMod (D.host.g kv.1)).val : ℕ) : 𝓞 D.host.E) : D.host.E) ≠ 0 := fun h => z.ne_zero (by
      rw [hz', RingOfIntegers.coe_eq_zero_iff.1 h, map_zero])
    rw [GlobalTheory.T.base_data_type_character_eq_local_component D _ _ _ hB (cf.mu0 j) (by rw [hp.mu0, ← hC]; exact hlev.mu0 j) _ hmem _ hu z hz', hτ i _ b kv x h1 h2, hρ.e_LL0,
      GlobalTheory.T.levelCharacters_typePlaces_eq_local_components hA D cf Rw low Pq S hL eig θ Bs hV τ hτ j kv x _ hu (by rw [sub_self]; exact zero_mem _)]
  · intro PP hPP u hu z hz
    rw [← hQ] at hPP
    have hl : ((D.ntw.l i : ℕ) : 𝓞 D.host.E) ∉ PP.asIdeal := (hAd.1 PP (mem_half.1 hPP).1).2
    have := GlobalTheory.T.residue_character_artin_tame_galois_eq_tame_value hA D ρ.rc hρ.rc _ (ρ.eOk i b k) ψ hT.2.2.1 PP _ hl (fun _ _ σ _ => hAd.2.2.2.2.1 σ) (hg.split.isIdemAt hPP) _
      (hg.res PP hPP) 1 u hu z hz
    rw [zpow_one] at this
    rw [Bs.exp.sgnT_one]
    exact this
  · intro PP hPP u hu z hz
    rw [← hD] at hPP
    have hde := hB.de
    have hres := hde.res PP hPP
    have hid := hde.split.isIdemAt hPP
    have hchi : (ρ.B i j b).de.chi = GlobalTheory.SeriesTie.charOf ρ.rc ((ρ.eO i b).comp (algebraMap (D.ntw.O0 i) (D.ntw.O i)))
        (Formalism.MainNotions.BlochKatoReduction.Gen.psiAt b (D.ntw.delta i)) := by rw [hρ.delta]; rfl
    rw [hchi] at hres
    have hPD : PP ∈ D.ntw.pD i := by
      rw [hρ.delta] at hPP
      exact (mem_half.1 hPP).1
    obtain ⟨h15, hord⟩ := delta_tame i hPD
    have hval : ∀ y : D.ntw.O0 i, ρ.ek i b k (NX.ofO0 D i k y) = ((ρ.eO i b).comp (algebraMap (D.ntw.O0 i) (D.ntw.O i))) y :=
      fun y => hρ.ek_e i b k _
    rw [hval, Bs.exp.sgnT_one]
    cases b
    · have hk : IsOpen (((D.ntw.delta i)⁻¹).ker : Set (G D.host.E D.nd.Om)) := by
        convert D.ntw.delta_open i using 1
        ext g
        simp [MonoidHom.mem_ker]
      have := GlobalTheory.T.residue_character_artin_tame_galois_eq_tame_value hA D ρ.rc hρ.rc _ _ (D.ntw.delta i)⁻¹ hk PP 15 h15
        (fun A hA σ hσ => ⟨1, by rw [pow_one, MonoidHom.inv_apply, inv_pow, hord A hA σ hσ, inv_one]⟩) hid _ hres (-1) u hu z hz
      have e1 : NX.tameVal (D.ntw.delta i)⁻¹ PP (-1) u = (NX.tameVal (D.ntw.delta i) PP (-1) u)⁻¹ := by
        unfold NX.tameVal
        split_ifs
        · rfl
        · exact inv_one.symm
      rw [e1, zpow_neg_one, map_units_inv, inv_inj] at this
      exact this
    · have := GlobalTheory.T.residue_character_artin_tame_galois_eq_tame_value hA D ρ.rc hρ.rc _ _ (D.ntw.delta i) (D.ntw.delta_open i) PP 15 h15
        (fun A hA σ hσ => ⟨1, by rw [pow_one, hord A hA σ hσ]⟩) hid _ hres 1 u hu z hz
      rw [zpow_one] at this
      exact this

set_option maxHeartbeats 1600000 in

theorem exists_reading : GlobalTheory.Published.GlobalArtinReciprocity → ∀ (D : D7) (cf : CharFrame D) (Rw : RowSide D) (low : Finset ℕ) (Pq : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E)) → PlE D.host) (S : RatDat D.ntw) (hL : ∀ j, ℕ → PlE D.host → Module.End D.what₂.LL (S.WL j)) (eig : ℕ → D.what₂.FT → ℕ → PlE D.host → ↥D.LL0) (θ : ∀ kk : Fin 2, Multiplicative (ZMod (D.host.g kk)) →* (↥D.LL0)ˣ) (Bs : SideB D cf Rw low Pq S hL eig θ), TauTrue Bs.exp → CharSide D cf → ValLL0 D cf →
    (∀ v, v ∈ placesOver D.host.E D.host.pde ∨ v ∈ placesOver D.host.E D.host.pde' → IsSplitPl D.host v) →
    (∀ v, NG.OverPl (Pq v) v) →
    ∀ (Γ : Type) [Group Γ] [Fintype Γ] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL Γ Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks]
    [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) (cG : G0 R.Pg D.R.r ≃* G0g D.nd),
    R.toLevCh.Is A3.A.μ0 → R.C = cf → GlobalTheory.Mem.R3.Keep (A3 := A3) R.toRealDat F.lv2 cG →
    ∀ (hF : D.host.F = maximalRealSubfield D.host.E) (PV : ∀ j : Fin D.R.m, principalLevelFrame.RowPsi (Vc D j) D.R.nV),
    (∀ j, IdFrame hF (PV j)) → ∀ (ρ : Setup D.ntw), ρ.Good → RealPin R cG ρ → ρ.LevelOf D.nexp →
    (∀ i P, IsSplitPl D.host P → (P ∈ ρ.ch i ↔ P ∈ Set.range Pq)) →
    ∃ rdV : ∀ i (j : Fin D.R.m) b k Q ψ, D.nexp.MtV i ((j : ℕ) + 1) b k Q ψ →ₛₗ[ρ.ek i b k]
        (Bridge.Gf (Vc D j) → PolF D (Wc D j).rank (Vc D j).rank),
      (∀ i j b k Q ψ, TwOK i k Q ψ → Function.Injective (rdV i j b k Q ψ) ∧
        (∀ F ∈ ρ.mt i j b k Q ψ, F ∈ Set.range (rdV i j b k Q ψ)) ∧
        Submodule.span (FractionRing (D.ntw.Ok i k)) {f | rdV i j b k Q ψ f ∈ ρ.mt i j b k Q ψ} = ⊤) ∧
      (∀ i (j : Fin D.R.m) b k Q ψ (hA : NX.AdmTw D i k Q ψ), TwOK i k Q ψ →
        ∃ ω : (Bs.exp.mtV i (j.1 + 1) b k Q ψ (by omega) (by omega) hA).W →ₛₗ[ρ.ek i b k] PolF D (Wc D j).rank (Vc D j).rank,
          Function.Injective ω ∧ ∀ f g, rdV i j b k Q ψ f ((finHom _).rangeRestrict ((PV j).ψ g)) =
            ω (((Bs.exp.mtV i (j.1 + 1) b k Q ψ (by omega) (by omega) hA).real f).1 g)) := by
  intro hA D cf Rw low Pq S hL eig θ Bs hτ cs hV hspl hPq Γ _ _ Pl0 I0 T A3 Ks _ _ _ R F cG hlev hC hK hF PV hPV ρ hρ hp hlv hch
  have cell : ∀ i (j : Fin D.R.m) b k Q ψ, ∃ r : D.nexp.MtV i ((j : ℕ) + 1) b k Q ψ →ₛₗ[ρ.ek i b k]
      (Bridge.Gf (Vc D j) → PolF D (Wc D j).rank (Vc D j).rank), ∀ hT : TwOK i k Q ψ, (Function.Injective r ∧
        (∀ F ∈ ρ.mt i j b k Q ψ, F ∈ Set.range r) ∧
        Submodule.span (FractionRing (D.ntw.Ok i k)) {f | r f ∈ ρ.mt i j b k Q ψ} = ⊤) ∧
        ∃ ω : (Bs.exp.mtV i (j.1 + 1) b k Q ψ (by omega) (by omega) (admissible_twist_of_twisting_character hT)).W →ₛₗ[ρ.ek i b k]
            PolF D (Wc D j).rank (Vc D j).rank, Function.Injective ω ∧ ∀ f g, r f (frameEquiv (PV j) g) =
          ω (((Bs.exp.mtV i (j.1 + 1) b k Q ψ (by omega) (by omega) (admissible_twist_of_twisting_character hT)).real f).1 g) := by
    intro i j b k Q ψ
    by_cases hT : TwOK i k Q ψ
    · obtain ⟨hg, ha, -⟩ := GlobalTheory.TwistGood.tw_good D D.nd D.ntw ρ hρ i j b k Q ψ hT
      obtain ⟨ω, hω⟩ := exists_wtMap Bs.exp cs hlev hρ hp i j b k Q ψ (PV j) (hPV j)
        (Bs.exp.mtV i (j.1 + 1) b k Q ψ (by omega) (by omega) (admissible_twist_of_twisting_character hT))
      obtain ⟨r, r1, r2, r3, r4⟩ := read_cell (ρ.B i j b) (hρ.base i j b) (ρ.tw i b k Q ψ) (frameEquiv (PV j)) (D.ntw.Ok i k)
        (ρ.ek i b k) (hρ.isCoefRing_k i b k) _ _ _ ω (GlobalTheory.T.frameKeepsMatrices_matches_rationalPoints D _ _ hF (PV j) (hPV j)).1 hω
        (levMatch hA D cf Rw low Pq S hL eig θ Bs hτ hV hspl hPq Γ Pl0 I0 T A3 Ks R F cG hlev hC hK hF PV hPV ρ hρ hp hlv hch
          i j b k Q ψ (admissible_twist_of_twisting_character hT) hT) _ (hρ.classes i j b _ hg ha).reps
        (Bs.exp.mtV i (j.1 + 1) b k Q ψ (by omega) (by omega) (admissible_twist_of_twisting_character hT)).real
      exact ⟨r, fun _ => ⟨⟨r1, r2, r3⟩, ω, hω.1, r4⟩⟩
    · exact ⟨0, fun h => absurd h hT⟩
  choose r hr using cell
  exact ⟨r, fun i j b k Q ψ hT => (hr i j b k Q ψ hT).1, fun i j b k Q ψ _ hT => (hr i j b k Q ψ hT).2⟩

theorem exists_idFrame : ∀ (D : D7) (hF : D.host.F = maximalRealSubfield D.host.E) (j : Fin D.R.m), FWT.VStd D j → ∃ P : principalLevelFrame.RowPsi (Vc D j) D.R.nV, IdFrame hF P ∧ GlobalTheory.Mem.R3.StdFrame hF P := GlobalTheory.T.exists_standard_frameKeepsMatrices

end GlobalTheory.MtRead
end
