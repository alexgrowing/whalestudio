import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LiftQMk
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TwistedGaloisRepCharacterBlocks
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TwistedDualFamiliesContinuous
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FiniteDimensionalKsOne
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsUniformiser
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExtendUnramEmb
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsTwistRepTwist
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TwistMRepVCont
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CrysWpRTw
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IncLocChiEpsUZpow
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ChiTContIsCrysMultV
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.JTilShiftBlock
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ReflSBlockJIff
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ScaleRootsProdIcc
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pass GlobalTheory.Cut GlobalTheory.UseLoc Module Classical

noncomputable section
namespace GlobalTheory.UseLocInst

set_option maxHeartbeats 1000000 in

theorem exists_setC : ∀ (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (i : D.nd.Loc)
    (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i)))
    (π : D.nd.X i), tableLineDegreeTwo.adm20 D HW F → AdmissibleParameterJ.ConclusionJa D → GoodR D.nd i r → π ∈ D.nd.Z i → TruncatedSeriesCountingIdentities.admG2 i r ρ π →
    TruncatedSeriesCountingIdentities.admG3 i r ρ π → TruncatedSeriesCountingIdentities.FamilyContinuous i r → TruncatedSeriesCountingIdentities.SemisimpleDecomposition i r ρ π → TruncatedSeriesCountingIdentities.CyclotomicInertiaImage (D := D) i → 5 ≤ D.nd.l i →
    D.nd.l i ∉ D.host.small → D.nd.l i ≠ D.host.q → D.nd.l i ≠ D.host.d →
    (∀ (n : ℕ) [NeZero n] (up : ZMod n → Bool) (τ : ZMod n → D.what₂.Tau), ∃ (h w η : ZMod n → ℕ) (typ : ZMod n → Bool)
      (U : ZMod n → Multiset ℤ), tableLineDegreeTwo.PositionHyps (D.nd.l i) n D.R.t h w η typ U ∧ ∀ (a : ZMod n) (b : ℤ),
        ((U a).count (b + w a) = 1 ↔ (b : ℚ) ∈ AdmissibleParameterJ.JW D (up a) (D.nd.j i) (τ a)) ∧ (U a).count (b + w a) ≤ 1) →
    ∀ (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i)),
      ∃ (C : TruncatedSeriesCountingIdentities.CoefExt D i w hw) (hA : CaseA (D.nbr i w hw).Kw C.LL) (lam : ↥(OL C.LL)) (_ : Irreducible lam)
        (θ : Br.G D.nbr i w hw →* (↥(OL C.LL))ˣ)
        (h w' η : ZMod (finrank ℚ_[D.nd.l i] ↥(K0 (D.nbr i w hw).Kw)) → ℕ)
        (typ : ZMod (finrank ℚ_[D.nd.l i] ↥(K0 (D.nbr i w hw).Kw)) → Bool)
        (U : ZMod (finrank ℚ_[D.nd.l i] ↥(K0 (D.nbr i w hw).Kw)) → Multiset ℤ),
        SetC HW r ρ π C hA lam θ h w' η typ U := by
  intro D HW F i r ρ π hB3 hJa hGood hZ hG2 hG3 hCont hDec hEps h5 hsm hq hd hPosition w hw
  obtain ⟨C, hA⟩ := GlobalTheory.UseLoc.exists_caseA_enl D i w hw hsm hq hd
  obtain ⟨lam, hlam⟩ := GlobalTheory.UseLocUnif.exists_uniformiser (D.nd.l i) C.LL
  obtain ⟨ep, hJ⟩ := hJa
  have hτ : ∀ a : ZMod (finrank ℚ_[D.nd.l i] ↥(K0 (D.nbr i w hw).Kw)),
      ∃ τ : Br.Kw D.nbr i w hw →ₐ[ℚ_[D.nd.l i]] ↥C.LL.1, tableLineDegreeTwo.Over (embC HW C hA) a τ ∧
        ∀ τ' : Br.Kw D.nbr i w hw →ₐ[ℚ_[D.nd.l i]] ↥C.LL.1, tableLineDegreeTwo.Over (embC HW C hA) a τ' → τ' = τ :=
    fun a => GlobalTheory.UseLoc.extendUnramEmb (D.nd.l i) (D.nbr i w hw).Kw C.LL hA.1 (embC HW C hA a)
  choose τa _hτa hτu using hτ
  have hJτ := fun a => hJ i r hGood w hw C (τa a)
  choose gA ρA _hRead hX hW using hJτ
  haveI := (Br.PD D.loc D.nbr i w hw).finK₀
  haveI : NeZero (finrank ℚ_[D.nd.l i] ↥(K0 (D.nbr i w hw).Kw)) := ⟨Module.finrank_pos.ne'⟩
  obtain ⟨h, w', η, typ, U, hS, hU⟩ := hPosition _ (fun a => decide (AdmissibleParameterJ.TypeU D ep (gA a))) ρA
  obtain ⟨θ, hθc, hθcr, hθj⟩ := (hB3 (D.nd.l i) (D.nbr i w hw).Kw C.LL hA).1 (fun a => (w' a : ℤ))
  have hθj' : ∀ a τ, tableLineDegreeTwo.Over (embC HW C hA) a τ → ∀ b,
      multV (Br.PD D.loc D.nbr i w hw) (Formalism.WeaklyAdmissibleFiltrations.charRep (tableLineDegreeTwo.charL (LL := ↥C.LL.1) θ)) τ b =
        if b = (w' a : ℤ) then 1 else 0 := hθj
  have hθnz : ∀ a τ, tableLineDegreeTwo.Over (embC HW C hA) a τ →
      multV (Br.PD D.loc D.nbr i w hw) (Formalism.WeaklyAdmissibleFiltrations.charRep (tableLineDegreeTwo.charL (LL := ↥C.LL.1) θ)) τ (w' a) ≠ 0 := by
    intro a τ hO
    rw [hθj' a τ hO]
    simp
  have hWp : ∀ a τ, tableLineDegreeTwo.Over (embC HW C hA) a τ → ∀ b : ℤ,
      multV (Br.PD D.loc D.nbr i w hw) (matRep (TruncatedSeriesCountingIdentities.locC C (WpO D.nd i ρ π))) τ b =
        ((U a).count (b + w' a) : ℤ) := by
    intro a τ hO b
    rw [hτu a τ hO, ((hW a) ρ π hZ hDec b).2.1]
    obtain ⟨h1, h2⟩ := hU a b
    by_cases hb : ((b : ℤ) : ℚ) ∈ AdmissibleParameterJ.JW D (decide (AdmissibleParameterJ.TypeU D ep (gA a))) (D.nd.j i) (ρA a)
    · rw [if_pos hb, h1.2 hb]
      simp
    · rw [if_neg hb]
      have : (U a).count (b + w' a) ≠ 1 := fun e => hb (h1.1 e)
      omega
  have hL6 := GlobalTheory.UseLoc.crys_Wp_rTw D i r ρ π w hw C hGood hZ hG2 hDec
  have hL4 := GlobalTheory.UseLoc.TwistCrysW.isCrys_and_multV D i w hw C
  have hL5 := GlobalTheory.UseLoc.twistM_repV_cont D i w hw C
  have hWcont : Continuous fun g => WpO D.nd i ρ π g :=
    (GlobalTheory.Pass.stepSub_holds D i r ρ hGood π hDec {π} rfl).1.1
  refine ⟨C, hA, lam, hlam, θ, h, w', η, typ, U, ?_, ?_⟩
  · refine ⟨D.R.t_odd.pos, ?_, ?_, ?_, ?_, ?_⟩
    · rw [Br.PD_p]
      exact hS
    · exact hL5 _ (WpO D.nd i ρ π) θ hWcont hθc
    · exact (hL4 _ (WpO D.nd i ρ π) θ hL6.1 hθcr).1
    · intro a τ hO b
      have e := (hL4 _ (WpO D.nd i ρ π) θ hL6.1 hθcr).2 τ (w' a) (hθnz a τ hO) (b - w' a)
      rw [sub_add_cancel] at e
      rw [e, hWp a τ hO, sub_add_cancel]
    · intro c hc
      obtain ⟨hc1, hc2⟩ := Finset.mem_Icc.1 hc
      obtain ⟨k1, k2, k3⟩ := GlobalTheory.UseLoc.chiT_cont_isCrys_multV D i r ρ π w hw C θ c hc1 hc2 hG2 hθc hθcr
      refine ⟨GlobalTheory.UseLoc.chiT_cyc D i w hw C θ c hc1 hc2, k1, k2, ?_⟩
      intro a τ hO b
      have e := k3 τ (b - ((c : ℤ) - 1))
      rw [sub_add_cancel b ((c : ℤ) - 1)] at e
      rw [e, hθj' a τ hO]
      split_ifs <;> omega
  · intro x
    refine ⟨hL5 _ (rTwO D.nd i r x) θ (GlobalTheory.Pass.FamCont.stepCont D i r hGood x).1 hθc,
      (hL4 _ (rTwO D.nd i r x) θ (hL6.2 x) hθcr).1, ?_,
      GlobalTheory.UseLoc.InstPoly.charpoly_congr D i r ρ π w hw C θ lam hlam hG3 x⟩
    intro a τ hO b
    have e := (hL4 _ (rTwO D.nd i r x) θ (hL6.2 x) hθcr).2 τ (w' a) (hθnz a τ hO) (b - w' a)
    rw [sub_add_cancel] at e
    rw [e, hτu a τ hO, ((hX a) x (b - w' a)).2.1]
    have e2 := GlobalTheory.jTil_shift_block (D.nd.l i) _ D.R.t h w' η typ U hS a
      (AdmissibleParameterJ.JW D (decide (AdmissibleParameterJ.TypeU D ep (gA a))) (D.nd.j i) (ρA a)) (hU a) (b - w' a)
    rw [sub_add_cancel] at e2
    rw [← e2]
    exact if_congr (GlobalTheory.UseLoc.JumpBlock.jumps_iff D _ _ _ _) rfl rfl

end GlobalTheory.UseLocInst
