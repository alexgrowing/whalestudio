import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RootsOfUnityRingLeWittIntegers
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SubsetTwistExceptionalPlaces
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RingSpecNormalisedCharacterEq
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsSameData
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.HeightCounting GlobalTheory.TwInputs.Move GlobalTheory.HeightCounting.SideCopy
open Formalism.L2.DIV Formalism.L2.Theta
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace GlobalTheory.HeightCounting.ExpCopy

open GlobalTheory.Mem.R3.Tr

theorem sig_heq {R R' : Ranks} (hR : R = R') {H : Host R} {H' : Host R'} (hH : HEq H H') {T T' : Type} (hT : T = T')
    {f : T ≃ R.Psi} {f' : T' ≃ R'.Psi} (hf : HEq f f') {t : T} {t' : T'} (ht : HEq t t')
    {x : H.E} {x' : H'.E} (hx : HEq x x') :
    HEq (H.sigmaOf ((f t : R.Psi) : R.GG) x)
      (H'.sigmaOf ((f' t' : R'.Psi) : R'.GG) x') := by
  subst hR; cases hH; subst hT; cases hf; cases ht; cases hx; rfl

section
variable {D D' : D7} {ι : D.what₂.LL →+* D'.what₂.LL} {e : ↥D'.LL0 ≃+* ↥D.LL0}

theorem kEmb_heq (h : CopyTw D D' ι e) {i : D.ntw.Tw} {i' : D'.ntw.Tw} (hi : HEq i i') (b : Bool) {t : D.what₂.Tau}
    {t' : D'.what₂.Tau} (ht : HEq t t') {x : D.host.E} {x' : D'.host.E} (hx : HEq x x') :
    HEq (Formalism.L2.NX.kEmb D i b t x) (Formalism.L2.NX.kEmb D' i' b t' x') := by
  have hσ := sig_heq h.gal.R h.gal.host h.Tau h.eTau ht hx
  have hy : e (Formalism.L2.NX.embEL0 D' (D'.host.sigmaOf ((D'.eTau t' : D'.R.Psi) : D'.R.GG) x')) =
      Formalism.L2.NX.embEL0 D (D.host.sigmaOf ((D.eTau t : D.R.Psi) : D.R.GG) x) :=
    Subtype.ext (ι.injective ((h.LL0 _).trans (h.map_embE hσ).symm))
  have := h.sideEmb_heq hi b (Formalism.L2.NX.embEL0 D' (D'.host.sigmaOf ((D'.eTau t' : D'.R.Psi) : D'.R.GG) x'))
  rw [hy] at this
  exact this

theorem side_heq (h : CopyTw D D' ι e) {i : D.ntw.Tw} {i' : D'.ntw.Tw} (hi : HEq i i') (b : Bool) (z : ↥D.LL0) :
    HEq (GlobalTheory.SeriesTie.sideEmb D.ntw i b z) (GlobalTheory.SeriesTie.sideEmb D'.ntw i' b (e.symm z)) := by
  have := h.sideEmb_heq hi b (e.symm z)
  rw [e.apply_symm_apply] at this
  exact this

end

theorem infG_eta {D : D7} {cf : CharFrame D} (hcs : CharSide D cf) (t : D.what₂.Tau) :
    D.naut.infG D.naut.etaT (Formalism.L2.Host.embPsi D.host (D.eTau t)) = {(((1 / 2 : ℚ)) : ℂ)} :=
  (hcs.infG D.naut.etaT (fun _ => 1 / 2) (by rw [hcs.etaT]; exact ⟨fun _ => 1, fun _ => by norm_num, cf.isEta.inf⟩) (D.eTau t)).1

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in

theorem core (D : D7) (r : Rest D) (X : NExpTied D) (hpl : HEq D.naut.plGw (overD D r).naut.plGw)
    (hhw : ∀ i j b (t : D.what₂.Tau), 1 ≤ j → j ≤ D.R.m →
      ∃ lam : Fin D.R.nV → ℤ, Formalism.L2.NX.HWAtF (Formalism.L2.NX.cE D) (X.rhoW i j b).dual ((by exact NX.kEmb (overD D r) i b t)) lam)
    (hwt : ∀ i j b (t : D.what₂.Tau) (hj : 1 ≤ j) (hjm : j ≤ D.R.m) (sh : ℂ) (lam : Fin D.R.nV → ℤ),
      (overD D r).naut.infG (overD D r).naut.etaT ((by exact embPsi D.host (D.eTau t))) = {sh} →
      Formalism.L2.NX.HWAtF (Formalism.L2.NX.cE D) (X.rhoW i j b).dual ((by exact NX.kEmb (overD D r) i b t)) lam →
      NG.infOf lam = NG.paramV D.R (D.hc t) ⟨j - 1, by omega⟩ sh) :
    ∃ X' : NExpTied (overD D r), HEq X.tauG X'.tauG ∧ ∀ (i : D.ntw.Tw) (j : ℕ) (b : Bool) (k : ℕ) (Q : Finset (PlE D.host))
      (ψ : G D.host.E D.nd.Om →* (D.ntw.Ok i k)ˣ) (h1 : 1 ≤ j) (h2 : j ≤ D.R.m) (hA : NX.AdmTw D i k Q ψ),
      HEq (X.mtV i j b k Q ψ h1 h2 hA).QP (X'.mtV ((by exact i)) j b k ((by exact Q)) ((by exact ψ)) h1 ((by exact h2)) ((by exact hA))).QP ∧
      HEq (X.mtV i j b k Q ψ h1 h2 hA).DP (X'.mtV ((by exact i)) j b k ((by exact Q)) ((by exact ψ)) h1 ((by exact h2)) ((by exact hA))).DP ∧
      ∀ (ε : FractionRing (D.ntw.Ok i k) →+* ℂ) (V : Type) [AddCommGroup V] [Module ℂ V]
        (ρ : D.nexp.MtV i j b k Q ψ → Formalism.AUTREP.GAf D.host.E D.R.nV → V),
        GlobalTheory.HeightCounting.Reads X i j b k Q ψ h1 h2 hA ε V ρ →
          GlobalTheory.HeightCounting.Reads X' ((by exact i)) j b k ((by exact Q)) ((by exact ψ)) h1 ((by exact h2)) ((by exact hA)) ((by exact ε)) V ((by exact ρ)) := by
  cases r
  rename NAut _ => n
  cases n
  dsimp only [overD] at hpl
  cases hpl
  refine ⟨@Formalism.L2.NExpTied.mk (_)
      (U_eq := (X.U_eq))
      (psiU_gen := (X.psiU_gen))
      (psiU_side := (X.psiU_side))
      (psiU_xi := (X.psiU_xi))
      (delU_cont := (X.delU_cont))
      (delU_ine := (X.delU_ine))
      (thU_empty := (X.thU_empty))
      (sgnT := (X.sgnT))
      (sgnT_one := (X.sgnT_one))
      (Wt := (X.Wt))
      (acgWt := (X.acgWt))
      (modWt := (X.modWt))
      (fdWt := (X.fdWt))
      (rhoW := (X.rhoW))
      (rhoW_irr := (X.rhoW_irr))
      (rhoW_alg := (X.rhoW_alg))
      (tauG := (X.tauG))
      (sgnG := (X.sgnG))
      (sgnG_one := (X.sgnG_one))
      (tau_galois_first_character := (X.tau_galois_first_character))
      (mtV := fun x1 x2 x3 x4 x5 x6 x7 x8 x9 => @Formalism.L2.NX.MtVReal.mk (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_)
        (W := (@NX.MtVReal.W D x1 x2 x3 x4 x5 x6 (@NExpTied.sgnT D X) (@NExpTied.Wt D X x1 x2 x3) (@NExpTied.acgWt D X x1 x2 x3) (@NExpTied.modWt D X x1 x2 x3) (@NExpTied.rhoW D X x1 x2 x3) (@NExpTied.tauG D X x1 x2 x3) (@NExpTied.mtV D X x1 x2 x3 x4 x5 x6 x7 x8 x9)))
        (acg := (@NX.MtVReal.acg D x1 x2 x3 x4 x5 x6 (@NExpTied.sgnT D X) (@NExpTied.Wt D X x1 x2 x3) (@NExpTied.acgWt D X x1 x2 x3) (@NExpTied.modWt D X x1 x2 x3) (@NExpTied.rhoW D X x1 x2 x3) (@NExpTied.tauG D X x1 x2 x3) (@NExpTied.mtV D X x1 x2 x3 x4 x5 x6 x7 x8 x9)))
        (mod := (@NX.MtVReal.mod D x1 x2 x3 x4 x5 x6 (@NExpTied.sgnT D X) (@NExpTied.Wt D X x1 x2 x3) (@NExpTied.acgWt D X x1 x2 x3) (@NExpTied.modWt D X x1 x2 x3) (@NExpTied.rhoW D X x1 x2 x3) (@NExpTied.tauG D X x1 x2 x3) (@NExpTied.mtV D X x1 x2 x3 x4 x5 x6 x7 x8 x9)))
        (fd := (@NX.MtVReal.fd D x1 x2 x3 x4 x5 x6 (@NExpTied.sgnT D X) (@NExpTied.Wt D X x1 x2 x3) (@NExpTied.acgWt D X x1 x2 x3) (@NExpTied.modWt D X x1 x2 x3) (@NExpTied.rhoW D X x1 x2 x3) (@NExpTied.tauG D X x1 x2 x3) (@NExpTied.mtV D X x1 x2 x3 x4 x5 x6 x7 x8 x9)))
        (ρ := (@NX.MtVReal.ρ D x1 x2 x3 x4 x5 x6 (@NExpTied.sgnT D X) (@NExpTied.Wt D X x1 x2 x3) (@NExpTied.acgWt D X x1 x2 x3) (@NExpTied.modWt D X x1 x2 x3) (@NExpTied.rhoW D X x1 x2 x3) (@NExpTied.tauG D X x1 x2 x3) (@NExpTied.mtV D X x1 x2 x3 x4 x5 x6 x7 x8 x9)))
        (irr := (@NX.MtVReal.irr D x1 x2 x3 x4 x5 x6 (@NExpTied.sgnT D X) (@NExpTied.Wt D X x1 x2 x3) (@NExpTied.acgWt D X x1 x2 x3) (@NExpTied.modWt D X x1 x2 x3) (@NExpTied.rhoW D X x1 x2 x3) (@NExpTied.tauG D X x1 x2 x3) (@NExpTied.mtV D X x1 x2 x3 x4 x5 x6 x7 x8 x9)))
        (alg := (@NX.MtVReal.alg D x1 x2 x3 x4 x5 x6 (@NExpTied.sgnT D X) (@NExpTied.Wt D X x1 x2 x3) (@NExpTied.acgWt D X x1 x2 x3) (@NExpTied.modWt D X x1 x2 x3) (@NExpTied.rhoW D X x1 x2 x3) (@NExpTied.tauG D X x1 x2 x3) (@NExpTied.mtV D X x1 x2 x3 x4 x5 x6 x7 x8 x9)))
        (bc := (@NX.MtVReal.bc D x1 x2 x3 x4 x5 x6 (@NExpTied.sgnT D X) (@NExpTied.Wt D X x1 x2 x3) (@NExpTied.acgWt D X x1 x2 x3) (@NExpTied.modWt D X x1 x2 x3) (@NExpTied.rhoW D X x1 x2 x3) (@NExpTied.tauG D X x1 x2 x3) (@NExpTied.mtV D X x1 x2 x3 x4 x5 x6 x7 x8 x9)))
        (J := (@NX.MtVReal.J D x1 x2 x3 x4 x5 x6 (@NExpTied.sgnT D X) (@NExpTied.Wt D X x1 x2 x3) (@NExpTied.acgWt D X x1 x2 x3) (@NExpTied.modWt D X x1 x2 x3) (@NExpTied.rhoW D X x1 x2 x3) (@NExpTied.tauG D X x1 x2 x3) (@NExpTied.mtV D X x1 x2 x3 x4 x5 x6 x7 x8 x9)))
        (χ := (@NX.MtVReal.χ D x1 x2 x3 x4 x5 x6 (@NExpTied.sgnT D X) (@NExpTied.Wt D X x1 x2 x3) (@NExpTied.acgWt D X x1 x2 x3) (@NExpTied.modWt D X x1 x2 x3) (@NExpTied.rhoW D X x1 x2 x3) (@NExpTied.tauG D X x1 x2 x3) (@NExpTied.mtV D X x1 x2 x3 x4 x5 x6 x7 x8 x9)))
        (J_open := (@NX.MtVReal.J_open D x1 x2 x3 x4 x5 x6 (@NExpTied.sgnT D X) (@NExpTied.Wt D X x1 x2 x3) (@NExpTied.acgWt D X x1 x2 x3) (@NExpTied.modWt D X x1 x2 x3) (@NExpTied.rhoW D X x1 x2 x3) (@NExpTied.tauG D X x1 x2 x3) (@NExpTied.mtV D X x1 x2 x3 x4 x5 x6 x7 x8 x9)))
        (hyp := (@NX.MtVReal.hyp D x1 x2 x3 x4 x5 x6 (@NExpTied.sgnT D X) (@NExpTied.Wt D X x1 x2 x3) (@NExpTied.acgWt D X x1 x2 x3) (@NExpTied.modWt D X x1 x2 x3) (@NExpTied.rhoW D X x1 x2 x3) (@NExpTied.tauG D X x1 x2 x3) (@NExpTied.mtV D X x1 x2 x3 x4 x5 x6 x7 x8 x9)))
        (QP := (@NX.MtVReal.QP D x1 x2 x3 x4 x5 x6 (@NExpTied.sgnT D X) (@NExpTied.Wt D X x1 x2 x3) (@NExpTied.acgWt D X x1 x2 x3) (@NExpTied.modWt D X x1 x2 x3) (@NExpTied.rhoW D X x1 x2 x3) (@NExpTied.tauG D X x1 x2 x3) (@NExpTied.mtV D X x1 x2 x3 x4 x5 x6 x7 x8 x9)))
        (QP_sub := (@NX.MtVReal.QP_sub D x1 x2 x3 x4 x5 x6 (@NExpTied.sgnT D X) (@NExpTied.Wt D X x1 x2 x3) (@NExpTied.acgWt D X x1 x2 x3) (@NExpTied.modWt D X x1 x2 x3) (@NExpTied.rhoW D X x1 x2 x3) (@NExpTied.tauG D X x1 x2 x3) (@NExpTied.mtV D X x1 x2 x3 x4 x5 x6 x7 x8 x9)))
        (QP_cover := (@NX.MtVReal.QP_cover D x1 x2 x3 x4 x5 x6 (@NExpTied.sgnT D X) (@NExpTied.Wt D X x1 x2 x3) (@NExpTied.acgWt D X x1 x2 x3) (@NExpTied.modWt D X x1 x2 x3) (@NExpTied.rhoW D X x1 x2 x3) (@NExpTied.tauG D X x1 x2 x3) (@NExpTied.mtV D X x1 x2 x3 x4 x5 x6 x7 x8 x9)))
        (QP_nconj := (@NX.MtVReal.QP_nconj D x1 x2 x3 x4 x5 x6 (@NExpTied.sgnT D X) (@NExpTied.Wt D X x1 x2 x3) (@NExpTied.acgWt D X x1 x2 x3) (@NExpTied.modWt D X x1 x2 x3) (@NExpTied.rhoW D X x1 x2 x3) (@NExpTied.tauG D X x1 x2 x3) (@NExpTied.mtV D X x1 x2 x3 x4 x5 x6 x7 x8 x9)))
        (DP := (@NX.MtVReal.DP D x1 x2 x3 x4 x5 x6 (@NExpTied.sgnT D X) (@NExpTied.Wt D X x1 x2 x3) (@NExpTied.acgWt D X x1 x2 x3) (@NExpTied.modWt D X x1 x2 x3) (@NExpTied.rhoW D X x1 x2 x3) (@NExpTied.tauG D X x1 x2 x3) (@NExpTied.mtV D X x1 x2 x3 x4 x5 x6 x7 x8 x9)))
        (DP_sub := (@NX.MtVReal.DP_sub D x1 x2 x3 x4 x5 x6 (@NExpTied.sgnT D X) (@NExpTied.Wt D X x1 x2 x3) (@NExpTied.acgWt D X x1 x2 x3) (@NExpTied.modWt D X x1 x2 x3) (@NExpTied.rhoW D X x1 x2 x3) (@NExpTied.tauG D X x1 x2 x3) (@NExpTied.mtV D X x1 x2 x3 x4 x5 x6 x7 x8 x9)))
        (DP_cover := (@NX.MtVReal.DP_cover D x1 x2 x3 x4 x5 x6 (@NExpTied.sgnT D X) (@NExpTied.Wt D X x1 x2 x3) (@NExpTied.acgWt D X x1 x2 x3) (@NExpTied.modWt D X x1 x2 x3) (@NExpTied.rhoW D X x1 x2 x3) (@NExpTied.tauG D X x1 x2 x3) (@NExpTied.mtV D X x1 x2 x3 x4 x5 x6 x7 x8 x9)))
        (DP_nconj := (@NX.MtVReal.DP_nconj D x1 x2 x3 x4 x5 x6 (@NExpTied.sgnT D X) (@NExpTied.Wt D X x1 x2 x3) (@NExpTied.acgWt D X x1 x2 x3) (@NExpTied.modWt D X x1 x2 x3) (@NExpTied.rhoW D X x1 x2 x3) (@NExpTied.tauG D X x1 x2 x3) (@NExpTied.mtV D X x1 x2 x3 x4 x5 x6 x7 x8 x9)))
        (sp := (@NX.MtVReal.sp D x1 x2 x3 x4 x5 x6 (@NExpTied.sgnT D X) (@NExpTied.Wt D X x1 x2 x3) (@NExpTied.acgWt D X x1 x2 x3) (@NExpTied.modWt D X x1 x2 x3) (@NExpTied.rhoW D X x1 x2 x3) (@NExpTied.tauG D X x1 x2 x3) (@NExpTied.mtV D X x1 x2 x3 x4 x5 x6 x7 x8 x9)))
        (sp_w := (@NX.MtVReal.sp_w D x1 x2 x3 x4 x5 x6 (@NExpTied.sgnT D X) (@NExpTied.Wt D X x1 x2 x3) (@NExpTied.acgWt D X x1 x2 x3) (@NExpTied.modWt D X x1 x2 x3) (@NExpTied.rhoW D X x1 x2 x3) (@NExpTied.tauG D X x1 x2 x3) (@NExpTied.mtV D X x1 x2 x3 x4 x5 x6 x7 x8 x9)))
        (redG := (@NX.MtVReal.redG D x1 x2 x3 x4 x5 x6 (@NExpTied.sgnT D X) (@NExpTied.Wt D X x1 x2 x3) (@NExpTied.acgWt D X x1 x2 x3) (@NExpTied.modWt D X x1 x2 x3) (@NExpTied.rhoW D X x1 x2 x3) (@NExpTied.tauG D X x1 x2 x3) (@NExpTied.mtV D X x1 x2 x3 x4 x5 x6 x7 x8 x9)))
        (J_mem := (@NX.MtVReal.J_mem D x1 x2 x3 x4 x5 x6 (@NExpTied.sgnT D X) (@NExpTied.Wt D X x1 x2 x3) (@NExpTied.acgWt D X x1 x2 x3) (@NExpTied.modWt D X x1 x2 x3) (@NExpTied.rhoW D X x1 x2 x3) (@NExpTied.tauG D X x1 x2 x3) (@NExpTied.mtV D X x1 x2 x3 x4 x5 x6 x7 x8 x9)))
        (chi_eq := (@NX.MtVReal.chi_eq D x1 x2 x3 x4 x5 x6 (@NExpTied.sgnT D X) (@NExpTied.Wt D X x1 x2 x3) (@NExpTied.acgWt D X x1 x2 x3) (@NExpTied.modWt D X x1 x2 x3) (@NExpTied.rhoW D X x1 x2 x3) (@NExpTied.tauG D X x1 x2 x3) (@NExpTied.mtV D X x1 x2 x3 x4 x5 x6 x7 x8 x9)))
        (real := (@NX.MtVReal.real D x1 x2 x3 x4 x5 x6 (@NExpTied.sgnT D X) (@NExpTied.Wt D X x1 x2 x3) (@NExpTied.acgWt D X x1 x2 x3) (@NExpTied.modWt D X x1 x2 x3) (@NExpTied.rhoW D X x1 x2 x3) (@NExpTied.tauG D X x1 x2 x3) (@NExpTied.mtV D X x1 x2 x3 x4 x5 x6 x7 x8 x9))))
      (rhoW_hw := (hhw))
      (rhoW_wt := (hwt)), (HEq.refl X.tauG), fun i j b k Q ψ h1 h2 hA => ⟨?_, ?_, fun ε V _ _ ρ hR => ?_⟩⟩
  · exact (HEq.refl (X.mtV i j b k Q ψ h1 h2 hA).QP)
  · exact (HEq.refl (X.mtV i j b k Q ψ h1 h2 hA).DP)
  · exact (hR)

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in

theorem expTied_copy : ∀ {D D' : D7} {ι : D.what₂.LL →+* D'.what₂.LL} {e : ↥D'.LL0 ≃+* ↥D.LL0}, CopyAll D D' ι e → ∀ {cf : CharFrame D} {cf' : CharFrame D'}, SameFrame cf cf' → CharSide D cf → CharSide D' cf' → ∀ X : NExpTied D, ∃ X' : NExpTied D', (TauTrue X → TauTrue X') ∧ ∀ (i : D.ntw.Tw) (i' : D'.ntw.Tw), HEq i i' → ∀ (j : ℕ) (b : Bool) (k : ℕ) (Q : Finset (PlE D.host)) (Q' : Finset (PlE D'.host)), HEq Q Q' → ∀ (ψ : G D.host.E D.nd.Om →* (D.ntw.Ok i k)ˣ) (ψ' : G D'.host.E D'.nd.Om →* (D'.ntw.Ok i' k)ˣ), HEq ψ ψ' → ∀ (h1 : 1 ≤ j) (h2 : j ≤ D.R.m) (h2' : j ≤ D'.R.m) (hA' : NX.AdmTw D' i' k Q' ψ'), ∃ hA : NX.AdmTw D i k Q ψ, HEq (X.mtV i j b k Q ψ h1 h2 hA).QP (X'.mtV i' j b k Q' ψ' h1 h2' hA').QP ∧ HEq (X.mtV i j b k Q ψ h1 h2 hA).DP (X'.mtV i' j b k Q' ψ' h1 h2' hA').DP ∧ ∀ (ε : FractionRing (D.ntw.Ok i k) →+* ℂ) (ε' : FractionRing (D'.ntw.Ok i' k) →+* ℂ), HEq ε ε' → ∀ (V V' : Type) [aV : AddCommGroup V] [mV : Module ℂ V] [aV' : AddCommGroup V'] [mV' : Module ℂ V'], V = V' → HEq aV aV' → HEq mV mV' → ∀ (r : D.nexp.MtV i j b k Q ψ → Formalism.AUTREP.GAf D.host.E D.R.nV → V) (r' : D'.nexp.MtV i' j b k Q' ψ' → Formalism.AUTREP.GAf D'.host.E D'.R.nV → V'), HEq r r' → GlobalTheory.HeightCounting.Reads X i j b k Q ψ h1 h2 hA ε V r → GlobalTheory.HeightCounting.Reads X' i' j b k Q' ψ' h1 h2' hA' ε' V' r' := by
  intro D D' ι e h cf cf' _ hcs hcs' X
  obtain ⟨r, rfl⟩ := h.cp.exists_rest
  have hk : ∀ i b t, Formalism.L2.NX.kEmb D i b t = (by with_unfolding_all exact ((Formalism.L2.NX.kEmb (overD D r) ((by with_unfolding_all exact (i :))) b ((by with_unfolding_all exact (t :)))) :)) := fun i b t =>
    RingHom.ext fun x => (by with_unfolding_all exact (eq_of_heq (α := FractionRing (D.ntw.O i)) (a := Formalism.L2.NX.kEmb D i b t x)
        (a' := (by with_unfolding_all exact ((Formalism.L2.NX.kEmb (overD D r) ((i)) b ((t)) ((x))) : _)))
        ((by with_unfolding_all exact ((kEmb_heq h.cp (i := i) (i' := (i)) (((HEq.refl i))) b (t := t) (t' := (t)) (((HEq.refl t)))
          (x := x) (x' := (x)) (((HEq.refl x)))) : _))) :))
  obtain ⟨X', hτ, hM⟩ := core D r X h.pl
    (fun i j b t h1 h2 => by
      have := X.rhoW_hw i j b t h1 h2
      rw [hk] at this
      exact this)
    (fun i j b t h1 h2 sh lam hsh hw => by
      refine X.rhoW_wt i j b t h1 h2 sh lam ?_ ?_
      · have h3 : ({(((1 / 2 : ℚ)) : ℂ)} : Multiset ℂ) = {sh} := (infG_eta hcs' ((by with_unfolding_all exact (t :)))).symm.trans (c := {sh}) ((by with_unfolding_all exact (hsh :)))
        exact (infG_eta hcs t).trans h3
      · rw [hk]
        exact hw)
  refine ⟨X', fun ⟨τ, hτ'⟩ => ?_, fun i i' hi j b k Q Q' hQ ψ ψ' hψ h1 h2 h2' hA' => ?_⟩
  · have hτ2 : X'.tauG = (by with_unfolding_all exact (X.tauG :)) := (by with_unfolding_all exact ((eq_of_heq (a := X'.tauG) (a' := (by with_unfolding_all exact (X.tauG :))) ((by with_unfolding_all exact (hτ.symm :)))) :))
    refine ⟨fun j kv => (Units.map e.symm.toRingHom.toMonoidHom).comp ((by with_unfolding_all exact ((τ j ((by with_unfolding_all exact (kv :)))) :))), fun i j b kv x h1 h2 => ?_⟩
    rw [hτ2]
    exact (by with_unfolding_all exact ((hτ' ((by with_unfolding_all exact (i :))) j b ((by with_unfolding_all exact (kv :))) ((by with_unfolding_all exact (x :))) h1 ((by with_unfolding_all exact (h2 :)))).trans (eq_of_heq (α := FractionRing (D.ntw.O ((by with_unfolding_all exact (i :)))))
      (a' := (by with_unfolding_all exact ((GlobalTheory.SeriesTie.sideEmb (overD D r).ntw i b (e.symm ((τ j ((kv)) ((x)) : (↥D.LL0)ˣ) : ↥D.LL0))) : _)))
      ((by with_unfolding_all exact ((side_heq h.cp (i := (i)) (i' := i) (((HEq.refl i))) b ((τ j ((kv)) ((x)) : (↥D.LL0)ˣ) : ↥D.LL0)) : _)))) :))
  · cases hi; cases hQ; cases hψ
    refine ⟨(by with_unfolding_all exact (hA' :)), (hM i j b k Q ψ h1 h2 ((by with_unfolding_all exact (hA' :)))).1, (hM i j b k Q ψ h1 h2 ((by with_unfolding_all exact (hA' :)))).2.1, ?_⟩
    intro ε ε' hε V V' aV mV aV' mV' hV haV hmV ρ ρ' hρ hR
    subst hV; cases haV; cases hmV; cases hε; cases hρ
    exact (by with_unfolding_all exact (((hM i j b k Q ψ h1 h2 ((by with_unfolding_all exact (hA' :)))).2.2 ε V ρ hR) :))

end GlobalTheory.HeightCounting.ExpCopy

end
