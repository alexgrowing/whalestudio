import Mathlib
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.HkSupSizedOfHkSup
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.SplitLinearModelNorm
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.UnramifiedCharacter
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.HeckePrimeDetection
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HeckePointLaws
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HeckeReadingKernelsMatchCosetsThroughFrameStatement

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT Formalism.L2.Pj
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

set_option autoImplicit false

namespace GlobalTheory.HeckeReadProof

open GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues

theorem phiW_eq {D : D7} (T : CoreJ D) (i : Fin D.R.m) (σ : T.Q.c.F →+* ℂ) (hV : T.V ((i : ℕ) + 1) σ = Wc D i)
    (a : (D.host.E →+* ℂ) × ℕ → ℕ) (f : T.R ((i : ℕ) + 1)) (h : GA D (Wc D i))
    (hx : (dictW T i σ hV h).2 ∈ ((T.U ((i : ℕ) + 1) σ).X (dictW T i σ hV h).1).dom) :
    phiW T i σ hV a f h = (lieFac (T.Q.Dw ((i : ℕ) + 1)) (xiR D) a : ℂ) *
      (T.cE ((i : ℕ) + 1) σ (dictW T i σ hV h).1 * castDict hV (T.mu ((i : ℕ) + 1) σ) h) *
      toC (evR (T.Q.Xo ((i : ℕ) + 1)) T.Q.c f ((T.U ((i : ℕ) + 1) σ).un (dictW T i σ hV h).1 ⟨(dictW T i σ hV h).2, hx⟩)) := by
  show T.phiJ _ σ a f _ = _
  rw [CoreJ.phiJ_apply]
  simp only [Core.phiAd, Pi.smul_apply, smul_eq_mul, adel, rdU, LinearMap.coe_mk, AddHom.coe_mk]
  simp only [dictW, castDict] at hx ⊢
  split_ifs with h1
  · ring
  · exact absurd hx h1

theorem heckeReadTie (hSL : ∀ D, GlobalTheory.IndefiniteRowSideFullHecke.SplitLinearModelNorm.SplitLinearModel D) (hVF : ∀ D, GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter.VacFixed D) :
    GlobalTheory.HeckeSupSt.HeckeReadTie := by
  intro D G _ _ Pl0 T0 A T _ R F κ v₀ hlev hgrp hfam hmod hthP ht i σ hσ hV hpin
  intro P p k α Rc hs cq f g hf hg hr h
  letI : Field (CAt σ) := inferInstanceAs (Field ℂ)
  haveI : IsAlgClosed (CAt σ) := inferInstanceAs (IsAlgClosed ℂ)
  have hgood : GoodEmb T.Q.c σ := hσ ▸ T.toCore.good_σ₀
  obtain ⟨hx, -, -⟩ := exists_witness T i σ hV ht.laws.toLawsM hgood h
  obtain ⟨e, he⟩ := GlobalTheory.T.heckeReading_kernels_match_cosets_through_frame D GlobalTheory.HeckePointLaw.heckePointLaws (hSL D) (hVF D) G Pl0 T0 A T R F κ v₀ hlev hgrp hfam
    hmod hthP ht i σ hσ hV hpin P p k α Rc hs h hx
  have hfin : Finite (hkKer (Xo := T.Q.Xo ((i : ℕ) + 1)) P.asIdeal p k (CAt σ)
      ((T.U ((i : ℕ) + 1) σ).un (dictW T i σ hV h).1 ⟨(dictW T i σ hV h).2, hx⟩)) := Finite.of_equiv _ e.symm
  rw [phiW_eq T i σ hV _ g h hx]
  have hr' := hr (CAt σ) ((T.U ((i : ℕ) + 1) σ).un (dictW T i σ hV h).1 ⟨(dictW T i σ hV h).2, hx⟩)
  have e1 : toC (evR (T.Q.Xo ((i : ℕ) + 1)) T.Q.c g
      ((T.U ((i : ℕ) + 1) σ).un (dictW T i σ hV h).1 ⟨(dictW T i σ hV h).2, hx⟩)) =
      σ cq * σ (hkScal T.Q.c 1 P.asIdeal k D.R.nV) * ∑ᶠ C,
        toC (evR (T.Q.Xo ((i : ℕ) + 1)) T.Q.c f (he C).1.choose) := by
    refine (congrArg toC hr').trans ?_
    have hs1 : σ (hkScal T.Q.c cq P.asIdeal k D.R.nV) = σ cq * σ (hkScal T.Q.c 1 P.asIdeal k D.R.nV) := by
      simp only [hkScal, one_mul, map_mul]
    show σ (hkScal T.Q.c cq P.asIdeal k D.R.nV) * toC (hkVal _ _ _ _ f _) = _
    rw [hs1]
    congr 1
    unfold hkVal
    show (∑ᶠ C, toC (hkTerm _ _ _ _ f _ C)) = _
    refine finsum_congr fun C => ?_
    unfold hkTerm
    split_ifs with h1
    · rfl
    · exact absurd (he C).1 h1
  rw [e1]
  have e2 : ∀ C, (lieFac (T.Q.Dw ((i : ℕ) + 1)) (xiR D) (wtA (κ i)) : ℂ) *
      (T.cE ((i : ℕ) + 1) σ (dictW T i σ hV h).1 * castDict hV (T.mu ((i : ℕ) + 1) σ) h) *
      σ (hkScal T.Q.c 1 P.asIdeal k D.R.nV) * toC (evR (T.Q.Xo ((i : ℕ) + 1)) T.Q.c f (he C).1.choose) =
      (muAt T R i P)⁻¹ ^ k * phiW T i σ hV (wtA (κ i)) f (h * (e C : GA D (Wc D i))) :=
    fun C => (he C).2 _ (he C).1.choose_spec f hf
  have e3 : ∑ᶠ C, (muAt T R i P)⁻¹ ^ k * phiW T i σ hV (wtA (κ i)) f (h * (e C : GA D (Wc D i))) =
      (muAt T R i P)⁻¹ ^ k * ∑ a ∈ Rc, phiW T i σ hV (wtA (κ i)) f (h * a) := by
    rw [finsum_comp_equiv e (f := fun a : Rc =>
      (muAt T R i P)⁻¹ ^ k * phiW T i σ hV (wtA (κ i)) f (h * (a : GA D (Wc D i))))]
    rw [finsum_eq_sum_of_fintype, Finset.sum_coe_sort Rc
      (fun a => (muAt T R i P)⁻¹ ^ k * phiW T i σ hV (wtA (κ i)) f (h * a)), Finset.mul_sum]
  rw [mul_assoc (σ cq) ((muAt T R i P)⁻¹ ^ k), ← e3, ← finsum_congr e2, ← mul_finsum]
  ring

end GlobalTheory.HeckeReadProof
