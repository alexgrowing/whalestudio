import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsSimilitudeTriangularPeriodsOfHeckePoint
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HeckeIsogenyLiftsToLatticeMapScalingForms
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HermFormEqOfImEqOnSpanningLatticeStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.EqOfFlagOfHermFormPreservingStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NonemptyTransferEquiv
import Development.AbelianVarietyTheory.BlockTheory.ExistenceTori.HalfDepthValuations
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.HkSupSizedOfHkSup
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.SplitLinearModelNorm
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.UnramifiedCharacter
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.HeckePrimeDetection
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT Formalism.L2.Pj
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section
open NumberField

set_option autoImplicit false

namespace GlobalTheory.HeckeInj

open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
  ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.HeckeEx MonoidalCategory CartesianMonoidalCategory MonObj

theorem smul_sum_sub_mem_span {V : Type} [AddCommGroup V] [Module ℂ V] {n : ℕ} (cf : Fin n → ℂ) (bv : Fin n → V)
    (s : ℂ) (i : Fin n) (h1 : cf i = 1) (h0 : ∀ j, i < j → cf j = 0) :
    s • ∑ j, cf j • bv j - s • bv i ∈ Submodule.span ℂ (bv '' {j | j < i}) := by
  classical
  have e1 : s • ∑ j, cf j • bv j - s • bv i = ∑ j, (s * (cf j - if j = i then 1 else 0)) • bv j := by
    simp only [mul_sub, sub_smul, Finset.sum_sub_distrib, Finset.smul_sum, smul_smul]
    congr 1
    simp
  rw [e1]
  refine Submodule.sum_mem _ fun j _ => ?_
  rcases lt_trichotomy j i with hj | rfl | hj
  · exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, hj, rfl⟩)
  · simp [h1]
  · simp [h0 j hj, hj.ne']

theorem exists_lift_pair {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
    {Dw : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Datum H} {l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H}
    {Xo : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Moduli Dw l} {σ' : ReciprocityTheory.ChartRestriction.G.Geo.Tor.KA l →+* ℂ} {g : ℕ}
    {ty : Fin g → (E →+* ℂ)} (F : ReciprocityTheory.ChartRestriction.G.Geo.Tor.FamilyUnif Xo σ' ty)
    (i j : Fin F.n) (P : (F.Di i).La →+ (Fin g → ℂ)) (P' : (F.Di j).La →+ (Fin g → ℂ))
    (hP : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsPeriod (F.Di i) ty P) (hP' : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsPeriod (F.Di j) ty P')
    {p : ℕ} (hp : p.Prime)
    {y y₁ y₂ : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp ℂ ⟶ Xo.X} (hy : y = F.u i P) (hy₁ : y₁ = F.u j P') (hy₂ : y₂ = F.u j P')
    (C C' : Subgroup (Over.mk y ⟶ Xo.univ.t.G))
    (ψ : pullback Xo.univ.t.G.hom y ⟶ pullback Xo.univ.t.G.hom y₁)
    (ψp : (Over.mk y ⟶ Xo.univ.t.G) →* (Over.mk y₁ ⟶ Xo.univ.t.G))
    (ψ' : pullback Xo.univ.t.G.hom y ⟶ pullback Xo.univ.t.G.hom y₂)
    (ψp' : (Over.mk y ⟶ Xo.univ.t.G) →* (Over.mk y₂ ⟶ Xo.univ.t.G))
    (hC : ∀ a ∈ C, a ^ p ^ 2 = 1) (hC' : ∀ a ∈ C', a ^ p ^ 2 = 1)
    (hI : Formalism.L2.Pj.IsHkIsog p y y₁ C ψ ψp) (hI' : Formalism.L2.Pj.IsHkIsog p y y₂ C' ψ' ψp') :
    ∃ (gam gam' : (F.Di i).La →ₗ[𝓞 E] (F.Di j).La) (h h' : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g → ℂ)),
      (∀ a b, (F.Di j).EF (gam a) (gam b) = (p : ℤ) ^ 2 * (F.Di i).EF a b) ∧ (∀ a, P' (gam a) = h (P a)) ∧
      (∀ a b, (F.Di j).EF (gam' a) (gam' b) = (p : ℤ) ^ 2 * (F.Di i).EF a b) ∧ (∀ a, P' (gam' a) = h' (P a)) ∧
      (∀ (w : Fin g → ℂ) (v : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp (DualNumber ℂ) ⟶ pullback Xo.univ.t.G.hom y),
        v ≫ pullback.snd _ _ = ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (algebraMap ℂ (DualNumber ℂ)) →
        ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsDerivAt0 (fun z => (F.ex i P z).left) w (v ≫ pullback.fst _ _) →
        ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsDerivAt0 (fun z => (F.ex j P' z).left) (h w) (v ≫ ψ ≫ pullback.fst _ _) ∧
        ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsDerivAt0 (fun z => (F.ex j P' z).left) (h' w) (v ≫ ψ' ≫ pullback.fst _ _)) ∧
      (h = h' → C = C') := by
  subst hy hy₁ hy₂
  obtain ⟨gam, h, h1, h2, -, h4⟩ :=
    GlobalTheory.HeckeLift.exists_linearMap_of_isHkIsog _ H Dw l Xo σ' g ty F i j P P' p C ψ ψp hP hP' hp hC hI
  obtain ⟨gam', h', h1', h2', -, h4'⟩ :=
    GlobalTheory.HeckeLift.exists_linearMap_of_isHkIsog _ H Dw l Xo σ' g ty F i j P P' p C' ψ' ψp' hP hP' hp hC' hI'
  refine ⟨gam, gam', h, h', h1, h2, h1', h2', fun w v hvs hd => ?_, fun hh => ?_⟩
  · have hfst : ∀ z, fibPt Xo.univ.t.G (F.ex i P z) ≫ pullback.fst _ _ = (F.ex i P z).left := fun z =>
      pullback.lift_fst _ _ _
    have d0 : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsDerivAt0 (fun z => fibPt Xo.univ.t.G (F.ex i P z)) w v := by
      refine FibreDeriv.isDerivAt0_of_isPullback (IsPullback.of_hasPullback Xo.univ.t.G.hom (F.u i P))
        (fun z => pullback.lift_snd _ _ _) ?_ hvs ?_
      · convert ExpChain.isHolTo_ex F i P hP using 2 with z
        exact hfst z
      · convert hd using 2 with z
        exact hfst z
    refine ⟨?_, ?_⟩
    · have d1 := FibreDeriv.isDerivAt0_comp d0 (ψ ≫ pullback.fst _ _)
      have e1 : ∀ z, fibPt Xo.univ.t.G (F.ex i P z) ≫ ψ ≫ pullback.fst _ _ = (F.ex j P' (h z)).left :=
        fun z => by
          rw [← Category.assoc, hI.2.2.1, h4]
          exact pullback.lift_fst _ _ _
      simp only [e1] at d1
      exact (ExpChain.isDerivAt0_comp_linear _ (ExpChain.isHolTo_ex F j P' hP') h.toLinearMap w _).1 d1
    · have d1 := FibreDeriv.isDerivAt0_comp d0 (ψ' ≫ pullback.fst _ _)
      have e1 : ∀ z, fibPt Xo.univ.t.G (F.ex i P z) ≫ ψ' ≫ pullback.fst _ _ = (F.ex j P' (h' z)).left :=
        fun z => by
          rw [← Category.assoc, hI'.2.2.1, h4']
          exact pullback.lift_fst _ _ _
      simp only [e1] at d1
      exact (ExpChain.isDerivAt0_comp_linear _ (ExpChain.isHolTo_ex F j P' hP') h'.toLinearMap w _).1 d1
  · rw [← hI.2.2.2.2.2.1, ← hI'.2.2.2.2.2.1]
    congr 1
    refine MonoidHom.ext fun x => ?_
    obtain ⟨z, rfl⟩ := F.ex_onto i P hP x
    rw [← h4, ← h4', hh]

end GlobalTheory.HeckeInj

namespace GlobalTheory.HeckeInj

open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
  ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.HeckeEx MonoidalCategory CartesianMonoidalCategory MonObj

set_option maxHeartbeats 1000000 in

theorem eq_of_hkRelFr_frBor : ∀ {E : Type} [Field E] [NumberField E] [NumberField.IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
    {Dw : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Datum H} {l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H} (Xo : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Moduli Dw l)
    (c : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Coeff l) (σ : c.F →+* ℂ) (r : ℕ) (U : Unf Xo c σ r), IsUnf U →
    ∀ (P : Ideal (𝓞 E)) (p i : ℕ), GlobalTheory.IndefiniteRowSideFullHecke.HeckePrimeDetection.IsHeckePrime l P p → ∀ (k : U.Comp) (x : (U.X k).dom),
      letI : Field (CAt σ) := inferInstanceAs (Field ℂ)
      haveI : IsAlgClosed (CAt σ) := inferInstanceAs (IsAlgClosed ℂ)
      ∀ (C C' : hkKer (Xo := Xo) P p i (CAt σ) (U.un k x)) (z z' w : FrPt Xo c (CAt σ)) (t t' : Ix Dw → (CAt σ)ˣ),
        hkRelFr P p i (GlobalTheory.ThetaTrace.hkTr Xo c p) (CAt σ) (U.un k x) C z →
        hkRelFr P p i (GlobalTheory.ThetaTrace.hkTr Xo c p) (CAt σ) (U.un k x) C' z' →
        (∀ j, j ≠ none → t j = 1) → (∀ j, j ≠ none → t' j = 1) → FrBor t w z → FrBor t' w z' → C = C' := by
  classical
  intro E _ _ _ H Dw l Xo c σ r U hU P p i hHP k x C C' z z' w t t' hz hz' ht ht' hB hB'
  obtain ⟨-, -, hall, -, -, g, e, F, ik, φ, -, hpt⟩ := hU
  obtain ⟨Pm, -, per, hPx, hv, -⟩ := hpt k x
  obtain ⟨k'', x'', t'', hB''⟩ := hall w
  obtain ⟨Pm'', -, per'', hPx'', hv'', -⟩ := hpt k'' x''
  obtain ⟨ψ, ψp, hI, hL, -⟩ := hz
  obtain ⟨ψ', ψp', hI', hL', -⟩ := hz'
  have hpp : p.Prime := hHP.2.2.2.1
  have hwx : w.x = F.u (ik k'') Pm'' := hB''.1.trans hPx''
  obtain ⟨gam, gam', h, h', hiso, hh, hiso', hh', hder, hker⟩ :=
    exists_lift_pair F (ik k) (ik k'') Pm Pm'' per per'' hpp hPx (hB.1.trans hwx) (hB'.1.trans hwx) C.1 C'.1
      ψ ψp ψ' ψp' (fun a ha => GlobalTheory.HkPts.pow_eq_one hHP.2.2.2.2 C.2 ha)
      (fun a ha => GlobalTheory.HkPts.pow_eq_one hHP.2.2.2.2 C'.2 ha) hI hI'
  choose c'' hc''1 hc''2 hc''3 using hB''.2.1
  let bv : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → (Fin g → ℂ) := fun τ j =>
    ∑ i, Formalism.L2.Pj.toC (c'' τ j i) • (Pi.single (e.symm ⟨τ, i⟩) 1 : Fin g → ℂ)
  have hdw : ∀ τ j, IsDerivAt0 (fun z => (F.ex (ik k'') Pm'' z).left) (bv τ j) (w.u τ j) := fun τ j =>
    (DerLin.isCombAt_iff_isDerivAt0 E H Dw l Xo _ g _ F _ Pm'' per'' _ ((U.un k'' x'').u τ) _ (hv'' τ) (c'' τ j)
      (w.u τ j)).1 (hPx'' ▸ hc''3 τ j)
  have tn := isDerivAt0_ex_isTanAt E H Dw l Xo _ g _ F _ Pm'' per''
  have hp0 : (p : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hpp.ne_zero
  have e1 : spMap (epsMul (1 : ℂ)) = 𝟙 _ := by
    have e0 : epsMul (1 : ℂ) = RingHom.id _ := by
      apply RingHom.ext
      intro a
      ext <;> simp [epsMul]
    rw [e0]
    first | rfl | exact Spec.map_id _ | simp [spMap] | (rw [CommRingCat.ofHom_id]; exact Spec.map_id _)
  letI : Field (Formalism.L2.Pj.CAt σ) := inferInstanceAs (Field ℂ)
  have col : ∀ (zz : Formalism.L2.Pj.FrPt Xo c (Formalism.L2.Pj.CAt σ)) (tt : Formalism.L2.Pj.Ix Dw → (Formalism.L2.Pj.CAt σ)ˣ)
      (ψ0 : pullback Xo.univ.t.G.hom (U.un k x).x ⟶ pullback Xo.univ.t.G.hom zz.x)
      (h0 : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g → ℂ)),
      (∀ τ j, Formalism.L2.Pj.IsLieImageH p ψ0 ((U.un k x).u τ j) (zz.u τ j)) →
      (∀ (w : Fin g → ℂ) (v : Sp (DualNumber ℂ) ⟶ pullback Xo.univ.t.G.hom (U.un k x).x),
        v ≫ pullback.snd _ _ = spMap (algebraMap ℂ (DualNumber ℂ)) →
        IsDerivAt0 (fun z => (F.ex (ik k) Pm z).left) w (v ≫ pullback.fst _ _) →
        IsDerivAt0 (fun z => (F.ex (ik k'') Pm'' z).left) (h0 w) (v ≫ ψ0 ≫ pullback.fst _ _)) →
      (∀ j, j ≠ none → tt j = 1) → Formalism.L2.Pj.FrBor tt w zz →
      ∀ τ m, h0 (Pi.single (e.symm ⟨τ, m⟩) 1) - (p : ℂ) • bv τ m ∈
        Submodule.span ℂ (bv τ '' {j | j < m}) := by
    intro zz tt ψ0 h0 hL0 hder0 ht0 hB0 τ m
    choose cf hcf1 hcf2 hcf3 using hB0.2.1
    obtain ⟨wv, hw1, hw2, hw3⟩ := hL0 τ m
    have d2 := hder0 (Pi.single (e.symm ⟨τ, m⟩) 1) wv hw2 (by have q := hv τ m; rw [← hw1] at q; exact q)
    have d1 := (DerLin.isCombAt_iff_isDerivAt0 E H Dw l Xo _ g _ F _ Pm'' per'' _ (w.u τ) _ (hdw τ) (cf τ m)
      (zz.u τ m)).1 (hwx ▸ hcf3 τ m)
    have d3 := ReciprocityTheory.ChartRestriction.G.PullbackSections.ExpRows.isDerivAt0_smul d1 (p : ℂ)
    have e3 : spMap (epsMul (p : ℂ)) ≫ zz.u τ m = wv ≫ ψ0 ≫ pullback.fst _ _ := by
      rw [hw3]
      refine (spMap_epsMul_comp (p : ℂ) ((p : ℂ)⁻¹) _).trans ?_
      rw [inv_mul_cancel₀ hp0, e1]
      exact Category.id_comp _
    rw [e3] at d3
    rw [(tn.2.2 _ (tn.1 _ _ d2)).unique d2 d3]
    refine smul_sum_sub_mem_span (fun j => Formalism.L2.Pj.toC (cf τ m j)) (bv τ) _ m ?_ fun j hj => ?_
    · show Formalism.L2.Pj.toC (cf τ m m) = 1
      rw [hcf1 τ m, ht0 _ (by simp)]
      rfl
    · show Formalism.L2.Pj.toC (cf τ m j) = 0
      rw [hcf2 τ m j hj]
      rfl
  obtain ⟨Hm, -, hpos, hHm⟩ := per''.2.2.2.2
  have hform : ∀ x y, hermForm Hm (h x) (h y) = hermForm Hm (h' x) (h' y) :=
    GlobalTheory.T.hermForm_eq_of_im_eq_on_spanning_family Pm per.2.2.2.1 Hm h.toLinearMap h'.toLinearMap fun a b => by
      simp only [LinearEquiv.coe_coe]
      rw [← hh, ← hh, ← hh', ← hh', hHm, hHm, hiso, hiso']
  have hhh := GlobalTheory.T.eq_of_flag_of_hermForm_preserving e Hm hpos h h' hform bv (p : ℂ) hp0
    (col z t ψ h hL (fun w v a b => (hder w v a b).1) ht hB)
    (col z' t' ψ' h' hL' (fun w v a b => (hder w v a b).2) ht' hB')
  exact Subtype.ext (hker hhh)

end GlobalTheory.HeckeInj
