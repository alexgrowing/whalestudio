import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HeckePointEqUnipotentFrameChangeCosetRepStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsSimilitudeTriangularPeriodsOfHeckePoint
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FramedPointBaseChangeUniqueReflIff
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

namespace GlobalTheory.HeckeExist

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD

attribute [local instance] GlobalTheory.HeckeEx.fieldCAt GlobalTheory.HeckeEx.algClosedCAt

theorem spMap_epsMul_one {Y : Scheme.{0}} (v : Sp (DualNumber ℂ) ⟶ Y) : spMap (epsMul (1 : ℂ)) ≫ v = v := by
  have e0 : epsMul (1 : ℂ) = RingHom.id _ := by
    apply RingHom.ext
    intro a
    ext <;> simp [epsMul]
  rw [e0]
  have : spMap (RingHom.id (DualNumber ℂ)) = 𝟙 _ := by
    first | rfl | exact Spec.map_id _ | simp [spMap] | (rw [CommRingCat.ofHom_id]; exact Spec.map_id _)
  rw [this, Category.id_comp]

set_option maxHeartbeats 1000000 in

theorem similitude_tri_of_hkIsog {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H}
    {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {σ : c.F →+* ℂ} {r : ℕ} (U : Unf Xo c σ r) (hU : IsUnf U)
    (P : Ideal (𝓞 E)) (p m : ℕ) (hP : GlobalTheory.IndefiniteRowSideFullHecke.HeckePrimeDetection.IsHeckePrime l P p) (k k' : U.Comp) (x : (U.X k).dom)
    (x' : (U.X k').dom) (C : Subgroup (Over.mk (U.un k x).x ⟶ Xo.univ.t.G)) (z : FrPt Xo c (CAt σ))
    (t : Ix Dw → (CAt σ)ˣ) (hK : Xo.univ.t.HeckeKer (Over.mk (U.un k x).x) Dw P p m C)
    (ψ : pullback Xo.univ.t.G.hom (U.un k x).x ⟶ pullback Xo.univ.t.G.hom z.x)
    (ψp : (Over.mk (U.un k x).x ⟶ Xo.univ.t.G) →* (Over.mk z.x ⟶ Xo.univ.t.G))
    (hI : IsHkIsog p (U.un k x).x z.x C ψ ψp)
    (hL : ∀ τ j, IsLieImageH p ψ ((U.un k x).u τ j) (z.u τ j)) (hB : FrBor t (U.un k' x') z) :
    ∃ (gam : (U.X k).Λ →ₗ[𝓞 E] (U.X k').Λ) (A : (E →+* ℂ) → ℕ → ℕ → ℂ),
      (∀ u v : (U.X k).Λ, Algebra.trace ℚ E (-(U.X k').ξ0 * herm (U.X k').Gm (gam u : Fin r → E) (gam v : Fin r → E)) =
        (p : ℚ) ^ 2 * Algebra.trace ℚ E (-(U.X k).ξ0 * herm (U.X k).Gm (u : Fin r → E) (v : Fin r → E))) ∧
      (∀ w : (U.X k').Λ, ∃ v, gam v = (p ^ 2) • w) ∧ (∀ τ i j, j < i → A τ i j = 0) ∧
      (∀ τ, ∀ n < Dw.mult τ, ∀ v : (U.X k).Λ, perFr (U.X k') x'.1 (gam v : Fin r → E) (relab c σ τ) n =
        p * ∑ j ∈ Finset.range (Dw.mult τ), A τ n j * perFr (U.X k) x.1 (v : Fin r → E) (relab c σ τ) j) ∧
      ∀ τ (n : Fin (Dw.mult τ)), A τ n n = toC (t (some ⟨τ, n⟩) : CAt σ) := by
  classical
  obtain ⟨-, -, -, -, -, g, e, F, ik, φ, hEF, hpt⟩ := hU
  obtain ⟨Pm, hPm, per, hPx, hv, -⟩ := hpt k x
  obtain ⟨Pm', hPm', per', hPx', hv', -⟩ := hpt k' x'
  have hpp : p.Prime := hP.2.2.2.1
  have hC : ∀ a ∈ C, a ^ p ^ 2 = 1 := fun a ha => GlobalTheory.HkPts.pow_eq_one hP.2.2.2.2 hK ha
  obtain ⟨gam, h, hiso, hh, honto, hder⟩ := GlobalTheory.HeckeEx.exists_lift_deriv F (ik k) (ik k') Pm Pm' per per' hpp hPx
    (hB.1.trans hPx') C ψ ψp hC hI
  choose cf hcf1 hcf2 hcf3 using hB.2.1
  have hp0 : (p : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hpp.ne_zero
  have hcol : ∀ τ n, h.toLinearMap (Pi.single (e.symm ⟨τ, n⟩) 1) =
      (∑ j, ((p : ℂ) * toC (cf τ n j)) • (Pi.single (e.symm ⟨τ, j⟩) 1 : Fin g → ℂ)) := by
    intro τ n
    obtain ⟨wv, hw1, hw2, hw3⟩ := hL τ n
    have d2 := hder (Pi.single (e.symm ⟨τ, n⟩) 1) wv hw2 (by have q := hv τ n; rw [← hw1] at q; exact q)
    have d1 := (GlobalTheory.DerLin.isCombAt_iff_isDerivAt0 E H Dw l Xo _ g _ F _ Pm' per' _ ((U.un k' x').u τ) _ (hv' τ) (cf τ n)
      (z.u τ n)).1 (hPx' ▸ hcf3 τ n)
    have d3 := ReciprocityTheory.ChartRestriction.G.PullbackSections.ExpRows.isDerivAt0_smul d1 (p : ℂ)
    have e3 : spMap (epsMul (p : ℂ)) ≫ z.u τ n = wv ≫ ψ ≫ pullback.fst _ _ := by
      rw [hw3]
      refine (GlobalTheory.HeckeEx.spMap_epsMul_comp (p : ℂ) ((p : ℂ)⁻¹) _).trans ?_
      rw [inv_mul_cancel₀ hp0]
      exact spMap_epsMul_one _
    rw [e3] at d3
    have tn := GlobalTheory.isDerivAt0_ex_isTanAt E H Dw l Xo _ g _ F _ Pm' per'
    show h (Pi.single (e.symm ⟨τ, n⟩) 1) = _
    rw [(tn.2.2 _ (tn.1 _ _ d2)).unique d2 d3, Finset.smul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    exact (smul_smul (p : ℂ) (toC (cf τ n j)) (Pi.single (e.symm ⟨τ, j⟩) 1 : Fin g → ℂ))
  refine ⟨(φ k').toLinearMap ∘ₗ gam ∘ₗ (φ k).symm.toLinearMap,
    fun τ i j => if hij : i < Dw.mult τ ∧ j < Dw.mult τ then
      toC (cf τ ⟨j, hij.2⟩ ⟨i, hij.1⟩) else 0, fun u v => ?_, fun w => ?_, fun τ i j hji => ?_,
    fun τ n hn v => ?_, fun τ i => ?_⟩
  · obtain ⟨u, rfl⟩ := (φ k).surjective u
    obtain ⟨v, rfl⟩ := (φ k).surjective v
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply]
    rw [← hEF, ← hEF, hiso]
    push_cast
    ring
  · obtain ⟨a, ha⟩ := honto ((φ k').symm w)
    refine ⟨φ k a, ?_⟩
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply]
    rw [ha, map_nsmul, LinearEquiv.apply_symm_apply]
  · beta_reduce
    split_ifs with hij
    · exact hcf2 τ _ _ hji
    · rfl
  · obtain ⟨v, rfl⟩ := (φ k).surjective v
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply]
    have a1 := hPm' (gam v) (e.symm ⟨τ, ⟨n, hn⟩⟩)
    rw [Equiv.apply_symm_apply] at a1
    rw [← a1, hh, Finset.sum_range, Finset.mul_sum]
    refine (GlobalTheory.LevelCusp.apply_of_cols e h.toLinearMap
      (fun τ i j => (p : ℂ) * toC (cf τ i j)) hcol (Pm v) τ ⟨n, hn⟩).trans
      (Finset.sum_congr rfl fun j _ => ?_)
    rw [hPm, Equiv.apply_symm_apply, dif_pos ⟨hn, j.2⟩, _root_.mul_assoc]
  · beta_reduce
    rw [dif_pos ⟨i.2, i.2⟩]
    exact congrArg _ (hcf1 τ i)

end GlobalTheory.HeckeExist

namespace GlobalTheory.HeckeExist

attribute [local instance] GlobalTheory.HeckeEx.fieldCAt GlobalTheory.HeckeEx.algClosedCAt

theorem isHeckePrime_of {D : D7} {Hh : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E} (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level Hh) (P : Formalism.L2.DIV.Pl D.host.E) (p : ℕ)
    (hc : Formalism.HermitianLatticesTheory.conjIdeal (K := D.host.E) P.asIdeal ≠ P.asIdeal) (hp : p.Prime) (hpP : (p : 𝓞 D.host.E) ∈ P.asIdeal)
    (hM : ¬ p ∣ l.M') : GlobalTheory.IndefiniteRowSideFullHecke.HeckePrimeDetection.IsHeckePrime l P.asIdeal p := by
  refine GlobalTheory.IndefiniteRowSideFullHecke.HeckePrimeDetection.isHeckePrime_iff.2 ⟨P.isMaximal, ?_, hp, hpP, hM⟩
  have hQ : Formalism.HermitianLatticesTheory.conjIdeal (K := D.host.E) P.asIdeal = P.asIdeal.map (Hh.bar : 𝓞 D.host.E →+* 𝓞 D.host.E) := by
    unfold Formalism.HermitianLatticesTheory.conjIdeal
    rw [Ideal.map]
    congr 1
    ext r
    constructor
    · rintro ⟨s, hs, e⟩
      refine ⟨s, hs, ?_⟩
      apply RingOfIntegers.coe_injective
      show ((Hh.bar s : 𝓞 D.host.E) : D.host.E) = (r : D.host.E)
      rw [Hh.bar_eq]
      exact e.symm
    · rintro ⟨s, hs, rfl⟩
      refine ⟨s, hs, ?_⟩
      show ((Hh.bar s : 𝓞 D.host.E) : D.host.E) = _
      rw [Hh.bar_eq]
      rfl
  rw [← hQ]
  have hmax : (P.asIdeal.map (Hh.bar : 𝓞 D.host.E →+* 𝓞 D.host.E)).IsMaximal :=
    Ideal.map_isMaximal_of_equiv Hh.bar
  rw [← hQ] at hmax
  by_contra hne
  have hle : Formalism.HermitianLatticesTheory.conjIdeal (K := D.host.E) P.asIdeal ≤ P.asIdeal :=
    le_sup_right.trans ((P.isMaximal.eq_of_le hne le_sup_left).symm.le)
  exact hc (hmax.eq_of_le P.isMaximal.ne_top hle)

theorem exists_coset_frBor_of_hkKer : ∀ (D : D7), GlobalTheory.IndefiniteRowSideFullHecke.HeckePrimeDetection.HeckePointLaws → GlobalTheory.IndefiniteRowSideFullHecke.SplitLinearModelNorm.SplitLinearModel D → GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter.VacFixed D →
    ∀ (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m)
    (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A)
    (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec),
    R.toLevCh.Is A.μ0 → R.IsGrp F → R.IsFam → R.IsModels → R.IsThP → TieIn T R κ v₀ →
    ∀ (i : Fin D.R.m) (σ : T.Q.c.F →+* ℂ), σ = T.σ₀ → ∀ hV : T.V ((i : ℕ) + 1) σ = Wc D i,
      GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.FramePin T R i σ hV →
    ∀ (P : Formalism.L2.DIV.Pl D.host.E) (p k : ℕ) (α : GA D (Wc D i)) (Rc : Finset (GA D (Wc D i))),
      GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.IsUnitaryHeckeOperatorSplitPrimeData T R i P p k α Rc →
    ∀ (h : GA D (Wc D i)) (hx : (GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.dictW T i σ hV h).2 ∈ ((T.U ((i : ℕ) + 1) σ).X (GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.dictW T i σ hV h).1).dom),
      letI : Field (CAt σ) := inferInstanceAs (Field ℂ)
      haveI : IsAlgClosed (CAt σ) := inferInstanceAs (IsAlgClosed ℂ)
      ∀ C : hkKer (Xo := T.Q.Xo ((i : ℕ) + 1)) P.asIdeal p k (CAt σ) ((T.U ((i : ℕ) + 1) σ).un (GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.dictW T i σ hV h).1 ⟨(GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.dictW T i σ hV h).2, hx⟩),
        ∃ a ∈ Rc, ∀ z, hkRelFr P.asIdeal p k (GlobalTheory.ThetaTrace.hkTr (T.Q.Xo ((i : ℕ) + 1)) T.Q.c p) (CAt σ) ((T.U ((i : ℕ) + 1) σ).un (GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.dictW T i σ hV h).1 ⟨(GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.dictW T i σ hV h).2, hx⟩) C z →
          ∃ (hx' : (GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.dictW T i σ hV (h * a)).2 ∈ ((T.U ((i : ℕ) + 1) σ).X (GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.dictW T i σ hV (h * a)).1).dom) (t : Ix (T.Q.Dw ((i : ℕ) + 1)) → (CAt σ)ˣ),
            (∀ j, j ≠ none → t j = 1) ∧ FrBor t ((T.U ((i : ℕ) + 1) σ).un (GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.dictW T i σ hV (h * a)).1 ⟨(GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.dictW T i σ hV (h * a)).2, hx'⟩) z := by
  intro D hHk hSL hVF G _ _ Pl0 T0 A T _ R F κ v₀ hLv hG hFam hMod hTh hTie i σ hσ hV hPin P p k α Rc hS h hx C
  obtain ⟨-, hTot, hFun, -⟩ := id hHk
  have hL := hTie.laws
  have hj : InR D ((i : ℕ) + 1) := ⟨Nat.le_add_left _ _, i.2⟩
  have hσ' : GoodEmb T.Q.c σ := hσ ▸ T.toCore.good_σ₀
  have hU : IsUnf (T.U ((i : ℕ) + 1) σ) := hL.unf _ hj σ hσ'
  obtain ⟨hSp, hp, hpP, hM, -, -, -⟩ := id hS
  have hP : GlobalTheory.IndefiniteRowSideFullHecke.HeckePrimeDetection.IsHeckePrime T.Q.l P.asIdeal p := isHeckePrime_of T.Q.l P p hSp.1 hp hpP hM
  obtain ⟨z₀, hz₀⟩ := hTot D.host.E T.Q.H (T.Q.Dw ((i : ℕ) + 1)) T.Q.l (T.Q.Xo ((i : ℕ) + 1)) T.Q.c P.asIdeal p k hP (CAt σ) _ C
  obtain ⟨k', x', t', hB⟩ := hU.2.2.1 z₀
  obtain ⟨ψ, ψp, hI, hLie, -⟩ := id hz₀
  obtain ⟨gam, A', h1, h2, h3, h4, h5⟩ := similitude_tri_of_hkIsog _ hU P.asIdeal p k hP _ k' _ x' C.1 z₀ t' C.2 ψ ψp hI hLie hB
  obtain ⟨a, ha, hx', t, ht, hB'⟩ := GlobalTheory.T.hecke_point_eq_unipotent_frame_change_coset_rep D hHk hSL hVF G Pl0 T0 A T R F κ v₀ hLv hG hFam hMod hTh hTie i σ hσ hV hPin P p k α Rc
    hS h hx C z₀ hz₀ k' x' t' hB gam A' h1 h2 h3 h4 h5
  refine ⟨a, ha, fun z hz => ?_⟩
  have e := hFun D.host.E T.Q.H (T.Q.Dw ((i : ℕ) + 1)) T.Q.l (T.Q.Xo ((i : ℕ) + 1)) T.Q.c P.asIdeal p k hP (CAt σ) _ C z₀ z hz₀ hz
  have e2 := (GlobalTheory.Frames.frMap_unique_refl_iff _ _ _ _ _ _ _ _ (AlgHom.id T.Q.c.F (CAt σ)) z₀).1 _ _ e
    (GlobalTheory.Frames.frMap_unique_refl_iff _ _ _ _ _ _ _ _ (AlgHom.id T.Q.c.F (CAt σ)) z₀).2.1
  subst e2
  exact ⟨hx', t, ht, hB'⟩

end GlobalTheory.HeckeExist
