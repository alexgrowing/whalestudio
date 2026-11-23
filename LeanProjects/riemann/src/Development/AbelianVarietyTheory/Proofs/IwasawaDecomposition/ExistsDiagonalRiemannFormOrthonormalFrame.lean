import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsLieBase
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.HodgePeriodGram
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HodgeChartBoundsOfSchurLemW
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PerValNeZero
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsExponentialChartAtPoint
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HodgeMetricUniformisationSmoothOnInterior
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsExponentialModelFiberOfUniformisationExp
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsHolomorphicUniformisationExpModelFiber
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExpModelFiberEqOneIffMemPeriodLattice
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.WeilPairingExpModelFiberEqAlternatingForm
open AlgebraicGeometry CategoryTheory Limits MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Matrix
open scoped ComplexOrder Topology
open GlobalTheory.ShFam.Hor GlobalTheory.CxPts
open MonoidalCategory CartesianMonoidalCategory MonObj GlobalTheory.ShFam.Hor.LogCh
open ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.ArcQ GlobalTheory.FrameNormLie GlobalTheory.HodgeSmooth
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

section EigenvectorOrthogonality

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TopologicalSpace Matrix
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.CxPts GlobalTheory.Toroidal GlobalTheory.LieMet GlobalTheory.GradedNorm
open GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.ProjVar.Var GlobalTheory.ShFam.Pad
open ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.ArcQ GlobalTheory.FrameNormLie GlobalTheory.ShFam
open scoped ComplexOrder

namespace GlobalTheory.HodgeSmooth.EigOrth

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {σ : c.F →+* ℂ} {r : ℕ}

open Classical in

def riemConst (U : Formalism.L2.PjFree.Unf Xo c σ r) (k : U.Comp) (τ : E →+* ℂ) : ℝ :=
  2 * ((if Formalism.L2.PjFree.relab c σ τ ∈ (U.X k).Ψ then Formalism.L2.PjFree.relab c σ τ
    else ComplexEmbedding.conjugate (Formalism.L2.PjFree.relab c σ τ)) (-(U.X k).ξ0)).im

theorem exists_diag_im {U : Formalism.L2.PjFree.Unf Xo c σ r} (hσ : Formalism.L2.PjFree.GoodEmb c σ)
    (hU : Formalism.L2.PjFree.IsUnf U) (W : UnfWit U) (k : U.Comp) (x : (U.X k).dom) (hx : IsOrth (U.X k) x.1) :
    ∃ D : Fin W.g → ℂ, (∀ τ (j : Fin (Dw.mult τ)), D (W.e.symm ⟨τ, j⟩) = ((riemConst U k τ : ℝ) : ℂ)) ∧
      ∀ v w, (hermForm (diagonal D) (W.Pm k x v) (W.Pm k x w)).im = (W.F.Di (W.ik k)).EF v w := by
  classical
  obtain ⟨hp0, hty⟩ := hU.2.1 k
  obtain ⟨hbij, hrt, -, -⟩ := GlobalTheory.Relab.relab_good E H l c σ hσ
  obtain ⟨f, hf⟩ := FrameUnif.exists_letter_equiv (U.X k).Ψ (U.X k).cmType Dw.p Dw.q r hU.1
    (Formalism.L2.PjFree.relab c σ) hbij Dw.mult
    (fun τ h => by unfold Datum.mult; rw [if_pos ((hrt τ).1 ((hty _).1 h))])
    (fun τ h => by unfold Datum.mult; rw [if_neg (fun h' => h ((hty _).2 ((hrt τ).2 h')))])
  rw [← hp0] at hf
  have hper (v) : W.Pm k x v = perVec (U.X k) (W.e.trans f) x.1 (W.φ k v : Fin r → E) := funext fun j => by
    rw [W.Pm_eq, perVec, Equiv.trans_apply]
    have h := hf (W.e j)
    generalize f (W.e j) = t at h ⊢
    obtain ⟨⟨τ, hτ⟩, ⟨n, hn⟩⟩ := t
    dsimp only at h ⊢
    rcases h with ⟨a, rfl, rfl⟩ | ⟨a, rfl, rfl, d⟩
    · rw [if_neg (by omega), Formalism.L2.PjFree.perFr, dif_pos a, dif_pos hn]
    · rw [if_pos (by omega), Formalism.L2.PjFree.perFr, dif_neg a,
        dif_pos (show conjEmb (Formalism.L2.PjFree.relab c σ (W.e j).1) ∈ (U.X k).Ψ from hτ), dif_pos hn]
      rfl
  refine ⟨diagXi (U.X k) (W.e.trans f), fun τ j => ?_, fun v w => ?_⟩
  · rw [diagXi, Equiv.trans_apply, Equiv.apply_symm_apply]
    rcases hf ⟨τ, j⟩ with ⟨a, h1, -⟩ | ⟨a, h1, -, -⟩
    · rw [h1]
      simp only [riemConst, if_pos a]
    · rw [h1]
      simp only [riemConst, if_neg a]
  · rw [hper, hper, im_diag_ortho _ _ _ hx, ← W.iso]
    simp

theorem riemConst_pos {U : Formalism.L2.PjFree.Unf Xo c σ r} (hσ : Formalism.L2.PjFree.GoodEmb c σ)
    (hU : Formalism.L2.PjFree.IsUnf U) (W : UnfWit U) (k : U.Comp) (x : (U.X k).dom) (hx : IsOrth (U.X k) x.1)
    (τ : E →+* ℂ) (hτ : 0 < Dw.mult τ) : 0 < riemConst U k τ := by
  classical
  obtain ⟨D, hD, him⟩ := exists_diag_im hσ hU W k x hx
  obtain ⟨-, -, -, hspan, Hm₀, -, hpos, hHm₀⟩ := W.period k x
  have e := UnitDet.eq_of_im_hermForm_eq _ hspan (diagonal D) Hm₀ (by
    rintro _ ⟨v, rfl⟩ _ ⟨w, rfl⟩
    rw [him, hHm₀])
  set j := W.e.symm ⟨τ, ⟨0, hτ⟩⟩
  have h := hpos (Pi.single j 1) (by simp)
  rw [← e] at h
  have h2 : hermForm (diagonal D) (Pi.single j 1) (Pi.single j 1) = D j := by
    simp [hermForm]
  rw [h2, hD] at h
  simpa using h

end GlobalTheory.HodgeSmooth.EigOrth

end EigenvectorOrthogonality

open GlobalTheory.HodgeSmooth.EigOrth in

theorem GlobalTheory.HodgeSmooth.exists_diag_riem_orth : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (r : ℕ) (U : Formalism.L2.PjFree.Unf Xo c σ r), Formalism.L2.PjFree.GoodEmb c σ → Formalism.L2.PjFree.IsUnf U → ∀ (W : UnfWit U), ∃ d : U.Comp → (E →+* ℂ) → ℝ, (∀ (k : U.Comp) (x : (U.X k).dom), IsOrth (U.X k) x.1 → ∀ τ : E →+* ℂ, 0 < Dw.mult τ → 0 < d k τ) ∧ ∀ (k : U.Comp) (x : (U.X k).dom), IsOrth (U.X k) x.1 → ∀ (i : Fin W.F.n) (P : (W.F.Di i).La →+ (Fin W.g → ℂ)), IsPeriod (W.F.Di i) (fun j => Formalism.L2.PjFree.relab c σ (W.e j).1) P → ∀ (Hm : Matrix (Fin W.g) (Fin W.g) ℂ), (∀ v w, (hermForm Hm (P v) (P w)).im = (W.F.Di i).EF v w) → W.F.u i P = (U.un k x).x → ∀ (τ τ' : E →+* ℂ) (zz : Fin (Dw.mult τ) → (Fin W.g → ℂ)) (zz' : Fin (Dw.mult τ') → (Fin W.g → ℂ)) (uu : Fin (Dw.mult τ) → (Sp (DualNumber ℂ) ⟶ Xo.univ.t.G.left)) (uu' : Fin (Dw.mult τ') → (Sp (DualNumber ℂ) ⟶ Xo.univ.t.G.left)) (T : Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) ℂ) (T' : Matrix (Fin (Dw.mult τ')) (Fin (Dw.mult τ')) ℂ), (∀ b, IsDerivAt0 (fun w => (W.F.ex i P w).left) (zz b) (uu b)) → (∀ b, IsDerivAt0 (fun w => (W.F.ex i P w).left) (zz' b) (uu' b)) → (∀ b, IsCombAt (U.un k x).x ((U.un k x).u τ) (show Fin (Dw.mult τ) → CAt σ from fun b' => T b' b) (uu b)) → (∀ b, IsCombAt (U.un k x).x ((U.un k x).u τ') (show Fin (Dw.mult τ') → CAt σ from fun b' => T' b' b) (uu' b)) → (of fun b b' => hermForm Hm (zz b') (zz b)) = ((d k τ : ℝ) : ℂ) • (Tᴴ * T) ∧ (τ' ≠ τ → ∀ b b', hermForm Hm (zz' b') (zz b) = 0) := by
  classical
  intro E _ _ _ H Dw l Xo c σ r U hσ hU W
  refine ⟨fun k τ => riemConst U k τ, fun k x hx τ hτ => riemConst_pos hσ hU W k x hx τ hτ, ?_⟩
  intro k x hx i P hP Hm hH hPu τ τ' zz zz' uu uu' T T' hder hder' hT hT'
  obtain ⟨D, hD, him⟩ := exists_diag_im hσ hU W k x hx
  have p := W.period k x
  obtain ⟨hPx, hv⟩ := W.lie k x
  obtain ⟨h, gam, hex, hh, hiso, -⟩ := familyUnif_exp_unique E H Dw l Xo _ _ _ W.F i (W.ik k) P _ hP p
    (by rw [← hPx]; exact hPu)
  set A := LinearMap.toMatrix' h.toLinearMap with hA
  have hAv : ∀ z, A *ᵥ z = h z := fun z => by rw [hA, LinearMap.toMatrix'_mulVec]; rfl
  have hcol : ∀ (τ : E →+* ℂ) (zz : Fin (Dw.mult τ) → (Fin W.g → ℂ))
      (uu : Fin (Dw.mult τ) → (Sp (DualNumber ℂ) ⟶ Xo.univ.t.G.left))
      (T : Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) ℂ),
      (∀ b, IsDerivAt0 (fun w => (W.F.ex i P w).left) (zz b) (uu b)) →
      (∀ b, IsCombAt (U.un k x).x ((U.un k x).u τ) (show Fin (Dw.mult τ) → CAt σ from fun b' => T b' b) (uu b)) →
      ∀ b, A *ᵥ zz b = ∑ j, T j b • (Pi.single (W.e.symm ⟨τ, j⟩) 1 : Fin W.g → ℂ) := by
    intro τ zz uu T hder hT b
    have d1 := (DerLin.isCombAt_iff_isDerivAt0 E H Dw l Xo _ _ _ W.F _ _ p _ ((U.un k x).u τ) _ (hv τ) _
      (uu b)).1 (hPx ▸ hT b)
    have d2 := (ExpChain.isDerivAt0_ex_iff E H Dw l Xo _ _ _ W.F _ P hP _ _ h.toLinearMap p hex _ _).1 (hder b)
    have tn := isDerivAt0_ex_isTanAt E H Dw l Xo _ _ _ W.F _ _ p
    rw [hAv]
    exact (tn.2.2 _ (tn.1 _ _ d2)).unique d2 d1
  have key := UnitDet.eq_of_im_hermForm_eq _ hP.2.2.2.1
    (Aᵀ * (diagonal D * A.map (starRingEnd ℂ))) Hm (by
      rintro _ ⟨v, rfl⟩ _ ⟨w, rfl⟩
      rw [← UnitDet.hermForm_mulVec, hAv, hAv, ← hh, ← hh, him, hiso, hH])
  refine ⟨?_, fun hne b b' => ?_⟩
  · have hsupp : ∀ b, diagonal D *ᵥ star (∑ j, T j b • (Pi.single (W.e.symm ⟨τ, j⟩) 1 : Fin W.g → ℂ)) =
        (((riemConst U k τ : ℝ) : ℂ) • (1 : Matrix (Fin W.g) (Fin W.g) ℂ)) *ᵥ
          star (∑ j, T j b • (Pi.single (W.e.symm ⟨τ, j⟩) 1 : Fin W.g → ℂ)) := by
      intro b
      simp only [smul_mulVec, Matrix.one_mulVec]
      funext p'
      rw [mulVec_diagonal, Pi.smul_apply, smul_eq_mul]
      by_cases hp : ∃ j, W.e.symm ⟨τ, j⟩ = p'
      · obtain ⟨j, rfl⟩ := hp
        rw [hD τ j]
      · push_neg at hp
        have : (∑ j, T j b • (Pi.single (W.e.symm ⟨τ, j⟩) 1 : Fin W.g → ℂ)) p' = 0 := by
          rw [Finset.sum_apply]
          exact Finset.sum_eq_zero fun j _ => by rw [Pi.smul_apply, Pi.single_eq_of_ne (hp j).symm, smul_zero]
        simp [Pi.star_apply, this]
    ext b b'
    rw [of_apply, ← key, ← UnitDet.hermForm_mulVec, hcol τ zz uu T hder hT, hcol τ zz uu T hder hT, hermForm,
      hsupp, ← hermForm]
    beta_reduce
    generalize ((riemConst U k τ : ℝ) : ℂ) = dd
    clear hsupp key hcol hAv hiso hh hex him hD hT hder hH hPu hT' hder'
    have hi : ∀ j j' : Fin (Dw.mult τ), W.e.symm ⟨τ, j⟩ = W.e.symm ⟨τ, j'⟩ ↔ j = j' := fun j j' => by simp
    simp [hermForm, smul_mulVec, sum_dotProduct, dotProduct_sum, star_sum, Pi.single_apply, hi, mul_apply, mul_comm]
  · rw [← key, ← UnitDet.hermForm_mulVec, hcol τ' zz' uu' T' hder' hT', hcol τ zz uu T hder hT]
    simp only [hermForm, dotProduct, mulVec_diagonal, Pi.star_apply]
    refine Finset.sum_eq_zero fun q _ => ?_
    by_cases hq : ∃ j, W.e.symm ⟨τ', j⟩ = q
    · obtain ⟨j, rfl⟩ := hq
      have : (∑ j'', T j'' b • (Pi.single (W.e.symm ⟨τ, j''⟩) 1 : Fin W.g → ℂ)) (W.e.symm ⟨τ', j⟩) = 0 := by
        rw [Finset.sum_apply]
        refine Finset.sum_eq_zero fun j'' _ => ?_
        rw [Pi.smul_apply, Pi.single_eq_of_ne, smul_zero]
        intro he
        exact hne (congrArg Sigma.fst (W.e.symm.injective he))
      rw [this]
      simp
    · push_neg at hq
      have : (∑ j, T' j b' • (Pi.single (W.e.symm ⟨τ', j⟩) 1 : Fin W.g → ℂ)) q = 0 := by
        rw [Finset.sum_apply]
        exact Finset.sum_eq_zero fun j _ => by rw [Pi.smul_apply, Pi.single_eq_of_ne (hq j).symm, smul_zero]
      rw [this]
      simp
