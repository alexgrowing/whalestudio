import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IdemAtEqOneIff
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsNumberFieldPoint
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsOpenImmersionOfSection
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SubmatrixMulVec
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.NvalDetFrChgConst
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsFinsetIntegralOfDefinite
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsIsUnf
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsLevelGoodAtAllPrimesAndIdx
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.LevelOfSplitAndLevelCoeffExist
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PtOfFrameEqOfPointEq
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.HasseNormTheoremQuadraticExtension
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.MemRangeOfIsAlgebraicRatFun
import Development.AbelianVarietyTheory.Definitions.CMLattices.IsCyclotomicExtensionCyclotomicField28

noncomputable section

namespace GlobalTheory.FlatLine.Definite

open NumberField IsDedekindDomain AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.Frames

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l}

theorem comp_eq {σ : c.F →+* ℂ} {r : ℕ} {U : Unf Xo c σ r} (hσ : GoodEmb c σ) (hU : IsUnf U) {k k' : U.Comp}
    (x : (U.X k).dom) (x' : (U.X k').dom) (h : (U.un k x).x = (U.un k' x').x) : k' = k := by
  obtain ⟨b, -, -, hb, t, ht⟩ := GlobalTheory.PointOfFrames.exists_frBor (Formalism.L2.PjFree.Unf.ofPj U) hU hσ k x (U.un k' x') h
  obtain ⟨γ, -, b', -, e⟩ := (hU.2.2.2.1 k k' ⟨_, hb⟩ x').1 ⟨t, ht⟩
  exact congrArg Sigma.fst e

theorem nonempty_flatSec {r : ℕ} (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (x : ℝ) (hq : Dw.q = 0) (hp : 1 ≤ Dw.p)
    (hg : ∀ p : ℕ, p.Prime → l.GoodAt p) (hU : ∀ σ, GoodEmb c σ → IsUnf (U σ)) (hF : FnAlgClosed Xo c)
    (Z : Comp Xo c) (τ : Psi H) : Nonempty (FlatSec U x Z τ) := by
  have hpq : 1 ≤ Dw.p + Dw.q := by omega
  have hP := hasPts U hpq hg hU Z
  obtain ⟨y₀, h₀, hy₀⟩ := GlobalTheory.FlatLine.DefinitePoint.main E H Dw l Xo c hq hF Z
  obtain ⟨f, f', m₁, m₂, i₁, i₂, hm, hv⟩ := exists_flatRule E H Dw l Xo c hq Z τ y₀ h₀ hy₀
  have chg : ∀ (S : Type) [CommRing S] [Algebra c.F S] (y z : FrPt Xo c S), LiesOn Z y →
      FrMap (Algebra.ofId c.F S) y₀ z → ∃ (g : (∀ ρ : E →+* ℂ, Matrix (Fin (Dw.mult ρ)) (Fin (Dw.mult ρ)) S)) (a : Sˣ), (∀ ρ, IsUnit (g ρ).det) ∧ FrChg g (a : S) y z :=
    fun S _ _ y z hy hz => (frChg_exists_unique E H Dw l Xo c S y z).1 (hz.1.trans (hy₀ S y hy).symm)

  have hinf : ∀ σ : c.F →+* ℂ, ∃ b : ℝ, 0 < b ∧ homN (U (goodOf c σ)) x (wtOf Dw (flatWt Dw τ) 0) f ''
      framesOn (U (goodOf c σ)) Z = {b} := by
    intro σ₀
    obtain ⟨⟨⟨k, x₀⟩, hx₀⟩, ht⟩ := hP.1 σ₀
    have hσ := goodEmb_goodOf c σ₀
    generalize goodOf c σ₀ = σ at *
    have hV := hU σ hσ
    obtain ⟨z, hz⟩ := exists_bc (Algebra.ofId c.F (CAt σ)) y₀
    have hτ : ∀ k, relab c σ τ.1 ∈ ((U σ).X k).Ψ := fun k => ((hV.2.1 k).2 _).2 (by
      have hσ0 : σ ⟨H.rt0, c.le (baseKA l).ρ.2⟩ = H.rt0 := hσ
      exact (congrArg σ (Subtype.ext τ.2)).trans hσ0)
    have rd : ∀ k y (hy : (⟨k, y⟩ : Σ k, Frame ((U σ).X k).Ψ r) ∈ framesOn (U σ) Z) g a,
        FrChg g a ((U σ).un k ⟨y, hy.1⟩) z → rdU (U σ) f k y = toC (g τ.1).det := fun k y hy g a hc => by
      simp only [rdU, LinearMap.coe_mk, AddHom.coe_mk, hy.1, dif_pos]
      exact congrArg toC (hv _ _ z g a (ht _ hy hy.1) hz hc)
    have hh : IsHorizontal (U σ) Z τ f := fun k => by
      by_cases hne : ∃ y, (⟨k, y⟩ : Σ k, Frame ((U σ).X k).Ψ r) ∈ framesOn (U σ) Z
      · obtain ⟨y₁, h₁⟩ := hne
        refine ⟨hτ k, rdU (U σ) f k y₁ * (mat y₁ ⟨_, hτ k⟩).det, fun y hy => ?_⟩
        obtain ⟨g₁, a₁, -, c₁⟩ := chg _ _ z h₁.2 hz
        obtain ⟨g, a, -, c₂⟩ := (frChg_exists_unique E H Dw l Xo c _ ((U σ).un k ⟨y, hy.1⟩)
          ((U σ).un k ⟨y₁, h₁.1⟩)).1 ((hy₀ _ _ h₁.2).trans (hy₀ _ _ hy.2).symm)
        have c₃ := (frChg_refl_and_comp E H Dw l Xo c _ _ _ _).2 _ _ _ _ c₂ c₁
        have e := GlobalTheory.FlatChange.det_frChg E H Dw l Xo c σ r (U σ) hq hσ hV k ⟨y, hy.1⟩ ⟨y₁, h₁.1⟩ τ (hτ k) g a c₂
        rw [rd k y hy _ _ c₃, rd k y₁ h₁ _ _ c₁, e, horizGen, Matrix.det_mul, mul_assoc, mul_assoc,
          mul_inv_cancel₀ (hy.1 _).1, mul_one]
        rfl
      · exact ⟨hτ k, 0, fun y hy => absurd ⟨y, hy⟩ hne⟩
    obtain ⟨b, hb⟩ := hh.homN_const hσ hV x k
    refine ⟨b, ?_, image_eq_singleton_iff.2 ⟨⟨_, hx₀⟩, ?_⟩⟩
    · have h1 := homN_mul (U σ) x (even_wtOf (-flatWt Dw τ) 0) (even_wtOf (flatWt Dw τ) 0) f' f ⟨k, x₀⟩ hx₀.1
      rw [← wtOf_add', neg_add_cancel, wtOf_zero, mul_comm f', hm, homN_idem _ x hx₀.1 hx₀.2 (ht _ hx₀ _),
        hb x₀ hx₀] at h1
      refine lt_of_le_of_ne (hb x₀ hx₀ ▸ homN_nonneg _ _ _ _ _) fun h0 => ?_
      rw [← h0, mul_zero] at h1
      exact one_ne_zero h1
    · rintro ⟨k', y⟩ hy
      obtain rfl : k' = k := comp_eq hσ hV ⟨x₀, hx₀.1⟩ ⟨y, hy.1⟩ ((hy₀ _ _ hx₀.2).trans (hy₀ _ _ hy.2).symm)
      exact hb y hy
  choose cI hI₁ hI₂ using hinf

  choose ρ hρ using GlobalTheory.FlatLine.PlaceConst.nval_det_frChg_const E H Dw l Xo c hpq hg y₀ τ.1
  obtain ⟨S, hS0, hS⟩ := GlobalTheory.FlatLine.exists_finset_integral_of_definite E H Dw l Xo c hq hp hg y₀
  refine ⟨⟨f, f', m₁, m₂, i₁, i₂, hm, cI, hI₁, hI₂, ρ, fun w => image_eq_singleton_iff.2 ⟨hP.2 w, ?_⟩, ?_⟩⟩
  · rintro _ ⟨⟨_, T, io, e, ho, y, hy, η, hη, rfl⟩, rfl⟩
    letI := io.toAlgebra
    obtain ⟨z, hz⟩ := exists_bc (Algebra.ofId c.F T.Fr) y₀
    obtain ⟨g, a, -, hc⟩ := chg _ y.1 z hy.2 hz
    show nval T.V e (evR Xo c f y.1) = _
    rw [hv _ _ z g a y.2.1 hz hc, hρ w T io e ho y.1 z g a y.2.2 hz hc]
    simp [flDefect_vw, hq]
  · refine (S.finite_toSet.biUnion fun s hs => finite_vAdd (hS0 s hs)).subset fun w hw => ?_
    by_contra hn
    simp only [Set.mem_iUnion, Function.mem_support, not_exists, not_not, Int.cast_eq_zero] at hn
    obtain ⟨_, ⟨_, T, io, e, ho, -⟩, -⟩ := hP.2 w
    letI := io.toAlgebra
    obtain ⟨z, hz⟩ := exists_bc (Algebra.ofId c.F T.Fr) y₀
    have hi := hS T io (fun s hs => by rw [ho.2 s]; exact mul_eq_zero_of_right _ (hn s hs)) z hz
    have h1 := hρ w T io e ho z z _ _ hi hz (frChg_refl_and_comp E H Dw l Xo c _ z z z).1
    rw [Matrix.det_one, nval_of_ne one_ne_zero, EReal.coe_eq_coe_iff] at h1
    exact hw (h1.symm.trans (by simp [vV]))

theorem exists_flatSec (x : ℝ) : ∃ (E : Type) (_ : Field E) (_ : NumberField E) (_ : IsCMField E)
    (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l)
    (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ (Dw.p + Dw.q)) (Z : Comp Xo c) (τ : Psi H),
    1 ≤ Dw.p ∧ (∀ σ, GoodEmb c σ → IsUnf (U σ)) ∧ Nonempty (FlatSec U x Z τ) := by
  obtain ⟨D, hp, hq⟩ := GlobalTheory.CM.CyclotomicTwentyEight.exists_datum
  have hpq : 1 ≤ D.p + D.q := by omega
  obtain ⟨l, -, hg, -⟩ := GlobalTheory.exists_level_goodAt_all_primes_and_idx _ GlobalTheory.CM.CyclotomicTwentyEight.host 1 one_pos
  obtain ⟨Xo⟩ := GlobalTheory.Moduli.moduli_scheme_exists _ _ D l hpq
  obtain ⟨c₀⟩ : Nonempty (Coeff l) := inferInstance
  obtain ⟨-, c, -, hc⟩ := GlobalTheory.GeomIrr.compNe_and_exists_fnAlgClosed _ _ D l Xo c₀ hpq
  obtain ⟨⟨Z⟩, -⟩ := GlobalTheory.GeomIrr.compNe_and_exists_fnAlgClosed _ _ D l Xo c hpq
  have hU : ∀ σ : c.F →+* ℂ, ∃ U : Unf Xo c σ (D.p + D.q), GoodEmb c σ → IsUnf U := fun σ => by
    by_cases hσ : GoodEmb c σ
    · obtain ⟨U, hU⟩ := GlobalTheory.IsUnfEx.exists_isUnf GlobalTheory.closing_of_abelianSchemeLaws GlobalTheory.QNorm.hasseNormSt
        GlobalTheory.abelianSchemeLaws_all.1.secBaseChange GlobalTheory.abelianSchemeLaws_all.2.secTwist _ _ D l Xo c σ hpq hσ
      exact ⟨U.toPj, fun _ => hU⟩
    · exact ⟨{ Comp := PEmpty, X := fun k => k.elim, un := fun k => k.elim }, fun h => absurd h hσ⟩
  choose U hU using hU
  obtain ⟨τ⟩ : Nonempty (Psi GlobalTheory.CM.CyclotomicTwentyEight.host) := by
    obtain ⟨ρ⟩ : Nonempty (GlobalTheory.CM.CyclotomicTwentyEight.CyclotomicFieldTwentyEight →+* ℂ) := inferInstance
    by_cases h : ρ (GlobalTheory.CM.CyclotomicTwentyEight.host.rt : GlobalTheory.CM.CyclotomicTwentyEight.CyclotomicFieldTwentyEight) = GlobalTheory.CM.CyclotomicTwentyEight.host.rt0
    exacts [⟨⟨ρ, h⟩⟩, ⟨⟨_, conj_mem h⟩⟩]
  exact ⟨_, _, _, _, _, D, l, Xo, c, U, Z, τ, hp.ge, hU,
    nonempty_flatSec U x hq hp.ge hg hU (hc c le_rfl) Z τ⟩

end GlobalTheory.FlatLine.Definite
