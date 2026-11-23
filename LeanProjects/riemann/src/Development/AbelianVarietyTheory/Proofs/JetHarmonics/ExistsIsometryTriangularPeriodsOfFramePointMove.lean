import Mathlib
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsIsometryOfSabMap
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FramedPointMoveCalculus
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.ExistsUnitGramFrameBorelChange
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.CabsDiagEqOne
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.UnitFramesGeneratorRatioModulusOne
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IsDerivAt0OfIsPullback

open NumberField AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj GlobalTheory.LevelCusp
open GlobalTheory.Dict (castFr)
open GlobalTheory.FrameNorm (IsUnitFr)
open scoped Matrix

namespace GlobalTheory.LevelCusp

theorem apply_of_cols {α : Type} {m : α → ℕ} {g : ℕ} (e : Fin g ≃ Σ τ : α, Fin (m τ))
    (h : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ)) (cf : ∀ τ, Fin (m τ) → Fin (m τ) → ℂ)
    (hcol : ∀ τ i, h (Pi.single (e.symm ⟨τ, i⟩) 1) =
      ∑ j, cf τ i j • (Pi.single (e.symm ⟨τ, j⟩) 1 : Fin g → ℂ)) (z : Fin g → ℂ) (τ : α) (i : Fin (m τ)) :
    h z (e.symm ⟨τ, i⟩) = ∑ j, cf τ j i * z (e.symm ⟨τ, j⟩) := by
  classical
  refine Pi.single_induction (p := fun z => h z (e.symm ⟨τ, i⟩) = ∑ j, cf τ j i * z (e.symm ⟨τ, j⟩)) z (by simp)
    (fun z w hz hw => by simp only [map_add, Pi.add_apply, hz, hw, mul_add, Finset.sum_add_distrib]) fun n a => ?_
  · beta_reduce
    obtain ⟨⟨τ', i'⟩, rfl⟩ := e.symm.surjective n
    have h1 : (Pi.single (e.symm ⟨τ', i'⟩) a : Fin g → ℂ) = a • (Pi.single (e.symm ⟨τ', i'⟩) 1 : Fin g → ℂ) := by
      rw [← Pi.single_smul, smul_eq_mul, mul_one]
    rw [h1, map_smul, hcol]
    simp only [Pi.smul_apply, Finset.sum_apply, smul_eq_mul, Pi.single_apply, EmbeddingLike.apply_eq_iff_eq]
    by_cases hτ : τ = τ'
    · subst hτ
      simp [mul_comm]
    · simp [hτ]

set_option maxHeartbeats 1000000 in

theorem exists_isometry_tri_of_frMove : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (r : ℕ) (U : Formalism.L2.PjFree.Unf Xo c σ r), Formalism.L2.PjFree.GoodEmb c σ → Formalism.L2.PjFree.IsUnf U → ∀ (ρ : Xo.X ⟶ Xo.X) (ν : SABMap Xo.univ.t Xo.univ.t ρ) (k k' : U.Comp) (x : (U.X k).dom) (x' : (U.X k').dom) (y' : FrPt Xo c (CAt σ)) (t : Ix Dw → (CAt σ)ˣ), FrMove ρ ν (U.un k x) y' → FrBor t (U.un k' x') y' → ∃ (gam : (U.X k).Λ ≃ₗ[𝓞 E] (U.X k').Λ) (A : (E →+* ℂ) → ℕ → ℕ → ℂ), (∀ u v : (U.X k).Λ, Algebra.trace ℚ E (-(U.X k').ξ0 * herm (U.X k').Gm (gam u : Fin r → E) (gam v : Fin r → E)) = Algebra.trace ℚ E (-(U.X k).ξ0 * herm (U.X k).Gm (u : Fin r → E) (v : Fin r → E))) ∧ (∀ τ i j, j < i → A τ i j = 0) ∧ (∀ τ, ∀ i < Dw.mult τ, ∀ v : (U.X k).Λ, Formalism.L2.PjFree.perFr (U.X k') x'.1 (gam v : Fin r → E) (Formalism.L2.PjFree.relab c σ τ) i = ∑ j ∈ Finset.range (Dw.mult τ), A τ i j * Formalism.L2.PjFree.perFr (U.X k) x.1 (v : Fin r → E) (Formalism.L2.PjFree.relab c σ τ) j) ∧ ∀ τ (i : Fin (Dw.mult τ)), A τ i i = Formalism.L2.PjFree.toC (t (some ⟨τ, i⟩) : CAt σ) := by
  classical
  intro E _ _ _ H Dw l Xo c σ r U _ hU ρ ν k k' x x' y' t hM hB
  obtain ⟨-, -, -, -, -, g, e, F, ik, φ, hEF, hpt⟩ := hU
  obtain ⟨P, hP, p, hPx, hv, -⟩ := hpt k x
  obtain ⟨P', hP', p', hPx', hv', -⟩ := hpt k' x'
  obtain ⟨gam, h, hiso, hh, hex⟩ := exists_isometry_of_sabMap F ν p p'
    (by rw [← hPx, ← hPx', ← hB.1]; exact hM.1.symm)
  choose cf hcf1 hcf2 hcf3 using hB.2.1
  have hcol : ∀ τ i, h.toLinearMap (Pi.single (e.symm ⟨τ, i⟩) 1) =
      (∑ j, (show ℂ from cf τ i j) • (Pi.single (e.symm ⟨τ, j⟩) 1 : Fin g → ℂ)) := by
    intro τ i
    have d1 := (DerLin.isCombAt_iff_isDerivAt0 E H Dw l Xo _ g _ F _ P' p' _ ((U.un k' x').u τ) _ (hv' τ) (cf τ i)
      (y'.u τ i)).1 (hPx' ▸ hcf3 τ i)
    have d0 := FibreDeriv.isDerivAt0_comp (hv τ i) ν.φ
    simp only [← hex] at d0
    have d2 := (ExpChain.isDerivAt0_comp_linear _ (ExpChain.isHolTo_ex F _ P' p') h.toLinearMap _ _).1 d0
    have tn := isDerivAt0_ex_isTanAt E H Dw l Xo _ g _ F _ P' p'
    rw [hM.2.1] at d1
    exact (tn.2.2 _ (tn.1 _ _ d2)).unique d2 d1
  refine ⟨(φ k).symm ≪≫ₗ gam ≪≫ₗ φ k',
    fun τ i j => if hij : i < Dw.mult τ ∧ j < Dw.mult τ then
      Formalism.L2.PjFree.toC (cf τ ⟨j, hij.2⟩ ⟨i, hij.1⟩) else 0, fun u v => ?_, fun τ i j hji => ?_,
    fun τ i hi v => ?_, fun τ i => ?_⟩
  · obtain ⟨u, rfl⟩ := (φ k).surjective u
    obtain ⟨v, rfl⟩ := (φ k).surjective v
    simp only [LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply]
    rw [← hEF, ← hEF, hiso]
  · beta_reduce
    split_ifs with hij
    · exact hcf2 τ _ _ hji
    · rfl
  · obtain ⟨v, rfl⟩ := (φ k).surjective v
    simp only [LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply]
    have a1 := hP' (gam v) (e.symm ⟨τ, ⟨i, hi⟩⟩)
    rw [Equiv.apply_symm_apply] at a1
    rw [← a1, hh, Finset.sum_range]
    refine (apply_of_cols e h.toLinearMap (fun τ i j => cf τ i j) hcol (P v) τ ⟨i, hi⟩).trans
      (Finset.sum_congr rfl fun j _ => ?_)
    rw [hP, Equiv.apply_symm_apply, dif_pos ⟨hi, j.2⟩]
    rfl
  · beta_reduce
    rw [dif_pos ⟨i.2, i.2⟩]
    exact congrArg _ (hcf1 τ i)

end GlobalTheory.LevelCusp
