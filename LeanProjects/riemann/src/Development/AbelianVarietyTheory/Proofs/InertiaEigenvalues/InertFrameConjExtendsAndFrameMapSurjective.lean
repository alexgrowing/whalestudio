import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.FinIso
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingSpecNormalisedCharacterEq
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RecProdRecSatakeLL
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StandardCosocleGL
import Formalism.SharpRestriction.LevelLetterCocycles.SphericalInertData
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FixedPlaceUnitaryLocalPointsEquivLocalUnitaryGro
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DefiniteUnitarySphericalIffHasSatakeInert
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SplitPlaceUnitaryLocalPointsEquivGL
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host GlobalTheory.HeightCounting NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.FormDict GlobalTheory.DefiniteBC
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
noncomputable section

namespace GlobalTheory.InertFrameConj

open Matrix

theorem cT_diagonal_mul {K : Type} [Field K] {n : ℕ} (σ : K →+* K) (d : Fin n → K) :
    Formalism.UG.cT σ (diagonal d) * diagonal d = diagonal fun j => σ (d j) * d j := by
  unfold Formalism.UG.cT
  rw [diagonal_map (map_zero σ), diagonal_transpose, diagonal_mul_diagonal]

def dg {K : Type} [Field K] {n : ℕ} (i : Fin n) (t : Kˣ) : GL (Fin n) K where
  val := diagonal (Function.update 1 i (t : K))
  inv := diagonal (Function.update 1 i ((t⁻¹ : Kˣ) : K))
  val_inv := by
    rw [diagonal_mul_diagonal, ← diagonal_one]
    congr 1
    ext j
    by_cases h : j = i
    · subst h; simp
    · simp [Function.update_of_ne h]
  inv_val := by
    rw [diagonal_mul_diagonal, ← diagonal_one]
    congr 1
    ext j
    by_cases h : j = i
    · subst h; simp
    · simp [Function.update_of_ne h]

theorem cT_dg {K : Type} [Field K] {n : ℕ} (σ : K →+* K) (i : Fin n) (t : Kˣ) :
    Formalism.UG.cT σ (dg i t).val * (dg i t).val = diagonal (Function.update 1 i (σ t * t)) := by
  change Formalism.UG.cT σ (diagonal _) * diagonal _ = _
  rw [cT_diagonal_mul]
  congr 1
  ext j
  by_cases h : j = i
  · subst h; simp
  · simp [Function.update_of_ne h]

theorem eq_of_cT_dg {K : Type} [Field K] {n : ℕ} (σ : K →+* K) (i : Fin n) (t : Kˣ)
    (h : Formalism.UG.cT σ (dg i t).val * (dg i t).val = 1) : σ t * t = 1 := by
  have := congrFun (congrFun h i) i
  rw [cT_dg] at this
  simpa using this

theorem dg_mem {K : Type} [Field K] {n : ℕ} (σ : K →+* K) (i : Fin n) (t : Kˣ) (h : σ t * t = 1) :
    dg i t ∈ Formalism.UG.UJ σ (1 : Matrix (Fin n) (Fin n) K) := by
  show Formalism.UG.cT σ (dg i t).val * 1 * (dg i t).val = 1
  rw [Matrix.mul_one, cT_dg, h, ← diagonal_one]
  congr 1
  ext j
  by_cases hj : j = i
  · subst hj; simp
  · simp [Function.update_of_ne hj]

theorem cT_mul_self_of_frame {K : Type} [Field K] {n : ℕ} (σ : K →+* K) (b g : GL (Fin n) K) (J : Matrix (Fin n) (Fin n) K)
    (hb : Formalism.UG.cT σ b.val * b.val = J)
    (h : Formalism.UG.cT σ (b⁻¹ * g * b).val * J * (b⁻¹ * g * b).val = J) : Formalism.UG.cT σ g.val * g.val = 1 := by
  have e1 : Formalism.UG.cT σ (b⁻¹).val * Formalism.UG.cT σ b.val = 1 := by
    rw [← Formalism.UG.cT_mul, Units.mul_inv, Formalism.UG.cT_one]
  have e2 : b.val * (b⁻¹).val = 1 := Units.mul_inv b
  subst hb
  simp only [Units.val_mul, Formalism.UG.cT_mul] at h
  have h' : Formalism.UG.cT σ b.val * (Formalism.UG.cT σ g.val * g.val) * b.val = Formalism.UG.cT σ b.val * b.val := by
    rw [← h]
    simp only [Matrix.mul_assoc]
    congr 2
    rw [← Matrix.mul_assoc (Formalism.UG.cT σ (b⁻¹).val), e1, Matrix.one_mul, ← Matrix.mul_assoc b.val, e2, Matrix.one_mul]
  have h'' := congrArg (fun M => Formalism.UG.cT σ (b⁻¹).val * M * (b⁻¹).val) h'
  simp only [Matrix.mul_assoc] at h''
  rwa [e2, Matrix.mul_one, ← Matrix.mul_assoc (Formalism.UG.cT σ (b⁻¹).val), e1, Matrix.one_mul, ← Matrix.mul_assoc,
    e1, Matrix.one_mul] at h''

theorem eq_of_norms {K : Type} [Field K] (σ : K →+* K) (Y Y' : K) (hne : Y ≠ Y') (h1 : σ Y * Y = σ Y' * Y')
    (h2 : σ (Y + 1) * (Y + 1) = σ (Y' + 1) * (Y' + 1)) : σ Y = Y' := by
  rw [map_add, map_add, map_one] at h2
  have h3 : σ Y + Y = σ Y' + Y' := by linear_combination h2 - h1
  have h4 : σ Y * (Y - Y') = Y' * (Y - Y') := by linear_combination h1 - Y' * h3
  exact mul_right_cancel₀ (sub_ne_zero.2 hne) h4

end GlobalTheory.InertFrameConj

open GlobalTheory.InertFrameConj GlobalTheory.SplitPts in

theorem GlobalTheory.InertFrameConj.conj_and_surjective : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ), 0 < n → ∀ (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) (w : HeightOneSpectrum (𝓞 L)), NG.OverPl w v → ∀ (Dv : InertDatum L n v w) (b : GL (Fin n) (w.adicCompletion L)), b ∈ GlobalTheory.LFun.KGL w n → Formalism.UG.cT Dv.σw b.val * b.val = Formalism.UG.antiJ (w.adicCompletion L) n → ∀ p : locU n w →* Formalism.UG.GU Dv.σw n, (∀ x, (p x).val = b⁻¹ * cLoc w x.val * b) → (∀ x : L, Dv.σw (algebraMap L _ x) = algebraMap L _ (IsCMField.complexConj L x)) ∧ Function.Surjective p := by
  intro L _ _ _ n hn v w _ Dv b _ hb p hp
  have i0 : Fin n := ⟨0, hn⟩

  have hu : ∀ x : locU n w, Formalism.UG.cT Dv.σw (cLoc w x.1).val * (cLoc w x.1).val = 1 := by
    intro x
    refine cT_mul_self_of_frame Dv.σw b (cLoc w x.1) _ hb ?_
    have h : Formalism.UG.cT Dv.σw (p x).val.val * Formalism.UG.antiJ (w.adicCompletion L) n * (p x).val.val =
        Formalism.UG.antiJ (w.adicCompletion L) n := (p x).2
    rw [hp x] at h
    exact h
  have hdg : ∀ (t : (w.adicCompletion L)ˣ) (x : locU n w), cLoc w x.1 = dg i0 t → Dv.σw t * t = 1 := by
    intro t x hx
    have := hu x
    rw [hx] at this
    exact eq_of_cT_dg Dv.σw i0 t this

  have hinj := (algebraMap L (w.adicCompletion L)).injective
  by_cases hsp : IsSplitAt w
  ·
    exfalso
    have h2 : (2 : w.adicCompletion L) ≠ 0 := by
      rw [show (2 : w.adicCompletion L) = algebraMap L _ 2 from (map_ofNat _ 2).symm]
      exact (map_ne_zero _).2 two_ne_zero
    have h := hdg (Units.mk0 2 h2) (locPt hsp (dg i0 (Units.mk0 2 h2))) (cLoc_locPt hsp _)
    rw [Units.val_mk0, map_ofNat] at h
    have h4 : algebraMap L (w.adicCompletion L) 4 = algebraMap L _ 1 := by
      rw [map_one, ← h, map_ofNat]; norm_num
    have := hinj h4
    norm_num at this

  have hcs : conjSrc (conjE L) w = w := by
    by_contra hne
    exact hsp ⟨_, hne, (GlobalTheory.Mem.Chr.under_eq_iff_conjPl (IsCMField.complexConj L)
      (Algebra.IsQuadraticExtension.finrank_eq_two _ _) (IsCMField.complexConj_ne_one L) w _).2
      (Or.inr (conjPl_self_conjSrc w))⟩
  obtain ⟨s, hs, hsv⟩ : ∃ s : w.adicCompletion L →+* w.adicCompletion L,
      (∀ k : L, s (algebraMap L _ k) = algebraMap L _ (IsCMField.complexConj L k)) ∧
        ∀ x, Valued.v (s x) = Valued.v x := by
    have key : ∀ (u : HeightOneSpectrum (𝓞 L)) (_ : u = w) (f : u.adicCompletion L →+* w.adicCompletion L),
        (∀ k : L, f (algebraMap L _ k) = algebraMap L _ (conjE L k)) → (∀ x, Valued.v (f x) = Valued.v x) →
        ∃ s : w.adicCompletion L →+* w.adicCompletion L,
          (∀ k : L, s (algebraMap L _ k) = algebraMap L _ (IsCMField.complexConj L k)) ∧
            ∀ x, Valued.v (s x) = Valued.v x := by
      rintro u rfl f h1 h2
      exact ⟨f, h1, h2⟩
    exact key _ hcs _ (conjLoc_spec (conjE L) w).2.1 (conjLoc_spec (conjE L) w).2.2
  obtain ⟨e, he⟩ := GlobalTheory.DefU.Inert.locU_equiv L n w s hs hsv

  have hpair : ∀ y : L, y ≠ IsCMField.complexConj L y →
      Dv.σw (algebraMap L _ y) * algebraMap L _ y =
        Dv.σw (algebraMap L _ (IsCMField.complexConj L y)) * algebraMap L _ (IsCMField.complexConj L y) := by
    intro y hy
    have hy0 : y ≠ 0 := fun h => hy (by rw [h, map_zero])
    have hc0 : IsCMField.complexConj L y ≠ 0 := fun h => hy0 (by
      simpa using congrArg (IsCMField.complexConj L) h)
    have hY : algebraMap L (w.adicCompletion L) y ≠ 0 := (map_ne_zero _).2 hy0
    have hY' : algebraMap L (w.adicCompletion L) (IsCMField.complexConj L y) ≠ 0 := (map_ne_zero _).2 hc0
    set z : (w.adicCompletion L)ˣ := Units.mk0 (algebraMap L _ y / algebraMap L _ (IsCMField.complexConj L y))
      (div_ne_zero hY hY') with hz
    have hsz : s z * z = 1 := by
      rw [hz, Units.val_mk0, map_div₀, hs, hs, IsCMField.complexConj_apply_apply]
      field_simp
    have hmem := dg_mem s i0 z hsz
    have h := hdg z (e.symm ⟨dg i0 z, hmem⟩) (by rw [← he, e.apply_symm_apply])
    rw [hz, Units.val_mk0, map_div₀] at h
    have hσ0 : Dv.σw (algebraMap L _ (IsCMField.complexConj L y)) ≠ 0 := (map_ne_zero _).2 hY'
    field_simp at h
    linear_combination h
  have hext : ∀ x : L, Dv.σw (algebraMap L _ x) = algebraMap L _ (IsCMField.complexConj L x) := by
    have hone : ∀ y : L, y ≠ IsCMField.complexConj L y →
        Dv.σw (algebraMap L _ y) = algebraMap L _ (IsCMField.complexConj L y) := by
      intro y hy
      refine eq_of_norms Dv.σw _ _ (fun h => hy (hinj h)) (hpair y hy) ?_
      have hy1 : y + 1 ≠ IsCMField.complexConj L (y + 1) := by
        rw [map_add, map_one]; exact fun h => hy (add_right_cancel h)
      have := hpair (y + 1) hy1
      simpa only [map_add, map_one] using this
    obtain ⟨t, ht⟩ : ∃ t : L, t ≠ IsCMField.complexConj L t := by
      by_contra hc
      push_neg at hc
      exact IsCMField.complexConj_ne_one L (AlgEquiv.ext fun t => (hc t).symm)
    intro x
    by_cases hx : x = IsCMField.complexConj L x
    · have hxt : x + t ≠ IsCMField.complexConj L (x + t) := by
        rw [map_add, ← hx]; exact fun h => ht (add_left_cancel h)
      have h1 := hone _ hxt
      rw [map_add, map_add, map_add, map_add, hone t ht, ← hx] at h1
      rw [← hx]
      exact add_right_cancel h1
    · exact hone x hx
  refine ⟨hext, ?_⟩
  obtain ⟨e', he'⟩ := GlobalTheory.DefU.Inert.locU_equiv L n w Dv.σw hext Dv.unram.2.1
  have hb1 : Formalism.UG.cT Dv.σw b.1 * 1 * b.1 = Formalism.UG.antiJ _ n := by rwa [Matrix.mul_one]
  intro g
  let P := e'.trans (GlobalTheory.InertSatake.conjEquiv Dv.σw b hb1)
  have hP : ((P (P.symm g) : Formalism.UG.GU Dv.σw n) : GL (Fin n) (w.adicCompletion L)) =
      b⁻¹ * cLoc w (P.symm g).1 * b := by
    change b⁻¹ * (e' _ : GL (Fin n) _) * b = _
    rw [he']
  refine ⟨P.symm g, Subtype.ext ?_⟩
  rw [hp, ← hP, P.apply_symm_apply]

end
