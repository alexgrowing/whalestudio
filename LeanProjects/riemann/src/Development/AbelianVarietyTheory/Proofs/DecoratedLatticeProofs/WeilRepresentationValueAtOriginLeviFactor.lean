import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsQuasiFam
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ThetaAbsoluteSum
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.TransvectionAction
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.WeilDatumExistence
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.AdjointIsotropicDecomposition
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeilActionLeviOriginEqCharScalarStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AdelicGLCircleCharacterTrivialOnDetOneStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HeckeCharacterEqOneOfTrivialSplitPlacesStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LeviFactorCharactersSplitPlaceStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryAdelicCharacterTrivialRatAndSplit
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf

noncomputable section

namespace GlobalTheory.LeviOrigin

def diagAt {R : Type*} [CommRing R] (ρ : ℕ) (i : Fin ρ) : R →* Matrix (Fin ρ) (Fin ρ) R where
  toFun t := Matrix.diagonal (Function.update (1 : Fin ρ → R) i t)
  map_one' := by
    have h1 : Function.update (1 : Fin ρ → R) i 1 = 1 := by
      funext j; by_cases h : j = i
      · subst h; simp
      · simp [Function.update_of_ne h]
    show Matrix.diagonal (Function.update (1 : Fin ρ → R) i 1) = 1
    rw [h1]; exact Matrix.diagonal_one
  map_mul' s t := by
    rw [Matrix.diagonal_mul_diagonal]
    congr 1
    funext j
    by_cases h : j = i
    · subst h; simp
    · simp [Function.update_of_ne h]

def dgU {R : Type*} [CommRing R] (ρ : ℕ) (i : Fin ρ) : Rˣ →* GL (Fin ρ) R := Units.map (diagAt ρ i)

theorem det_dgU {R : Type*} [CommRing R] (ρ : ℕ) (i : Fin ρ) (t : Rˣ) :
    Matrix.GeneralLinearGroup.det (dgU ρ i t) = t := by
  ext
  rw [Matrix.GeneralLinearGroup.val_det_apply]
  show (Matrix.diagonal (Function.update (1 : Fin ρ → R) i (t : R))).det = t
  rw [Matrix.det_diagonal, Finset.prod_update_of_mem (Finset.mem_univ i)]
  simp

theorem continuous_dgU {R : Type*} [CommRing R] [TopologicalSpace R] (ρ : ℕ) (i : Fin ρ) :
    Continuous (dgU (R := R) ρ i) := by
  apply Continuous.units_map
  show Continuous fun t : R => Matrix.diagonal (Function.update (1 : Fin ρ → R) i t)
  exact Continuous.matrix_diagonal (continuous_const.update i continuous_id)

theorem dgU_map {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) (ρ : ℕ) (i : Fin ρ) (x : Rˣ) :
    dgU ρ i (Units.map f.toMonoidHom x) = Matrix.GeneralLinearGroup.map f (dgU ρ i x) := by
  ext k l
  show Matrix.diagonal (Function.update (1 : Fin ρ → S) i (f x)) k l =
    f (Matrix.diagonal (Function.update (1 : Fin ρ → R) i (x : R)) k l)
  simp only [Matrix.diagonal_apply]
  split_ifs with h
  · subst h
    by_cases h' : k = i
    · subst h'; simp
    · simp [Function.update_of_ne h']
  · simp

theorem dgU_sub_one {R : Type*} [CommRing R] (ρ : ℕ) (i : Fin ρ) (x : Rˣ) (k l : Fin ρ) :
    ((dgU ρ i x).1 - 1) k l = if k = i ∧ l = i then (x : R) - 1 else 0 := by
  show Matrix.diagonal (Function.update (1 : Fin ρ → R) i (x : R)) k l - (1 : Matrix (Fin ρ) (Fin ρ) R) k l = _
  simp only [Matrix.diagonal_apply, Matrix.one_apply]
  by_cases h : k = l
  · subst h
    by_cases h' : k = i
    · subst h'; simp
    · simp [Function.update_of_ne h', h']
  · simp [h]
    intro hk hl; exact absurd (hk.trans hl.symm) h

end GlobalTheory.LeviOrigin

theorem GlobalTheory.LeviOrigin.alpha_eq (D : D7) (ρ : ℕ) (α : GL (Fin ρ) (AE D) →* Circle) (χT : (AE D)ˣ →* Circle)
    (hαc : Continuous α) (hαr : ∀ a : GL (Fin ρ) D.host.E, α (Matrix.GeneralLinearGroup.map (incA D) a) = 1)
    (hα1 : ∀ a : GL (Fin ρ) (AE D), Matrix.GeneralLinearGroup.det a = 1 → α a = 1)
    (hχ : IsHeckeChar D χT)
    (hs : ∀ e, IsSplitIdem D e → ∀ a : GL (Fin ρ) (AE D), (∀ i j, (e + cA D e) * (a.1 - 1) i j = (a.1 - 1) i j) →
      α a = (χT (Matrix.GeneralLinearGroup.det a))⁻¹) :
    ∀ a : GL (Fin ρ) (AE D), α a = (χT (Matrix.GeneralLinearGroup.det a))⁻¹ := by
  rcases Nat.eq_zero_or_pos ρ with h0 | hpos
  · intro a
    have hd : Matrix.GeneralLinearGroup.det a = 1 := by
      ext; rw [Matrix.GeneralLinearGroup.val_det_apply]; subst h0; simp
    rw [hα1 a hd, hd, map_one, inv_one]
  obtain ⟨i0⟩ : Nonempty (Fin ρ) := ⟨⟨0, hpos⟩⟩
  have hhec : IsHeckeChar D (α.comp (GlobalTheory.LeviOrigin.dgU ρ i0) * χT) := by
    refine ⟨?_, ?_⟩
    · exact (hαc.comp (GlobalTheory.LeviOrigin.continuous_dgU ρ i0)).mul hχ.1
    · intro x
      rw [MonoidHom.mul_apply, MonoidHom.comp_apply, hχ.2 x, mul_one, GlobalTheory.LeviOrigin.dgU_map (incA D) ρ i0 x]
      exact hαr _
  have hν := GlobalTheory.T.heckeCharacter_eq_one_of_trivial_splitPlaces D _ hhec (by
    intro e he x hx
    have h2 := hs e he (GlobalTheory.LeviOrigin.dgU ρ i0 x) (by
      intro k l
      rw [GlobalTheory.LeviOrigin.dgU_sub_one]
      split_ifs
      · exact hx
      · exact mul_zero _)
    rw [MonoidHom.mul_apply, MonoidHom.comp_apply, h2, GlobalTheory.LeviOrigin.det_dgU, inv_mul_cancel])
  have hdg : ∀ t, α (GlobalTheory.LeviOrigin.dgU ρ i0 t) = (χT t)⁻¹ := by
    intro t
    have := hν t
    rw [MonoidHom.mul_apply, MonoidHom.comp_apply] at this
    exact eq_inv_of_mul_eq_one_left this
  intro a
  have hb : Matrix.GeneralLinearGroup.det (a * (GlobalTheory.LeviOrigin.dgU ρ i0 (Matrix.GeneralLinearGroup.det a))⁻¹) = 1 := by
    rw [map_mul, map_inv, GlobalTheory.LeviOrigin.det_dgU, mul_inv_cancel]
  have h1 := hα1 _ hb
  have h3 : α a = α (a * (GlobalTheory.LeviOrigin.dgU ρ i0 (Matrix.GeneralLinearGroup.det a))⁻¹) *
      α (GlobalTheory.LeviOrigin.dgU ρ i0 (Matrix.GeneralLinearGroup.det a)) := by
    rw [← map_mul, inv_mul_cancel_right]
  rw [h3, h1, one_mul]
  exact hdg _

theorem GlobalTheory.LeviOrigin.value_at_origin : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S S₀ T : HSp D) (ρ : ℕ) (d : HypDec S S₀ ρ) (χS χT : (AE D)ˣ →* Circle) (om : Om S T) (om₀ : Om S₀ T), IsWeilDatumO ψ S T χS χT om → IsWeilDatumO ψ S₀ T χS χT om₀ → ∀ (μ : Measure (Mx D T.rank ρ)) (𝓕 : Set (Mx D T.rank ρ)), IsCovolOne (ratMx D T.rank ρ) μ 𝓕 → ∀ f, IsThetaFunO ψ S T f → (∀ g, d.mixS T ψ μ 𝓕 (om (d.emb0 g, 1) f) 0 = om₀ (g, 1) (d.mixS T ψ μ 𝓕 (f) 0)) ∧ (∀ a : GL (Fin ρ) (AE D), Matrix.GeneralLinearGroup.det a = 1 → d.mixS T ψ μ 𝓕 (om (d.levi a, 1) f) 0 = d.mixS T ψ μ 𝓕 (f) 0) ∧ ∀ a : GL (Fin ρ) (AE D), d.mixS T ψ μ 𝓕 (om (d.levi a, 1) f) 0 = ((((χT (Matrix.GeneralLinearGroup.det a))⁻¹ : Circle) : ℂ) * (GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule.halfMod T.rank a : ℂ)) • d.mixS T ψ μ 𝓕 (f) 0 := by
  intro D ψ S S₀ T ρ d χS χT om om₀ hW hW₀ μ 𝓕 hμ f hf
  obtain ⟨α, ξ, hαc, hαr, hξc, hξr, hmain⟩ := GlobalTheory.T.weilAction_levi_origin_eq_charScalar D ψ S S₀ T ρ d χS χT om om₀ hW hW₀ μ 𝓕 hμ
  have hsp := GlobalTheory.T.leviFactor_characters_splitPlace D ψ S S₀ T ρ d χS χT om om₀ hW hW₀ μ 𝓕 hμ α ξ hmain

  have hξ : ∀ g, ξ g = 1 :=
    GlobalTheory.SplitCharTrivial.eq_one_of_rat_of_split D S₀ ξ hξc hξr (fun e he => (hsp e he).1)

  have hα1 : ∀ a : GL (Fin ρ) (AE D), Matrix.GeneralLinearGroup.det a = 1 → α a = 1 :=
    GlobalTheory.T.adelic_GL_circle_character_trivial_on_det_one D ρ α hαc
  have hα := GlobalTheory.LeviOrigin.alpha_eq D ρ α χT hαc hαr hα1 hW.hecT (fun e he => (hsp e he).2)
  have hhalf : ∀ a : GL (Fin ρ) (AE D), Matrix.GeneralLinearGroup.det a = 1 →
      GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule.halfMod T.rank a = 1 := by
    intro a ha
    unfold GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule.halfMod
    rw [ha, MonoidHom.map_one (GlobalTheory.Doubling.absE D.host.F D.host.E)]
    simp
  have hom₀ : ∀ x, om₀ (1, 1) x = x := by
    intro x; rw [← Prod.one_eq_mk, map_one, Module.End.one_apply]
  have key : ∀ a, d.mixS T ψ μ 𝓕 (om (d.levi a, 1) f) 0 = ((((χT (Matrix.GeneralLinearGroup.det a))⁻¹ : Circle) : ℂ) * (GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule.halfMod T.rank a : ℂ)) • d.mixS T ψ μ 𝓕 (f) 0 := by
    intro a
    have := hmain a 1 f hf
    rw [map_one, mul_one, hξ 1, hom₀, hα a] at this
    simpa using this
  refine ⟨?_, ?_, key⟩
  · intro g
    have := hmain 1 g f hf
    rw [map_one, one_mul, hξ g, map_one, hhalf 1 (map_one _)] at this
    simpa using this
  · intro a ha
    rw [key a, ha, map_one, inv_one, hhalf a ha]
    simp
