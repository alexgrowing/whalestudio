import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingSpecNormalisedCharacterEq
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SplitPlaceLocalComponentExistsUniqueClass
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsComplEquiv
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SplitPlaceCompletionEquivUnique
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsLevelCharacterAtConjugateSplitPlace
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.EqOrIsConjPlaceOfOverSplitPlace
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.ConjLocComp

open GlobalTheory.TypeTame

theorem map_invTranspose {A B : Type} [CommRing A] [CommRing B] (n : ℕ) (f : A →+* B) (g : GL (Fin n) A) :
    Matrix.GeneralLinearGroup.map f (invTranspose n g) = invTranspose n (Matrix.GeneralLinearGroup.map f g) := by
  apply Units.ext
  rw [invTranspose_val, ← map_inv]
  rfl

theorem exists_conj {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ} {W : Type} [AddCommGroup W] [Module ℂ W]
    (S : Submodule ℂ (GAf L n → W)) (s : SplitPlace L) (σ : GlobalTheory.SmGL.IrrRep (GL (Fin n) (s.w.adicCompletion L)))
    (hσ : IsLocS S s σ) :
    ∃ (κ : s.w.adicCompletion L ≃+* (conjSP s).w.adicCompletion L)
      (σ' : GlobalTheory.SmGL.IrrRep (GL (Fin n) ((conjSP s).w.adicCompletion L))) (e : σ.V ≃ₗ[ℂ] σ'.V),
      Continuous κ ∧ (∀ x : L, κ (algebraMap L _ x) = algebraMap L _ (IsCMField.complexConj L x)) ∧
      IsLocS S (conjSP s) σ' ∧
      ∀ g a, e (σ.ρ (invTranspose n g) a) = σ'.ρ (Matrix.GeneralLinearGroup.map κ.toRingHom g) (e a) := by
  obtain ⟨i, T, hi, hiL, hTi, hTm, hTe⟩ := hσ
  obtain ⟨i₀, hi₀, hi₀', hi₀L⟩ := GlobalTheory.SplitComplHomeo.exists_complEquiv L s
  obtain rfl := GlobalTheory.splitPlace_completion_equiv_unique L s i₀ i hi₀ hi hi₀L hiL
  obtain ⟨i', hi', hi'', hi'L⟩ := GlobalTheory.SplitComplHomeo.exists_complEquiv L (conjSP s)
  let j : s.v.adicCompletion (maximalRealSubfield L) ≃+* (conjSP s).w.adicCompletion L := i'
  let κ : s.w.adicCompletion L ≃+* (conjSP s).w.adicCompletion L := i₀.symm.trans j
  have hκ : Continuous κ := hi'.comp hi₀'
  have hκ' : Continuous κ.symm := hi₀.comp hi''
  let ψ : GL (Fin n) ((conjSP s).w.adicCompletion L) →* GL (Fin n) (s.w.adicCompletion L) :=
    (invTranspose n).comp (Matrix.GeneralLinearGroup.map κ.symm.toRingHom)
  have hψc : Continuous ψ :=
    (continuous_invTranspose n).comp (Continuous.units_map _ (continuous_id.matrix_map hκ'))
  have hψκ : ∀ g, ψ (Matrix.GeneralLinearGroup.map κ.toRingHom g) = invTranspose n g := fun g =>
    congrArg (invTranspose n) (GlobalTheory.LocCompSplit.gl_map_symm_map κ g)
  have hψs : Function.Surjective ψ := fun g =>
    ⟨Matrix.GeneralLinearGroup.map κ.toRingHom (invTranspose n g), by rw [hψκ, invTranspose_invTranspose]⟩
  have hj : ∀ g : GL (Fin n) (s.v.adicCompletion (maximalRealSubfield L)),
      Matrix.GeneralLinearGroup.map j.toRingHom g =
        Matrix.GeneralLinearGroup.map κ.toRingHom (Matrix.GeneralLinearGroup.map i₀.toRingHom g) := fun g => by
    refine Units.ext (Matrix.ext fun a b => ?_)
    show j (g.val a b) = j (i₀.symm (i₀ (g.val a b)))
    rw [RingEquiv.symm_apply_apply]
  let σ' : GlobalTheory.SmGL.IrrRep (GL (Fin n) ((conjSP s).w.adicCompletion L)) :=
    ⟨σ.V, σ.ρ.comp ψ, fun v => (σ.smooth v).preimage hψc,
      GlobalTheory.LocCompSplit.isIrreducible_comp_of_surjective σ.ρ ψ hψs σ.irr⟩
  refine ⟨κ, σ', LinearEquiv.refl ℂ σ.V, hκ, fun x => ?_, ⟨i', T, hi', hi'L, hTi, hTm, fun x hx a => ?_⟩, fun g a => ?_⟩
  · rw [← hi'L, conjSP_i, IsCMField.complexConj_apply_apply, ← hiL]
    show j (i₀.symm (i₀ (s.i x))) = j (s.i x)
    rw [RingEquiv.symm_apply_apply]
  · have h1 : ψ (Matrix.GeneralLinearGroup.map j.toRingHom (invTranspose n (s.loc n x))) =
        Matrix.GeneralLinearGroup.map i₀.toRingHom (s.loc n x) := by
      rw [hj, hψκ, map_invTranspose, invTranspose_invTranspose]
    have h2 := hTe x hx a
    rw [← h1, ← conjSP_loc] at h2
    exact h2
  · show σ.ρ (invTranspose n g) a = σ.ρ (ψ (Matrix.GeneralLinearGroup.map κ.toRingHom g)) a
    rw [hψκ]

theorem exists_isLocS_conjSP : ∀ (D : D7) (n : ℕ) (π : NG.AutRep D.host.E n) (s : SplitPlace D.host.E)
    (σ : GlobalTheory.SmGL.IrrRep (GL (Fin n) (s.w.adicCompletion D.host.E))), IsLocS π.S s σ →
    ∃ (κ : s.w.adicCompletion D.host.E ≃+* (GlobalTheory.TypeTame.conjSP s).w.adicCompletion D.host.E)
      (σ' : GlobalTheory.SmGL.IrrRep (GL (Fin n) ((GlobalTheory.TypeTame.conjSP s).w.adicCompletion D.host.E))) (e : σ.V ≃ₗ[ℂ] σ'.V),
      Continuous κ ∧ (∀ x : D.host.E, κ (algebraMap D.host.E _ x) = algebraMap D.host.E _ (D.host.conj x)) ∧
      IsLocS π.S (GlobalTheory.TypeTame.conjSP s) σ' ∧
      ∀ g a, e (σ.ρ (GlobalTheory.TypeTame.invTranspose n g) a) = σ'.ρ (Matrix.GeneralLinearGroup.map κ.toRingHom g) (e a) := by
  intro D n π s σ hσ
  obtain ⟨κ, σ', e, h1, h2, h3, h4⟩ := exists_conj π.S s σ hσ
  exact ⟨κ, σ', e, h1, fun x => by rw [h2, GlobalTheory.SplitPlaceOver.host_conj_eq'], h3, h4⟩

end GlobalTheory.ConjLocComp
