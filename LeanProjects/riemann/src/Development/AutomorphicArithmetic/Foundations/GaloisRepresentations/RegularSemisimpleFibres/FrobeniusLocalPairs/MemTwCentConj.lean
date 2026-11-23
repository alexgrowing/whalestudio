import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.FrobeniusLocalPairs.LiftFactorization
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.OrbitalIntegrals.BrMain
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteTwistedClassesCharpoly

noncomputable section

open MeasureTheory ValuativeRel Matrix GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets
open scoped Classical ENNReal

namespace UpperTheory.Gal.InertialTypesAlt.L

open PositivityTheory.Rg.Tf.Loc UpperTheory.V.Z.Tf.Orb

private theorem norm_eq {k E : Type} [Field k] [Field E] [Algebra k E] (σ : E ≃ₐ[k] E) (n : ℕ)
    (δ : GL (Fin n) E) : GlobalTheory.LBC.norm k σ δ = normGL σ δ := by
  unfold GlobalTheory.LBC.norm normGL twNorm
  congr 1
  apply List.ext_getElem
  · simp
  · intro i h1 h2
    simp only [List.getElem_ofFn, List.getElem_map, List.getElem_range]
    show (sigmaGL (σ ^ i) : Monoid.End (GL (Fin n) E)) δ = _
    rw [sigmaGL_pow]

private theorem charpoly_incl {k E : Type} [Field k] [Field E] [Algebra k E] {n : ℕ}
    (γ : GL (Fin n) k) :
    ((incl γ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E).charpoly =
      (γ : Matrix (Fin n) (Fin n) k).charpoly.map (algebraMap k E) := by
  show ((GeneralLinearGroup.map (algebraMap k E) γ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E).charpoly = _
  rw [← Matrix.charpoly_map]
  rfl

private theorem twConj_conj {G : Type} [Group G] (θ : Monoid.End G) (h x δ : G) :
    twConj θ (h⁻¹ * x * h) (twConj θ h δ) = h⁻¹ * twConj θ x δ * θ h := by
  unfold twConj
  simp only [map_mul, map_inv, _root_.mul_inv_rev, inv_inv]
  group

private theorem mem_twCent_conj {G : Type} [Group G] (θ : Monoid.End G) (h x δ : G) :
    x ∈ twCent θ δ ↔ h⁻¹ * x * h ∈ twCent θ (twConj θ h δ) := by
  show twConj θ x δ = δ ↔ twConj θ (h⁻¹ * x * h) (twConj θ h δ) = twConj θ h δ
  rw [twConj_conj]
  unfold twConj
  constructor
  · intro hx
    rw [hx]
  · intro hx
    have := congrArg (fun y => h * y * (θ h)⁻¹) hx
    simpa [mul_assoc] using this

private theorem twCent_eq {G : Type} [Group G] (θ : Monoid.End G) (δ : G) :
    twCent θ δ = GlobalTheory.BCT.twCent θ δ := by
  ext x
  show twConj θ x δ = δ ↔ x * δ = δ * θ x
  unfold twConj
  constructor
  · intro hx
    calc x * δ = x * (x⁻¹ * δ * θ x) := by rw [hx]
      _ = δ * θ x := by group
  · intro hx
    calc x⁻¹ * δ * θ x = x⁻¹ * (δ * θ x) := by group
      _ = x⁻¹ * (x * δ) := by rw [hx]
      _ = δ := by group

theorem dict : Dict := by
  intro k E _ _ _ _ _ _ _ _ _ _ _ _ _ σ hgen n
  have hcp : ∀ γ : GL (Fin n) k,
      ((incl γ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E).charpoly =
        (γ : Matrix (Fin n) (Fin n) k).charpoly.map (algebraMap k E) := fun γ => charpoly_incl γ
  have hconj : ∀ (h a : GL (Fin n) E),
      ((h * a * h⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E).charpoly =
        (a : Matrix (Fin n) (Fin n) E).charpoly := by
    intro h a
    rw [Units.val_mul, Units.val_mul, Matrix.coe_units_inv]
    exact Matrix.charpoly_units_conj h a
  have hpow : sigmaGL σ ^ Module.finrank k E = (1 : Monoid.End (GL (Fin n) E)) := by
    rw [← sigmaGL_pow, ← IsGalois.card_aut_eq_finrank, pow_card_eq_one', sigmaGL_one]
  refine ⟨rfl, fun δ => norm_eq σ n δ, fun δ => twCent_eq _ δ, ?_, ?_, ?_⟩
  · intro γ
    ext x
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact Iff.rfl
  · intro δ h γ hreg hN
    have heq : (γ : Matrix (Fin n) (Fin n) k).charpoly.map (algebraMap k E) =
        ((normGL σ δ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E).charpoly := by
      rw [hN, hconj, hcp]
    have hγ : IsRegSemisimple γ := by
      have hs : ((normGL σ δ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E).charpoly.Separable := hreg
      rw [← heq] at hs
      exact (Polynomial.separable_map _).mp hs
    refine ⟨hγ, heq, ?_⟩
    intro x
    have hN' : normGL σ (twConj (sigmaGL σ) h δ) = incl γ := by
      unfold normGL
      rw [twNorm_twConj_of_pow_eq_one _ hpow]
      change h⁻¹ * normGL σ δ * h = incl γ
      rw [hN]
      group
    obtain ⟨_, hc⟩ := twCentImg_holds k E σ hgen n _ γ hγ hN'
    rw [mem_twCent_conj (sigmaGL σ) h x δ, hc, Subgroup.mem_map]
    constructor
    · rintro ⟨t, ht, hx⟩
      exact ⟨t, ht, hx.symm⟩
    · rintro ⟨t, ht, hx⟩
      exact ⟨t, ht, hx.symm⟩
  · intro δ γ hγ heq
    have hs : ((incl γ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E).charpoly.Separable := by
      rw [hcp]
      exact (Polynomial.separable_map _).mpr hγ
    obtain ⟨g, hg⟩ := GlobalTheory.BCT.ClsFin.conj_of_charpoly (incl γ) (normGL σ δ) hs (by rw [hcp, heq])
    exact ⟨g⁻¹, by rw [hg, inv_inv]⟩

end UpperTheory.Gal.InertialTypesAlt.L
