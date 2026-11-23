import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PeriodComparison
import Development.AbelianVarietyTheory.Definitions.Divisors.JetAnalytic
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrysToDRBijective
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsCrystalPairing
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueDetGen
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDetGenHolUnif

set_option autoImplicit false

noncomputable section

open GlobalTheory.LatVal GlobalTheory.LatJet
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.CMVal
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.LatJet

theorem exists_detGen_coeff_algebraic : ∀ (E : Type) [Field E] [NumberField E] (I : Type) [Fintype I] (φ : I → E →+* ℂ) (L : Set E) (𝔠 : FracId (FR E))
    (X₀ : Obj (FR E) 𝔠 (Sp Qb)) (X : Obj (FR E) 𝔠 (Sp ℂ)) (p : X.A.left ⟶ X₀.A.left) (U : Unif φ L 0 X)
    (v₀ : I → X₀.Lie) (v : I → X.Lie) (a : I → ℂ),
    X.IsPullBy X₀ (spMap (algebraMap Qb ℂ)) p →
    (∀ i, Obj.LieCorr (algebraMap Qb ℂ) p (v₀ i) (v i) ∧ U.u.IsDiff (Pi.single (U.e.symm i) (a i)) (v i).hom) →
    ∃ (δ₀ : X₀.DetGen) (δ : X.DetGen) (C : ℂ), Obj.DetCorr (algebraMap Qb ℂ) p δ₀.1 δ.1 ∧ U.IsDet δ.1 C ∧
      IsAlgebraic ℚ (C * ∏ i, a i) := by
  intro E _ _ I _ φ L 𝔠 X₀ X p U v₀ v a hpb hv
  haveI := Obj.invertible_detOmega X₀
  obtain ⟨d, -, hd⟩ := finrank_eq_one_iff'.1 (Module.Invertible.finrank_eq_one Qb X₀.DetOmega)
  let δ₀ : X₀.DetGen := ⟨d, eq_top_iff.2 fun w _ ↦ Submodule.mem_span_singleton.2 (hd w)⟩
  obtain ⟨δ, hδ, -⟩ := hpb.existsUnique_detGen (algebraMap Qb ℂ) δ₀
  obtain ⟨δ₁, hδ₁⟩ := Obj.exists_detGen_holUnif (FR E) 𝔠 X _ U.u 1 one_ne_zero
  have hmem : δ.1 ∈ Submodule.span ℂ {δ₁.1} := by rw [δ₁.2]; exact Submodule.mem_top
  obtain ⟨C, hC⟩ := Submodule.mem_span_singleton.1 hmem
  have hdet : U.IsDet δ.1 C := fun w W hW ↦ by
    rw [← hC, AlternatingMap.smul_apply, hδ₁ w W hW, smul_eq_mul, _root_.one_mul]
  refine ⟨δ₀, δ, C, hδ, hdet, ?_⟩
  have hW : ∀ j, U.u.IsDiff ((Matrix.diagonal fun j ↦ a (U.e j)) j) (v (U.e j)).hom := fun j ↦ by
    have h := (hv (U.e j)).2
    rw [Equiv.symm_apply_apply] at h
    convert h using 1
    ext k
    simp [Matrix.diagonal_apply, Pi.single_apply, eq_comm]
  have h1 := hdet (fun j ↦ v (U.e j)) _ hW
  have h2 := hδ (fun j ↦ v₀ (U.e j)) (fun j ↦ v (U.e j)) fun j ↦ (hv (U.e j)).1
  rw [Matrix.det_diagonal, Equiv.prod_comp U.e a] at h1
  rw [← h1, h2]
  exact (mem_algebraicClosure_iff.1 (δ₀.1 fun j ↦ v₀ (U.e j)).2)

end GlobalTheory.LatJet
