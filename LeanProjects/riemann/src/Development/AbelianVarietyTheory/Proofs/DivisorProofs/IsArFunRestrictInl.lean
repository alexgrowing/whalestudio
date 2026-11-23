import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsFlagBundleRankOne
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.RegularAlteration
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NontrivialIsomClassInt
import Development.AbelianVarietyTheory.Definitions.Divisors.GenericPointAsIdeal
open NumberField MvPolynomial Filter Topology Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovTest GlobalTheory.Published
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt
open scoped Classical

namespace GlobalTheory.FlagCmp

theorem isArFun_restrict_inl (hI : Published.ArIso) {k : Type} [CommRing k] {X : Scheme.{0}} [IsIntegral X] {p : X ⟶ Sp k}
    {D : ℕ} (hX : IsArithVar p D) {ι κ : Type} [Fintype ι] [Fintype κ] (L : ι → HermLB p) (M : κ → HermLB p)
    {Φ : MvPolynomial ι ℝ →ₗ[ℝ] ℝ} {Ψ : MvPolynomial (ι ⊕ κ) ℝ →ₗ[ℝ] ℝ} (hΦ : IsArFun L D Φ)
    (hΨ : IsArFun (Sum.elim L M) D Ψ) (P : MvPolynomial ι ℝ) : Ψ (rename Sum.inl P) = Φ P := by
  have iso : ∀ j, (comb (Sum.elim L M) (fun i => if i = Sum.inl j then (1 : ℤ) else 0)).Isometric (L j) := fun j => by
    refine HermLB.icls_eq_iff.1 ?_
    rw [GlobalTheory.ArInt.icls_comb, Fintype.sum_sum_type]
    simp [ite_smul]
  have h := ((hI k X p D hX).2 (ι ⊕ κ) (Sum.elim L M) Ψ hΨ).2.2 ι L _ iso
  have e := GlobalTheory.ArInt.Model.isArFun_unique hX hΦ h
  rw [e]
  change _ = Ψ (aeval _ P)
  congr 1
  have : (aeval fun j => lin fun i : ι ⊕ κ => (((if i = Sum.inl j then (1 : ℤ) else 0 : ℤ)) : ℝ)) =
      (rename Sum.inl : MvPolynomial ι ℝ →ₐ[ℝ] MvPolynomial (ι ⊕ κ) ℝ) := by
    refine MvPolynomial.algHom_ext fun j => ?_
    simp [lin, apply_ite]
  rw [this]

end GlobalTheory.FlagCmp
