import Mathlib
import Development.AbelianVarietyTheory.Definitions.ThetaValues.LeCovCoeff
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ThExprUniqOfChartIndep2
import Development.AbelianVarietyTheory.Counterexamples.LevelGroupExamples.SectionBaseChangeOfBasis
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ShortThetaValueExistsUniqueNaturalOfLaws
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.AdmissibleColumnsLeAndHarmonicMapCover

open AlgebraicGeometry CategoryTheory NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.FieldBC

namespace GlobalTheory.ClassSumUnique

theorem eq_of_forall_algClosed {K R : Type} [Field K] [CommRing R] [Algebra K R] [IsReduced R] (u v : R)
    (h : ∀ (k : Type) [Field k] [IsAlgClosed k] [Algebra K k] (φ : R →ₐ[K] k), φ u = φ v) : u = v := by
  rw [← sub_eq_zero]
  refine IsNilpotent.eq_zero (nilpotent_iff_mem_prime.2 fun J hJ => ?_)
  let ψ : R →+* AlgebraicClosure J.ResidueField :=
    (algebraMap J.ResidueField (AlgebraicClosure J.ResidueField)).comp (algebraMap R J.ResidueField)
  letI : Algebra K (AlgebraicClosure J.ResidueField) := (ψ.comp (algebraMap K R)).toAlgebra
  have e : ψ u = ψ v := h (AlgebraicClosure J.ResidueField) { ψ with commutes' := fun _ => rfl }
  have e' : algebraMap R J.ResidueField u = algebraMap R J.ResidueField v :=
    (algebraMap J.ResidueField (AlgebraicClosure J.ResidueField)).injective e
  rw [← Ideal.algebraMap_residueField_eq_zero, map_sub, e', sub_self]

theorem sec_eq_of_geometric {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
    {Xo : Moduli Dw l} {c : Coeff l} {a : (E →+* ℂ) × ℕ → ℕ} {m : ℕ} {f f' : Rul Xo c} (hf : f ∈ sec Xo c a m)
    (hf' : f' ∈ sec Xo c a m)
    (h : ∀ (k : Type) [Field k] [IsAlgClosed k] [Algebra c.F k] (y : FrPt Xo c k), evR Xo c f y = evR Xo c f' y) :
    f = f' := by
  have hS := GlobalTheory.abelianSchemeLaws_all.1.secBaseChange
  have hWD : GlobalTheory.CoefChangeCompare.ValueWD Xo c :=
    evalWD_fr (frChartF_of (GlobalTheory.Frames.chartCoverF_of_secBaseChange hS E H Dw l Xo c))
  have hBC : GlobalTheory.CoefChangeCompare.HasBC Xo c := GlobalTheory.CoefChangeCompare.hasBC_of hS
  funext p y
  haveI := ((GlobalTheory.reduced_finiteType_iff_testRing c.F).2 p).2
  refine eq_of_forall_algClosed (K := c.F) _ _ fun k _ _ _ φ => ?_
  obtain ⟨z, hz⟩ := hBC p.R k φ y
  rw [← GlobalTheory.CoefChangeCompare.evR_of_map hWD hf.1 hz, ← GlobalTheory.CoefChangeCompare.evR_of_map hWD hf'.1 hz]
  exact h k z

theorem isThClsD_unique : Formalism.MainNotions.ModuliIntegralCharts.H1.ChartIndepSt2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (n : ℕ) (d : DeltaDat Xo c n) (Cl : Type) [Fintype Cl] (w : Cl → (Fin n → LevQ Dw d.l₂) → c.F) (La : Cl → GenLat E n) (Nc gam : Cl → ℕ) (vol : c.F) (ep : Cl → c.F) (Vs : Type) [AddCommGroup Vs] [Module c.F Vs] (io : Vs →ₗ[c.F] MvPolynomial (LtN Dw n) c.F), d.IsLev → (∃ _ : StarRing (𝓞 E), IsNab d.Xo₂ d.c₂ d.nab₂) → (∀ k, (La k).Unimod ∧ (La k).TrivAt d.l₂.M ∧ (La k).LevOK (Nc k) d.l₂.M) → ∀ (a : (E →+* ℂ) × ℕ → ℕ), (∀ v, io v ∈ HHa Dw.mult n c.F ComplexEmbedding.conjugate (InPsi H) (fun τ i => a (τ, i))) → ∀ (x : Cl → Vs) (a' : (E →+* ℂ) × ℕ → ℕ) (m : ℕ), ∀ f ∈ sec Xo c a' m, ∀ f' ∈ sec Xo c a' m, IsThClsD Xo c d w La Nc gam vol ep io x f → IsThClsD Xo c d w La Nc gam vol ep io x f' → f = f' := by
  intro hC E _ _ _ H Dw l Xo c n d Cl _ w La Nc gam vol ep Vs _ _ io hd hnab hLa a hio x a' m f hf f' hf' h h'
  obtain ⟨_, hnab⟩ := hnab
  refine sec_eq_of_geometric hf hf' fun k _ _ _ y => ?_
  letI : Algebra d.c₂.F k := ((algebraMap c.F k).comp (d.eF.symm : d.c₂.F →+* c.F)).toAlgebra
  have hk : ∀ a : c.F, algebraMap d.c₂.F k (d.eF a) = algebraMap c.F k a := fun a => by
    show algebraMap c.F k (d.eF.symm (d.eF a)) = _
    rw [AlgEquiv.symm_apply_apply]
  obtain ⟨y₂, hy⟩ := hd.2.2.2.2.2.2.1 k hk y
  obtain ⟨v, hv, e⟩ := h k hk y y₂ hy
  obtain ⟨v', hv', e'⟩ := h' k hk y y₂ hy
  have hvv : v = v' := funext fun cl =>
    ((GlobalTheory.shortThetaValue_existsUnique_natural GlobalTheory.abelianSchemeLaws_all.1 hC E H Dw d.l₂ d.Xo₂ d.c₂ d.nab₂ hnab n
      (La cl) (Nc cl) (hLa cl).1 (hLa cl).2.1 (hLa cl).2.2 a _
      ((GlobalTheory.admissible_columns_le_and_harmonic_map_cover E H Dw l Xo c n d).2 a _ (hio (x cl))) (fun q => d.eF (w cl q)) 1).1 k y₂).unique
      (hv cl) (hv' cl)
  rw [e, e', hvv]

end GlobalTheory.ClassSumUnique
