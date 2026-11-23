import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.VecOfSpec
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FactorsThroughZeroLocus
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HomogeneousFormVanishingCombinationChartIndepStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GermFormPulledBackCombinationsExpandMonomialsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SectionLocalExpansion
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GermConstantsEqAlongAffineSpaceSquareStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoordinatePolynomialsFormMemKernelDifferentialStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqZeroOfDifferentialKernelZeroGermsStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Out
open GlobalTheory.HomFixMat GlobalTheory.HomFixUniv

namespace GlobalTheory.FormsLocus
open GlobalTheory.AbLaw in

theorem germ_eq {Rg : Type} [CommRing Rg] {A₀ T X : Scheme.{0}} {f : A₀ ⟶ Sp Rg} {N : LB A₀} {mA mB : ℕ}
    (Q : ∀ d : ℕ, Perf f (GlobalTheory.AbLaw.pw N (d : ℤ))) (a : Fin mA → LB.Sec N)
    (g : T ⟶ Sp (MvPolynomial (Fin (mA * mB)) Rg)) (φ : X ⟶ A₀) (p : X ⟶ T)
    (hw : φ ≫ f = p ≫ g ≫ affπ Rg (mA * mB)) (d : ℕ) (F : MvPolynomial (Fin mB) Rg) (hF : F.IsHomogeneous d)
    (z : X) (i : (Q d).I) (hz : φ z ∈ (Q d).W i) :
    MvPolynomial.eval₂Hom (gc (p ≫ g ≫ affπ Rg (mA * mB)) z) (comb a φ p (matOf g) z ((Q d).ch i)) F =
      ∑ k, gs p z ⊤ (ringOf g (polys Q a d F k)) * gs φ z ((Q d).W i) ((Q d).u k i) := by
  have hq : φ z ∈ N.U ((Q d).ch i) := (Q d).le i hz
  have hψ : ∀ x : Γ(T, ⊤), gs p z ⊤ x =
      ((X.presheaf.germ (p ⁻¹ᵁ ⊤) z trivial).hom.comp (p.app ⊤).hom) x := fun x => gs_eq p z ⊤ trivial x
  rw [GlobalTheory.T.germ_form_pulledBack_combinations_expand_monomials Rg A₀ T X f N mA mB a g φ p hw d F hF z _ hq]
  have hv : ∀ ν, gs φ z (N.U ((Q d).ch i)) ((monSec a d ν).f ((Q d).ch i)) =
      ∑ k, gs p z ⊤ (ringOf g (MvPolynomial.C (vecOf (Q d) (monSec a d ν) k))) * gs φ z ((Q d).W i) ((Q d).u k i) := by
    intro ν
    exact (GlobalTheory.T.section_local_expansion Rg A₀ X f _ (Q d) (monSec a d ν) φ z i hz).trans
      (Finset.sum_congr rfl fun k _ => by rw [GlobalTheory.T.germ_constants_eq_along_affineSpace_square Rg A₀ T X f (mA * mB) g φ p hw z])
  simp only [hv, polys, hψ, map_sum, map_mul, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun ν _ => by ring

theorem exists_closed_formsOK : ∀ (Rg : Type) [CommRing Rg] [IsNoetherianRing Rg] (A₀ B₀ : Scheme.{0}) (f : A₀ ⟶ Sp Rg) (fB : B₀ ⟶ Sp Rg) (N : LB A₀) (H : LB B₀) (mA mB : ℕ) (a : Fin mA → LB.Sec N) (b : Fin mB → LB.Sec H), Flat f → GlobalTheory.AbLaw.IsProjBy f → N.IsLB → ∃ (Z : Scheme.{0}) (ιZ : Z ⟶ Sp (MvPolynomial (Fin (mA * mB)) Rg)), IsClosedImmersion ιZ ∧ ∀ (T X' : Scheme.{0}) (g : T ⟶ Sp (MvPolynomial (Fin (mA * mB)) Rg)) (φ : X' ⟶ A₀) (p : X' ⟶ T), IsPullback φ p f (g ≫ affπ Rg (mA * mB)) → (GlobalTheory.HomFixUniv.FormsOK a fB b φ p (g ≫ affπ Rg (mA * mB)) (matOf g) ↔ ∃ w : T ⟶ Z, w ≫ ιZ = g) := by
  intro Rg _ _ A₀ B₀ f fB N H mA mB a b hf hp hN
  have Q : ∀ d : ℕ, GlobalTheory.AbLaw.Perf f (GlobalTheory.AbLaw.pw N (d : ℤ)) := fun d =>
    (GlobalTheory.AbLaw.nonempty_perf_of_noetherian Rg A₀ f hf hp _ (GlobalTheory.AbLaw.isLB_pw hN d)).some
  refine ⟨Sp (MvPolynomial (Fin (mA * mB)) Rg ⧸ formIdeal Q a fB b),
    Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (formIdeal Q a fB b))),
    IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective, ?_⟩
  intro T X' g φ p hpb
  rw [GlobalTheory.T.factors_through_zero_locus]
  have hmem : ∀ d (z : X'), ∃ i, φ z ∈ (Q d).W i := fun d z =>
    TopologicalSpace.Opens.mem_iSup.1 (by rw [(Q d).cover]; trivial)
  constructor
  · intro hF
    have hle : formIdeal Q a fB b ≤ RingHom.ker (ringOf g) := by
      refine Ideal.span_le.2 ?_
      rintro _ ⟨d, F, k, hFh, hK, rfl⟩
      have := GlobalTheory.T.eq_zero_of_differential_kernel_zero_germs Rg A₀ T X' f _ (Q d) (g ≫ affπ Rg (mA * mB)) φ p hpb
        (fun k => ringOf g (polys Q a d F k)) (GlobalTheory.T.coordinatePolynomials_form_mem_kernel_differential Rg A₀ T f N mA mB Q a g d F) (fun z i hz => by
          rw [← germ_eq Q a g φ p hpb.w d F hFh z i hz]
          exact hF d F hFh hK z ((Q d).ch i) ((Q d).le i hz))
      exact congrFun this k
    exact fun P hP => hle hP
  · intro h d F hFh hK z q hq
    obtain ⟨i, hi⟩ := hmem d z
    rw [GlobalTheory.T.homogeneousForm_vanishing_combination_chart_indep Rg A₀ T X' N mA mB a φ p _ (matOf g) d F hFh z q ((Q d).ch i) hq ((Q d).le i hi),
      germ_eq Q a g φ p hpb.w d F hFh z i hi]
    refine Finset.sum_eq_zero fun k _ => ?_
    rw [h _ (Ideal.subset_span ⟨d, F, k, hFh, hK, rfl⟩), gs_eq p z ⊤ trivial, map_zero, map_zero, zero_mul]

end GlobalTheory.FormsLocus
