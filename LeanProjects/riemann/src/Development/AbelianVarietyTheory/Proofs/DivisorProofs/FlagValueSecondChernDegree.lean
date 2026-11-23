import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TendstoUniformlyOfFamAt
import Development.AbelianVarietyTheory.Definitions.Divisors.HypothesesX
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.RegularAlteration
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsX
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ResidueDegreeOfIsClosedImmersion
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NontrivialIsomClassInt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsometricGrLBPullFlag
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFlagBundlePullFlag
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.RingKrullDimQuotientEqOfMemMinimalPrimes
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagVarietyArithDimension
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagVarietyValueUnique
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.VerticalFlagBundleExistsStatement
open NumberField MvPolynomial Filter Topology Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovTest GlobalTheory.Published
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt
open scoped Classical
open GlobalTheory.CovTestDR GlobalTheory.VdmRec GlobalTheory.MetFam GlobalTheory.ShFam GlobalTheory.Toroidal GlobalTheory.CxPts
open scoped ComplexOrder

set_option autoImplicit false

namespace GlobalTheory.VdmSurf

open Limits

theorem closure_genericPoint {A B : Scheme.{0}} [IrreducibleSpace A] (f : A ⟶ B) [IsClosedImmersion f] :
    closure {f (genericPoint A)} = Set.range f := by
  have := (genericPoint_spec A).image f.continuous
  rw [Set.image_univ, f.isClosedEmbedding.isClosed_range.closure_eq] at this
  exact this.def

theorem vdmPol_zero (r : ℕ) : vdmPol r 0 = ((r.factorial : ℝ)⁻¹) •
    (aeval fun z : Σ _ : Unit, Fin r => (MvPolynomial.X (some z.2) : MvPolynomial (Option (Fin r)) ℝ))
      ((∑ z : Σ _ : Unit, Fin r, MvPolynomial.X z ^ 2) * (∏ a : Unit, ∏ i : Fin r, ∏ i' ∈ Finset.Ioi i,
        (MvPolynomial.X (⟨a, i'⟩ : Σ _ : Unit, Fin r) - MvPolynomial.X ⟨a, i⟩)) : MvPolynomial (Σ _ : Unit, Fin r) ℝ) := by
  simp [vdmPol, Fintype.sum_sigma, smul_eq_C_mul, mul_assoc]

theorem val_eq_two_mul : Hypotheses2 → ArCalc → RegularAlteration → ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (d : ℕ), IsArithVar p d → ∀ (E : X.Modules) (r : ℕ) (h : VMetric p E r) (H : h.IsCInf) (F : FlagSp E r) (N : HermLB p) (S : Scheme.{0}) [IsIntegral S] (i : S ⟶ X) [IsClosedImmersion i], IsArithVar (i ≫ p) 1 → ∀ c : ℝ, (h.pull i rfl).IsCh2Deg c → F.val H N (i (genericPoint S)) 0 = 2 * c := by
  intro hP hC hR k _ X _ p d hX E r h H F N S _ i _ hS c hc
  haveI := hX.isLocallyNoetherian
  haveI := hS.isLocallyNoetherian
  have hi : closure {i (genericPoint S)} = Set.range i := closure_genericPoint i
  have hdim : topologicalKrullDim (closure ({i (genericPoint S)} : Set X)) = (0 + 2 : ℕ) := by
    rw [topologicalKrullDim_eq_of_isEmbedding i.isClosedEmbedding.isEmbedding hi.symm, hS.dim_eq]
  obtain ⟨y, Φ, hy, hΦ, hv⟩ : F.IsVal H N (i (genericPoint S)) 0 (F.val H N (i (genericPoint S)) 0) :=
    Classical.epsilon_spec ((GlobalTheory.VdmWd.existsUnique_val_arch hC k X p d hX E r h H F N _ 0).1 hdim).exists
  rw [← hv]
  obtain ⟨hY, -, hz⟩ := (GlobalTheory.FlagTop.main k X p d hX E r h.isVB).2 F
  obtain ⟨y', hy', hcl, -⟩ := hz (i (genericPoint S))
  obtain rfl : y = y' := ((hy.2 y' hy'.1).antisymm (hy'.2 y hy.1)).eq
  let F' : FlagSp ((Scheme.Modules.pullback i).obj E) r :=
    ⟨pullback F.π i, pullback.snd F.π i, GlobalTheory.FlagBaseChange.pullFlag F.π i F.fl,
      GlobalTheory.FlagBaseChange.isFlagBundle_pullFlag X F.Y _ F.π i Unit _ _ _ F.univ⟩
  let j := pullback.fst F.π i
  have w' : pullback.snd F.π i ≫ i ≫ p = j ≫ F.π ≫ p := by
    rw [← Category.assoc, ← pullback.condition, Category.assoc]
  have hY' : IsArithVar (j ≫ F.π ≫ p) (1 + r.choose 2) :=
    w' ▸ ((GlobalTheory.FlagTop.main k S (i ≫ p) 1 hS _ r (h.pull i rfl).isVB).2 F').1
  haveI : IsIntegral (pullback F.π i : Scheme.{0}) := hY'.isIntegral
  have hj : j (genericPoint (pullback F.π i : Scheme.{0})) = y := by
    refine (inseparable_iff_closure_eq.2 ?_).eq
    rw [closure_genericPoint j, hcl, hi]
    exact Scheme.Pullback.range_fst F.π i
  have e : 0 + 2 + r.choose 2 = 1 + r.choose 2 + 1 := by omega
  rw [e] at hΦ
  have hA : IsArFun (fun o => (F.fam H N o).pull j rfl) (1 + r.choose 2) Φ := by
    refine ⟨fun n => ?_, hΦ.2⟩
    obtain ⟨g, hg, e₁⟩ := hΦ.1 n
    rw [← e₁, ← hj]
    exact (isometric_comb_pull _ n j rfl).symm.isSelfInter hY' (hg.isSelfInter_restrict hY j rfl)
  have hB := ((hC.arIso k _ _ _ hY').2 _ _ Φ hA).2.2 (Σ _ : Unit, Fin r)
    (fun z => VMetric.grLB F'.fl z.2 ((H.pull i rfl).pull (pullback.snd F.π i) w'))
    (fun z => Pi.single (some z.2) 1) fun z => (isometric_comb_single _ _).trans
      (GlobalTheory.FlagBaseChange.isometric_grLB_pullFlag k X F.Y S p _ F.π rfl i E r h H F.fl w' z.2)
  have key := GlobalTheory.T.vertical_flag_bundle_exists hP hC hR k S _ (i ≫ p) _ _ hS hY' (pullback.snd F.π i) w' Unit (fun _ => _) (fun _ => r)
    (fun _ => h.pull i rfl) (fun _ => H.pull i rfl) (fun _ => F'.fl) F'.univ (fun _ => c) (fun _ => hc) _ hB
  simp only [lin_single, LinearMap.comp_apply, AlgHom.toLinearMap_apply] at key
  rw [vdmPol_zero, map_smul, key]
  have : (r.factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.2 r.factorial_ne_zero
  simp [this]

end GlobalTheory.VdmSurf
