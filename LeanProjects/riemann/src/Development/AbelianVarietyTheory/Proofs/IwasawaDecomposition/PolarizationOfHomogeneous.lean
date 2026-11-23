import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsIsHodgeFrameIff
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.DegFrame
import Development.AbelianVarietyTheory.Statements.HeightBoundStatement.HTBoundSt
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LineModel
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ArBirational
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EqOfIsometricTrivShift
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AltSumMultilinear
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ArakelovTopUnique
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.InducedMetricPullbackStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.InducedMetricPowStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AdmissibleModelsOfHtBound
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FromModelOfLocMax
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsModelPresentingDivisorStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FamilyMetricsSmoothStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MetricConjugationSymmetryStatement
open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.Geo GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.TrueGeo GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueCx

namespace GlobalTheory.ShFam.PolarPowers

theorem polar_map {A B : Type} [AddCommGroup A] [AddCommGroup B] (g : A →+ B) (f : B → ℝ) (S : Multiset A) :
    polar f (S.map g) = polar (f ∘ g) S := by
  unfold Pad.polar
  rw [Multiset.card_map, PolarMultilinear.powerset_map, Multiset.map_map]
  congr 2
  refine Multiset.map_congr rfl fun T _ => ?_
  simp [Function.comp, Multiset.card_map, map_multiset_sum]

theorem exists_fin {A : Type} (S : Multiset A) {d : ℕ} (h : Multiset.card S = d) :
    ∃ a : Fin d → A, Multiset.map a Finset.univ.val = S := by
  subst h
  refine ⟨fun j => S.toList.get (j.cast (by simp)), ?_⟩
  rw [Fin.univ_val_map]
  conv_rhs => rw [← Multiset.coe_toList S]
  congr 1
  apply List.ext_get <;> simp

noncomputable def linZ (ι : Type) [Fintype ι] : (ι → ℤ) →ₗ[ℤ] MvPolynomial ι ℝ :=
  (AddMonoidHom.mk' (fun n : ι → ℤ => ArInt.lin fun i => (n i : ℝ)) (by
    intro a b
    simp [ArInt.lin, Finset.sum_add_distrib, add_mul])).toIntLinearMap

theorem linZ_apply {ι : Type} [Fintype ι] (n : ι → ℤ) : linZ ι n = ArInt.lin fun i => (n i : ℝ) := rfl

theorem linZ_single {ι : Type} [Fintype ι] [DecidableEq ι] (i : ι) : linZ ι (Pi.single i 1) = MvPolynomial.X i := by
  rw [linZ_apply, ArInt.lin, Finset.sum_eq_single i]
  · simp
  · intro j _ hj; simp [Pi.single_apply, hj]
  · simp

end GlobalTheory.ShFam.PolarPowers

theorem GlobalTheory.ShFam.PolarPowers.polar_eq_of_pow : ∀ (ι : Type) [Fintype ι] (B : Type) [AddCommGroup B] (w : ι → B) (f : B → ℝ) (d : ℕ) (Ψ : MvPolynomial ι ℝ →ₗ[ℝ] ℝ) (c : ℝ), (∀ n : ι → ℤ, f (∑ i, n i • w i) = c * Ψ (GlobalTheory.ArInt.lin (fun i => (n i : ℝ)) ^ d)) → ∀ μ : Multiset ι, Multiset.card μ = d → polar f (μ.map w) = c * Ψ ((μ.map MvPolynomial.X).prod) := by
  classical
  intro ι _ B _ w f d Ψ c hf μ hμ
  let g : (ι → ℤ) →+ B := AddMonoidHom.mk' (fun n => ∑ i, n i • w i) (by
    intro a b; simp [add_smul, Finset.sum_add_distrib])
  let M : MultilinearMap ℤ (fun _ : Fin d => ι → ℤ) ℝ :=
    ((c • Ψ).restrictScalars ℤ).compMultilinearMap
      ((MultilinearMap.mkPiAlgebra ℤ (Fin d) (MvPolynomial ι ℝ)).compLinearMap fun _ => GlobalTheory.ShFam.PolarPowers.linZ ι)
  have hM : ∀ a, M a = c * Ψ (∏ j, GlobalTheory.ShFam.PolarPowers.linZ ι (a j)) := by
    intro a; simp [M]
  have hsym : ∀ (σ : Equiv.Perm (Fin d)) (a : Fin d → ι → ℤ), M (a ∘ σ) = M a := by
    intro σ a
    rw [hM, hM]
    congr 2
    exact Equiv.prod_comp σ (fun j => GlobalTheory.ShFam.PolarPowers.linZ ι (a j))
  have hfg : f ∘ g = fun b => M fun _ => b := by
    funext b
    rw [hM, Function.comp, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    exact hf b
  let S : Multiset (ι → ℤ) := μ.map fun i => Pi.single i 1
  have hS : S.map g = μ.map w := by
    simp only [S, Multiset.map_map]
    refine Multiset.map_congr rfl fun i _ => ?_
    simp [g, Function.comp, Pi.single_apply]
  have hcard : Multiset.card S = d := by simp [S, hμ]
  obtain ⟨a, ha⟩ := GlobalTheory.ShFam.PolarPowers.exists_fin S hcard
  rw [← hS, GlobalTheory.ShFam.PolarPowers.polar_map, hfg, ← ha, PolarMultilinear.polar_diag _ d M hsym a, hM]
  congr 2
  rw [Finset.prod_eq_multiset_prod]
  have e : (Multiset.map (fun j => GlobalTheory.ShFam.PolarPowers.linZ ι (a j)) Finset.univ.val) =
      (Multiset.map a Finset.univ.val).map (GlobalTheory.ShFam.PolarPowers.linZ ι) := by
    rw [Multiset.map_map]; rfl
  rw [e, ha]
  simp only [S, Multiset.map_map]
  congr 1
  refine Multiset.map_congr rfl fun i _ => ?_
  exact GlobalTheory.ShFam.PolarPowers.linZ_single i
