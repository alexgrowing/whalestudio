import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AdelicDivisorZeroTrivialStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AdelicDivisorInducedAddStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AdelicDivisorInducedNegStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AdelicDivisorInducedNsmulStatement
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

set_option autoImplicit false

theorem GlobalTheory.CombInd.induced_comb : ∀ (D : D7) (A : Amb D) (N j : ℕ) (S : Sig A N j) (κ : Lv A) (s : FinalTheorems S κ) (x : ToroidalCompactificationData s) (Φ : s.Flag) (k : s.Comp) (R : ℝ) (M : GlobalTheory.TrueGeo.Model (Φ.C k).Y) (ι : Type) [Fintype ι] (w : ι → Sym D.host.E →₀ ℤ) (L : ι → GlobalTheory.HermLB M.p) (m : ℕ+), (∀ i, ∀ a ∈ (w i).support, a.2.1 = some R) → (∀ i, (adlOf (Φ.C k) (metsOf x Φ k) (w i)).Induced M (L i) m 0) → ∀ n : ι → ℤ, (adlOf (Φ.C k) (metsOf x Φ k) (∑ i, n i • w i)).Induced M (GlobalTheory.ArInt.comb L n) m 0 := by
  intro D A N j S κ s x Φ k R M ι _ w L m hR hI n
  classical
  have hsm : ∀ (v : Sym D.host.E →₀ ℤ) (c : ℤ), (∀ a ∈ v.support, a.2.1 = some R) →
      ∀ a ∈ (c • v).support, a.2.1 = some R := fun v c h a ha => h a (Finsupp.support_smul ha)
  have hadd : ∀ (v v' : Sym D.host.E →₀ ℤ), (∀ a ∈ v.support, a.2.1 = some R) →
      (∀ a ∈ v'.support, a.2.1 = some R) → ∀ a ∈ (v + v').support, a.2.1 = some R := fun v v' h h' a ha => by
    rcases Finset.mem_union.1 (Finsupp.support_add ha) with ha | ha
    · exact h a ha
    · exact h' a ha
  have hzp : ∀ i, (adlOf (Φ.C k) (metsOf x Φ k) (n i • w i)).Induced M (ArInt.zp (L i) (n i)) m 0 := fun i => by
    have e : n i • w i = (n i).toNat • w i + -((-n i).toNat • w i) := by
      rw [← natCast_zsmul, ← natCast_zsmul, ← sub_eq_add_neg, ← sub_smul, Int.toNat_sub_toNat_neg]
    have hn : ∀ c : ℕ, ∀ a ∈ (c • w i).support, a.2.1 = some R := fun c => by
      rw [← natCast_zsmul]; exact hsm _ _ (hR i)
    rw [e]
    exact GlobalTheory.T.adelic_divisor_induced_add D A N j S κ s x Φ k M m R _ _ _ _ (hn _)
      (fun a ha => hn _ a (by rwa [Finsupp.support_neg] at ha))
      (GlobalTheory.T.adelic_divisor_induced_nsmul D A N j S κ s x Φ k M m R _ _ (hR i) (hI i) _)
      (GlobalTheory.T.adelic_divisor_induced_neg D A N j S κ s x Φ k M m R _ _ (hn _)
        (GlobalTheory.T.adelic_divisor_induced_nsmul D A N j S κ s x Φ k M m R _ _ (hR i) (hI i) _))
  have key : ∀ l : List ι, (∀ a ∈ (l.map fun i => n i • w i).sum.support, a.2.1 = some R) ∧
      (adlOf (Φ.C k) (metsOf x Φ k) (l.map fun i => n i • w i).sum).Induced M
        (l.foldr (fun i M' => (ArInt.zp (L i) (n i)).tens M') (HermLB.triv M.p)) m 0 := by
    intro l
    induction l with
    | nil => exact ⟨by simp, GlobalTheory.T.adelic_divisor_zero_trivial D A N j S κ s x Φ k M m⟩
    | cons i l ih =>
      rw [List.map_cons, List.sum_cons, List.foldr_cons]
      exact ⟨hadd _ _ (hsm _ _ (hR i)) ih.1,
        GlobalTheory.T.adelic_divisor_induced_add D A N j S κ s x Φ k M m R _ _ _ _ (hsm _ _ (hR i)) ih.1 (hzp i) ih.2⟩
  have e : ∑ i, n i • w i = ((Finset.univ : Finset ι).toList.map fun i => n i • w i).sum := by
    rw [Finset.sum_map_toList]
  rw [e]
  exact (key _).2
