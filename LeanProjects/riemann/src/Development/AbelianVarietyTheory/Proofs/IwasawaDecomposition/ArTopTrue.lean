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
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AdelicDivisorInducedLinearStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsCommonRefinementModelsStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PolarizationOfHomogeneousStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AdelicDivisorInducedExistsStatement
open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.Geo GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.TrueGeo GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueCx

namespace GlobalTheory.ArTopTrue

theorem arTop_true : GlobalTheory.Published.ArCalc → GlobalTheory.Published.ArDegree → HTBoundSt → ∀ (D : D7) (A : Amb D) (N j : ℕ) (S : Sig A N j) (κ : Lv A) (s : FinalTheorems S κ) (x : ToroidalCompactificationData s) (Φ : s.Flag) (k : s.Comp) (R : ℝ), 2 ≤ R → (∀ w : Sym D.host.E →₀ ℤ, (∀ a ∈ w.support, {q | a.1 q = true}.Finite ∧ a.2.1 = some R) → ∃ t, (adlOf (Φ.C k) (metsOf x Φ k) w).IsArTop t) ∧ ∀ (ι : Type) [Fintype ι] (w : ι → Sym D.host.E →₀ ℤ), (∀ i, ∀ a ∈ (w i).support, {q | a.1 q = true}.Finite ∧ a.2.1 = some R) → ∃ (M : GlobalTheory.TrueGeo.Model (Φ.C k).Y) (L : ι → GlobalTheory.HermLB M.p) (m : ℕ+) (Ψ : MvPolynomial ι ℝ →ₗ[ℝ] ℝ), (∀ i, (adlOf (Φ.C k) (metsOf x Φ k) (w i)).Induced M (L i) m 0) ∧ (haveI := M.ar.isIntegral; GlobalTheory.ArInt.IsArFun L (Φ.C k).Y.dim Ψ) ∧ ∀ μ : Multiset ι, Multiset.card μ = (Φ.C k).Y.dim + 1 → (arIn s Φ (metsOf x Φ)).num k (μ.map w) = Ψ ((μ.map MvPolynomial.X).prod) / ((((m : ℕ) : ℝ)) ^ ((Φ.C k).Y.dim + 1) * (Module.finrank ℚ D.what₂.LL : ℝ)) := by
  intro hC hD hB D A N j S κ s x Φ k R hR
  have hI5 := GlobalTheory.T.adelic_divisor_induced_exists hB D A N j S κ s x Φ k R hR
  have top : ∀ (w : Sym D.host.E →₀ ℤ) (M : GlobalTheory.TrueGeo.Model (Φ.C k).Y) (L : GlobalTheory.HermLB M.p) (m : ℕ+) (a : ℝ),
      (adlOf (Φ.C k) (metsOf x Φ k) w).Induced M L m 0 → (haveI := M.ar.isIntegral; L.IsSelfInter a) →
      (adlOf (Φ.C k) (metsOf x Φ k) w).IsArTop
        (a / ((m : ℕ) : ℝ) ^ ((Φ.C k).Y.dim + 1) / (Module.finrank ℚ D.what₂.LL : ℝ)) := by
    intro w M L m a hI ha
    refine ⟨M, L, m, 0, a, hI, ha, ?_⟩
    have hn : (adlOf (Φ.C k) (metsOf x Φ k) w).n = 1 := rfl
    simp [hn]
  refine ⟨fun w hw => ?_, fun ι _ w hw => ?_⟩
  · obtain ⟨M, L, m, hI⟩ := hI5 w hw
    haveI := M.ar.isIntegral
    obtain ⟨h, hh⟩ := (hC.arExists _ M.X M.p _ M.ar).1 L
    exact ⟨_, top w M L m _ hI ⟨h, hh, rfl⟩⟩
  classical
  obtain ⟨M₀, -, -, -⟩ := hI5 0 (by simp)
  choose Mi Li mi hIi using fun i => hI5 (w i) (hw i)
  obtain ⟨P, π, hπ⟩ := GlobalTheory.T.exists_common_refinement_models _ _ M₀ ι Mi
  have hE : 0 < ∏ i, (mi i : ℕ) := Finset.prod_pos fun i _ => (mi i).pos
  let m : ℕ+ := ⟨∏ i, (mi i : ℕ), hE⟩
  have hdiv : ∀ i, (mi i : ℕ) ∣ ∏ i, (mi i : ℕ) := fun i => Finset.dvd_prod_of_mem _ (Finset.mem_univ i)
  let e : ι → ℕ+ := fun i => ⟨(∏ i, (mi i : ℕ)) / mi i, Nat.div_pos (Nat.le_of_dvd hE (hdiv i)) (mi i).pos⟩
  have hme : ∀ i, mi i * e i = m := fun i => PNat.eq (by rw [PNat.mul_coe, PNat.mk_coe]; exact Nat.mul_div_cancel' (hdiv i))
  let L : ι → GlobalTheory.HermLB P.p := fun i => ((Li i).pull (π i) (hπ i).1).pow (e i)
  have hL : ∀ i, (adlOf (Φ.C k) (metsOf x Φ k) (w i)).Induced P (L i) m 0 := fun i => by
    have h1 := GlobalTheory.T.induced_metric_pow _ _ _ _ P _ (mi i) (e i) 0
      (GlobalTheory.T.induced_metric_pullback _ _ _ _ (Mi i) P (π i) (hπ i).1 (hπ i).2 (Li i) (mi i) 0 (hIi i))
    rwa [hme i] at h1
  haveI := P.ar.isIntegral
  obtain ⟨Ψ, hΨ⟩ := ((hC.arExists _ P.X P.p _ P.ar).2 ι L).1
  refine ⟨P, L, m, Ψ, hL, hΨ, fun μ hμ => ?_⟩
  have hsum : ∀ n : ι → ℤ, (adlOf (Φ.C k) (metsOf x Φ k) (∑ i, n i • w i)).arTop =
      Ψ (GlobalTheory.ArInt.lin (fun i => (n i : ℝ)) ^ ((Φ.C k).Y.dim + 1)) / ((m : ℕ) : ℝ) ^ ((Φ.C k).Y.dim + 1) /
        (Module.finrank ℚ D.what₂.LL : ℝ) := by
    intro n
    have hI := GlobalTheory.T.adelic_divisor_induced_linear D A N j S κ s x Φ k R P ι w L m (fun i a ha => (hw i a ha).2) hL n
    have ht := top _ P _ m _ hI (hΨ.1 n)
    have hex : ∃ t, (adlOf (Φ.C k) (metsOf x Φ k) (∑ i, n i • w i)).IsArTop t := ⟨_, ht⟩
    rw [Adl.arTop, dif_pos hex]
    exact GlobalTheory.TrueGeo.ArUniq.isArTop_unique hC hD _ _ _ _ _ _ hex.choose_spec ht
  have h4 := GlobalTheory.T.polarization_of_homogeneous ι (Sym D.host.E →₀ ℤ) w (fun v => (adlOf (Φ.C k) (metsOf x Φ k) v).arTop)
    ((Φ.C k).Y.dim + 1) Ψ (1 / ((((m : ℕ) : ℝ)) ^ ((Φ.C k).Y.dim + 1) * (Module.finrank ℚ D.what₂.LL : ℝ)))
    (fun n => by rw [hsum n]; ring) μ hμ
  change polar (fun v => (adlOf (Φ.C k) (metsOf x Φ k) v).arTop) (μ.map w) = _
  rw [h4]
  ring

end GlobalTheory.ArTopTrue
