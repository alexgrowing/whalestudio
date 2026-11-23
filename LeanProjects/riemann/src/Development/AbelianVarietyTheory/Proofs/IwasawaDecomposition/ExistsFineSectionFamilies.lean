import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IntegralCharts
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUniqueCoeffsStableBasisStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StableBasisNonvanishingClosedPointStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MultiplierPowerUnitConstantStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsGeneratorMultiplierPowerStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GeneratorCorrespondencePullbackStatement

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open GlobalTheory.LN GlobalTheory.TorRef GlobalTheory.IntegralCombination GlobalTheory.UU Formalism.L2.Pj
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.IntFam

open GlobalTheory.ZH.AdaptedSpan

theorem intFam : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], IsCN R →
    ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G]
      [IsCommMonObj G], IsSemiAbelian G → Unif (maximalIdeal R) D A G → ∀ N : ℕ, 1 ≤ N → FineData D.toPre N →
    ∃ (n : ℕ) (Φ : Fin n → Fam D.toPre (FractionRing R) N) (f : Fin n → ∀ α, SecAb D.toPre N α),
      (∀ i α, GeneratorPullback.SecScal D.toPre.P.L (DegPre.famφ D.toPre (FractionRing R) α) (DegPre.famε N) ((Φ i).s α)
        (D.toPre.famφB α) (DegPre.famε N) (f i α) (DegPre.prB D.toPre (FractionRing R)).left 1) ∧
      LinearIndependent (FractionRing R) Φ ∧ Submodule.span (FractionRing R) (Set.range Φ) = ⊤ ∧
      ∀ c : Fin n → R, (∃ i, c i ∉ maximalIdeal R) →
        ∃ (α : D.toPre.X) (j : Fin 4 → D.toPre.P.L.ι) (b : D.toPre.P.A.left),
          D.toPre.P.A.hom b = closedPoint R ∧
          b ∈ D.toPre.P.A.left.basicOpen ((∑ i, c i • f i α).f j) := by
  intro R _ _ _ hCN D A G _ _ _ U N hN hF
  classical
  obtain ⟨hnoeth, hnorm, -, -⟩ := hCN
  haveI := hnoeth
  have hG := GlobalTheory.allSixLaws.1.globalFns
  let K := FractionRing R
  obtain ⟨ρ, hρ, hsurj, hcan⟩ := GlobalTheory.FamDim.exists_class_reps D.toPre.X N hN
  choose μ₀ r hr hrs using fun q => hF (ρ q)
  let a : (Fin D.toPre.rank → Fin N) → D.toPre.X := fun q => ρ q + N • μ₀ q
  have hdis : ∀ q q' mu, a q + N • mu = a q' → q = q' := fun q q' mu h => hρ q q' (μ₀ q + mu - μ₀ q') (by
    have : ρ q + N • (μ₀ q + mu - μ₀ q') = a q + N • mu - N • μ₀ q' := by
      simp only [a, smul_sub, smul_add]; abel
    rw [this, h]; simp only [a]; abel)
  have hcov : ∀ β, ∃ q mu, a q + N • mu = β := fun β => by
    obtain ⟨q, mu, h⟩ := hsurj β
    refine ⟨q, mu - μ₀ q, ?_⟩
    rw [← h]; simp only [a, smul_sub]; abel
  have hclass : ∀ q (x y : D.toPre.X), a q + N • x = a q + N • y → x = y := fun q x y e =>
    hcan x y (add_left_cancel e)
  have hst : ∀ q, ∃ (m : ℕ) (b : Fin m → D.toPre.SecB N (a q)), StableBasis D.toPre N (a q) b := fun q => by
    obtain ⟨m, b, -, hb⟩ := GlobalTheory.twistBaseChange R D.toPre N hN (a q)
    exact ⟨m, b, hb⟩
  choose m b hb using hst
  let I := Σ q, Fin (m q)
  choose Φ₀ hΦ₁ hΦ₀ using fun x : I =>
    UUA.exists_fam_rep (D := D.toPre) (F := K) hG D.tau_bimult N (a x.1) (hclass x.1)
      (pullAb D.toPre K N (a x.1) (b x.1 x.2))
  have hoff : ∀ (x : I) q, q ≠ x.1 → famAt D.toPre K N (a q) (Φ₀ x) = 0 := fun x q hq =>
    SecOps.sec_ext fun j => hΦ₀ x (a q) (fun mu h => hq (hdis _ _ _ h).symm) j
  have hf : ∀ (x : I) (α : D.toPre.X), ∃ f : SecAb D.toPre N α, pullAb D.toPre K N α f = (Φ₀ x).s α ∧
      (∀ h : α = a x.1, f = h ▸ b x.1 x.2) ∧ ((∀ mu, a x.1 + N • mu ≠ α) → f = 0) := fun x α => by
    by_cases h0 : α = a x.1
    · subst h0
      exact ⟨b x.1 x.2, (hΦ₁ x).symm, fun _ => rfl, fun h => absurd (by simp) (h 0)⟩
    by_cases h1 : ∃ mu, a x.1 + N • mu = α
    · obtain ⟨mu, rfl⟩ := h1
      obtain ⟨s, hs⟩ := hrs x.1 (μ₀ x.1 + mu)
      have e : ρ x.1 + N • (μ₀ x.1 + mu) = a x.1 + N • mu := by simp only [a, smul_add]; abel
      rw [e] at hs
      have hr' : PsiCoord D.toPre (a x.1) (r x.1) := hr x.1
      obtain ⟨u₀, c, hu₀, hrel⟩ := GlobalTheory.T.exists_generator_multiplier_power R hnorm D.toPre N hN (a x.1) mu s
        (fun ξ J hJ hJc => GlobalTheory.T.multiplier_power_unit_constant R _ D N _ _ _ _ hr' hs ξ J hJ hJc)
      obtain ⟨f, hf⟩ := GlobalTheory.T.generator_correspondence_pullback R D.toPre N (a x.1) mu u₀ c hu₀ hrel (b x.1 x.2) (Φ₀ x) (hΦ₁ x)
      exact ⟨f, hf, fun h => absurd h h0, fun h => absurd rfl (h mu)⟩
    · refine ⟨0, ?_, fun h => absurd h h0, fun _ => rfl⟩
      rw [map_zero]
      exact SecOps.sec_ext fun j => (hΦ₀ x α (fun mu h => h1 ⟨mu, h⟩) j).symm
  choose f hfK hf₁ hf₀ using hf
  have hmain : LinearIndependent K Φ₀ := by
    rw [Fintype.linearIndependent_iff]
    rintro c hc ⟨q, i⟩
    have h1 : ∑ i, c ⟨q, i⟩ • pullAb D.toPre K N (a q) (b q i) = 0 := by
      have h2 := congrArg (famAt D.toPre K N (a q)) hc
      rw [map_sum, map_zero, Fintype.sum_sigma, Finset.sum_eq_single q] at h2
      · refine Eq.trans (Finset.sum_congr rfl fun i _ => ?_) h2
        rw [map_smul]
        exact congrArg (c ⟨q, i⟩ • ·) (hΦ₁ ⟨q, i⟩).symm
      · intro q' _ hq
        exact Finset.sum_eq_zero fun i _ => by rw [map_smul, hoff ⟨q', i⟩ q hq.symm, smul_zero]
      · intro h; exact absurd (Finset.mem_univ q) h
    have h3 := (GlobalTheory.T.existsUnique_coeffs_stable_basis R D.toPre N (a q) (m q) (b q) (hb q) 0).unique
      (y₁ := fun i => c ⟨q, i⟩) (y₂ := fun _ => 0) h1.symm (by simp)
    exact congrFun h3 i
  have hspan : Submodule.span K (Set.range Φ₀) = ⊤ := by
    refine top_unique fun s _ => ?_
    choose c hc using fun q => (GlobalTheory.T.existsUnique_coeffs_stable_basis R D.toPre N (a q) (m q) (b q) (hb q) (s.s (a q))).exists
    refine (Submodule.mem_span_range_iff_exists_fun K).2 ⟨fun x => c x.1 x.2, fam_ext fun β j => ?_⟩
    obtain ⟨q, mu, rfl⟩ := hcov β
    refine GlobalTheory.FamDim.fam_term_eq hG ?_ mu j
    have h2 : famAt D.toPre K N (a q) (∑ x, c x.1 x.2 • Φ₀ x) = s.s (a q) := by
      rw [map_sum, Fintype.sum_sigma, Finset.sum_eq_single q]
      · refine Eq.trans (Finset.sum_congr rfl fun i _ => ?_) (hc q).symm
        rw [map_smul]
        exact congrArg (c q i • ·) (hΦ₁ ⟨q, i⟩)
      · intro q' _ hq
        exact Finset.sum_eq_zero fun i _ => by rw [map_smul, hoff ⟨q', i⟩ q hq.symm, smul_zero]
      · intro h; exact absurd (Finset.mem_univ q) h
    exact h2
  let e := Fintype.equivFin I
  refine ⟨Fintype.card I, fun i => Φ₀ (e.symm i), fun i => f (e.symm i), fun i α => ?_, ?_, ?_, fun c ⟨i₀, hi₀⟩ => ?_⟩
  · have h1 : Out.scal (DegPre.BF D.toPre K).hom (1 : R) = 1 := by unfold Out.scal; rw [map_one, map_one]
    rw [← h1]
    refine (GlobalTheory.ZH.AdaptedSpan.secScal_iff_pullAb D.toPre K ((Φ₀ (e.symm i)).s α) (f (e.symm i) α) 1).2 ?_
    rw [map_one]
    exact (hfK _ α).trans (one_smul K (show SecAbF D.toPre K N α from (Φ₀ (e.symm i)).s α)).symm
  · exact hmain.comp _ e.symm.injective
  · rw [← hspan]
    exact congrArg _ (e.symm.surjective.range_comp Φ₀)
  · set x₀ := e.symm i₀ with hx₀
    have hsum : (∑ i, c i • f (e.symm i) (a x₀.1) : SecAb D.toPre N (a x₀.1)) =
        ∑ i, c (e ⟨x₀.1, i⟩) • (show SecAb D.toPre N (a x₀.1) from b x₀.1 i) := by
      rw [← Equiv.sum_comp e (fun i => c i • f (e.symm i) (a x₀.1)), Fintype.sum_sigma, Finset.sum_eq_single x₀.1]
      · refine Finset.sum_congr rfl fun i _ => ?_
        rw [Equiv.symm_apply_apply, hf₁ ⟨x₀.1, i⟩ _ rfl]
      · intro q _ hq
        refine Finset.sum_eq_zero fun i _ => ?_
        rw [Equiv.symm_apply_apply, hf₀ ⟨q, i⟩ _ (fun mu h => hq (hdis _ _ _ h)), smul_zero]
      · intro h; exact absurd (Finset.mem_univ _) h
    obtain ⟨j, y, hy, hm⟩ := GlobalTheory.T.stable_basis_nonvanishing_closed_point R D.toPre N (a x₀.1) (m x₀.1) (b x₀.1) (hb x₀.1)
      (fun i => c (e ⟨x₀.1, i⟩)) ⟨x₀.2, by
        have : e ⟨x₀.1, x₀.2⟩ = i₀ := by rw [Sigma.eta, hx₀, Equiv.apply_symm_apply]
        rw [this]; exact hi₀⟩
    refine ⟨a x₀.1, j, y, hy, ?_⟩
    rw [hsum]
    exact hm

end GlobalTheory.IntFam
