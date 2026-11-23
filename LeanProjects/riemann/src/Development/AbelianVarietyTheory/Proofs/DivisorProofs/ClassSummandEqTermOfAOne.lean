import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.CxTotalEqFullSumIrrOfCxCountReg
import Development.AbelianVarietyTheory.Definitions.Divisors.MinpolyIrreducibleNatDegreeOfRankOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MinpolyOfRegAfOfFixL
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIntOfDenLe
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OrbitalTermIntegralExpression
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OrbitalTermRealTrivialisation
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToVInjective
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OrbitSumConjClasses
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CentralizerOrbitSumConjugate
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PairWeightInvariantFormGroupConjStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OrbitalSumAtPlaceDecomposition
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjugacyClassPartEqWeightMulKottwitzPointSumStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PairWeightSupportFiniteOfFiniteFixingStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteWeightedPairOrbitsOfFiniteWeightedFixedPoiStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SeparableFormGroupElementFixesUniquePositiveLineStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FullSumRegroup
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OrbitalIntegralTestFunctionFirst
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OrbitalIntegralTestFunctionSecond
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteMarkedPairClassesDegreeOneTermNeZeroStatement

noncomputable section

open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx
open scoped TensorProduct Classical

namespace GlobalTheory.LKCx.CxReg

open GlobalTheory.LKCx.Regroup

variable {p : ℕ} [Fact p.Prime]

theorem sep_of_regAf (G : HTGroup p) (v : InfinitePlace G.F) (hv : sigPosH (G.gram_herm v) = 1) (f : G.GAf → ℂ)
    (hreg : ∀ g, f g ≠ 0 → RegAf G g) (β : G.Cˣ) (x : (AfP p ⊗[ℚ] G.C)ˣ) (t : (AfP p)ˣ)
    (hx : Triv G (AfP p) β x t) (hsym : sh G β = β) (hR : ∃ z : (ℝ ⊗[ℚ] G.C)ˣ, Triv G ℝ β z 1) :
    (∀ (y : grp G β) (h : G.GAf), f (h⁻¹ * toAfF G β x t hx y * h) ≠ 0 → (∃ z : Fin G.n → ℂ, 0 < (star z ⬝ᵥ (herm G v β *ᵥ z)).re ∧ FixL G v β y z) → (minpoly G.F (((y : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C)).natDegree = G.n ∧ (minpoly G.F (((y : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C)).Separable) := by
  rintro y h hne ⟨z, hz, hfix⟩
  exact GlobalTheory.LKCx.minpoly_of_regAf_of_fixL p G v hv β hsym hR x t hx y h ⟨z, hz⟩ hfix (hreg _ hne)

theorem finite_pts_reg (G : HTGroup p) (ha : G.a = 1) (v : InfinitePlace G.F) (hv : sigPosH (G.gram_herm v) = 1)
    (L : G.Level) (f : G.GAf → ℂ) (hf : IsTest (MonoidHom.id _) L.K.toSubgroup L.K.toSubgroup f)
    (hreg : ∀ g, f g ≠ 0 → RegAf G g) (K' : Subgroup (Gr G 1)) (f' : Gr G 1 → ℂ)
    (hf' : IsTest (sigG G 1) (KHT p G.m G.n 1 G.Fw) K' f') (β : G.Cˣ) (x : (AfP p ⊗[ℚ] G.C)ˣ) (t : (AfP p)ˣ)
    (hx : Triv G (AfP p) β x t) (hsym : sh G β = β) (htr : ∃ z : (ℝ ⊗[ℚ] G.C)ˣ, Triv G ℝ β z 1) :
    Set.Finite {q : Pts G v β x t hx L.K.toSubgroup K' | ∃ y : grp G β, FixL G v β y (Quot.out q).2.1 ∧
      f ((Quot.out q).1.1⁻¹ * toAfF G β x t hx y * (Quot.out q).1.1) *
        f' ((Quot.out q).1.2⁻¹ * toP1 G β y * (Quot.out q).1.2) ≠ 0} := by
  have hsep := sep_of_regAf G v hv f hreg β x t hx hsym htr
  obtain ⟨Y, hY⟩ := Classical.axiomOfChoice
    (fun P => GlobalTheory.T.orbital_integral_test_function_first p G ha v hv L f hf K' f' hf' β x t hx hsep hsym htr P)
  refine ((GlobalTheory.T.orbital_term_real_trivialisation p G ha v hv L f hf K' f' hf' β x t hx hsym htr).biUnion
    (fun P _ => (Y P).finite_toSet.biUnion
      (fun y₀ _ => GlobalTheory.T.orbital_integral_test_function_second p G ha v hv L f hf K' f' hf' β x t hx hsep hsym htr y₀))).subset ?_
  rintro q ⟨y, hy, hne⟩
  obtain ⟨y₀, hy₀, γ, rfl⟩ := hY _ y rfl ⟨Quot.out q, hy, hne⟩
  simp only [Set.mem_iUnion]
  exact ⟨_, ⟨γ * y₀ * γ⁻¹, Quot.out q, rfl, hy, hne⟩, y₀, hy₀, γ, hy, hne⟩

theorem class_summand_eq_term_of_a_one : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p), G.a = 1 → ∀ v : InfinitePlace G.F, sigPosH (G.gram_herm v) = 1 → ∀ (wt : Polynomial G.F → ℂ) (Kf : Subgroup G.GAf) (f : G.GAf → ℂ) (K' : Subgroup (Gr G 1)) (f' : Gr G 1 → ℂ), (∀ k ∈ Kf, ∀ g, f (k⁻¹ * g * k) = f g) → (∀ k ∈ K', ∀ g, f' (k⁻¹ * g * sigG G 1 k) = f' g) → ∀ (P : Pair G) (x : (AfP p ⊗[ℚ] G.C)ˣ) (t : (AfP p)ˣ) (hx : Triv G (AfP p) P.β x t) (r : grp G P.β), (r : G.Cˣ × ℚˣ) = (P.γ, P.c) → (if (∃ z : Fin G.n → ℂ, 0 < (star z ⬝ᵥ (herm G v P.β *ᵥ z)).re ∧ FixL G v P.β r z) then wt (minpoly G.F (((r : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C)) * pointSum ((toAfF G P.β x t hx).comp (Subgroup.centralizer {r}).subtype) ((toP1 G P.β).comp (Subgroup.centralizer {r}).subtype) (MonoidHom.id (Gr G 1)) Kf K' (toAfF G P.β x t hx r) (toP1 G P.β r) f f' else 0) = (if ∃ μ, P.Mark μ then wt P.pol * P.term Kf f 1 K' f' else 0) := by
  intro p _ G hG v hv wt Kf f K' f' hf hf' P x t hx r hr
  have hiff := fix_iff_mark G hG v hv P r hr
  by_cases hm : ∃ μ, P.Mark μ
  · rw [if_pos (hiff.2 hm), if_pos hm]
    obtain ⟨μ, hμ⟩ := hm
    have hpos := cent_sim_pos p G P μ hG hμ
    set e := centEquiv G P hpos r hr with he
    have h1 : (toAfF G P.β x t hx).comp (Subgroup.centralizer {r}).subtype =
        (P.toAf x t hx).comp e.toMonoidHom := by
      ext1 y; rfl
    have h2 : (toP1 G P.β).comp (Subgroup.centralizer {r}).subtype = (P.toQr 1 1).comp e.toMonoidHom := by
      ext1 y
      show inclG G 1 (locC G y.1.1) = (MulAut.conj (1 : Gr G 1)⁻¹) (inclG G 1 (locC G y.1.1))
      simp
    have h3 : toAfF G P.β x t hx r = P.toAf x t hx P.self := by
      obtain ⟨r, hr'⟩ := r
      simp only at hr
      subst hr
      rfl
    have h4 : toP1 G P.β r = inclG G 1 P.atP := by
      show inclG G 1 (locC G (r : G.Cˣ × ℚˣ)) = _
      rw [hr]; rfl
    have h5 : minpoly G.F (((r : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C) = P.pol := by
      rw [hr]; rfl
    rw [h1, h2, h3, h4, h5, GlobalTheory.pointSum_comp_mulEquiv, GlobalTheory.T.orbital_term_point_sum p G P Kf f K' f' hf hf' x t hx]
  · rw [if_neg (fun h => hm (hiff.1 h)), if_neg hm]

end GlobalTheory.LKCx.CxReg

namespace GlobalTheory.LKCx

end GlobalTheory.LKCx
