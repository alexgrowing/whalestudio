import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SiegelAtOfKnownTheorem
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsTamePolyhedralFanStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsOddLevelCoverStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PolyhedralFanSiegelBaseChangeStatement

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.ShFam GlobalTheory.Models GlobalTheory.SiegLoc

namespace GlobalTheory.SiegLoc

theorem finrank_cm (E : Type) [Field E] [NumberField E] [IsCMField E] :
    2 ≤ Module.finrank ℚ E ∧ 2 ∣ Module.finrank ℚ E := by
  have h := IsTotallyComplex.finrank (K := E)
  have hp : 0 < Module.finrank ℚ E := Module.finrank_pos
  exact ⟨by omega, ⟨_, h⟩⟩

theorem siegLocSt_of_siegelToroidalIntegral : GlobalTheory.Published.SiegelToroidalIntegral → SiegLocSt := by
  intro hP E _ _ _ H D hpq Xo
  obtain ⟨h2, hev⟩ := finrank_cm E
  set g := Module.finrank ℚ E / 2 * (D.p + D.q) with hgdef
  have hg1 : 1 ≤ g := Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero (by omega) (by omega))
  obtain ⟨φ, hφ, hS⟩ := siegAt_of_siegelToroidalIntegral hP g hg1
  obtain ⟨φs, hφs, htame, hag⟩ := GlobalTheory.T.exists_tame_polyhedral_fan g φ hφ
  refine ⟨g, φs, ?_, hφs, htame, fun l c hgood => ?_⟩
  · obtain ⟨f, hf⟩ := hev
    rw [hgdef, hf, Nat.mul_div_cancel_left _ (by norm_num : 0 < 2)]
    rcases le_total D.p D.q with h | h
    · rw [min_eq_left h]; nlinarith
    · rw [min_eq_right h]; nlinarith
  · obtain ⟨I, hI, R, hR, a, b, ω, n, hcov, hn⟩ := GlobalTheory.T.exists_odd_level_cover E H l c hgood
    have key : ∀ i, ∃ C : Model (Xo l) c (ω i), HasCones (ConeZ E φs) C ∧
        PolRay (comb 0 (resInt _ φs) 0 (resInt _ φs)) (resInt _ φs) 1 C := fun i =>
      GlobalTheory.T.polyhedral_fan_siegel_base_change E H D l (Xo l) c φ φs (n i) (R i) (b i) (ω i) hpq hφ (hS (n i) (hn i).1 (hn i).2.1) (hn i).1
        (hn i).2.1 (hn i).2.2.1 hag (hcov.2.1 i).1 (hcov.2.1 i).2.1 (by rw [← (hn i).2.2.2]; exact (hcov.2.1 i).2.2)
    choose C hC using key
    exact ⟨I, hI, R, hR, a, b, ω, C, hcov, hC⟩

end GlobalTheory.SiegLoc
