import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PeriodComparison
import Development.AbelianVarietyTheory.Definitions.Divisors.JetAnalytic
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrysToDRBijective
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsCrystalPairing
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueDetGen
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAppellHumbertUniformization
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CmPointHodgePeriodFormulaStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionTransportCmPeriodStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CmLatticeSpansRealSpaceStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.CMVal GlobalTheory.LatVal GlobalTheory.LatJet
open GlobalTheory.IndefiniteRowSideFullHecke.LatticeNormTransport (upIdele IsLatOf)
attribute [local instance] Over.cartesianMonoidalCategory
set_option autoImplicit false

namespace GlobalTheory.ConjHerm

theorem exists_conj_herm : GlobalTheory.Published.PeriodComparison → GlobalTheory.Published.AbelianDeRham → GlobalTheory.Published.AbelianDualCrystal → ∀ (K : Type) [Field K] [NumberField K] (d : ℕ) (δ : K) (io : K →+* ℂ), Module.finrank ℚ K = 2 → 0 < d → δ ^ 2 = -(d : K) →
    ∀ (g : ℂ ≃+* ℂ) (t : (Af K)ˣ) (Λ₀ Λ₁ : PeriodPair) (Ω₀ Ω₁ : ℂ), Ω₀ ^ 12 = latDisc Λ₀ → TorsTransport io g t Λ₀ Λ₁ Ω₀ Ω₁ →
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] [Algebra K E] (I : Type) [Fintype I] (φ : I → E →+* ℂ),
      IsCMType φ → (∀ i, (φ i).comp (algebraMap K E) = io) → ∀ (c : Ideal (OF E)) (y : (Af E)ˣ), c ≠ ⊥ →
      ∀ (𝔠 : FracId (FR E)) (T : CxPt 𝔠 φ (lattice c y)) (X' : Obj (FR E) 𝔠 (Sp ℂ)) (p : X'.A.left ⟶ T.X.A.left),
        X'.IsPullBy T.X (spMap (g : ℂ →+* ℂ)) p →
        ∀ u' : HolUnif X'.A (X'.diag T.U.c) (Module.finrank ℚ (FR E)), (∀ w, w ∈ u'.Λ ↔ ∃ x ∈ lattice c (y * (upIdele K E t)⁻¹), w = fun j ↦ GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates.defCoord (fun i ↦ (g : ℂ →+* ℂ).comp (φ i)) 0 x (T.U.e j)) →
          (∀ (w : Fin (Module.finrank ℚ (FR E)) → ℂ) (v : epsR ℂ ⟶ T.X.A) (v' : epsR ℂ ⟶ X'.A),
            v'.left ≫ p = spMap (Chart.dualMapR (g : ℂ →+* ℂ)) ≫ v.left → T.U.u.IsDiff w v →
              u'.IsDiff (fun j ↦ g (Ω₀ * w j) / Ω₁) v') →
          (∀ x x' : E, ((upIdele K E t : Af E) * algebraMap E (Af E) x' - algebraMap E (Af E) x) * ((y⁻¹ : (Af E)ˣ) : Af E) ∈ hatO c →
            (u'.ex (fun j ↦ g (φ (T.U.e j) x'))).left ≫ p = spMap (g : ℂ →+* ℂ) ≫ (T.U.u.ex (fun j ↦ φ (T.U.e j) x)).left) →
          ∃ (u'' : HolUnif X'.A (X'.diag T.U.c) (Module.finrank ℚ (FR E))) (h' : I → ℝ), u''.ex = u'.ex ∧
            (∃ χ, u''.IsAH (Matrix.diagonal fun j ↦ (h' (T.U.e j) : ℂ)) χ) ∧
            ∀ i, g ((T.U.h i : ℂ) * (Real.sqrt d : ℝ)) = ((modF t : ℝ) : ℂ) * ((h' i : ℂ) * (Real.sqrt d : ℝ)) := by
  intro hPC hADR hADC K _ _ d δ io hK hd hδ g t Λ₀ Λ₁ Ω₀ Ω₁ hΩ hT E _ _ _ _ I _ φ hφ hres c y hc 𝔠 T X' p hp u' hΛ hdiff hex
  obtain ⟨u₀, Hm, χ, hex₀, hAH⟩ := GlobalTheory.RealMult.Obj.exists_isAH_diag (FR E) 𝔠 X' T.U.c T.U.pos u'
  obtain ⟨β, hβ⟩ := GlobalTheory.T.cm_point_hodge_period_formula E I φ hφ c y hc 𝔠 T
  have hE := GlobalTheory.T.torsion_transport_cm_period hPC hADR hADC K d δ io hK hd hδ g t Λ₀ Λ₁ Ω₀ Ω₁ hΩ hT E I φ hφ hres c y hc 𝔠 T X' p hp u' hΛ hdiff hex
    u₀ Hm χ hex₀ hAH
  have hmem : ∀ w, w ∈ u₀.Λ ↔ ∃ x ∈ lattice c (y * (upIdele K E t)⁻¹), w = fun j ↦ g (φ (T.U.e j) x) := by
    intro w
    rw [← u₀.ker, hex₀, u'.ker, hΛ]
    simp [GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates.defCoord]
  have hN : 0 < modF t := by
    unfold modF
    refine finprod_induction (fun x => 0 < x) one_pos (fun _ _ => mul_pos) (fun v => ?_)
    have : (0:ℝ) < (Ideal.absNorm v.asIdeal : ℕ) := by
      exact_mod_cast Nat.pos_of_ne_zero (by rw [Ne, Ideal.absNorm_eq_zero_iff]; exact v.ne_bot)
    exact zpow_pos this _
  obtain ⟨h', hHm, hid⟩ := GlobalTheory.T.cm_lattice_spans_real_space K d δ io hd hδ g hT.2.2.1 E I φ hφ hres _ T.U.e u₀.Λ _ u₀.full hmem T.U.h β hβ
    (modF t) hN Hm hAH.1 hE
  exact ⟨u₀, h', hex₀, ⟨χ, hHm ▸ hAH⟩, hid⟩

end GlobalTheory.ConjHerm
