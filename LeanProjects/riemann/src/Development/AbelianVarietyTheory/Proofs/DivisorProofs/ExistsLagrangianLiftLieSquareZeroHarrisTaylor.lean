import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.NotCompactOfMEqOne
import Development.AbelianVarietyTheory.Definitions.Divisors.InfUniv
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GroupObjectLiftDividedPowers
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorModOfTmul
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIdempotentImaginaryQuadraticEigenCrystalStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLieConditionSummandResidueCharPStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLiftSummandLieResidueCharZeroStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LagrangianCompletionSupIdealSmulEqStatement

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.UPel.Sm GlobalTheory.Cris GlobalTheory.DeRham
open scoped TensorProduct

namespace GlobalTheory.HTSummand

theorem exists_lagrangian_lift_lie : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (R : Type) [CommRing R] (b : GlobalTheory.UPel.HT.Base D R) (C : Type) [CommRing C] [IsLocalRing C] [IsArtinianRing C] (I : Ideal C), I ^ 2 = ⊥ → ∀ (tR : R →+* C) (H : Type 1) [AddCommGroup H] [Module C H] [Module.Finite C H] [Module.Projective C H] (ρ : D.O →+* Module.End C H), (letI := GlobalTheory.HTSummand.tensorModOf (ρ.comp (algebraMap (𝓞 D.F) D.O)); Module.Projective (C ⊗[ℤ] 𝓞 D.F) H) → ∀ (φ : LinearMap.BilinForm C H), (∀ x y, φ x y = -φ y x) → Function.Bijective φ → (∀ (c : D.O) x y, φ (ρ c x) y = φ x (ρ (D.star c).unop y)) → ∀ (F : Submodule C H), I • ⊤ ≤ F → (∀ (c : D.O), ∀ x ∈ F, ρ c x ∈ F) → (∀ x ∈ F, ∀ y ∈ F, φ x y ∈ I) → (∀ x, (∀ y ∈ F, φ x y ∈ I) → x ∈ F) → (∃ E' M : Submodule C H, IsCompl E' M ∧ E' ⊔ I • ⊤ = F) → (∀ d, ρ (algebraMap (𝓞 D.F) D.O D.ω) d - tR b.ρ • d ∈ F → ∃ w : Fin D.a → H, (∀ i (c : 𝓞 D.F), ρ (algebraMap (𝓞 D.F) D.O c) (w i) - tR (b.t i c) • w i ∈ F) ∧ d - ∑ i, w i ∈ F) → ∃ E : Submodule C H, (∃ M : Submodule C H, IsCompl E M) ∧ E ⊔ I • ⊤ = F ∧ (∀ (c : D.O), ∀ x ∈ E, ρ c x ∈ E) ∧ (∀ x ∈ E, ∀ y ∈ E, φ x y = 0) ∧ ∀ d, ρ (algebraMap (𝓞 D.F) D.O D.ω) d - tR b.ρ • d ∈ E → ∃ w : Fin D.a → H, (∀ i (c : 𝓞 D.F), ρ (algebraMap (𝓞 D.F) D.O c) (w i) - tR (b.t i c) • w i ∈ E) ∧ d - ∑ i, w i ∈ E := by
  intro p _ D R _ b C _ _ _ I hI tR H _ _ _ _ ρ hproj φ hskew hbij hadj F hIF hFO hFiso hFlag hE' hLie
  obtain ⟨e, he, hρe, hφe, hωe, ⟨v, hv, hωk⟩, hestab⟩ := GlobalTheory.T.exists_idempotent_imaginaryQuadratic_eigen_crystal p D R b C tR H ρ φ hadj
  have hFe := hestab F hFO
  have hLie' : ∀ d ∈ LinearMap.range e, ∃ w : Fin D.a → H, (∀ i (c : 𝓞 D.F), ρ (algebraMap (𝓞 D.F) D.O c) (w i) - tR (b.t i c) • w i ∈ F) ∧ d - ∑ i, w i ∈ F := by
    rintro d ⟨y, rfl⟩
    exact hLie _ (by rw [hωe, sub_self]; exact F.zero_mem)
  have hcore : ∃ G M : Submodule C H, G ⊓ M = ⊥ ∧ G ⊔ M = LinearMap.range e ∧ (∀ (c : D.O), ∀ x ∈ G, ρ c x ∈ G) ∧ G ⊔ (I • ⊤ ⊓ LinearMap.range e) = F ⊓ LinearMap.range e ∧ ∀ d ∈ LinearMap.range e, ∃ w : Fin D.a → H, (∀ i (c : 𝓞 D.F), ρ (algebraMap (𝓞 D.F) D.O c) (w i) - tR (b.t i c) • w i ∈ G) ∧ d - ∑ i, w i ∈ G := by
    by_cases hp : IsUnit (p : C)
    · exact GlobalTheory.T.exists_liftSummand_lie_residueCharZero p D R b C I hI hp tR H ρ hproj e he hρe hωe F hIF hFO hFe hE' hLie'
    · exact GlobalTheory.T.exists_lieCondition_summand_residueCharP p D R b C I hI ((IsLocalRing.mem_maximalIdeal _).2 hp) tR H ρ hproj e he hρe hωe F hIF hFO hFe hE' hLie'
  obtain ⟨G, M, hGM, hGMr, hGO, hGF, hGLie⟩ := hcore
  obtain ⟨E, hEc, hEe, hEF, hEiso, hEO, hEst⟩ := GlobalTheory.T.lagrangianCompletion_sup_ideal_smul_eq C I H D.O ρ (fun a => (D.star a).unop) φ e he hρe hskew (fun a => D.star_star a) hadj hφe hbij F hIF hFiso hFlag hFe G M hGM hGMr hGO hGF
  refine ⟨E, hEc, hEF, hEO, hEiso, ?_⟩
  intro d hd
  have hGE : G ≤ E := hEe ▸ inf_le_left
  set k := d - e d with hkdef
  have hek : e k = 0 := by
    have := LinearMap.congr_fun he d
    simp only [Module.End.mul_apply] at this
    simp [hkdef, this]
  have hkE : k ∈ E := by
    set x := ρ (algebraMap (𝓞 D.F) D.O D.ω) d - tR b.ρ • d with hx
    have h1 : x - e x ∈ E := E.sub_mem hd (hEst _ hd)
    have h2 : x - e x = ρ (algebraMap (𝓞 D.F) D.O D.ω) k - tR b.ρ • k := by
      have hc := LinearMap.congr_fun (hρe (algebraMap (𝓞 D.F) D.O D.ω)) d
      simp only [Module.End.mul_apply] at hc
      simp only [hx, hkdef, map_sub, LinearMap.map_smul, smul_sub, hc]
      abel
    rw [h2, hωk k hek] at h1
    obtain ⟨u, rfl⟩ := hv
    have := E.smul_mem (↑u⁻¹ : C) h1
    rwa [smul_smul, Units.inv_mul, one_smul] at this
  obtain ⟨w, hw, hdw⟩ := hGLie (e d) ⟨d, rfl⟩
  refine ⟨w, fun i c => hGE (hw i c), ?_⟩
  have : d - ∑ i, w i = (e d - ∑ i, w i) + k := by rw [hkdef]; abel
  rw [this]
  exact E.add_mem (hGE hdw) hkE

end GlobalTheory.HTSummand
