import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AveragedIntegralFunctional
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicStoneVonNeumannLagrangianUniquenessStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilRepresentationPreservesSchwartz
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchrodingerLatticeSumIntegrableStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchrodingerLatticeDistributionContinuousStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchrodingerThetaLatticeTranslationStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchrodingerLatticeIntegralNonvanishingStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LagrangianLatticeThetaIntegralFormula
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LagrangianLatticeThetaIntegralBoundStatement

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

namespace GlobalTheory.LagrangianAverage

theorem schr_add_fun {R : Type} [CommRing R] [Invertible (2 : R)] (ψ : AddChar R ℂ) {κ : Type} [Fintype κ]
    (w : (κ → R) × (κ → R)) (φ φ' : (κ → R) → ℂ) : schr ψ w (φ + φ') = schr ψ w φ + schr ψ w φ' := by
  funext x; simp [schr, mul_add]

theorem schr_smul_fun {R : Type} [CommRing R] [Invertible (2 : R)] (ψ : AddChar R ℂ) {κ : Type} [Fintype κ]
    (w : (κ → R) × (κ → R)) (c : ℂ) (φ : (κ → R) → ℂ) : schr ψ w (c • φ) = c • schr ψ w φ := by
  funext x; simp [schr]; ring

theorem exists_linear_extension {V : Type} [AddCommGroup V] [Module ℂ V] (p : Submodule ℂ V) (Φ : V → ℂ)
    (hadd : ∀ x ∈ p, ∀ y ∈ p, Φ (x + y) = Φ x + Φ y) (hsmul : ∀ (c : ℂ), ∀ x ∈ p, Φ (c • x) = c * Φ x) :
    ∃ L : V →ₗ[ℂ] ℂ, ∀ x ∈ p, L x = Φ x := by
  let f : p →ₗ[ℂ] ℂ :=
    { toFun := fun x => Φ x, map_add' := fun x y => hadd x x.2 y y.2, map_smul' := fun c x => hsmul c x x.2 }
  obtain ⟨g, hg⟩ := LinearMap.exists_extend f
  exact ⟨g, fun x hx => by simpa [f] using congrArg (fun h => h ⟨x, hx⟩) hg⟩

theorem exists_lift_basis : ∀ (F : Type) [Field F] (κ : Type) [Fintype κ] (Λ : Submodule F ((κ → F) × (κ → F))),
    ∃ (r : ℕ) (u : Fin r → (κ → F) × (κ → F)),
    (∀ j, u j ∈ Λ) ∧ LinearIndependent F (fun j => (u j).1) ∧ ∀ v ∈ Λ, ∃ c : Fin r → F, v.1 = ∑ j, c j • (u j).1 := by
  intro F _ κ _ Λ
  let P : Submodule F (κ → F) := Λ.map (LinearMap.fst F (κ → F) (κ → F))
  let b := Module.finBasis F P
  have hlift : ∀ j, ∃ z ∈ Λ, z.1 = (b j : κ → F) := fun j => by
    obtain ⟨z, hz, e⟩ := Submodule.mem_map.1 (b j).2
    exact ⟨z, hz, e⟩
  choose u hu hu1 using hlift
  refine ⟨Module.finrank F P, u, hu, ?_, ?_⟩
  · have : (fun j => (u j).1) = P.subtype ∘ b := funext fun j => hu1 j
    rw [this]; exact b.linearIndependent.map' P.subtype (Submodule.ker_subtype P)
  · intro v hv
    have hvP : v.1 ∈ P := Submodule.mem_map.2 ⟨v, hv, rfl⟩
    refine ⟨b.repr ⟨v.1, hvP⟩, ?_⟩
    have h2 := congrArg Subtype.val (b.sum_repr ⟨v.1, hvP⟩)
    simp only [Submodule.coe_sum, Submodule.coe_smul] at h2
    refine h2.symm.trans ?_
    simp [hu1]

theorem main : ∀ (F : Type) [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ), IsStd ψ → ∀ (κ : Type) [Fintype κ]
    (Λ : Submodule F ((κ → F) × (κ → F))), (∀ a ∈ Λ, ∀ b ∈ Λ, a.1 ⬝ᵥ b.2 = b.1 ⬝ᵥ a.2) → Module.finrank F Λ = Fintype.card κ →
    ∀ (ι : Type) [Fintype ι] (w : ι → (κ → F) × (κ → F)), (∀ i j, (w i).1 ⬝ᵥ (w j).2 = (w j).1 ⬝ᵥ (w i).2) →
    (∀ c : ι → F, (∀ v ∈ Λ, (∑ i, c i • w i).1 ⬝ᵥ v.2 = v.1 ⬝ᵥ (∑ i, c i • w i).2) → c = 0) →
    ∀ l ∈ (adeleClass F).adm κ,
    (∀ (t : AF F), ∀ v ∈ Λ, ∀ φ ∈ schA F κ,
      l (schr ψ (t • ((fun i => algebraMap F (AF F) (v.1 i)), (fun i => algebraMap F (AF F) (v.2 i)))) φ) = l φ) →
    ∀ ν : @Measure (ι → AF F) (borel _), @Measure.IsAddHaarMeasure _ _ _ (borel _) ν →
      (∀ φ ∈ schA F κ, Integrable (fun t : ι → AF F =>
          l (schr ψ (∑ i, t i • ((fun k => algebraMap F (AF F) ((w i).1 k)), (fun k => algebraMap F (AF F) ((w i).2 k)))) φ)) ν) ∧
      ∃ l' ∈ (adeleClass F).adm κ, ∀ φ ∈ schA F κ, l' φ = ∫ t, l (schr ψ (∑ i, t i •
          ((fun k => algebraMap F (AF F) ((w i).1 k)), (fun k => algebraMap F (AF F) ((w i).2 k)))) φ) ∂ν := by
  intro F _ _ ψ hψ κ _ Λ hiso hrank ι _ w hw hnd l hl hinv ν hν
  obtain ⟨r, u, huΛ, hli, hsp⟩ := exists_lift_basis F κ Λ
  letI mS : MeasurableSpace (Fin r → AF F) := borel _
  haveI : BorelSpace (Fin r → AF F) := ⟨rfl⟩
  let μ : Measure (Fin r → AF F) := Measure.addHaar
  have hμ : Measure.IsAddHaarMeasure μ := inferInstance
  let Φ : ((κ → AF F) → ℂ) → ℂ := fun φ => ∫ x, schr ψ (∑ j, x j • ((fun k => algebraMap F (AF F) ((u j).1 k)), (fun k => algebraMap F (AF F) ((u j).2 k)))) φ 0 ∂μ
  have hint := GlobalTheory.T.schrodinger_lattice_sum_integrable F ψ hψ κ r u hli μ hμ
  have Φadd : ∀ φ ∈ schA F κ, ∀ φ' ∈ schA F κ, Φ (φ + φ') = Φ φ + Φ φ' := by
    intro φ hφ φ' hφ'
    simp only [Φ, schr_add_fun, Pi.add_apply]
    exact integral_add (hint φ hφ) (hint φ' hφ')
  have Φsmul : ∀ (c : ℂ), ∀ φ ∈ schA F κ, Φ (c • φ) = c * Φ φ := by
    intro c φ hφ
    simp only [Φ, schr_smul_fun, Pi.smul_apply, smul_eq_mul]
    exact integral_const_mul c _
  obtain ⟨lam, hlam⟩ := exists_linear_extension (schA F κ) Φ Φadd Φsmul
  have lam_adm : lam ∈ (adeleClass F).adm κ := by
    intro g hg
    obtain ⟨T, hT⟩ := GlobalTheory.T.schrodinger_lattice_distribution_continuous F ψ hψ κ r u hli μ hμ g hg
    refine ⟨T, fun f => ?_⟩
    rw [hlam _ (Submodule.subset_span ⟨f, g, hg, rfl⟩)]
    exact hT f
  have lam_inv : ∀ (t : AF F), ∀ v ∈ Λ, ∀ φ ∈ schA F κ,
      lam (schr ψ (t • ((fun k => algebraMap F (AF F) (v.1 k)), (fun k => algebraMap F (AF F) (v.2 k)))) φ) = lam φ := by
    intro t v hv φ hφ
    rw [hlam _ (GlobalTheory.HeisSchA.schr_mem_schA ψ hψ _ φ hφ), hlam φ hφ]
    exact GlobalTheory.T.schrodinger_theta_lattice_translation F ψ κ Λ hiso r u huΛ hsp μ hμ t v hv φ
  have lam_ne : ∃ φ ∈ schA F κ, lam φ ≠ 0 := by
    obtain ⟨φ, hφ, h⟩ := GlobalTheory.T.schrodinger_lattice_integral_nonvanishing F ψ hψ κ r u hli μ hμ
    exact ⟨φ, hφ, by rwa [hlam φ hφ]⟩
  obtain ⟨c, hc⟩ := GlobalTheory.T.adelicStoneVonNeumann_lagrangian_uniqueness F ψ hψ κ Λ hiso hrank l hl lam lam_adm hinv lam_inv lam_ne
  have hl_eq : ∀ φ ∈ schA F κ, ∀ t : ι → AF F,
      l (schr ψ (∑ i, t i • ((fun k => algebraMap F (AF F) ((w i).1 k)), (fun k => algebraMap F (AF F) ((w i).2 k)))) φ) = c * Φ (schr ψ (∑ i, t i • ((fun k => algebraMap F (AF F) ((w i).1 k)), (fun k => algebraMap F (AF F) ((w i).2 k)))) φ) := fun φ hφ t => by
    rw [hc _ (GlobalTheory.HeisSchA.schr_mem_schA ψ hψ _ φ hφ), hlam _ (GlobalTheory.HeisSchA.schr_mem_schA ψ hψ _ φ hφ)]
  have hint3 := GlobalTheory.T.lagrangian_lattice_theta_integral_formula F ψ hψ κ Λ hiso hrank r u huΛ hli hsp μ hμ ι w hw hnd ν hν
  refine ⟨fun φ hφ => ?_, ?_⟩
  · have : (fun t : ι → AF F => l (schr ψ (∑ i, t i • ((fun k => algebraMap F (AF F) ((w i).1 k)), (fun k => algebraMap F (AF F) ((w i).2 k)))) φ)) =
        fun t => c * Φ (schr ψ (∑ i, t i • ((fun k => algebraMap F (AF F) ((w i).1 k)), (fun k => algebraMap F (AF F) ((w i).2 k)))) φ) := funext (hl_eq φ hφ)
    rw [this]
    exact (hint3 φ hφ).const_mul c
  · let Ψ : ((κ → AF F) → ℂ) → ℂ := fun φ => ∫ t, Φ (schr ψ (∑ i, t i • ((fun k => algebraMap F (AF F) ((w i).1 k)), (fun k => algebraMap F (AF F) ((w i).2 k)))) φ) ∂ν
    have Ψadd : ∀ φ ∈ schA F κ, ∀ φ' ∈ schA F κ, Ψ (φ + φ') = Ψ φ + Ψ φ' := by
      intro φ hφ φ' hφ'
      have : (fun t : ι → AF F => Φ (schr ψ (∑ i, t i • ((fun k => algebraMap F (AF F) ((w i).1 k)), (fun k => algebraMap F (AF F) ((w i).2 k)))) (φ + φ'))) =
          fun t => Φ (schr ψ (∑ i, t i • ((fun k => algebraMap F (AF F) ((w i).1 k)), (fun k => algebraMap F (AF F) ((w i).2 k)))) φ) + Φ (schr ψ (∑ i, t i • ((fun k => algebraMap F (AF F) ((w i).1 k)), (fun k => algebraMap F (AF F) ((w i).2 k)))) φ') := by
        funext t
        rw [schr_add_fun]
        exact Φadd _ (GlobalTheory.HeisSchA.schr_mem_schA ψ hψ _ φ hφ) _ (GlobalTheory.HeisSchA.schr_mem_schA ψ hψ _ φ' hφ')
      simp only [Ψ]
      rw [this]
      exact integral_add (hint3 φ hφ) (hint3 φ' hφ')
    have Ψsmul : ∀ (a : ℂ), ∀ φ ∈ schA F κ, Ψ (a • φ) = a * Ψ φ := by
      intro a φ hφ
      have : (fun t : ι → AF F => Φ (schr ψ (∑ i, t i • ((fun k => algebraMap F (AF F) ((w i).1 k)), (fun k => algebraMap F (AF F) ((w i).2 k)))) (a • φ))) =
          fun t => a * Φ (schr ψ (∑ i, t i • ((fun k => algebraMap F (AF F) ((w i).1 k)), (fun k => algebraMap F (AF F) ((w i).2 k)))) φ) := by
        funext t
        rw [schr_smul_fun]
        exact Φsmul _ _ (GlobalTheory.HeisSchA.schr_mem_schA ψ hψ _ φ hφ)
      simp only [Ψ]
      rw [this]
      exact integral_const_mul a _
    obtain ⟨L, hL⟩ := exists_linear_extension (schA F κ) Ψ Ψadd Ψsmul
    refine ⟨c • L, ?_, fun φ hφ => ?_⟩
    · intro g hg
      obtain ⟨T, hT⟩ := GlobalTheory.T.lagrangian_lattice_theta_integral_bound F ψ hψ κ Λ hiso hrank r u huΛ hli hsp μ hμ ι w hw hnd ν hν g hg
      refine ⟨c • T, fun f => ?_⟩
      rw [LinearMap.smul_apply, hL _ (Submodule.subset_span ⟨f, g, hg, rfl⟩), ContinuousLinearMap.smul_apply]
      exact congrArg (c • ·) (hT f)
    · rw [LinearMap.smul_apply, hL φ hφ, smul_eq_mul, ← integral_const_mul]
      congr 1
      funext t
      rw [hl_eq φ hφ t]

end GlobalTheory.LagrangianAverage
