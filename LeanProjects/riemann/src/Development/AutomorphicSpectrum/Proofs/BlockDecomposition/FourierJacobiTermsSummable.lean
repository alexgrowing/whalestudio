import Mathlib
import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.ThetaIdempotents.HeckeEta
import Formalism.LocalToGlobal.BesselHermitianTheta.LemmasWeil
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaLiftEisensteinLevelSubgroup
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TsumMeas
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ShAdd
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CentreCharacterProperties
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LatticeTranslationPreservedStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CoefficientHeisenbergEquivarianceStatement

noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS PositivityTheory.Rg.Rsw

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.FJE.Domination

theorem summable_tsum_le_of_shift {ι : Type*} [AddCommGroup ι] {F c : ι → ℝ} (ζ : ι) (hF : ∀ i, 0 ≤ F i)
    (h : ∀ i, F (i + ζ) ≤ c i) (hc : Summable c) : Summable F ∧ ∑' i, F i ≤ ∑' i, c i := by
  have hs : Summable (F ∘ Equiv.addRight ζ) := Summable.of_nonneg_of_le (fun _ => hF _) h hc
  refine ⟨(Equiv.addRight ζ).summable_iff.1 hs, ?_⟩
  rw [← (Equiv.addRight ζ).tsum_eq F]
  exact hs.tsum_le_tsum h hc

variable {D : D7} {n ρ p : ℕ} {hn : ρ + p = n}

theorem rt_add_add (η ζ : Matrix (Fin ρ) (Fin p) D.host.E) (y : Mx D ρ p) :
    GlobalTheory.CompanionTheory.FJE.rt (η + ζ) + y = GlobalTheory.CompanionTheory.FJE.rt η + (GlobalTheory.CompanionTheory.FJE.rt ζ + y) := by
  have : GlobalTheory.CompanionTheory.FJE.rt (η + ζ) = GlobalTheory.CompanionTheory.FJE.rt η + GlobalTheory.CompanionTheory.FJE.rt ζ := by
    ext i j
    exact map_add (incA D) _ _
  rw [this, add_assoc]

theorem norm_Wz_shift (M : Maps D hn) (m : Meas D ρ p) (ψ : AddChar (AF D.host.F) ℂ) (hψ : IsCharAF D.host.F ψ)
    (b₀ : HermE D ρ) (χ : (AE D)ˣ →* Circle) (s : ℂ) (f : G D n → ℂ) (hf : IsLaw χ s f) (g : G D n) (e : G D p)
    (η ζ₂ : Matrix (Fin ρ) (Fin p) D.host.E) (y' x₀ y₀ : Mx D ρ p) (z' : hermA D ρ)
    (hz : M.emb e * (M.nzx 0 x₀ * M.sh y₀) = M.nzx z' (GlobalTheory.CompanionTheory.FJE.rt ζ₂) * M.sh y' * M.emb e) :
    ‖Wz M m ψ b₀ f (M.sh (GlobalTheory.CompanionTheory.FJE.rt η + y') * M.emb e * g)‖ =
      ‖Wz M m ψ b₀ f (M.sh (η.map (incA D)) * M.emb e * (M.nzx 0 x₀ * (M.sh y₀ * g)))‖ := by
  have e1 : M.sh (η.map (incA D)) * M.emb e * (M.nzx 0 x₀ * (M.sh y₀ * g)) =
      M.sh (GlobalTheory.CompanionTheory.FJE.rt η) * (M.nzx z' (GlobalTheory.CompanionTheory.FJE.rt ζ₂) * (M.sh y' * M.emb e * g)) := by
    calc _ = M.sh (η.map (incA D)) * (M.emb e * (M.nzx 0 x₀ * M.sh y₀)) * g := by
          simp only [mul_assoc]
      _ = _ := by
          rw [hz]
          simp only [mul_assoc]
  have e2 : M.sh (GlobalTheory.CompanionTheory.FJE.rt η + y') * M.emb e * g =
      M.sh (GlobalTheory.CompanionTheory.FJE.rt η) * (M.sh y' * M.emb e * g) := by
    rw [← GlobalTheory.CompanionTheory.FJE.sh_add]
    simp only [mul_assoc]
  have hv : ‖GlobalTheory.CompanionTheory.FJE.chv ψ b₀ (GlobalTheory.CompanionTheory.FJE.rt ζ₂) (GlobalTheory.CompanionTheory.FJE.rt η)‖ = 1 := hψ.2.1 _
  rw [e1, e2, GlobalTheory.T.coefficient_heisenberg_equivariance M m ψ hψ b₀ χ s f hf, norm_mul, norm_mul,
    (GlobalTheory.CompanionTheory.FJE.CentralChar.chz_facts ψ hψ b₀).2.1, hv, one_mul, one_mul]

theorem apply_add_symm {A : Type*} [TopologicalSpace A] [AddCommGroup A] (T : (A × A) ≃ₜ+ (A × A)) {a₁ a₂ b₁ b₂ y : A}
    (h : T (a₁, a₂) = (b₁, b₂)) : T (a₁ + (T.symm (y, 0)).1, a₂ + (T.symm (y, 0)).2) = (b₁ + y, b₂) := by
  have e : (a₁ + (T.symm (y, 0)).1, a₂ + (T.symm (y, 0)).2) = (a₁, a₂) + T.symm (y, 0) := rfl
  rw [e, map_add, h, T.apply_symm_apply]
  simp

set_option maxHeartbeats 1000000 in

theorem domination : ∀ {D : D7} {n ρ p : ℕ} {hn : ρ + p = n} (M : Maps D hn) (m : Meas D ρ p)
    (ψ : AddChar (AF D.host.F) ℂ), IsCharAF D.host.F ψ → ∀ (b₀ : HermE D ρ) (χ : (AE D)ˣ →* Circle) (s : ℂ)
    (f : G D n → ℂ), IsLaw χ s f → ∀ g : G D n,
    (∀ C : Set (G D n), IsCompact C →
      ∃ c : GlobalTheory.Eis.Cosets (P D p) (GF D p) × Matrix (Fin ρ) (Fin p) D.host.E → ℝ, Summable c ∧
        ∀ g ∈ C, ∀ u, ‖Wz M m ψ b₀ f (M.sh (u.2.map (incA D)) * M.emb (u.1.out : GF D p) * g)‖ ≤ c u) →
    ∃ t : GlobalTheory.Eis.Cosets (P D p) (GF D p) → ℝ, Summable t ∧
      ∀ (q : GlobalTheory.Eis.Cosets (P D p) (GF D p)) (y : Mx D ρ p),
        Summable (fun η : Matrix (Fin ρ) (Fin p) D.host.E =>
          ‖Wz M m ψ b₀ f (M.sh (GlobalTheory.CompanionTheory.FJE.rt η + y) * M.emb (q.out : GF D p) * g)‖) ∧
        ∑' η : Matrix (Fin ρ) (Fin p) D.host.E,
          ‖Wz M m ψ b₀ f (M.sh (GlobalTheory.CompanionTheory.FJE.rt η + y) * M.emb (q.out : GF D p) * g)‖ ≤ t q := by
  intro D n ρ p hn M m ψ hψ b₀ χ s f hf g hdom
  obtain ⟨i1, i2, i3, i4, i5, K, hK, hKc⟩ := lattice_Mx D ρ p
  have hΦ : Continuous fun v : Mx D ρ p × Mx D ρ p => M.nzx 0 v.2 * (M.sh v.1 * g) := by
    have h1 : Continuous fun v : Mx D ρ p × Mx D ρ p => M.nzx 0 v.2 :=
      M.nzx_cont.comp (continuous_const.prodMk continuous_snd)
    have h2 : Continuous fun v : Mx D ρ p × Mx D ρ p => M.sh v.1 := M.sh_cont.comp continuous_fst
    exact h1.mul (h2.mul continuous_const)
  obtain ⟨c, hc, hb⟩ := hdom _ ((hK.prod hK).image hΦ)
  refine ⟨fun q => ∑' η, c (q, η), hc.prod, fun q y => ?_⟩
  obtain ⟨T, hT1, -, hT3⟩ := GlobalTheory.T.lattice_translation_preserved M ((q.out : GF D p) : G D p) (q.out : GF D p).2
  obtain ⟨a₁, ha₁, hy⟩ := hKc (T.symm (y, 0)).1
  obtain ⟨a₂, ha₂, hx⟩ := hKc (T.symm (y, 0)).2
  obtain ⟨ξ₁, rfl⟩ : ∃ ξ, GlobalTheory.CompanionTheory.FJE.rt ξ = a₁ := ha₁
  obtain ⟨ξ₂, rfl⟩ : ∃ ξ, GlobalTheory.CompanionTheory.FJE.rt ξ = a₂ := ha₂
  obtain ⟨ζ₁, ζ₂, hζ⟩ := hT1 ξ₁ ξ₂
  have hTv := apply_add_symm (y := y) T hζ
  obtain ⟨z', hz'⟩ := hT3 (GlobalTheory.CompanionTheory.FJE.rt ξ₁ + (T.symm (y, 0)).1) (GlobalTheory.CompanionTheory.FJE.rt ξ₂ + (T.symm (y, 0)).2)
  rw [hTv] at hz'
  refine summable_tsum_le_of_shift ζ₁ (fun _ => norm_nonneg _) (fun η => ?_) (hc.prod_factor q)
  rw [rt_add_add, norm_Wz_shift M m ψ hψ b₀ χ s f hf g _ η ζ₂ _ _ _ z' hz']
  exact hb _ ⟨(_, _), ⟨hy, hx⟩, rfl⟩ (q, η)

end GlobalTheory.CompanionTheory.FJE.Domination
