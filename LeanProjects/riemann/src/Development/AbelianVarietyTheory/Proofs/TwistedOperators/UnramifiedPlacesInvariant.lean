import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolMatchFiniteSetVacuum
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaEqB
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HoweDualityUnitary
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HoweDualityReal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneMemKAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InertPlaceLatticeStabiliserFixesVacuumStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilRepresentationLocalityUnitaryGroupWPairVWStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilOperatorLatticeStabiliserRightPreservesVacuuStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeisenbergSelfDualLatticeFixedFunctionsLineStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PsiUnramifiedAwayDifferent
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LatAtVSelfDual
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.EigenEqOne

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree

noncomputable section
namespace GlobalTheory.LocVacFix

theorem bad_finite (F : Type) [Field F] [NumberField F] :
    {v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F | differentIdeal ℤ (𝓞 F) ≤ v.asIdeal ∨ (6 : 𝓞 F) ∈ v.asIdeal}.Finite := by
  have hd : {v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F | v.asIdeal ∣ differentIdeal ℤ (𝓞 F)}.Finite :=
    Ideal.finite_factors (differentIdeal_ne_bot (A := ℤ) (B := 𝓞 F))
  have h6 : {v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F | v.asIdeal ∣ Ideal.span {(6 : 𝓞 F)}}.Finite := by
    refine Ideal.finite_factors ?_
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
    exact_mod_cast (show ((6 : ℕ) : 𝓞 F) ≠ 0 from Nat.cast_ne_zero.mpr (by norm_num))
  refine (hd.union h6).subset ?_
  rintro v (hv | hv)
  · exact Or.inl (Ideal.dvd_iff_le.mpr hv)
  · exact Or.inr (Ideal.dvd_iff_le.mpr ((Ideal.span_singleton_le_iff_mem _).mpr hv))

theorem two_three_of_six {F : Type} [Field F] [NumberField F] (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F)
    (h6 : (6 : 𝓞 F) ∉ v.asIdeal) : (2 : 𝓞 F) ∉ v.asIdeal ∧ 3 < Ideal.absNorm v.asIdeal := by
  have h2 : (2 : 𝓞 F) ∉ v.asIdeal := by
    intro h
    apply h6
    have e : (6 : 𝓞 F) = 3 * 2 := by norm_num
    rw [e]
    exact v.asIdeal.mul_mem_left 3 h
  refine ⟨h2, ?_⟩
  have hmem : ((Ideal.absNorm v.asIdeal : ℕ) : 𝓞 F) ∈ v.asIdeal := Ideal.absNorm_mem v.asIdeal
  have hz : Ideal.absNorm v.asIdeal ≠ 0 := by
    rw [Ne, Ideal.absNorm_eq_zero_iff]
    exact v.ne_bot
  have ho : Ideal.absNorm v.asIdeal ≠ 1 := by
    rw [Ne, Ideal.absNorm_eq_one_iff]
    exact v.isPrime.ne_top
  by_contra hle
  push_neg at hle
  generalize hN : Ideal.absNorm v.asIdeal = N at hmem hz ho hle
  interval_cases N
  · exact hz rfl
  · exact ho rfl
  · exact h2 (by exact_mod_cast hmem)
  · apply h6
    have e : (6 : 𝓞 F) = 2 * 3 := by norm_num
    rw [e]
    exact v.asIdeal.mul_mem_left 2 (by exact_mod_cast hmem)

theorem vac_fixed_split : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E) (a a' : ℕ) (G : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo σ a a') (X : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars F E)
    (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V G.W) (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V' G.W), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsTriple B G X om om' →
    ∀ (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F), (∀ w : HeightOneSpectrum (𝓞 E), ¬ Formalism.UG.IsInertAt F E v w) → v ∉ X.T →
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.PsiUnr B.ψ v → (2 : 𝓞 F) ∉ v.asIdeal → 3 < Ideal.absNorm v.asIdeal →
    ∀ k ∈ GlobalTheory.InertSph.KAt σ G.W v,
      GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Acts (GlobalTheory.AdelicU.evFin F v) (om (1, k)) (G.M.vac v) (G.M.vac v) := by
  intro F E _ _ _ _ _ σ B a a' G X om om' hT v hsp hvT hψ h2 h3 k hk
  obtain ⟨hSB, hne, θ, hθ, heig⟩ := hT.geo.hM.vac v
  obtain ⟨φ₁, hφ₁, hact⟩ := GlobalTheory.T.weilRepresentationLocality_unitaryGroupW_pairVW F E σ B a a' G X om om' hT v k hk.1 (G.M.vac v) hSB
  have heig₁ := GlobalTheory.T.weilOperator_latticeStabiliser_right_preserves_vacuumType F E σ B a a' G X om om' hT v k hk θ hθ (G.M.vac v) hSB φ₁ hφ₁ heig hact
  obtain ⟨c, hc⟩ := GlobalTheory.T.heisenbergSelfDualLattice_fixedFunctions_line F E σ B a a' G X om om' hT v hψ
    (GlobalTheory.PsiUnrSelfDual.latAtV_selfDual F E σ B a a' G X om om' hT v hψ) θ hθ (G.M.vac v) hSB hne heig
    φ₁ hφ₁ heig₁
  subst hc
  have hc1 : c = 1 := GlobalTheory.SplitVac.eigen_eq_one F E σ B a a' G X om om' hT v hsp hvT hψ h2 h3 k hk c hact
  rw [hc1, one_smul] at hact
  exact hact

theorem vac_fixed_cofinite : GlobalTheory.FunPr.Hypotheses₂ → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E) (a a' : ℕ) (G : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo σ a a') (X : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars F E)
    (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V G.W) (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V' G.W), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsTriple B G X om om' →
    ∃ S₀ : Finset (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F), ∀ v, v ∉ S₀ → ∀ k ∈ GlobalTheory.InertSph.KAt σ G.W v,
      GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Acts (GlobalTheory.AdelicU.evFin F v) (om (1, k)) (G.M.vac v) (G.M.vac v) := by
  intro _ F E _ _ _ _ _ σ B a a' G X om om' hT
  classical
  refine ⟨X.T ∪ (bad_finite F).toFinset, ?_⟩
  intro v hv k hk
  simp only [Finset.mem_union, Set.Finite.mem_toFinset, Set.mem_setOf_eq, not_or] at hv
  obtain ⟨hvT, hd, h6⟩ := hv
  have hψ := GlobalTheory.StdCharUnrF.psiUnr_of_not_le F B.ψ hT.base.std v hd
  obtain ⟨h2, h3⟩ := two_three_of_six v h6
  by_cases hin : ∃ w : HeightOneSpectrum (𝓞 E), Formalism.UG.IsInertAt F E v w
  · obtain ⟨w, hw⟩ := hin
    exact GlobalTheory.T.inert_place_lattice_stabiliser_fixes_vacuum F E σ B a a' G X om om' hT v w hw hvT k hk
  · push_neg at hin
    exact vac_fixed_split F E σ B a a' G X om om' hT v hin hvT hψ h2 h3 k hk

end GlobalTheory.LocVacFix
