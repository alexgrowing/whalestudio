import Mathlib
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.KFiniteVectors.KFiniteThetaLifts.PureThetaTransfer.REALTH
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FieldSphericalVectorTheta
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SplitOrInertOfUnramified
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsUnramifiedCharCompUnitsMap
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsStdInvAndTrivialAndNontrivial
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IntegrableMulIntInd
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DifferentIdealRat
open NumberField IsDedekindDomain MeasureTheory Matrix GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic Ad3 Ad3.K Ad3.K.QuadraticBaseChangeGL3 Ad3.K.QuadraticBaseChangeGL3.Th ComplexConjugate
open GroundTheory.Automorphic.GodementSection (localChar)
open GroundTheory.Global.AdicLiesOver
open scoped NumberField.AdeleRing ValuativeRel

noncomputable section

namespace GlobalTheory.CompanionTheory.StdSphOf

theorem indicator_prod_integers (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] :
    IsLocallyConstant (Set.indicator {x : F × F | x.1 ∈ 𝒪[F] ∧ x.2 ∈ 𝒪[F]} (1 : F × F → ℂ)) ∧
      HasCompactSupport (Set.indicator {x : F × F | x.1 ∈ 𝒪[F] ∧ x.2 ∈ 𝒪[F]} (1 : F × F → ℂ)) := by
  have hset : ({x : F | x ∈ 𝒪[F]} : Set F) = (valBall F 0 : Set F) := by
    rw [coe_valBall_zero]; rfl
  have hc1 : IsClopen ({x : F | x ∈ 𝒪[F]} : Set F) := by
    rw [hset]; exact ⟨isClosed_valBall 0, isOpen_valBall 0⟩
  have hk1 : IsCompact ({x : F | x ∈ 𝒪[F]} : Set F) := by
    rw [hset]; exact isCompact_valBall 0
  have hS : ({x : F × F | x.1 ∈ 𝒪[F] ∧ x.2 ∈ 𝒪[F]} : Set (F × F)) =
      ({x : F | x ∈ 𝒪[F]} : Set F) ×ˢ ({x : F | x ∈ 𝒪[F]} : Set F) := rfl
  have hclopen : IsClopen ({x : F × F | x.1 ∈ 𝒪[F] ∧ x.2 ∈ 𝒪[F]} : Set (F × F)) := by
    rw [hS]; exact hc1.prod hc1
  have hcomp : IsCompact ({x : F × F | x.1 ∈ 𝒪[F] ∧ x.2 ∈ 𝒪[F]} : Set (F × F)) := by
    rw [hS]; exact hk1.prod hk1
  refine ⟨?_, HasCompactSupport.intro hcomp fun x hx => Set.indicator_of_notMem hx _⟩
  refine (IsLocallyConstant.iff_exists_open _).2 fun x => ?_
  by_cases hx : x ∈ ({x : F × F | x.1 ∈ 𝒪[F] ∧ x.2 ∈ 𝒪[F]} : Set (F × F))
  · exact ⟨_, hclopen.isOpen, hx, fun y hy => by
      rw [Set.indicator_of_mem hy, Set.indicator_of_mem hx]; rfl⟩
  · exact ⟨_, hclopen.compl.isOpen, hx, fun y hy => by
      rw [Set.indicator_of_notMem hy, Set.indicator_of_notMem hx]⟩

theorem stdsph : ∀ (K : Type) [Field K] [NumberField K], Ad3.K.QuadraticBaseChangeGL3.Th.SPHF → Ad3.K.QuadraticBaseChangeGL3.Th.SPHS →
    Ad3.K.QuadraticBaseChangeGL3.Th.LAMU → Ad3.K.QuadraticBaseChangeGL3.Th.NORMU → Ad3.K.QuadraticBaseChangeGL3.Th.STDSPH K := by
  intro K _ _ hF hS hL hN h2 c v hU W' hW
  have hψ : IsStd (GP.psiF v) := GlobalTheory.CompanionTheory.StdCharQ.stdChar v
  obtain ⟨hχc, hχ1, hχ0⟩ :=
    (GlobalTheory.CompanionTheory.StdAddChar.isStd_inv_and_trivial_and_nontrivial (Qv v) _ hψ).1
  rcases hW with ⟨w₁, w₂, i₁, i₂, hne, rfl⟩ | ⟨w, i, hu, σ, η, hσ, hη, rfl⟩
  · haveI := i₁
    haveI := i₂
    have r₁ : IsUnramifiedChar (cAt c v w₁) :=
      GlobalTheory.CompanionTheory.SphTheta.isUnramifiedChar_comp_unitsMap (Qv v) (Kv K w₁) (localChar c w₁) (hU w₁).1
    have r₂ : IsUnramifiedChar (cAt c v w₂) :=
      GlobalTheory.CompanionTheory.SphTheta.isUnramifiedChar_comp_unitsMap (Qv v) (Kv K w₂) (localChar c w₂) (hU w₂).1
    obtain ⟨hlc, hcs⟩ := indicator_prod_integers (Qv v)
    exact ⟨hS (Qv v) _ hχc hχ1 hχ0 _ _ r₁ r₂, Or.inl ⟨w₁, w₂, i₁, i₂, hne,
      Submodule.subset_span ⟨_, hlc, hcs, 1, by simp⟩, rfl⟩⟩
  · haveI := i
    rcases GlobalTheory.CompanionTheory.QuadPlace.split_or_inert_of_unramified K h2 v (fun w _ => (hU w).2) with
      ⟨a, b, ha, hb, hab⟩ | ⟨w', hw', -, hf, hord⟩
    · exact absurd ((hu a ha).trans (hu b hb).symm) hab
    obtain rfl : w' = w := hu w' hw'
    have hres : residueCard (Kv K w') = residueCard (Qv v) ^ 2 := GlobalTheory.CompanionTheory.NormGauss.card_E hf hord
    have hcont : Continuous (algebraMap (Qv v) (Kv K w')) := continuous_adicCompletionMap v w'
    have hcu := (hU w').1
    have hsph := hF (Qv v) _ hχc hχ1 (Kv K w') hf hcont σ hσ η hη hχ0 hres (localChar c w') hcu
    obtain ⟨hlam, hneg⟩ := hL (Qv v) _ hχc hχ1 (Kv K w') hf hcont σ hσ η hη hχ0 hres
    have hWm := GlobalTheory.CompanionTheory.NormModulus.wMod (Qv v) _ hχc hχ1 (Kv K w') hf hcont σ hσ η hη
    have hSB : Set.indicator {x : Kv K w' | x ∈ 𝒪[Kv K w']} (1 : Kv K w' → ℂ) ∈
        GL2LocalData.SBc (Qv v) (Kv K w') (localChar c w') := by
      obtain ⟨h1, h3⟩ := GlobalTheory.CompanionTheory.SphFUnr.indicator_integers_mem_SBE (Kv K w')
      refine ⟨h1, h3, fun u hu' x => ?_⟩
      have hm : modulus (u : Kv K w') = 1 := by
        have h := hWm (u : Kv K w')
        rw [hu'] at h
        simp only [modulus_one] at h
        exact_mod_cast h
      have hcone : localChar c w' u = 1 :=
        MonoidHom.mem_ker.1 (hcu (ord_eq_zero_iff_mem.1 (modulus_eq_one_iff.1 hm).2))
      rw [GlobalTheory.CompanionTheory.PiKFUnr.indicator_mul_of_modulus_eq_one hm x, hcone]
      simp
    refine ⟨hsph, Or.inr ⟨w', i, hu, σ, η, hσ, hη, Submodule.subset_span ⟨_, hSB, 1, by simp⟩, ?_⟩⟩
    rw [hlam, hneg]
    simp

end GlobalTheory.CompanionTheory.StdSphOf
