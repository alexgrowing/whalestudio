import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolActs
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilRepresentationIntegralAction
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsArchSchwartzDerivativeHeisenbergLine
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchHeisenbergDerivativesExistStatement

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

noncomputable section

namespace GlobalTheory.KHeisComm

variable {F : Type} [Field F] [NumberField F]

theorem archimedean_isomorphism_split_trivial {κ : Type} (z : κ → mixedEmbedding.mixedSpace F) :
    GlobalTheory.ArchIsom.r0 F κ (GlobalTheory.ArchIsom.splitEquiv F κ (z, 0)) = 1 := by
  change GlobalTheory.ArchIsom.g0 F κ 0 = 1
  simp [GlobalTheory.ArchIsom.g0, Set.indicator_of_mem (GlobalTheory.ArchIsom.zero_mem_intPts (F := F) κ)]

theorem tens_split {κ : Type} (φ : (κ → mixedEmbedding.mixedSpace F) → ℂ) (z : κ → mixedEmbedding.mixedSpace F) :
    tens (evI F) φ (GlobalTheory.ArchIsom.r0 F κ) (GlobalTheory.ArchIsom.splitEquiv F κ (z, 0)) = φ z := by
  have hz : (fun i => evI F (GlobalTheory.ArchIsom.splitEquiv F κ (z, 0) i)) = z :=
    funext fun i => GlobalTheory.ArchIsom.evI_splitEquiv κ _ i
  simp only [tens, hz, archimedean_isomorphism_split_trivial, mul_one]

open scoped Classical in

theorem proj_mem_adm {κ : Type} [Fintype κ] (x : κ → AF F) :
    (LinearMap.proj x : ((κ → AF F) → ℂ) →ₗ[ℂ] ℂ) ∈ (adeleClass F).adm κ := by
  intro g _
  refine ⟨g (fun i => (x i).2) • ((BoundedContinuousFunction.evalCLM ℂ
      (fun i => InfiniteAdeleRing.ringEquiv_mixedSpace F (x i).1)).comp
    (SchwartzMap.toBoundedContinuousFunctionCLM ℂ (κ → mixedEmbedding.mixedSpace F) ℂ)), fun f => ?_⟩
  simp [pureA, mul_comm]

end GlobalTheory.KHeisComm

open GlobalTheory.KHeisComm in
open scoped Classical in

theorem GlobalTheory.KHeisComm.actsD_heisLine_mat_mul : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ)
    (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ),
    GlobalTheory.ThK.IsPair B M χX χW om r s r' s' → ∀ k ∈ KInf σ X B.emb, ∀ u : Matrix (Fin n) (Fin d) (AE F E), At (evI F) u →
    ∀ f f₁ fk h : SInf F (Fin n × Fin d), ActsD (evI F) (M.heisLine B.ψ u) f f₁ → Acts (evI F) (om (k, 1)) f fk →
      Acts (evI F) (om (k, 1)) f₁ h → ActsD (evI F) (M.heisLine B.ψ (mat k * u)) fk h := by
  intro F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hP k _ u hu f f₁ fk h hD hA hA₁
  have hψ : IsStd B.ψ := hP.base.std
  have hS := IsUWeilPair.isUSplitting hP.weil
  obtain ⟨D, hDD⟩ := GlobalTheory.T.archHeisenbergDerivatives_exist F E σ (Fin n) (Fin d) (Fin n × Fin d) B.ψ (incM F X.J) (incM F W.J) M.co hψ
  obtain ⟨D₁, hD₁⟩ := GlobalTheory.HeisDeriv.exists_heisLine_deriv M B.ψ hψ (mat k * u)
  have hg0 := GlobalTheory.ArchIsom.standard_vector_mem_schwartz_bruhat (F := F) (Fin n × Fin d)

  have hf₁ : (D u f : SInf F (Fin n × Fin d)) = f₁ := by
    refine SchwartzMap.ext fun z => ?_
    set x := GlobalTheory.ArchIsom.splitEquiv F (Fin n × Fin d) (z, 0)
    have a1 : HasDerivAt (fun t => M.heisLine B.ψ u t (tens (evI F) (⇑f) (GlobalTheory.ArchIsom.r0 F (Fin n × Fin d))) x)
        (pureA F (⇑(D u f)) (GlobalTheory.ArchIsom.g0 F (Fin n × Fin d)) x) 0 :=
      (hDD u hu f).1 _ hg0 _ (proj_mem_adm x)
    have a2 := hD _ (GlobalTheory.ArchIsom.restriction_at_standard_point _ f) x
    have e := a1.unique a2
    rw [← GlobalTheory.ArchIsom.tensor_at_standard_point, tens_split, tens_split] at e
    exact e
  suffices e : h = D₁ fk by rw [e]; exact hD₁ fk
  refine SchwartzMap.ext fun z => ?_
  set x := GlobalTheory.ArchIsom.splitEquiv F (Fin n × Fin d) (z, 0)
  have hl := hS.adm (k, 1) _ (proj_mem_adm x)
  have b1 := (hDD u hu f).1 _ hg0 _ hl
  have hmem : ∀ g : SInf F (Fin n × Fin d), tens (evI F) (⇑g) (GlobalTheory.ArchIsom.r0 F (Fin n × Fin d)) ∈ schA F (Fin n × Fin d) :=
    fun g => (GlobalTheory.ArchIsom.restriction_at_standard_point _ g).2
  have hfun : (fun t : ℝ => ((LinearMap.proj x : ((Fin n × Fin d → AF F) → ℂ) →ₗ[ℂ] ℂ) ∘ₗ om (k, 1))
      (M.co.rho B.ψ (realAd F t • u) (pureA F (⇑f) (GlobalTheory.ArchIsom.g0 F (Fin n × Fin d))))) =
      fun t => M.heisLine B.ψ (mat k * u) t (tens (evI F) (⇑fk) (GlobalTheory.ArchIsom.r0 F (Fin n × Fin d))) x := by
    funext t
    rw [LinearMap.comp_apply, LinearMap.proj_apply, ← GlobalTheory.ArchIsom.tensor_at_standard_point, hS.impl (k, 1) _ _ (hmem f),
      hA _ (GlobalTheory.ArchIsom.restriction_at_standard_point _ f)]
    have hw : actAB (cA σ) ((k, 1) : UA σ X.J × UA σ W.J) (realAd F t • u) = realAd F t • (mat k * u) := by
      simp only [actAB, mat, OneMemClass.coe_one, Units.val_one, Matrix.transpose_one, Matrix.mul_one, Matrix.mul_smul]
    rw [hw]
    rfl
  have hval : ((LinearMap.proj x : ((Fin n × Fin d → AF F) → ℂ) →ₗ[ℂ] ℂ) ∘ₗ om (k, 1))
      (pureA F (⇑(D u f)) (GlobalTheory.ArchIsom.g0 F (Fin n × Fin d))) = h z := by
    rw [LinearMap.comp_apply, LinearMap.proj_apply, hf₁, ← GlobalTheory.ArchIsom.tensor_at_standard_point, hA₁ _ (GlobalTheory.ArchIsom.restriction_at_standard_point _ f₁),
      tens_split]
  rw [hfun, hval] at b1
  have b2 := hD₁ fk _ (GlobalTheory.ArchIsom.restriction_at_standard_point _ fk) x
  rw [tens_split] at b2
  exact b1.unique b2
