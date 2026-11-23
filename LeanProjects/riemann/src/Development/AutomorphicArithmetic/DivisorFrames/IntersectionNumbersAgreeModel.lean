import Mathlib
import Development.AutomorphicArithmetic.DivisorFrames.IntersectionNumberPullbackDegree
import Development.AutomorphicArithmetic.DivisorFrames.ExistsNormalCommonModel
import Development.AutomorphicArithmetic.DivisorFrames.PullCartierPicAgree
import Development.AutomorphicArithmetic.DivisorFrames.GenericPointResidueDegree
import Development.AutomorphicArithmetic.LocalEmbeddings.ConsAgree
import Development.AbelianVarietyTheory.Definitions.Divisors.ToIThCapDegOfAddNsmulDivP
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ChiLenPicPushforwardOfIsClosedImmersion
open CategoryTheory Limits AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.ConsGeo

private theorem embDeg_equiv {K L : Type} [Field K] [Field L] (ε : K ≃+* L) : embDeg ε.toRingHom = 1 := by
  unfold embDeg
  letI := ε.toRingHom.toAlgebra
  have e : K ≃ₗ[K] L := LinearEquiv.ofBijective (Algebra.linearMap K L) ε.bijective
  rw [← e.finrank_eq, Module.finrank_self]

private theorem embDeg_comp_equiv {K L M : Type} [Field K] [Field L] [Field M] (θ : K →+* L) (ε : L ≃+* M) :
    embDeg (ε.toRingHom.comp θ) = embDeg θ := by
  unfold embDeg
  letI := θ.toAlgebra
  letI := (ε.toRingHom.comp θ).toAlgebra
  have e : L ≃ₐ[K] M := AlgEquiv.ofRingEquiv (f := ε) (fun _ => rfl)
  exact e.toLinearEquiv.finrank_eq.symm

private theorem spectrumMap_comp {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap (g.comp f) = spMap g ≫ spMap f := by
  unfold spMap
  rw [← Spec.map_comp]
  rfl

theorem UpperTheory.intersection_numbers_agree_model :
    ∀ (k : Type) [Field k] [CharZero k] (X₁ X₂ : Scheme.{0}) [IsIntegral X₁] [IsIntegral X₂] (s₁ : X₁ ⟶ Sp k) (s₂ : X₂ ⟶ Sp k) (θ : X₂.functionField →+* X₁.functionField) (d : ℕ), IsProjOver s₁ → IsProjOver s₂ → topologicalKrullDim X₁ = d → topologicalKrullDim X₂ = d → spMap θ ≫ gpt X₂ ≫ s₂ = gpt X₁ ≫ s₁ → 0 < embDeg θ → ∀ (D₁ : Fin d → CartierDiv X₁) (D₂ : Fin d → CartierDiv X₂), (∀ i, DvrAgree θ (D₁ i) (D₂ i)) → (letI := algebraΓOfHom s₁; interNum k (GlobalTheory.structureModule X₁) fun i => toLB (D₁ i)) = (embDeg θ : ℤ) * (letI := algebraΓOfHom s₂; interNum k (GlobalTheory.structureModule X₂) fun i => toLB (D₂ i)) := by
  intro k _ _ X₁ X₂ _ _ s₁ s₂ θ d h₁ h₂ hd₁ hd₂ hθ hpos D₁ D₂ hD
  obtain ⟨W, _, p₁, p₂, ε, hn, hp, hs, hg₁, hg₂⟩ := UpperTheory.exists_normal_proj_common_model k X₁ X₂ s₁ s₂ θ h₁ h₂ hθ
  haveI := isNoetherian_of_isProjOver hp
  obtain ⟨a₁, b₁⟩ := UpperTheory.generic_point_residueDegree X₁ W p₁ ε.toRingHom hg₁
  obtain ⟨a₂, b₂⟩ := UpperTheory.generic_point_residueDegree X₂ W p₂ (ε.toRingHom.comp θ)
    (by rw [hg₂, spectrumMap_comp, Category.assoc])
  rw [embDeg_equiv] at b₁
  rw [embDeg_comp_equiv] at b₂
  have e₁ := UpperTheory.intersection_number_pullback_degree k X₁ W s₁ p₁ d h₁ hp hd₁ a₁ (by rw [b₁]; exact one_ne_zero)
    (fun i => toLB (D₁ i)) (fun i => isLB_toLB _)
  have e₂ := UpperTheory.intersection_number_pullback_degree k X₂ W s₂ p₂ d h₂ (hs ▸ hp) hd₂ a₂ (by rw [b₂]; exact hpos.ne')
    (fun i => toLB (D₂ i)) (fun i => isLB_toLB _)
  rw [b₁, Nat.cast_one, one_mul] at e₁
  rw [b₂, hs] at e₂
  rw [← e₁, ← e₂]
  letI := algebraΓOfHom (p₁ ≫ s₁)
  refine interNum_congr_cls k _ (fun i => LB.isLB_pull (isLB_toLB _) _) (fun i => LB.isLB_pull (isLB_toLB _) _)
    fun i => ?_
  rw [cls_pull (isLB_toLB _), cls_pull (isLB_toLB _), ← toPic_apply, ← toPic_apply]
  exact UpperTheory.pull_cartier_pic_agree X₁ X₂ W p₁ p₂ θ ε hn hg₁ hg₂ _ _ (hD i)
