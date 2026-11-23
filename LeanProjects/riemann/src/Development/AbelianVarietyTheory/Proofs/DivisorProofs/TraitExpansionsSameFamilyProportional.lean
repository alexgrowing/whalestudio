import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIntFamPull
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.CombEqZeroIffExpansionCombEqZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LabExtOfTrait
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.IsSemiAbelianOfGenericAbelianOfClosedIsGt
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsLeadOfUnif
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Definitions.Uniformization.SeriesFrame
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.FamMod
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.Mum

open ReciprocityTheory.ChartRestriction.G.DVR

theorem Trait.exp_pair : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (C : LabCover D) (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W] (T : Trait C W) (k : ℕ), 1 ≤ k → ∀ (F : IntFam (maximalIdeal R) D.toPre k) (s₁ s₂ : SecK C.P.L.L C.α k) (a₁ b₁ a₂ b₂ : W), T.Exp a₁ b₁ s₁ F → T.Exp a₂ b₂ s₂ F → ∀ (Z : Scheme.{0}) (p : Z ⟶ T.G.left) (p' : Z ⟶ C.A.A.left), p ≫ T.β = p' ≫ C.α → ∀ (z : Z) (J : (Z ⟶ C.G.left) → C.P.L.L.ι), Good C.P.L.L z J → gs p z ⊤ (scal T.G.hom (b₂ * a₁)) * sval s₁ p' z J = gs p z ⊤ (scal T.G.hom (b₁ * a₂)) * sval s₂ p' z J := by
  intro R _ _ _ hB D C W _ _ _ T k hk F s₁ s₂ a₁ b₁ a₂ b₂ h₁ h₂ Z p p' hpp' z J hJ
  obtain ⟨σ₁, ⟨τ₁, f₁, hc₁, hp₁, he₁⟩, hg₁⟩ := h₁
  obtain ⟨σ₂, ⟨τ₂, f₂, hc₂, hp₂, he₂⟩, hg₂⟩ := h₂
  have hf : f₁ = f₂ := funext fun x =>
    (SecPull.existsUnique_secPull _ _ _ _ _ _ _ D.toPre.P.isLB T.D'.toPre.P.isLB T.hD.w T.hD.w_gen (Fin 4)
      (T.D'.toPre.famφB x) (D.toPre.famφB (T.hD.xe x)) (DegPre.famε k) _ (ExpGTrans.famφB_pull T.hD x)
      (F.f (T.hD.xe x))).unique (hp₁ x) (hp₂ x)
  subst hf
  have hW := T.cdvr
  have := hW.1
  have := hW.2.2
  have bW : AdmBase W (maximalIdeal W) := ⟨inferInstance, inferInstance, inferInstance, hW.2.1⟩
  have hGs : IsSemiAbelian T.G := by
    obtain ⟨bc, mbc, -⟩ := grpPullback_iso T.cart (isGrpPullback_pullback C.G T.ξ)
    exact GlobalTheory.isSemiAbelian_of_grpIso bc (IsSemiAbelian.pullback T.ξ C.G C.semi)
  have hGc := hGs.geomConnected
  have H := (comb_eq_zero_iff_expansion_comb_eq_zero W _ bW T.D' T.A T.G T.U.toUnifPre k 2 ![1, -1] ![τ₁, τ₂]
    ![f₁, f₁] (fun i => by fin_cases i; exacts [he₁, he₂])).2 hGc (fun α j => by simp [Fin.sum_univ_two, Out.scal])
  have hτ : τ₁ = τ₂ := SecOps.sec_ext fun j => by
    have := H j
    simpa [Fin.sum_univ_two, Out.scal, add_neg_eq_zero] using this
  subst hτ
  choose J' hJ' using fun ψ : Z ⟶ T.G.left => exists_chart T.U.LG.isLB (ψ z)
  have c₁ := hc₁ Z p z J J' hJ hJ'
  have c₂ := hc₂ Z p z J J' hJ hJ'
  have g₁ := hg₁ Z p p' hpp' z J hJ
  have g₂ := hg₂ Z p p' hpp' z J hJ
  have m : ∀ a b : W, gs p z ⊤ (scal T.G.hom (a * b)) = gs p z ⊤ (scal T.G.hom a) * gs p z ⊤ (scal T.G.hom b) :=
    fun a b => by
      rw [show scal T.G.hom (a * b) = scal T.G.hom a * scal T.G.hom b by simp only [scal, map_mul]]
      exact gs_mul p z ⊤ (show p z ∈ (⊤ : T.G.left.Opens) from trivial) _ _
  have key : gs p z ⊤ (scal T.G.hom b₂) * sval σ₁ p z J = gs p z ⊤ (scal T.G.hom b₁) * sval σ₂ p z J := by
    rw [c₁, c₂]; ring
  rw [g₁, g₂] at key
  rw [m, m]
  linear_combination key

end GlobalTheory.Mum
