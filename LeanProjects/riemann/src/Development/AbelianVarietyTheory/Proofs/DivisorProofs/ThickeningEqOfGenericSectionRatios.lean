import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.FormalEnd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SecRatioEqRefl
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordConstruction
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FstGenericAppInjective
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SecRatioAppRestrict
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormalEndSecCoNonzeroLift
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemBasicOpenOfSectionRatioEqBasePointStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisedGroupMorphismsAgreeOfSectionRatiosStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SemiAbelianThickeningHomEqOfEqOnOpenStatement

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.Mum

theorem fstG_comm_thick (R : Type) [CommRing R] (I : Ideal R) (e : ℕ) (G : Over (Sp R)) (g : G ⟶ G) :
    ((Over.pullback (thick R I e)).map g).left ≫ (fstG I e G).left = (fstG I e G).left ≫ g.left := by
  first
    | (have := congrArg CommaMorphism.left ((Over.mapPullbackAdj (thick R I e)).counit.naturality g)
       simpa [fstG] using this)
    | (simp [fstG]; exact pullback.lift_fst _ _ _)

theorem thick_eq_of_ratios : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ U : Unif (maximalIdeal R) D A G, ∀ (a a' : D.toPre.P.A ⟶ D.toPre.P.A) (h h' : D.toPre.X →+ D.toPre.X), EndData D.toPre a a' h h' → ∀ b, FormalEnd U.toUnifPre a h' b → ∀ (N : ℕ) (S : ∀ k : ℕ, H0 U.LG.L k → H0 U.LG.L (N * k)), (∀ (k e : ℕ) (s₁ s₂ : H0 U.LG.L k), SecRatioEq U.LG.L ((b e).left ≫ (fstG (maximalIdeal R) e G).left) (fstG (maximalIdeal R) e G).left s₁ s₂ (S k s₁) (S k s₂)) → (∀ k : ℕ, 3 ≤ k → ∃ s₀ : H0 U.LG.L k, SecCoNonzero U.LG.L ((b 0).left ≫ (fstG (maximalIdeal R) 0 G).left) (fstG (maximalIdeal R) 0 G).left s₀ (S k s₀)) → ∀ φ : (Over.pullback (jK R)).obj G ⟶ (Over.pullback (jK R)).obj G, (∀ (k : ℕ) (s₁ s₂ : H0 U.LG.L k), SecRatioEq U.LG.L (φ.left ≫ pullback.fst G.hom (jK R)) (pullback.fst G.hom (jK R)) s₁ s₂ (S k s₁) (S k s₂)) → ∀ g : G ⟶ G, IsMonHom g → (Over.pullback (jK R)).map g = φ → ∀ e, (Over.pullback (thick R (maximalIdeal R) e)).map g = b e := by
  intro R _ _ _ hB D A G _ _ hG U a a' h h' hE b hb N S hS hC φ hφ g hg hgφ e
  have hcomm : φ.left ≫ pullback.fst G.hom (jK R) = pullback.fst G.hom (jK R) ≫ g.left := by
    subst hgφ
    first
      | (simp; done)
      | (simp; exact pullback.lift_fst _ _ _)
      | exact pullback.lift_fst _ _ _
  have hGI : GeometricallyIntegral G.hom := GlobalTheory.geometricallyIntegral_of_isSemiAbelian G (h := hG)
  have hfin : Finite (irreducibleComponents (Sp R)) := by
    rw [irreducibleComponents_eq_singleton]
    infer_instance
  have hfl : Flat G.hom := by
    obtain ⟨_, hsm, -, -, -, -⟩ := hG
    infer_instance
  have hred : IsReduced G.left :=
    GeometricallyReduced.isReduced_of_flat_of_finite_irreducibleComponents G.hom
  have hdom : IsDominant (pullback.fst G.hom (jK R)) :=
    isDominant_genericFibre_of_flat R (FractionRing R) G.hom

  have hGrat : ∀ (k : ℕ) (s₁ s₂ : H0 U.LG.L k),
      SecRatioEq U.LG.L g.left (𝟙 G.left) s₁ s₂ (S k s₁) (S k s₂) := by
    intro k s₁ s₂
    apply SecRatioEq.of_isDominant (pullback.fst G.hom (jK R))
    rw [← hcomm, Category.comp_id]
    exact hφ k s₁ s₂

  have hxc : ((Over.pullback (thick R (maximalIdeal R) e)).map g).left ≫ (fstG (maximalIdeal R) e G).left =
      (fstG (maximalIdeal R) e G).left ≫ g.left := fstG_comm_thick R (maximalIdeal R) e G g
  have hxrat : ∀ (k : ℕ) (s₁ s₂ : H0 U.LG.L k),
      SecRatioEq U.LG.L (((Over.pullback (thick R (maximalIdeal R) e)).map g).left ≫ (fstG (maximalIdeal R) e G).left)
        (fstG (maximalIdeal R) e G).left s₁ s₂ (S k s₁) (S k s₂) := by
    intro k s₁ s₂
    have := secRatioEq_comp U.LG.L g.left (𝟙 G.left) (fstG (maximalIdeal R) e G).left s₁ s₂ (S k s₁) (S k s₂)
      (hGrat k s₁ s₂)
    rwa [Category.comp_id, ← hxc] at this
  have hxmon : IsMonHom ((Over.pullback (thick R (maximalIdeal R) e)).map g) := inferInstance
  obtain ⟨k₀, hk₀, hnear⟩ := GlobalTheory.T.uniformisedGroup_morphisms_agree_of_sectionRatios R hB D A G hG U
  obtain ⟨s₀, hs₀⟩ := hC k₀ hk₀

  obtain ⟨y, i'', i', hy1, hy2⟩ :=
    formalEnd_secCoNonzero_lift R hB D A G hG U a h' b hb k₀ (N * k₀) s₀ (S k₀ s₀) hs₀ e
  obtain ⟨i, hy0⟩ := GlobalTheory.T.mem_basicOpen_of_sectionRatioEq_basePoint R hB D A G hG U e k₀ (N * k₀) hk₀
    ((Over.pullback (thick R (maximalIdeal R) e)).map g) (S k₀) (hxrat k₀) y s₀ i' hy2
  obtain ⟨W, hyW, hW⟩ := hnear e k₀ (N * k₀) le_rfl ((Over.pullback (thick R (maximalIdeal R) e)).map g) (b e)
    (S k₀) (hxrat k₀) (fun s₁ s₂ => hS k₀ e s₁ s₂) y s₀ i i' i'' hy0 hy2 hy1
  exact GlobalTheory.T.semiAbelian_thickening_hom_eq_of_eq_on_open R hB D A G hG U e _ (b e) hxmon (hb.1 e) W y hyW hW

end GlobalTheory.Mum
