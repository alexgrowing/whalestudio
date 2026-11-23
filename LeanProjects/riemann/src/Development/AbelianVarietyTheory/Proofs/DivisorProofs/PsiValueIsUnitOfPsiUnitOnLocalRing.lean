import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.TateProductRigidificationTrivial
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordConstruction
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnramSub
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.PsiUnitOnOfFixedOverUnramifiedExtension
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section
namespace GlobalTheory.PsiValUnit
open GlobalTheory.BXOf

theorem psi_val_unit_of_psiUnitOn : ∀ (R : Type) [CommRing R] [IsDomain R] (D : DegPre R) (W : (Sp R).Opens) (χ : D.X), PsiUnitOn D χ W → ∀ (F : Type) [Field F] [Algebra (FractionRing R) F] (T : Subring F) [IsLocalRing T] (φ₁ : R →+* T), (∀ r, (φ₁ r : F) = algebraMap (FractionRing R) F (algebraMap R _ r)) → spMap φ₁ (closedPoint T) ∈ W → ∀ (J₀ : D.P.A.left → D.P.L.ι), (∀ x, x ∈ D.P.L.U (J₀ x)) → ∀ (J : ((TF (R := R) F).left ⟶ D.P.A.left) → D.P.L.ι), (∀ ψ : Sp T ⟶ D.P.A.left, J (spMap T.subtype ≫ ψ) = J₀ (ψ (closedPoint T))) → ∃ u : Tˣ, (GlobalTheory.BXOf.sig F (val (D.psi χ) ((𝟙 (TF (R := R) F) :).left ≫ jFK (R := R) F) (closedPoint F) J) : F) = ((u : T) : F) := by
  intro R _ _ D W χ hW F _ _ T _ φ₁ hφ hP J₀ h₀ J hJ
  have hmem : spMap φ₁ (closedPoint T) ∈ W ⊓ (D.c χ).left ⁻¹ᵁ D.P.L.U (J₀ ((D.c χ).left (spMap φ₁ (closedPoint T)))) :=
    ⟨hP, h₀ _⟩
  obtain ⟨V, hVa, hPV, hVle⟩ := (TopologicalSpace.Opens.isBasis_iff_nbhd.mp (Sp R).isBasis_affineOpens) hmem
  set j₀ := J₀ ((D.c χ).left (spMap φ₁ (closedPoint T))) with hj₀
  have hxK : D.xK χ = jK R ≫ (D.c χ).left := by
    show (toUnit (TK R) ≫ D.c χ).left = _
    rw [Over.comp_left]
    congr 1
  have hwch : jK R ⁻¹ᵁ V ≤ (LB.LinComb D.P.L (K := PUnit) (fun _ => D.xK χ) (fun _ => -1)).U (fun _ => j₀) :=
    fun x hx => Set.mem_iInter.2 fun _ => by
      show D.xK χ x ∈ D.P.L.U j₀
      rw [hxK]
      exact (hVle hx).2
  obtain ⟨r, hr, hre⟩ := hW (fun _ => j₀) V hVa (fun x hx => (hVle hx).1) (fun x hx => (hVle hx).2) hwch
  have hcomp : ((𝟙 (TF (R := R) F) :).left ≫ jFK (R := R) F) ≫ jK R = spMap T.subtype ≫ spMap φ₁ := by
    rw [Over.id_left, Category.id_comp]
    rw [jFK, jK, spMap, spMap, ← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp]
    congr 2
    exact (RingHom.ext hφ).symm
  have hch : J (((𝟙 (TF (R := R) F) :).left ≫ jFK (R := R) F) ≫ D.xK χ) = j₀ := by
    have e : ((𝟙 (TF (R := R) F) :).left ≫ jFK (R := R) F) ≫ D.xK χ = spMap T.subtype ≫ (spMap φ₁ ≫ (D.c χ).left) := by
      rw [hxK, ← Category.assoc, hcomp, Category.assoc]
    rw [e, hJ]
    rfl
  have e1 := val_of (D.psi χ) ((𝟙 (TF (R := R) F) :).left ≫ jFK (R := R) F) (closedPoint F) J (fun _ => j₀) (fun _ => hch)
  have hin : jK R (((𝟙 (TF (R := R) F) :).left ≫ jFK (R := R) F) (closedPoint F)) ∈ V := by
    show (((𝟙 (TF (R := R) F) :).left ≫ jFK (R := R) F) ≫ jK R) (closedPoint F) ∈ V
    rw [hcomp]
    exact top_le_of_mem (spMap φ₁) hPV trivial
  have e2 : res hwch ((D.psi χ).s fun _ => j₀) = pullU (jK R) V hr.unit := Units.ext hre.symm
  have e3 := gm_res ((𝟙 (TF (R := R) F) :).left ≫ jFK (R := R) F) (closedPoint F) hwch hin ((D.psi χ).s fun _ => j₀)
  rw [e2, gm_pull ((𝟙 (TF (R := R) F) :).left ≫ jFK (R := R) F) (jK R) (closedPoint F) V hin hr.unit, hcomp] at e3
  have e4 := sig_nat T.subtype (spMap φ₁) hPV hr.unit
  refine ⟨sig T (gm (spMap φ₁) (closedPoint T) V hr.unit), ?_⟩
  exact (congrArg (fun u => (sig F u : F)) (e1.trans e3.symm)).trans (congrArg Units.val e4).symm

end GlobalTheory.PsiValUnit
