import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SRelOneOneIff
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.SiegelToroidalIntegral
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.GaloisCoverDescentAndCartesianSquares
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsDescentLinearisedLineBundleGaloisCover
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsAbelianTripleDescentGaloisCover
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSiegelObjectOfDescendedData
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianSchemeLawsUnconditional
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AbelianSchemeGerms

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZM GlobalTheory.SiegLev GlobalTheory.SiegelTor
open scoped CategoryTheory.Obj

noncomputable section

namespace GlobalTheory.SquareDescent

open GlobalTheory.CechPic

variable {S : Scheme.{0}}

theorem square_hom_ext (A : Over S) {Z : Scheme.{0}} {f g : Z ⟶ (A ⊗ A).left}
    (h₁ : f ≫ (fst A A).left = g ≫ (fst A A).left) (h₂ : f ≫ (snd A A).left = g ≫ (snd A A).left) : f = g :=
  pullback.hom_ext h₁ h₂

theorem eSec_fst (A : Over S) [GrpObj A] : eSec (A ⊗ A) ≫ (fst A A).left = eSec A := by
  show (η[A ⊗ A] ≫ fst A A).left = η[A].left
  simp [Hom.one_def]

theorem eSec_snd (A : Over S) [GrpObj A] : eSec (A ⊗ A) ≫ (snd A A).left = eSec A := by
  show (η[A ⊗ A] ≫ snd A A).left = η[A].left
  simp [Hom.one_def]

theorem eSec_lift_one (A : Over S) [GrpObj A] : eSec A ≫ (lift (1 : A ⟶ A) (𝟙 A)).left = eSec (A ⊗ A) := by
  apply pullback.hom_ext
  · change eSec A ≫ (lift (1 : A ⟶ A) (𝟙 A)).left ≫ (fst A A).left = eSec (A ⊗ A) ≫ (fst A A).left
    show (η[A] ≫ lift (1 : A ⟶ A) (𝟙 A) ≫ fst A A).left = (η[A ⊗ A] ≫ fst A A).left
    simp [Hom.one_def]
  · change eSec A ≫ (lift (1 : A ⟶ A) (𝟙 A)).left ≫ (snd A A).left = eSec (A ⊗ A) ≫ (snd A A).left
    show (η[A] ≫ lift (1 : A ⟶ A) (𝟙 A) ≫ snd A A).left = (η[A ⊗ A] ≫ snd A A).left
    simp [Hom.one_def]

theorem exists_bundle_descent : ∀ (X Y : Scheme.{0}) (π : X ⟶ Y) (Ga : Type) [Group Ga] (ρ : Ga → (X ⟶ X)) (A : Over X) [GrpObj A] (A₀ : Over Y) [GrpObj A₀] (φ : A.left ⟶ A₀.left) (ν : Ga → (A.left ⟶ A.left)) (P : LB (G2 A).left), IsGaloisCover Ga ρ π → IsAbelianScheme A → IsAbelianScheme A₀ → IsGrpPullback A A₀ π φ → IsGaloisCover Ga ν φ → (∀ a, IsGrpPullback A A (ρ a) (ν a)) → ν 1 = 𝟙 _ → (∀ a c, ν (a * c) = ν a ≫ ν c) → P.IsLB → (∃ t : (P.pull (lift (1 : A ⟶ A) (𝟙 A)).left).Gen, t.IsGen) → (∀ a, ∃ φ₂ : (G2 A).left ⟶ (G2 A).left, IsSquare (ν a) φ₂ ∧ LBIso P (P.pull φ₂)) → ∃ (P₀ : LB (G2 A₀).left) (φ₂ : (G2 A).left ⟶ (G2 A₀).left), P₀.IsLB ∧ IsSquare φ φ₂ ∧ LBIso P (P₀.pull φ₂) ∧ ∃ t : (P₀.pull (eSec (G2 A₀))).Gen, t.IsGen := by
  intro X Y π Ga _ ρ A _ A₀ _ φ ν P hπ hA hA₀ gp hν hνρ ν₁ νm hP ⟨t₀, ht₀⟩ hsq
  obtain ⟨hL, -⟩ := GlobalTheory.abelianSchemeLaws_all
  have hG := hL.globalFns
  have hA₂ : IsAbelianScheme (G2 A) := AbelianSchemeGerms.isAbelianScheme_tensor _ _ hA hA
  choose ν₂ hν₂ iν₂ using hsq
  have ν₂m : ∀ a c, ν₂ (a * c) = ν₂ a ≫ ν₂ c := fun a c => square_hom_ext A
    (by rw [(hν₂ _).1, Category.assoc, (hν₂ c).1, reassoc_of% (hν₂ a).1, νm])
    (by rw [(hν₂ _).2, Category.assoc, (hν₂ c).2, reassoc_of% (hν₂ a).2, νm])
  have wA : (fst A A).left ≫ A.hom = (snd A A).left ≫ A.hom := (Over.w (fst A A)).trans (Over.w (snd A A)).symm
  let φ₂ : (G2 A).left ⟶ (G2 A₀).left := pullback.lift ((fst A A).left ≫ φ) ((snd A A).left ≫ φ)
    (by rw [Category.assoc, Category.assoc, gp.1.w, reassoc_of% wA])
  have hsqφ : IsSquare φ φ₂ := ⟨pullback.lift_fst _ _ _, pullback.lift_snd _ _ _⟩
  have hpb := GlobalTheory.SiegelDescent.isPullback_square gp.1 φ₂ hsqφ
  have hu : ∀ a, ν₂ a ≫ (G2 A).hom = (G2 A).hom ≫ ρ a := fun a => by
    rw [← Over.w (fst A A), reassoc_of% (hν₂ a).1, (hνρ a).1.w, Category.assoc]
  have hinv : ∀ a, ν₂ a ≫ φ₂ = φ₂ := fun a => square_hom_ext A₀
    (by rw [Category.assoc, hsqφ.1, reassoc_of% (hν₂ a).1, hν.inv a])
    (by rw [Category.assoc, hsqφ.2, reassoc_of% (hν₂ a).2, hν.inv a])
  have hφ₂ : IsGaloisCover Ga ν₂ φ₂ := ((galoisCover_descent X Y π Ga ρ hπ).2.2 (G2 A).left (G2 A₀).left φ₂ ν₂
    (G2 A).hom (G2 A₀).hom hu hpb.w.symm).2 hpb.flip hinv
  have he : eSec (G2 A) ≫ (G2 A).hom = 𝟙 X := Over.w η[G2 A]
  have hτ : ∀ a, eSec (G2 A) ≫ ν₂ a = ρ a ≫ eSec (G2 A) := fun a => square_hom_ext A
    (by rw [Category.assoc, (hν₂ a).1, reassoc_of% eSec_fst A, GlobalTheory.TripleDescent.one_comm (hνρ a), Category.assoc,
      eSec_fst])
    (by rw [Category.assoc, (hν₂ a).2, reassoc_of% eSec_snd A, GlobalTheory.TripleDescent.one_comm (hνρ a), Category.assoc,
      eSec_snd])
  have hc0 : cls _ (pull_isLB hP (lift (1 : A ⟶ A) (𝟙 A)).left) = 0 := (cls_eq_zero_iff _).2 ⟨t₀, ht₀⟩
  have hPe : pull (eSec (G2 A)) (cls P hP) = 0 := by
    rw [← eSec_lift_one, pull_comp, ← cls_pull hP _ (pull_isLB hP _), hc0, map_zero]
  obtain ⟨r, hr⟩ := (cls_eq_zero_iff (pull_isLB hP (eSec (G2 A)))).1 hPe
  obtain ⟨u, hu₁, hu₂⟩ := GlobalTheory.TripleDescent.exists_linearisation hP (G2 A).hom (eSec (G2 A)) he (hG _ _ hA₂).2 ρ ν₂
    hπ.mul ν₂m hτ r hr iν₂
  obtain ⟨M, hM, iM⟩ := GlobalTheory.LinDescent.exists_descent_of_isGaloisCover _ _ φ₂ Ga ν₂ P hφ₂ hP u hu₁ hu₂
  have hMP : pull φ₂ (cls M hM) = cls P hP := ((cls_eq_iff hP (pull_isLB hM φ₂)).2 iM).symm
  have he₀ : eSec (G2 A₀) ≫ (G2 A₀).hom = 𝟙 Y := Over.w η[G2 A₀]
  have hφe : eSec (G2 A) ≫ φ₂ = π ≫ eSec (G2 A₀) := square_hom_ext A₀
    (by rw [Category.assoc, hsqφ.1, reassoc_of% eSec_fst A, GlobalTheory.TripleDescent.one_comm gp, Category.assoc, eSec_fst])
    (by rw [Category.assoc, hsqφ.2, reassoc_of% eSec_snd A, GlobalTheory.TripleDescent.one_comm gp, Category.assoc, eSec_snd])
  let P₀ : LB (G2 A₀).left := LB.LinComb M (K := Fin 2) ![𝟙 _, (G2 A₀).hom ≫ eSec (G2 A₀)] ![1, -1]
  have hP₀ : P₀.IsLB := LB.isLB_linComb hM _ _
  have hc : cls P₀ hP₀ = cls M hM - pull ((G2 A₀).hom ≫ eSec (G2 A₀)) (cls M hM) := by
    rw [cls_linComb hM, Fin.sum_univ_two]
    simp [pull_id, sub_eq_add_neg]
  refine ⟨P₀, φ₂, hP₀, hsqφ, ?_, ?_⟩
  · refine (cls_eq_iff hP (pull_isLB hP₀ φ₂)).1 ?_
    rw [cls_pull hP₀, hc, map_sub, ← pull_comp, hMP, ← Category.assoc, hpb.w, Category.assoc, ← hφe,
      ← Category.assoc, pull_comp, hMP, pull_comp, hPe, map_zero, sub_zero]
  · refine (cls_eq_zero_iff (pull_isLB hP₀ _)).1 ?_
    rw [cls_pull hP₀, hc, map_sub, ← pull_comp, ← Category.assoc, he₀]
    erw [Category.id_comp, sub_self]

end GlobalTheory.SquareDescent
