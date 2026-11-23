import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.FormalEnd
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordConstruction
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsRigidTranslatePrincipalPolarisationOrderTw
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMumfordBundlePullbackGrpPullback
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianSchemeLawsWithoutCohomology
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.PelObjectClassPrimAndIsoClosed
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsThetaOfTranslDiff
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.BaseTransl

variable {S S' : Scheme.{0}} {f : S' ⟶ S} {G : Over S} [GrpObj G] {G' : Over S'} [GrpObj G']
  {g : G'.left ⟶ G.left}

theorem toBase_injective (hg : IsPullback g G'.hom G.hom f) {T : Over S'} {x x' : T ⟶ G'}
    (h : toBase hg.w x = toBase hg.w x') : x = x' := by
  have e : x.left ≫ g = x'.left ≫ g := congrArg (fun z => z.left) h
  ext
  exact hg.hom_ext e (by rw [Over.w x, Over.w x'])

theorem toBase_one (hg : IsPullback g G'.hom G.hom f)
    (hm : ∀ (T : Over S') (x y : T ⟶ G'), toBase hg.w (x * y) = toBase hg.w x * toBase hg.w y) (T : Over S') :
    toBase hg.w (1 : T ⟶ G') = 1 := by
  have := hm T 1 1
  rw [_root_.mul_one] at this
  exact mul_eq_left.1 this.symm

theorem isGrpPullback_of_toBase (hg : IsPullback g G'.hom G.hom f)
    (hm : ∀ (T : Over S') (x y : T ⟶ G'), toBase hg.w (x * y) = toBase hg.w x * toBase hg.w y) :
    IsGrpPullback G' G f g := by
  refine ⟨hg, fun T x y x₀ y₀ hx hy => ?_⟩
  have ex : x₀ = toBase hg.w x := by ext; exact hx
  have ey : y₀ = toBase hg.w y := by ext; exact hy
  rw [ex, ey, ← hm]
  rfl

open GlobalTheory.RigidTranslate in

theorem exists_baseChange_translate : ∀ (K K' : Type) [Field K] [Field K'] (io : K →+* K') (A : PolAV (Sp K)) (y : Over.mk (spMap io) ⟶ A.A), y * y = 1 → ∃ (A₁ : PolAV (Sp K')) (α₁ : A₁.A.left ⟶ A.A.left) (α₁₂ : (G2 A₁.A).left ⟶ (G2 A.A).left) (t : 𝟙_ (Over (Sp K')) ⟶ A₁.A), IsGrpPullback A₁.A A.A (spMap io) α₁ ∧ IsSquare α₁ α₁₂ ∧ LBIso (abelian₂ A₁.A A₁.L) ((abelian₂ A.A A.L).pull α₁₂) ∧ t.left ≫ α₁ = y.left ∧ LBIso A₁.L (GlobalTheory.RigidTranslate.rigTransl (A.L.pull α₁) t) := by
  intro K K' _ _ io A y hy
  obtain ⟨P, g, hg, -, hm, w, hw⟩ := GlobalTheory.polBaseChange_holds (Sp K) (Sp K') (spMap io) A
  have hpb : IsGrpPullback P.A A.A (spMap io) g := isGrpPullback_of_toBase hg hm
  have := P.isAb.comm
  have := P.isAb.proper
  have := A.isAb.comm
  let t₀ : 𝟙_ (Over (Sp K')) ⟶ P.A := Over.homMk (hg.lift y.left (𝟙 _) (by rw [Over.w y, Category.id_comp]; rfl))
    (hg.lift_snd _ _ _)
  have ht₀ : t₀.left ≫ g = y.left := hg.lift_fst _ _ _
  let e : Over.mk ((𝟙_ (Over (Sp K'))).hom ≫ spMap io) ⟶ Over.mk (spMap io) := Over.homMk (𝟙 _) (Category.id_comp _)
  have hte : toBase hg.w t₀ = e ≫ y := by
    ext
    exact ht₀.trans (Category.id_comp _).symm
  have htt : t₀ * t₀ = 1 := by
    refine toBase_injective hg ?_
    rw [hm, hte, toBase_one hg hm, ← MonObj.comp_mul, hy, MonObj.comp_one]
  have hwL : LBIso (A.L.pull g) P.L := ⟨w, hw⟩
  obtain ⟨c, hc⟩ := GlobalTheory.Moduli.cube_of_isLB _ P P.L P.isLB
  let A₁ : PolAV (Sp K') :=
    { A := P.A, isAb := P.isAb, g := P.g, smoothDim := P.smoothDim, L := rigTransl P.L t₀
      isLB := DVR.linComb_isLB _ P.isLB _ _
      rigid := rigidified_rigTransl P.isLB
      sym := sym_rigTransl htt P.isLB P.sym
      ample := relAmple_rigTransl htt P.isLB P.ample
      ktriv := kTriv_rigTransl htt P.isLB P.ktriv }
  obtain ⟨β₂, hsq, hlam⟩ := GlobalTheory.Mum.lbIso_lam_pull_of_isGrpPullback _ _ _ A.A P.A g hpb
  have hLamA : (abelian₂ A.A A.L).IsLB := DVR.linComb_isLB _ A.isLB _ _
  have hLamP : (abelian₂ P.A P.L).IsLB := DVR.linComb_isLB _ P.isLB _ _
  have h3 := hlam A.L P.L _ (abelian₂ A.A A.L) (𝟙 _) A.isLB P.isLB hLamA hwL.symm (GlobalTheory.DescendedPrincipal.lbIso_pull_id hLamA).symm
  rw [Category.comp_id] at h3
  have h1 : LBIso (abelian₂ A₁.A A₁.L) ((abelian₂ P.A P.L).pull (𝟙 _)) := lam_rigTransl P.isLB c hc
  refine ⟨A₁, g, β₂, t₀, hpb, hsq, ?_, ht₀, GlobalTheory.PelPrim.lbIso_linComb hwL.symm _ _⟩
  exact LBIso.trans (DVR.linComb_isLB _ A₁.isLB _ _) (pull_isLB hLamP _) (pull_isLB hLamA _) h1
    (LBIso.trans (pull_isLB hLamP _) hLamP (pull_isLB hLamA _) (GlobalTheory.DescendedPrincipal.lbIso_pull_id hLamP) h3)

end GlobalTheory.BaseTransl
