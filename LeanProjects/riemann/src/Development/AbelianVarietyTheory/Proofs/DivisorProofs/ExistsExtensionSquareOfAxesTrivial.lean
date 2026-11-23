import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HenselianLocalRingOfIsAdicComplete
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.Definitions.Degenerations.ExistsGenPullTriv
import Development.AbelianVarietyTheory.Definitions.Uniformization.IsCPPullback
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.SemistableFin
import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Clauses
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLineBundleExtensionOfGenericFibreDvr
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LineBundleIsoAbelianSchemeDVROfGenericIsoStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsProjectiveModel
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsAmpleLBOfRelAmpleOfIsAffine
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AbelianSchemeGerms
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.PrecompleteBases.PsbLb
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.Biextensions.GenericFiberCubeInclusion

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AbLaw GlobalTheory.UU GlobalTheory.LN GlobalTheory.Raynaud IsLocalRing
open scoped CategoryTheory.Obj

noncomputable section

namespace GlobalTheory.AxisTrivExt

variable {S S' : Scheme.{0}}

theorem isPullback_sq {A : Over S'} {G : Over S} {b : S' ⟶ S} {f : A.left ⟶ G.left}
    (m : IsPullback f A.hom G.hom b) {h : (A ⊗ A).left ⟶ (G ⊗ G).left}
    (h₁ : h ≫ (fst G G).left = (fst A A).left ≫ f) (h₂ : h ≫ (snd G G).left = (snd A A).left ≫ f) :
    IsPullback h (A ⊗ A).hom (G ⊗ G).hom b := by
  have p : IsPullback (fst G G).left (snd G G).left G.hom G.hom := IsPullback.of_hasPullback _ _
  have p' : IsPullback (fst A A).left (snd A A).left A.hom A.hom := IsPullback.of_hasPullback _ _
  have q := p'.paste_horiz m
  rw [← h₁, ← m.w] at q
  have r := (IsPullback.of_right q h₂ p).paste_vert m
  rwa [Over.w, Over.w] at r

theorem unit_comp {A : Over S'} {G : Over S} [GrpObj A] [GrpObj G] {f : S' ⟶ S} {a : A.left ⟶ G.left}
    (ha : IsGrpPullback A G f a) : η[A].left ≫ a = f ≫ η[G].left := by
  let p : (𝟙_ (Over S') ⟶ A) → (Over.mk ((𝟙_ (Over S')).hom ≫ f) ⟶ G) := fun x =>
    Over.homMk (x.left ≫ a) (by
      rw [Category.assoc, ha.1.w, ← Category.assoc, Over.w x]; rfl)
  have hp : p 1 * p 1 = p 1 := by
    apply Over.OverMorphism.ext
    rw [ha.2 _ 1 1 (p 1) (p 1) rfl rfl, _root_.mul_one]; rfl
  have h1 : p 1 = 1 := by simpa using hp
  have e := congrArg (fun z => z.left) h1
  have e₁ : (1 : 𝟙_ (Over S') ⟶ A) = η[A] := by rw [Hom.one_def]; simp
  simp only [p, e₁, Hom.one_def] at e
  refine e.trans ?_
  simp

theorem one_comm {A : Over S'} {G : Over S} [GrpObj A] [GrpObj G] {f : S' ⟶ S} {a : A.left ⟶ G.left}
    (ha : IsGrpPullback A G f a) : (1 : A ⟶ A).left ≫ a = a ≫ (1 : G ⟶ G).left := by
  rw [Hom.one_def, Hom.one_def, Over.comp_left, Over.comp_left, Category.assoc, unit_comp ha]
  have e₁ : (toUnit A).left = A.hom := by simpa using Over.w (toUnit A)
  have e₂ : (toUnit G).left = G.hom := by simpa using Over.w (toUnit G)
  rw [e₁, e₂, ← Category.assoc, ← Category.assoc, ha.1.w]

theorem lift_match {A : Over S'} {X : Over S} {i : A.left ⟶ X.left} {l : (A ⊗ A).left ⟶ (X ⊗ X).left}
    (hl₁ : l ≫ (fst X X).left = (fst A A).left ≫ i) (hl₂ : l ≫ (snd X X).left = (snd A A).left ≫ i)
    (u v : A ⟶ A) (U V : X ⟶ X) (hu : i ≫ U.left = u.left ≫ i) (hv : i ≫ V.left = v.left ≫ i) :
    (lift u v).left ≫ l = i ≫ (lift U V).left := by
  have p : IsPullback (fst X X).left (snd X X).left X.hom X.hom := IsPullback.of_hasPullback _ _
  symm
  apply p.hom_ext
  · rw [Category.assoc, ← Over.comp_left, lift_fst, hu, Category.assoc, hl₁, ← Category.assoc, ← Over.comp_left,
      lift_fst]
  · rw [Category.assoc, ← Over.comp_left, lift_snd, hv, Category.assoc, hl₂, ← Category.assoc, ← Over.comp_left,
      lift_snd]

theorem exists_extension_square_of_axes_trivial : ∀ (W L : Type) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field L] [Algebra W L] [IsFractionRing W L] (G : Over (Sp W)) [GrpObj G] (A : Over (Sp L)) [GrpObj A] (φ : A.left ⟶ G.left) (φ₂ : (G2 A).left ⟶ (G2 G).left), IsAbelianScheme G → IsGrpPullback A G (spMap (algebraMap W L)) φ → IsSquare φ φ₂ → ∀ P : LB (G2 A).left, P.IsLB → (∃ t : (P.pull (lift (1 : A ⟶ A) (𝟙 A)).left).Gen, t.IsGen) → (∃ t : (P.pull (lift (𝟙 A) (1 : A ⟶ A)).left).Gen, t.IsGen) → ∃ P' : LB (G2 G).left, P'.IsLB ∧ (∃ t : (P'.pull (lift (1 : G ⟶ G) (𝟙 G)).left).Gen, t.IsGen) ∧ (∃ t : (P'.pull (lift (𝟙 G) (1 : G ⟶ G)).left).Gen, t.IsGen) ∧ LBIso P (P'.pull φ₂) := by
  intro W L _ _ _ _ _ _ G _ A _ φ φ₂ hG hA hsq P hP h₁ h₂
  have h2 : IsPullback φ₂ (G2 A).hom (G2 G).hom (spMap (algebraMap W L)) := isPullback_sq hA.1 hsq.1 hsq.2
  have hG2 : IsAbelianScheme (G2 G) := ReciprocityTheory.ChartRestriction.G.Geo.Tor.AbelianSchemeGerms.isAbelianScheme_tensor G G hG hG
  have he : h2.isoPullback.hom ≫ pullback.fst _ _ = φ₂ := h2.isoPullback_hom_fst
  obtain ⟨M, w, hM, hw⟩ := exists_lineBundle_extension_of_genericFibre_dvr W L (G2 G) hG2
    (P.pull h2.isoPullback.inv) (pull_isLB hP _)
  have i1 : LBIso ((P.pull h2.isoPullback.inv).pull h2.isoPullback.hom) (M.pull φ₂) :=
    GenSpread.lbIso_pull_of_lbIso (LBIso.symm ⟨w, hw⟩) h2.isoPullback.hom he.symm
  have i0 : LBIso (P.pull (𝟙 _)) ((P.pull h2.isoPullback.inv).pull h2.isoPullback.hom) :=
    GenSpread.lbIso_pull_pull hP h2.isoPullback.hom (by simp)
  have iP : LBIso P (M.pull φ₂) :=
    LBIso.trans hP (pull_isLB (pull_isLB hP _) _) (pull_isLB hM _)
      (LBIso.trans hP (pull_isLB hP _) (pull_isLB (pull_isLB hP _) _) (lbIso_pull_id hP).symm i0) i1
  have hT := LB.isLB_triv G.left
  have axis : ∀ (iA : A.left ⟶ (G2 A).left) (iG : G.left ⟶ (G2 G).left), iA ≫ φ₂ = φ ≫ iG →
      (∃ t : (P.pull iA).Gen, t.IsGen) → ∃ t : (M.pull iG).Gen, t.IsGen := by
    intro iA iG hc hgen
    let c : LB.Gen (LB.triv G.left) := ⟨fun _ => 1⟩
    have hcg : c.IsGen := fun _ _ => by simp [c]
    have a1 : LBIso (LB.triv A.left) ((LB.triv G.left).pull φ) :=
      (GlobalTheory.CechPic.iso_triv_iff _).2 ⟨LB.genPull _ c φ, LB.isGen_genPull _ c hcg φ⟩
    have a2 : LBIso (LB.triv A.left) (P.pull iA) := (GlobalTheory.CechPic.iso_triv_iff _).2 hgen
    have a3 : LBIso (P.pull iA) ((M.pull φ₂).pull iA) := GenSpread.lbIso_pullback iP iA
    have b1 : LBIso (M.pull (φ ≫ iG)) ((M.pull φ₂).pull iA) := GenSpread.lbIso_pull_pull hM iA hc.symm
    have b2 : LBIso (M.pull (φ ≫ iG)) ((M.pull iG).pull φ) := GenSpread.lbIso_pull_pull hM φ rfl
    have lTA := LB.isLB_triv A.left
    have q1 : LBIso ((M.pull iG).pull φ) (LB.triv A.left) :=
      LBIso.trans (pull_isLB (pull_isLB hM _) _) (pull_isLB hM _) lTA b2.symm
        (LBIso.trans (pull_isLB hM _) (pull_isLB (pull_isLB hM _) _) lTA b1
          (LBIso.trans (pull_isLB (pull_isLB hM _) _) (pull_isLB hP _) lTA a3.symm a2.symm))
    have q2 : LBIso ((M.pull iG).pull φ) ((LB.triv G.left).pull φ) :=
      LBIso.trans (pull_isLB (pull_isLB hM _) _) lTA (pull_isLB hT _) q1 a1
    have q3 : LBIso (M.pull iG) (LB.triv G.left) :=
      GlobalTheory.T.lineBundleIso_abelianSchemeDVR_of_generic_iso W L G A.left A.hom φ hG hA.1 (M.pull iG) (LB.triv G.left) (pull_isLB hM _) hT q2
    exact (GlobalTheory.CechPic.iso_triv_iff _).1 q3.symm
  refine ⟨M, hM, axis _ _ ?_ h₁, axis _ _ ?_ h₂, iP⟩
  · exact lift_match hsq.1 hsq.2 _ _ _ _ (one_comm hA).symm (by simp)
  · exact lift_match hsq.1 hsq.2 _ _ _ _ (by simp) (one_comm hA).symm

end GlobalTheory.AxisTrivExt
