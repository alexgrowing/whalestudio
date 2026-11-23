import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsFrameVec
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieLatticeEvalFractionField
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsExcisionNbhdAway
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.GenericExistsUniqueOActOfIsGrpPullback
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabComp
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.SpecFracExt
open NumberField IsDedekindDomain MeasureTheory Filter Topology
open Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Inst Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Rec
open AlgebraicGeometry CategoryTheory
open scoped Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.Ar.Rec.FinRd.Roots.LieBasis

open scoped CategoryTheory.Obj

theorem exists_extended_identification : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E), GlobalTheory.Published.SemiAbelianHomExtension → ∀ (X : Scheme.{0}) (tX : SAB H X) (T : CDVR) (zV : Spec (CommRingCat.of T.V) ⟶ X) (G : SAB H (Spec (CommRingCat.of T.V))) (t' : SAB H (Spec (CommRingCat.of T.Fr))) (m2 : SABMap t' G (Spec.map (CommRingCat.ofHom (algebraMap T.V T.Fr)))) (b : t'.G.left ⟶ tX.G.left), IsGrpPullback t'.G tX.G (FinRd.Roots.gen T zV) b → (∀ a, (t'.act.act a).left ≫ b = b ≫ (tX.act.act a).left) → ∃ Ψ : G.G.left ⟶ tX.G.left, IsGrpPullback G.G tX.G zV Ψ ∧ m2.φ ≫ Ψ = b ∧ ∀ a, (G.act.act a).left ≫ Ψ = Ψ ≫ (tX.act.act a).left := by
  intro E _ _ _ H hE X tX T zV G t' m2 b hb hact
  have hp : IsGrpPullback ((Over.pullback zV).obj tX.G) tX.G zV (Limits.pullback.fst tX.G.hom zV) :=
    isGrpPullback_pullback tX.G zV
  let ψ : t'.G.left ⟶ ((Over.pullback zV).obj tX.G).left :=
    Limits.pullback.lift b (t'.G.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap T.V T.Fr)))
      (by rw [hb.1.w, Category.assoc])
  have hψf : ψ ≫ Limits.pullback.fst tX.G.hom zV = b := Limits.pullback.lift_fst _ _ _
  have hψs : ψ ≫ ((Over.pullback zV).obj tX.G).hom =
      t'.G.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap T.V T.Fr)) := Limits.pullback.lift_snd _ _ _
  have hψ : IsGrpPullback t'.G ((Over.pullback zV).obj tX.G)
      (Spec.map (CommRingCat.ofHom (algebraMap T.V T.Fr))) ψ :=
    hp.cancel (hb.congr rfl hψf.symm) hψs
  have hj : GlobalTheory.IsGenericPointHom (Spec.map (CommRingCat.ofHom (algebraMap T.V T.Fr))) :=
    GlobalTheory.IsGenericPointHom.fractionField T.V T.Fr
  have hS := GlobalTheory.Published.SemiAbelianHomExtension.isNormalScheme_spec T.V
  have hH' := IsSemiAbelian.pullback zV tX.G tX.semi
  obtain ⟨e, ⟨hmon, heq⟩, -⟩ := hE.generic_existsUnique_iso_of_extensions hS hj G.semi hH' m2.cart hψ
  obtain ⟨_, _⟩ := hj.quasiCompact_and_dominant
  obtain ⟨_, _⟩ := GlobalTheory.ExtUnique.flat_and_isSeparated_of_isSemiAbelian G.G G.semi
  obtain ⟨-, _⟩ := GlobalTheory.ExtUnique.flat_and_isSeparated_of_isSemiAbelian _ hH'
  refine ⟨e.hom.left ≫ Limits.pullback.fst tX.G.hom zV,
    ((isGrpPullback_of_iso e).comp hp).congr (Category.id_comp _) rfl, ?_, fun a => ?_⟩
  · rw [← Category.assoc, heq, hψf]
  · have hB : ((Over.pullback zV).map (tX.act.act a)).left ≫ Limits.pullback.fst tX.G.hom zV =
        Limits.pullback.fst tX.G.hom zV ≫ (tX.act.act a).left := Limits.pullback.lift_fst _ _ _
    have hψa : (t'.act.act a).left ≫ ψ = ψ ≫ ((Over.pullback zV).map (tX.act.act a)).left := by
      apply Limits.pullback.hom_ext
      · rw [Category.assoc, Category.assoc, hB, hψf, ← Category.assoc ψ, hψf, hact]
      · have h₁ := hψs
        have h₂ := Over.w ((Over.pullback zV).map (tX.act.act a))
        have h₃ := Over.w (t'.act.act a)
        change _ ≫ ((Over.pullback zV).obj tX.G).hom = _ ≫ ((Over.pullback zV).obj tX.G).hom
        rw [Category.assoc, Category.assoc, h₂, h₁, ← Category.assoc, h₃]
    have key : G.act.act a ≫ e.hom = e.hom ≫ (Over.pullback zV).map (tX.act.act a) := by
      refine GlobalTheory.ExtUnique.over_hom_ext_of_isPullback m2.cart.1 ?_
      rw [Over.comp_left, Over.comp_left, ← Category.assoc, ← m2.act a, Category.assoc, heq, hψa,
        ← Category.assoc, heq]
    have key' := congrArg (fun f => f.left ≫ Limits.pullback.fst tX.G.hom zV) key
    simp only [Over.comp_left, Category.assoc, hB] at key'
    simpa only [Category.assoc] using key'

end GlobalTheory.CompanionTheory.Ar.Rec.FinRd.Roots.LieBasis
