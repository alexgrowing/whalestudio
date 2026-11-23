import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HenselianLocalRingOfIsAdicComplete
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.VeryAmplePowerOfExtensionGenericFibreAbelianMode
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.RelAmpleIffVeryAmpleBy
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsAbelianSchemeOfIsGrpPullback
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.Definitions.Degenerations.ExistsGenPullTriv
import Development.AbelianVarietyTheory.Definitions.Uniformization.IsCPPullback
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.SemistableFin
import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Clauses
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AbLaw GlobalTheory.UU GlobalTheory.LN GlobalTheory.Raynaud IsLocalRing
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.ModelAmpleExt

theorem pw_pw' {X : Scheme.{0}} (H : LB X) (a b : ℤ) :
    GlobalTheory.AbLaw.pw (GlobalTheory.AbLaw.pw H a) b = GlobalTheory.AbLaw.pw H (a * b) :=
  congrArg (fun g => (⟨H.ι, H.U, g⟩ : LB X)) (funext fun i => funext fun j => (zpow_mul (H.g i j) a b).symm)

theorem relAmple_of_generic : ∀ (W L : Type) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field L] [Algebra W L] [IsFractionRing W L] (G : Over (Sp W)) [GrpObj G] (A : Over (Sp L)) [GrpObj A] (φ : A.left ⟶ G.left), IsAbelianScheme G → IsGrpPullback A G (spMap (algebraMap W L)) φ → ∀ M : LB G.left, M.IsLB → Out.RelAmple A (M.pull φ) → Out.RelAmple G M := by
  intro W L _ _ _ _ _ _ G _ A _ φ hG hφ M hM hA
  have hAab : IsAbelianScheme A := GlobalTheory.PolPull.isAbelianScheme_of_isGrpPullback hG hφ
  obtain ⟨d, hd, hex⟩ := (GlobalTheory.Unif.relAmple_iff_veryAmpleBy L A (M.pull φ) (pull_isLB hM φ)).1 hA

  rw [← GlobalTheory.TrivLocus.pull_pw M φ (d : ℤ)] at hex
  obtain ⟨m, s, hs⟩ := hex
  set f := spMap (algebraMap W L) with hf
  set g := spMap (algebraMap L L) with hg
  have hg1 : g = 𝟙 _ := by
    simp [hg, spMap]
  haveI : IsIso g := by rw [hg1]; infer_instance
  have h1 : inv (pullback.fst A.hom g) ≫ pullback.snd A.hom g = A.hom := by
    rw [IsIso.inv_comp_eq, pullback.condition, hg1, Category.comp_id]
  let i : pullback G.hom f ≅ pullback A.hom g :=
    hφ.1.isoPullback.symm ≪≫ (asIso (pullback.fst A.hom g)).symm
  have hi : i.hom ≫ pullback.snd A.hom g = pullback.snd G.hom f := by
    simp only [i, Iso.trans_hom, Iso.symm_hom, asIso_inv, Category.assoc, h1]
    exact hφ.1.isoPullback_inv_snd
  let e : (Over.pullback f).obj G ≅ (Over.pullback g).obj A := Over.isoMk i hi
  have he : e.hom.left ≫ pullback.fst A.hom g = hφ.1.isoPullback.inv := by
    simp [e, i]
  have hMd := GlobalTheory.AbLaw.isLB_pw hM (d : ℤ)
  obtain ⟨w, hw⟩ : LBIso ((GlobalTheory.AbLaw.pw M (d : ℤ)).pull (pullback.fst G.hom f))
      (((GlobalTheory.AbLaw.pw M (d : ℤ)).pull φ).pull (e.hom.left ≫ pullback.fst A.hom g)) :=
    LBIso.chartPull
      (chartPullSame (GlobalTheory.AbLaw.pw M (d : ℤ)) (fun _ : PUnit => pullback.fst G.hom f) (fun _ => φ) (fun _ => 1)
        (e.hom.left ≫ pullback.fst A.hom g) fun _ => by rw [he]; exact hφ.1.isoPullback_inv_fst.symm)
      (ReciprocityTheory.ChartRestriction.G.Geo.Tor.chartPullPull _ _ _ rfl) ⟨_, Geo.Tor.idIso_isGen (pull_isLB hMd φ)⟩
  obtain ⟨n, hn, hex2⟩ := GlobalTheory.ModelAmple.veryAmpleBy_pw_of_generic L W L A hAab G hG e
    ((GlobalTheory.AbLaw.pw M (d : ℤ)).pull φ) m s (GlobalTheory.AbLaw.pw M (d : ℤ)) w (pull_isLB hMd φ) hs hMd hw
  rw [pw_pw', show (d : ℤ) * (n : ℤ) = ((d * n : ℕ) : ℤ) by push_cast; rfl] at hex2
  exact (GlobalTheory.Unif.relAmple_iff_veryAmpleBy W G M hM).2 ⟨d * n, Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero
    (Nat.one_le_iff_ne_zero.1 hd) (Nat.one_le_iff_ne_zero.1 hn)), hex2⟩

end GlobalTheory.ModelAmpleExt
