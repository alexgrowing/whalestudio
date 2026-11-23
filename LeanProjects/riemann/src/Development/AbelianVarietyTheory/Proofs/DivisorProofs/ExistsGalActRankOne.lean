import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.QuasiCompact
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsIdentityPullbackDegeneration
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.PullPointIdentityDegeneration
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.GmMulEqOfResMulEq

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Mum

section
variable {R : Type} [CommRing R] [IsLocalRing R] {S : Scheme.{0}}

def Near.pull (π : S ⟶ Sp R) (G : Over (Sp R)) [Smooth G.hom] [IsSeparated G.hom] [QuasiCompact G.hom] :
    Near π ((Over.pullback π).obj G) where
  U := G
  smooth := inferInstance
  separated := inferInstance
  quasiCompact := inferInstance
  u := 𝟙 _
  isOpen := inferInstanceAs (IsOpenImmersion (𝟙 (pullback G.hom π)))
  u_over := Category.id_comp _
  all := fun g _ => ⟨g, rfl⟩

end

open GlobalTheory.TorsionFormCompare in

theorem isPullUnif_refl {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegData R I}
    {A : PolAV (Sp (FractionRing R))} {G : Over (Sp R)} [GrpObj G] [IsCommMonObj G] (U : Unif I D A G)
    (hD : IsPullDeg (RingHom.id R) D.toPre D.toPre) (hid : IsIdPull hD)
    (bc : G ≅ (Over.pullback (specOf (RingHom.id R))).obj G)
    (hbc : bc.hom.left ≫ pullback.fst G.hom (specOf (RingHom.id R)) = 𝟙 _) : IsPullUnif (RingHom.id R) hD bc U U := by
  obtain ⟨hx, he, hw⟩ := hid
  have hs := specOf_id R
  have heG : eSec G ≫ bc.hom.left ≫ pullback.fst G.hom (specOf (RingHom.id R)) = specOf (RingHom.id R) ≫ eSec G := by
    rw [hbc, hs, Category.comp_id]; exact (Category.id_comp _).symm
  refine (GlobalTheory.isPullUnif_iff_stalks R R I I _ D D hD A A G G bc U U).2
    ⟨isoPullId (Geo.Tor.idIso U.LG.L) hbc, (isGen_iff _).2 (isoPullId_pgen (idIso_isGen U.LG.isLB) hbc), heG,
      isoPullId_maps (idIso_maps U.LG) hbc hs heG, fun e => ⟨𝟙 _, by rw [hbc, Category.id_comp, Category.comp_id],
      ⟨by rw [he, Category.id_comp, Category.comp_id], fun x => ?_⟩, ?_⟩⟩
  · rw [hx x]
    exact ⟨fun κ => by rw [he, Category.id_comp, Category.comp_id],
      pmaps_self_of_tautological he hD.w hw _ _ _ ((U.gt e).t_gen x)⟩
  · intro Z r z jM jM' jL jL' h₁ h₂ h₃ h₄
    have h₁' : (U.gt e).pG.left (r z) ∈ D.toPre.P.L.U jM := by rw [he] at h₁; exact h₁
    have h₃' : (fstG I e G).left (r z) ∈ U.LG.L.U jL := by rw [hbc] at h₃; exact h₃
    rw [Category.comp_id, gw_isoPullId _ hbc _ z jL jL' h₃' h₄, hw Z (r ≫ (U.gt e).pG.left) z jM jM' h₁' h₂]
    have H := (isGen_iff (U.w e)).1 (U.w_gen e) Z r z jM jM' (fun _ => jL) (fun _ => jL') h₁' h₂
      (mem_pull.2 h₃') (mem_pull.2 h₄)
    have hp : r z ∈ (U.LG.L.pull (fstG I e G).left).U (fun _ => jL) ⊓ (U.LG.L.pull (fstG I e G).left).U (fun _ => jL') :=
      ⟨mem_pull.2 h₃', mem_pull.2 h₄⟩
    have e₂ : gm r z _ ((U.LG.L.pull (fstG I e G).left).g (fun _ => jL) (fun _ => jL')) =
        gm (r ≫ (fstG I e G).left) z _ (U.LG.L.g jL jL') := by
      show gm r z _ (∏ _k : PUnit, (res _ (pullU _ _ (U.LG.L.g jL jL'))) ^ (1 : ℤ)) = _
      rw [Fintype.prod_unique, zpow_one]
      exact (gm_res r z _ hp _).trans (gm_pull r _ z (U.LG.L.U jL ⊓ U.LG.L.U jL') ⟨h₃', h₄⟩ _)
    rw [H, e₂]
    show _ = _ * gm (r ≫ (fstG I e G).left) z _ (U.LG.L.g jL jL')
    rw [mul_right_comm _ _⁻¹, inv_mul_cancel_right]

end GlobalTheory.Mum
