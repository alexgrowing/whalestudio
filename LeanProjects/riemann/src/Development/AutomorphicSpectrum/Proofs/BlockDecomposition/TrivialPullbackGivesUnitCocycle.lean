import Mathlib
import Development.WeilBound.CoreStatements.AutomorphicKernels.AbelianDeRham.AbelianHodgeDeRham.H1DimGeAbelianDim
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsGenOfSmallExtension
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.CechHOneVanishesOnOpenOfIsAffineOpen
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TrMulTrInv
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CechDR MainStatements.Hodge GlobalTheory.CompanionTheory.FewEq
open GlobalTheory.AbLaw (rs)

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace GlobalTheory.CompanionTheory.FewEq

open GlobalTheory.SmallExtLift

theorem exists_local_of_gen {R : Type} [CommRing R] {X Y : Scheme.{0}} (s : X ⟶ Sp R) (J : Ideal R)
    {π : Y ⟶ X} {f' : Y ⟶ Sp (R ⧸ J)}
    (H : IsPullback π f' s (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J))))
    (M : LB X) (A : Type) (V : A → X.Opens) (j : A → M.ι) (hj : ∀ a, V a ≤ M.U (j a))
    (hV : ∀ a, IsAffineOpen (V a)) (hVV : ∀ a b, IsAffineOpen (V a ⊓ V b))
    (t : LB.Gen (M.pull π)) (ht : t.IsGen) :
    ∃ y z : ∀ a, Γ(X, V a), (∀ a, y a * z a - 1 ∈ ext s J (V a)) ∧
      ∀ a b, rs X inf_le_left (y a) - tr M V j hj a b * rs X inf_le_right (y b) ∈
        ext s J (V a ⊓ V b) := by
  choose y hy using fun a => app_surj Ideal.Quotient.mk_surjective H (hV a)
    (rs Y (pull_le M π (j a) (hj a)) (t.s fun _ => j a).val)
  choose z hz using fun a => app_surj Ideal.Quotient.mk_surjective H (hV a)
    (rs Y (pull_le M π (j a) (hj a)) (t.s fun _ => j a)⁻¹.val)
  refine ⟨y, z, fun a => ?_, fun a b => ?_⟩
  · have h := mem_of_app_eq_zero Ideal.Quotient.mk_surjective H (hV a) (y a * z a - 1) (by
      rw [map_sub, map_mul, map_one, hy, hz, ← map_mul, Units.mul_inv, map_one, sub_self])
    rwa [Ideal.mk_ker] at h
  · have h := mem_of_app_eq_zero Ideal.Quotient.mk_surjective H (hVV a b)
      (rs X inf_le_left (y a) - tr M V j hj a b * rs X inf_le_right (y b)) (gr_ext fun w hw => by
        have e : ∀ c (h : (𝟙 Y ≫ π) w ∈ V c), gr (𝟙 Y ≫ π) w (V c) h (y c) =
            gr (𝟙 Y) w _ (pull_le M π (j c) le_rfl (hj c h)) (t.s fun _ => j c).val := fun c h =>
          (gr_app (𝟙 Y) π w (V c) h (y c)).symm.trans
            ((congrArg _ (hy c)).trans (gr_res (𝟙 Y) w _ h _))
        refine (gr_app _ _ _ _ _ _).trans ?_
        simp only [tr]
        rw [map_zero, map_sub, map_mul, gr_res, gr_res, gr_res, e, e, sub_eq_zero]
        exact gr_gen ht (𝟙 Y) w (hj a hw.1) (hj b hw.2))
    rwa [Ideal.mk_ker] at h

theorem exists_local_of_triv : ∀ (R : Type) [CommRing R] (X : Scheme.{0}) (s : X ⟶ Sp R) (J : Ideal R) (M : LB X), M.IsLB →
    ∀ (A : Type) (V : A → X.Opens) (j : A → M.ι) (hj : ∀ a, V a ≤ M.U (j a)),
      (∀ a, IsAffineOpen (V a)) → (∀ a b, IsAffineOpen (V a ⊓ V b)) →
      GlobalTheory.AbLaw.Triv (M.pull (pullback.fst s (spMap (Ideal.Quotient.mk J)))) →
      ∃ y z : ∀ a, Γ(X, V a), (∀ a, y a * z a - 1 ∈ ext s J (V a)) ∧
        ∀ a b, rs X inf_le_left (y a) - tr M V j hj a b * rs X inf_le_right (y b) ∈ ext s J (V a ⊓ V b) := by
  intro R _ X s J M _ A V j hj hV hVV ⟨t, ht⟩
  exact exists_local_of_gen s J (IsPullback.of_hasPullback s (spMap (Ideal.Quotient.mk J))) M A V j
    hj hV hVV t ht

end GlobalTheory.CompanionTheory.FewEq
