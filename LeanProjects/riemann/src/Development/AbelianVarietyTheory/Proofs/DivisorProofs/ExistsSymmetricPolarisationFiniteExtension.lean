import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.EvenDefect
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.SiegelToroidalPolCharts
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.SecCmp
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHalvingPointAbelianSchemeFiniteExtStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGeneratorMumfordBundleInvPullbackPrimitiveStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrimitiveBundleEqTranslateAmpleNoetherianLocalStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSymmetricRigidifiedTranslateAmpleKTrivialStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SiegelStructurePullback
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsAbelianSchemeOfIsGrpPullback
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.PolDeg.SymPol

variable {S S' : Scheme.{0}} {f : S' ⟶ S} {G : Over S} {G' : Over S'} [GrpObj G] [GrpObj G'] {φ : G'.left ⟶ G.left}

theorem inv_comm (h : IsGrpPullback G' G f φ) : (ι[G']).left ≫ φ = φ ≫ (ι[G]).left := by
  have e := congrArg (fun z => z.left) (map_inv (pushHom h G') (𝟙 G'))
  rw [Hom.inv_def, Hom.inv_def, Category.id_comp] at e
  refine Eq.trans e ?_
  show (𝟙 _ ≫ φ) ≫ _ = _
  rw [Category.id_comp]

theorem exists_half (h : IsGrpPullback G' G f φ) (a : 𝟙_ (Over S) ⟶ G) (b : Over.mk f ⟶ G) (hb : b ^ 2 = toUnit _ ≫ a) :
    ∃ b' : 𝟙_ (Over S') ⟶ G',
      ((toUnit G' ≫ b' ^ 2) * 𝟙 G').left ≫ φ = φ ≫ ((toUnit G ≫ a) * 𝟙 G).left := by
  have w : b.left ≫ G.hom = 𝟙 S' ≫ f := (Over.w b).trans (Category.id_comp _).symm
  let b' : 𝟙_ (Over S') ⟶ G' := Over.homMk (h.1.lift _ _ w) (h.1.lift_snd _ _ _)
  have hb' : b'.left ≫ φ = b.left := h.1.lift_fst _ _ _
  let j : Over.mk (G'.hom ≫ f) ⟶ Over.mk f := Over.homMk G'.hom rfl
  have hu : (toUnit G').left = G'.hom := (Category.comp_id _).symm.trans (Over.w (toUnit G'))
  have e₁ : pushHom h G' (toUnit G' ≫ b') = j ≫ b := Over.OverMorphism.ext (by
    show ((toUnit G').left ≫ b'.left) ≫ φ = G'.hom ≫ b.left
    rw [Category.assoc, hb', hu])
  have e₂ : pushHom h G' ((toUnit G' ≫ b' ^ 2) * 𝟙 G') = pushHom h G' (𝟙 G') ≫ ((toUnit G ≫ a) * 𝟙 G) := by
    rw [map_mul, MonObj.comp_pow, map_pow, e₁, ← MonObj.comp_pow, hb, MonObj.comp_mul, Category.comp_id,
      ← Category.assoc, ← Category.assoc, toUnit_unique (j ≫ toUnit _) (pushHom h G' (𝟙 G') ≫ toUnit G)]
  refine ⟨b', (congrArg (fun z => z.left) e₂).trans ?_⟩
  show (𝟙 _ ≫ φ) ≫ _ = _
  rw [Category.id_comp]

theorem exists_gen_theta_pull [IsCommMonObj G] [IsCommMonObj G'] (h : IsGrpPullback G' G f φ) {L : LB G.left}
    (ht : ∃ t : LB.Gen (Theta G L), t.IsGen) : ∃ t : LB.Gen (Theta G' (L.pull φ)), t.IsGen := by
  obtain ⟨t, ht⟩ := ht
  exact gen_chartPull (chartPullLinComb L φ _ _ _ (cubeMapOf h).F3 fun I => (cubeMapOf h).psum_comm I.down) t ht

end GlobalTheory.PolDeg.SymPol

open GlobalTheory.PolDeg.SymPol GlobalTheory.CechPic in

theorem GlobalTheory.PolDeg.exists_symmetric_pol : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (Q : Data R), IsCN R → ∃ (R' : Type) (_ : CommRing R') (_ : IsDomain R') (_ : IsLocalRing R') (ρ : R →+* R') (P : PolAV (Sp R')) (β : P.A.left ⟶ Q.B.left) (β₂ : (G2 P.A).left ⟶ (G2 Q.B).left), IsCN R' ∧ Function.Injective ρ ∧ ρ.Finite ∧ IsLocalHom ρ ∧ IsGrpPullback P.A Q.B (spMap ρ) β ∧ IsSquare β β₂ ∧ (letI := P.isAb.comm; LBIso (abelian₂ P.A P.L) ((abelian₂ Q.B Q.M.L).pull β₂)) := by
  intro R _ _ _ Q hR
  haveI := hR.1
  have hM := Q.M.isLB
  have hΘ : ∃ t : LB.Gen (Theta Q.B Q.M.L), t.IsGen := ⟨Q.cub.t, Q.cub.isGen⟩
  obtain ⟨a, ha⟩ := GlobalTheory.T.primitive_bundle_eq_translate_ample_noetherian_local R Q.B Q.g Q.M.L _ Q.isAb Q.smoothDim hM Q.ample Q.ktriv hΘ
    (LB.isLB_linComb hM _ _) (GlobalTheory.T.exists_generator_mumfordBundle_inv_pullback_primitive R Q.B Q.M Q.cub Q.isAb)
  have ea := (cls_eq_iff (LB.isLB_linComb hM _ _) (LB.isLB_linComb hM _ _)).2 ha
  rw [cls_linComb hM, cls_linComb hM, Fin.sum_univ_two, Fin.sum_univ_two] at ea
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, one_smul, add_left_inj] at ea
  obtain ⟨R', _, _, _, ρ, b, hR', hinj, hfin, hloc, hb⟩ := GlobalTheory.T.exists_halving_point_abelianScheme_finite_ext R Q.B a hR Q.isAb
  haveI := hR'.1
  have h := isGrpPullback_pullback Q.B (spMap ρ)
  have hA := PolPull.isAbelianScheme_of_isGrpPullback Q.isAb h
  haveI := hA.comm
  obtain ⟨b', hb'⟩ := exists_half h a b hb
  have hM' := pull_isLB hM (pullback.fst Q.B.hom (spMap ρ))
  have hid := (cls_eq_iff hM' hM').1 rfl
  obtain ⟨w, hw⟩ := id hid
  obtain ⟨L, hL, hrig, hsym, hamp, hK, hΛ⟩ := GlobalTheory.T.exists_symmetric_rigidified_translate_ample_K_trivial R' _ _ b' hA hM'
    (relAmple_pull h.1 hM hM' ((isGen_iff w).1 hw) ⊤ (isAffineOpen_top _) (fun _ => trivial) Q.ample)
    (kTriv_pull h hM hM' ((isGen_iff w).1 hw) Q.ktriv) (exists_gen_theta_pull h hΘ)
    ((cls_eq_iff (pull_isLB hM' _) (pull_isLB hM' _)).1 (by
      rw [cls_pull hM', cls_pull hM', cls_pull hM, ← pull_comp, ← pull_comp, inv_comm h, hb', pull_comp, pull_comp, ea]))
  obtain ⟨β₂, hβ₂⟩ := SiegPull.exists_isSquare h.1.w
  exact ⟨R', _, _, _, ρ,
    { A := (Over.pullback (spMap ρ)).obj Q.B, isAb := hA, g := Q.g
      smoothDim := (smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback h.1 Q.smoothDim
      L := L, isLB := hL, rigid := hrig, sym := hsym, ample := hamp, ktriv := hK }, _, β₂, hR', hinj, hfin, hloc, h, hβ₂,
    LBIso.trans (LB.isLB_linComb hL _ _) (LB.isLB_linComb hM' _ _) (pull_isLB (LB.isLB_linComb hM _ _) _) hΛ
      (SiegPull.lbIso_lam_pull h hid hβ₂)⟩

end
