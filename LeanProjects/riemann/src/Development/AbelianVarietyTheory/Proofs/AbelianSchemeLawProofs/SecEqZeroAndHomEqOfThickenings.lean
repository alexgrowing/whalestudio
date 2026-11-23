import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.DegExp
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.IsIntegralOfSmoothFieldOfConnectedSpace
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.IsIsoOfIsClosedImmersionOfThickenings
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.CoeNonzeroLocusCanonicalEqComplRange

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

namespace ThickeningDetermines

open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R Cartier EffCartierData TopologicalSpace

variable {X Y : Scheme.{0}} {N : LB X}

theorem exists_mem_chart (hN : N.IsLB) (x : X) : ∃ i, x ∈ N.U i :=
  Opens.mem_iSup.1 (hN.cover.ge (Set.mem_univ x))

theorem associated_germ_sec (s : N.Sec) (i j : N.ι) (x : X) (hi : x ∈ N.U i) (hj : x ∈ N.U j) :
    Associated ((X.presheaf.germ _ x hi).hom (s.f i)) ((X.presheaf.germ _ x hj).hom (s.f j)) := by
  have hm : x ∈ N.U i ⊓ N.U j := ⟨hi, hj⟩
  have h0 : Associated (resG X (inf_le_left : N.U i ⊓ N.U j ≤ N.U i) (s.f i))
      (resG X (inf_le_right : N.U i ⊓ N.U j ≤ N.U j) (s.f j)) :=
    (congrArg (Associated · _) (s.compat i j)).mpr
      (associated_unit_mul_left _ _ (N.g i j).isUnit)
  have := h0.map (X.presheaf.germ _ x hm).hom
  rwa [germ_resG, germ_resG] at this

noncomputable def secIdeal (hN : N.IsLB) (s : N.Sec) : X.IdealSheafData :=
  locIdeal N.U s.f (exists_mem_chart hN) (associated_germ_sec s)

theorem secIdeal_le_ker (hN : N.IsLB) (s : N.Sec) (φ : Y ⟶ X) [QuasiCompact φ]
    (h : ∀ j, (φ.app _).hom (s.f j) = 0) : secIdeal hN s ≤ φ.ker := by
  have loc : ∀ x : X, ∃ (W : X.affineOpens) (i : N.ι), x ∈ W.1 ∧ W.1 ≤ N.U i := fun x ↦ by
    obtain ⟨i, hi⟩ := exists_mem_chart hN x
    obtain ⟨W, hxW, hW⟩ := exists_affine_le hi
    exact ⟨W, i, hxW, hW⟩
  choose W i hx hW using loc
  refine Scheme.IdealSheafData.le_of_iSup_eq_top W
    (eq_top_iff.2 fun x _ ↦ Opens.mem_iSup.2 ⟨x, hx x⟩) fun x ↦ ?_
  refine (ideal_locIdeal _ _ _ _ (W x) (i x) (hW x)).trans_le ?_
  rw [Ideal.span_singleton_le_iff_mem, Scheme.Hom.ker_apply, RingHom.mem_ker, app_resG, h,
    map_zero]

theorem eq_zero_of_secIdeal_eq_bot (hN : N.IsLB) (s : N.Sec) (h : secIdeal hN s = ⊥) (j : N.ι) :
    s.f j = 0 := by
  refine X.IsSheaf.section_ext fun x hx ↦ ?_
  obtain ⟨W, hxW, hW⟩ := exists_affine_le (V := N.U j) hx
  refine ⟨W.1, hW, hxW, ?_⟩
  have h1 := ideal_locIdeal _ _ (exists_mem_chart hN) (associated_germ_sec s) W j hW
  have h2 : (secIdeal hN s).ideal W = ⊥ := by rw [h]; rfl
  have h3 := Ideal.span_singleton_eq_bot.1 (h1.symm.trans h2)
  exact h3.trans (map_zero _).symm

end ThickeningDetermines

open ThickeningDetermines in

theorem sec_eq_zero_and_hom_eq_of_thickenings : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (I : Ideal R), I ≤ Ideal.jacobson ⊥ → ∀ (H : Over (Spec (CommRingCat.of R))) [GrpObj H] [Smooth H.hom] [GeometricallyConnected H.hom], (∀ (N : LB H.left), N.IsLB → ∀ s : LB.Sec N, (∀ (n : ℕ) j, ((fstG I n H).left.app _).hom (s.f j) = 0) → ∀ j, s.f j = 0) ∧ (∀ (Y : Over (Spec (CommRingCat.of R))) [IsSeparated Y.hom] (f g : H ⟶ Y), (∀ n : ℕ, (fstG I n H).left ≫ f.left = (fstG I n H).left ≫ g.left) → f = g) := by
  intro R _ _ I hI H _ _ _
  have := grpObj_geometricallyIntegral_of_smooth _ H
  have key := isIso_of_isClosedImmersion_of_thickenings R I hI H η[H] (fun p ↦ inferInstance)
  refine ⟨fun N hN s hs ↦ eq_zero_of_secIdeal_eq_bot hN s ?_, fun Y _ f g h ↦ ?_⟩
  · have := key _ (secIdeal hN s).subschemeι fun n ↦ by
      have : IsClosedImmersion (thick R I n) :=
        IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective
      have : QuasiCompact (fstG I n H).left :=
        inferInstanceAs (QuasiCompact (pullback.fst H.hom (thick R I n)))
      exact ⟨IsClosedImmersion.lift _ (fstG I n H).left (by
        rw [Scheme.IdealSheafData.ker_subschemeι]
        exact secIdeal_le_ker hN s _ (hs n)), IsClosedImmersion.lift_fac _ _ _⟩
    rw [← Scheme.IdealSheafData.ker_subschemeι (secIdeal hN s)]
    exact IsClosedImmersion.isIso_iff_ker_eq_bot.1 this
  · have := key _ (equalizer.ι f g).left fun n ↦
      ⟨(equalizer.lift (fstG I n H) (Over.OverMorphism.ext (h n))).left,
        by rw [← Over.comp_left, equalizer.lift_ι]⟩
    refine Over.OverMorphism.ext ?_
    rw [← cancel_epi (equalizer.ι f g).left]
    exact congrArg CommaMorphism.left (equalizer.condition f g)

end GlobalTheory
